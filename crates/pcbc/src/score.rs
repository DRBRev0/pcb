use anyhow::{Context, Result, bail};
use clap::Args;
use comfy_table::{Cell, ContentArrangement, Table, presets};
use pcb_layout::utils as layout_utils;
use pcb_score::{BoardModel, ScoreInputs, Weights, score_board};
use pcb_ui::prelude::*;
use std::path::PathBuf;

use crate::build::{BuildEvalState, create_diagnostics_passes};
use crate::config_input::{CONFIG_ARG_HELP, parse_config_overrides};

#[derive(Args, Debug, Default, Clone)]
#[command(about = "Score the routing quality of a board layout")]
pub struct ScoreArgs {
    /// Path to .zen file
    #[arg(value_name = "FILE", value_hint = clap::ValueHint::FilePath)]
    pub file: PathBuf,

    #[arg(long = "config", value_name = "KEY=VALUE", help = CONFIG_ARG_HELP)]
    pub config: Vec<String>,

    /// Disable network access (offline mode) - only use vendored dependencies
    #[arg(long = "offline")]
    pub offline: bool,

    /// Skip the KiCad DRC gate (fast mode for autorouting inner loops).
    /// The DRC gate is authoritative: run it on any candidate you keep.
    #[arg(long = "skip-drc")]
    pub skip_drc: bool,

    /// Path to a TOML file overriding category weights (keys of [score])
    #[arg(long = "weights", value_name = "FILE")]
    pub weights: Option<PathBuf>,

    /// Suppress diagnostics by kind or severity during the build
    #[arg(short = 'S', long = "suppress", value_name = "KIND")]
    pub suppress: Vec<String>,

    /// Output format
    #[arg(short = 'f', long, value_enum, default_value_t = ScoreOutputFormat::Human)]
    pub format: ScoreOutputFormat,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum ScoreOutputFormat {
    /// Human-readable output
    #[default]
    Human,
    /// JSON output (stable schema)
    Json,
}

pub fn execute(args: ScoreArgs) -> Result<()> {
    crate::file_walker::require_zen_file(&args.file)?;
    let config_inputs = parse_config_overrides(&args.config)?;
    let hide_progress = args.format == ScoreOutputFormat::Json;

    let weights = load_weights(args.weights.as_deref())?;

    // Build the .zen so we have the netlist (net properties, roles) and the
    // layout directory.
    let resolution_result = crate::resolve::resolve(Some(&args.file), args.offline)?;
    let zen_path = &args.file;
    let file_name = zen_path.file_name().unwrap().to_string_lossy().to_string();

    let build_result = BuildEvalState::new(resolution_result).build(
        zen_path,
        config_inputs,
        create_diagnostics_passes(&args.suppress, &[]),
        false,
        &mut false.clone(),
        &mut false.clone(),
    );
    let Some(schematic) = build_result.schematic else {
        bail!("Build failed");
    };

    let Some(layout_dir) = layout_utils::resolve_layout_dir(&schematic)? else {
        bail!(
            "{} has no layout. Add a `Layout` to the board and run 'pcb layout {}' first.",
            file_name,
            zen_path.display()
        );
    };
    let kicad_files = layout_utils::require_kicad_files(&layout_dir)?;
    let pcb_file = kicad_files.kicad_pcb();
    if !pcb_file.exists() {
        bail!(
            "Layout file not found: {}. Run 'pcb layout {}' to generate it.",
            pcb_file.display(),
            zen_path.display()
        );
    }

    let spinner = Spinner::builder(format!("{file_name}: Scoring layout"))
        .hidden(hide_progress)
        .start();

    let board_source = std::fs::read_to_string(&pcb_file)
        .with_context(|| format!("failed to read {}", pcb_file.display()))?;
    let board = BoardModel::parse(&board_source)?;

    let drc_report = if args.skip_drc {
        None
    } else {
        let drc_output = tempfile::NamedTempFile::new()?;
        let working_dir = pcb_file.parent();
        let report = pcb_kicad::run_drc(&pcb_file, false, working_dir, drc_output.path())
            .with_context(
                || "KiCad DRC failed; install kicad-cli or pass --skip-drc to score geometry only",
            )?;
        Some(report)
    };

    let report = score_board(&ScoreInputs {
        board: &board,
        board_source: &board_source,
        board_path: &pcb_file.to_string_lossy(),
        drc: drc_report.as_ref(),
        netlist: Some(&schematic),
        weights,
    })?;

    spinner.finish();

    match args.format {
        ScoreOutputFormat::Json => println!("{}", serde_json::to_string_pretty(&report)?),
        ScoreOutputFormat::Human => print_human(&report),
    }

    Ok(())
}

fn load_weights(path: Option<&std::path::Path>) -> Result<Weights> {
    let Some(path) = path else {
        return Ok(Weights::default());
    };
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read weights file {}", path.display()))?;
    let table: toml::Value = content
        .parse()
        .with_context(|| format!("invalid TOML in {}", path.display()))?;
    let section = table.get("score").unwrap_or(&table);
    let weights: Weights = section
        .clone()
        .try_into()
        .with_context(|| format!("invalid [score] weights in {}", path.display()))?;
    Ok(weights)
}

fn print_human(report: &pcb_score::ScoreReport) {
    let gates = &report.gates;
    let gate_line = |passed: bool, label: String| {
        if passed {
            println!("  {} {}", "✓".green(), label);
        } else {
            println!("  {} {}", "✗".red(), label);
        }
    };

    println!();
    println!("{}", "Gates".bold());
    gate_line(
        gates.connectivity.passed,
        format!(
            "Connectivity: {}/{} nets routed ({:.1}%)",
            gates.connectivity.connected_nets,
            gates.connectivity.total_nets,
            gates.connectivity.ratio * 100.0
        ),
    );
    if report.inputs.drc_ran {
        gate_line(
            gates.drc_errors.passed,
            format!("DRC errors: {}", gates.drc_errors.count),
        );
    } else {
        println!(
            "  {} DRC errors: not checked (--skip-drc); the score is not authoritative",
            "-".yellow()
        );
    }

    println!();
    let mut table = Table::new();
    table
        .load_preset(presets::UTF8_FULL_CONDENSED)
        .set_content_arrangement(ContentArrangement::Dynamic)
        .set_header(["Category", "Weight", "Score", "Details"]);
    for category in &report.categories {
        let score_text = category
            .score
            .map(|s| format!("{:.1}%", s * 100.0))
            .unwrap_or_else(|| "n/a".to_string());
        let applicable = category.metrics.iter().filter(|m| m.applicable).count();
        table.add_row([
            Cell::new(&category.label),
            Cell::new(format!("{:.0}", category.weight)),
            Cell::new(score_text),
            Cell::new(format!(
                "{applicable}/{} metrics applicable",
                category.metrics.len()
            )),
        ]);
    }
    println!("{table}");

    for category in &report.categories {
        let interesting: Vec<_> = category
            .metrics
            .iter()
            .filter(|m| m.applicable && !m.worst.is_empty())
            .collect();
        if interesting.is_empty() {
            continue;
        }
        println!();
        println!("{}", format!("Worst offenders — {}", category.label).bold());
        for metric in interesting {
            let entries: Vec<String> = metric
                .worst
                .iter()
                .map(|w| format!("{} ({})", w.label, w.value))
                .collect();
            println!("  {}: {}", metric.id, entries.join(", "));
        }
    }

    println!();
    println!(
        "{}  {}",
        "Score:".bold(),
        if gates.passed {
            format!("{:.1}/100", report.score).green().to_string()
        } else {
            format!("0 (gates failing; quality {:.1})", report.quality)
                .red()
                .to_string()
        }
    );
    println!(
        "{} {:.1}/100 (continuous autorouting objective)",
        "Fitness:".bold(),
        report.fitness
    );
}

#![cfg(not(target_os = "windows"))]

//! Tests for `pcb score` on a workspace with a pre-routed layout.

use pcb_test_utils::assert_snapshot;
use pcb_test_utils::sandbox::Sandbox;

const MODULE_ZEN: &str = r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

P1 = io(Net)
P2 = io(Net)

Resistor(name="R1", value="1kohm", package="0603", P1=P1, P2=P2)
Resistor(name="R2", value="1kohm", package="0603", P1=P1, P2=P2)

Layout(name="Module", path="module/", bom_profile=None)
"#;

fn sandbox_with_routed_layout() -> Sandbox {
    let mut sandbox = Sandbox::new();
    sandbox.write(
        "pcb.toml",
        "[workspace]\nname = \"zener\"\npcb-version = \"0.4\"\n",
    );
    sandbox.write("Module.zen", MODULE_ZEN);
    // Reuse the routed board fixture from pcb-layout's sync tests.
    let resources = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../pcb-layout/tests/resources/tracks/module"
    );
    for file in ["layout.kicad_pcb", "layout.kicad_pro", "fp-lib-table"] {
        let content = std::fs::read_to_string(format!("{resources}/{file}")).expect("fixture file");
        sandbox.write(&format!("module/{file}"), &content);
    }
    sandbox
}

#[test]
fn test_score_json_output() {
    let output = sandbox_with_routed_layout()
        .snapshot_run("pcbc", ["score", "Module.zen", "--skip-drc", "-f", "json"]);

    // The board hash and absolute paths vary per checkout; snapshot only the
    // stable structure.
    let json_start = output.find('{').expect("json in output");
    let json_end = output.rfind('}').expect("json end");
    let mut report: serde_json::Value =
        serde_json::from_str(&output[json_start..=json_end]).expect("valid JSON report");
    report["board"]["path"] = serde_json::Value::String("<PATH>".to_string());
    report["board"]["sha256"] = serde_json::Value::String("<SHA256>".to_string());
    assert_snapshot!(
        "score_json_output",
        serde_json::to_string_pretty(&report).unwrap()
    );
}

#[test]
fn test_score_human_output() {
    let output =
        sandbox_with_routed_layout().snapshot_run("pcbc", ["score", "Module.zen", "--skip-drc"]);
    assert_snapshot!("score_human_output", output);
}

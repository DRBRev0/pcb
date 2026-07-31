use std::collections::{BTreeSet, HashMap};

use pcb_sch::Schematic;
use starlark::codemap::ResolvedSpan;
use starlark::errors::EvalSeverity;
use starlark::values::ValueLike;

use crate::lang::pin_erc::{
    pin_no_connect_body, pin_types_are_only_no_connect, signal_pin_type_candidates,
};
use crate::lang::symbol::SymbolValue;
use crate::{Diagnostic, Diagnostics, EvalOutput, FrozenNetValue, ModulePath};

#[derive(Clone)]
struct NetMetadata {
    display_name: String,
    path: String,
    span: Option<ResolvedSpan>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ComponentSignalKey {
    component_path: String,
    signal_name: String,
}

#[derive(Clone)]
struct NetPinAttachment {
    component_name: String,
    signal_name: String,
    pin_types: Vec<String>,
}

#[derive(Clone)]
struct ErcNet<'a> {
    net: &'a pcb_sch::Net,
    metadata: Option<NetMetadata>,
    pin_attachments: Vec<NetPinAttachment>,
}

struct SchematicErcContext<'a> {
    nets: Vec<ErcNet<'a>>,
}

trait SchematicErcPass {
    fn run(&self, ctx: &SchematicErcContext<'_>, diagnostics: &mut Diagnostics);
}

struct PinNoConnectPass;

fn component_path(module_path: &ModulePath, component_name: &str) -> String {
    if module_path.is_root() {
        component_name.to_string()
    } else {
        format!("{module_path}.{component_name}")
    }
}

fn signal_names(symbol: &SymbolValue) -> BTreeSet<&str> {
    symbol
        .pad_to_signal
        .values()
        .map(|value| value.as_str())
        .collect()
}

impl<'a> SchematicErcContext<'a> {
    fn build(eval_output: &EvalOutput, schematic: &'a Schematic) -> Self {
        let mut pin_types_by_component_signal: HashMap<ComponentSignalKey, Vec<String>> =
            HashMap::new();
        let mut net_metadata: HashMap<u64, NetMetadata> = HashMap::new();

        for (module_path, module) in eval_output.module_tree() {
            for component in module.components() {
                let component_path = component_path(&module_path, component.name());

                if let Some(symbol) = component.symbol().downcast_ref::<SymbolValue>() {
                    for signal_name in signal_names(symbol) {
                        let candidates = signal_pin_type_candidates(symbol, signal_name);
                        if !candidates.is_empty() {
                            pin_types_by_component_signal.insert(
                                ComponentSignalKey {
                                    component_path: component_path.clone(),
                                    signal_name: signal_name.to_string(),
                                },
                                candidates,
                            );
                        }
                    }
                }

                for net_value in component.connections().values() {
                    if let Some(net) = net_value.downcast_ref::<FrozenNetValue>() {
                        net_metadata.entry(net.id()).or_insert_with(|| NetMetadata {
                            display_name: net.name().to_string(),
                            path: net.declaration_path().unwrap_or_default().to_string(),
                            span: net.declaration_span(),
                        });
                    }
                }
            }
        }

        let mut nets = Vec::new();
        for net in schematic.nets.values() {
            let mut pin_attachments = Vec::new();

            for port_ref in &net.ports {
                let Some((component_ref, signal_name)) =
                    schematic.component_ref_and_pin_for_port(port_ref)
                else {
                    continue;
                };

                let component_path = component_ref.instance_path.join(".");
                let Some(pin_types) = pin_types_by_component_signal.get(&ComponentSignalKey {
                    component_path: component_path.clone(),
                    signal_name: signal_name.to_string(),
                }) else {
                    continue;
                };

                let component_name = component_ref
                    .instance_path
                    .last()
                    .map(String::as_str)
                    .unwrap_or("<component>")
                    .to_string();

                pin_attachments.push(NetPinAttachment {
                    component_name,
                    signal_name: signal_name.to_string(),
                    pin_types: pin_types.clone(),
                });
            }

            nets.push(ErcNet {
                net,
                metadata: net_metadata.get(&net.id).cloned(),
                pin_attachments,
            });
        }

        Self { nets }
    }
}

/// Checks current budgets from io() declarations and static DC inference:
/// - error when a net's effective sources (declared + statically inferred
///   through typed passives) cannot cover its effective sinks;
/// - warning for nets whose current can neither be declared nor inferred,
///   once the design has opted into current accounting anywhere (a design
///   with zero declarations and no voltage-driven passives stays silent);
/// - warning for resistive subnetworks with no voltage reference to infer
///   from (`erc.current_budget.uninferable`);
/// - warning when io() `signal` declarations on one net disagree.
struct CurrentBudgetPass;

impl ErcNet<'_> {
    fn diagnostic_path(&self) -> String {
        self.metadata
            .as_ref()
            .map(|metadata| metadata.path.clone())
            .unwrap_or_default()
    }

    fn diagnostic_span(&self) -> Option<ResolvedSpan> {
        self.metadata.as_ref().and_then(|metadata| metadata.span)
    }

    fn display_name(&self) -> &str {
        self.metadata
            .as_ref()
            .map(|metadata| metadata.display_name.as_str())
            .filter(|name| !name.is_empty())
            .unwrap_or(self.net.name.as_str())
    }
}

impl SchematicErcPass for CurrentBudgetPass {
    fn run(&self, ctx: &SchematicErcContext<'_>, diagnostics: &mut Diagnostics) {
        use rust_decimal::prelude::ToPrimitive;

        let amps = |net: &pcb_sch::Net, key: &str| -> Option<f64> {
            net.properties
                .get(key)
                .and_then(pcb_sch::AttributeValue::physical)
                .and_then(|p| p.nominal.to_f64())
        };

        // Opt-in: any io() current declaration, or any net covered by the
        // static DC inference (voltage-driven passives).
        let any_current_declared = ctx.nets.iter().any(|net| {
            net.net.properties.contains_key("current_sink_total")
                || net.net.properties.contains_key("current_source_total")
        });
        let any_static_solved = ctx
            .nets
            .iter()
            .any(|net| net.net.properties.contains_key("current_sink_static"));
        let opted_in = any_current_declared || any_static_solved;

        for net in &ctx.nets {
            let net_kind = net.net.kind.as_str();
            if matches!(net_kind, "NotConnected" | "Ground") {
                continue;
            }

            let declared_sink = amps(net.net, "current_sink_total");
            let declared_source = amps(net.net, "current_source_total");
            let static_sink = amps(net.net, "current_sink_static");
            let static_source = amps(net.net, "current_source_static");
            let has_voltage = net.net.properties.contains_key("voltage");
            let uninferable = matches!(
                net.net.properties.get("current_static_uninferable"),
                Some(pcb_sch::AttributeValue::Boolean(true))
            );

            let combine = |declared: Option<f64>, inferred: Option<f64>| match (declared, inferred)
            {
                (None, None) => None,
                (a, b) => Some(a.unwrap_or(0.0) + b.unwrap_or(0.0)),
            };
            let sink_total = combine(declared_sink, static_sink);
            let source_total = combine(declared_source, static_source);

            match (sink_total, source_total) {
                // A declared-voltage rail is a supply by definition: only an
                // explicitly declared source budget can be exceeded.
                (Some(sink), Some(source)) if declared_source.is_some() || !has_voltage => {
                    if source + 1e-12 < sink {
                        let body = format!(
                            "Net '{}' current budget exceeded: sources supply {:.6}A but sinks draw {:.6}A (declared + statically inferred)",
                            net.display_name(),
                            source,
                            sink,
                        );
                        diagnostics.diagnostics.push(
                            Diagnostic::categorized(
                                &net.diagnostic_path(),
                                &body,
                                "erc.current_budget",
                                EvalSeverity::Error,
                            )
                            .with_span(net.diagnostic_span()),
                        );
                    }
                }
                (None, None) if uninferable && opted_in => {
                    let body = format!(
                        "Net '{}' current cannot be inferred: its resistive network cannot be solved from declared data (declare voltage= on the driving rails, or sink_current/source_current on an io())",
                        net.display_name(),
                    );
                    diagnostics.diagnostics.push(
                        Diagnostic::categorized(
                            &net.diagnostic_path(),
                            &body,
                            "erc.current_budget.uninferable",
                            EvalSeverity::Warning,
                        )
                        .with_span(net.diagnostic_span()),
                    );
                }
                (None, None) if opted_in && !has_voltage => {
                    let body = format!(
                        "Net '{}' has no declared or inferable current: no connected io() declares sink_current or source_current, and no DC path allows inferring it",
                        net.display_name(),
                    );
                    diagnostics.diagnostics.push(
                        Diagnostic::categorized(
                            &net.diagnostic_path(),
                            &body,
                            "erc.current_budget.undeclared",
                            EvalSeverity::Warning,
                        )
                        .with_span(net.diagnostic_span()),
                    );
                }
                _ => {}
            }

            if let Some(pcb_sch::AttributeValue::Array(values)) =
                net.net.properties.get("signal_conflict")
            {
                let classes: Vec<&str> = values
                    .iter()
                    .filter_map(pcb_sch::AttributeValue::string)
                    .collect();
                let body = format!(
                    "Net '{}' has conflicting io() signal declarations: {}",
                    net.display_name(),
                    classes.join(", "),
                );
                diagnostics.diagnostics.push(
                    Diagnostic::categorized(
                        &net.diagnostic_path(),
                        &body,
                        "erc.signal_conflict",
                        EvalSeverity::Warning,
                    )
                    .with_span(net.diagnostic_span()),
                );
            }
        }
    }
}

impl SchematicErcPass for PinNoConnectPass {
    fn run(&self, ctx: &SchematicErcContext<'_>, diagnostics: &mut Diagnostics) {
        for net in &ctx.nets {
            let net_kind = net.net.kind.as_str();

            if net_kind == "NotConnected" {
                continue;
            }

            for attachment in &net.pin_attachments {
                if !pin_types_are_only_no_connect(&attachment.pin_types) {
                    continue;
                }

                let body = pin_no_connect_body(
                    &attachment.component_name,
                    &attachment.signal_name,
                    net_kind,
                    net.metadata
                        .as_ref()
                        .map(|metadata| metadata.display_name.as_str())
                        .unwrap_or(net.net.name.as_str()),
                );
                let path = net
                    .metadata
                    .as_ref()
                    .map(|metadata| metadata.path.clone())
                    .unwrap_or_default();
                let span = net.metadata.as_ref().and_then(|metadata| metadata.span);

                diagnostics.diagnostics.push(
                    Diagnostic::categorized(&path, &body, "pin.no_connect", EvalSeverity::Warning)
                        .with_span(span),
                );
            }
        }
    }
}

pub fn run_schematic_erc(eval_output: &EvalOutput, schematic: &Schematic) -> Diagnostics {
    let ctx = SchematicErcContext::build(eval_output, schematic);
    let mut diagnostics = Diagnostics::default();
    let passes: [&dyn SchematicErcPass; 2] = [&PinNoConnectPass, &CurrentBudgetPass];

    for pass in passes {
        pass.run(&ctx, &mut diagnostics);
    }

    diagnostics
}

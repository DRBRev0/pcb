#![cfg(not(target_os = "windows"))]

//! Tests for io()-declared current budgets (`sink_current` / `source_current`)
//! and signal classes (`signal`), and the ERC checks built on them.

use pcb_test_utils::assert_snapshot;
use pcb_test_utils::sandbox::Sandbox;

const SOURCE_1A_ZEN: &str = r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

OUT = io(Net, source_current="1A", direction="output")
GND = io(Ground)

Resistor(name="R1", value="10kOhm", package="0402", P1=OUT, P2=GND)
"#;

const SOURCE_100MA_ZEN: &str = r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

OUT = io(Net, source_current="100mA", direction="output")
GND = io(Ground)

Resistor(name="R1", value="10kOhm", package="0402", P1=OUT, P2=GND)
"#;

const LOAD_300MA_ZEN: &str = r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

VIN = io(Net, sink_current="300mA")
GND = io(Ground)

Resistor(name="R1", value="10kOhm", package="0402", P1=VIN, P2=GND)
"#;

#[test]
fn test_current_budget_ok() {
    let output = Sandbox::new()
        .with_workspace()
        .write("source.zen", SOURCE_1A_ZEN)
        .write("load.zen", LOAD_300MA_ZEN)
        .write(
            "board.zen",
            r#"
Source = Module("./source.zen")
Load = Module("./load.zen")

vbus = Net("VBUS")
gnd = Ground("GND")

Source(name="PSU", OUT=vbus, GND=gnd)
Load(name="L1", VIN=vbus, GND=gnd)
Load(name="L2", VIN=vbus, GND=gnd)
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("current_budget_ok", output);
}

#[test]
fn test_current_budget_exceeded() {
    let output = Sandbox::new()
        .with_workspace()
        .write("source.zen", SOURCE_100MA_ZEN)
        .write("load.zen", LOAD_300MA_ZEN)
        .write(
            "board.zen",
            r#"
Source = Module("./source.zen")
Load = Module("./load.zen")

vbus = Net("VBUS")
gnd = Ground("GND")

Source(name="PSU", OUT=vbus, GND=gnd)
Load(name="L1", VIN=vbus, GND=gnd)
Load(name="L2", VIN=vbus, GND=gnd)
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("current_budget_exceeded", output);
}

#[test]
fn test_current_undeclared_warning() {
    // Once a design declares currents anywhere, nets without any declared or
    // inferable current get a warning.
    let output = Sandbox::new()
        .with_workspace()
        .write("source.zen", SOURCE_1A_ZEN)
        .write("load.zen", LOAD_300MA_ZEN)
        .write(
            "board.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")
Source = Module("./source.zen")
Load = Module("./load.zen")

vbus = Net("VBUS")
gnd = Ground("GND")
other = Net("NO_CURRENT_INFO")

Source(name="PSU", OUT=vbus, GND=gnd)
Load(name="L1", VIN=vbus, GND=gnd)

Resistor(name="R10", value="1kOhm", package="0402", P1=other, P2=vbus)
Resistor(name="R11", value="1kOhm", package="0402", P1=other, P2=gnd)
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("current_undeclared_warning", output);
}

#[test]
fn test_no_declarations_no_warning() {
    // A design with zero current declarations stays silent.
    let output = Sandbox::new()
        .with_workspace()
        .write(
            "board.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

a = Net("A")
gnd = Ground("GND")

Resistor(name="R1", value="1kOhm", package="0402", P1=a, P2=gnd)
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("no_declarations_no_warning", output);
}

#[test]
fn test_signal_conflict_warning() {
    let output = Sandbox::new()
        .with_workspace()
        .write(
            "drv_clock.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

OUT = io(Net, signal="clock", direction="output")
GND = io(Ground)

Resistor(name="R1", value="10kOhm", package="0402", P1=OUT, P2=GND)
"#,
        )
        .write(
            "drv_digital.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

OUT = io(Net, signal="digital", direction="output")
GND = io(Ground)

Resistor(name="R1", value="10kOhm", package="0402", P1=OUT, P2=GND)
"#,
        )
        .write(
            "board.zen",
            r#"
DrvClock = Module("./drv_clock.zen")
DrvDigital = Module("./drv_digital.zen")

x = Net("X")
gnd = Ground("GND")

DrvClock(name="A", OUT=x, GND=gnd)
DrvDigital(name="B", OUT=x, GND=gnd)
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("signal_conflict_warning", output);
}

#[test]
fn test_net_level_signal_overrides_io() {
    // A net-level `signal` declaration wins over io() ones: no conflict warning.
    let output = Sandbox::new()
        .with_workspace()
        .write(
            "drv_clock.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

OUT = io(Net, signal="clock", direction="output")
GND = io(Ground)

Resistor(name="R1", value="10kOhm", package="0402", P1=OUT, P2=GND)
"#,
        )
        .write(
            "drv_digital.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

OUT = io(Net, signal="digital", direction="output")
GND = io(Ground)

Resistor(name="R1", value="10kOhm", package="0402", P1=OUT, P2=GND)
"#,
        )
        .write(
            "board.zen",
            r#"
DrvClock = Module("./drv_clock.zen")
DrvDigital = Module("./drv_digital.zen")

x = Net("X", signal="analog")
gnd = Ground("GND")

DrvClock(name="A", OUT=x, GND=gnd)
DrvDigital(name="B", OUT=x, GND=gnd)
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("net_level_signal_overrides_io", output);
}

#[test]
fn test_invalid_signal_value_on_io() {
    let output = Sandbox::new()
        .with_workspace()
        .write(
            "board.zen",
            r#"
X = io(Net, signal="warp_speed")
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("invalid_signal_value_on_io", output);
}

#[test]
fn test_invalid_signal_value_on_net() {
    let output = Sandbox::new()
        .with_workspace()
        .write(
            "board.zen",
            r#"
x = Net("X", signal="warp_speed")
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("invalid_signal_value_on_net", output);
}

#[test]
fn test_invalid_current_dimension() {
    let output = Sandbox::new()
        .with_workspace()
        .write(
            "board.zen",
            r#"
X = io(Net, sink_current="5V")
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("invalid_current_dimension", output);
}

#[test]
fn test_current_args_rejected_on_interface_io() {
    let output = Sandbox::new()
        .with_workspace()
        .write(
            "board.zen",
            r#"
load("@stdlib/interfaces.zen", "Spi")

SPI = io(Spi, sink_current="10mA")
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("current_args_rejected_on_interface_io", output);
}

#[test]
fn test_net_properties_in_netlist() {
    // The aggregated properties must land on the schematic nets.
    let full_output = Sandbox::new()
        .with_workspace()
        .write("source.zen", SOURCE_1A_ZEN)
        .write("load.zen", LOAD_300MA_ZEN)
        .write(
            "board.zen",
            r#"
Source = Module("./source.zen")
Load = Module("./load.zen")

vbus = Net("VBUS", signal="static")
gnd = Ground("GND")

Source(name="PSU", OUT=vbus, GND=gnd)
Load(name="L1", VIN=vbus, GND=gnd)
Load(name="L2", VIN=vbus, GND=gnd)
"#,
        )
        .run("pcbc", ["build", "board.zen", "--netlist"])
        .stdout_capture()
        .stderr_capture()
        .read()
        .expect("build --netlist should succeed");

    let json_start = full_output.find('{').expect("JSON in netlist output");
    let netlist: serde_json::Value =
        serde_json::from_str(&full_output[json_start..]).expect("netlist output should be JSON");
    let nets = netlist["nets"].as_object().expect("nets object");
    let (_, vbus) = nets
        .iter()
        .find(|(name, _)| name.contains("VBUS"))
        .expect("VBUS net present");
    let props = vbus["properties"].as_object().expect("properties");

    assert_eq!(props["current_sink_total"]["String"], "0.600A");
    assert_eq!(props["current_source_total"]["String"], "1A");
    assert_eq!(props["signal"]["String"], "static");
    let ports = props["current_ports"]["Json"]
        .as_array()
        .expect("current_ports");
    assert_eq!(ports.len(), 3);
    assert_eq!(ports[0]["port"], "L1.VIN");
    assert_eq!(ports[0]["role"], "sink");
    assert_eq!(ports[0]["amps"], 0.3);
    assert_eq!(ports[2]["port"], "PSU.OUT");
    assert_eq!(ports[2]["role"], "source");
    assert_eq!(ports[2]["amps"], 1.0);
}

#[test]
fn test_matched_group_propagates_to_netlist() {
    let full_output = Sandbox::new()
        .with_workspace()
        .write(
            "pair.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

A = io(Net, matched_group="lane0")
B = io(Net, matched_group="lane0")

Resistor(name="R1", value="22Ohm", package="0402", P1=A, P2=B)
"#,
        )
        .write(
            "board.zen",
            r#"
Pair = Module("./pair.zen")

d0 = Net("D0")
d1 = Net("D1")
d2 = Net("D2", matched_group="lane1")
d3 = Net("D3")

Pair(name="P", A=d0, B=d1)
Pair(name="P2", A=d2, B=d3)
"#,
        )
        .run("pcbc", ["build", "board.zen", "--netlist"])
        .stdout_capture()
        .stderr_capture()
        .read()
        .expect("build --netlist should succeed");

    let json_start = full_output.find('{').expect("JSON in netlist output");
    let netlist: serde_json::Value =
        serde_json::from_str(&full_output[json_start..]).expect("netlist output should be JSON");
    let nets = netlist["nets"].as_object().expect("nets object");
    for net_name in ["D0", "D1"] {
        let (_, net) = nets
            .iter()
            .find(|(name, _)| name.contains(net_name))
            .unwrap_or_else(|| panic!("{net_name} present"));
        assert_eq!(
            net["properties"]["matched_group"]["String"], "lane0",
            "io()-declared group lands on {net_name}"
        );
    }
    // The net-level declaration wins over the io()-declared group.
    let (_, d2) = nets
        .iter()
        .find(|(name, _)| name.contains("D2"))
        .expect("D2");
    assert_eq!(d2["properties"]["matched_group"]["String"], "lane1");
}

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

const DIVIDER_ZEN: &str = r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

VIN = io(Net)
OUT = io(Net)
GND = io(Ground)

Resistor(name="RTOP", value="10kOhm", package="0402", P1=VIN, P2=OUT)
Resistor(name="RBOT", value="10kOhm", package="0402", P1=OUT, P2=GND)
"#;

#[test]
fn test_static_inference_on_divider() {
    // A divider from a declared 5V rail to ground: the 250uA static draw is
    // inferred with no hand-written current declarations.
    let full_output = Sandbox::new()
        .with_workspace()
        .write("divider.zen", DIVIDER_ZEN)
        .write(
            "board.zen",
            r#"
Divider = Module("./divider.zen")

vcc = Net("VCC", voltage="5V")
mid = Net("MID")
gnd = Ground("GND")

Divider(name="DIV", VIN=vcc, OUT=mid, GND=gnd)
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

    let (_, vcc) = nets
        .iter()
        .find(|(name, _)| name.contains("VCC"))
        .expect("VCC net");
    // 5V across 20k: 250uA drawn from the rail.
    assert_eq!(
        vcc["properties"]["current_sink_static"]["String"],
        "0.00025A"
    );
    assert_eq!(vcc["properties"]["current_source_static"]["String"], "0A");
    let ports = vcc["properties"]["current_ports"]["Json"]
        .as_array()
        .expect("current_ports on VCC");
    assert!(
        ports.iter().any(
            |p| p["port"].as_str().unwrap_or("").starts_with("component:") && p["role"] == "sink"
        ),
        "static component entry present: {ports:?}"
    );

    // The mid node passes the current through: 250uA in, 250uA out.
    let (_, mid) = nets
        .iter()
        .find(|(name, _)| name.contains("MID"))
        .expect("MID net");
    assert_eq!(
        mid["properties"]["current_sink_static"]["String"],
        "0.00025A"
    );
    assert_eq!(
        mid["properties"]["current_source_static"]["String"],
        "0.00025A"
    );
}

#[test]
fn test_static_draw_exceeding_declared_budget_errors() {
    // The rail declares a 100uA source budget but the divider statically
    // draws 250uA: budget error without any declared sink.
    let output = Sandbox::new()
        .with_workspace()
        .write("divider.zen", DIVIDER_ZEN)
        .write(
            "source.zen",
            r#"
Capacitor = Module("@stdlib/generics/Capacitor.zen")

OUT = io(Net, source_current="100uA", direction="output")
GND = io(Ground)

Capacitor(name="CS", value="1uF", package="0402", P1=OUT, P2=GND)
"#,
        )
        .write(
            "board.zen",
            r#"
Divider = Module("./divider.zen")
Source = Module("./source.zen")

vcc = Net("VCC", voltage="5V")
mid = Net("MID")
gnd = Ground("GND")

Source(name="PSU", OUT=vcc, GND=gnd)
Divider(name="DIV", VIN=vcc, OUT=mid, GND=gnd)
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("static_budget_exceeded", output);
}

#[test]
fn test_uninferable_resistive_network_warns() {
    // A resistor between two nets with no voltage reference anywhere in the
    // subnetwork: the current cannot be inferred. The design opts into
    // current accounting through the solved divider elsewhere.
    let output = Sandbox::new()
        .with_workspace()
        .write("divider.zen", DIVIDER_ZEN)
        .write(
            "link.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

A = io(Net)
B = io(Net)

Resistor(name="RL", value="1kOhm", package="0402", P1=A, P2=B)
"#,
        )
        .write(
            "board.zen",
            r#"
Divider = Module("./divider.zen")
Link = Module("./link.zen")

vcc = Net("VCC", voltage="5V")
mid = Net("MID")
gnd = Ground("GND")
floating_a = Net("FLOAT_A")
floating_b = Net("FLOAT_B")

Divider(name="DIV", VIN=vcc, OUT=mid, GND=gnd)
Link(name="LNK", A=floating_a, B=floating_b)
"#,
        )
        .snapshot_run("pcbc", ["build", "board.zen"]);
    assert_snapshot!("static_uninferable_warning", output);
}

#[test]
fn test_capacitor_only_net_is_known_zero() {
    // A decoupling-only net: capacitors draw no DC current, so the net's
    // static current is known to be zero (jCw -> open at DC).
    let full_output = Sandbox::new()
        .with_workspace()
        .write(
            "cap.zen",
            r#"
Capacitor = Module("@stdlib/generics/Capacitor.zen")

A = io(Net)
GND = io(Ground)

Capacitor(name="C1", value="100nF", package="0402", P1=A, P2=GND)
"#,
        )
        .write(
            "board.zen",
            r#"
Cap = Module("./cap.zen")

quiet = Net("QUIET")
gnd = Ground("GND")

Cap(name="CD", A=quiet, GND=gnd)
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
    let (_, quiet) = nets
        .iter()
        .find(|(name, _)| name.contains("QUIET"))
        .expect("QUIET net");
    assert_eq!(quiet["properties"]["current_sink_static"]["String"], "0A");
}

fn static_netlist_nets(board: &str, extra_files: &[(&str, &str)]) -> serde_json::Value {
    let mut sandbox = Sandbox::new().with_workspace();
    for (name, content) in extra_files {
        sandbox.write(name, content);
    }
    let full_output = sandbox
        .write("board.zen", board)
        .run("pcbc", ["build", "board.zen", "--netlist"])
        .stdout_capture()
        .stderr_capture()
        .read()
        .expect("build --netlist should succeed");
    let json_start = full_output.find('{').expect("JSON in netlist output");
    serde_json::from_str::<serde_json::Value>(&full_output[json_start..])
        .expect("netlist output should be JSON")["nets"]
        .clone()
}

fn static_sink_amps(nets: &serde_json::Value, net_name: &str) -> f64 {
    let (_, net) = nets
        .as_object()
        .expect("nets object")
        .iter()
        .find(|(name, _)| name.contains(net_name))
        .unwrap_or_else(|| panic!("{net_name} present"));
    net["properties"]["current_sink_static"]["String"]
        .as_str()
        .unwrap_or_else(|| panic!("{net_name} has current_sink_static"))
        .trim_end_matches('A')
        .parse()
        .expect("amps parse")
}

const DIODE_LOAD_ZEN: &str = r#"
Resistor = Module("@stdlib/generics/Resistor.zen")
Rectifier = Module("@stdlib/generics/Rectifier.zen")

VIN = io(Net)
GND = io(Ground)

mid = Net("DMID")
Rectifier(name="D1", reverse_voltage="100V", forward_voltage="0.7V", package="DO-214AC", A=VIN, K=mid)
Resistor(name="RL", value="1kOhm", package="0402", P1=mid, P2=GND)
"#;

#[test]
fn test_diode_conducts_only_forward() {
    // Forward: 5V -> anode; (5 - 0.7) / (1k + 1) = 4.2957mA flows.
    let nets = static_netlist_nets(
        r#"
Load = Module("./load.zen")

vcc = Net("VCC", voltage="5V")
gnd = Ground("GND")

Load(name="L", VIN=vcc, GND=gnd)
"#,
        &[("load.zen", DIODE_LOAD_ZEN)],
    );
    let amps = static_sink_amps(&nets, "VCC");
    assert!(
        (amps - 0.0042957).abs() < 1e-5,
        "forward diode current, got {amps}"
    );

    // Reversed: cathode to the rail; the diode blocks, everything is a
    // known zero (not uninferable).
    let blocked = static_netlist_nets(
        r#"
Load = Module("./load.zen")

vneg = Net("VNEG", voltage="-5V")
gnd = Ground("GND")

Load(name="L", VIN=vneg, GND=gnd)
"#,
        &[("load.zen", DIODE_LOAD_ZEN)],
    );
    let amps = static_sink_amps(&blocked, "VNEG");
    assert!(amps.abs() < 1e-9, "blocked diode draws nothing, got {amps}");
}

#[test]
fn test_zener_clamp_current_is_inferred() {
    // 12V --1k--> ZNET --[zener 5.1V, K=ZNET A=GND]--> GND.
    // Breakdown: I = (12 - 5.1) / (1k + 1) = 6.888mA drawn from the rail.
    let nets = static_netlist_nets(
        r#"
Resistor = Module("@stdlib/generics/Resistor.zen")
Zener = Module("@stdlib/generics/Zener.zen")

vin = Net("V12", voltage="12V")
znet = Net("ZNET")
gnd = Ground("GND")

Resistor(name="R1", value="1kOhm", package="0402", P1=vin, P2=znet)
Zener(name="DZ", zener_voltage="5.1V", package="SOD-123", A=gnd, K=znet)
"#,
        &[],
    );
    let amps = static_sink_amps(&nets, "V12");
    assert!(
        (amps - 0.0068931).abs() < 1e-5,
        "zener clamp current, got {amps}"
    );
    // The clamp node passes the current through.
    let znet = static_sink_amps(&nets, "ZNET");
    assert!((znet - 0.0068931).abs() < 1e-5, "got {znet}");
}

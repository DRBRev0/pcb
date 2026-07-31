#![cfg(not(target_os = "windows"))]

//! Tests for `pcb sim --static`: the generated DC operating-point testbench.

use pcb_test_utils::assert_snapshot;
use pcb_test_utils::sandbox::Sandbox;

const ZENER_CLAMP_ZEN: &str = r#"
Resistor = Module("@stdlib/generics/Resistor.zen")
Zener = Module("@stdlib/generics/Zener.zen")

vin = Net("V12", voltage="12V")
znet = Net("ZNET")
gnd = Ground("GND")

Resistor(name="R1", value="1kOhm", package="0402", P1=vin, P2=znet)
Zener(name="DZ", zener_voltage="5.1V", package="SOD-123", A=gnd, K=znet)
"#;

#[test]
fn test_static_testbench_generation() {
    let output = Sandbox::new()
        .with_workspace()
        .write("board.zen", ZENER_CLAMP_ZEN)
        .snapshot_run("pcbc", ["sim", "board.zen", "--static", "--netlist"]);
    assert_snapshot!("sim_static_zener_clamp", output);
}

#[test]
fn test_static_testbench_requires_a_voltage() {
    // No declared voltage anywhere: nothing can drive the testbench.
    let output = Sandbox::new()
        .with_workspace()
        .write(
            "board.zen",
            r#"
Resistor = Module("@stdlib/generics/Resistor.zen")

a = Net("A")
b = Net("B")

Resistor(name="R1", value="1kOhm", package="0402", P1=a, P2=b)
"#,
        )
        .snapshot_run("pcbc", ["sim", "board.zen", "--static", "--netlist"]);
    assert_snapshot!("sim_static_requires_voltage", output);
}

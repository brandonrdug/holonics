//! Exterior consumer of the finite solenoidal chart and the existing exact wave operator.
//! Usage: solenoidal_wave NODES TICKS TICK_NUM TICK_DEN MODULI_CSV
//! Material is declared unit C=L=1 with zero leakage; the initial voltage is one unit at node 0.
//! This is a constitutive/clock demonstration, not Athena output or a learned prediction.

use std::error::Error;

use holonics::geometry::solenoid::{FiniteSolenoidalTower, SolenoidalChart};
use holonics::physics::solenoidal::ReflectedPair;
use holonics::physics::solenoidal::flow::SolenoidalWave;
use holonics::physics::wave::{Incidence, WaveChain, WaveMaterial, WaveState};
use holonics::ratio::places::PlaceReading;
use holonics::ratio::{GaussianRat, Rat, integer, rat};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

fn main() -> Result<(), Box<dyn Error>> {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    if arguments.len() != 5 {
        return Err("usage: solenoidal_wave NODES TICKS TICK_NUM TICK_DEN MODULI_CSV".into());
    }
    let nodes: usize = arguments[0].parse()?;
    let ticks: usize = arguments[1].parse()?;
    let numerator: BigInt = arguments[2].parse()?;
    let denominator: BigInt = arguments[3].parse()?;
    if denominator.is_zero() {
        return Err("the declared tick denominator must be nonzero".into());
    }
    let tick = Rat::new(numerator, denominator);
    let moduli: Vec<BigUint> = arguments[4]
        .split(',')
        .map(str::parse)
        .collect::<Result<_, _>>()?;
    let levels = moduli.len();
    let tower = FiniteSolenoidalTower::new(moduli)?;
    let chart = SolenoidalChart::from_transverse(tower, integer(0), vec![BigUint::zero(); levels])?;
    let incidence = Incidence::ring(nodes)?;
    let material = WaveMaterial::uniform(&incidence, &integer(1), &integer(0), &integer(1))?;
    let medium = WaveChain::new(incidence, material, tick)?;
    let mut voltage = vec![integer(0); nodes];
    voltage[0] = integer(1); // Incidence::ring has admitted the nonempty node extent.
    let state = WaveState::new(voltage, vec![integer(0); nodes]);
    let mut flow = SolenoidalWave::new(chart, integer(1), medium, state)?;
    let source = vec![integer(0); nodes];
    for crossing in 0..ticks {
        let reading = flow.advance(&source)?;
        let places = PlaceReading::of(&reading.longitudinal_step)?;
        println!(
            "tick={} lift={} phase={} winding={} stored_change={} source_power={} dissipated={} residual={}",
            crossing + 1,
            reading.chart.longitudinal_lift(),
            reading.chart.phase(),
            reading.chart.winding(),
            reading.balance.stored_change,
            reading.balance.source_power,
            reading.balance.dissipated,
            reading.balance.residual,
        );
        println!(
            "clock_step_places={:?} product={} reconstructed={}",
            places.places(),
            places.product(),
            places.reconstruct()
        );
        for level in 0..levels {
            println!(
                "level={} circle_turn={}",
                level,
                reading.chart.circle_turn(level)?
            );
        }
    }
    // Declared coordinates only: the constructor accepts no assertion that these are zeros.
    let pair = ReflectedPair::new(rat(1, 2), integer(1))?;
    let contact = pair.read()?;
    let tank = pair.certify_foster()?;
    println!(
        "declared_pair_power={} no_slip={} omega_squared={} impedance_at_one={:?}",
        contact.dissipated_power,
        contact.no_slip,
        tank.lc_mode().omega_squared(),
        tank.impedance(&GaussianRat::real(integer(1)))?,
    );
    Ok(())
}

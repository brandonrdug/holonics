//! **The Holarchy: what `Holon::interconnect` returns, and its receiver-relative quantities.**
//!
//! [definition] A Holarchy is a Holon perceived as a compound of distinct Holons, always in a
//! context ([object §11](../../../../docs/ELEMENTARY_OBJECTS.md#11-holarchy)). It is what
//! [`Holon::interconnect`] returns: the joined whole, again a [`Holon`], with its retained
//! constituents, the port provenance of every whole port, and the typed [`Gluing`]; or, when the
//! join does not close, a typed [`GluingDefect`] ([`gluing`] runs the nine checks of Lean
//! `Holarchy/Join.interconnect` on the two Holons' own data, shared port by shared port).
//!
//! [definition] **The parts and the gluing are the Holarchy; the dense whole is a chart of them.**
//! Lean's `Holarchy/Join.Holarchy` keeps only the declaration and its proof that it glues, and
//! `Holarchy.whole` is a function of the constituents (`joinHolon A.holon B.holon F E`, Dirac by
//! `joinD_isDirac`). So [`Holarchy`] retains the join (both constituents, the gluing and the port
//! layout) and its whole, whose counts, active block, pumps, named ports, cells and navigators are
//! read at the join, while its port Holon (the composed Dirac structure with block storage and
//! resistance) is assembled from the retained join only when it is read, and kept
//! ([`Holon::port_holon`]). A constituent may be the unassembled whole of an earlier join, so a
//! Holarchy of many small Holons (the HNN field's rings and contacts, `hnn::Field::holon`) is
//! certified block by block and costs what its blocks cost (guard 14). The whole joins
//! (`Holarchy/Join.Holarchy.wholeConstituent`):
//!
//! - **ports**: the port Holon of both constituents composed through the gain link at the shared
//!   ports, the kinds merged left before right ([`gluing`], Lean `Holarchy/Join.joinHolon`), and
//!   the named ports in that order when both constituents name theirs;
//! - **elements**: block storage, resistance and active relation; the pumps, when either Holon
//!   pumps, as the block of their storage in force on the declared joint clock;
//! - **cells**: the glued complex (and its connection), which each constituent's own complex
//!   embeds into, the whole's interior `m_L c_L + m_R c_R` and the faces of the unshared ports;
//! - **navigators**: both families, the left's first; the retained constituents carry the
//!   provenance. Their joint clock torus, lifted, is the whole's parametric orientation
//!   ([`Holarchy::parametric`]), whose walks are the Holarchy's aeons.
//!
//! The constituents' own port restrictions stay scoped to the retained constituents; the whole's
//! restriction to each child is the transposed cellular embedding on currents
//! (`Holarchy/Join.CellEmbedding.restrict_exact`) and, on ports, the interface fibre
//! ([`Holarchy::interface_fibre`]).
//!
//! [definition] **A Holarchy's quantities belong to the receiver** ([`view`]): the view, the count
//! and the refinement are read at a receiver's grain and clock, never as a fixed count.
//!
//! | Lean `Holarchy/Join` | Rust |
//! |---|---|
//! | `interconnect`, `interconnect_ok_iff`, `GluingDefect`, `GluingDefect.not_glues` | [`Holon::interconnect`], [`GluingDefect`] |
//! | `interconnect_ok_retains` | [`Holarchy::left`], [`Holarchy::right`], [`Holarchy::gluing`] |
//! | `joinBond`, `interfacePower`, `interfacePower_eq`, `interfacePower_cancels_iff` | [`Gluing::join_bond`], [`Gluing::interface_power`], check 2 of [`gluing`] |
//! | `gainLink_isDirac`, `joinD_isDirac`, `joinHolon`, `joinHolon_one`, `Holarchy.whole`, `Holarchy.wholeConstituent` | [`Holarchy::whole`] (its port Holon assembled on first read) |
//! | `Holarchy.power_balance`, `Holarchy.balance_is_sum` | [`Holarchy::power_balance`] |
//! | `interfaceFibre`, `interface_obstructed_iff`, `interface_plural_iff` | [`Holarchy::interface_fibre`] |
//! | `CellEmbedding.flux_pullback`, `Holarchy.wholeInterior`, `Holarchy.whole_flux`, `Holarchy.sharedFace_silent` | [`Holarchy::flux`] |
//! | `OnJointClock`, `OnJointClock.lock`, `Holarchy.wholeConstituent_pumpRate` | check 9 of [`gluing`], [`Holarchy::pump_lock`] |
//! | `Holarchy.parametric` | [`Holarchy::parametric`] |
//!
//! [open] Beyond Lean, the Rust whole carries its pumps' joined storage schedule on the joint
//! clock (Lean namespaces the pumps and puts their rates on the joint clock,
//! `Holarchy.wholeConstituent_pumpRate`, but joins no storage schedule), and the interface fibre
//! returns its obstruction covector or free directions as data; the schedule law is owed in #62.
//! The restriction facet `π` is joined in neither. The globe of a block
//! (`Holarchy/Globe.HolarchyGlobe`, `holarchyGlobe_iff_linear`) has no Rust consumer here.

pub mod gluing;
pub mod view;

#[cfg(test)]
mod tests;

pub use gluing::{CellGluing, CellularMap, Gluing, GluingDefect, JointClock};
pub use view::{Block, Count, Grain, GrainRestriction, RegionReceiver, TickView, Unresolved};

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::Zero;

use crate::aeon::ClockLift;
use crate::holon::port::Bond;
use crate::holon::{Holon, HolonError, PowerBalance};
use crate::navigator::address::{AddressError, LockAddress};
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{at, dot, matrix};
use gluing::{Layout, Slot, check_cell_shapes, check_cells, check_clocks, check_units};

/// [definition] Which constituent (Lean `Holarchy/Join.Side`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Side {
    Left,
    Right,
}

/// [definition] **A Holarchy of two constituents**: the retained constituents and the typed
/// gluing, which determine the whole (Lean `Holarchy/Join.Holarchy` keeps only `decl` and `glues`;
/// `Holarchy.whole` is a function of them), and the whole as a Holon whose port Holon is assembled
/// from them on first read.
#[derive(Clone, Debug)]
pub struct Holarchy {
    join: Arc<Join>,
    whole: Holon,
}

impl PartialEq for Holarchy {
    /// The same constituents under the same gluing: the whole is a function of them.
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.join, &other.join) || self.join == other.join
    }
}

impl Eq for Holarchy {}

/// [definition] **A join as declared**: the two retained constituents, the gluing that passed the
/// nine checks, and the port layout it induces. It is the complete representation of the whole's
/// port Holon ([`Join::assemble`], Lean `Holarchy.whole = joinHolon A.holon B.holon F E`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Join {
    left: Holon,
    right: Holon,
    gluing: Gluing,
    layout: Layout,
}

impl Join {
    /// [definition] **The whole's port Holon** (Lean `Holarchy/Join.joinHolon`): both structures
    /// side by side, composed with the gain link at the shared ports, the kinds merged; block
    /// storage and resistance. A constituent that is itself a join is assembled first.
    pub(crate) fn assemble(&self) -> Result<crate::holon::PortHolon, HolonError> {
        gluing::join_port_holons(
            self.left.port_holon(),
            self.right.port_holon(),
            &self.gluing,
            &self.layout,
        )
    }
}

impl Holon {
    /// [definition] **Interconnect two Holons** (Lean `Holarchy/Join.interconnect`,
    /// `interconnect_ok_iff`): validate that the gluing fits both Holons, then run the nine checks
    /// on the Holons' own units, gains, complexes, interiors, port faces and pumps, in Lean's
    /// order; return the Holarchy exactly when all nine pass, or the first failed check as a typed
    /// defect with a computed witness (`GluingDefect.not_glues`).
    ///
    /// [definition] **The checks are local to the shared ports and the two Holons' own data**, and
    /// nothing dense is assembled: the whole's port Holon is built from the retained join only when
    /// it is read ([`Holon::port_holon`] on [`Holarchy::whole`]). A constituent may itself be the
    /// whole of an earlier join, still unassembled, so a Holarchy of many small Holons costs what
    /// its blocks cost.
    pub fn interconnect(&self, other: &Holon, gluing: &Gluing) -> Result<Holarchy, GluingDefect> {
        let layout = Layout::new(self.counts(), other.counts(), gluing.shared())
            .map_err(GluingDefect::Malformed)?;
        check_cell_shapes(self, other, gluing).map_err(GluingDefect::Malformed)?;
        check_units(self, other, gluing)?;
        gluing.check_power()?;
        check_cells(self, other, gluing)?;
        check_clocks(self, other, gluing)?;
        let join = Arc::new(Join {
            left: self.clone(),
            right: other.clone(),
            gluing: gluing.clone(),
            layout,
        });
        let whole = join_holons(&join).map_err(GluingDefect::Malformed)?;
        Ok(Holarchy { join, whole })
    }
}

/// The joined whole as a Holon (Lean `Holarchy/Join.Holarchy.wholeConstituent`): its port Holon
/// the join's, assembled on first read; elements, pumps, named ports, cells and navigators.
fn join_holons(join: &Arc<Join>) -> Result<Holon, HolonError> {
    let (left, right, gluing, layout) = (&join.left, &join.right, &join.gluing, &join.layout);
    let active = left.active().direct_sum(right.active())?;
    let mut whole = Holon::joined(layout.counts(), Arc::clone(join), active)?;
    if let Some(pump) = gluing::joint_pump(left, right, gluing)? {
        whole = whole.with_pump(pump)?;
    }
    if let (Some(left_ports), Some(right_ports)) = (left.ports(), right.ports()) {
        let named = layout
            .provenance
            .iter()
            .map(|(side, port)| match side {
                Side::Left => left_ports[*port].clone(),
                Side::Right => right_ports[*port].clone(),
            })
            .collect();
        whole = whole.with_ports(named)?;
    }
    if let Some(cells) = gluing.cells() {
        let d = cells.region_degree();
        let interior = crate::ratio::linear::vector::add(
            &cells.pushed_interior(Side::Left, left)?,
            &cells.pushed_interior(Side::Right, right)?,
        );
        whole = whole
            .with_complex(cells.glued().clone(), cells.connection().cloned())
            .with_interior(interior)?;
        let (a, b) = (left.counts(), right.counts());
        let faces: Vec<usize> = layout
            .provenance
            .iter()
            .filter_map(|(side, port)| {
                let (holon, offset) = match side {
                    Side::Left => (left, a.external_offset()),
                    Side::Right => (right, b.external_offset()),
                };
                let external = holon.counts().external;
                let own = port.checked_sub(offset).filter(|e| *e < external)?;
                let face = holon.port_faces()?[own];
                Some(cells.map(*side).image(d.saturating_sub(1))[face])
            })
            .collect();
        if faces.len() == layout.counts().external {
            whole = whole.with_port_faces(faces)?;
        }
    }
    for navigator in left.navigators().iter().chain(right.navigators()) {
        whole = whole.with_navigator(navigator.clone());
    }
    Ok(whole)
}

/// [definition] **The interface fibre over a whole bond** (Lean `Holarchy/Join.interfaceFibre`):
/// the shared bonds `q` (as the left Holon sees them) with which the left admits its part and the
/// right admits its part with `joinBond q`. It is an affine subspace, so its gluing is exactly one
/// of three: obstructed exactly when the whole refuses the bond (`interface_obstructed_iff`),
/// plural exactly when two shared bonds realize it (`interface_plural_iff`), unique otherwise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfaceGluing {
    /// One shared bond realizes the whole bond.
    Unique(Bond),
    /// A particular shared bond and the free directions: the plurality is returned whole.
    Plural {
        particular: Bond,
        directions: Vec<Bond>,
    },
    /// No shared bond does; the covector on the stacked constituent constraints that pairs to
    /// zero with every shared bond and not with the whole bond's own terms.
    Obstructed { covector: Vec<Rat> },
}

/// [definition] **The whole's power balance with each constituent's**, at one admitted point of
/// the whole (Lean `Holarchy/Join.Holarchy.power_balance`, `Holarchy.balance_is_sum`): the shared bond
/// `q` through which the point restricts, and each constituent's balance with its shared ports
/// counted external. The constituents' port powers sum to the whole's; storage rate, dissipation
/// and active power add.
///
/// [definition] `shared` is **one representative** of the interface fibre over the point
/// ([`Holarchy::interface_fibre`]): its unique member, or the particular member when the fibre is
/// plural. The balances do not depend on it. Every member restricts the same storage, resistive
/// and active bonds to each constituent, and each constituent's Dirac structure is power-neutral,
/// so its port power, shared ports included, is fixed by those bonds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JoinBalance {
    pub whole: PowerBalance,
    pub left: PowerBalance,
    pub right: PowerBalance,
    /// One member of the interface fibre, not the whole fibre.
    pub shared: Bond,
}

/// [definition] **The whole's flux and each constituent's own flux** of one current on the glued
/// faces (Lean `Holarchy/Join.Holarchy.whole_flux`): `whole = ⟨j, ∂ wholeInterior⟩` and
/// `left = ⟨m_(d−1)ᵀ j, ∂_left c_left⟩`, each constituent read in its own complex.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FluxSplit {
    pub whole: Rat,
    pub left: Rat,
    pub right: Rat,
}

impl Holarchy {
    /// The left constituent, retained.
    pub fn left(&self) -> &Holon {
        &self.join.left
    }

    /// The right constituent, retained.
    pub fn right(&self) -> &Holon {
        &self.join.right
    }

    pub fn constituent(&self, side: Side) -> &Holon {
        match side {
            Side::Left => &self.join.left,
            Side::Right => &self.join.right,
        }
    }

    /// The typed gluing, retained.
    pub fn gluing(&self) -> &Gluing {
        &self.join.gluing
    }

    /// [definition] **The joined whole** (Lean `Holarchy/Join.Holarchy.whole`,
    /// `Holarchy.wholeConstituent`), again a Holon, so it can be joined again. Its counts,
    /// elements' active block, pumps, named ports, cells and navigators are read from the
    /// constituents at the join; its port Holon (the composed Dirac structure with block storage and
    /// resistance) is assembled from the retained join on its first read and kept.
    pub fn whole(&self) -> &Holon {
        &self.whole
    }

    /// Whole port `i` is port `.1` of constituent `.0`.
    pub fn provenance(&self) -> &[(Side, usize)] {
        &self.join.layout.provenance
    }

    /// [definition] **The Holarchy's parametric orientation** (Lean
    /// `Holarchy/Join.Holarchy.parametric`, over `Aeon/Clock/Winding.clockLift`): the lift of the
    /// joint clock torus of the whole's navigators, the left's first, one circle per navigator of
    /// its clock's ring period. Its aeons are the Holarchy's aeons.
    pub fn parametric(&self) -> ClockLift {
        ClockLift::of_clocks(
            &self
                .whole
                .navigators()
                .iter()
                .map(|navigator| navigator.clock().clone())
                .collect::<Vec<_>>(),
        )
    }

    /// Each constituent's bond on its own ports, given the whole bond and a shared bond `q` as the
    /// left sees it (the right sees `joinBond q`).
    fn constituent_bonds(&self, whole: &Bond, shared: &Bond) -> Result<(Bond, Bond), HolonError> {
        let assemble = |slots: &[Slot], carried: &Bond| {
            let (flow, effort) = slots
                .iter()
                .map(|slot| match slot {
                    Slot::Whole(i) => (whole.flow()[*i].clone(), whole.effort()[*i].clone()),
                    Slot::Shared(k) => (carried.flow()[*k].clone(), carried.effort()[*k].clone()),
                })
                .unzip();
            Bond::new(flow, effort)
        };
        Ok((
            assemble(&self.join.layout.left_slots, shared)?,
            assemble(
                &self.join.layout.right_slots,
                &self.gluing().join_bond(shared)?,
            )?,
        ))
    }

    /// [proved-derived; implemented-exact] **The interface fibre over a whole bond**
    /// (`interfaceFibre`, `interface_obstructed_iff`, `interface_plural_iff`): solve the two
    /// constituents' constraint rows for the shared bond exactly.
    pub fn interface_fibre(&self, whole: &Bond) -> Result<InterfaceGluing, HolonError> {
        let total = self.whole.counts().total();
        if whole.ports() != total {
            return Err(HolonError::Shape {
                what: "whole bond",
                expected: total,
                found: whole.ports(),
            });
        }
        let t = self.gluing().shared().len();
        // Each constituent's bond with every shared slot zero: its known part.
        let zero = Bond::zero(t);
        let (left_known, right_known) = self.constituent_bonds(whole, &zero)?;
        let (fa, ea) = (
            self.left().port_holon().dirac().form().flow_matrix()?,
            self.left().port_holon().dirac().form().effort_matrix()?,
        );
        let (fb, eb) = (
            self.right().port_holon().dirac().form().flow_matrix()?,
            self.right().port_holon().dirac().form().effort_matrix()?,
        );
        let (a, b) = (self.left().counts(), self.right().counts());
        let left_ports: Vec<usize> = self
            .gluing()
            .shared()
            .iter()
            .map(|(i, _)| a.external_offset() + i)
            .collect();
        let right_ports: Vec<usize> = self
            .gluing()
            .shared()
            .iter()
            .map(|(_, j)| b.external_offset() + j)
            .collect();
        let (gain_f, gain_e) = (self.gluing().flow_gain(), self.gluing().effort_gain());
        let rows = fa.rows() + fb.rows();
        // Variables q = (f_q, e_q). Left rows read q directly; right rows read (−F f_q, E e_q).
        let coefficient = matrix(rows, 2 * t, |row, column| {
            let (j, on_effort) = (column % t.max(1), column >= t);
            if row < fa.rows() {
                let port = left_ports[j];
                if on_effort {
                    at(&ea, row, port)
                } else {
                    at(&fa, row, port)
                }
            } else {
                let r = row - fa.rows();
                (0..t).fold(Rat::zero(), |sum, k| {
                    let port = right_ports[k];
                    if on_effort {
                        sum + at(&eb, r, port) * at(gain_e, k, j)
                    } else {
                        sum - at(&fb, r, port) * at(gain_f, k, j)
                    }
                })
            }
        })?;
        let known =
            |f: &ExactRatMatrix, e: &ExactRatMatrix, bond: &Bond| -> Result<Vec<Rat>, HolonError> {
                Ok(crate::ratio::linear::vector::add(
                    &f.apply(bond.flow())?,
                    &e.apply(bond.effort())?,
                ))
            };
        let mut target = crate::ratio::linear::vector::neg(&known(&fa, &ea, &left_known)?);
        target.extend(crate::ratio::linear::vector::neg(&known(
            &fb,
            &eb,
            &right_known,
        )?));
        Ok(match coefficient.preimage_fibre(&target)? {
            None => InterfaceGluing::Obstructed {
                covector: coefficient.preimage_obstruction(&target)?.expect(
                    "a target outside the image pairs nonzero with a covector of the cokernel",
                ),
            },
            Some((particular, kernel)) if kernel.is_empty() => {
                InterfaceGluing::Unique(Bond::from_coordinates(&particular)?)
            }
            Some((particular, kernel)) => InterfaceGluing::Plural {
                particular: Bond::from_coordinates(&particular)?,
                directions: kernel
                    .iter()
                    .map(|direction| Bond::from_coordinates(direction))
                    .collect::<Result<_, _>>()?,
            },
        })
    }

    /// [proved-derived; implemented-exact] **The whole's balance is the sum of the constituents'**
    /// (`Holarchy.power_balance`, `Holarchy.balance_is_sum`): at an admitted point of the whole, restrict
    /// through a shared bond of the interface fibre and read each constituent's own balance. A
    /// point the whole does not admit is refused.
    pub fn power_balance(
        &self,
        x: &[Rat],
        v: &[Rat],
        resistive_flow: &[Rat],
        external: &Bond,
        active: &Bond,
    ) -> Result<JoinBalance, HolonError> {
        let whole_holon = self.whole.port_holon();
        let whole = whole_holon.power_balance(x, v, resistive_flow, external, active)?;
        let bond = whole_holon.motion_bond(x, v, resistive_flow, external, active)?;
        let shared = match self.interface_fibre(&bond)? {
            InterfaceGluing::Unique(q) => q,
            InterfaceGluing::Plural { particular, .. } => particular,
            InterfaceGluing::Obstructed { .. } => return Err(HolonError::NotAdmitted),
        };
        let (a, b) = (self.left().counts(), self.right().counts());
        let (left_bond, right_bond) = self.constituent_bonds(&bond, &shared)?;
        let external_of = |bond: &Bond, offset: usize, count: usize| {
            bond.select(&(offset..offset + count).collect::<Vec<_>>())
        };
        let left = self.left().port_holon().power_balance(
            &x[..a.storage],
            &v[..a.storage],
            &resistive_flow[..a.resistive],
            &external_of(&left_bond, a.external_offset(), a.external)?,
            &active.select(&(0..a.active).collect::<Vec<_>>())?,
        )?;
        let right = self.right().port_holon().power_balance(
            &x[a.storage..],
            &v[a.storage..],
            &resistive_flow[a.resistive..],
            &external_of(&right_bond, b.external_offset(), b.external)?,
            &active.select(&(a.active..a.active + b.active).collect::<Vec<_>>())?,
        )?;
        Ok(JoinBalance {
            whole,
            left,
            right,
            shared,
        })
    }

    /// The cellular gluing and its region degree `d ≥ 1`, or a refusal naming what is missing.
    pub(crate) fn regions(&self) -> Result<(&CellGluing, usize), HolonError> {
        let Some(cells) = self.gluing().cells() else {
            return Err(HolonError::Unsupported {
                what: "a flux or a view",
                reason: "the Holarchy declares no glued complex",
            });
        };
        let d = cells.region_degree();
        if d == 0 {
            return Err(HolonError::Unsupported {
                what: "a flux or a view",
                reason: "the glued complex has no faces",
            });
        }
        Ok((cells, d))
    }

    /// The whole's interior on the glued regions, `m_L c_L + m_R c_R` (Lean
    /// `Holarchy/Join.Holarchy.wholeInterior`).
    pub fn whole_interior(&self) -> Result<Vec<Rat>, HolonError> {
        self.regions()?;
        self.whole
            .interior()
            .map(<[Rat]>::to_vec)
            .ok_or(HolonError::Unsupported {
                what: "a flux or a view",
                reason: "the whole declares no interior",
            })
    }

    /// [proved-derived; implemented-exact] **The whole's flux is the sum of the constituents' own
    /// fluxes** (`Holarchy.whole_flux`, from `CellEmbedding.flux_pullback`): each constituent reads
    /// the restricted current `m_(d−1)ᵀ j` in its own complex. Each shared port's face enters the
    /// two constituents with opposite coefficients (check 8 of `interconnect`), so it is silent in
    /// the whole (`Holarchy.sharedFace_silent`) and its flux cancels in the sum.
    pub fn flux(&self, current: &[Rat]) -> Result<FluxSplit, HolonError> {
        let (cells, d) = self.regions()?;
        let faces = cells.glued().cells(d - 1);
        if current.len() != faces {
            return Err(HolonError::Shape {
                what: "current on the glued faces",
                expected: faces,
                found: current.len(),
            });
        }
        let whole = dot(
            current,
            &cells.glued_boundary(d)?.apply(&self.whole_interior()?)?,
        );
        let own = |side: Side| -> Result<Rat, HolonError> {
            let holon = self.constituent(side);
            let restricted = cells.map_at(side, d - 1)?.transpose()?.apply(current)?;
            let chain = gluing::boundary(holon.complex(), holon.connection(), d)?
                .apply(gluing::holon_interior(holon)?)?;
            Ok(dot(&restricted, &chain))
        };
        Ok(FluxSplit {
            whole,
            left: own(Side::Left)?,
            right: own(Side::Right)?,
        })
    }

    /// [proved-derived; implemented-exact] **The lock of the two pumps** under the joint clock
    /// (Lean `Holarchy/Join.OnJointClock.lock`, over `Aeon/Clock/Lock.lock_at_address`): when both
    /// constituents pump, their rates are `k_L ω` and `k_R ω`, so they stand in the ratio
    /// `k_L : k_R`, whose Stern–Brocot word is their lock address. `None` when fewer than two
    /// pumps.
    pub fn pump_lock(&self) -> Result<Option<LockAddress>, AddressError> {
        let (Some(left), Some(right), Some(joint)) = (
            self.left().pump(),
            self.right().pump(),
            self.gluing().joint_clock(),
        ) else {
            return Ok(None);
        };
        let multiple = |pump: &crate::holon::element::Pump| {
            BigInt::from(joint.multiple(&gluing::turn_rate(&pump.clock)).expect(
                "check 9 of `interconnect` admitted each pump's rate as a whole multiple of the \
                 joint clock's",
            ))
        };
        LockAddress::from_ratio(&multiple(left), &multiple(right)).map(Some)
    }
}

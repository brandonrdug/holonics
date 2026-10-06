//! **The pair's boundary reading: port permutations, the reflected return and menu loop closure.**
//!
//! [definition] Brandon's Enigma/Bombe reading of the pair
//! ([keys](../../../../../docs/ELEMENTARY_OBJECTS.md#keys-locks-and-navigation)): the boundary
//! ports of a contact are permuted by fixed material and by a boundary map `S` (the plugboard),
//! a passage through a reflection `F` returns through the operand `A` that produced it,
//! `R = A⁻¹ F A`, and a menu loop at port `a` performs an ordered stage word conjugated by the
//! unknown boundary map. The loop closes exactly when the known stage word fixes the boundary
//! image:
//!
//! ```text
//! (S⁻¹ C₁ S)(S⁻¹ C₂ S)⋯(S⁻¹ C_k S) = S⁻¹ (C₁ C₂ ⋯ C_k) S          boundary conjugation
//! (S⁻¹ W S) a = a   ⇔   W (S a) = S a                              menu loop closure
//! ```
//!
//! So closure reads the boundary map only through the image `S a`, and [`menu_loop_closure`] takes
//! that image. Products follow Lean's `Equiv.Perm` multiplication: `(σ τ) x = σ (τ x)`, so in an
//! ordered word the last stage acts first.
//!
//! | Lean `Transport/HelicalPairInteraction` | Rust |
//! |---|---|
//! | `Equiv.Perm α` on a finite port population | [`PortPermutation`] |
//! | `reflectedReturn`, `reflectedReturn_involutive`, `reflectedReturn_no_fixed_point` | [`reflected_return`] |
//! | `boundary_conj_list_prod` | [`PortPermutation::product`] and the tests |
//! | `menu_loop_closure` | [`menu_loop_closure`] |
//!
//! The consistent keys of a menu, and their pruning, are `crate::compression::keys`.

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use thiserror::Error;

use crate::ratio::gcd;

/// Every refusal of a boundary reading. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum MenuError {
    #[error("the images {images:?} are not a permutation of the ports 0..{ports}")]
    NotPermutation { images: Vec<usize>, ports: usize },
    #[error("port {port} lies outside a population of {ports}")]
    PortOutside { port: usize, ports: usize },
    #[error("a permutation of {left} ports cannot compose with one of {right}")]
    PortCount { left: usize, right: usize },
}

/// [definition] **A permutation of a finite port population** `0..n`: the boundary map, the
/// reflection or a stage. Its only constructor checks that the images are a bijection.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PortPermutation {
    images: Vec<usize>,
}

impl PortPermutation {
    /// The permutation sending port `i` to `images[i]`; refuses anything but a bijection.
    pub fn new(images: Vec<usize>) -> Result<Self, MenuError> {
        let ports = images.len();
        let mut seen = vec![false; ports];
        for image in &images {
            if *image >= ports || seen[*image] {
                return Err(MenuError::NotPermutation { images, ports });
            }
            seen[*image] = true;
        }
        Ok(Self { images })
    }

    /// The identity on `ports` ports.
    pub fn identity(ports: usize) -> Self {
        Self {
            images: (0..ports).collect(),
        }
    }

    /// The transposition of ports `a` and `b`.
    pub fn swap(ports: usize, a: usize, b: usize) -> Result<Self, MenuError> {
        for port in [a, b] {
            if port >= ports {
                return Err(MenuError::PortOutside { port, ports });
            }
        }
        let mut images: Vec<usize> = (0..ports).collect();
        images.swap(a, b);
        Ok(Self { images })
    }

    /// The port population.
    pub fn ports(&self) -> usize {
        self.images.len()
    }

    /// The images, in port order.
    pub fn images(&self) -> &[usize] {
        &self.images
    }

    /// The image of one port.
    pub fn apply(&self, port: usize) -> Result<usize, MenuError> {
        self.images
            .get(port)
            .copied()
            .ok_or(MenuError::PortOutside {
                port,
                ports: self.ports(),
            })
    }

    /// `self · right`: the permutation `x ↦ self(right(x))` (Lean `Equiv.Perm` multiplication).
    pub fn multiply(&self, right: &Self) -> Result<Self, MenuError> {
        if self.ports() != right.ports() {
            return Err(MenuError::PortCount {
                left: self.ports(),
                right: right.ports(),
            });
        }
        Ok(compose_same(self, right))
    }

    /// The inverse permutation.
    pub fn inverse(&self) -> Self {
        let mut images = vec![0; self.ports()];
        for (port, image) in self.images.iter().enumerate() {
            images[*image] = port;
        }
        Self { images }
    }

    /// The order: the least common multiple of the cycle lengths, the period of the powers.
    pub fn order(&self) -> BigUint {
        let mut visited = vec![false; self.ports()];
        let mut order = BigInt::one();
        for start in 0..self.ports() {
            if visited[start] {
                continue;
            }
            let mut length = 0u64;
            let mut port = start;
            while !visited[port] {
                visited[port] = true;
                port = self.images[port];
                length += 1;
            }
            let length = BigInt::from(length);
            order = &order / gcd(&order, &length) * length;
        }
        order.into_parts().1
    }

    /// `self^exponent`, by squaring over the exponent reduced modulo the order.
    pub fn power(&self, exponent: &BigUint) -> Self {
        let reduced = exponent % self.order();
        let mut result = Self::identity(self.ports());
        let mut base = self.clone();
        for bit in 0..reduced.bits() {
            if reduced.bit(bit) {
                result = compose_same(&result, &base);
            }
            base = compose_same(&base, &base);
        }
        result
    }

    /// **The ordered product** `W = C₁ C₂ ⋯ C_k` of a stage word on `ports` ports, the last stage
    /// acting first; the empty word is the identity (Lean `List.prod`).
    pub fn product(ports: usize, word: &[Self]) -> Result<Self, MenuError> {
        word.iter()
            .try_fold(Self::identity(ports), |product, stage| {
                product.multiply(stage)
            })
    }
}

/// `left · right` for two permutations already known to share a port population.
fn compose_same(left: &PortPermutation, right: &PortPermutation) -> PortPermutation {
    PortPermutation {
        images: right.images.iter().map(|x| left.images[*x]).collect(),
    }
}

/// [definition] **The reflected return** `A⁻¹ F A` of a forward passage `A` through a reflection
/// `F`, using the operand that produced the forward passage (Lean
/// `Transport/HelicalPairInteraction.reflectedReturn`). An involutive reflection gives an involutive
/// return (`reflectedReturn_involutive`), and a fixed-point-free reflection a fixed-point-free
/// return (`reflectedReturn_no_fixed_point`).
pub fn reflected_return(
    forward: &PortPermutation,
    reflection: &PortPermutation,
) -> Result<PortPermutation, MenuError> {
    forward.inverse().multiply(reflection)?.multiply(forward)
}

/// [proved-derived; implemented-exact] **Menu loop closure** (Lean
/// `Transport/HelicalPairInteraction.menu_loop_closure`): a loop whose stage word `W` is read
/// through a boundary map `S` closes at its port `a` exactly when `W` fixes the boundary image
/// `S a`. This takes that image and returns the Bombe test `W (S a) = S a`; no other value of `S`
/// is read.
pub fn menu_loop_closure(
    ports: usize,
    stages: &[PortPermutation],
    image: usize,
) -> Result<bool, MenuError> {
    Ok(PortPermutation::product(ports, stages)?.apply(image)? == image)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn permutation(images: &[usize]) -> PortPermutation {
        PortPermutation::new(images.to_vec()).unwrap()
    }

    /// Every permutation of `ports` ports, for exhaustive checks.
    fn all(ports: usize) -> Vec<PortPermutation> {
        let mut result: Vec<Vec<usize>> = vec![Vec::new()];
        for _ in 0..ports {
            let mut extended = Vec::new();
            for prefix in &result {
                for x in (0..ports).filter(|x| !prefix.contains(x)) {
                    let mut next = prefix.clone();
                    next.push(x);
                    extended.push(next);
                }
            }
            result = extended;
        }
        result
            .into_iter()
            .map(|images| permutation(&images))
            .collect()
    }

    /// `S⁻¹ C S`.
    fn conjugate(boundary: &PortPermutation, stage: &PortPermutation) -> PortPermutation {
        boundary
            .inverse()
            .multiply(stage)
            .unwrap()
            .multiply(boundary)
            .unwrap()
    }

    /// A bijection is admitted and anything else is refused with its images.
    #[test]
    fn only_a_bijection_is_a_port_permutation() {
        assert_eq!(permutation(&[2, 0, 1]).apply(0), Ok(2));
        assert_eq!(
            PortPermutation::new(vec![0, 0, 1]),
            Err(MenuError::NotPermutation {
                images: vec![0, 0, 1],
                ports: 3
            })
        );
        assert!(PortPermutation::new(vec![0, 3, 1]).is_err());
        assert_eq!(all(4).len(), 24);
    }

    /// Lean `reflectedReturn_involutive`, `reflectedReturn_no_fixed_point`: through an involutive,
    /// fixed-point-free reflection every return is involutive and fixes no port, at every forward
    /// passage of `Sym(4)`.
    #[test]
    fn the_reflected_return_keeps_the_reflection_laws() {
        let reflection = permutation(&[1, 0, 3, 2]);
        for forward in all(4) {
            let returned = reflected_return(&forward, &reflection).unwrap();
            assert_eq!(
                returned.multiply(&returned).unwrap(),
                PortPermutation::identity(4)
            );
            assert!((0..4).all(|port| returned.apply(port).unwrap() != port));
        }
    }

    /// Lean `boundary_conj_list_prod` and `menu_loop_closure`: for every boundary map of three
    /// ports, every stage word of length at most two and every port, the conjugated word is the
    /// conjugated product, and the conjugated loop closes exactly when the word fixes `S a`.
    #[test]
    fn a_menu_loop_closes_exactly_when_its_word_fixes_the_boundary_image() {
        let every = all(3);
        let mut words: Vec<Vec<PortPermutation>> = vec![Vec::new()];
        for first in &every {
            words.push(vec![first.clone()]);
            for second in &every {
                words.push(vec![first.clone(), second.clone()]);
            }
        }
        for boundary in &every {
            for word in &words {
                let conjugated: Vec<PortPermutation> = word
                    .iter()
                    .map(|stage| conjugate(boundary, stage))
                    .collect();
                let conjugated_word = PortPermutation::product(3, &conjugated).unwrap();
                let product = PortPermutation::product(3, word).unwrap();
                assert_eq!(conjugated_word, conjugate(boundary, &product));
                for port in 0..3 {
                    assert_eq!(
                        conjugated_word.apply(port).unwrap() == port,
                        menu_loop_closure(3, word, boundary.apply(port).unwrap()).unwrap()
                    );
                }
            }
        }
    }

    /// The order is the period of the powers, and a power is read modulo it.
    #[test]
    fn a_power_is_read_modulo_the_order() {
        let rotor = permutation(&[1, 2, 0, 4, 3]);
        assert_eq!(rotor.order(), BigUint::from(6u32));
        assert_eq!(
            rotor.power(&BigUint::from(6u32)),
            PortPermutation::identity(5)
        );
        let mut stepped = PortPermutation::identity(5);
        for exponent in 0u32..13 {
            assert_eq!(rotor.power(&BigUint::from(exponent)), stepped);
            stepped = stepped.multiply(&rotor).unwrap();
        }
    }
}

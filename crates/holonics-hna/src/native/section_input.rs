//! Exterior symbol-basis measurement. An alphabet ordinal addresses a unit basis vector; it
//! is never read as amplitude, distance, a latent identity, or a native model clock.
use super::NativeSessionError;
use holonic_engine::{
    codec_recovery::{Symbol, SymbolAlphabet},
    native_ecology::constitutive_fibre::{
        NormalBasisSelection, NormalWaveBasisChart, NormalWaveBasisFace,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
};

pub struct SymbolCurrentChart {
    alphabet: SymbolAlphabet,
    coordinates: Vec<usize>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::{
        embedding_fiber::ResidentReadout,
        native_ecology::constitutive_fibre::{ResidentConstitutiveSection, ResidentNormalMaterial},
    };
    #[test]
    fn unicode_is_an_exterior_symbol_and_opaque_equal_spellings_can_stay_distinct() {
        let chart = SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['a', 'é']).unwrap());
        assert_eq!(chart.decode_text("aé").unwrap(), vec![Symbol(0), Symbol(1)]);
        assert!(chart.decode_text("b").is_err());
        let opaque = SymbolAlphabet::declared(vec![
            ("left".into(), vec![0xff]),
            ("right".into(), vec![0xff]),
        ])
        .unwrap();
        assert_ne!(opaque.symbol_of("left"), opaque.symbol_of("right"));
    }
    #[test]
    #[ignore = "requires CUDA; exterior alphabet permutation transports exact source/cross geometry and no ordinal supplies amplitude"]
    fn symbol_relabeling_carries_the_same_difference_geometry() {
        let readout = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&readout).unwrap();
        let left =
            SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['a', 'b', 'é']).unwrap());
        let right =
            SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['é', 'a', 'b']).unwrap());
        let symbols = "abéaébba";
        let a = left.mount(&s, &left.decode_text(symbols).unwrap()).unwrap();
        let b = right
            .mount(&s, &right.decode_text(symbols).unwrap())
            .unwrap();
        assert_eq!(a.rows(), symbols.chars().count());
        assert!(a.rows() < symbols.len());
        let a = ResidentConstitutiveSection::integers(&a)
            .unwrap()
            .differences(&s)
            .unwrap();
        let b = ResidentConstitutiveSection::integers(&b)
            .unwrap()
            .differences(&s)
            .unwrap();
        let mut ma = ResidentNormalMaterial::found(&s, 3, 3, ResidentGrain(u32::BITS)).unwrap();
        let mut mb = ResidentNormalMaterial::found(&s, 3, 3, ResidentGrain(u32::BITS)).unwrap();
        ma.receive_section(a.source(), a.observed()).unwrap();
        mb.receive_section(b.source(), b.observed()).unwrap();
        let a = ma.inspect().unwrap();
        let b = mb.inspect().unwrap();
        let permutation = [1, 2, 0];
        let source = |index: usize| (index / 3) * 3 + permutation[index % 3];
        for i in 0..9 {
            for j in 0..9 {
                assert_eq!(a.source_normal[i][j], b.source_normal[source(i)][source(j)]);
            }
        }
        for i in 0..3 {
            for j in 0..9 {
                assert_eq!(
                    a.cross_source[i][j],
                    b.cross_source[permutation[i]][source(j)]
                );
            }
        }
        assert_eq!(a.target_energy, b.target_energy);
        assert_eq!(a.source_normal_error, b.source_normal_error);
        assert_eq!(a.cross_source_error, b.cross_source_error);
    }
}
impl SymbolCurrentChart {
    pub fn declared(alphabet: SymbolAlphabet) -> Self {
        let coordinates = (0..alphabet.len()).collect();
        Self {
            alphabet,
            coordinates,
        }
    }
    /// A declared simultaneous source/receiver rechart. The permutation acts on actual unit
    /// coordinates; symbol spelling and occurrence identity do not supply its coefficients.
    pub fn recharted(
        alphabet: SymbolAlphabet,
        coordinates: Vec<usize>,
    ) -> Result<Self, NativeSessionError> {
        let mut sorted = coordinates.clone();
        sorted.sort_unstable();
        if coordinates.len() != alphabet.len() || !sorted.iter().copied().eq(0..alphabet.len()) {
            return Err(NativeSessionError::Application(
                "symbol basis is not a complete permutation".into(),
            ));
        }
        Ok(Self {
            alphabet,
            coordinates,
        })
    }
    pub fn coordinates(&self) -> &[usize] {
        &self.coordinates
    }
    pub fn receiver<'c>(
        &self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<NormalWaveBasisChart<'c>, NativeSessionError> {
        Ok(NormalWaveBasisChart::from_permutation(
            surface,
            &self.coordinates,
        )?)
    }
    /// Decode a face already selected on device. No score or centre is ranked on the host.
    pub fn emit<'c>(
        &self,
        source: NormalWaveBasisFace<'c>,
    ) -> Result<SymbolEmission<'c>, NativeSessionError> {
        if source.basis_coordinates() != self.coordinates {
            return Err(NativeSessionError::Application(
                "emission and symbol source charts differ".into(),
            ));
        }
        let selection = source.selection()?;
        let symbol = Symbol(
            u32::try_from(selection.selected)
                .map_err(|e| NativeSessionError::Application(e.to_string()))?,
        );
        let octets = self
            .alphabet
            .octets(symbol)
            .ok_or_else(|| NativeSessionError::Application("selected symbol outside codec".into()))?
            .to_vec();
        Ok(SymbolEmission {
            symbol,
            octets,
            selection,
            source,
        })
    }
    pub fn alphabet(&self) -> &SymbolAlphabet {
        &self.alphabet
    }
    pub fn components(&self) -> usize {
        2 * self.alphabet.len()
    }
    pub fn mount<'c>(
        &self,
        surface: &'c ResidentSurface<'c>,
        symbols: &[Symbol],
    ) -> Result<ResidentSection<'c>, NativeSessionError> {
        if symbols.is_empty() || symbols.iter().any(|s| s.0 as usize >= self.alphabet.len()) {
            return Err(NativeSessionError::Application(
                "empty or unsupported symbol section".into(),
            ));
        }
        let words = symbols
            .len()
            .checked_mul(self.components())
            .ok_or_else(|| NativeSessionError::Application("symbol section extent".into()))?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(words)
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        values.resize(words, (0, 0));
        for (row, symbol) in symbols.iter().enumerate() {
            values[row * self.components() + 2 * self.coordinates[symbol.0 as usize]] = (1, 1);
        }
        let rest = ResidentSectionRest::found(
            symbols.len(),
            self.components(),
            ResidentGrain(0),
            i64::BITS,
            values,
        )
        .map_err(NativeSessionError::Application)?;
        surface
            .mount_section_rest(&rest)
            .map_err(|e| NativeSessionError::Application(e.to_string()))
    }
    /// Unicode decoding is explicitly exterior. Multi-octet spellings are not multiple native
    /// impulses; a different codec may supply opaque symbols through `mount` directly.
    pub fn decode_text(&self, text: &str) -> Result<Vec<Symbol>, NativeSessionError> {
        text.chars()
            .map(|c| {
                self.alphabet.symbol_of(&c.to_string()).ok_or_else(|| {
                    NativeSessionError::Application(
                        "text is outside the declared symbol chart".into(),
                    )
                })
            })
            .collect()
    }
}

/// A known emitted action and its complete producing receiver. Re-entry may mount this action
/// as a new ordinary source; it does not turn the earlier wave family into a singleton or label
/// the action as a human observation. The old receiver remains available while this is retained.
pub struct SymbolEmission<'c> {
    symbol: Symbol,
    octets: Vec<u8>,
    selection: NormalBasisSelection,
    source: NormalWaveBasisFace<'c>,
}
impl<'c> SymbolEmission<'c> {
    pub fn symbol(&self) -> Symbol {
        self.symbol
    }
    pub fn octets(&self) -> &[u8] {
        &self.octets
    }
    pub fn selection(&self) -> &NormalBasisSelection {
        &self.selection
    }
    pub fn source(&self) -> &NormalWaveBasisFace<'c> {
        &self.source
    }
}

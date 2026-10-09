import CMAmbientAwayIdeals

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

theorem prime_pair_basicOpen_cover {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (c w : R) (h : Ideal.span ({f c, f w} : Set S) = ⊤)
    (x : PrimeSpectrum S) :
    PrimeSpectrum.comap f x ∈ PrimeSpectrum.basicOpen c ∨
      PrimeSpectrum.comap f x ∈ PrimeSpectrum.basicOpen w := by
  by_contra hn
  have hc : f c ∈ x.asIdeal := not_not.mp (not_or.mp hn).1
  have hw : f w ∈ x.asIdeal := not_not.mp (not_or.mp hn).2
  have hle : Ideal.span ({f c, f w} : Set S) ≤ x.asIdeal := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact hc
    · rcases Set.mem_singleton_iff.mp hp with rfl
      exact hw
  rw [h] at hle
  exact x.isPrime.ne_top (top_unique hle)

theorem ambient_pair_cover {R S : CommRingCat.{u}} {E X : Scheme.{u}}
    (f : R ⟶ S) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (k : Spec S ⟶ E) (g : E ⟶ X)
    (hsq : Spec.map f ≫ j = k ≫ g) (c w : R)
    (h : Ideal.span ({f.hom c, f.hom w} : Set S) = ⊤)
    (x : Spec S) :
    g (k x) ∈ (ambientAwayOpen j c).opensRange ∨
      g (k x) ∈ (ambientAwayOpen j w).opensRange := by
  have hs : g (k x) = j ((Spec.map f) x) := by
    exact (congrArg (fun (t : Spec S ⟶ X) => t x) hsq).symm
  rw [hs]
  have hc := prime_pair_basicOpen_cover f.hom c w h x
  rcases hc with hc | hw
  · left
    dsimp only [ambientAwayOpen]
    rw [Scheme.Hom.opensRange_comp,
      Scheme.Hom.opensRange_localizationAway]
    exact ⟨(Spec.map f) x, hc, rfl⟩
  · right
    dsimp only [ambientAwayOpen]
    rw [Scheme.Hom.opensRange_comp,
      Scheme.Hom.opensRange_localizationAway]
    exact ⟨(Spec.map f) x, hw, rfl⟩

#print axioms prime_pair_basicOpen_cover
#print axioms ambient_pair_cover
end Holonics.Hodge.CMGraphSource

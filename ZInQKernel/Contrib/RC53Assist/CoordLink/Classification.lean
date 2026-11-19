import ZInQKernel.Contrib.RC53Assist.CoordLink.Patterns

/-! # The rank-one and acyclic coordinate predicates restate the coordinate identity

`RankOneCoordinateProvenanceG` and `AcyclicCoordinateConventionG` are the restrictions of the
coordinate identity `urel x = kmOrig …` to the rank-one and acyclic patterns, after the proved
rank-one formula and the acyclic vanishing of the original coordinate. So replacing `RelIsKMG` by
their conjunction (`relIsKMG_iff_provenance_and_convention`) is a casewise restatement of the open
coordinate identity, not an independent provenance construction; the identity stays open until it is
derived from separately specified object and comparison data. These two equivalences were found and
checked in an independent review.
-/

namespace ZInQ.Contrib.RC53Assist.CoordLink.Classification

open Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)
open ZInQ.Contrib.RC53Assist.CoordLink

variable {K : Type} [Field K] [NumberField K]
  {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
  [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}
  (M : Identification2G K S S' hS b dK hK cE tK)
  (urel : Addr b → FractionRing OO)
  (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
  (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
  (hz : M.D.d1 *ᵥ z = 0)
  (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)

theorem rankOne_is_restricted_conclusion :
    RankOneCoordinateProvenanceG M urel z lam ↔
      ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 → M.D.RankOnePattern x →
        urel x = kmOrig M z lam hz hlam x := by
  constructor
  · intro h x hΔ hR
    exact (h x hΔ hR).trans (kmOrig_rankOne_formula M z lam hz hlam x hΔ hR).symm
  · intro h x hΔ hR
    exact (h x hΔ hR).trans (kmOrig_rankOne_formula M z lam hz hlam x hΔ hR)

theorem acyclic_is_restricted_conclusion :
    AcyclicCoordinateConventionG M urel ↔
      ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 → M.D.AcyclicPattern x →
        urel x = kmOrig M z lam hz hlam x := by
  constructor
  · intro h x hΔ hA
    exact (h x hΔ hA).trans (kmOrig_zero_of_acyclic M z lam hz hlam x hΔ hA).symm
  · intro h x hΔ hA
    exact (h x hΔ hA).trans (kmOrig_zero_of_acyclic M z lam hz hlam x hΔ hA)

end ZInQ.Contrib.RC53Assist.CoordLink.Classification

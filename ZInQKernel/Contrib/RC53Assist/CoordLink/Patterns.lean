import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG

/-!
# The direct coordinate obligation, split by genuine generic patterns

Manuscript ex:arith-coordinate, TeX 3877–3892, and
ex:limits-fixed-field-clearing, TeX 5509–5516 and 5605–5617.

The existing cancellation and determinant computations give an explicit formula
for the original rank-one tensor coordinate.  They also give zero at every
acyclic constituent.  The direct relaxed-coordinate identification is equivalent
to matching that explicit rank-one formula and the stated acyclic convention.
These are provenance obligations, not printed propositions.  In particular no
power-series-unit correction, exact augmented core at a zero coordinate, or
new printed leaf is used here.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordLink

open Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

variable {K : Type} [Field K] [NumberField K]
  {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
  [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- The original rank-one tensor coordinate after new-local and Smith-block
cancellation, with the retained orientation and transported functional. -/
def rankOneScalarG (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (x : Addr b) : FractionRing OO :=
  -(evK (sgnChar x) (kappaOfG M) *
    (Dx M.D x).alphaB (evK (sgnChar x) ∘ z) *
    (Dx M.D x).betaB (evK (sgnChar x) ∘ transportFun (M.C.map (φO b)) lam) *
    (Dx M.D x).A0.det * ((Dx M.D x).A1.det)⁻¹ * (Dx M.D x).A2.det)

/-- The explicit rank-one formula is a theorem about the existing original
complex, not an assumption about the relaxed coordinate. -/
theorem kmOrig_rankOne_formula (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) (hΔ : evK (sgnChar x) M.toIdentification.B.Δ ≠ 0)
    (hR : M.D.RankOnePattern x) :
    kmOrig M z lam hz hlam x = rankOneScalarG M z lam x := by
  let μ := transportFun (M.C.map (φO b)) lam
  have hμ := hμ_cancel (M.C.map (φO b)) M.isUnit_B hlam
  have h := (coordComputation_km M.D z μ hz hμ M.toIdentification.A0
    M.toIdentification.s M.toIdentification.s_ne M.toIdentification.central).1 x hΔ hR
  rw [kmOrig_eq, h]
  erw [alphaK_eq, betaK_eq, cleanT_eq]
  unfold rankOneScalarG kappaOfG
  ring

/-- At a rank-one constituent, degeneracy is exactly vanishing of one of the
two transported free-line coefficients.  All retained disk factors are nonzero. -/
theorem kmOrig_zero_iff_rankOne_tensor (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) (hΔ : evK (sgnChar x) M.toIdentification.B.Δ ≠ 0)
    (hR : M.D.RankOnePattern x) :
    kmOrig M z lam hz hlam x = 0 ↔
      (Dx M.D x).alphaB (evK (sgnChar x) ∘ z) = 0 ∨
      (Dx M.D x).betaB (evK (sgnChar x) ∘ transportFun (M.C.map (φO b)) lam) = 0 := by
  obtain ⟨h0, h1, h2⟩ := M.D.dets_of_Δ M.toIdentification.A0 M.toIdentification.s
    M.toIdentification.s_ne M.toIdentification.central x hΔ
  have hκ : evK (sgnChar x) (kappaOfG M) ≠ 0 :=
    ((isUnit_kappaG M).map (evK (sgnChar x))).ne_zero
  have hA0 : (Dx M.D x).A0.det ≠ 0 := by rw [← evK_det_A0]; exact h0
  have hA1 : (Dx M.D x).A1.det ≠ 0 := by rw [← evK_det_A1]; exact h1
  have hA2 : (Dx M.D x).A2.det ≠ 0 := by rw [← evK_det_A2]; exact h2
  rw [kmOrig_rankOne_formula M z lam hz hlam x hΔ hR]
  simp [rankOneScalarG, hκ, hA0, hA1, hA2]

/-- The rank-one part of the coordinate definition in the original retained
basis (TeX 3877–3888 and 5513–5516).  This is not a printed leaf: it identifies
the actual relaxed scalar with the explicit tensor formed from the actual
transported class and paired functional. -/
def RankOneCoordinateProvenanceG (M : Identification2G K S S' hS b dK hK cE tK)
    (urel : Addr b → FractionRing OO)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b)) : Prop :=
  ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 → M.D.RankOnePattern x →
    urel x = rankOneScalarG M z lam x

/-- The manuscript's coordinate-zero convention at acyclic constituents,
TeX 3889–3891 and 5612–5615.  This is a definition/provenance obligation,
not a cited printed theorem. -/
def AcyclicCoordinateConventionG (M : Identification2G K S S' hS b dK hK cE tK)
    (urel : Addr b → FractionRing OO) : Prop :=
  ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 → M.D.AcyclicPattern x → urel x = 0

/-- The exact direct gap: original rank-one tensor provenance plus the
acyclic coordinate-zero convention.  The generic pattern dichotomy and
all determinant computations are supplied by the existing proved lemmas. -/
theorem relIsKMG_iff_provenance_and_convention
    (M : Identification2G K S S' hS b dK hK cE tK)
    (urel : Addr b → FractionRing OO)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0) :
    ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M urel z lam hz hlam ↔
      RankOneCoordinateProvenanceG M urel z lam ∧ AcyclicCoordinateConventionG M urel := by
  constructor
  · intro h
    constructor
    · intro x hΔ hR
      exact (h x hΔ).trans (kmOrig_rankOne_formula M z lam hz hlam x hΔ hR)
    · intro x hΔ hA
      exact (h x hΔ).trans (kmOrig_zero_of_acyclic M z lam hz hlam x hΔ hA)
  · rintro ⟨hR, hA⟩ x hΔ
    obtain ⟨h0, h1, h2⟩ := M.D.dets_of_Δ M.toIdentification.A0 M.toIdentification.s
      M.toIdentification.s_ne M.toIdentification.central x hΔ
    rcases M.D.patterns_of_det_ne_zero x h0 h1 h2 with hr | ha
    · exact (hR x hΔ hr).trans (kmOrig_rankOne_formula M z lam hz hlam x hΔ hr).symm
    · exact (hA x hΔ ha).trans (kmOrig_zero_of_acyclic M z lam hz hlam x hΔ ha).symm

/-- Direct constructor from the two precisely scoped manuscript-coordinate
obligations, with no integral two-term core or correction-unit requirement. -/
theorem relIsKMG_of_provenance_and_convention
    (M : Identification2G K S S' hS b dK hK cE tK)
    (urel : Addr b → FractionRing OO)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (hR : RankOneCoordinateProvenanceG M urel z lam)
    (hA : AcyclicCoordinateConventionG M urel) :
    ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M urel z lam hz hlam :=
  (relIsKMG_iff_provenance_and_convention M urel z lam hz hlam).mpr ⟨hR, hA⟩

set_option pp.universes false

end ZInQ.Contrib.RC53Assist.CoordLink

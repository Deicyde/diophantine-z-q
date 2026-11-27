import ZInQKernel.Contrib.OneProof.BstRegular.Abstract
import ZInQKernel.Contrib.OneProof.PanBergerRefereed

/-!
# bst-regular: `B_st` is `G_K`-regular ⇒ dimension form ⇔ basis form ⇒ `ColmezThm01 ↔ BergerSurveyF`

The two inputs that the tree does not prove are stated as Props (no axiom, no hypothesis is added to any frozen
statement; the theorems below take them as arguments):

* `BstFracInvariants` (step (c)): `(Frac B_st)^{G_K} ⊆ B_st` inside `B_dR`, for every finite `K/ℚ_p` in `ℚ̄_p`.
  Printed: Fontaine, Astérisque 223 (1994), Exp. II/III (`B_st` is `G_K`-regular; with `(Frac B_st)^{G_K} = K_0`),
  locator UNVERIFIED; route guide Brinon–Conrad, CMI notes, §9.2 (unrefereed, not a source).
* `BstLineUnits` (step (d)): a nonzero `b ∈ B_st` with `σ(b) ∈ ℚ_p b` for all `σ ∈ G_K` is a unit of `B_st`.
  Same printed source (UNVERIFIED locator).

Together they give `IsRegularB` for `B_st = BstFOf` and `H = G_K` (`isRegularB_bst`, the stability being
`FontaineSt.bstF_stable`), and then, through the abstract step `isAdmissibleT_of_isAdmissible_of_regular`:

1. `isAdmissibleT_of_isAdmissible`; 2. `isPstFBasis_iff_isPstF`, `localIsPstFBasis_iff_localIsPstF`;
3. `colmezThm01_iff_bergerSurveyF`.

No count change: this file retires no frozen field.
-/

noncomputable section

namespace HDec
namespace PkgI4
namespace BstRegular

open Module BergerBst BmaxOne PanBergerSplit FontaineSt PanDict PanBergerRefereed

/-- **(c) `(Frac B_st)^{G_K} ⊆ B_st`** (Fontaine; the printed statement is `(Frac B_st)^{G_K} = B_st^{G_K} = K_0`):
for `x, y ∈ B_st`, `y ≠ 0`, every `z ∈ B_dR` with `z y = x` (i.e. `z = x / y`) fixed by `G_K` lies in `B_st`. -/
def BstFracInvariants : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ x ∈ BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p),
    ∀ y ∈ BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p), y ≠ 0 →
    ∀ z : BdR p, z * y = x → (∀ σ ∈ K.fixingSubgroup, bdrAct p σ z = z) →
      z ∈ BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)

/-- **(d) lines in `B_st` are units** (Fontaine): a nonzero `b ∈ B_st` spanning a `G_K`-stable `ℚ_p`-line is a unit of
`B_st`. -/
def BstLineUnits : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ b ∈ BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p), b ≠ 0 →
    (∀ σ ∈ K.fixingSubgroup, ∃ c : ℚ_[p], bdrAct p σ b = algebraMap ℚ_[p] (BdR p) c * b) →
    ∃ b' ∈ BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p), b * b' = 1

variable (p : ℕ) [Fact p.Prime]

/-- **`B_st` is `G_K`-regular**, given (c) and (d). -/
theorem isRegularB_bst (hc : BstFracInvariants) (hl : BstLineUnits) {ε₀ : PreTilt 𝓞_ℂ_[p] p}
    (h : IsGenEps p ε₀) (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    IsRegularB p (BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)) K.fixingSubgroup where
  stable σ _ x hx := bstF_stable p h σ x hx
  frac x hx y hy hy0 hrel := by
    have := isDomain_BdR p
    obtain ⟨y', hy'⟩ : ∃ y' : BdR p, y * y' = 1 :=
      (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).mul_inv_cancel hy0
    set z := x * y' with hz
    have hzy : z * y = x := by rw [hz, mul_assoc, mul_comm y' y, hy', mul_one]
    have hfix : ∀ σ ∈ K.fixingSubgroup, bdrAct p σ z = z := by
      intro σ hσ
      have hσy : bdrAct p σ y ≠ 0 := by
        intro h0
        have := congrArg (bdrAct p σ) hy'
        rw [map_mul, h0, zero_mul, map_one] at this
        exact zero_ne_one this
      have h1 : bdrAct p σ z * bdrAct p σ y = bdrAct p σ x := by rw [← map_mul, hzy]
      apply mul_right_cancel₀ (mul_ne_zero hy0 hσy)
      calc bdrAct p σ z * (y * bdrAct p σ y) = bdrAct p σ x * y := by rw [← h1]; ring
        _ = x * bdrAct p σ y := hrel σ hσ
        _ = z * (y * bdrAct p σ y) := by rw [← hzy]; ring
    exact ⟨z, hc p ε₀ h K inferInstance x hx y hy hy0 z hzy hfix, hfix, hzy.symm⟩
  line b hb hb0 hline := hl p ε₀ h K inferInstance b hb hb0 hline

section Targets

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **Target 1: dimension form ⇒ basis form for `B_st` over `G_K`**, given (c) and (d). -/
theorem isAdmissibleT_of_isAdmissible (hc : BstFracInvariants) (hl : BstLineUnits)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {ε₀ : PreTilt 𝓞_ℂ_[p] p}
    (h : IsGenEps p ε₀) {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) (ρ : GQp p →* GL (Fin n) E)
    (hadm : IsAdmissible p (BstFOf p h w hw) K.fixingSubgroup ρ) :
    IsAdmissibleT p (BstFOf p h w hw) K.fixingSubgroup ρ := by
  rw [bstFOf_eq_xi p h hw hgen] at hadm ⊢
  exact isAdmissibleT_of_isAdmissible_of_regular p _ _ (isRegularB_bst p hc hl h K) ρ hadm

/-- **Target 2a: `IsPstFBasis ↔ IsPstF`**, given (c) and (d). -/
theorem isPstFBasis_iff_isPstF (hc : BstFracInvariants) (hl : BstLineUnits) {ε₀ : PreTilt 𝓞_ℂ_[p] p}
    (h : IsGenEps p ε₀) {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) (ρ : GQp p →* GL (Fin n) E) :
    IsPstFBasis p h w hw ρ ↔ IsPstF p h w hw ρ := by
  refine ⟨isPstF_of_basis p h hw hgen ρ, ?_⟩
  rintro ⟨K, hK, hadm⟩
  exact ⟨K, hK, isAdmissibleT_of_isAdmissible p hc hl K h hw hgen ρ hadm⟩

/-- **Target 2b: `LocalIsPstFBasis ↔ LocalIsPstF`**, given (c) and (d). -/
theorem localIsPstFBasis_iff_localIsPstF (hc : BstFracInvariants) (hl : BstLineUnits)
    {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) :
    LocalIsPstFBasis p h w hw n ρ ↔ LocalIsPstF p h w hw n ρ := by
  refine ⟨localIsPstF_of_basis p h hw hgen n ρ, ?_⟩
  rintro ⟨E, hE, ρE, hmod, hpst⟩
  exact ⟨E, hE, ρE, hmod, (isPstFBasis_iff_isPstF p hc hl h hw hgen ρE).mpr hpst⟩

end Targets

/-- **Target 3: `ColmezThm01 ↔ BergerSurveyF`**, given (c) and (d). The forward direction is the tree's
`bergerSurveyF_of_colmez` (no input needed). -/
theorem colmezThm01_iff_bergerSurveyF (hc : BstFracInvariants) (hl : BstLineUnits) :
    ColmezThm01 ↔ BergerSurveyF := by
  refine ⟨bergerSurveyF_of_colmez, fun hB => ?_⟩
  intro p _ ε₀ h w hw hgen n E _ ρE hcont hdr
  exact (isPstFBasis_iff_isPstF p hc hl h hw hgen ρE).mpr (hB p ε₀ h w hw hgen n E ρE hcont hdr)

end BstRegular
end PkgI4
end HDec

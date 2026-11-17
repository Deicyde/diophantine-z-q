import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Assembly

/-! faltings5-lower, part 4: `FaltingsLemma5Lower` from three glue statements about the Néron
extension `f : 𝒩_A → 𝒩_B` of an isogeny (all three are standard facts in characteristic `0`). -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

/-- **Glue (étaleness at the origin).** The extension of an isogeny is bijective on the cotangent
spaces `ω_{A_K} = 𝔪/𝔪²` of the generic fibres at the origin. -/
def IsogCotBijective : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (f : 𝒩A.G ⟶ 𝒩B.G) [IsMonHom f],
      CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f → Function.Bijective (cotMap 𝒩A 𝒩B f)

/-- **Glue (surjectivity on complex points).** -/
def IsogPtsSurjective : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (f : 𝒩A.G ⟶ 𝒩B.G) [IsMonHom f],
      CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f →
      ∀ τ : K →+* ℂ, Function.Surjective fun p : 𝒩A.Pts τ => p ≫ f

/-- **Glue (the kernel on complex points).** It is finite, of order at most `deg φ = #ker φ(K̄)`. -/
def IsogKerCard : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (f : 𝒩A.G ⟶ 𝒩B.G) [IsMonHom f],
      CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f →
      ∀ τ : K →+* ℂ, Finite {p : 𝒩A.Pts τ // p ≫ f = 1} ∧
        Nat.card {p : 𝒩A.Pts τ // p ≫ f = 1} ≤ isogDeg φ

/-- **`FaltingsLemma5Lower` from the three glue statements.** -/
theorem faltingsLemma5Lower_of (h1 : IsogCotBijective) (h2 : IsogPtsSurjective)
    (h3 : IsogKerCard) : ZInQ.HeightSplit.FaltingsLemma5Lower := by
  intro K _ _ A B φ hφ 𝒩A 𝒩B _ hB _ _ x y hx hy
  obtain ⟨f, hm, he⟩ := CToPrinted.exists_extension φ hφ 𝒩A 𝒩B hB
  haveI := hm
  set c : ℝ := (1 / 2) * Real.log (isogDeg φ)
  have key : 𝒩B.height + ((-c : ℝ) : EReal) ≤ 𝒩A.height := by
    conv_rhs => rw [GroupModel.height]
    refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
    subst hM
    have hle := height_le_of_metrized M 𝒩B f (h1 K A B φ hφ M.model 𝒩B f he)
      (h2 K A B φ hφ M.model 𝒩B f he) (isogDeg φ) (h3 K A B φ hφ M.model 𝒩B f he)
    calc 𝒩B.height + ((-c : ℝ) : EReal)
        ≤ ((M.hodge.modelHeight + c : ℝ) : EReal) + ((-c : ℝ) : EReal) := by gcongr
      _ = (M.hodge.modelHeight : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
  rw [hx, hy, ← EReal.coe_add, EReal.coe_le_coe_iff] at key
  linarith

end GapHeight

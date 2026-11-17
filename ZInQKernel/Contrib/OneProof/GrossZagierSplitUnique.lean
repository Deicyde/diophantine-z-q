import ZInQKernel.Contrib.OneProof.GrossZagierSplit
import ZInQKernel.Contrib.OneProof.GrossZagierModelUnique

/-!
# h33-d1: the Gross–Zagier curve leaf on one model, with the twist by splitting in `K`

Task h33-d1 (2026-11-17). Report: `docs/research/h33-d1.md`; scratch and log: `scratch/h33-d1/`.

Combines eps-splitting's `GZSplit.GrossZagierCurveCdSplit` (Heegner hypothesis "every `p ∣ N`
splits in `K`", twist by the quadratic character of `K`) with the one-model form of
`GrossZagierModelUnique.lean`: the new leaf `GrossZagierCurveCdSplitSome` asks the statement on
**some** normal proper model of `X₀(N)`. `grossZagierAlgOptCd_of_splitSome` discharges `hGZ`;
neither the step S1 (every model is the canonical model: model uniqueness, proved) nor the step on
`ε_D` (eps-splitting, proved) is left.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Topology HeckeRing.GL2
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZSplitUnique

open ZInQ.GZSch ZInQ.GZAlg ZInQ.GZDict2 ZInQ.GZSplit ZInQ.GZUnique

/-- **The split Gross–Zagier statement on one model `(X, ι)` of `X₀(N)`**: the part of
`GZSplit.GrossZagierCurveAtSplit E` after the model (verbatim). -/
def GZSplitBody (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] (f : Newform N 2) (X : Scheme.{0})
    [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)) (ι : X.functionField ≃+* X0Field N) : Prop :=
    ∀ π : X ⟶ ESch E, π ≫ toSpecQ E = sX →
    (∃ p₁ p₂ : X, π p₁ ≠ π p₂) →
    (∀ p : X, IsCuspInfty N ι p → π p ∉ (chartZ E).opensRange) →
    ∀ D β : ℤ, ZInQ.GZDecomp.IsOddImagFundDisc D → D < -4 →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    (∀ p : ℕ, p.Prime → p ∣ N → ZInQ.EpsSplit.IsSplitIn K p) →
    (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), ZInQ.GZModuli.IsHeegnerPointReps N D β τ →
    ∀ x : R → (Spec (CommRingCat.of ℂ) ⟶ X), (∀ r, IsPointAt N ι (τ r) (x r)) →
    ∀ ιK : K →ₐ[ℚ] ℂ, ιK δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ n : ℤ, n ≠ 0 →
    ∀ y : (E⁄K).Point, WeierstrassCurve.Affine.Point.map ιK y = n • ∑ r, ptOf E (x r ≫ π) →
    ∀ F G : ℂ → ℂ, ZInQ.GZDecomp.IsEntireCont (ZInQ.GZDecomp.coeff f) 2 F →
      ZInQ.GZDecomp.IsEntireCont
        (fun m => ZInQ.GZDecomp.coeff f m * (ZInQ.EpsSplit.quadChar K m : ℂ)) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

theorem grossZagierCurveAtSplit_iff (E : WeierstrassCurve ℚ) :
    GrossZagierCurveAtSplit E ↔ ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
      (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
      ∀ (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX →
      ZInQ.Contrib.CurvesG.IsNormalScheme X → topologicalKrullDim X = 1 →
      ∀ ι : X.functionField ≃+* X0Field N, GZSplitBody E N f X sX ι := Iff.rfl

/-- **Transfer between models** of the split statement. -/
theorem gzSplitBody_transfer (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] (f : Newform N 2)
    {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    (sX' : X' ⟶ Spec (CommRingCat.of ℚ)) [IsProper sX] [IsProper sX']
    (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p))
    (hv' : ∀ p : X', ValuationRing (X'.presheaf.stalk p))
    (ι : X.functionField ≃+* X0Field N) (ι' : X'.functionField ≃+* X0Field N)
    (hX : GZSplitBody E N f X sX ι) : GZSplitBody E N f X' sX' ι' := by
  obtain ⟨F, G, hFG, -, hcG, -, hpF, -⟩ := model_transfer sX sX' hv hv' ι ι'
  have hFG' : ∀ p : X', G (F p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, hFG]; rfl
  intro π' hπ' hnc hcusp D β hD hD4 K _ _ _ hK δ hδ hH hβ R _ τ hτ x' hx' ιK hιK n hn y hy
    Fc Gc hFc hGc
  refine hX (G ≫ π') (specQ_ext _ _) ?_ ?_ D β hD hD4 K hK δ hδ hH hβ R τ hτ (fun r => x' r ≫ F)
    (fun r => hpF (τ r) (x' r) (hx' r)) ιK hιK n hn y ?_ Fc Gc hFc hGc
  · obtain ⟨p₁, p₂, hne⟩ := hnc
    refine ⟨F p₁, F p₂, ?_⟩
    simp only [Scheme.Hom.comp_apply, hFG']
    exact hne
  · intro p hp
    simpa only [Scheme.Hom.comp_apply] using hcusp (G p) (hcG p hp)
  · rw [hy]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Category.assoc, ← Category.assoc F G π', hFG, Category.id_comp]

/-- **Leaf (Gross–Zagier, curve form, one model, twist by splitting in `K`).** As
`GZSplit.GrossZagierCurveAtSplit E`, asked for **some** integral normal scheme `X`, proper of
dimension `1` over `ℚ`, with `ι : K(X) ≃ ℚ(X₀(N)) = ℚ(j, j_N)` (the canonical model `X₀(N)/ℚ` is
one; Shimura 1971 §6.7, UNVERIFIED locator).

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
(1986), 225–320, Thm I.6.3 and Ch. V §2 (Thm 2.1), for a modular parametrization
`π : X₀(N) → E` with `π(∞) = 0`. Weakenings as in `GrossZagierCurveAtSplit`. -/
def GrossZagierCurveAtSplitSome (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX ∧
      ZInQ.Contrib.CurvesG.IsNormalScheme X ∧ topologicalKrullDim X = 1 ∧
      ∃ ι : X.functionField ≃+* X0Field N, GZSplitBody E N f X sX ι

/-- **Leaf of the `C_d` route**: `GrossZagierCurveAtSplitSome E'` for every short model `E'` in the
isogeny class of `C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree. -/
def GrossZagierCurveCdSplitSome : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], ZInQ.GZOptimal.IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = (ZInQ.shortCurve (-(d : ℚ) ^ 2)).LFunction n) →
      GrossZagierCurveAtSplitSome E'

theorem grossZagierCurveAtSplit_of_some (E : WeierstrassCurve ℚ)
    (h : GrossZagierCurveAtSplitSome E) : GrossZagierCurveAtSplit E := by
  rw [grossZagierCurveAtSplit_iff]
  intro N _ f hχ hf X' _ sX' hprop' hN' hdim' ι'
  obtain ⟨X, hXi, sX, hprop, hN, hdim, ι, hbody⟩ := h N f hχ hf
  haveI := hprop
  haveI := hprop'
  exact gzSplitBody_transfer E N f sX sX' (valuationRing_of_model sX hprop hN hdim)
    (valuationRing_of_model sX' hprop' hN' hdim') ι ι' hbody

/-- The all-models split leaf implies the one-model one (a model exists). -/
theorem grossZagierCurveAtSplitSome_of_all (E : WeierstrassCurve ℚ)
    (h : GrossZagierCurveAtSplit E) : GrossZagierCurveAtSplitSome E := by
  intro N _ f hχ hf
  obtain ⟨X, hXi, sX, hprop, hN, hdim, ⟨ι⟩⟩ := exists_model N
  exact ⟨X, hXi, sX, hprop, hN, hdim, ι, h N f hχ hf X sX hprop hN hdim ι⟩

theorem grossZagierCurveCdSplit_of_some (h : GrossZagierCurveCdSplitSome) : GrossZagierCurveCdSplit :=
  fun d hd hsq E' _ hE' hL => grossZagierCurveAtSplit_of_some E' (h d hd hsq E' hE' hL)

/-- **What `frozenTarget` reads (`hGZ`), from the one-model split leaf.** -/
theorem grossZagierAlgOptCd_of_splitSome (h : GrossZagierCurveCdSplitSome) :
    GZAlg.GrossZagierAlgOptCd :=
  grossZagierAlgOptCd_of_split (grossZagierCurveCdSplit_of_some h)

end ZInQ.GZSplitUnique

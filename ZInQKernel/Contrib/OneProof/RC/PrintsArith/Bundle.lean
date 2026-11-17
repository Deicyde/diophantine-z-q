import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Kato
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Local
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.KatoHypV

/-!
# Lane RC9: the arithmetic prints bundled, and their forms for `E_ℓ`

`ArithPrints` bundles the arithmetic prints of lane RC9 that are stated over genuine definitions,
in the manner of the shared top layer's `ZInQ.Contrib.CloudB3RC53.Prints` (which holds BCDT,
Kolyvagin, Dokchitser–Dokchitser and Cai–Shu–Tian and is not restated here). `GlueArith` bundles
the two textbook facts the derived forms use. The interface-level statements (`KatoZetaLeaf`,
`CCLThm2_15Applied`, `CJReductionData.Thm3_1KappaOne`) are not bundled: their objects are abstract.

For the curves `E_ℓ` of Theorem 5.3 (`ZInQ.Contrib.CloudB3RC53.Ecurve ℓ`), PROVED from the bundles:
`ecurve_hasNoCM` (non-CM), `ecurve_serre_scalar` (tex 2882–2887), `ecurve_serre_SL2_part`
(tex 3597–3605) and `ecurve_kato_hyp_v` (Kato's hypothesis (v), tex 7228–7231).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsArith

open scoped WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53

/-- **The arithmetic prints of lane RC9 over genuine definitions** (each field a PRINT leaf; see
its definition for the locator, the use and the hypothesis match). -/
structure ArithPrints : Prop where
  /-- Serre, Invent. Math. 15 (1972), §4.4, Théorème 3, p. 299. -/
  serre : SerreThm3
  /-- Kato, Astérisque 295, Corollary 14.3, p. 235 (`K = ℚ`, `χ = 1`). -/
  katoCor14_3 : KatoCor14_3
  /-- Kato, Astérisque 295, Theorem 13.5(2), p. 227 (Rohrlich), weight two. -/
  katoThm13_5_2 : KatoThm13_5_2
  /-- Elkik, Astérisque 183, Théorème, p. 59 (Manin–Drinfeld), analytic form. -/
  maninDrinfeld : ManinDrinfeld
  /-- Edixhoven, Compositio 81, Theorem 5.3 and Remark 5.4.1, pp. 299–300, consequence form. -/
  edixhoven : EdixhovenTwistComponents
  /-- Lang, Amer. J. Math. 78 (1956), Theorem 1 and corollary, consequence form (UNVERIFIED). -/
  lang : LangThm1

/-- **The textbook facts (GLUE, not proved here) used by the derived forms.** -/
structure GlueArith : Prop where
  /-- Rational CM `j`-invariants are integers (Silverman, *Advanced Topics*, II.6.1). -/
  cmj : CMjInteger
  /-- `det ρ₂ = χ₂` (Weil pairing), in the direction used. -/
  det : ∀ E : WeierstrassCurve ℚ, DetTateTwoCyclotomic E

/-- `E_ℓ` is elliptic for `ℓ > 0`. -/
theorem ecurve_isElliptic {ℓ : ℕ} (hℓ : 0 < ℓ) : (Ecurve ℓ).IsElliptic :=
  ZInQ.Manuscript.PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')

/-- **`E_ℓ` has no complex multiplication** (PROVED from `GlueArith`). -/
theorem ecurve_hasNoCM (G : GlueArith) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    @HasNoCM (Ecurve ℓ) (ecurve_isElliptic hℓ) :=
  curve_hasNoCM G.cmj (by exact_mod_cast hℓ.ne')

/-- **The scalar element of tex 2883–2887 for `E_ℓ`** (PROVED from the bundles): there are `n ≥ 2`
and `g ∈ G_ℚ` with `ρ₂(g) = (1 + 2^n) · id` on `T₂E_ℓ`. -/
theorem ecurve_serre_scalar (P : ArithPrints) (G : GlueArith) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ g : GalQ,
      ∀ x : TateMod (Ecurve ℓ) 2, tateRep (Ecurve ℓ) 2 g x = (1 + (2 : ℤ_[2]) ^ n) • x :=
  @serre_scalar P.serre (Ecurve ℓ) (ecurve_isElliptic hℓ) (ecurve_hasNoCM G hℓ)

/-- **`Γ_d ⊆ J` for `E_ℓ` (tex 3597–3605)** (PROVED from the bundles). -/
theorem ecurve_serre_SL2_part (P : ArithPrints) (G : GlueArith) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ α : TateMod (Ecurve ℓ) 2 ≃ₗ[ℤ_[2]] TateMod (Ecurve ℓ) 2,
      LinearMap.det α.toLinearMap = 1 →
      (∀ x, ∃ y, α x = x + (2 : ℤ_[2]) ^ d • y) →
      ∃ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) ∧
        tateRep (Ecurve ℓ) 2 σ = α.toLinearMap :=
  @serre_SL2_part P.serre (Ecurve ℓ) (ecurve_isElliptic hℓ) (ecurve_hasNoCM G hℓ)
    (G.det (Ecurve ℓ))

/-- **Kato's hypothesis (v) for `T₂E_ℓ ⊗ χ`** (PROVED from the bundles; tex 7228–7231). -/
theorem ecurve_kato_hyp_v (P : ArithPrints) (G : GlueArith) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (χ : GalQ →* ℤˣ) :
    ∃ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) ∧ χ σ = 1 ∧
      Module.finrank ℤ_[2] (LinearMap.ker (tateRep (Ecurve ℓ) 2 σ - 1)) = 1 :=
  @kato_hyp_v (Ecurve ℓ) (ecurve_isElliptic hℓ) P.serre (ecurve_hasNoCM G hℓ)
    (G.det (Ecurve ℓ)) χ

end ZInQ.Manuscript.RC.PrintsArith

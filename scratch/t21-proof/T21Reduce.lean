import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2

/-!
# t21-proof: reduction of `TYZThm21At31` to two glue statements

`TYZThm21At31` (TYZ Theorem 2.1 at `(3, 1)`) from
* `BrandtValueAt3`: every test vector `f_3` (for every admissible `τ`) has `f_3(1) = ±3`
  (a finite Brandt computation; glue);
* `LcalUnitOneThree`: `0 < ‖𝓛(m)²‖ < 4` at `m = 1, 3` (a numerical estimate of `L(C_1, 1)` and
  `L(C_3, 1)`; glue).
Proved here: `Cl(ℚ(√−3)) = 1` collapses the class sum to `f_3(τ̂(1)) = f_3(1)`, `#μ(ℚ(√−3)) = 6`
(Mathlib's `IsCyclotomicExtension.Rat.torsionOrder_eq`), and `ℓ(m)² = 𝓛(m)²` with `0 < |𝓛(m)²| < 4`
forces `ℓ(m) = ±1`.
-/

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split NumberField NumberField.Units IsDedekindDomain
open scoped Quaternion

/-- **Glue (finite Brandt computation at `n = 3`)**: for every admissible `τ : ℚ(√−3) → B` and
every test vector `f_3` (a `ℤ`-generator of `π_ℤ^{U_3}`), `f_3(1) = ±3`. -/
def BrandtValueAt3 : Prop :=
  ∀ τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ], AdmissibleTau 3 τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector 3 τ f →
    f 1 = 3 ∨ f 1 = -3

/-- **Glue (numerical estimate)**: `0 < ‖𝓛(m)²‖ < 4` for `m = 1, 3`. -/
def LcalUnitOneThree : Prop :=
  (0 < ‖lcalSq 1‖ ∧ ‖lcalSq 1‖ < 4) ∧ (0 < ‖lcalSq 3‖ ∧ ‖lcalSq 3‖ < 4)

/-! ## `#μ(ℚ(√−3)) = 6` -/

theorem torsionOrder_three : torsionOrder (QNeg 3) = 6 := by
  have := ZInQ.Contrib.TYZLcal.isCyclotomicExtension_three
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 3)]
  decide

/-! ## The class sum collapses -/

instance subsingleton_cl3 : Subsingleton (ClassGroup (𝓞 (QNeg 3))) := by
  have h1 : Fintype.card (ClassGroup (𝓞 (QNeg 3))) = 1 :=
    card_classGroup_eq_one_iff.mpr ZInQ.Contrib.TYZLcal.pid_three
  exact Fintype.card_le_one_iff_subsingleton.mp h1.le

theorem classSum_eq {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {f : ℍ[AQ] → ℤ} (hf : InPiZ 3 τ f) :
    ∑ t : ClassGroup (𝓞 (QNeg 3)), f ((tauHatU 3 τ (clLift 3 t) : ℍ[AQ]ˣ) : ℍ[AQ]) = f 1 := by
  rw [Fintype.sum_subsingleton _ 1]
  have h : FiniteAdeleRing.toClassGroup (𝓞 (QNeg 3)) (QNeg 3) (clLift 3 1) =
      FiniteAdeleRing.toClassGroup (𝓞 (QNeg 3)) (QNeg 3) 1 := Subsingleton.elim _ _
  rw [tv_eq_of_toClassGroup_eq hf h, map_one, Units.val_one]

/-! ## `ℓ(m) = ±1` -/

theorem int_eq_pm_one_of_sq {a : ℤ} {z : ℂ} (ha : (a : ℂ) ^ 2 = z) (h0 : 0 < ‖z‖) (h4 : ‖z‖ < 4) :
    a = 1 ∨ a = -1 := by
  have hn : ‖z‖ = ((a ^ 2 : ℤ) : ℝ) := by
    rw [← ha, norm_pow, Complex.norm_intCast]; push_cast; rw [sq_abs]
  rw [hn] at h0 h4
  have h0' : 0 < a ^ 2 := by exact_mod_cast h0
  have h4' : a ^ 2 < 4 := by exact_mod_cast h4
  have : a ≠ 0 := by rintro rfl; simp at h0'
  have h2 : -2 < a ∧ a < 2 := by constructor <;> nlinarith
  omega

/-! ## The reduction -/

theorem tyzThm21At31_of_glue (hB : BrandtValueAt3) (hL : LcalUnitOneThree) : TYZThm21At31 := by
  intro τ hτ f hf ℓ hℓ
  have h1 := int_eq_pm_one_of_sq (hℓ 1 squarefree_one (Or.inl rfl)) hL.1.1 hL.1.2
  have h3 := int_eq_pm_one_of_sq (hℓ 3 Nat.prime_three.squarefree (Or.inr rfl)) hL.2.1 hL.2.2
  rw [classSum_eq hf.1, torsionOrder_three]
  have hp : ℓ 3 * ℓ 1 = 1 ∨ ℓ 3 * ℓ 1 = -1 := by
    rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3 <;> simp [h1, h3]
  rcases hB τ hτ f hf with hf1 | hf1 <;> rcases hp with hp | hp
  · exact ⟨1, Or.inl rfl, by rw [hf1, hp]; norm_num⟩
  · exact ⟨-1, Or.inr rfl, by rw [hf1, hp]; norm_num⟩
  · exact ⟨-1, Or.inr rfl, by rw [hf1, hp]; norm_num⟩
  · exact ⟨1, Or.inl rfl, by rw [hf1, hp]; norm_num⟩

end ZInQ.Contrib.T21Proof

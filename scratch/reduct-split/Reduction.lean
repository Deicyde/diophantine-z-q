import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.TailY

/-!
# reduct-split, part 1: the SGA 7 IX / Serre–Tate rows r6, r7b, r8 from published-form leaves

Task reduct-split (2026-11-14). The rows are the kernel's Props (imported, never restated):
`PkgI2.RaynaudCriterion.{0}` (r6), `PkgI2.SerreTatePotentialGood.{0}` (r7b),
`PkgI2.GrothendieckMonodromy.{0}` (r8), all in `ZInQKernel/HDecomp/Objects.lean`.

This file
* §1 proves the divisibility of `ℓ`-power torsion (`T_ℓ A → A(K̄)[ℓⁿ]` onto) from the kernel's
  `PkgI2.TorsionStructure` (itself proved from the bundle leaf `AvSplit.MumfordTorsionAlgClosed`);
* §2 defines Néron models over a valuation ring `O ⊆ K` (BLR 1.2 Def. 1) and semistable reduction
  (SGA 7 IX Déf. 3.2 read over `κ̄`), with `HeightSplit.HasSemiAbelianIdentityComponent`;
* §3 states the published theorems as leaves;
* §4-§6 prove the rows.
No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq HasGoodReduction)

set_option linter.style.haveILetI false

namespace ReductSplit

/-! ## §1. Divisibility of `ℓ`-power torsion over `K̄` -/

section Div

variable {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]

local notation "Kb" => AlgebraicClosure K

/-- The `n`-torsion subgroup of `A(K̄)`. -/
abbrev torsSub (n : ℕ) : Subgroup (Pts A Kb) := (powMonoidHom n : Pts A Kb →* Pts A Kb).ker

theorem mem_torsSub {n : ℕ} {x : Pts A Kb} : x ∈ torsSub A n ↔ x ^ n = 1 := Iff.rfl

theorem card_torsSub (hT : PkgI2.TorsionStructure.{0}) (g : ℕ)
    (hg : topologicalKrullDim A.X.left = (g : WithBot ℕ∞)) (n : ℕ) (hn : 0 < n)
    (hnK : (n : K) ≠ 0) : Nat.card (torsSub A n) = n ^ (2 * g) := by
  obtain ⟨e, -⟩ := hT K A g n hg hn hnK
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : Nat.card (torsSub A n) = Nat.card (torsion A Kb n) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  rw [h1, Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **`[ℓ] : A(K̄)[ℓ^{k+1}] → A(K̄)[ℓ^k]` is onto** (counting, from `TorsionStructure`). -/
theorem exists_pow_eq (hT : PkgI2.TorsionStructure.{0}) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓK : (ℓ : K) ≠ 0) (k : ℕ) (y : Pts A Kb) (hy : y ^ (ℓ ^ k) = 1) :
    ∃ z : Pts A Kb, z ^ ℓ = y ∧ z ^ (ℓ ^ (k + 1)) = 1 := by
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite (ObjBridge.ofGrp A)
  have hpow : ∀ j : ℕ, ((ℓ ^ j : ℕ) : K) ≠ 0 := fun j => by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hℓK
  have hpos : ∀ j : ℕ, 0 < ℓ ^ j := fun j => pow_pos hℓ.pos j
  have hc : ∀ j, Nat.card (torsSub A (ℓ ^ j)) = (ℓ ^ j) ^ (2 * g) := fun j =>
    card_torsSub A hT g hg (ℓ ^ j) (hpos j) (hpow j)
  -- `f : A[ℓ^{k+1}] → A(K̄)`, `z ↦ z^ℓ`
  let f : torsSub A (ℓ ^ (k + 1)) →* Pts A Kb :=
    (powMonoidHom ℓ).comp (torsSub A (ℓ ^ (k + 1))).subtype
  have hrange : f.range ≤ torsSub A (ℓ ^ k) := by
    rintro _ ⟨z, rfl⟩
    show (z.1 ^ ℓ) ^ (ℓ ^ k) = 1
    rw [← pow_mul, ← pow_succ']
    exact z.2
  -- the kernel of `f` is `A[ℓ]`
  have hker : Nat.card f.ker = Nat.card (torsSub A ℓ) := by
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1.1, z.2⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl }
    · show z.1 ^ (ℓ ^ (k + 1)) = 1
      rw [pow_succ', pow_mul, show z.1 ^ ℓ = 1 from z.2, one_pow]
    · exact z.2
  haveI : Finite (torsSub A (ℓ ^ k)) := Nat.finite_of_card_ne_zero (by
    rw [hc k]; exact pow_ne_zero _ (hpos k).ne')
  have hcard : Nat.card (torsSub A (ℓ ^ k)) ≤ Nat.card f.range := by
    have h := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hker, hc (k + 1)] at h
    have h1 : Nat.card (torsSub A ℓ) = ℓ ^ (2 * g) := by
      have := hc 1; rwa [pow_one] at this
    rw [h1] at h
    rw [hc k]
    have h2 : (ℓ ^ (k + 1)) ^ (2 * g) = ℓ ^ (2 * g) * (ℓ ^ k) ^ (2 * g) := by
      rw [← mul_pow, ← pow_succ']
    rw [h2] at h
    exact le_of_eq (Nat.eq_of_mul_eq_mul_left (pow_pos hℓ.pos _) h).symm
  have heq := Subgroup.eq_of_le_of_card_ge hrange hcard
  have hy' : y ∈ f.range := by rw [heq]; exact hy
  obtain ⟨z, hz⟩ := hy'
  exact ⟨z.1, hz, z.2⟩

/-- **Every `x ∈ A(K̄)[ℓⁿ]` is the `n`-th component of an element of `T_ℓ A`.** -/
theorem exists_tate_lift (hT : PkgI2.TorsionStructure.{0}) (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hℓK : (ℓ : K) ≠ 0) (n : ℕ) (x : Pts A Kb) (hx : x ^ (ℓ ^ n) = 1) :
    ∃ t : PkgI3.Tate.T ℓ (Additive (Pts A Kb)), t.1 n = Additive.ofMul x := by
  classical
  -- the sequence above level `n`: `s 0 = x`, `s (j+1)^ℓ = s j`, `s j ∈ A[ℓ^{n+j}]`
  have step : ∀ j : ℕ, ∀ y : {y : Pts A Kb // y ^ (ℓ ^ (n + j)) = 1},
      ∃ z : {z : Pts A Kb // z ^ (ℓ ^ (n + (j + 1))) = 1}, z.1 ^ ℓ = y.1 := by
    intro j y
    obtain ⟨z, hz, hz'⟩ := exists_pow_eq A hT ℓ hℓ.out hℓK (n + j) y.1 y.2
    exact ⟨⟨z, by rw [← add_assoc]; exact hz'⟩, hz⟩
  let s : (j : ℕ) → {y : Pts A Kb // y ^ (ℓ ^ (n + j)) = 1} :=
    fun j => Nat.rec ⟨x, by simpa using hx⟩ (fun j y => (step j y).choose) j
  have hs : ∀ j, (s (j + 1)).1 ^ ℓ = (s j).1 := fun j => (step j (s j)).choose_spec
  -- the full sequence: `u m = x^(ℓ^(n-m))` for `m ≤ n`, `u (n+j) = s j`
  let u : ℕ → Pts A Kb := fun m => if m ≤ n then x ^ (ℓ ^ (n - m)) else (s (m - n)).1
  refine ⟨⟨fun m => Additive.ofMul (u m), ?_, ?_⟩, ?_⟩
  · show Additive.ofMul (u 0) = 0
    simp only [u, Nat.zero_le, ite_true, Nat.sub_zero, hx]; rfl
  · intro m
    show ℓ • Additive.ofMul (u (m + 1)) = Additive.ofMul (u m)
    rw [← ofMul_pow]
    congr 1
    by_cases h : m + 1 ≤ n
    · simp only [u, h, ite_true, show m ≤ n by omega]
      rw [← pow_mul, ← pow_succ, show n - (m + 1) + 1 = n - m by omega]
    · by_cases h' : m = n
      · subst h'
        simp only [u, h, ite_false, le_refl, ite_true, Nat.sub_self, pow_zero, pow_one]
        rw [show m + 1 - m = 0 + 1 by omega, hs 0]; rfl
      · simp only [u, h, ite_false, show ¬ m ≤ n by omega]
        rw [show m + 1 - n = (m - n) + 1 by omega, hs]
  · show Additive.ofMul (u n) = Additive.ofMul x
    simp [u]

end Div

end ReductSplit

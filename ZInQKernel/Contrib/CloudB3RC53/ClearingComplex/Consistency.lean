import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.Patterns

/-!
# Consistency of the single identification GLUE

The GLUE input `ClearingComplex.Identification b dK hK cE tK` is used as a hypothesis. This file
checks that its fields do not contradict each other: the trivial remaining complex
(`unitCx 0`: no Smith disks, `D¹ = H₁ → H₂ = D²` the zero map) with central free ranks
`(0, 1, 1, 0)` satisfies every field, with `d_K = h_K = c_E = t_K = 0`
(`identification_trivial`, PROVED). Its augmentation is the trivial old complex, its
sign-evaluated differentials are (empty) new-local Schur complements, and its central complex
has `H¹ ≅ H² ≅ ℤ₂`, `H³ = 0`, with `J = H³_C = 0` in (5.7d). The generic pattern of this complex is
the rank-one pattern (`unitCx_zero_rankOne`).

The witness has an empty new-local family, so `Identification b 0 0 0 0` is always inhabited and
the content sits in the coordinate identity E1; `Identification` is superseded by `Identification2`
(`NewLocalModel.lean`, consistency with a nonempty family in `PlaceSupport.lean`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks aug sgnChar)
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.RankCounts.SmithCx

variable {b : ℕ}

theorem mi_unitCx {S : Type*} [CommRing S] (c : S) (i : ℕ) : (unitCx c).mi i = 0 := by
  rcases i with _ | _ | _ | i <;> rfl

/-- The zero family is a sign-evaluated new-local Schur complement (empty new-local family). -/
theorem isNewLocalSchur_zero {r c : Type} [Fintype r] [Fintype c] [DecidableEq r]
    [DecidableEq c] : IsNewLocalSchur (b := b) fun _ => (0 : Matrix r c OO) := by
  refine ⟨Unit, Empty, inferInstance, inferInstance, inferInstance, inferInstance, fun _ => 0,
    fun _ => 0, fun _ => by norm_num, fun _ => 1, fun _ => 0, ?_, 0, ?_, r, c, inferInstance,
    inferInstance, 0, 0, 0, 1, 1, ?_⟩
  · intro q; simp [Matrix.det_isEmpty]
  · ext i; exact i.1.elim
  · intro x; simp

theorem isNewLocalSchur_of_eq_zero {r c : Type} [Fintype r] [Fintype c] [DecidableEq r]
    [DecidableEq c] {Mx : Addr b → Matrix r c OO} (h : ∀ x, Mx x = 0) : IsNewLocalSchur Mx := by
  have : Mx = fun _ => 0 := funext h
  subst this
  exact isNewLocalSchur_zero

/-- The trivial block complex over `𝒪[G]`. -/
abbrev D₀ (b : ℕ) : BlockComplex (MonoidAlgebra OO (SignGroup b)) := unitCx 0

/-- Its (empty) Smith data. -/
abbrev A0₀ (b : ℕ) : (i : ℕ) → Matrix (Fin ((D₀ b).mi i)) (Fin ((D₀ b).mi i)) Lam := fun _ => 0
abbrev s₀ (b : ℕ) : (i : ℕ) → Fin ((D₀ b).mi i) → ℤ_[2] := fun _ _ => 1

theorem empty_mi (i : ℕ) : IsEmpty (Fin ((D₀ b).mi i)) := by
  rw [mi_unitCx]; infer_instance

theorem central₀ (i : ℕ) :
    (A0₀ b i).map PowerSeries.constantCoeff = Matrix.diagonal (s₀ b i) := by
  have := empty_mi (b := b) i
  ext j; exact isEmptyElim j

/-- The Smith data of the trivial complex. -/
abbrev B₀ (b : ℕ) : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO :=
  (D₀ b).toSmithBlocks (A0₀ b) (s₀ b) (fun _ _ => one_ne_zero) central₀

theorem hamp₀ : ∀ i, 3 ≤ i → i < (B₀ b).n → (B₀ b).m i = 0 := fun i hi hn => by
  change i < 3 at hn
  omega

/-- Free generators `(0, 1, 1, 0)`. -/
def fr₀ : ℕ → ℕ := fun i => if i = 1 ∨ i = 2 then 1 else 0

theorem mTot₀ : (B₀ b).mTot = 0 := by
  simp [SmithBlocks.mTot, BlockComplex.toSmithBlocks, mi_unitCx]

theorem dd₀ (i : ℕ) : dd (B₀ b) i = 0 := by
  unfold dd
  split_ifs
  · exact mi_unitCx _ i
  · rfl

theorem subsingleton_centralH₀_three : Subsingleton ((centralH (B₀ b)) fr₀ 3) := by
  have e := Hequiv (f := fr₀) (σ (B₀ b)) (σ_ne (B₀ b)) 3
  have : Subsingleton ((Fin (fr₀ 3) → ℤ_[2]) × Q (σ (B₀ b)) 3) := by
    have h1 : Subsingleton (Fin (fr₀ 3) → ℤ_[2]) :=
      ⟨fun a b => funext fun j => (show Fin 0 from j).elim0⟩
    have h2 : Subsingleton (Q (σ (B₀ b)) 3) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ a
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ b
      congr 1
      funext j
      have hj : db (dd (B₀ b)) 3 = 0 := dd₀ 2
      exact (Fin.cast hj j).elim0
    infer_instance
  exact e.toEquiv.subsingleton

theorem sum_val_σ₀ (i : ℕ) : ∑ j, ((σ (B₀ b)) i j).valuation = 0 := by
  have : IsEmpty (Fin (dd (B₀ b) i)) := by rw [dd₀]; infer_instance
  simp

/-- **The central counts of the trivial complex** (`BudgetInputs` with all constants `0`). -/
theorem budgetInputs₀ : BudgetInputs (B₀ b) 0 0 0 0 := by
  refine ⟨fr₀, ?_, (centralH (B₀ b)) fr₀ 1, (centralH (B₀ b)) fr₀ 2, PUnit, PUnit, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, LinearEquiv.refl _ _, LinearMap.id, 0, 0, 0,
    ⟨Function.injective_id, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sum_finrank_centralCx (B₀ b) fr₀ hamp₀, mTot₀]
    rw [Fin.sum_univ_four]
    simp [fr₀]
  · intro x; simp
  · intro x; exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · intro x; exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · intro x
    have := subsingleton_centralH₀_three (b := b)
    exact ⟨0, Subsingleton.elim _ _⟩
  · rw [length_torsion_H (σ (B₀ b)) (σ_ne (B₀ b)) 1, length_Q_succ (σ (B₀ b)) (σ_ne (B₀ b)) 0,
      sum_val_σ₀]
  · simp
  · rw [length_torsion_H (σ (B₀ b)) (σ_ne (B₀ b)) 2, length_Q_succ (σ (B₀ b)) (σ_ne (B₀ b)) 1,
      sum_val_σ₀]
  · simp
  · simp [finrank_centralH, fr₀]
  · simp [finrank_centralH, fr₀]

/-- **Consistency of the identification GLUE** (PROVED): the trivial remaining complex satisfies
every field of `Identification b 0 0 0 0`. -/
def identification_trivial (b : ℕ) : Identification b 0 0 0 0 where
  D := D₀ b
  A0 := A0₀ b
  s := s₀ b
  s_ne := fun _ _ => one_ne_zero
  central := central₀
  aug_eq := fun i => by
    have := empty_mi (b := b) i
    ext j; exact isEmptyElim j
  poles0 := isNewLocalSchur_of_eq_zero fun x => by ext i j; exact j.elim0
  poles1 := isNewLocalSchur_of_eq_zero fun x => by
    ext i j
    show Determinant.signEval (sgnChar x) 0 = 0
    exact map_zero _
  poles2 := isNewLocalSchur_of_eq_zero fun x => by ext i j; exact i.elim0
  budget := budgetInputs₀

theorem identification_nonempty (b : ℕ) : Nonempty (Identification b 0 0 0 0) :=
  ⟨identification_trivial b⟩

/-- The trivial identification has the rank-one generic pattern at every sign character. -/
theorem identification_trivial_rankOne (b : ℕ) (x : Addr b) :
    (identification_trivial b).D.RankOnePattern x :=
  unitCx_zero_rankOne x

end ZInQ.Contrib.CloudB3RC53.ClearingComplex

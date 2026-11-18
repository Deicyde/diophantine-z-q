import Mathlib

/-!
# Lane RC23-visibility: the local neighbour count behind (O.6)

Manuscript, Appendix F, proof of Proposition `ex:app-theta-form` (tex 8409–9099), paragraph
"All-index recurrence and its phases" (tex 9039–9058), with `Q_B(x) = Nrd(x) = −x²` (tex 8497).

At a good odd prime `p`, `R_p = M₂(ℤ_p)` and `V_p = 𝔰𝔩₂`; on trace-zero matrices
`Q_B(x) = Nrd(x) = −x² = det x`. The `p + 1` neighbours are indexed by the lines of `𝔽_p²`; that an
integral `x` lies in the neighbour of a line exactly when its reduction preserves the line is the
standard description of the neighbours, used at tex 9042–9044 and not formalized here. This file
proves the count of preserved lines entering (O.6):

* `−x² = det(x) · 1` for a trace-zero `2 × 2` matrix (tex 8497): `neg_mul_self_eq_det`;
* `𝔽_p²` has `p + 1` lines (tex 9042): `card_lines`;
* a nonzero trace-zero `x` over `𝔽_p` preserves exactly `1 + (−det x / p)` lines (tex 9043–9044):
  `card_preserved_lines`; the nilpotent case gives one line: `card_preserved_lines_nilpotent`; for
  integral `x` with nonzero reduction and `Q_B(x) = n` the count is `1 + (−n/p)`:
  `card_preserved_lines_int` (entries in `ℤ`) and `card_preserved_lines_padic` (entries in `ℤ_p`);
* if `x ∈ pR_p⁰` (zero reduction) all `p + 1` lines are preserved, an excess of `p` over the formula
  (tex 9045–9046): `card_preserved_lines_zero`, `card_preserved_lines_int_zero`.

Lines are the points of Mathlib's projective line `ℙ (ZMod p) (Fin 2 → ZMod p)`, and `x` preserves the
line `L` when it maps a representative of `L` into `L` (`Preserves`). All theorems are PROVED; lane
RC12 had left this count as GLUE.
-/

namespace ZInQ.Manuscript.RC.Visibility

open Matrix
open scoped LinearAlgebra.Projectivization

/-- **PROVED (tex 8497).** For a trace-zero `2 × 2` matrix over a commutative ring,
`−x² = det(x) · 1`; so on `V_p = 𝔰𝔩₂` the form `Q_B(x) = Nrd(x) = −x²` is `det x`. -/
theorem neg_mul_self_eq_det {R : Type*} [CommRing R] (x : Matrix (Fin 2) (Fin 2) R)
    (hx : x.trace = 0) : -(x * x) = x.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have h11 : x 1 1 = -x 0 0 := by rw [trace_fin_two] at hx; linear_combination hx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, det_fin_two, h11] <;> ring

variable {K : Type*} [Field K]

/-- The matrix `x` preserves the line `L` of `K²`: `x` maps a representative of `L` into `L`
(tex 9043). Kind: definition. -/
def Preserves (x : Matrix (Fin 2) (Fin 2) K) (L : ℙ K (Fin 2 → K)) : Prop :=
  x.mulVec L.rep ∈ L.submodule

/-- **PROVED (tex 9043).** `x` preserves the line through `v ≠ 0` iff `v` is an eigenvector:
`x v = μ v` for some `μ` (independent of the representative). -/
theorem preserves_mk (x : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) (hv : v ≠ 0) :
    Preserves x (Projectivization.mk K v hv) ↔ ∃ μ : K, x.mulVec v = μ • v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  unfold Preserves
  rw [← ha, Projectivization.submodule_mk, Submodule.mem_span_singleton, Units.smul_def,
    Matrix.mulVec_smul]
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨(a : K)⁻¹ * μ, ?_⟩
    rw [mul_smul, hμ, smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul]
  · rintro ⟨μ, hμ⟩
    exact ⟨(a : K) * μ, by rw [hμ, smul_smul]⟩

/-- The lines `[0 : 1]` (`none`) and `[1 : t]` (`some t`) of `K²` (tex 9042).
Kind: definition. -/
def lineOf : Option K → ℙ K (Fin 2 → K)
  | none => Projectivization.mk K ![0, 1] (fun h => by simpa using congrFun h 1)
  | some t => Projectivization.mk K ![1, t] (fun h => by simpa using congrFun h 0)

/-- **PROVED (tex 9042).** The lines `[0 : 1]`, `[1 : t]` are pairwise distinct. -/
theorem lineOf_injective : Function.Injective (lineOf (K := K)) := by
  rintro (_ | s) (_ | t) h
  · rfl
  · exfalso
    simp only [lineOf] at h
    rw [Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp at h0 h1
    rw [h0] at h1
    simp at h1
  · exfalso
    simp only [lineOf] at h
    rw [Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    simp at h0
  · simp only [lineOf] at h
    rw [Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp at h0 h1
    rw [h0, one_mul] at h1
    rw [h1]

/-- **PROVED (tex 9042).** Every line of `K²` is `[0 : 1]` or some `[1 : t]`. -/
theorem lineOf_surjective : Function.Surjective (lineOf (K := K)) := by
  intro L
  induction L with
  | h v hv =>
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [h0, h1])
      refine ⟨none, ?_⟩
      simp only [lineOf]
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨(v 1)⁻¹, ?_⟩
      ext i
      fin_cases i <;> simp [h0, h1]
    · refine ⟨some (v 1 / v 0), ?_⟩
      simp only [lineOf]
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨(v 0)⁻¹, ?_⟩
      ext i
      fin_cases i
      · simp [h0]
      · simp
        field_simp

/-- **PROVED (tex 9043–9044).** `x` preserves `[0 : 1]` iff `x₀₁ = 0` (for `x = (a b; c −a)`:
iff `b = 0`). -/
theorem preserves_none (x : Matrix (Fin 2) (Fin 2) K) :
    Preserves x (lineOf none) ↔ x 0 1 = 0 := by
  simp only [lineOf]
  rw [preserves_mk]
  constructor
  · rintro ⟨μ, hμ⟩
    have h0 := congrFun hμ 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · intro h
    refine ⟨x 1 1, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

/-- **PROVED (tex 9043–9044).** `x` preserves `[1 : t]` iff `x₀₁ t² + (x₀₀ − x₁₁) t − x₁₀ = 0`
(for `x = (a b; c −a)`: iff `b t² + 2a t − c = 0`). -/
theorem preserves_some (x : Matrix (Fin 2) (Fin 2) K) (t : K) :
    Preserves x (lineOf (some t)) ↔ x 0 1 * t ^ 2 + (x 0 0 - x 1 1) * t - x 1 0 = 0 := by
  simp only [lineOf]
  rw [preserves_mk]
  constructor
  · rintro ⟨μ, hμ⟩
    have h0 := congrFun hμ 0
    have h1 := congrFun hμ 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    rw [← h0] at h1
    linear_combination -h1
  · intro h
    refine ⟨x 0 0 + x 0 1 * t, ?_⟩
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination -h

/-- **PROVED (tex 9042–9044).** Over a finite field, the number of lines preserved by `x` is
`[x₀₁ = 0] + #{t : x₀₁ t² + (x₀₀ − x₁₁) t − x₁₀ = 0}` (the line `[0 : 1]` and the lines `[1 : t]`). -/
theorem card_preserved_eq [Fintype K] [DecidableEq K] (x : Matrix (Fin 2) (Fin 2) K) :
    Nat.card {L : ℙ K (Fin 2 → K) // Preserves x L} =
      (if x 0 1 = 0 then 1 else 0) +
        (Finset.univ.filter (fun t : K => x 0 1 * t ^ 2 + (x 0 0 - x 1 1) * t - x 1 0 = 0)).card := by
  classical
  have e : {o : Option K // Preserves x (lineOf o)} ≃ {L : ℙ K (Fin 2 → K) // Preserves x L} :=
    (Equiv.ofBijective lineOf ⟨lineOf_injective, lineOf_surjective⟩).subtypeEquiv
      (fun o => Iff.rfl)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_option, Finset.card_filter]
  simp only [preserves_none, preserves_some]

/-- **PROVED (tex 9042).** The `p + 1` neighbours: `𝔽_p²` has `p + 1` lines. -/
theorem card_lines (p : ℕ) [Fact p.Prime] :
    Nat.card (ℙ (ZMod p) (Fin 2 → ZMod p)) = p + 1 := by
  rw [Projectivization.card_of_finrank_two _ _ (Module.finrank_fin_fun _), Nat.card_zmod]

/-- **PROVED (tex 9043–9044).** For an odd prime `p` and a nonzero trace-zero
`x = (a b; c −a)` over `𝔽_p`, the number of lines preserved by `x` is `1 + (−det x / p)`, the
nilpotent case (`det x = 0`) included. Here `−det x = a² + bc`; for `b ≠ 0` the map `t ↦ bt + a`
carries the roots of `bt² + 2at − c` onto the square roots of `a² + bc`, counted by
`quadraticChar_card_sqrts`; for `b = 0` the line `[0 : 1]` is preserved, plus the root
`t = c/(2a)` if `a ≠ 0` (then `−det x = a²` is a nonzero square), and nothing else if `a = 0`
(then `c ≠ 0` and `−det x = 0`). -/
theorem card_preserved_lines {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (x : Matrix (Fin 2) (Fin 2) (ZMod p)) (htr : x.trace = 0) (hx : x ≠ 0) :
    (Nat.card {L : ℙ (ZMod p) (Fin 2 → ZMod p) // Preserves x L} : ℤ) =
      1 + quadraticChar (ZMod p) (-x.det) := by
  have h11 : x 1 1 = -x 0 0 := by rw [trace_fin_two] at htr; linear_combination htr
  have hdet : -x.det = x 0 0 ^ 2 + x 0 1 * x 1 0 := by rw [det_fin_two, h11]; ring
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hF
  rw [card_preserved_eq, hdet, h11]
  set a := x 0 0 with ha_def
  set b := x 0 1 with hb_def
  set c := x 1 0 with hc_def
  by_cases hb : b = 0
  · rw [ite_eq_left hb]
    by_cases ha : a = 0
    · have hc : c ≠ 0 := by
        intro hc
        apply hx
        ext i j
        fin_cases i <;> fin_cases j
        · exact ha
        · exact hb
        · exact hc
        · simp [h11, ha]
      have hempty :
          Finset.univ.filter (fun t : ZMod p => b * t ^ 2 + (a - -a) * t - c = 0) = ∅ := by
        ext t
        simp [ha, hb, hc]
      rw [hempty, ha, hb]
      simp
    · have hone : Finset.univ.filter (fun t : ZMod p => b * t ^ 2 + (a - -a) * t - c = 0) =
          {c / (2 * a)} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hb]
        constructor
        · intro h
          field_simp
          linear_combination h
        · intro h
          rw [h]
          field_simp
          ring
      rw [hone, Finset.card_singleton, hb, zero_mul, add_zero, quadraticChar_sq_one' ha]
      norm_num
  · rw [ite_eq_right hb]
    have hcard : (Finset.univ.filter (fun t : ZMod p => b * t ^ 2 + (a - -a) * t - c = 0)).card =
        {s : ZMod p | s ^ 2 = a ^ 2 + b * c}.toFinset.card := by
      apply Finset.card_nbij' (fun t => b * t + a) (fun s => (s - a) / b)
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
          Set.coe_toFinset] at ht ⊢
        linear_combination b * ht
      · intro s hs
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
          Set.coe_toFinset] at hs ⊢
        have ht : b * ((s - a) / b) = s - a := by field_simp
        have : b * (b * ((s - a) / b) ^ 2 + (a - -a) * ((s - a) / b) - c) = 0 := by
          linear_combination (b * ((s - a) / b) + a + s) * ht + hs
        exact (mul_eq_zero.mp this).resolve_left hb
      · intro t _
        simp only
        field_simp
        ring
      · intro s _
        simp only
        field_simp
        ring
    rw [hcard, zero_add, quadraticChar_card_sqrts hF]
    ring

/-- **PROVED (tex 9044, "including the nilpotent case").** A nonzero nilpotent trace-zero `x`
over `𝔽_p` (`p` odd) preserves exactly one line; here `det x = 0` by `neg_mul_self_eq_det`. -/
theorem card_preserved_lines_nilpotent {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (x : Matrix (Fin 2) (Fin 2) (ZMod p)) (htr : x.trace = 0) (hx : x ≠ 0) (hnil : x * x = 0) :
    Nat.card {L : ℙ (ZMod p) (Fin 2 → ZMod p) // Preserves x L} = 1 := by
  have hdet : x.det = 0 := by
    have h := congrFun (congrFun (neg_mul_self_eq_det x htr) 0) 0
    simpa [hnil] using h.symm
  have h := card_preserved_lines hp2 x htr hx
  rw [hdet, neg_zero, MulChar.map_zero, add_zero] at h
  exact_mod_cast h

/-- **PROVED (tex 9043–9044, the integral form).** For an odd prime `p` and an integral trace-zero
`x` with nonzero reduction mod `p` and `Q_B(x) = det x = n`, the reduction preserves exactly
`1 + (−n/p)` lines. -/
theorem card_preserved_lines_int {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (x : Matrix (Fin 2) (Fin 2) ℤ) (htr : x.trace = 0)
    (hx : x.map (Int.castRingHom (ZMod p)) ≠ 0) {n : ℤ} (hn : x.det = n) :
    (Nat.card {L : ℙ (ZMod p) (Fin 2 → ZMod p) //
        Preserves (x.map (Int.castRingHom (ZMod p))) L} : ℤ) = 1 + legendreSym p (-n) := by
  have htr' : (x.map (Int.castRingHom (ZMod p))).trace = 0 := by
    rw [← AddMonoidHom.map_trace, htr, map_zero]
  rw [card_preserved_lines hp2 _ htr' hx]
  have hdet : (x.map (Int.castRingHom (ZMod p))).det = ((n : ℤ) : ZMod p) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hn, eq_intCast]
  rw [hdet, legendreSym, Int.cast_neg]

/-- **PROVED (tex 9041–9044, over `ℤ_p`).** For `x ∈ R_p⁰ = 𝔰𝔩₂(ℤ_p)` with nonzero reduction and
`Q_B(x) = det x = n`, the reduction preserves exactly `1 + (−n/p)` lines (`p` odd). -/
theorem card_preserved_lines_padic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (x : Matrix (Fin 2) (Fin 2) ℤ_[p]) (htr : x.trace = 0)
    (hx : x.map PadicInt.toZMod ≠ 0) {n : ℤ_[p]} (hn : x.det = n) :
    (Nat.card {L : ℙ (ZMod p) (Fin 2 → ZMod p) // Preserves (x.map PadicInt.toZMod) L} : ℤ) =
      1 + quadraticChar (ZMod p) (PadicInt.toZMod (-n)) := by
  have htr' : (x.map PadicInt.toZMod).trace = 0 := by
    rw [← AddMonoidHom.map_trace, htr, map_zero]
  rw [card_preserved_lines hp2 _ htr' hx, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hn,
    RingHom.map_neg]

/-- **PROVED (tex 9045–9046).** If the reduction is zero (`x ∈ pR_p⁰`), every one of the `p + 1`
lines is preserved, and the count exceeds the formula `1 + (−det x / p)` (here `1 + (0/p) = 1`)
by `p`. -/
theorem card_preserved_lines_zero {p : ℕ} [Fact p.Prime]
    (x : Matrix (Fin 2) (Fin 2) (ZMod p)) (hx : x = 0) :
    (∀ L, Preserves x L) ∧
      Nat.card {L : ℙ (ZMod p) (Fin 2 → ZMod p) // Preserves x L} = p + 1 ∧
        (Nat.card {L : ℙ (ZMod p) (Fin 2 → ZMod p) // Preserves x L} : ℤ) =
          (1 + quadraticChar (ZMod p) (-x.det)) + p := by
  have hall : ∀ L, Preserves x L := fun L => by
    rw [Preserves, hx, Matrix.zero_mulVec]
    exact Submodule.zero_mem _
  have hcard : Nat.card {L : ℙ (ZMod p) (Fin 2 → ZMod p) // Preserves x L} = p + 1 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), card_lines]
  refine ⟨hall, hcard, ?_⟩
  rw [hcard, hx, Matrix.det_zero, neg_zero, MulChar.map_zero]
  push_cast
  ring

/-- **PROVED (tex 9045–9046, the integral form).** If every entry of the integral `x` is divisible
by `p` (`x ∈ pR_p⁰`) and `Q_B(x) = det x = n`, all `p + 1` lines are preserved by the (zero)
reduction, which is `p` more than `1 + (−n/p)` (here `(−n/p) = 0`). -/
theorem card_preserved_lines_int_zero {p : ℕ} [Fact p.Prime]
    (x : Matrix (Fin 2) (Fin 2) ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j) {n : ℤ} (hn : x.det = n) :
    (Nat.card {L : ℙ (ZMod p) (Fin 2 → ZMod p) //
        Preserves (x.map (Int.castRingHom (ZMod p))) L} : ℤ) =
      (1 + legendreSym p (-n)) + p := by
  have h0 : x.map (Int.castRingHom (ZMod p)) = 0 := by
    ext i j
    simp only [Matrix.map_apply, eq_intCast, Matrix.zero_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hx i j)
  have hdet : (x.map (Int.castRingHom (ZMod p))).det = ((n : ℤ) : ZMod p) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hn, eq_intCast]
  obtain ⟨-, -, h⟩ := card_preserved_lines_zero _ h0
  rw [h, hdet, legendreSym, Int.cast_neg]

end ZInQ.Manuscript.RC.Visibility

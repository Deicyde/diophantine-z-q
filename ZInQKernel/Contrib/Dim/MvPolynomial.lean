import Mathlib

/-!
# Heights of maximal ideals of polynomial rings over a field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task infra-smooth-dim, `scratch/infra-smooth-dim/`). Mathlib only.

## Main results

* `ZInQ.Contrib.Dim.height_eq_natCard_of_isMaximal_mvPolynomial`: for a field `k`, a finite type
  `ι` and a maximal ideal `M` of `k[x_i : i ∈ ι]`, `ht M = |ι|`.
* `ZInQ.Contrib.Dim.ringKrullDim_mvPolynomial_fin`: `dim k[x_1, ..., x_s] = s`.
-/

namespace ZInQ.Contrib.Dim

open Ideal

/-- **Every maximal ideal of `k[x_i : i ∈ ι]` has height `|ι|`** (`k` a field, `ι` finite).
Proof by induction on `ι` through `Option`, using `k[x_ι][y] ≅ k[x_{Option ι}]` and
`ht P = ht (P ∩ k[x_ι]) + 1` for maximal `P` of a polynomial ring over a Jacobson ring. -/
theorem height_eq_natCard_of_isMaximal_mvPolynomial (k : Type*) [Field k] :
    ∀ (ι : Type) [Finite ι] (M : Ideal (MvPolynomial ι k)) [M.IsMaximal],
      M.height = Nat.card ι := by
  intro ι _
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    intro M _
    have e' := (MvPolynomial.renameEquiv k e).toRingEquiv
    have : (M.map e'.symm).IsMaximal := map_isMaximal_of_equiv e'.symm
    rw [← e'.symm.height_map M, H, Nat.card_congr e]
  | h_empty =>
    intro M _
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (I := M) IsPrime.ne_top'
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      at h1
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero, add_zero] at h1
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero]
    exact_mod_cast nonpos_iff_eq_zero.mp (by exact_mod_cast h1)
  | @h_option α _ IH =>
    intro M _
    let e := (MvPolynomial.optionEquivLeft k α).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := map_isMaximal_of_equiv e
    let p := P.comap (Polynomial.C : MvPolynomial α k →+* _)
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver p := ⟨rfl⟩
    rw [← e.height_map M, Polynomial.height_eq_height_add_one p P, IH p]
    simp [Nat.card_eq_fintype_card, Fintype.card_option]

/-- `dim k[x_1, ..., x_s] = s` for a field `k`. -/
theorem ringKrullDim_mvPolynomial_fin (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

end ZInQ.Contrib.Dim

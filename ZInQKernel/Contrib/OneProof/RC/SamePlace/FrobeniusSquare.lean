import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Comparison

/-! # `frobenius_sq` from the operator comparison (rc-same-place1, item 7)

* (a) `uniformizer_involutive`: the right division-uniformizer permutation
  `Adelic.uniformizer ell h N hN` of the ideal classes is an involution. Route (the lead's ruling
  R4), mirroring `Adelic.atkin_involutive`: apply `rightClassPerm_involutive` with the central
  rational unit `u = RightIdeal.scalarUnit ell` and `r = (diagonal u)⁻¹ * (k * k)` for the
  uniformizer adele `k`. At `ell` the local square is `Π² = −ell` (`divisionUnit_sq`, a coordinate
  computation in `ℍ[ℚ_ell, -1, 0, -ell]`), so `r_ell = −1`, an integral unit
  (`neg_one_mem_localUnits`); at `t ≠ ell`, `k_t = 1` and `r_t = ell⁻¹`, a `t`-adic unit.
* (b) `frobenius_involutive`: for every coarse fibre `X` with `X.ss = univ`, every class-set
  comparison `J` (GLUE) and every operator comparison `O` (ELLIOT), `X.frobenius` is an
  involution: every point is `(J.classes z).val`, and `O.frobenius` twice reduces the claim to
  (a) through `uniformizerOnDoubleCosets`.

`frobenius_involutive` inherits `O`'s ELLIOT status, and a future discharge of `O` must not assume
it. A direct moduli proof (tex 8469–8473: a model over `F_{ell^2}` with scalar Frobenius, so every
supersingular pair class is `F_{ell^2}`-rational; UNVERIFIED) would remove the dependence on `O`.

Provenance: on the spot (c), the route of the lead's ruling R4. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Manuscript.RC.SamePlace

open Eichler Adelic

open private divisionUnit diagonal_scalar_val from
  ZInQKernel.Contrib.OneProof.RC.Adelic.Operations

section Local

variable {a b : ℚ}

/-- `−1` is a local unit of every order at every prime. -/
theorem neg_one_mem_localUnits (R : Order a b) (p : Prime) :
    (-1 : (Bp p.val a b)ˣ) ∈ localUnits R p := by
  refine ⟨?_, ?_⟩
  · change -(1 : Bp p.val a b) ∈ R.completion p.val
    exact neg_mem (one_mem _)
  · rw [inv_neg_one]
    change -(1 : Bp p.val a b) ∈ R.completion p.val
    exact neg_mem (one_mem _)

end Local

variable (ell : ℕ) [Fact ell.Prime] (h : ell % 4 = 3) (N : ℕ) (hN : 0 < N)

/-- The division uniformizer of the level order at `ell` is `j = ⟨0, 0, 1, 0⟩` in
`ℍ[ℚ_ell, -1, 0, -ell]`. -/
theorem divisionUnit_val :
    ((divisionUnit ell h : (Bp ell (-1) (-(ell : ℚ)))ˣ) : Bp ell (-1) (-(ell : ℚ))) =
      ⟨0, 0, 1, 0⟩ := by
  ext <;> rfl

/-- **`Π² = −ell`** for the division uniformizer of the level order at `ell` (coordinate
computation with `QuaternionAlgebra.mk_mul_mk`). -/
theorem divisionUnit_sq :
    ((divisionUnit ell h : (Bp ell (-1) (-(ell : ℚ)))ˣ) : Bp ell (-1) (-(ell : ℚ))) *
        (divisionUnit ell h : (Bp ell (-1) (-(ell : ℚ)))ˣ) =
      algebraMap ℚ_[ell] (Bp ell (-1) (-(ell : ℚ))) (-(ell : ℚ_[ell])) := by
  rw [divisionUnit_val, QuaternionAlgebra.mk_mul_mk]
  ext <;> simp

/-- **The division uniformizer permutation is an involution** (tex 8489–8490; ruling R4). -/
theorem uniformizer_involutive : Function.Involutive (Adelic.uniformizer ell h N hN) := by
  let R := LevelR ell h N hN
  let q : Prime := ⟨ell, Fact.out⟩
  have hm : ell ≠ 0 := (Fact.out : ell.Prime).ne_zero
  let u : (B (-1) (-(ell : ℚ)))ˣ := RightIdeal.scalarUnit ell hm
  let k := single R q (divisionUnit ell h)
  let r := (diagonal R u)⁻¹ * (k * k)
  have hunit : r ∈ integralUnits R := by
    intro t
    change ((diagonal R u).val t)⁻¹ * (k.val t * k.val t) ∈ localUnits R t
    by_cases ht : t = q
    · subst ht
      have hsq : k.val q * k.val q = -(diagonal R u).val q := by
        apply Units.ext
        change ((k.val q : Bp ell (-1) (-(ell : ℚ))) * (k.val q : Bp ell (-1) (-(ell : ℚ)))) =
          -((diagonal R u).val q : Bp ell (-1) (-(ell : ℚ)))
        unfold k
        rw [single_same, diagonal_scalar_val, divisionUnit_sq, map_neg]
      rw [hsq, mul_neg, inv_mul_cancel]
      exact neg_one_mem_localUnits R q
    -- Adapted from `Adelic.atkin_involutive` (RC/Adelic/Operations.lean:166-178, base
    -- 8b140cd2a), with `m = ell`.
    · unfold k
      rw [single_away ht, mul_one, mul_one]
      apply (localUnits R t).inv_mem
      have hd : ¬ t.val ∣ ell := fun hd => ht (Subtype.ext
        ((Nat.prime_dvd_prime_iff_eq t.prop Fact.out).mp hd))
      obtain ⟨v, hv⟩ := nat_isUnit t hd
      let V := Units.map (algebraMap ℤ_[t.val] (R.completion t.val)).toMonoidHom v
      rw [localUnits_eq_range]
      refine ⟨V, Units.ext ?_⟩
      rw [diagonal_scalar_val]
      change algebraMap ℤ_[t.val] (Bp t.val (-1) (-(ell : ℚ))) (v : ℤ_[t.val]) = _
      rw [hv]
      rfl
  unfold Adelic.uniformizer
  refine rightClassPerm_involutive _ _ u ?_ ⟨r, hunit⟩ ?_
  -- Adapted from `Adelic.atkin_involutive` (RC/Adelic/Operations.lean:180-189, base 8b140cd2a).
  · intro z
    apply Subtype.ext
    funext t
    apply Units.ext
    change (z.val t : Bp t.val (-1) (-(ell : ℚ))) * ((diagonal R u).val t : Bp t.val (-1) (-(ell : ℚ))) =
      ((diagonal R u).val t : Bp t.val (-1) (-(ell : ℚ))) * (z.val t : Bp t.val (-1) (-(ell : ℚ)))
    rw [diagonal_scalar_val]
    exact (Algebra.commutes _ _).symm
  · exact (mul_inv_cancel_left (diagonal R u) (k * k)).symm

/-- The uniformizer permutation on double cosets is an involution. -/
theorem uniformizerOnDoubleCosets_involutive :
    Function.Involutive (PMAdelic.uniformizerOnDoubleCosets ell h N hN) := by
  intro z
  simp only [PMAdelic.uniformizerOnDoubleCosets, Equiv.trans_apply, Equiv.symm_apply_apply,
    uniformizer_involutive ell h N hN _, Equiv.apply_symm_apply]

variable {ell h N hN}

/-- **`frobenius_sq` from the operator comparison** (ELLIOT, through `O.frobenius`): for every
coarse fibre with `X.ss = univ`, every `J` and every `O`, `X.frobenius` is an involution. -/
theorem frobenius_involutive {hcop : N.Coprime ell} {X : PMAdelic.CoarseFibre}
    (hss : X.ss = Set.univ) (J : PMAdelic.JetchevKane ell h N hN hcop X)
    (O : PMAdelic.OperatorComparison ell h N hN hcop X J) : Function.Involutive X.frobenius := by
  intro x
  have hx : x ∈ X.ss := hss ▸ Set.mem_univ x
  obtain ⟨z, hz⟩ := J.classes.surjective ⟨x, hx⟩
  have hz' : (J.classes z).val = x := congrArg Subtype.val hz
  rw [← hz', O.frobenius, O.frobenius, uniformizerOnDoubleCosets_involutive ell h N hN z]

end ZInQ.Manuscript.RC.SamePlace

#print axioms ZInQ.Manuscript.RC.SamePlace.neg_one_mem_localUnits
#print axioms ZInQ.Manuscript.RC.SamePlace.divisionUnit_sq
#print axioms ZInQ.Manuscript.RC.SamePlace.uniformizer_involutive
#print axioms ZInQ.Manuscript.RC.SamePlace.uniformizerOnDoubleCosets_involutive
#print axioms ZInQ.Manuscript.RC.SamePlace.frobenius_involutive

import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Smith form over a DVR: lengths of cokernels (Lane RC7, manuscript §9)

This file formalizes the length facts about finite free complexes over `ℤ_[p]` used in §9 of the
manuscript (`diophantine_zq.tex`):

* tex 5326–5334: the singular complexes `[ℤ₂² --(Φ - r)--> ℤ₂²]` (in degrees one and two) with
  nonzero determinant have zero degree-one cohomology, and their degree-two cokernel has length
  equal to the `2`-adic valuation of the determinant (so at most `c_E` each, and `2 c_E` in total);
* tex 5375–5383: a Smith disk `[ℤ₂ --(2^e u)--> ℤ₂]`, `u` a unit, contributes exactly `e` to the
  torsion length, and a sum of Smith disks contributes the sum of the valuations of its Smith
  entries.

Lengths are Mathlib's `Module.length` (valued in `ℕ∞`); the order of vanishing
`Ring.ord R x = Module.length R (R ⧸ Ideal.span {x})` is Mathlib's.  The general statement
(`length_quotient_range_eq_ord_det`) holds over any principal ideal domain and is proved with
Mathlib's Smith normal form for full-rank submodules; over `ℤ_[p]` the order of vanishing is the
`p`-adic valuation `PadicInt.valuation`.  Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Determinant

open Module

section PID

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Tex 5382–5383 (PROVED).**  The order of vanishing (length of the cyclic quotient) is additive
on finite products of nonzero elements of a domain: this is how the Smith entries of a sum of disks
add up to the total torsion length. -/
theorem ord_finset_prod {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Ring.ord_mul' R
      (mem_nonZeroDivisors_of_ne_zero (ha j (Finset.mem_insert_self j s))),
      ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))]

/-- **Tex 5326–5334 and 5375–5383 (PROVED), general form.**  Over a principal ideal domain `R`,
if a square matrix `X` has nonzero determinant then the cokernel of `X : Rⁿ → Rⁿ` has length equal
to the order of vanishing of `det X`, i.e. `length (Rⁿ ⧸ X Rⁿ) = length (R ⧸ (det X))`.

Proof: Smith normal form of the full-rank submodule `X Rⁿ`, which splits the cokernel as
`∏ i, R ⧸ (aᵢ)` with `det X` associated to `∏ i, aᵢ`. -/
theorem length_quotient_range_eq_ord_det [IsPrincipalIdealRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (X : Matrix n n R) (hX : X.det ≠ 0) :
    Module.length R ((n → R) ⧸ LinearMap.range X.mulVecLin) = Ring.ord R X.det := by
  set N := LinearMap.range X.mulVecLin
  have hinj : Function.Injective X.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hX
  -- `X` is an isomorphism onto its range, so the range has full rank.
  let e : (n → R) ≃ₗ[R] N := LinearEquiv.ofInjective X.mulVecLin hinj
  have h : Module.finrank R N = Module.finrank R (n → R) := e.finrank_eq.symm
  -- Smith normal form: bases `b'` of `Rⁿ` and `ab` of `N` with `ab i = a i • b' i`.
  let b := Pi.basisFun R n
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : (n → R) ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : (n → R) →ₗ[R] (n → R) := N.subtype ∘ₗ (e' : (n → R) →ₗ[R] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    simp only [f, e', LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply]
    exact ab_eq i
  -- The diagonal map has determinant `∏ i, a i`.
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  -- `det X` and `∏ i, a i` differ by a unit (two isomorphisms `Rⁿ ≃ N`).
  have hX' : X.mulVecLin = N.subtype ∘ₗ (e : (n → R) →ₗ[R] N) := by
    ext v; rfl
  have hassoc : Associated X.det (∏ i, a i) := by
    rw [← hdetf, ← LinearMap.det_toLin', Matrix.toLin'_apply', hX']
    exact LinearMap.associated_det_comp_equiv _ _ _
  -- The cokernel is `∏ i, R ⧸ (a i)`; lengths add.
  rw [(N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype,
    Ring.ord_eq_of_associated hassoc,
    ord_finset_prod _ _ (fun i _ => Submodule.smithNormalFormCoeffs_ne_zero b h i)]
  rfl

end PID

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- **Tex 5375–5383 (PROVED).**  Over `ℤ_[p]` the order of vanishing of a nonzero element is its
`p`-adic valuation: `length (ℤ_[p] ⧸ (x)) = v_p(x)`. -/
theorem ord_eq_valuation {x : ℤ_[p]} (hx : x ≠ 0) : Ring.ord ℤ_[p] x = (x.valuation : ℕ∞) := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [Ring.ord_mul_of_isUnit_left (Units.isUnit _),
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero PadicInt.prime_p.ne_zero),
    Ring.ord_of_irreducible PadicInt.irreducible_p]
  simp

/-- **Tex 5326–5334 (PROVED).**  A square matrix over `ℤ_[p]` with nonzero determinant is injective
(`ℤ_[p]` is a domain): the singular complex `[ℤ_[p]ⁿ --X--> ℤ_[p]ⁿ]` has zero cohomology in its
lower degree. -/
theorem ker_mulVecLin_eq_bot {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℤ_[p])
    (hX : X.det ≠ 0) : LinearMap.ker X.mulVecLin = ⊥ :=
  LinearMap.ker_eq_bot.mpr (Matrix.mulVec_injective_of_det_ne_zero hX)

/-- **Tex 5326–5334 (PROVED).**  A square matrix `X` over `ℤ_[p]` with nonzero determinant has
cokernel of length `v_p(det X)`: the singular complex `[ℤ_[p]ⁿ --X--> ℤ_[p]ⁿ]` has upper-degree
cohomology of length equal to the valuation of its determinant. -/
theorem length_quotient_range_eq_valuation_det {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℤ_[p]) (hX : X.det ≠ 0) :
    Module.length ℤ_[p] ((n → ℤ_[p]) ⧸ LinearMap.range X.mulVecLin) = (X.det.valuation : ℕ∞) := by
  rw [length_quotient_range_eq_ord_det X hX, ord_eq_valuation hX]

/-- **Tex 5375–5383 (PROVED).**  The cyclic case: for `a ≠ 0` in `ℤ_[p]`,
`length (ℤ_[p] ⧸ (a)) = v_p(a)`. -/
theorem length_quotient_span_eq_valuation {a : ℤ_[p]} (ha : a ≠ 0) :
    Module.length ℤ_[p] (ℤ_[p] ⧸ Ideal.span {a}) = (a.valuation : ℕ∞) :=
  ord_eq_valuation ha

/-- **Tex 5375–5383 (PROVED).**  A Smith entry `p^e u` with `u` a unit has valuation `e`. -/
theorem valuation_pow_mul_unit (e : ℕ) (u : ℤ_[p]ˣ) :
    ((p : ℤ_[p]) ^ e * (u : ℤ_[p])).valuation = e := by
  have hu : (u : ℤ_[p]).valuation = 0 := by
    have h := PadicInt.valuation_mul (p := p) u.ne_zero (u⁻¹).ne_zero
    rw [Units.mul_inv, PadicInt.valuation_one] at h
    omega
  rw [PadicInt.valuation_p_pow_mul _ _ u.ne_zero, hu, add_zero]

/-- **Tex 5375–5383 (PROVED).**  The torsion of a Smith disk `[ℤ_[p] --(p^e u)--> ℤ_[p]]`,
`u` a unit, has length exactly `e`. -/
theorem length_quotient_span_pow_mul_unit (e : ℕ) (u : ℤ_[p]ˣ) :
    Module.length ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ e * (u : ℤ_[p])}) = e := by
  rw [length_quotient_span_eq_valuation
    (mul_ne_zero (pow_ne_zero _ PadicInt.prime_p.ne_zero) u.ne_zero), valuation_pow_mul_unit]

/-- **Tex 5375–5383 (PROVED).**  A Smith disk `[ℤ_[p] --(p^e u)--> ℤ_[p]]` (as a `1 × 1` matrix),
`u` a unit, has zero cohomology in its lower degree and cokernel of length `e`. -/
theorem smith_disk_cohomology (e : ℕ) (u : ℤ_[p]ˣ) :
    LinearMap.ker (!![(p : ℤ_[p]) ^ e * (u : ℤ_[p])]).mulVecLin = ⊥ ∧
      Module.length ℤ_[p]
        ((Fin 1 → ℤ_[p]) ⧸ LinearMap.range (!![(p : ℤ_[p]) ^ e * (u : ℤ_[p])]).mulVecLin) = e := by
  have hdet : (!![(p : ℤ_[p]) ^ e * (u : ℤ_[p])]).det = (p : ℤ_[p]) ^ e * (u : ℤ_[p]) :=
    Matrix.det_fin_one_of _
  have hne : (!![(p : ℤ_[p]) ^ e * (u : ℤ_[p])]).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero (pow_ne_zero _ PadicInt.prime_p.ne_zero) u.ne_zero
  refine ⟨ker_mulVecLin_eq_bot _ hne, ?_⟩
  rw [length_quotient_range_eq_valuation_det _ hne, hdet, valuation_pow_mul_unit]

/-- **Tex 5375–5383 (PROVED).**  A direct sum of Smith disks `[ℤ_[p] --(p^{eᵢ} uᵢ)--> ℤ_[p]]`,
`uᵢ` units (including disks with `eᵢ = 0`), has torsion of length `∑ i, eᵢ`: every disk contributes
its exponent. -/
theorem length_quotient_range_diagonal_pow_mul_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (u : ι → ℤ_[p]ˣ) :
    Module.length ℤ_[p] ((ι → ℤ_[p]) ⧸
        LinearMap.range (Matrix.diagonal fun i => (p : ℤ_[p]) ^ e i * (u i : ℤ_[p])).mulVecLin) =
      ((∑ i, e i : ℕ) : ℕ∞) := by
  have hne : ∀ i, (p : ℤ_[p]) ^ e i * (u i : ℤ_[p]) ≠ 0 := fun i =>
    mul_ne_zero (pow_ne_zero _ PadicInt.prime_p.ne_zero) (u i).ne_zero
  have hdet : (Matrix.diagonal fun i => (p : ℤ_[p]) ^ e i * (u i : ℤ_[p])).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)
  rw [length_quotient_range_eq_ord_det _ hdet, Matrix.det_diagonal,
    ord_finset_prod _ _ (fun i _ => hne i), Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ord_eq_valuation (hne i), valuation_pow_mul_unit]

end Padic

section SingularComplex

/-- **Tex 5326–5328 (PROVED).**  For a `2 × 2` matrix `Φ` with trace `a` and determinant `r`,
`det (Φ - r) = r (r + 1 - a) = r det (1 - Φ)`. -/
theorem det_sub_smul_one_fin_two {R : Type*} [CommRing R] (Φ : Matrix (Fin 2) (Fin 2) R)
    (a r : R) (htr : Φ.trace = a) (hdet : Φ.det = r) :
    (Φ - r • (1 : Matrix (Fin 2) (Fin 2) R)).det = r * (r + 1 - a) ∧
      r * (r + 1 - a) = r * (1 - Φ).det := by
  subst htr hdet
  constructor
  · simp [Matrix.det_fin_two, Matrix.trace_fin_two]
    ring
  · simp [Matrix.det_fin_two, Matrix.trace_fin_two]
    ring

/-- **Tex 5326–5334 (PROVED).**  The rank-two singular complex `[ℤ₂² --X--> ℤ₂²]` with
`det X ≠ 0` (for instance `X = Φ - r`) has zero degree-one cohomology and degree-two cokernel of
length `v₂(det X)`. -/
theorem singular_complex_cohomology (X : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hX : X.det ≠ 0) :
    LinearMap.ker X.mulVecLin = ⊥ ∧
      Module.length ℤ_[2] ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range X.mulVecLin) =
        (X.det.valuation : ℕ∞) :=
  ⟨ker_mulVecLin_eq_bot X hX, length_quotient_range_eq_valuation_det X hX⟩

/-- **Tex 5326–5334 (PROVED).**  If the two singular complexes `[ℤ₂² --X--> ℤ₂²]` and
`[ℤ₂² --Y--> ℤ₂²]` (one at each place over the moving prime) have nonzero determinants of valuation
at most `c`, their degree-two cokernels have total length at most `2 c`. -/
theorem singular_complexes_total_length_le (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hX : X.det ≠ 0)
    (hY : Y.det ≠ 0) (c : ℕ) (hXc : X.det.valuation ≤ c) (hYc : Y.det.valuation ≤ c) :
    Module.length ℤ_[2] (((Fin 2 → ℤ_[2]) ⧸ LinearMap.range X.mulVecLin) ×
        ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range Y.mulVecLin)) ≤ 2 * c := by
  rw [Module.length_prod, length_quotient_range_eq_valuation_det X hX,
    length_quotient_range_eq_valuation_det Y hY]
  exact_mod_cast (by omega : X.det.valuation + Y.det.valuation ≤ 2 * c)

end SingularComplex

end ZInQ.Manuscript.RC.Determinant

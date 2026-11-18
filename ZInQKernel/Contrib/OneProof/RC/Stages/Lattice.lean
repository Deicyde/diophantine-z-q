import Mathlib

/-! The integral linear algebra in tex 8327–8347. We use the two elementary
unipotents explicitly for the full-lattice assertion (provenance (c)). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Stages

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {T : Type*} [AddCommGroup T] [Module ℤ_[2] T]

/-- In a closed additive subgroup of a 2-adic module, integral multiples extend
by density to all 2-adic multiples. -/
theorem smul_mem_of_closed [TopologicalSpace T] [ContinuousSMul ℤ_[2] T]
    (H : AddSubgroup T) (hH : IsClosed (H : Set T)) {x : T} (hx : x ∈ H) (a : ℤ_[2]) :
    a • x ∈ H := by
  refine PadicInt.denseRange_natCast.induction_on a
    (hH.preimage (continuous_id.smul continuous_const)) ?_
  intro n
  rw [Nat.cast_smul_eq_nsmul]
  exact H.nsmul_mem hx n

/-- The power of two contained in the ideal of any nonzero 2-adic integer. -/
theorem exists_two_pow_mul {c : ℤ_[2]} (hc : c ≠ 0) :
    ∃ a : ℕ, ∃ t : ℤ_[2], (2 : ℤ_[2]) ^ a = c * t := by
  obtain ⟨a, ha⟩ := PadicInt.ideal_eq_span_pow_p
    (s := Ideal.span {c}) (by simpa [Ideal.span_singleton_eq_bot] using hc)
  refine ⟨a, ?_⟩
  have hm : (2 : ℤ_[2]) ^ a ∈ Ideal.span {c} := ha ▸ Ideal.subset_span (by simp)
  exact Ideal.mem_span_singleton.mp hm

/-- A nonzero rank-two submodule invariant under all the permitted elementary
unipotents contains a full power-of-two lattice. -/
theorem full_lattice_of_unipotents (B : Module.Basis (Fin 2) ℤ_[2] T)
    (H : Submodule ℤ_[2] T) {n : ℕ}
    (hstable : ∀ i j : Fin 2, i ≠ j → ∀ x ∈ H,
      x + (2 : ℤ_[2]) ^ n • (B.coord j x • B i) ∈ H)
    {v : T} (hv : v ∈ H) (hvne : v ≠ 0) :
    ∃ a : ℕ, ∀ x : T, (2 : ℤ_[2]) ^ a • x ∈ H := by
  have hvcoord : ∃ j, B.coord j v ≠ 0 := by
    by_contra! h
    apply hvne
    apply B.repr.injective
    ext j
    simpa using h j
  obtain ⟨j, hj⟩ := hvcoord
  obtain ⟨i, hij⟩ : ∃ i : Fin 2, i ≠ j := exists_ne j
  have hin (x : T) (hx : x ∈ H) {i j : Fin 2} (hij : i ≠ j) :
      ((2 : ℤ_[2]) ^ n * B.coord j x) • B i ∈ H := by
    simpa only [add_sub_cancel_left, smul_smul] using
      H.sub_mem (hstable i j hij x hx) hx
  obtain ⟨s, r, hr⟩ := exists_two_pow_mul (c := B.coord j v) hj
  have hi : (2 : ℤ_[2]) ^ (n + s) • B i ∈ H := by
    have h := H.smul_mem r (hin v hv hij)
    rwa [smul_smul, mul_left_comm r, mul_comm r, ← hr, ← pow_add] at h
  have hj' : (2 : ℤ_[2]) ^ (n + (n + s)) • B j ∈ H := by
    have h := hin _ hi hij.symm
    rwa [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, ← pow_add] at h
  have hi' : (2 : ℤ_[2]) ^ (n + (n + s)) • B i ∈ H := by
    simpa only [smul_smul, ← pow_add] using H.smul_mem ((2 : ℤ_[2]) ^ n) hi
  refine ⟨n + (n + s), fun x => ?_⟩
  rw [← B.sum_repr x, Finset.smul_sum]
  apply H.sum_mem
  intro k _
  have hk : k = i ∨ k = j := by
    have hfin : ∀ (i j k : Fin 2), i ≠ j → k = i ∨ k = j := by decide
    exact hfin i j k hij
  have hB : (2 : ℤ_[2]) ^ (n + (n + s)) • B k ∈ H := by
    rcases hk with rfl | rfl
    · exact hi'
    · exact hj'
  rw [smul_comm]
  exact H.smul_mem _ hB

/-- Build the transvection using its inverse, with no determinant hypothesis. -/
def elementary (B : Module.Basis (Fin 2) ℤ_[2] T) (i j : Fin 2) (hij : i ≠ j)
    (r : ℤ_[2]) : T ≃ₗ[ℤ_[2]] T := by
  let N := (B.coord j).smulRight (B i)
  have hN (x : T) : N (N x) = 0 := by
    have h : B.coord j (B i) = 0 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hij.symm]
    simp [N, h]
  apply LinearEquiv.ofLinearMap (1 + r • N) (1 - r • N) <;>
    ext x <;>
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.smul_apply, map_add, map_sub, map_smul, hN, smul_zero,
      add_zero, sub_zero] <;> abel

/-- Pointwise formula for the elementary automorphism. -/
theorem elementary_apply (B : Module.Basis (Fin 2) ℤ_[2] T) (i j : Fin 2) (hij : i ≠ j)
    (r : ℤ_[2]) (x : T) :
    elementary B i j hij r x = x + r • (B.coord j x • B i) := rfl

/-- Dividing a nonzero integral fixed row by the generator of its image makes
it primitive. The row and a vector on which it takes value one are both integral. -/
theorem primitive_row_of_nonzero (C : T →ₗ[ℤ_[2]] T)
    (r : T →ₗ[ℤ_[2]] ℤ_[2]) (hne : r ≠ 0)
    (hr : ∀ x, r (C x) = r x) :
    ∃ (b : T →ₗ[ℤ_[2]] ℤ_[2]) (t : T), (∀ x, b (C x) = b x) ∧ b t = 1 := by
  let I : Ideal ℤ_[2] := r.range
  have hI : I ≠ ⊥ := by
    intro h
    apply hne
    apply LinearMap.ext
    intro x
    change r x = 0
    have hx : r x ∈ I := ⟨x, rfl⟩
    rwa [h, Ideal.mem_bot] at hx
  obtain ⟨e, he⟩ := PadicInt.ideal_eq_span_pow_p hI
  let q : ℤ_[2] := ((2 : ℕ) : ℤ_[2]) ^ e
  have he' : I = Ideal.span {q} := he
  have hq : q ≠ 0 := pow_ne_zero e (by norm_num)
  have hex (x : T) : ∃ u, r x = q * u := by
    apply Ideal.mem_span_singleton.mp
    rw [← he']
    exact ⟨x, rfl⟩
  choose b hb using hex
  let bₗ : T →ₗ[ℤ_[2]] ℤ_[2] :=
    { toFun := b
      map_add' := fun x y => mul_left_cancel₀ hq (by rw [mul_add, ← hb, ← hb, ← hb, map_add])
      map_smul' := fun a x => mul_left_cancel₀ hq (by
        change q * b (a • x) = q * (a * b x)
        rw [← hb, mul_left_comm, ← hb, map_smul, smul_eq_mul]) }
  have hmem : q ∈ I := by rw [he']; exact Ideal.subset_span (by simp)
  obtain ⟨t, ht⟩ : ∃ t, r t = q := hmem
  refine ⟨bₗ, t, fun x => mul_left_cancel₀ hq ?_, mul_left_cancel₀ hq ?_⟩
  · change q * b (C x) = q * b x
    rw [← hb, ← hb, hr]
  · change q * b t = q * 1
    rw [← hb, ht, mul_one]

/-- An integral involution other than minus the identity admits a primitive fixed
row. Choose a nonzero coordinate of (C + 1) and remove its maximal common power of two. -/
theorem primitive_row_of_involution (B : Module.Basis (Fin 2) ℤ_[2] T)
    (C : T →ₗ[ℤ_[2]] T) (hC : ∀ x, C (C x) = x) (hneg : C ≠ -1) :
    ∃ (b : T →ₗ[ℤ_[2]] ℤ_[2]) (t : T), (∀ x, b (C x) = b x) ∧ b t = 1 := by
  have hex : ∃ x, C x + x ≠ 0 := by
    by_contra! h
    apply hneg
    ext x
    exact eq_neg_of_add_eq_zero_left (h x)
  obtain ⟨x, hx⟩ := hex
  have hc : ∃ j, B.coord j (C x + x) ≠ 0 := by
    by_contra! h
    apply hx
    apply B.repr.injective
    apply Finsupp.ext
    intro j
    simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using h j
  obtain ⟨j, hj⟩ := hc
  let r : T →ₗ[ℤ_[2]] ℤ_[2] := (B.coord j).comp (C + 1)
  have hne : r ≠ 0 := by
    intro hr
    exact hj (show r x = 0 from by rw [hr]; rfl)
  apply primitive_row_of_nonzero C r hne
  intro y
  change B.coord j (C (C y) + C y) = B.coord j (C y + y)
  rw [hC, add_comm y]

#print axioms primitive_row_of_nonzero
#print axioms primitive_row_of_involution
#print axioms smul_mem_of_closed
#print axioms exists_two_pow_mul
#print axioms full_lattice_of_unipotents
#print axioms elementary
#print axioms elementary_apply

end ZInQ.Manuscript.RC.Stages

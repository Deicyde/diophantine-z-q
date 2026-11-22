import ZInQKernel.Contrib.OneProof.FowlerBridgesDiscriminant
import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.Data.ZMod.QuotientGroup

/-! # Uniqueness of quadratic orders from their trace discriminant

Identify an order with a rank-two algebra `ℤ[θ]` and its trace discriminant with
Mathlib’s polynomial discriminant. Mathlib classifies these quadratic algebras
over `ℤ` by their discriminant.
-/

namespace HDec.CMBranch.FowlerBridges

open NumberField Module TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

private theorem exists_basis_one (A : Type*) [CommRing A] [Nontrivial A]
    [Module.Free ℤ A] (h : finrank ℤ A = 2) :
    ∃ b : Basis (Fin 2) ℤ A, b 0 = 1 :=
  Module.IsUnimodular.exists_basis_zero_eq h (Module.Free.isUnimodular_one (R := ℤ) (A := A))

private theorem basis_discr (A : Type*) [CommRing A] (b : Basis (Fin 2) ℤ A) (h₀ : b 0 = 1)
    (a d : ℤ) (h₂ : b 1 * b 1 = a • b 0 + d • b 1) :
    Algebra.discr ℤ b = d ^ 2 + 4 * a := by
  have htr (x : A) : Algebra.trace ℤ A x = (Algebra.leftMulMatrix b x).trace :=
    Algebra.trace_eq_matrix_trace b x
  have hrep (x : A) (i j : Fin 2) :
      Algebra.leftMulMatrix b x i j = b.repr (x * b j) i :=
    Algebra.leftMulMatrix_eq_repr_mul b x i j
  have t1 : Algebra.trace ℤ A 1 = 2 := by
    rw [htr, Matrix.trace_fin_two, hrep, hrep, one_mul, one_mul, b.repr_self, b.repr_self]
    simp
  have td : Algebra.trace ℤ A (b 1) = d := by
    rw [htr, Matrix.trace_fin_two, hrep, hrep, h₀, mul_one, b.repr_self, h₂,
      map_add, map_smul, map_smul]
    simp
  have tdd : Algebra.trace ℤ A (b 1 * b 1) = 2 * a + d ^ 2 := by
    rw [h₂, map_add, map_smul, map_smul, h₀, t1, td]
    simp
    ring
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, h₀, one_mul, mul_one]
  rw [t1, td, tdd]
  ring

/-- On the standard quadratic algebra over the integers the polynomial
discriminant is the trace discriminant of its standard basis. -/
theorem quadraticAlgebra_basis_discr (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = QuadraticAlgebra.discr a b := by
  refine basis_discr _ _ (QuadraticAlgebra.basis_apply_zero a b) _ _ ?_
  rw [QuadraticAlgebra.basis_apply_zero, QuadraticAlgebra.basis_apply_one]
  exact QuadraticAlgebra.omega_mul_omega_eq_add

/-- Every order in a quadratic number field has integral rank two. -/
theorem order_finrank_eq_two {k : Type*} [Field k] [NumberField k] (hk : finrank ℚ k = 2)
    (O : NumberFieldOrder k) : finrank ℤ O.toSubalgebra = 2 := by
  let b := Module.Free.chooseBasis ℤ O.toSubalgebra
  let bQ := b.localizationLocalization ℚ ℤ⁰ k
  rw [Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis bQ, hk]

private theorem exists_order_algEquiv {k : Type*} [Field k] [NumberField k]
    (hk : finrank ℚ k = 2) (O : NumberFieldOrder k) :
    ∃ a b : ℤ, O.discr = QuadraticAlgebra.discr a b ∧
      Nonempty (O.toSubalgebra ≃ₐ[ℤ] QuadraticAlgebra ℤ a b) := by
  let : Algebra.IsQuadraticExtension ℤ O.toSubalgebra :=
    { finrank_eq_two' := order_finrank_eq_two hk O }
  obtain ⟨a, b, ⟨e⟩⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra
    (R := ℤ) (A := O.toSubalgebra)
  refine ⟨a, b, ?_, ⟨e⟩⟩
  rw [← O.discr_eq_discr ((QuadraticAlgebra.basis a b).map e.symm.toLinearEquiv),
    ← quadraticAlgebra_basis_discr]
  exact (Algebra.discr_eq_discr_of_algEquiv _ e.symm).symm

/-- The trace discriminant of any quadratic order is zero or one modulo four. -/
theorem order_discr_mod_four {k : Type*} [Field k] [NumberField k] (hk : finrank ℚ k = 2)
    (O : NumberFieldOrder k) : O.discr % 4 = 0 ∨ O.discr % 4 = 1 := by
  obtain ⟨a, b, hd, _⟩ := exists_order_algEquiv hk O
  rw [hd, QuadraticAlgebra.discr_def]
  simp only [Int.add_emod, Int.mul_emod_right, add_zero, Int.sq_emod_four]
  omega

/-- The discriminant determines a quadratic order up to ring isomorphism, including
when the two orders lie in different number fields. -/
theorem orders_ringEquiv_of_discr_eq {k l : Type*} [Field k] [NumberField k]
    [Field l] [NumberField l] (hk : finrank ℚ k = 2) (hl : finrank ℚ l = 2)
    (O : NumberFieldOrder k) (P : NumberFieldOrder l) (h : O.discr = P.discr) :
    Nonempty (O.toSubalgebra ≃+* P.toSubalgebra) := by
  obtain ⟨a, b, he, ⟨e⟩⟩ := exists_order_algEquiv hk O
  obtain ⟨c, d, hf, ⟨f⟩⟩ := exists_order_algEquiv hl P
  obtain ⟨g⟩ := QuadraticAlgebra.nonempty_algEquiv_int_iff.mpr (he.symm.trans (h.trans hf))
  exact ⟨(e.trans (g.trans f.symm)).toRingEquiv⟩

/-- Equality of order discriminants identifies the ambient quadratic fields by
localizing the order isomorphism. -/
theorem fields_ringEquiv_of_order_discr_eq {k l : Type*} [Field k] [NumberField k]
    [Field l] [NumberField l] (hk : finrank ℚ k = 2) (hl : finrank ℚ l = 2)
    (O : NumberFieldOrder k) (P : NumberFieldOrder l) (h : O.discr = P.discr) :
    Nonempty (k ≃+* l) := by
  obtain ⟨e⟩ := orders_ringEquiv_of_discr_eq hk hl O P h
  exact ⟨IsFractionRing.ringEquivOfRingEquiv e⟩

/-- A quadratic field is determined by its maximal order discriminant. -/
theorem fields_ringEquiv_of_discr_eq {k l : Type*} [Field k] [NumberField k]
    [Field l] [NumberField l] (hk : finrank ℚ k = 2) (hl : finrank ℚ l = 2)
    (h : NumberField.discr k = NumberField.discr l) : Nonempty (k ≃+* l) := by
  apply fields_ringEquiv_of_order_discr_eq hk hl (maximalNumberFieldOrder k)
    (maximalNumberFieldOrder l)
  simpa only [NumberFieldOrder.discr_maximal] using h

/-- The order discriminant determines the field discriminant and the positive
conductor index in its square-index factorization. -/
theorem discr_and_index_eq_of_order_discr_eq {k l : Type*} [Field k] [NumberField k]
    [Field l] [NumberField l] (hk : finrank ℚ k = 2) (hl : finrank ℚ l = 2)
    (O : NumberFieldOrder k) (P : NumberFieldOrder l) (h : O.discr = P.discr) :
    NumberField.discr k = NumberField.discr l ∧ O.index = P.index := by
  obtain ⟨e⟩ := fields_ringEquiv_of_order_discr_eq hk hl O P h
  have hd := NumberField.discr_eq_discr_of_ringEquiv k e
  refine ⟨hd, ?_⟩
  rw [O.discr_eq_index_sq_mul, P.discr_eq_index_sq_mul, hd] at h
  have hs : (O.index : ℤ) ^ 2 = (P.index : ℤ) ^ 2 :=
    mul_right_cancel₀ (NumberField.discr_ne_zero l) h
  exact_mod_cast (sq_eq_sq₀ (Int.natCast_nonneg _) (Int.natCast_nonneg _)).mp hs

/-- Dividing the order discriminant by the field discriminant recovers the square
of the conductor index. -/
theorem index_sq_eq_discr_ediv {k : Type*} [Field k] [NumberField k]
    (O : NumberFieldOrder k) : (O.index : ℤ) ^ 2 = O.discr / NumberField.discr k := by
  rw [O.discr_eq_index_sq_mul, Int.mul_ediv_cancel _ (NumberField.discr_ne_zero k)]

set_option maxHeartbeats 400000 in
/-- In a quadratic field an order of additive index `f` in the maximal order is
exactly `ℤ + f · 𝓞 k`. The second basis coordinate maps the maximal order onto `ℤ`
with kernel the rational integers; the image of the order is the subgroup `fℤ`. -/
theorem mem_order_iff_intCast_add_index_smul {k : Type*} [Field k] [NumberField k]
    (hk : finrank ℚ k = 2) (O : NumberFieldOrder k) (x : 𝓞 k) :
    x ∈ O.toRingOfIntegers ↔ ∃ (a : ℤ) (y : 𝓞 k), x = (a : 𝓞 k) + O.index • y := by
  obtain ⟨b, hb⟩ := exists_basis_one (𝓞 k) ((RingOfIntegers.rank k).trans hk)
  let L := O.toRingOfIntegers.toSubmodule
  let π := b.coord 1
  have hπ₀ : π (b 0) = 0 := by simp [π, Basis.coord_apply]
  have hπ₁ : π (b 1) = 1 := by simp [π, Basis.coord_apply]
  have hπ : Function.Surjective π := fun n => ⟨n • b 1, by simp only [map_smul, hπ₁, smul_eq_mul, mul_one]⟩
  have hker : LinearMap.ker π ≤ L := by
    intro y hy
    have hy' : π y = 0 := hy
    have hy₀ : y = b.repr y 0 • b 0 := by
      simpa [Fin.sum_univ_two, show b.repr y 1 = 0 from hy'] using (b.sum_repr y).symm
    rw [hy₀, hb, zsmul_one]
    exact intCast_mem O.toRingOfIntegers.toSubring _
  let J : Ideal ℤ := Submodule.map π L
  have hcomap : Submodule.comap π (J : Submodule ℤ ℤ) = L := Submodule.comap_map_eq_self hker
  have hmem (y : 𝓞 k) : π y ∈ J ↔ y ∈ L := by
    change y ∈ Submodule.comap π (J : Submodule ℤ ℤ) ↔ y ∈ L
    rw [hcomap]
  have hadd : J.toAddSubgroup.comap π.toAddMonoidHom = L.toAddSubgroup := by
    ext y
    exact hmem y
  have hJ : J.toAddSubgroup = AddSubgroup.zmultiples (Submodule.IsPrincipal.generator J) := by
    calc
      J.toAddSubgroup = (Ideal.span {Submodule.IsPrincipal.generator J}).toAddSubgroup :=
        congrArg _ (Ideal.span_singleton_generator J).symm
      _ = _ := Ideal.span_singleton_toAddSubgroup_eq_zmultiples _
  have hf : O.index = (Submodule.IsPrincipal.generator J).natAbs := by
    calc
      O.index = L.toAddSubgroup.index := O.index_eq_addSubgroup_index
      _ = (J.toAddSubgroup.comap π.toAddMonoidHom).index :=
        congrArg AddSubgroup.index hadd.symm
      _ = J.toAddSubgroup.index :=
        J.toAddSubgroup.index_comap_of_surjective (f := π.toAddMonoidHom) hπ
      _ = (Submodule.IsPrincipal.generator J).natAbs := by rw [hJ, Int.index_zmultiples]
  have hJ' : J.toAddSubgroup = AddSubgroup.zmultiples (O.index : ℤ) := by
    rw [hf, Int.zmultiples_natAbs, hJ]
  change x ∈ L ↔ _
  rw [← hmem x]
  change π x ∈ J.toAddSubgroup ↔ _
  rw [hJ', Int.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨b.repr x 0, n • b 1, ?_⟩
    have hcoords : x = b.repr x 0 • b 0 + π x • b 1 := by
      simpa [Fin.sum_univ_two, π, Basis.coord_apply] using (b.sum_repr x).symm
    calc
      x = b.repr x 0 • b 0 + π x • b 1 := hcoords
      _ = _ := by rw [hb, zsmul_one, hn, mul_zsmul, natCast_zsmul]
  · rintro ⟨a, y, rfl⟩
    refine ⟨π y, ?_⟩
    have ha : π (a : 𝓞 k) = 0 := by
      rw [← zsmul_one a, ← hb, map_zsmul, hπ₀, smul_zero]
    calc
      π ((a : 𝓞 k) + O.index • y) = O.index • π y := by
        rw [map_add, map_nsmul, ha, zero_add]
      _ = _ := nsmul_eq_mul _ _

/-- The lattice description in the finite-index subring presentation used by the
manuscript's CM branch. -/
theorem mem_isImagQuadOrder_iff {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : IsImagQuadOrder k R) (x : 𝓞 k) :
    (x : k) ∈ R ↔ ∃ (a : ℤ) (y : 𝓞 k), x = (a : 𝓞 k) + LeafQM.AV.conductor R • y := by
  have h := mem_order_iff_intCast_add_index_smul hR.2.1 (toOrder R hR) x
  rw [toOrder_index_eq_conductor] at h
  exact h

/-- A field isomorphism carries the order of a given conductor index to the order
of the same index in the other quadratic field. -/
theorem map_order_of_index_eq {k l : Type*} [Field k] [NumberField k]
    [Field l] [NumberField l] (hk : finrank ℚ k = 2) (hl : finrank ℚ l = 2)
    (O : NumberFieldOrder k) (P : NumberFieldOrder l) (h : O.index = P.index)
    (e : k ≃+* l) :
    O.toRingOfIntegers.toSubring.map e.toIntAlgEquiv.mapIntegralClosure.toRingEquiv.toRingHom =
      P.toRingOfIntegers.toSubring := by
  let E : 𝓞 k ≃+* 𝓞 l := e.toIntAlgEquiv.mapIntegralClosure.toRingEquiv
  change O.toRingOfIntegers.toSubring.map E.toRingHom = P.toRingOfIntegers.toSubring
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, y, rfl⟩ := (mem_order_iff_intCast_add_index_smul hk O x).mp hx
    exact (mem_order_iff_intCast_add_index_smul hl P _).mpr
      ⟨a, E y, by simp [h]⟩
  · intro hz
    obtain ⟨a, y, rfl⟩ := (mem_order_iff_intCast_add_index_smul hl P z).mp hz
    refine ⟨(a : 𝓞 k) + O.index • E.symm y,
      (mem_order_iff_intCast_add_index_smul hk O _).mpr ⟨_, _, rfl⟩, ?_⟩
    simp [h]

end HDec.CMBranch.FowlerBridges

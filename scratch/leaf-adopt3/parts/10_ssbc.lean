section GlueSSBCSec
/-! ### Copied from `scratch/glue-ssbc/SSBC.lean` (compiled there; imports covered by Mathlib). Inserted by leaf-adopt3 following g0-split's recipe. -/
noncomputable section

namespace GlueSSBC

open Module Representation

section General

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- The trace form `(x, y) ↦ tr_W (x y)` on a subalgebra `B ⊆ End_F W` is nondegenerate. -/
def TraceNondeg (B : Subalgebra F (Module.End F W)) : Prop :=
  ∀ x ∈ B, (∀ y ∈ B, LinearMap.trace F W (x * y) = 0) → x = 0

/-- A finite-dimensional subalgebra of `End W` with nondegenerate trace form is a semisimple
ring. -/
theorem isSemisimpleRing_of_traceNondeg (B : Subalgebra F (Module.End F W))
    (h : TraceNondeg B) : IsSemisimpleRing B := by
  have : IsArtinianRing B := IsArtinianRing.of_finite F B
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [Ideal.jacobson_bot] at hn
  have hnil : ∀ y : B, IsNilpotent ((x : Module.End F W) * y) := by
    intro y
    have hxy : x * y ∈ Ring.jacobson B := Ideal.mul_mem_right _ _ hx
    refine ⟨n, ?_⟩
    have : (x * y) ^ n ∈ Ring.jacobson B ^ n := Ideal.pow_mem_pow hxy n
    rw [hn] at this
    have h0 : (x * y) ^ n = 0 := (Submodule.mem_bot _).mp this
    have := congrArg (fun z : B => (z : Module.End F W)) h0
    simpa using this
  have : (x : Module.End F W) = 0 := by
    apply h _ x.2
    intro y hy
    exact (LinearMap.isNilpotent_trace_of_isNilpotent (hnil ⟨y, hy⟩)).eq_zero
  exact (Submodule.mem_bot _).mpr (Subtype.ext this)

set_option backward.isDefEq.respectTransparency false in
/-- A faithful finite-dimensional semisimple module makes the subalgebra a semisimple ring. -/
theorem isSemisimpleRing_of_isSemisimpleModule (B : Subalgebra F (Module.End F W))
    [IsSemisimpleModule B W] : IsSemisimpleRing B := by
  let bas := Module.finBasis F W
  let n := Module.finrank F W
  let f : B →ₗ[B] (Fin n →₀ W) :=
    (Finsupp.linearEquivFunOnFinite B W (Fin n)).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun i => LinearMap.toSpanSingleton B W (bas i))
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro b hb
    rw [LinearMap.mem_ker] at hb
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply bas.ext
    intro i
    have := congrArg (fun φ : Fin n →₀ W => φ i) hb
    simpa [f, Subalgebra.smul_def, Module.End.smul_def] using this
  have : IsSemisimpleModule B (LinearMap.range f) := inferInstance
  refine IsSemisimpleModule.congr (R := B) (N := B) (M := ↥(LinearMap.range f)) ?_
  exact LinearEquiv.ofInjective f hf

/-- **Char 0:** a subalgebra of `End W` over which `W` is semisimple has nondegenerate trace
form. -/
theorem traceNondeg_of_isSemisimpleModule [CharZero F] (B : Subalgebra F (Module.End F W))
    [IsSemisimpleModule B W] : TraceNondeg B := by
  have := isSemisimpleRing_of_isSemisimpleModule B
  let I : Ideal B :=
    { carrier := {x | ∀ y : B, LinearMap.trace F W ((x : Module.End F W) * y) = 0}
      add_mem' := by
        intro a b ha hb y
        simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, add_mul, map_add] at *
        rw [ha y, hb y, add_zero]
      zero_mem' := by intro y; simp
      smul_mem' := by
        intro c x hx y
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul] at *
        rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc]
        have := hx (y * c)
        simpa using this }
  obtain ⟨e, he, hIe⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  have heI : e ∈ I := hIe ▸ Ideal.subset_span (Set.mem_singleton e)
  have he' : IsIdempotentElem (e : Module.End F W) := by
    have := congrArg (fun z : B => (z : Module.End F W)) he.eq
    simpa [IsIdempotentElem] using this
  have htr : LinearMap.trace F W (e : Module.End F W) = 0 := by
    have := heI e
    rwa [he'.eq] at this
  have he0 : e = 0 := Subtype.ext ((LinearMap.IsIdempotentElem.trace_eq_zero_iff he').mp htr)
  have hI : I = ⊥ := by rw [hIe, he0, Ideal.span_singleton_eq_bot]
  intro x hx hxy
  have : (⟨x, hx⟩ : B) ∈ I := fun y => hxy y y.2
  rw [hI] at this
  exact congrArg Subtype.val ((Submodule.mem_bot _).mp this)

end General

section Rep

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Base change `ρ_E` of a representation along a field extension `E/k` (verbatim from
glue-I3-linalg). -/
def repBaseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) :
    Representation E G (TensorProduct k E V) where
  toFun g := (ρ g).baseChange E
  map_one' := by
    change (ρ 1).baseChange E = LinearMap.id
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]
  map_mul' g h := by
    change (ρ (g * h)).baseChange E = (ρ g).baseChange E ∘ₗ (ρ h).baseChange E
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- `ρ` is semisimple iff `V` is a semisimple module over the span of `ρ(G)`. -/
theorem isSemisimpleRepresentation_iff_range (ρ : Representation k G V) :
    ρ.IsSemisimpleRepresentation ↔ IsSemisimpleModule (asAlgebraHom ρ).range V := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  let σ : MonoidAlgebra k G →+* (asAlgebraHom ρ).range := (asAlgebraHom ρ).rangeRestrict.toRingHom
  have : RingHomSurjective σ := ⟨AlgHom.rangeRestrict_surjective _⟩
  let l : ρ.asModule →ₛₗ[σ] V :=
    { toFun := ρ.asModuleEquiv
      map_add' := map_add _
      map_smul' := fun r x => asModuleEquiv_map_smul ρ r x }
  exact LinearMap.isSemisimpleModule_iff_of_bijective l ρ.asModuleEquiv.bijective

theorem mem_range_of (ρ : Representation k G V) (g : G) : ρ g ∈ (asAlgebraHom ρ).range :=
  ⟨MonoidAlgebra.of k G g, asAlgebraHom_of ρ g⟩

theorem asAlgebraHom_eq_sum (ρ : Representation k G V) (r : MonoidAlgebra k G) :
    asAlgebraHom ρ r = r.coeff.sum (fun g a => a • ρ g) := by
  rw [asAlgebraHom_def, MonoidAlgebra.lift_apply]

theorem baseChange_mem_range (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V)
    (y : Module.End k V) (hy : y ∈ (asAlgebraHom ρ).range) :
    y.baseChange E ∈ (asAlgebraHom (repBaseChange E ρ)).range := by
  obtain ⟨s, rfl⟩ := hy
  show (asAlgebraHom ρ s).baseChange E ∈ _
  induction s using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.baseChange_add]; exact Subalgebra.add_mem _ ha hb
  | single g a =>
    rw [asAlgebraHom_single, LinearMap.baseChange_smul, ← algebraMap_smul E a]
    exact Subalgebra.smul_mem _ (mem_range_of (repBaseChange E ρ) g) _

variable [FiniteDimensional k V]

/-- **Base change of the trace-form criterion.** -/
theorem traceNondeg_baseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V)
    (hA : TraceNondeg (asAlgebraHom ρ).range) :
    TraceNondeg (asAlgebraHom (repBaseChange E ρ)).range := by
  intro x hx hxy
  obtain ⟨r, rfl⟩ := hx
  change (∀ y ∈ _, LinearMap.trace E _ (asAlgebraHom (repBaseChange E ρ) r * y) = 0) at hxy
  show asAlgebraHom (repBaseChange E ρ) r = 0
  rw [asAlgebraHom_eq_sum] at hxy ⊢
  set c := r.coeff
  have hρE : ∀ g, repBaseChange E ρ g = (ρ g).baseChange E := fun g => rfl
  -- every `k`-linear functional of the coefficients gives an element of the radical over `k`
  have key : ∀ f : Module.Dual k E, c.sum (fun g a => f a • ρ g) = 0 := by
    intro f
    apply hA _ (Subalgebra.sum_mem _ fun g _ => Subalgebra.smul_mem _ (mem_range_of ρ g) _)
    intro y hy
    have h0 := congrArg f (hxy _ (baseChange_mem_range E ρ y hy))
    simp only [Finsupp.sum, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hρE,
      ← LinearMap.baseChange_mul, LinearMap.trace_baseChange, smul_eq_mul, map_zero] at h0 ⊢
    rw [← h0]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm (c g), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  let b := Module.finBasis k V
  have hv : ∀ v : V, (c.sum (fun g a => a • repBaseChange E ρ g)) (1 ⊗ₜ v) = 0 := by
    intro v
    apply (Algebra.TensorProduct.basis E b).repr.injective
    ext j
    rw [map_zero, Finsupp.zero_apply]
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro f
    have hk := congrArg (fun φ : Module.End k V => b.repr (φ v) j) (key f)
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hρE,
      LinearMap.baseChange_tmul, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply,
      smul_eq_mul, LinearMap.zero_apply, map_zero, Finsupp.zero_apply] at hk ⊢
    rw [← hk]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm (c g), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  apply (Algebra.TensorProduct.basis E b).ext
  intro i
  rw [Algebra.TensorProduct.basis_apply, hv, LinearMap.zero_apply]

/-- **`SemisimpleBaseChange`, proved.** In characteristic `0`, a semisimple finite-dimensional
representation stays semisimple after any extension of the coefficient field. -/
theorem isSemisimpleRepresentation_baseChange [CharZero k] (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) (hρ : ρ.IsSemisimpleRepresentation) :
    (repBaseChange E ρ).IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_range] at hρ ⊢
  have hA := traceNondeg_of_isSemisimpleModule (asAlgebraHom ρ).range
  have := isSemisimpleRing_of_traceNondeg _ (traceNondeg_baseChange E ρ hA)
  infer_instance

end Rep

/-- glue-I3-linalg's Prop, verbatim (with `repBaseChange` from this file). -/
def SemisimpleBaseChange : Prop :=
  ∀ (k E G V : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V),
    ρ.IsSemisimpleRepresentation → (repBaseChange E ρ).IsSemisimpleRepresentation

theorem semisimpleBaseChange : SemisimpleBaseChange :=
  fun _ E _ _ _ _ _ _ _ _ _ _ ρ hρ => isSemisimpleRepresentation_baseChange E ρ hρ

end GlueSSBC
end
end GlueSSBCSec


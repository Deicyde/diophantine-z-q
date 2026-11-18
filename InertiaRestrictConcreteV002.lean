import IntegralClosureActionV004
import InertiaRestrictionProfiniteV002
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.MulAction

/-!
# Inertia of a finite Galois subextension is the restriction of inertia of `w`

Let `O` be a discrete valuation subring of a field `K` of characteristic zero, `Ω` an algebraic
closure of `K`, `w` a valuation subring of `Ω` above `O`, and `N/K` a finite Galois subextension.
Let `q` be the center of `w` on the integral closure `S` of `O` in `Ω` and `p = q ∩ R` its trace on
the integral closure `R` of `O` in `N`.

* `map_inertia_restrict`: restriction maps the inertia group of `q` in `Aut_K(Ω)` onto the inertia
  group of `p` in `Gal(N/K)`. The kernel `Gal(Ω/N)` is profinite (Krull topology), acts continuously
  on the discrete ring `S` (stabilizers contain open fixing subgroups), and its invariants in `S` are
  exactly `R` (infinite Galois correspondence).
* `inertia_fixes_of_fixedField`: if an intermediate field `M ⊆ N` is fixed by the inertia subgroup of
  `w`, it is fixed by the inertia group of `p` in `Gal(N/K)`; so `M` lies in the inertia field of `p`.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open scoped Pointwise

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem integralOver_val (O : ValuationSubring K) (N : IntermediateField K Ω) {x : N}
    (hx : IntegralOver (Ω := N) O x) : IntegralOver O (x : Ω) := by
  let _ : Algebra O N := ((algebraMap K N).comp (algebraMap O K)).toAlgebra
  let _ : Algebra O Ω := ((algebraMap K Ω).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower O K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h : IsIntegral O x := hx
  exact h.map (N.val.restrictScalars O)

theorem integralOver_of_val (O : ValuationSubring K) (N : IntermediateField K Ω) {x : N}
    (hx : IntegralOver O (x : Ω)) : IntegralOver (Ω := N) O x := by
  let _ : Algebra O N := ((algebraMap K N).comp (algebraMap O K)).toAlgebra
  let _ : Algebra O Ω := ((algebraMap K Ω).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower O K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h : IsIntegral O (x : Ω) := hx
  exact (isIntegral_algHom_iff (N.val.restrictScalars O) N.val.injective).mp h

/-- The inclusion of integral closures `R → S`. -/
def inclIntClosure (O : ValuationSubring K) (N : IntermediateField K Ω) :
    intClosure (Ω := N) O →+* intClosure (Ω := Ω) O where
  toFun x := ⟨((x : N) : Ω), integralOver_val O N x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The trace of the center of `w` on the integral closure of `O` in `N`. -/
def centerIdealN (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (N : IntermediateField K Ω) :
    Ideal (intClosure (Ω := N) O) :=
  (centerIdeal O w hw).comap (inclIntClosure O N)

/-- **Restriction maps inertia onto inertia.** -/
theorem map_inertia_restrict [CharZero K] [IsAlgClosure K Ω] (O : ValuationSubring K)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (N : IntermediateField K Ω) [FiniteDimensional K N] [Normal K N] :
    ((centerIdeal O w hw).inertia (Ω ≃ₐ[K] Ω)).map (AlgEquiv.restrictNormalHom N) =
      (centerIdealN O w hw N).inertia (N ≃ₐ[K] N) := by
  have hGal : IsGalois K Ω :=
    { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField
      to_normal := IsAlgClosure.normal K Ω }
  let _ : Algebra (intClosure (Ω := N) O) (intClosure (Ω := Ω) O) :=
    (inclIntClosure O N).toAlgebra
  let _ : TopologicalSpace (intClosure (Ω := Ω) O) := ⊥
  have : DiscreteTopology (intClosure (Ω := Ω) O) := ⟨rfl⟩
  have hcont : ContinuousSMul (Ω ≃ₐ[K] Ω) (intClosure (Ω := Ω) O) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro s
    let E : IntermediateField K Ω := IntermediateField.adjoin K {(s : Ω)}
    have : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (s : Ω))
    refine Subgroup.isOpen_mono (H₁ := E.fixingSubgroup) ?_ E.fixingSubgroup_isOpen
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    exact (IntermediateField.mem_fixingSubgroup_iff E σ).1 hσ (s : Ω)
      (IntermediateField.mem_adjoin_simple_self K (s : Ω))
  have hcomp : CompactSpace N.fixingSubgroup :=
    isCompact_iff_compactSpace.mp N.fixingSubgroup_isClosed.isCompact
  have hinv : Algebra.IsInvariant (intClosure (Ω := N) O) (intClosure (Ω := Ω) O)
      N.fixingSubgroup := by
    constructor
    intro s hs
    have hsN : (s : Ω) ∈ N := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup N, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have := hs ⟨σ, hσ⟩
      exact congrArg Subtype.val this
    refine ⟨⟨⟨(s : Ω), hsN⟩, integralOver_of_val O N (x := ⟨(s : Ω), hsN⟩) s.2⟩, ?_⟩
    rfl
  have hlies : (centerIdeal O w hw).LiesOver (centerIdealN O w hw N) := ⟨rfl⟩
  refine map_inertia_of_surjective_of_profinite (AlgEquiv.restrictNormalHom N) N.fixingSubgroup
    (centerIdealN O w hw N) (centerIdeal O w hw)
    (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := N) (E := Ω)) ?_ ?_
  · intro σ hσ
    rw [MonoidHom.mem_ker]
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff N σ).1 hσ x x.2
  · intro g x
    apply Subtype.ext
    change (((AlgEquiv.restrictNormalHom N g) (x : N) : N) : Ω) = g ((x : N) : Ω)
    rw [AlgEquiv.restrictNormalHom_apply]

/-- **Fields fixed by the inertia of `w` lie in the inertia field of `p`.** -/
theorem inertia_fixes_of_fixedField [CharZero K] [IsAlgClosure K Ω] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (N : IntermediateField K Ω) [FiniteDimensional K N] [Normal K N]
    {m : Ω} (hmN : m ∈ N)
    (hm : ∀ σ : Ω ≃ₐ[K] Ω, (∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) → σ m = m)
    (τ : N ≃ₐ[K] N) (hτ : τ ∈ (centerIdealN O w hw N).inertia (N ≃ₐ[K] N)) :
    τ ⟨m, hmN⟩ = ⟨m, hmN⟩ := by
  rw [← map_inertia_restrict O w hw N] at hτ
  obtain ⟨σ, hσ, rfl⟩ := hτ
  apply Subtype.ext
  rw [AlgEquiv.restrictNormalHom_apply]
  exact hm σ (mem_inertia_of_mem_inertia_centerIdeal O w hw σ hσ)

end InertiaPointDescent

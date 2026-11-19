import ZInQKernel.Contrib.OneProof.RC.Intertwine.Comparison
import ZInQKernel.Contrib.OneProof.RC.Intertwine.Normalization
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-! The restricted product measure in rectangular coordinates. Its
determinant multiplier is the finite product from tex 8647 and 9004–9007. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine

open OldStageLaw MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open scoped BigOperators RestrictedProduct

instance : Fact (∀ p : Place, IsOpen (PadicInt.subring p.val : Set ℚ_[p.val])) := ⟨by
  intro p
  change IsOpen {y : ℚ_[p.val] | ‖y‖ ≤ 1}
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p.val]) one_ne_zero⟩

instance : MeasurableSpace (Fin 3 → RationalFiniteAdeles) := borel _
instance : BorelSpace (Fin 3 → RationalFiniteAdeles) := ⟨rfl⟩

instance : MeasurableAdd (Fin 3 → RationalFiniteAdeles) where
  measurable_const_add _ := (continuous_const.add continuous_id).measurable
  measurable_add_const _ := (continuous_id.add continuous_const).measurable

theorem integralAdeles_open : IsOpen (integralAdeles : Set RationalFiniteAdeles) := by
  exact RestrictedProduct.isOpen_forall_mem (fun p : Place =>
    Fact.out (p := ∀ p : Place, IsOpen (PadicInt.subring p.val : Set ℚ_[p.val])) p)

theorem integralAdeles_compact : IsCompact (integralAdeles : Set RationalFiniteAdeles) := by
  rw [show (integralAdeles : Set RationalFiniteAdeles) =
      range (RestrictedProduct.structureMap (fun p : Place => ℚ_[p.val])
        (fun p => (PadicInt.subring p.val : Set ℚ_[p.val])) cofinite) by
    rw [RestrictedProduct.range_structureMap]
    rfl]
  letI (p : Place) : CompactSpace ↥(PadicInt.subring p.val : Set ℚ_[p.val]) :=
    isCompact_iff_compactSpace.mp (by
      change IsCompact {y : ℚ_[p.val] | ‖y‖ ≤ 1}
      simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
        isCompact_closedBall (0 : ℚ_[p.val]) 1)
  exact isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

private theorem rectangular_eq_pi :
    (lattice integralAdeles : Set (Fin 3 → RationalFiniteAdeles)) =
      Set.univ.pi (fun _ => (integralAdeles : Set RationalFiniteAdeles)) := by
  ext x
  change (∀ i, x i ∈ integralAdeles) ↔ _
  simp [Set.mem_pi]

theorem rectangular_open : IsOpen (lattice integralAdeles : Set (Fin 3 → RationalFiniteAdeles)) := by
  rw [rectangular_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => integralAdeles_open

theorem rectangular_compact :
    IsCompact (lattice integralAdeles : Set (Fin 3 → RationalFiniteAdeles)) := by
  rw [rectangular_eq_pi]
  exact isCompact_univ_pi fun _ => integralAdeles_compact

def rectangularCompacts : PositiveCompacts (Fin 3 → RationalFiniteAdeles) :=
  ⟨⟨lattice integralAdeles, rectangular_compact⟩,
    by rw [rectangular_open.interior_eq]; exact ⟨0, (lattice integralAdeles).zero_mem⟩⟩

def coordinateHaar : Measure (Fin 3 → RationalFiniteAdeles) :=
  addHaarMeasure rectangularCompacts

def normalizedHaar (a : Fin 3 → ℕ) : Measure (Fin 3 → RationalFiniteAdeles) :=
  ENNReal.ofReal (finiteVolume a) • coordinateHaar

instance (a : Fin 3 → ℕ) : (normalizedHaar a).IsAddLeftInvariant := by
  unfold normalizedHaar coordinateHaar
  infer_instance

instance (a : Fin 3 → ℕ) : IsFiniteMeasureOnCompacts (normalizedHaar a) := by
  unfold normalizedHaar coordinateHaar
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top

theorem normalizedHaar_volume {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)] :
    ((normalizedHaar a).real (lattice integralAdeles) : ℂ) =
      ∏ i, 1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ) := by
  have h : 0 ≤ finiteVolume a := Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  rw [normalizedHaar, measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal h,
    show coordinateHaar.real (lattice integralAdeles) = 1 by
      change (addHaarMeasure rectangularCompacts (rectangularCompacts : Set _)).toReal = 1
      rw [addHaarMeasure_self, ENNReal.toReal_one],
    mul_one]
  exact finiteVolume_eq

theorem continuous_finitePhase : Continuous (finitePhase rationalFiniteModel) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  apply ContinuousAt.congr (f := fun _ => finitePhase rationalFiniteModel x) continuousAt_const
  filter_upwards [(integralAdeles_open.preimage (continuous_id.sub continuous_const)).mem_nhds
    (show x - x ∈ integralAdeles by simp)] with y hy
  have hmem : y - x ∈ integralAdeles := hy
  have hr := finitePhase_add rationalFiniteModel (y - x) x
  rw [sub_add_cancel, (finitePhase_eq_one rationalFiniteModel _).2 hmem, one_mul] at hr
  exact hr.symm

theorem integrable_latticeCharacter {a : Fin 3 → ℕ} (y : Fin 3 → RationalFiniteAdeles) :
    Integrable (latticeCharacter (a := a) rationalFiniteModel y) (normalizedHaar a) := by
  have hp : Continuous fun x : Fin 3 → RationalFiniteAdeles => polar a x y := by
    unfold polar
    fun_prop
  exact ((continuous_finitePhase.comp hp).continuousOn.integrableOn_compact
    rectangular_compact).integrable_indicator rectangular_open.measurableSet

/-- The polar dual condition is the coordinatewise local annihilator at
every rational prime, with no exclusion at two. -/
theorem adelic_annihilator_placewise (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)]
    (y : Fin 3 → RationalFiniteAdeles) :
    (∀ x ∈ lattice integralAdeles, finitePhase rationalFiniteModel (polar a x y) = 1) ↔
      ∀ (p : Place) (i : Fin 3), ((2 * a i : ℕ) : ℚ_[p.val]) * (y i) p ∈ PadicInt.subring p.val := by
  rw [annihilator_iff]
  have he (p : Place) (i : Fin 3) :
      (((2 * a i : ℕ) : RationalFiniteAdeles) * y i) p =
        ((2 * a i : ℕ) : ℚ_[p.val]) * (y i) p := by
    let ev : RationalFiniteAdeles →+* ℚ_[p.val] :=
      RestrictedProduct.evalRingHom (fun t : Place => ℚ_[t.val]) p
    change ev ((((2 * a i : ℕ) : RationalFiniteAdeles) * y i)) = _
    rw [map_mul, map_natCast]
    rfl
  change (∀ (i : Fin 3) (p : Place), _ ∈ PadicInt.subring p.val) ↔ _
  simpa only [he] using
    (forall_comm (p := fun (i : Fin 3) (p : Place) =>
      ((2 * a i : ℕ) : ℚ_[p.val]) * (y i) p ∈ PadicInt.subring p.val))

/-- Rectangular Fourier calculation on the rational finite adèles themselves,
with the finite determinant normalization. -/
theorem adelic_fourier {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)] (w : Grid a → ℂ) :
    J rationalFiniteModel (finiteFourier w) =
      haarFourier (a := a) rationalFiniteModel (normalizedHaar a) (J rationalFiniteModel w) :=
  J_fourier _ _ rectangular_open.measurableSet integrable_latticeCharacter normalizedHaar_volume w

/-- The upper inverse generator is the product of the local phases at any
finite set covering the nonintegral phase arguments. -/
theorem adelic_phase {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]
    (n : ℤ) (w : Grid a → ℂ) (x : Fin 3 → RationalFiniteAdeles) (S : Finset Place)
    (hS : ∀ p, p ∉ S →
      ((-(n : RationalFiniteAdeles)) * quad a x) p ∈ PadicInt.subring p.val) :
    J rationalFiniteModel (twist n w) x =
      (∏ p ∈ S, rationalPhase (localFraction p (((-(n : RationalFiniteAdeles)) * quad a x) p))) *
        J rationalFiniteModel w x := by
  rw [J_twist]
  change finitePhase rationalFiniteModel (-(n : RationalFiniteAdeles) * quad a x) *
    J rationalFiniteModel w x = _
  rw [finitePhase_local_product _ S hS]

/-- A common normalized lift gives both identities on this concrete space.
Use the same real index and lifts for `a` and `referenceForm`. -/
theorem adelic_comparison {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (E : (Grid a → ℂ) →ₗ[ℂ] V)
    (eval : V →ₗ[ℂ] ((Fin 3 → RationalFiniteAdeles) → ℂ))
    (heval : Function.Injective eval) (hE : ∀ w, eval (E w) = J rationalFiniteModel w)
    (R : G →* Module.End ℂ V) (lift : Step → G) (realIndex finiteIndex : ℂˣ)
    (hindex : realIndex * finiteIndex = 1)
    (hT : ∀ n v x, eval (R (lift (.trans n)) v) x =
      finitePhase rationalFiniteModel (-(n : RationalFiniteAdeles) * quad a x) * eval v x)
    (hW : ∀ v, eval (R (lift .inv) v) =
      (finiteIndex : ℂ) • haarFourier (a := a) rationalFiniteModel (normalizedHaar a) (eval v)) :
    Function.Injective E ∧
      RelativeAction.IntertwinesGenerators E R lift (generatorScalar realIndex) := by
  have hγ : finiteIndex = realIndex⁻¹ := eq_inv_of_mul_eq_one_right hindex
  apply comparison rationalFiniteModel E eval heval hE (normalizedHaar a)
    rectangular_open.measurableSet integrable_latticeCharacter normalizedHaar_volume R lift
    realIndex hT
  simpa only [hγ] using hW

/-- The weighted and ordinary rectangular spaces use one lift and one
generator scalar. The separately supplied index products use the same real index. -/
theorem adelic_pair_comparison {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]
    {G V V₀ : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V₀] [Module ℂ V₀]
    (E : (Grid a → ℂ) →ₗ[ℂ] V) (E₀ : (Grid referenceForm → ℂ) →ₗ[ℂ] V₀)
    (eval : V →ₗ[ℂ] ((Fin 3 → RationalFiniteAdeles) → ℂ))
    (eval₀ : V₀ →ₗ[ℂ] ((Fin 3 → RationalFiniteAdeles) → ℂ))
    (heval : Function.Injective eval) (heval₀ : Function.Injective eval₀)
    (hE : ∀ w, eval (E w) = J rationalFiniteModel w)
    (hE₀ : ∀ w, eval₀ (E₀ w) = J rationalFiniteModel w)
    (R : G →* Module.End ℂ V) (R₀ : G →* Module.End ℂ V₀)
    (lift : Step → G) (realIndex finiteIndex finiteIndex₀ : ℂˣ)
    (hindex : realIndex * finiteIndex = 1) (hindex₀ : realIndex * finiteIndex₀ = 1)
    (hT : ∀ n v x, eval (R (lift (.trans n)) v) x =
      finitePhase rationalFiniteModel (-(n : RationalFiniteAdeles) * quad a x) * eval v x)
    (hT₀ : ∀ n v x, eval₀ (R₀ (lift (.trans n)) v) x =
      finitePhase rationalFiniteModel (-(n : RationalFiniteAdeles) * quad referenceForm x) * eval₀ v x)
    (hW : ∀ v, eval (R (lift .inv) v) =
      (finiteIndex : ℂ) • haarFourier (a := a) rationalFiniteModel (normalizedHaar a) (eval v))
    (hW₀ : ∀ v, eval₀ (R₀ (lift .inv) v) = (finiteIndex₀ : ℂ) •
      haarFourier (a := referenceForm) rationalFiniteModel (normalizedHaar referenceForm) (eval₀ v)) :
    (Function.Injective E ∧
      RelativeAction.IntertwinesGenerators E R lift (generatorScalar realIndex)) ∧
    (Function.Injective E₀ ∧
      RelativeAction.IntertwinesGenerators E₀ R₀ lift (generatorScalar realIndex)) :=
  ⟨adelic_comparison E eval heval hE R lift realIndex finiteIndex hindex hT hW,
    adelic_comparison E₀ eval₀ heval₀ hE₀ R₀ lift realIndex finiteIndex₀ hindex₀ hT₀ hW₀⟩

#print axioms integralAdeles_open
#print axioms integralAdeles_compact
#print axioms rectangular_eq_pi
#print axioms rectangular_open
#print axioms rectangular_compact
#print axioms normalizedHaar_volume
#print axioms continuous_finitePhase
#print axioms integrable_latticeCharacter
#print axioms adelic_annihilator_placewise
#print axioms adelic_fourier
#print axioms adelic_phase
#print axioms adelic_comparison
#print axioms adelic_pair_comparison

end ZInQ.Manuscript.RC.Intertwine

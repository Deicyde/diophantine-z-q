import ZInQKernel.Contrib.OneProof.JavanpeykarFix
import ZInQKernel.Contrib.OneProof.PrintedStableHeight

noncomputable section

set_option linter.style.haveILetI false

open scoped TensorProduct

namespace JavanpeykarRebase

/-- **Leaf: a finite constant field extension of an algebraic function field is unramified** -/
def ConstantFieldExtensionUnramifiedFinite : Prop :=
  ∀ (K F L FL : Type) [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL] [CharZero K] [FiniteDimensional K L]
    (ι : F →ₐ[K] FL),
    (∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K {t}) F) →
    (∀ a : F, IsAlgebraic K a → a ∈ Set.range (algebraMap K F)) →
    Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)) →
    ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ∀ π : F,
      π ∈ (w.comap (ι : F →+* FL)).nonunits →
      (∀ x ∈ (w.comap (ι : F →+* FL)).nonunits, ∃ y ∈ w.comap (ι : F →+* FL), x = π * y) →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = ι π * y

theorem mem_nonunits_comap {E E' : Type} [Field E] [Field E'] (A : ValuationSubring E')
    (f : E →+* E') (x : E) : x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero]

section Tensor

variable {K F L : Type} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]

theorem range_lTensor_mono {L1 L2 : IntermediateField K L} (h : L1 ≤ L2) :
    LinearMap.range (L1.val.toLinearMap.lTensor F) ≤
      LinearMap.range (L2.val.toLinearMap.lTensor F) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(IntermediateField.inclusion h).toLinearMap.lTensor F x, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  rfl

/-- Every element of `F ⊗_K L` (`L/K` algebraic) comes from `F ⊗_K L'` for a finite subextension
`L'`. -/
theorem exists_fd_of_tensor [Algebra.IsAlgebraic K L] (z : F ⊗[K] L) :
    ∃ L' : IntermediateField K L, FiniteDimensional K L' ∧
      z ∈ LinearMap.range (L'.val.toLinearMap.lTensor F) := by
  induction z using TensorProduct.inductionOn with
  | tmul f l =>
    refine ⟨IntermediateField.adjoin K {l},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral l), ?_⟩
    exact ⟨f ⊗ₜ ⟨l, IntermediateField.mem_adjoin_simple_self K l⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨L1, h1, hx⟩ := hx
    obtain ⟨L2, h2, hy⟩ := hy
    exact ⟨L1 ⊔ L2, inferInstance, Submodule.add_mem _ (range_lTensor_mono le_sup_left hx)
      (range_lTensor_mono le_sup_right hy)⟩

end Tensor

/-- **The algebraic case of the leaf from the finite case (glue, proved).** -/
theorem full_of_finite (h : ConstantFieldExtensionUnramifiedFinite) :
    JavanpeykarFix.ConstantFieldExtensionUnramifiedFull := by
  intro K F L FL _ _ _ _ _ _ _ _ _ _ _ ι ht hfull hbij w hw π hπ hgen x hx
  obtain ⟨z, rfl⟩ := hbij.2 x
  obtain ⟨L', hL', z', rfl⟩ := exists_fd_of_tensor (F := F) z
  let j' : L' →ₐ[K] FL := (IsScalarTower.toAlgHom K L FL).comp L'.val
  have hfac : ∀ u : F ⊗[K] L',
      Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)
        (L'.val.toLinearMap.lTensor F u) = Algebra.TensorProduct.productMap ι j' u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a b => simp [j']
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  have hinj : Function.Injective (Algebra.TensorProduct.productMap ι j') := by
    intro u v huv
    rw [← hfac, ← hfac] at huv
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := F) L'.val.toLinearMap
      Subtype.val_injective (hbij.1 huv)
  haveI : FiniteDimensional K j'.fieldRange :=
    (AlgHom.equivFieldRange j').toLinearEquiv.finiteDimensional
  let E : IntermediateField K FL := ι.fieldRange ⊔ j'.fieldRange
  have hE : E.toSubalgebra = (Algebra.TensorProduct.productMap ι j').range := by
    rw [Algebra.TensorProduct.productMap_range, IntermediateField.sup_toSubalgebra_of_right,
      AlgHom.fieldRange_toSubalgebra, AlgHom.fieldRange_toSubalgebra]
  let ι' : F →ₐ[K] E := ι.codRestrict E.toSubalgebra fun a =>
    (le_sup_left : ι.fieldRange ≤ E) ⟨a, rfl⟩
  let j'' : L' →ₐ[K] E := j'.codRestrict E.toSubalgebra fun a =>
    (le_sup_right : j'.fieldRange ≤ E) ⟨a, rfl⟩
  letI : Algebra L' E := j''.toRingHom.toAlgebra
  haveI : IsScalarTower K L' E := IsScalarTower.of_algebraMap_eq fun a => (j''.commutes a).symm
  have hval : ∀ u : F ⊗[K] L',
      (E.val (Algebra.TensorProduct.productMap ι' (IsScalarTower.toAlgHom K L' E) u) : FL) =
        Algebra.TensorProduct.productMap ι j' u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a b => simp; rfl
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  have hbij' : Function.Bijective
      (Algebra.TensorProduct.productMap ι' (IsScalarTower.toAlgHom K L' E)) := by
    refine ⟨fun u v huv => hinj ?_, fun e => ?_⟩
    · rw [← hval, ← hval, huv]
    · have he : (e : FL) ∈ E.toSubalgebra := e.2
      rw [hE] at he
      obtain ⟨u, hu⟩ := he
      exact ⟨u, Subtype.ext ((hval u).trans hu)⟩
  let w' : ValuationSubring E := w.comap (E.val : E →+* FL)
  have hcomp : w'.comap (ι' : F →+* E) = w.comap (ι : F →+* FL) := by
    ext a
    simp only [w', ValuationSubring.mem_comap]
    rfl
  have hw' : ∀ c : L', algebraMap L' E c ∈ w' := fun c => ValuationSubring.mem_comap.mpr (hw c)
  have key := h K F L' E ι' ht hfull hbij' w' hw' π (hcomp ▸ hπ) (hcomp ▸ hgen)
  set x' : E := Algebra.TensorProduct.productMap ι' (IsScalarTower.toAlgHom K L' E) z'
  have hxx : (E.val x' : FL) = Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)
      (L'.val.toLinearMap.lTensor F z') := (hval z').trans (hfac z').symm
  have hx' : x' ∈ w'.nonunits := by
    have h1 : (E.val x' : FL) ∈ w.nonunits := by rw [hxx]; exact hx
    exact (mem_nonunits_comap _ _ _).mpr h1
  obtain ⟨y', hy', hxy⟩ := key x' hx'
  refine ⟨E.val y', hy', ?_⟩
  rw [← hxx, hxy, map_mul]
  rfl

end JavanpeykarRebase

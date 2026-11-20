import Mathlib

/-!
# Artin–Tate for the finite-flat quotient's affine charts

The intermediate algebra is proved finite type, not assumed. The proof chooses
coefficients for multiplication of a finite module-generating family by the
finite algebra generators, puts these coefficients in a finite-type subalgebra,
and applies Noetherianity to the intermediate submodule.
-/

noncomputable section
open Algebra Submodule

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- Artin–Tate: a faithful finite intermediate algebra of a finite-type algebra is finite type. -/
theorem finiteType_of_finite_intermediate (k R S : Type*) [CommRing k] [IsNoetherianRing k]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] [Algebra.FiniteType k S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) : Algebra.FiniteType k R := by
  classical
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := S)
  let w : Fin (n + 1) → S := Fin.cases 1 v
  have hw : span R (Set.range w) = ⊤ := by
    apply top_unique
    rw [← hv]
    apply span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, by simp [w]⟩
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k S).FG)
  have hcoeff (a : t) (i : Fin (n + 1)) : ∃ c : Fin (n + 1) → R,
      ∑ j, c j • w j = a.1 * w i := by
    apply (Submodule.mem_span_range_iff_exists_fun R).mp
    rw [hw]
    trivial
  choose c hc using hcoeff
  let coeff : t × Fin (n + 1) × Fin (n + 1) → R := fun p => c p.1 p.2.1 p.2.2
  let R₀ := Algebra.adjoin k (Set.range coeff)
  haveI : Algebra.FiniteType k R₀ := Algebra.FiniteType.adjoin_of_finite (Set.finite_range coeff)
  haveI : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing k R₀
  let V : Submodule R₀ S := span R₀ (Set.range w)
  have hgen (a : t) (i : Fin (n + 1)) : a.1 * w i ∈ V := by
    rw [← hc a i]
    have he : (∑ j, c a i j • w j) =
        ∑ j, (⟨c a i j, Algebra.subset_adjoin ⟨(a, i, j), rfl⟩⟩ : R₀) • w j := rfl
    rw [he]
    exact V.sum_mem fun j _ => V.smul_mem _ (subset_span ⟨j, rfl⟩)
  have hmul (a : t) : ∀ x ∈ V, a.1 * x ∈ V := by
    intro x hx
    induction hx using span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hgen a i
    | zero => simpa using V.zero_mem
    | add x y hx hy hx' hy' => simpa only [mul_add] using V.add_mem hx' hy'
    | smul r x hx hx' => simpa only [mul_smul_comm] using V.smul_mem r hx'
  let P : Subalgebra k S :=
    { carrier := {a | ∀ x ∈ V, a * x ∈ V}
      zero_mem' := by intro x hx; simpa using V.zero_mem
      one_mem' := by intro x hx; simpa using hx
      add_mem' := by intro a b ha hb x hx; simpa only [add_mul] using V.add_mem (ha x hx) (hb x hx)
      mul_mem' := by intro a b ha hb x hx; rw [mul_assoc]; exact ha _ (hb x hx)
      algebraMap_mem' := by
        intro r x hx
        have h := V.smul_mem (algebraMap k R₀ r) hx
        simpa only [Algebra.smul_def, ← IsScalarTower.algebraMap_apply] using h }
  have hP : P = ⊤ := by
    apply top_unique
    rw [← ht]
    exact Algebra.adjoin_le fun a ha => hmul ⟨a, ha⟩
  have h1 : (1 : S) ∈ V := by
    exact subset_span ⟨0, by simp [w]⟩
  have hV : V = ⊤ := by
    apply top_unique
    intro a _
    have ha : a ∈ P := by rw [hP]; trivial
    simpa only [mul_one] using ha 1 h1
  haveI : Module.Finite R₀ S := Module.Finite.of_fg_top (by
    rw [← hV]
    exact Submodule.fg_def.mpr ⟨Set.range w, Set.finite_range w, rfl⟩)
  haveI : IsNoetherian R₀ S := inferInstance
  haveI : Module.Finite R₀ R :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom R₀ R S).toLinearMap hinj
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R₀)
    (inferInstance : Algebra.FiniteType R₀ R)

end ZInQ.Contrib.CloudR2Poincare.L4

import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Sheaves of modules over the spectrum of a field are quasi-coherent and free

This removes an unnecessary general quasi-coherence dependency from the port of
Stacks 047I. A sheaf map on a one-point space is an isomorphism when its map on
all global sections is an isomorphism, because the singleton family consisting
of the top open is a basis. Mathlib's tilde-Gamma counit is an isomorphism on global
sections, hence every module on `Spec k` is quasi-coherent. A vector-space basis
then gives a free sheaf, exactly as in AxiomMath/Stacks c496df0d,
`GroupScheme/Differentials.lean:218–228` (Apache-2.0; credit retained here).

Prominent change notice, 2026-11-14: the rational-field special case is proved
from Mathlib rather than importing general quasi-coherence of relative differentials.
No desired smoothness, reducedness or abelian-variety fact is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

/-- On a one-point (or empty) space, a sheaf morphism is determined by its top component. -/
theorem isIso_sheaf_of_isIso_top_of_subsingleton (R : Type u) [Ring R]
    (X : TopCat.{u}) [Subsingleton X]
    {M N : TopCat.Sheaf (ModuleCat.{u} R) X} (f : M ⟶ N)
    (hf : IsIso (f.hom.app (Opposite.op ⊤))) : IsIso f := by
  have hB : TopologicalSpace.Opens.IsBasis
      (Set.range fun _ : Unit => (⊤ : TopologicalSpace.Opens X)) := by
    have h : TopologicalSpace.IsTopologicalBasis ({Set.univ} : Set (Set X)) := by
      refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
      · rintro U (rfl : U = Set.univ)
        exact isOpen_univ
      · intro x U hx _
        refine ⟨Set.univ, by simp, Set.mem_univ x, ?_⟩
        intro y _
        simpa only [Subsingleton.elim y x] using hx
    change TopologicalSpace.IsTopologicalBasis
      (SetLike.coe '' Set.range fun _ : Unit => (⊤ : TopologicalSpace.Opens X))
    convert h using 1
    ext U
    constructor
    · rintro ⟨V, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_singleton _
    · intro hU
      have hU' : U = Set.univ := Set.mem_singleton_iff.mp hU
      subst U
      exact ⟨⊤, ⟨Unit.unit, rfl⟩, rfl⟩
  exact TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun _ : Unit => (⊤ : TopologicalSpace.Opens X)) (φ := f) hB (fun _ => hf)

/-- The tilde-Gamma counit for any module on `Spec k` is an isomorphism. -/
theorem isIso_fromTildeΓ_specField {k : Type u} [Field k]
    (N : (Spec (CommRingCat.of k)).Modules) : IsIso N.fromTildeΓ := by
  letI : (modulesSpecToSheaf (R := CommRingCat.of k)).Full :=
    SpecModulesToSheafFullyFaithful.full
  letI : (modulesSpecToSheaf (R := CommRingCat.of k)).Faithful :=
    SpecModulesToSheafFullyFaithful.faithful
  have htop : IsIso ((modulesSpecToSheaf.map N.fromTildeΓ).hom.app (Opposite.op ⊤)) := by
    haveI : IsIso (tilde.toOpen
        ((modulesSpecToSheaf.obj N).presheaf.obj (Opposite.op ⊤)) ⊤) :=
      @tilde.isIso_toOpen_top _ ((modulesSpecToSheaf.obj N).presheaf.obj (Opposite.op ⊤))
    rw [← isIso_comp_left_iff
      (tilde.toOpen ((modulesSpecToSheaf.obj N).presheaf.obj (Opposite.op ⊤)) ⊤),
      Scheme.Modules.toOpen_fromTildeΓ_app]
    simpa using IsIso.id ((modulesSpecToSheaf.obj N).presheaf.obj (Opposite.op ⊤))
  haveI : IsIso (modulesSpecToSheaf.map N.fromTildeΓ) :=
    isIso_sheaf_of_isIso_top_of_subsingleton k _ _ htop
  exact isIso_of_reflects_iso N.fromTildeΓ modulesSpecToSheaf

/-- Every sheaf of modules on the spectrum of a field is quasi-coherent. -/
local instance isQuasicoherent_specField {k : Type u} [Field k]
    (N : (Spec (CommRingCat.of k)).Modules) : N.IsQuasicoherent := by
  exact (isQuasicoherent_iff_isIso_fromTildeΓ N).mpr
    (isIso_fromTildeΓ_specField N)

/-- Every sheaf of modules on `Spec k` is free (basis-indexed, with no finiteness assumption). -/
theorem exists_free_iso_specField (k : Type u) [Field k]
    (N : (Spec (CommRingCat.of k)).Modules) :
    ∃ I : Type u,
      Nonempty (N ≅ SheafOfModules.free (R := (Spec (CommRingCat.of k)).ringCatSheaf) I) := by
  let R : CommRingCat.{u} := CommRingCat.of k
  let V : ModuleCat.{u} R := (modulesSpecToSheaf.obj N).presheaf.obj (Opposite.op ⊤)
  let _ : Field (R : Type u) := inferInstanceAs (Field k)
  let b := Module.Basis.ofVectorSpace (R : Type u) (V : Type u)
  haveI : IsIso N.fromTildeΓ := isIso_fromTildeΓ_specField N
  refine ⟨Module.Basis.ofVectorSpaceIndex (R : Type u) (V : Type u), ⟨?_⟩⟩
  exact (asIso N.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso b.repr.toModuleIso ≪≫
    tildeFinsupp _

end ZInQ.Contrib.CloudR2Poincare.L3

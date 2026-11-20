import ZInQKernel.Contrib.CloudR2Poincare.L3.B2Interface
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.AcyclicResolution
import Mathlib.Topology.Sheaves.Flasque

/-!
# Finite closed support: flasque extension by zero and native cohomology

A section on V⊆U glues to zero on U\(S∩V), since the overlap has no support.
This proves actual flasqueness on the original scheme, without replacing F by
an unspecified finite subscheme. Native W07 flasque acyclicity and H0≅Γ finish.
-/

noncomputable section
open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L4

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- Sections on an open with zero stalks are zero, by the actual sheaf section-ext principle. -/
theorem sections_subsingleton_of_stalks {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (h : ∀ x : X, x ∈ U → Subsingleton (F.presheaf.stalk x)) :
    Subsingleton (F.presheaf.obj (op U)) := by
  constructor
  intro s t
  apply TopCat.Presheaf.section_ext F U s t
  intro x hx
  haveI := h x hx
  exact Subsingleton.elim _ _

/-- An actual abelian sheaf with finite CLOSED support is flasque. -/
theorem isFlasque_of_finite_closed_support {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (S : Set X) (hS : S.Finite)
    (hc : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hz : ∀ x : X, x ∉ S → Subsingleton (F.presheaf.stalk x)) :
    TopCat.Presheaf.IsFlasque F.presheaf := by
  classical
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  have hVU : V.unop ≤ U.unop := i.unop.le
  let T : Set X := S ∩ (V.unop : Set X)
  have hT : T.Finite := hS.subset fun _ hx => hx.1
  have hTc : IsClosed T := by
    have hh := hT.isClosed_biUnion (f := fun x => ({x} : Set X)) fun x hx => hc x hx.1
    have he : (⋃ x ∈ T, ({x} : Set X)) = T := by ext x; simp
    rwa [he] at hh
  let N : Opens X := ⟨(U.unop : Set X) \ T, U.unop.isOpen.sdiff hTc⟩
  have hNU : N ≤ U.unop := fun _ hx => hx.1
  have h0 : Subsingleton (F.presheaf.obj (op (V.unop ⊓ N))) :=
    sections_subsingleton_of_stalks F (V.unop ⊓ N) fun x hx => hz x (by
      intro hxS
      have hn : x ∈ U.unop ∧ x ∉ T := hx.2
      exact hn.2 ⟨hxS, hx.1⟩)
  letI := h0
  let f : Fin 2 → Opens X := ![V.unop, N]
  let sf : (j : Fin 2) → F.presheaf.obj (op (f j))
    | 0 => s
    | 1 => 0
  haveI : Subsingleton (F.presheaf.obj (op (f 0 ⊓ f 1))) := by
    simpa [f] using h0
  haveI : Subsingleton (F.presheaf.obj (op (f 1 ⊓ f 0))) := by
    simpa [f, inf_comm] using h0
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf f sf := by
    simp only [TopCat.Presheaf.IsCompatible, Fin.forall_fin_two]
    refine ⟨⟨rfl, Subsingleton.elim _ _⟩, ?_, rfl⟩
    haveI : Subsingleton (F.presheaf.obj (op (N ⊓ V.unop))) := by
      simpa only [inf_comm] using h0
    exact Subsingleton.elim _ _
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing F f sf hcompat
  have hsup : iSup f = U.unop := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      fin_cases j
      · exact hVU
      · exact hNU
    · intro x hx
      by_cases hv : x ∈ V.unop
      · exact (le_iSup f 0) hv
      · apply (le_iSup f 1)
        exact ⟨hx, fun hxt => hv hxt.2⟩
  refine ⟨F.presheaf.map (eqToHom hsup.symm).op t, ?_⟩
  rw [← Functor.map_comp_apply]
  have hi : (eqToHom hsup.symm).op ≫ i = (homOfLE (le_iSup f 0)).op :=
    Subsingleton.elim _ _
  rw [hi]
  exact ht 0

/-- The exact native B2 finite-support input is proved, with no extra labelled hypothesis. -/
theorem FiniteSupportCohomology_proof : L3.FiniteSupportCohomology.{u} := by
  intro k _ _ _ B F _ S hS hc hz
  let G := (SheafOfModules.toSheaf.{u} B.X.left.ringCatSheaf).obj F
  have hG : TopCat.Presheaf.IsFlasque G.obj :=
    isFlasque_of_finite_closed_support G S hS hc hz
  haveI := hG
  refine ⟨?_, ?_⟩
  · intro p hp
    cases p with
    | zero => exact False.elim ((lt_irrefl 0) hp)
    | succ n => exact TopCat.Sheaf.IsFlasque.subsingleton_H n G
  · intro hH0
    haveI := hH0
    haveI : Subsingleton Γ(F, ⊤) :=
      (Scheme.Modules.H.zeroLinearEquiv F).symm.injective.subsingleton
    haveI (U : B.X.left.Opens) : Subsingleton Γ(F, U) := by
      have hsurj : Function.Surjective (F.presheaf.map (homOfLE (le_top (a := U))).op) :=
        (AddCommGrpCat.epi_iff_surjective _).mp (hG.epi _)
      constructor
      intro x y
      obtain ⟨sx, rfl⟩ := hsurj x
      obtain ⟨sy, rfl⟩ := hsurj y
      rw [Subsingleton.elim sx sy]
    apply (IsZero.iff_id_eq_zero F).mpr
    ext U s
    exact Subsingleton.elim _ _

end ZInQ.Contrib.CloudR2Poincare.L4

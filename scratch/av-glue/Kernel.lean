import Mathlib
import ZInQKernel.Contrib.AVB1.Poincare

/-!
# av-glue, part C: `KernelAbSubvariety` from a statement about the kernel group scheme

Check with `lake env lean scratch/av-glue/Kernel.lean`.

`KernelAbSubvariety` (part A's leaf) has the hypothesis "`h` is not locally quasi-finite". Here
that hypothesis is moved to the kernel: if the kernel `ker h = A ×_B Spec k` (Mathlib's fibre
product of `h` with the identity section of `B`) is locally quasi-finite over `k`, then so is `h`
(the shear isomorphism `A ×_k ker h ≅ A ×_B A`, `(a, x) ↦ (a, a + x)`, proved here). So
`KernelAbSubvariety` follows from `KernelIdentityComponent`: if `ker h` is not quasi-finite over
`k`, `(ker h)⁰_red` is a positive-dimensional abelian subvariety killed by `h`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace AVGlue

/-- (verbatim from `scratch/av-glue/SurjIsog.lean`) **LEAF (new; `(ker h)⁰_red` is an abelian
subvariety).** See there. -/
def KernelAbSubvariety : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k)
    (h : _root_.PkgI3.AbVar.Hom A B), ¬ LocallyQuasiFinite h.hom.left →
    ∃ (C : _root_.PkgI3.AbVar k) (j : _root_.PkgI3.AbVar.Hom C A),
      IsClosedImmersion j.hom.left ∧ 0 < C.dim ∧ j.hom ≫ h.hom = 1

section Kernel

variable {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X)

/-- The kernel `ker h = A ×_B Spec k` (fibre product of `h` with the identity section), as a
`k`-scheme. -/
noncomputable abbrev kerOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (pullback.fst h.left (η[B.X]).left ≫ A.X.hom)

/-- The inclusion of the kernel. -/
noncomputable def kerι : kerOver h ⟶ A.X := Over.homMk (pullback.fst h.left (η[B.X]).left) rfl

lemma kerι_left : (kerι h).left = pullback.fst h.left (η[B.X]).left := rfl

instance : Mono (kerι h) := by
  haveI : Mono (kerι h).left := (inferInstance : Mono (pullback.fst h.left (η[B.X]).left))
  exact Over.mono_of_mono_left _

lemma ker_snd_eq :
    pullback.snd h.left (η[B.X]).left = pullback.fst h.left (η[B.X]).left ≫ A.X.hom := by
  have h2 := congrArg (· ≫ B.X.hom) (pullback.condition (f := h.left) (g := (η[B.X]).left))
  simp only [Category.assoc, Over.w] at h2
  simpa using h2.symm

lemma kerι_comp : kerι h ≫ h = 1 := by
  ext1
  rw [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left, kerι_left, pullback.condition,
    ker_snd_eq]
  rfl

/-- Lifting into the kernel. -/
noncomputable def kerLift {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ A.X) (hg : g ≫ h = 1) :
    W ⟶ kerOver h :=
  Over.homMk (pullback.lift g.left W.hom (by
    have := congrArg Over.Hom.left hg
    rwa [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left] at this)) (by simp)

@[reassoc (attr := simp)]
lemma kerLift_ι {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ A.X) (hg : g ≫ h = 1) :
    kerLift h g hg ≫ kerι h = g := by
  ext1; simp [kerLift, kerι]

/-! ### The shear isomorphism `A ×_k ker h ≅ A ×_B A` -/

variable [IsMonHom h]

/-- `(a, x) ↦ a + x`. -/
noncomputable def shearS : A.X ⊗ kerOver h ⟶ A.X := fst _ _ * (snd _ _ ≫ kerι h)

lemma shearS_comp : shearS h ≫ h = fst _ _ ≫ h := by
  rw [shearS, MonObj.mul_comp, Category.assoc, kerι_comp, MonObj.comp_one, _root_.mul_one]

/-- `A ×_B A` as a `k`-scheme. -/
noncomputable abbrev pbOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (pullback.fst h.left h.left ≫ A.X.hom)

lemma pb_w : pullback.snd h.left h.left ≫ A.X.hom = pullback.fst h.left h.left ≫ A.X.hom := by
  have h2 := congrArg (· ≫ B.X.hom) (pullback.condition (f := h.left) (g := h.left))
  simp only [Category.assoc, Over.w] at h2
  exact h2.symm

noncomputable def pbFst : pbOver h ⟶ A.X := Over.homMk (pullback.fst h.left h.left) rfl
noncomputable def pbSnd : pbOver h ⟶ A.X := Over.homMk (pullback.snd h.left h.left) (pb_w h)

lemma pbFst_comp : pbFst h ≫ h = pbSnd h ≫ h := by
  ext1; exact pullback.condition

/-- `(a, a') ↦ a' - a`. -/
noncomputable def pbD : pbOver h ⟶ A.X := (pbFst h)⁻¹ * pbSnd h

lemma pbD_comp : pbD h ≫ h = 1 := by
  rw [pbD, MonObj.mul_comp, GrpObj.inv_comp, pbFst_comp, inv_mul_cancel]

noncomputable def pbT : pbOver h ⟶ kerOver h := kerLift h (pbD h) (pbD_comp h)

/-- The shear map `A ×_k ker h → A ×_B A`. -/
noncomputable def shearHom : (A.X ⊗ kerOver h).left ⟶ pullback h.left h.left :=
  pullback.lift (fst A.X (kerOver h)).left (shearS h).left (by
    rw [← Over.comp_left, ← Over.comp_left, shearS_comp])

/-- Its inverse. -/
noncomputable def shearInv : pullback h.left h.left ⟶ (A.X ⊗ kerOver h).left :=
  pullback.lift (pullback.fst h.left h.left) (pbT h).left (by
    have := Over.w (pbT h)
    simpa using this.symm)

noncomputable def shearHomO : A.X ⊗ kerOver h ⟶ pbOver h :=
  Over.homMk (shearHom h) (by simp [shearHom])

noncomputable def shearInvO : pbOver h ⟶ A.X ⊗ kerOver h :=
  Over.homMk (shearInv h) (by simp [shearInv])

lemma shearHomO_fst : shearHomO h ≫ pbFst h = fst _ _ := by
  ext1; simp [shearHomO, pbFst, shearHom]

lemma shearHomO_snd : shearHomO h ≫ pbSnd h = shearS h := by
  ext1; simp [shearHomO, pbSnd, shearHom]

lemma shearInvO_fst : shearInvO h ≫ fst _ _ = pbFst h := by
  ext1; simp [shearInvO, pbFst, shearInv]

lemma shearInvO_snd : shearInvO h ≫ snd _ _ = pbT h := by
  ext1; simp [shearInvO, shearInv]

/-- The shear isomorphism. -/
noncomputable def shearIso : (A.X ⊗ kerOver h).left ≅ pullback h.left h.left where
  hom := shearHom h
  inv := shearInv h
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [shearHom, shearInv]
    · apply (cancel_mono (pullback.fst h.left (η[B.X]).left)).1
      have e1 : shearHomO h ≫ pbD h = snd _ _ ≫ kerι h := by
        rw [pbD, MonObj.comp_mul, GrpObj.comp_inv, shearHomO_fst, shearHomO_snd, shearS,
          inv_mul_cancel_left]
      have e2 := congrArg Over.Hom.left e1
      simp only [Over.comp_left] at e2
      simp only [Category.assoc, shearInv, pullback.lift_snd]
      change shearHom h ≫ (pbT h ≫ kerι h).left = _
      rw [pbT, kerLift_ι]
      exact e2.trans (by simp [kerι])
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [shearHom, shearInv]
    · have e1 : shearInvO h ≫ shearS h = pbSnd h := by
        rw [shearS, MonObj.comp_mul, ← Category.assoc, shearInvO_fst, shearInvO_snd, pbT,
          kerLift_ι, pbD, mul_inv_cancel_left]
      have e2 := congrArg Over.Hom.left e1
      simp only [Over.comp_left] at e2
      simp only [Category.assoc, shearHom, pullback.lift_snd]
      change shearInv h ≫ (shearS h).left = _
      exact e2.trans (by simp [pbSnd])

lemma shearIso_hom_fst :
    (shearIso h).hom ≫ pullback.fst h.left h.left = pullback.fst A.X.hom (kerOver h).hom := by
  simp [shearIso, shearHom]

/-- **If the kernel is locally quasi-finite over `k`, so is `h`.** -/
theorem lqf_of_ker [IsProper h.left] (hK : LocallyQuasiFinite (kerOver h).hom) :
    LocallyQuasiFinite h.left := by
  haveI : LocallyQuasiFinite (pullback.fst A.X.hom (kerOver h).hom) := inferInstance
  haveI : LocallyQuasiFinite (pullback.fst h.left h.left) := by
    have : pullback.fst h.left h.left =
        (shearIso h).inv ≫ pullback.fst A.X.hom (kerOver h).hom := by
      rw [← shearIso_hom_fst, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
  by_cases hy : y ∈ Set.range h.left
  · obtain ⟨x0, rfl⟩ := hy
    refine (((pullback.fst h.left h.left).finite_preimage_singleton x0).image
      (pullback.snd h.left h.left)).subset ?_
    intro a ha
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x0 a ha.symm
    exact ⟨z, hz1, hz2⟩
  · exact Set.finite_empty.subset fun a ha => hy ⟨a, ha⟩

end Kernel

/-- **LEAF (`(ker h)⁰_red` is an abelian subvariety, kernel form).** Over a field of
characteristic `0`, let `h : A → B` be a homomorphism of abelian varieties and
`ker h = A ×_B Spec k` its kernel (Mathlib's fibre product of `h` with the identity section of
`B`). If `ker h` is not locally quasi-finite over `k` (i.e. `ker h` is positive-dimensional),
there is an abelian variety `C` with a homomorphism `j : C → A` that is a closed immersion,
`0 < dim C`, and `h ∘ j = 0`: take `C = (ker h)⁰_red`. Sources (UNVERIFIED locators): Milne,
*Abelian varieties* (Cornell-Silverman 1986), §8; Milne's notes (2008) I §8; Mumford §8; reduced
group schemes over a perfect field are smooth, and in characteristic `0` every group scheme of
finite type is reduced (Cartier; Mumford §11 Thm 1); `dim (ker h)⁰ = dim ker h` (a group scheme of
finite type over a field is equidimensional). A consequence of these, never stronger. -/
def KernelIdentityComponent : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k)
    (h : _root_.PkgI3.AbVar.Hom A B),
    ¬ LocallyQuasiFinite (pullback.fst h.hom.left (η[B.X]).left ≫ A.X.hom) →
    ∃ (C : _root_.PkgI3.AbVar k) (j : _root_.PkgI3.AbVar.Hom C A),
      IsClosedImmersion j.hom.left ∧ 0 < C.dim ∧ j.hom ≫ h.hom = 1

/-- A homomorphism of abelian varieties is proper. -/
theorem isProper_hom'' {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) :
    IsProper h.left := by
  have : IsProper (h.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp h.left B.X.hom

/-- **`KernelAbSubvariety` from `KernelIdentityComponent`** (glue: the shear isomorphism). -/
theorem kernelAbSubvariety_of_identityComponent (hK1 : KernelIdentityComponent) :
    KernelAbSubvariety := by
  intro k _ _ A B h hnot
  refine hK1 k A B h fun hq => hnot ?_
  haveI := isProper_hom'' h.hom
  exact lqf_of_ker h.hom hq

end AVGlue

#print axioms AVGlue.kernelAbSubvariety_of_identityComponent

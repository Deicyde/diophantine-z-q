import Mathlib

/-!
# The finite-kernel argument for a complement sum

H-72 round 2, lane L4. This file works in the actual category `Over (Spec k)` with
Mathlib's Cartesian monoidal structure and `GrpObj`, not a substitute group or torus.

CHANGE NOTICE / SOURCE CREDIT: the kernel, lifting, and shear constructions below are
adapted from the unconditional first section of `scratch/av-glue/Kernel.lean` at
`df98652abbeeef78b57f0868f19523a26d811b58`. We generalize its `PkgI3.AbVar` parameters
into explicit `Over (Spec k)` objects and proper/separated hypotheses. No conditional
Cartier, connected-component, or equidimensionality leaf from that source is used.

The new argument projects the kernel of `(b,z) ↦ i(b)g(z)` to `B`. This projection is
monic because `g` is monic; it is proper, hence a closed immersion. Its composite with
the finite map `φ ∘ i` is the unit map. Thus the kernel is finite over `k`, and the
source's shear isomorphism proves local quasi-finiteness of the sum. Proper plus
locally quasi-finite gives finiteness.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

variable {k : Type u} [Field k]

/-- A map from a proper `k`-scheme to a separated `k`-scheme is proper. -/
theorem isProper_over_hom {A J : Over (Spec (.of k))} [IsProper A.hom]
    [IsSeparated J.hom] (h : A ⟶ J) : IsProper h.left := by
  haveI : IsProper (h.left ≫ J.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp h.left J.hom

/-- The identity section of a separated group scheme is a closed immersion. -/
theorem isClosedImmersion_eta (J : Over (Spec (.of k))) [GrpObj J]
    [IsSeparated J.hom] : IsClosedImmersion (η[J]).left := by
  haveI : IsClosedImmersion ((η[J]).left ≫ J.hom) := by
    rw [Over.w]
    change IsClosedImmersion (𝟙 (Spec (.of k)))
    infer_instance
  exact IsClosedImmersion.of_comp (η[J]).left J.hom

section Kernel

variable {A J : Over (Spec (.of k))} [GrpObj J] (h : A ⟶ J)

/-- The scheme-theoretic kernel as the pullback along the identity section. -/
abbrev kerOver : Over (Spec (.of k)) :=
  Over.mk (pullback.fst h.left (η[J]).left ≫ A.hom)

/-- The kernel inclusion. -/
def kerι : kerOver h ⟶ A :=
  Over.homMk (pullback.fst h.left (η[J]).left) rfl

lemma kerι_left : (kerι h).left = pullback.fst h.left (η[J]).left := rfl

instance [IsSeparated J.hom] : Mono (kerι h) := by
  haveI := isClosedImmersion_eta J
  haveI : Mono (kerι h).left :=
    (inferInstance : Mono (pullback.fst h.left (η[J]).left))
  exact Over.mono_of_mono_left _

instance [IsSeparated J.hom] : IsClosedImmersion (kerι h).left := by
  haveI := isClosedImmersion_eta J
  exact inferInstanceAs (IsClosedImmersion (pullback.fst h.left (η[J]).left))

instance [IsSeparated J.hom] [IsProper A.hom] : IsProper (kerOver h).hom := by
  dsimp only [kerOver, Over.mk_hom]
  haveI := isClosedImmersion_eta J
  infer_instance

lemma ker_snd_eq :
    pullback.snd h.left (η[J]).left = pullback.fst h.left (η[J]).left ≫ A.hom := by
  have h2 := congrArg (· ≫ J.hom)
    (pullback.condition (f := h.left) (g := (η[J]).left))
  simp only [Category.assoc, Over.w] at h2
  simpa using h2.symm

lemma kerι_comp : kerι h ≫ h = 1 := by
  ext1
  rw [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left, kerι_left,
    pullback.condition, ker_snd_eq]
  rfl

/-- The universal lift into the scheme-theoretic kernel. -/
def kerLift {W : Over (Spec (.of k))} (g : W ⟶ A) (hg : g ≫ h = 1) :
    W ⟶ kerOver h :=
  Over.homMk (pullback.lift g.left W.hom (by
    have he := congrArg Over.Hom.left hg
    rwa [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left] at he)) (by simp)

@[reassoc (attr := simp)]
lemma kerLift_ι {W : Over (Spec (.of k))} (g : W ⟶ A) (hg : g ≫ h = 1) :
    kerLift h g hg ≫ kerι h = g := by
  ext1
  simp [kerLift, kerι]

variable [GrpObj A] [IsMonHom h]

/-- `(a,x) ↦ ax`. -/
def shearS : A ⊗ kerOver h ⟶ A := fst _ _ * (snd _ _ ≫ kerι h)

lemma shearS_comp : shearS h ≫ h = fst _ _ ≫ h := by
  rw [shearS, MonObj.mul_comp, Category.assoc, kerι_comp, MonObj.comp_one, _root_.mul_one]

/-- `A ×_J A` considered as a `k`-scheme. -/
abbrev pbOver : Over (Spec (.of k)) :=
  Over.mk (pullback.fst h.left h.left ≫ A.hom)

lemma pb_w : pullback.snd h.left h.left ≫ A.hom =
    pullback.fst h.left h.left ≫ A.hom := by
  have h2 := congrArg (· ≫ J.hom) (pullback.condition (f := h.left) (g := h.left))
  simp only [Category.assoc, Over.w] at h2
  exact h2.symm

def pbFst : pbOver h ⟶ A := Over.homMk (pullback.fst h.left h.left) rfl

def pbSnd : pbOver h ⟶ A := Over.homMk (pullback.snd h.left h.left) (pb_w h)

lemma pbFst_comp : pbFst h ≫ h = pbSnd h ≫ h := by
  ext1
  exact pullback.condition

/-- `(a,a') ↦ a⁻¹a'`. -/
def pbD : pbOver h ⟶ A := (pbFst h)⁻¹ * pbSnd h

lemma pbD_comp : pbD h ≫ h = 1 := by
  rw [pbD, MonObj.mul_comp, GrpObj.inv_comp, pbFst_comp, inv_mul_cancel]

def pbT : pbOver h ⟶ kerOver h := kerLift h (pbD h) (pbD_comp h)

def shearHom : (A ⊗ kerOver h).left ⟶ pullback h.left h.left :=
  pullback.lift (fst A (kerOver h)).left (shearS h).left (by
    rw [← Over.comp_left, ← Over.comp_left, shearS_comp])

def shearInv : pullback h.left h.left ⟶ (A ⊗ kerOver h).left :=
  pullback.lift (pullback.fst h.left h.left) (pbT h).left (by
    have he := Over.w (pbT h)
    simpa using he.symm)

def shearHomO : A ⊗ kerOver h ⟶ pbOver h :=
  Over.homMk (shearHom h) (by simp [shearHom])

def shearInvO : pbOver h ⟶ A ⊗ kerOver h :=
  Over.homMk (shearInv h) (by simp [shearInv])

lemma shearHomO_fst : shearHomO h ≫ pbFst h = fst _ _ := by
  ext1
  simp [shearHomO, pbFst, shearHom]

lemma shearHomO_snd : shearHomO h ≫ pbSnd h = shearS h := by
  ext1
  simp [shearHomO, pbSnd, shearHom]

lemma shearInvO_fst : shearInvO h ≫ fst _ _ = pbFst h := by
  ext1
  simp [shearInvO, pbFst, shearInv]

lemma shearInvO_snd : shearInvO h ≫ snd _ _ = pbT h := by
  ext1
  simp [shearInvO, shearInv]

/-- The exact scheme-level shear `A ×_k ker(h) ≅ A ×_J A`. -/
def shearIso [IsSeparated J.hom] : (A ⊗ kerOver h).left ≅ pullback h.left h.left where
  hom := shearHom h
  inv := shearInv h
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [shearHom, shearInv]
    · apply (cancel_mono (pullback.fst h.left (η[J]).left)).1
      have e1 : shearHomO h ≫ pbD h = snd _ _ ≫ kerι h := by
        rw [pbD, MonObj.comp_mul, GrpObj.comp_inv, shearHomO_fst, shearHomO_snd,
          shearS, inv_mul_cancel_left]
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
        rw [shearS, MonObj.comp_mul, ← Category.assoc, shearInvO_fst, shearInvO_snd,
          pbT, kerLift_ι, pbD, mul_inv_cancel_left]
      have e2 := congrArg Over.Hom.left e1
      simp only [Over.comp_left] at e2
      simp only [Category.assoc, shearHom, pullback.lift_snd]
      change shearInv h ≫ (shearS h).left = _
      exact e2.trans (by simp [pbSnd])

lemma shearIso_hom_fst [IsSeparated J.hom] :
    (shearIso h).hom ≫ pullback.fst h.left h.left = pullback.fst A.hom (kerOver h).hom := by
  simp [shearIso, shearHom]

/-- A proper group homomorphism with a locally quasi-finite kernel is locally quasi-finite. -/
theorem lqf_of_ker [IsSeparated J.hom] [IsProper h.left]
    (hK : LocallyQuasiFinite (kerOver h).hom) : LocallyQuasiFinite h.left := by
  haveI : LocallyQuasiFinite (pullback.fst A.hom (kerOver h).hom) := inferInstance
  haveI : LocallyQuasiFinite (pullback.fst h.left h.left) := by
    have he : pullback.fst h.left h.left =
        (shearIso h).inv ≫ pullback.fst A.hom (kerOver h).hom := by
      rw [← shearIso_hom_fst, Iso.inv_hom_id_assoc]
    rw [he]
    infer_instance
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

section Sum

variable (B Z J D : Over (Spec (.of k))) [GrpObj B] [GrpObj Z] [GrpObj J] [GrpObj D]
    [IsCommMonObj J] [IsProper B.hom] [IsProper Z.hom] [IsProper J.hom]
    [IsSeparated D.hom]
    (i : B ⟶ J) (g : Z ⟶ J) (φ : J ⟶ D)
    [IsMonHom i] [IsMonHom g] [IsMonHom φ]

/-- The literal complement sum map. -/
abbrev sumMap : B ⊗ Z ⟶ J := fst B Z ≫ i * snd B Z ≫ g

instance : IsMonHom (sumMap B Z J i g) := by
  change IsMonHom (lift (fst B Z ≫ i) (snd B Z ≫ g) ≫ μ[J])
  infer_instance

/-- Projection of the kernel of the sum to its `B` coordinate. -/
def sumKerPr : kerOver (sumMap B Z J i g) ⟶ B :=
  kerι (sumMap B Z J i g) ≫ fst B Z

/-- Injectivity of `g` makes the projection of the kernel to `B` monic. -/
theorem mono_sumKerPr [IsClosedImmersion g.left] : Mono (sumKerPr B Z J i g) := by
  haveI : Mono g := Over.mono_of_mono_left g
  constructor
  intro W u v hp
  apply (cancel_mono (kerι (sumMap B Z J i g))).1
  have eb : u ≫ kerι (sumMap B Z J i g) ≫ fst B Z ≫ i =
      v ≫ kerι (sumMap B Z J i g) ≫ fst B Z ≫ i := by
    simpa only [sumKerPr, Category.assoc] using congrArg (· ≫ i) hp
  have eu : (u ≫ kerι (sumMap B Z J i g) ≫ fst B Z ≫ i) *
      (u ≫ kerι (sumMap B Z J i g) ≫ snd B Z ≫ g) = 1 := by
    simpa only [sumMap, MonObj.comp_mul, Category.assoc, MonObj.comp_one] using
      congrArg (u ≫ ·) (kerι_comp (sumMap B Z J i g))
  have ev : (v ≫ kerι (sumMap B Z J i g) ≫ fst B Z ≫ i) *
      (v ≫ kerι (sumMap B Z J i g) ≫ snd B Z ≫ g) = 1 := by
    simpa only [sumMap, MonObj.comp_mul, Category.assoc, MonObj.comp_one] using
      congrArg (v ≫ ·) (kerι_comp (sumMap B Z J i g))
  have ezg : u ≫ kerι (sumMap B Z J i g) ≫ snd B Z ≫ g =
      v ≫ kerι (sumMap B Z J i g) ≫ snd B Z ≫ g := by
    rw [eb] at eu
    exact mul_left_cancel (eu.trans ev.symm)
  have ez : u ≫ kerι (sumMap B Z J i g) ≫ snd B Z =
      v ≫ kerι (sumMap B Z J i g) ≫ snd B Z := by
    apply (cancel_mono g).1
    simpa only [Category.assoc] using ezg
  ext1
  · simpa only [sumKerPr, Category.assoc] using hp
  · simpa only [Category.assoc] using ez

/-- The kernel of the complement sum is finite over the ground field. -/
theorem finite_sum_kernel [IsClosedImmersion g.left] [IsFinite (i ≫ φ).left]
    (hg : g ≫ φ = 1) : IsFinite (kerOver (sumMap B Z J i g)).hom := by
  haveI : IsProper (B ⊗ Z).hom := by dsimp; infer_instance
  haveI : Mono (sumKerPr B Z J i g) := mono_sumKerPr B Z J i g
  haveI : IsProper (sumKerPr B Z J i g).left :=
    isProper_over_hom (sumKerPr B Z J i g)
  haveI : IsClosedImmersion (sumKerPr B Z J i g).left :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  have hpφ : sumKerPr B Z J i g ≫ (i ≫ φ) = 1 := by
    have he := congrArg (· ≫ φ) (kerι_comp (sumMap B Z J i g))
    simpa only [sumMap, sumKerPr, MonObj.mul_comp, MonObj.comp_mul, Category.assoc,
      hg, MonObj.comp_one, MonObj.one_comp, _root_.mul_one] using he
  have he := congrArg Over.Hom.left hpφ
  simp only [Over.comp_left, Hom.one_def, Over.toUnit_left] at he
  haveI : IsFinite ((kerOver (sumMap B Z J i g)).hom ≫ (η[D]).left) := by
    rw [← he]
    infer_instance
  exact IsFinite.of_comp _ (η[D]).left

/-- A complement sum is finite when `g` is a closed immersion, `φ ∘ g = 0`, and `φ ∘ i` is finite. -/
theorem finite_sum [IsClosedImmersion g.left] [IsFinite (i ≫ φ).left]
    (hg : g ≫ φ = 1) : IsFinite (sumMap B Z J i g).left := by
  haveI : IsProper (B ⊗ Z).hom := by dsimp; infer_instance
  haveI : IsProper (sumMap B Z J i g).left := isProper_over_hom _
  haveI : IsFinite (kerOver (sumMap B Z J i g)).hom := finite_sum_kernel B Z J D i g φ hg
  haveI : LocallyQuasiFinite (sumMap B Z J i g).left := lqf_of_ker _ inferInstance
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Sum

end ZInQ.Contrib.CloudR2Poincare.L4

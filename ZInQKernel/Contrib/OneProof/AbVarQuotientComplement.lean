import ZInQKernel.Contrib.OneProof.AbVarQuotientFinite
import ZInQKernel.Contrib.CloudR2Poincare.FinalUnconditional
import ZInQKernel.Contrib.OneProof.ShimuraQuotientGeometry

/-! The quotient by an abelian subvariety, via a finite quotient of a complement. -/

noncomputable section

namespace ShimuraSteps.Quotient

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar
open ZInQ.Contrib.MilneQuasiInverse
open Descent.GroupDescent.Construction Descent.GroupKernelPowerDescent.Construction
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 700000

attribute [local instance] Kernel.kernelGroup

local notation "OverQ" => Over (Spec (CommRingCat.of ℚ))

variable {C B J Q : AbVar ℚ}

private abbrev abVarProduct (A B : AbVar ℚ) : AbVar ℚ where
  X := A.X ⊗ B.X
  proper := by
    change IsProper (pullback.fst A.X.hom B.X.hom ≫ A.X.hom)
    infer_instance
  smooth := by
    change Smooth (pullback.fst A.X.hom B.X.hom ≫ A.X.hom)
    infer_instance
  geomInt := by
    change GeometricallyIntegral (pullback.fst A.X.hom B.X.hom ≫ A.X.hom)
    have : Smooth (pullback.fst A.X.hom B.X.hom ≫ A.X.hom) := inferInstance
    have : GeometricallyConnected (pullback.fst A.X.hom B.X.hom ≫ A.X.hom) :=
      GeometricallyConnected.comp _ _
    exact TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral _

private abbrev addMap (i : AbVar.Hom C J) (g : AbVar.Hom B J) :
    AbVar.Hom (abVarProduct C B) J :=
  Hom.mk' ((fst C.X B.X ≫ i.hom) * (snd C.X B.X ≫ g.hom))

private abbrev intersectionInclusion (i : AbVar.Hom C J) (g : AbVar.Hom B J) :
    Kernel.kernelObject (addMap i g).hom ⟶ B.X :=
  Kernel.kernelInclusion (addMap i g).hom ≫ snd C.X B.X

private abbrev intersectionToC (i : AbVar.Hom C J) (g : AbVar.Hom B J) :
    Kernel.kernelObject (addMap i g).hom ⟶ C.X :=
  (Kernel.kernelInclusion (addMap i g).hom ≫ fst C.X B.X)⁻¹

/-- The kernel of addition, with the first coordinate negated, is the
scheme-theoretic intersection of the complement map with the subvariety. -/
private theorem intersection_isPullback (i : AbVar.Hom C J) (g : AbVar.Hom B J) :
    IsPullback (intersectionInclusion i g) (intersectionToC i g) g.hom i.hom := by
  let s := (addMap i g).hom
  let k := Kernel.kernelInclusion s
  have h : (k ≫ fst C.X B.X ≫ i.hom) * (k ≫ snd C.X B.X ≫ g.hom) = 1 := by
    simpa only [k, s, Hom.hom_mk', MonObj.comp_mul, Category.assoc] using
      Kernel.kernelInclusion_comp s
  have hw : intersectionInclusion i g ≫ g.hom = intersectionToC i g ≫ i.hom := by
    rw [intersectionToC, GrpObj.inv_comp]
    simpa only [k, s, intersectionInclusion, Category.assoc] using eq_inv_of_mul_eq_one_right h
  haveI : Mono k := inferInstance
  refine IsPullback.mk' hw (fun {T} {u v} h₁ h₂ => ?_) ?_
  · apply (cancel_mono k).mp
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [intersectionToC, GrpObj.comp_inv, inv_inj, Category.assoc, k, s] using h₂
    · simpa only [intersectionInclusion, Category.assoc, k, s] using h₁
  · intro T b c hbc
    let x : T ⟶ (abVarProduct C B).X := lift c⁻¹ b
    have hx : x ≫ s = 1 := by
      simp only [s, x, Hom.hom_mk', MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        GrpObj.inv_comp, hbc, inv_mul_cancel]
    let y := (Kernel.kernelPointsEquiv s T).symm ⟨x, hx⟩
    have hy : y ≫ k = x := pullback.lift_fst _ _ _
    refine ⟨y, ?_, ?_⟩
    · change y ≫ k ≫ snd C.X B.X = b
      rw [← Category.assoc, hy, lift_snd]
    · change y ≫ (k ≫ fst C.X B.X)⁻¹ = c
      rw [GrpObj.comp_inv, ← Category.assoc, hy, lift_fst, inv_inv]

/-- Factoring through a monomorphism can be checked after an effective epimorphism. -/
private theorem factor_of_effectiveEpi {X Y Z W : OverQ} (e : X ⟶ Y) [EffectiveEpi e]
    (i : Z ⟶ W) [Mono i] (a : Y ⟶ W) (u : X ⟶ Z) (h : u ≫ i = e ≫ a) :
    ∃ v : Y ⟶ Z, v ≫ i = a := by
  have hr {T : OverQ} (x y : T ⟶ X) (hxy : x ≫ e = y ≫ e) : x ≫ u = y ≫ u := by
    apply (cancel_mono i).mp
    simpa only [Category.assoc, h] using congrArg (· ≫ a) hxy
  refine ⟨EffectiveEpi.desc e u hr, (cancel_epi e).mp ?_⟩
  rw [← Category.assoc, EffectiveEpi.fac, h]

private theorem descended_kernel (i : AbVar.Hom C J) (g : AbVar.Hom B J)
    [Mono i.hom] [IsFinite (addMap i g).hom.left] [Flat (addMap i g).hom.left]
    [Surjective (addMap i g).hom.left] {p : AbVar.Hom B Q}
    (hp : IsFiniteSubgroupQuotient (intersectionInclusion i g) p) (q : AbVar.Hom J Q)
    (hq : (addMap i g).hom ≫ q.hom = snd C.X B.X ≫ p.hom)
    (hi : i.hom ≫ q.hom = 1) :
    IsPullback i.hom (toUnit C.X) q.hom η[Q.X] := by
  refine IsPullback.mk' hi (fun {T} {u v} hu _ => (cancel_mono i.hom).mp hu) ?_
  intro T x r hx
  let s := (addMap i g).hom
  let a : pullback s x ⟶ (abVarProduct C B).X := pullback.fst _ _
  let e : pullback s x ⟶ T := pullback.snd _ _
  have he : a ≫ s = e ≫ x := pullback.condition
  have hpb : IsPullback a e s x := IsPullback.of_hasPullback s x
  have hpb' := (Over.forget _).map_isPullback hpb
  haveI : Flat e.left := MorphismProperty.of_isPullback (P := @Flat) hpb' (inferInstance : Flat s.left)
  haveI : IsFinite e.left := MorphismProperty.of_isPullback (P := @IsFinite) hpb' (inferInstance : IsFinite s.left)
  haveI : Surjective e.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb' (inferInstance : Surjective s.left)
  haveI : EffectiveEpi e := effectiveEpi_over_of_fpqc e
  have hb : (a ≫ snd C.X B.X) ≫ p.hom = toUnit _ ≫ η[Q.X] := by
    rw [Category.assoc, ← hq, ← Category.assoc, he, Category.assoc, hx, ← Category.assoc]
    exact congrArg (· ≫ η[Q.X]) (toUnit_unique _ _)
  let b := hp.kernel.lift (a ≫ snd C.X B.X) (toUnit _) hb
  have hb' : b ≫ intersectionInclusion i g = a ≫ snd C.X B.X := hp.kernel.lift_fst _ _ _
  let u := (a ≫ fst C.X B.X) * (b ≫ intersectionToC i g)
  have hu : u ≫ i.hom = e ≫ x := by
    rw [← he]
    have hw : b ≫ intersectionToC i g ≫ i.hom = a ≫ snd C.X B.X ≫ g.hom := by
      rw [← (intersection_isPullback i g).w, ← Category.assoc, hb', Category.assoc]
    simp only [u, MonObj.mul_comp, Category.assoc, hw, s, Hom.hom_mk', MonObj.comp_mul]
  obtain ⟨v, hv⟩ := factor_of_effectiveEpi e i.hom x u hu
  exact ⟨v, hv, toUnit_unique _ _⟩

/-- The quotient by an abelian subvariety over ℚ exists, including its actual
scheme-theoretic kernel and its universal property for abelian varieties. -/
theorem abVarQuotientBySubvarietyExists : AbVarQuotientBySubvarietyExists := by
  intro J C i hi
  obtain ⟨B, g, hs⟩ := ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof ℚ J C i hi
  let s := (addMap i g).hom
  haveI : IsFinite s.left := hs.1
  haveI : Surjective s.left := hs.2
  haveI : IsClosedImmersion i.hom.left := hi
  haveI : Mono i.hom := Over.mono_of_mono_left _
  haveI : Flat s.left := finite_surjective_abVarHom_flat (addMap i g) hs
  let j := intersectionInclusion i g
  have hpb := intersection_isPullback i g
  haveI : IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      ((Over.forget _).map_isPullback hpb.flip) hi
  haveI : IsFinite (Kernel.kernelObject s).hom := Kernel.kernel_isFinite s
  obtain ⟨Q, p, hp⟩ := finiteSubgroupQuotient_exists B j
  let f : AbVar.Hom (abVarProduct C B) Q := Hom.mk' (snd C.X B.X ≫ p.hom)
  haveI : Epi s := ZInQ.Contrib.CloudR2Poincare.L4.epi_over_of_flat_surjective s
  haveI : EffectiveEpi s.left := inferInstance
  haveI : Epi (s ⊗ₘ s) := by
    haveI := effectiveEpi_tensor_over_of_fpqc s s
    infer_instance
  obtain ⟨q₀, hq₀, hq⟩ := groupHom_descends_of_kernel s f.hom (fun T x hx => by
    let x' := (Kernel.kernelPointsEquiv s T).symm ⟨x, hx⟩
    have hx' : x' ≫ Kernel.kernelInclusion s = x := pullback.lift_fst _ _ _
    have hh : x ≫ snd C.X B.X = x' ≫ j := by
      simpa only [j, intersectionInclusion, Category.assoc] using
        congrArg (· ≫ snd C.X B.X) hx'.symm
    change x ≫ (snd C.X B.X ≫ p.hom) = 1
    have hz : j ≫ p.hom = 1 := hp.kernel.w
    rw [← Category.assoc, hh, Category.assoc, hz, MonObj.comp_one])
  haveI := hq₀
  let q : AbVar.Hom J Q := Hom.mk' q₀
  have hq' : s ≫ q.hom = snd C.X B.X ≫ p.hom := hq
  have hqC : i.hom ≫ q.hom = 1 := by
    let l : C.X ⟶ (abVarProduct C B).X := lift (𝟙 C.X) (1 : C.X ⟶ B.X)
    have hl : l ≫ s = i.hom := by
      simp [l, s, MonObj.comp_mul]
    have h := congrArg (l ≫ ·) hq'
    rw [← Category.assoc, hl, ← Category.assoc, show l ≫ snd C.X B.X = 1 by simp [l],
      MonObj.one_comp] at h
    exact h
  have hqB : g.hom ≫ q.hom = p.hom := by
    let l : B.X ⟶ (abVarProduct C B).X := lift (1 : B.X ⟶ C.X) (𝟙 B.X)
    have hl : l ≫ s = g.hom := by
      simp [l, s, MonObj.comp_mul]
    have h := congrArg (l ≫ ·) hq'
    rw [← Category.assoc, hl, ← Category.assoc, show l ≫ snd C.X B.X = 𝟙 _ by simp [l],
      Category.id_comp] at h
    exact h
  haveI : Surjective p.hom.left := hp.isogeny.2
  haveI : Surjective (g.hom.left ≫ q.hom.left) := by
    change Surjective (g.hom ≫ q.hom).left
    rw [hqB]
    infer_instance
  have hsurj : Surjective q.hom.left := Surjective.of_comp g.hom.left q.hom.left
  refine ⟨Q, q, ⟨hsurj, descended_kernel i g hp q hq' hqC, ?_⟩⟩
  intro D v hv
  let gv : AbVar.Hom B D := Hom.mk' (g.hom ≫ v.hom)
  have hjv : j ≫ gv.hom = 1 := by
    change j ≫ g.hom ≫ v.hom = 1
    rw [← Category.assoc, hpb.w, Category.assoc, hv, Hom.hom_zero, MonObj.comp_one]
  obtain ⟨w, hw, huw⟩ := hp.lift_unique D gv hjv
  have hw' : q.hom ≫ w.hom = v.hom := by
    apply (cancel_epi s).mp
    rw [← Category.assoc, hq', Category.assoc, hw]
    change snd C.X B.X ≫ g.hom ≫ v.hom =
      ((fst C.X B.X ≫ i.hom) * (snd C.X B.X ≫ g.hom)) ≫ v.hom
    simp only [MonObj.mul_comp, Category.assoc, hv, Hom.hom_zero, MonObj.comp_one, _root_.one_mul]
  refine ⟨w, hw', fun w' hw'' => huw w' ?_⟩
  change p.hom ≫ w'.hom = g.hom ≫ v.hom
  rw [← hqB, Category.assoc, hw'']

end ShimuraSteps.Quotient

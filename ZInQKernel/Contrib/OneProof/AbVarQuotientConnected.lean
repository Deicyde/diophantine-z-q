import ZInQKernel.Contrib.OneProof.AbVarQuotientComplement
import ZInQKernel.Contrib.CloudR2Poincare.L3.KernelIdentity
import ZInQKernel.Contrib.AbVarBC.Mul

/-! The printed kernel test characterizes connected scheme kernels of surjections. -/

noncomputable section

namespace ShimuraSteps.Quotient

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar R16Thm1
open ZInQ.Contrib.CloudR2Poincare
open ZInQ.Contrib.MilneQuasiInverse
open scoped CategoryTheory.MonObj

attribute [local instance] Kernel.kernelGroup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 600000

local notation "OverQ" => Over (Spec (CommRingCat.of ℚ))

variable {J Q A : AbVar ℚ}

private theorem componentModel_kernel (ν : AbVar.Hom J A) :
    IsPullback (L3.kerι ν.hom) (toUnit _) ν.hom η[A.X] := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of ℚ)))
  change IsPullback (pullback.fst ν.hom.left (η[A.X]).left)
    (pullback.fst ν.hom.left (η[A.X]).left ≫ J.X.hom) ν.hom.left (η[A.X]).left
  rw [← L3.ker_snd_eq (A := J) (B := A) ν.hom]
  exact IsPullback.of_hasPullback _ _

private theorem openImmersion_of_closed_and_open_range {X Y : Scheme} (f : X ⟶ Y)
    [IsClosedImmersion f] [IsReduced Y] (hf : IsOpen (Set.range f)) : IsOpenImmersion f := by
  let U : Y.Opens := ⟨Set.range f, hf⟩
  let a := IsOpenImmersion.lift U.ι f (by rw [Scheme.Opens.range_ι]; exact fun _ h => h)
  have ha : a ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (a ≫ U.ι) := by rw [ha]; infer_instance
  haveI : IsClosedImmersion a := IsClosedImmersion.of_comp a U.ι
  haveI : Surjective a := ⟨fun y => by
    obtain ⟨x, hx⟩ : U.ι y ∈ Set.range f := y.2
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ha, hx]⟩
  haveI : IsIso a := isIso_of_isClosedImmersion_of_surjective _
  rw [← ha]
  infer_instance

/-- The unit of the residual kernel is open because its inverse image
under the proper surjection on kernels is the open identity component. -/
private theorem residual_unit_open (ν : AbVar.Hom J A)
    (q : AbVar.Hom J Q) (ψ : AbVar.Hom Q A)
    (hq : IsAbVarQuotient (L3.covHom ν.hom) q) (hfac : q.hom ≫ ψ.hom = ν.hom) :
    IsOpenImmersion (η[Kernel.kernelObject ψ.hom]).left := by
  let K := Kernel.kernelObject ψ.hom
  let k₀ := Kernel.kernelInclusion ψ.hom
  let j₀ := L3.kerι ν.hom
  let j := L3.jK ν.hom
  let k : L3.kerOver ν.hom ⟶ K := (Kernel.kernelPointsEquiv ψ.hom _).symm
    ⟨j₀ ≫ q.hom, by
      change (j₀ ≫ q.hom) ≫ ψ.hom = 1
      rw [Category.assoc, hfac]
      exact L3.kerι_comp _⟩
  have hk : k ≫ k₀ = j₀ ≫ q.hom := pullback.lift_fst _ _ _
  have hbot : IsPullback j₀ k q.hom k₀ := by
    apply IsPullback.of_bot ?_ hk.symm (IsPullback.of_hasPullback ψ.hom η[A.X])
    have hu : k ≫ pullback.snd ψ.hom η[A.X] = toUnit _ := toUnit_unique _ _
    rw [hu, hfac]
    exact componentModel_kernel ν
  have htop : IsPullback j (toUnit _) k η[K] := by
    apply IsPullback.flip
    refine IsPullback.of_bot ?_ ?_ hbot.flip
    · rw [IsMonHom.one_hom]
      exact hq.kernel.flip
    · apply (cancel_mono k₀).mp
      rw [Category.assoc, Category.assoc, IsMonHom.one_hom, hk]
      exact hq.kernel.w.symm
  have hbot' : IsPullback j₀.left k.left q.hom.left k₀.left :=
    (Over.forget _).map_isPullback hbot
  haveI : Surjective k.left := MorphismProperty.of_isPullback (P := @Surjective) hbot' hq.surjective
  haveI : IsProper q.hom.left := L4.isProper_over_hom _
  haveI : IsProper k.left :=
    MorphismProperty.of_isPullback (P := @IsProper) hbot' (inferInstance : IsProper q.hom.left)
  have htop' : IsPullback j.left (toUnit (L3.covOver ν.hom)).left k.left (η[K]).left :=
    (Over.forget _).map_isPullback htop
  have hrange : Set.range j.left = k.left ⁻¹' Set.range (η[K]).left := by
    simpa only [Set.preimage_univ, Set.image_univ] using
      Scheme.image_preimage_eq_of_isPullback htop'.flip Set.univ
  have hopen : IsOpen (k.left ⁻¹' Set.range (η[K]).left) := by
    rw [← hrange]
    exact IsOpenImmersion.isOpen_range (L3.U0 ν.hom).ι
  have hqmap := k.left.isClosedMap.isQuotientMap k.left.continuous k.left.surjective
  haveI : IsClosedImmersion k₀.left := kernelInclusion_closed ψ
  haveI : IsProper K.hom := by
    rw [← Over.w k₀]
    infer_instance
  haveI : Smooth K.hom := ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof ℚ K inferInstance
  haveI : IsReduced K.left := CurveSplit.isReduced_of_smooth K.hom
  haveI := unit_closed K
  exact openImmersion_of_closed_and_open_range (η[K]).left
    (hqmap.isCoinducing.isOpen_preimage.mp hopen)

/-- An open kernel unit makes the homomorphism formally unramified: the diagonal
is its pullback under the difference map on the kernel pair. -/
private theorem finite_of_open_kernel_unit (f : AbVar.Hom Q A)
    (he : IsOpenImmersion (η[Kernel.kernelObject f.hom]).left) : IsFinite f.hom.left := by
  let F := f.hom
  let K := Kernel.kernelObject F
  let j := Kernel.kernelInclusion F
  let P := pullback F F
  let δ := pullback.diagonal F
  let a := pullback.fst F F
  let b := pullback.snd F F
  let d : P ⟶ K := (Kernel.kernelPointsEquiv F P).symm
    ⟨a * b⁻¹, by
      change (a * b⁻¹) ≫ F = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp]
      exact mul_inv_eq_one.mpr pullback.condition⟩
  have hd (T : OverQ) (u : T ⟶ P) : u ≫ d ≫ j = (u ≫ a) * (u ≫ b)⁻¹ := by
    have hh : d ≫ j = a * b⁻¹ := pullback.lift_fst _ _ _
    rw [hh, MonObj.comp_mul, GrpObj.comp_inv]
  have hd₀ : δ ≫ d = toUnit _ ≫ η[K] := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hd, show δ ≫ a = 𝟙 _ from pullback.diagonal_fst F,
      show δ ≫ b = 𝟙 _ from pullback.diagonal_snd F, mul_inv_cancel,
      Category.assoc, IsMonHom.one_hom, Hom.one_def]
  have hdiag : IsPullback δ (toUnit _) d η[K] := by
    refine IsPullback.mk' hd₀ ?_ ?_
    · intro T x y h _
      have hh := congrArg (· ≫ a) h
      simpa [δ, a] using hh
    · intro T u v huv
      have hh : (u ≫ a) * (u ≫ b)⁻¹ = 1 := by
        rw [← hd, ← Category.assoc, huv, Category.assoc, IsMonHom.one_hom,
          show v = toUnit _ from toUnit_unique _ _]
        rfl
      have hab := mul_inv_eq_one.mp hh
      refine ⟨u ≫ a, ?_, toUnit_unique _ _⟩
      apply pullback.hom_ext
      · simp [δ, a]
      · simpa [δ, b] using hab
  have hd' : IsOpenImmersion δ.left := MorphismProperty.of_isPullback
    (P := @IsOpenImmersion) ((Over.forget _).map_isPullback hdiag.flip) he
  let e := PreservesPullback.iso (Over.forget (Spec (CommRingCat.of ℚ))) F F
  have hδ : pullback.diagonal F.left = δ.left ≫ e.hom := by
    apply pullback.hom_ext
    · rw [pullback.diagonal_fst, Category.assoc]
      erw [PreservesPullback.iso_hom_fst]
      change 𝟙 _ = (δ ≫ a).left
      rw [show δ ≫ a = 𝟙 _ from pullback.diagonal_fst F]
      rfl
    · rw [pullback.diagonal_snd, Category.assoc]
      erw [PreservesPullback.iso_hom_snd]
      change 𝟙 _ = (δ ≫ b).left
      rw [show δ ≫ b = 𝟙 _ from pullback.diagonal_snd F]
      rfl
  haveI : IsOpenImmersion (pullback.diagonal F.left) := by rw [hδ]; infer_instance
  haveI : IsProper F.left := L4.isProper_over_hom _
  haveI : LocallyQuasiFinite F.left :=
    ZInQ.Contrib.AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- A surjective map satisfying the printed factorization test has connected
scheme-theoretic kernel. Surjectivity is the separate printed hypothesis. -/
theorem schemeKernelConnected_of_kerConnected (ν : AbVar.Hom J A)
    (hν : Surjective ν.hom.left) (hc : KerConnected ν) : SchemeKernelConnected ν := by
  let C := L3.covAbVar ν.hom
  let i : AbVar.Hom C J := L3.covHom ν.hom
  obtain ⟨Q, q, hq⟩ := abVarQuotientBySubvarietyExists J C i (L3.covHom_closed ν.hom)
  obtain ⟨ψ, hψ, _⟩ := hq.lift_unique A ν (L3.covHom_killed ν.hom)
  haveI : Surjective (q.hom.left ≫ ψ.hom.left) := by
    change Surjective (q.hom ≫ ψ.hom).left
    rwa [hψ]
  have hψsurj := Surjective.of_comp q.hom.left ψ.hom.left
  have hψfin := finite_of_open_kernel_unit ψ (residual_unit_open ν q ψ hq hψ)
  haveI : IsIso ψ.hom := hc Q q ψ hq.surjective ⟨hψfin, hψsurj⟩ hψ
  have hker : IsPullback i.hom (toUnit C.X) ν.hom η[A.X] := by
    have hright : IsPullback η[Q.X] (𝟙 _) ψ.hom η[A.X] :=
      IsPullback.of_vert_isIso ⟨by rw [IsMonHom.one_hom, Category.id_comp]⟩
    have hp := hq.kernel.paste_vert hright
    rw [hψ, Category.comp_id] at hp
    exact hp
  haveI : GeometricallyIntegral C.X.hom := C.geomInt
  have : IsIntegral C.X.left := GeometricallyIntegral.isIntegral_of_subsingleton C.X.hom
  let e := (Over.forget (Spec (CommRingCat.of ℚ))).mapIso hker.isoPullback
  let eh : C.X.left ≃ₜ (Kernel.kernelObject ν.hom).left := e.hom.homeomorph
  exact eh.surjective.connectedSpace eh.continuous

/-- For a surjective homomorphism the printed test and connectedness of the
scheme-theoretic kernel are equivalent. -/
theorem kerConnected_iff_schemeKernelConnected (ν : AbVar.Hom J A)
    (hν : Surjective ν.hom.left) : KerConnected ν ↔ SchemeKernelConnected ν :=
  ⟨schemeKernelConnected_of_kerConnected ν hν, kerConnected_of_schemeKernelConnected⟩

end ShimuraSteps.Quotient

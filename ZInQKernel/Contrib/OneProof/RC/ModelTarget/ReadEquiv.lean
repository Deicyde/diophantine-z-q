import ZInQKernel.Contrib.OneProof.RC.ModelTarget.Read

/-! The residue reading of the good cubic is a multiplicative bijection onto the points of
the reduced equation over `K`, and it commutes with the arithmetic Frobenius
(tex 8477–8492). On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open WeierstrassCurve WeierstrassCurve.ModelTorsion
open scoped WeierstrassCurve CategoryTheory.Obj WeierstrassCurve.Projective

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

open PMQuotient (residueSource residueFrob)
open PMGeometry (ReducedEquation)

variable {ell : ℕ} [Fact ell.Prime] {W₀ : WeierstrassCurve ℤ}
  {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]

theorem resUp_structure (y : residueSource ell K ⟶ (special ell).obj (detE ell W₀)) :
    (y.left ≫ pullback.fst _ _) ≫ projStructure (detW ell W₀) =
      Spec.map (CommRingCat.ofHom (resRing ell K)) := by
  rw [← resUp_left]
  exact Over.w (resUp y)

theorem readFun_eq (y : residueSource ell K ⟶ (special ell).obj (detE ell W₀))
    (v : Fin 3 → K) (hv : ((detW ell W₀).toProjective.map (resRing ell K)).Equation v) (i : Fin 3)
    (hi : IsUnit (v i)) (h : y.left ≫ pullback.fst _ _ = chartMorphism (detW ell W₀) (resRing ell K) v hv i hi) :
    readFun y = Projective.Point.toAffine ((ReducedEquation W₀ ell)⁄K).toProjective v := by
  have h1 : val (detW ell W₀) (resUp y) =
      Projective.Point.toAffine ((detW ell W₀).toProjective.map (resRing ell K)) v := by
    unfold val
    exact (fieldValue_congr (detW ell W₀) _ (resUp_left y) _ (resUp_structure y)).trans
      (fieldValue_eq (detW ell W₀) _ _ _ v hv i hi h)
  rw [readFun, h1]
  exact pointCongr_toAffine _ v

theorem readFun_injective (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    Function.Injective (readFun (ell := ell) (W₀ := W₀) (K := K)) := by
  intro y z h
  have := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  have h' := (pointCongr (resRing_curve ell W₀ K)).injective h
  have hl := fieldValue_injective (detW ell W₀) (resRing ell K) _ _ (Over.w (resUp y))
    (Over.w (resUp z)) h'
  rw [resUp_left, resUp_left] at hl
  apply Over.OverMorphism.ext
  apply pullback.hom_ext hl
  exact (Over.w y).trans (Over.w z).symm

theorem readFun_surjective :
    Function.Surjective (readFun (ell := ell) (W₀ := W₀) (K := K)) := by
  intro P
  obtain ⟨v, hv, i, hi, hval⟩ : ∃ (v : Fin 3 → K)
      (hv : ((detW ell W₀).toProjective.map (resRing ell K)).Equation v) (i : Fin 3) (hi : IsUnit (v i)),
      Projective.Point.toAffine ((ReducedEquation W₀ ell)⁄K).toProjective v = P := by
    rcases P with _ | ⟨x, y, h⟩
    · exact ⟨![0, 1, 0], Projective.equation_zero, 1, isUnit_one, Projective.Point.toAffine_zero⟩
    · have h' : ((ReducedEquation W₀ ell)⁄K).toProjective.Nonsingular ![x, y, 1] :=
        (Projective.nonsingular_some _ _).mpr h
      have he : ((detW ell W₀).toProjective.map (resRing ell K)).Equation ![x, y, 1] := by
        have := h'.1
        rw [← resRing_curve ell W₀ K] at this
        exact this
      exact ⟨![x, y, 1], he, 2, isUnit_one, Projective.Point.toAffine_some h'⟩
  let p := chartMorphism (detW ell W₀) (resRing ell K) v hv i hi
  have hp : p ≫ (detE ell W₀).hom =
      (residueSource ell K).hom ≫ Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)) := by
    change p ≫ projStructure (detW ell W₀) = _
    rw [chartMorphism_structure, residue_structure]
  let y : residueSource ell K ⟶ (special ell).obj (detE ell W₀) :=
    Over.homMk (pullback.lift p (residueSource ell K).hom hp) (pullback.lift_snd _ _ _)
  refine ⟨y, ?_⟩
  rw [readFun_eq y v hv i hi (pullback.lift_fst _ _ _), hval]

variable (ell W₀ K)

/-- **The residue reading** `read` of `PMWire.GoodRow` for the good cubic: the residue
points of the special fibre, with the group law induced from the cubic, are the points of
the reduced equation over `K`. -/
def read (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    letI := weierstrassModelGrp ell h₅ W₀ hΔ
    (residueSource ell K ⟶ (special ell).obj (detE ell W₀)) ≃*
      Multiplicative ((ReducedEquation W₀ ell)⁄K).toAffine.Point :=
  letI := weierstrassModelGrp ell h₅ W₀ hΔ
  MulEquiv.ofBijective
    (MonoidHom.mk' (fun y => Multiplicative.ofAdd (readFun y)) (fun y z => by
      rw [readFun_mul h₅ hΔ]
      rfl))
    (show Function.Bijective _ from ⟨fun y z h => readFun_injective hΔ (Multiplicative.ofAdd.injective h),
      fun P => by
        obtain ⟨y, hy⟩ := readFun_surjective (Multiplicative.toAdd P)
        exact ⟨y, by
          show Multiplicative.ofAdd (readFun y) = P
          rw [hy]
          rfl⟩⟩)

theorem read_apply (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ)
    (y : residueSource ell K ⟶ (special ell).obj (detE ell W₀)) :
    (read ell W₀ K h₅ hΔ y).toAdd = readFun y := by
  let _ := weierstrassModelGrp ell h₅ W₀ hΔ
  rfl

/-- **Frobenius compatibility of the residue reading** (`read_frob` of `PMWire.GoodRow`). -/
theorem read_frob (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ)
    (y : residueSource ell K ⟶ (special ell).obj (detE ell W₀)) :
    (read ell W₀ K h₅ hΔ (residueFrob ell K ≫ y)).toAdd =
      Stages.curveFrob (K := K) (ReducedEquation W₀ ell) (read ell W₀ K h₅ hΔ y).toAdd := by
  rw [read_apply, read_apply]
  let σ := FiniteField.frobeniusAlgHom (ZMod ell) K
  obtain ⟨v, hv, i, hi, e⟩ := exists_chartMorphism (detW ell W₀) (resRing ell K) _ (resUp_structure y)
  have hσ : (σ : K →+* K).comp (resRing ell K) = resRing ell K := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, resRing]
    exact σ.commutes _
  have hv' : ((detW ell W₀).toProjective.map (resRing ell K)).Equation ((σ : K →+* K) ∘ v) := by
    have := equation_map (detW ell W₀) (resRing ell K) (σ : K →+* K) v hv
    rw [hσ] at this
    exact this
  have hfrob : (residueFrob ell K ≫ y).left ≫ pullback.fst _ _ =
      chartMorphism (detW ell W₀) (resRing ell K) ((σ : K →+* K) ∘ v) hv' i (hi.map _) := by
    have hl : (residueFrob ell K ≫ y).left =
        Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫ y.left := rfl
    rw [hl, Category.assoc, e]
    exact (chartMorphism_map (detW ell W₀) (resRing ell K) (σ : K →+* K) v hv i hi
      (by rw [hσ]; exact hv')).trans (chartMorphism_ring_congr _ hσ _ _ _ _ _)
  rw [readFun_eq _ _ hv' i _ hfrob, readFun_eq y v hv i hi e, Stages.curveFrob,
    map_toAffine]
  rfl

#print axioms readFun_injective
#print axioms readFun_surjective
#print axioms read
#print axioms read_frob

end ZInQ.Manuscript.RC.ModelTarget

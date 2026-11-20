import ZInQKernel.Contrib.OneProof.RC.J0Cusps.AffineLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelSource
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.AffineNeighborhood

/-! Uniqueness of the limit of a modular chart on the normalization.
On the spot (c), tex 1785–1787 and 2937–2939. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits PkgI3

namespace ZInQ.Manuscript.RC.J0Cusps

private theorem evaluation_eq_sectionMap {X : Over (Spec (.of ℂ))}
    (p : Point ℂ X) (U : X.left.Opens) (hp : p.underlying ∈ U) (r : Γ(X.left, U)) :
    Point.evaluate U r p = sectionEval p.left U
      (ge_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem p.left hp)) r := by
  rw [Point.evaluate, dite_eq_left hp]
  let f : Spec (.of ℂ) ⟶ X.left := p.left
  have hc : f (IsLocalRing.closedPoint ℂ) ∈ U := hp
  change Scheme.stalkClosedPointTo f (X.left.presheaf.germ U _ hc r) = _
  have hh : X.left.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo f =
      sectionEval f U (ge_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem f hc)) := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, sectionEval,
      Scheme.Hom.appLE, Category.assoc]
    rfl
  exact congrArg (fun v : Γ(X.left, U) ⟶ CommRingCat.of ℂ => v r) hh

/-- If any pair of complex points is contained in one affine open, regular
functions on that affine open separate them in the complex topology. -/
theorem t2_of_affine_pair (X : Over (Spec (.of ℂ)))
    (h : ∀ x y : Point ℂ X, ∃ U : X.left.affineOpens, x.underlying ∈ U.1 ∧ y.underlying ∈ U.1) :
    T2Space (Point ℂ X) := by
  classical
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨U, hx, hy⟩ := h x y
  have hn : ∃ r : Γ(X.left, U.1), Point.evaluate U.1 r x ≠ Point.evaluate U.1 r y := by
    by_contra! he
    apply hxy
    apply Over.OverMorphism.ext
    have hx' : ⊤ ≤ x.left ⁻¹ᵁ U.1 :=
      ge_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem x.left hx)
    have hy' : ⊤ ≤ y.left ⁻¹ᵁ U.1 :=
      ge_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem y.left hy)
    have hh : sectionEval x.left U.1 hx' = sectionEval y.left U.1 hy' :=
      CommRingCat.hom_ext (RingHom.ext fun r => by
        simpa only [evaluation_eq_sectionMap x U.1 hx, evaluation_eq_sectionMap y U.1 hy]
          using he r)
    rw [← sectionMap_factor x.left U.2 hx', ← sectionMap_factor y.left U.2 hy', hh]
  obtain ⟨r, hr⟩ := hn
  obtain ⟨S, T, hS, hT, hxS, hyT, hd⟩ := t2_separation hr
  refine ⟨Point.overOpen U.1 ∩ Point.evaluate U.1 r ⁻¹' S,
    Point.overOpen U.1 ∩ Point.evaluate U.1 r ⁻¹' T,
    Point.isOpen_overOpen_inter_preimage U.1 r S hS,
    Point.isOpen_overOpen_inter_preimage U.1 r T hT, ⟨hx, hxS⟩, ⟨hy, hyT⟩, ?_⟩
  exact Set.disjoint_left.mpr fun z hz hz' => Set.disjoint_left.mp hd hz.2 hz'.2

/-- The topology on the normalized modular curve's complex points is Hausdorff. -/
theorem source_t2 (N : ℕ) [NeZero N] : T2Space (Point ℂ (complexBaseChange.obj (source N))) := by
  classical
  let X := source N
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
  let k : (complexBaseChange.obj X).left ⟶ X.left := pullback.fst X.hom f
  have hf : IsAffineHom f := inferInstance
  let : IsAffineHom k := isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback X.hom f).flip hf
  let : IsIntegral X.left := X0Model.integral N
  let : IsProper X.hom := X0Model.proper N
  let : SmoothOfRelativeDimension 1 X.hom := model_smooth_one N
  apply t2_of_affine_pair
  intro x y
  obtain ⟨U, hU⟩ := exists_affineOpens_forall_mem_of_smooth_integral_curve X.hom
    {k x.underlying, k y.underlying}
  refine ⟨⟨k ⁻¹ᵁ U.1, U.2.preimage k⟩, ?_, ?_⟩
  · exact hU _ (by simp)
  · exact hU _ (by simp)

private theorem complexLift_injective (X : Over (Spec (.of ℚ))) :
    Function.Injective (complexLift (X := X)) := by
  intro p q h
  apply Over.OverMorphism.ext
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
  have eval (a : AbVar.ptObj (K := ℚ) ℂ ⟶ X) :
      (complexLift a).left ≫ pullback.fst X.hom f = a.left :=
    pullback.lift_fst _ _ _
  exact (eval p).symm.trans ((congrArg (fun z : Point ℂ (complexBaseChange.obj X) =>
    z.left ≫ pullback.fst X.hom f) h).trans (eval q))

/-- A complex source limit determines its point over the rationals with
complex coordinates. -/
theorem source_limit_unique (N : ℕ) [NeZero N] {I : Type} {F : Filter I} [F.NeBot]
    {x : I → Point ℂ (complexBaseChange.obj (source N))}
    {p q : AbVar.ptObj (K := ℚ) ℂ ⟶ source N}
    (hp : Filter.Tendsto x F (nhds (complexLift p)))
    (hq : Filter.Tendsto x F (nhds (complexLift q))) : p = q := by
  let := source_t2 N
  exact complexLift_injective _ (tendsto_nhds_unique hp hq)


end ZInQ.Manuscript.RC.J0Cusps

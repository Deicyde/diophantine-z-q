import ZInQKernel.Contrib.CloudB3W17bOkaComparison.IntrinsicOpenValues

/-!
# Continuity of actual intrinsic analytic residue values

The local-lift argument follows Oka's AnalyticSpace/Continuity.lean, upstream
9a9fc315498d58484ac1abc9668548212eb7c1ff (Apache-2.0; authors Yuichiro Hoshi,
Junnosuke Koizumi, Christian Merten). This bridge uses the independently proved
actual germ-colimit residue evaluation instead of the Taylor/Weierstrass example
cone. Only actual local-model stalk surjections, constants, germs and holomorphic
representatives are used. No compatibility/GAGA or reducedness premise.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic IsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

lemma intrinsic_germ_restrict_maximalIdeal_iff {n : ℕ}
    (V : Opens (_root_.complexAffineSpace.{0} n))
    {A : Opens ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding)}
    {y : (_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding} (hy : y ∈ A)
    (s : ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.obj (op A)) :
    ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ A y hy s ∈
        maximalIdeal (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.stalk y) ↔
      OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj A) ⟨y, hy, rfl⟩ s = 0 :=
  (intrinsicStalkCoefficients (euclideanOpen n V) y).evalHom_eq_zero_iff.symm.trans
    (Iff.of_eq (congrArg (fun c : ℂ => c = 0) (intrinsicEval_open_germ n V y A hy s)))

/-- Actual chart stalk maps transport literal holomorphic representative values to the original analytic stalk. -/
theorem intrinsicEvalStalk_chart
    {Z : AnalyticSpace.{0}} {U₀ : Opens Z} {n : ℕ} {V : Opens (_root_.complexAffineSpace.{0} n)}
    {i : Z.toLocallyRingedSpace.restrict U₀.isOpenEmbedding ⟶
      (_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding}
    (hlin : IsCLinearHom i (Z.toLocallyRingedSpace.resAlgMap Z.algebraMap U₀)
      (constantsAlgMap n V))
    (w : Z.toLocallyRingedSpace.restrict U₀.isOpenEmbedding)
    {A : Opens ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding)} (hA : i.base w ∈ A)
    (s : ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.obj (op A)) :
    intrinsicStalkEval Z w.1
      ((Z.toLocallyRingedSpace.restrictStalkIso U₀.isOpenEmbedding w).hom
        ((i.stalkMap w).hom
          (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ A
            (i.base w) hA s))) =
      OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj A) ⟨i.base w, hA, rfl⟩ s := by
  set e := Z.toLocallyRingedSpace.restrictStalkIso U₀.isOpenEmbedding w
  set c := OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj A) ⟨i.base w, hA, rfl⟩ s
  set cst : ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.obj (op A) :=
    ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.map (homOfLE le_top).op
      (constantsAlgMap n V c) with hcst
  have hc : e.hom ((i.stalkMap w).hom
      (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ A
        (i.base w) hA cst)) = Z.toLocallyRingedSpace.stalkAlgMap Z.algebraMap w.1 c := by
    rw [hcst, ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ_res_apply
      (homOfLE le_top) (i.base w) hA (constantsAlgMap n V c),
      show ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ ⊤
        (i.base w) trivial (constantsAlgMap n V c) =
        ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).stalkAlgMap
          (constantsAlgMap n V) (i.base w) c from rfl, hlin.stalkAlgMap w c]
    exact LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap _ Z.algebraMap U₀ w c
  have hm : ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ A
      (i.base w) hA (s - cst) ∈
        maximalIdeal (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.stalk (i.base w)) := by
    rw [intrinsic_germ_restrict_maximalIdeal_iff V]
    refine (map_sub _ s cst).trans (sub_eq_zero.mpr ?_)
    rw [hcst]
    exact ((OkaRing.evalHom_restrict _ _ _).trans (OkaRing.evalHom_algebraMap _ c)).symm
  have hs : e.hom ((i.stalkMap w).hom
      (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ A (i.base w) hA s)) -
      e.hom ((i.stalkMap w).hom
        (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ A (i.base w) hA cst)) =
    e.hom ((i.stalkMap w).hom
      (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ A (i.base w) hA (s - cst))) := by
    simp only [map_sub]
  rw [intrinsicStalkEval_eq_iff, ← hc, mem_maximalIdeal, mem_nonunits_iff]
  rw [mem_maximalIdeal, mem_nonunits_iff] at hm
  exact fun hu => hm ((i.prop w).map_nonunit _
    ((isUnit_map_iff e.commRingCatIsoToRingEquiv _).mp ((congrArg IsUnit hs).mp hu)))

/-- Real analytic local-model charts prove continuity of actual section residue values. -/
theorem intrinsic_continuousAt_eval (Z : AnalyticSpace.{0}) {U : Opens Z}
    (g : Z.presheaf.obj (op U)) (z₀ : U) :
    ContinuousAt (fun z : U => intrinsicEval Z z.1 z.2 g) z₀ := by
  obtain ⟨U₀, n, k, V, i, f, hcut, hlin⟩ := Z.local_model z₀.1
  set B : Opens (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) :=
    ⟨Subtype.val ⁻¹' (U : Set Z), U.2.preimage continuous_subtype_val⟩
  have hBU : U₀.1.isOpenEmbedding.isOpenMap.functor.obj B ≤ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hx
  set t : (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.obj (op B) :=
    Z.presheaf.map (homOfLE hBU).op g
  obtain ⟨A, hA, s, B', hB'B, hB'A, hx₀B', hres⟩ :=
    LocallyRingedSpace.exists_localLift i hcut.surjective_stalkMap t ⟨z₀.1, U₀.2⟩ z₀.2
  set W : Opens Z := U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'
  have hWU₀ : ∀ z ∈ W, z ∈ U₀.1 := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have hWU : W ≤ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hBU ⟨x, hB'B hx, rfl⟩
  have hval : ∀ (x : Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) (hx : x ∈ B'),
      intrinsicEval Z x.1 (hWU ⟨x, hx, rfl⟩) g =
        OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj A)
          ⟨i.base x, hB'A hx, rfl⟩ s := by
    intro x hx
    have h₂ : (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ
        ((Opens.map i.base).obj A) x (hB'A hx) (i.c.app (op A) s) =
      (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ B x (hB'B hx) t := by
      exact ((Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ_res_apply
          (homOfLE hB'A) x hx (i.c.app (op A) s)).symm.trans
        ((congrArg (fun a => (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ B' x hx a)
          hres).trans ((Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ_res_apply
            (homOfLE hB'B) x hx t))
    have h₁ : Z.presheaf.germ U x.1 (hWU ⟨x, hx, rfl⟩) g =
      (Z.toLocallyRingedSpace.restrictStalkIso U₀.1.isOpenEmbedding x).hom
        ((i.stalkMap x).hom
          (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).presheaf.germ A
            (i.base x) (hB'A hx) s)) :=
      (((congrArg (fun a => (Z.toLocallyRingedSpace.restrictStalkIso U₀.1.isOpenEmbedding x).hom a)
          ((LocallyRingedSpace.stalkMap_germ_apply i A x (hB'A hx) s).trans h₂)).trans
        (LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply Z.toLocallyRingedSpace
          U₀.1.isOpenEmbedding B x (hB'B hx) t)).trans
        (Z.presheaf.germ_res_apply (homOfLE hBU) x.1 ⟨x, hB'B hx, rfl⟩ g)).symm
    change intrinsicStalkEval Z x.1 (Z.presheaf.germ U x.1 _ g) = _
    rw [h₁]
    exact intrinsicEvalStalk_chart hlin x (hB'A hx) s
  have hmemB' : ∀ (z : Z) (hz : z ∈ W),
      (⟨z, hWU₀ z hz⟩ : Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) ∈ B' := by
    rintro _ ⟨y, hy, rfl⟩; exact hy
  set S : Set U := {z : U | (z : Z) ∈ W}
  have hS : IsOpen S := W.2.preimage continuous_subtype_val
  have hzS : z₀ ∈ S := ⟨⟨z₀.1, U₀.2⟩, hx₀B', rfl⟩
  refine ContinuousOn.continuousAt ?_ (hS.mem_nhds hzS)
  rw [continuousOn_iff_continuous_restrict]
  have hq : Continuous fun z : S =>
      ((i.base ⟨z.1.1, hWU₀ _ z.2⟩ :
        (_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).1 : ULift.{0} (Fin n) → ℂ) :=
    continuous_subtype_val.comp (i.base.hom.continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _))
  have hmaps : ∀ z : S,
      ((i.base ⟨z.1.1, hWU₀ _ z.2⟩ :
        (_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).1 : ULift.{0} (Fin n) → ℂ) ∈
      V.isOpenEmbedding.isOpenMap.functor.obj A :=
    fun z => ⟨i.base ⟨z.1.1, hWU₀ _ z.2⟩, hB'A (hmemB' _ z.2), rfl⟩
  have heq : (S.domRestrict fun z : U => intrinsicEval Z z.1 z.2 g) =
      (fun y : V.isOpenEmbedding.isOpenMap.functor.obj A => OkaRing.evalHom y.2 s) ∘
        fun z : S => (⟨_, hmaps z⟩ : V.isOpenEmbedding.isOpenMap.functor.obj A) :=
    funext fun z => hval _ (hmemB' _ z.2)
  rw [heq]
  exact (OkaRing.continuous_evalHom s).comp (hq.subtype_mk hmaps)

/-- Actual analytic section values are continuous on their true open domain. -/
theorem intrinsic_continuous_eval (Z : AnalyticSpace.{0}) {U : Opens Z}
    (g : Z.presheaf.obj (op U)) : Continuous fun z : U => intrinsicEval Z z.1 z.2 g :=
  continuous_iff_continuousAt.mpr (intrinsic_continuousAt_eval Z g)

/-- A real global analytic section has continuous actual residue values. -/
theorem intrinsic_continuous_eval_top (Z : AnalyticSpace.{0}) (g : Z.presheaf.obj (op ⊤)) :
    Continuous fun z : Z => intrinsicEval Z (U := ⊤) z trivial g := by
  have h : Continuous fun z : (⊤ : Opens Z) => intrinsicEval Z z.1 z.2 g := intrinsic_continuous_eval Z g
  have hc : Continuous fun z : Z => (⟨z, trivial⟩ : (⊤ : Opens Z)) := continuous_induced_rng.mpr continuous_id
  exact (h.comp hc).congr fun _ => rfl

end ZInQ.Contrib.CloudB3W17bOkaComparison

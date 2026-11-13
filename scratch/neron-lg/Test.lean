import ZInQKernel.HDecomp.Faltings.H5BaseChange
open CategoryTheory AlgebraicGeometry Limits

theorem pbCompInv_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (ZInQ.H5Neron.pbCompInv f g G).left ≫ pullback.fst G.hom (f ≫ g) =
      pullback.fst (pullback.snd G.hom g) f ≫ pullback.fst G.hom g := by
  have h := conjugateEquiv_counit ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom G
  have h2 := congrArg CommaMorphism.left h
  simp only [Over.map_map_left, Over.mapPullbackAdj_counit_app, Adjunction.comp_counit_app] at h2
  simpa [ZInQ.H5Neron.pbCompInv, Over.pullbackComp, conjugateIsoEquiv, Over.mapComp] using h2

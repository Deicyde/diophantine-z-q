/-! ## period-glue: `BaseChangeClassUnique` proved

Task period-glue, 2026-11-13. `PeriodMapH.BaseChangeClassUnique` (period-map's
`part_heavy.lean`, unchanged) is proved outright (`baseChangeClassUnique_proof`): the two pullback
squares give a unique isomorphism `e : Q.A ≅ Q'.A` over `Spec ℂ` compatible with the maps to
`P.A`; uniqueness of maps into a pullback makes it commute with `ι(a)` and carry `η(a)` to `η'(a)`;
at `a = 0` it carries the identity section to the identity section, so it and its inverse are
homomorphisms by rigidity (mul-rigidity's `MulRigidity.isMonHom_of_geometricallyIntegral`,
copied verbatim above). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlueH

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

/-- **Rigidity for the abelian varieties of this file (proved, mul-rigidity).** -/
theorem isMonHom_of_pointed {K : Type} [Field K] (A B : PkgI3.AbVar K) (h : A.X ⟶ B.X)
    (h0 : η[A.X] ≫ h = η[B.X]) : IsMonHom h :=
  MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X h h0

/-- The structure map of the point object `Spec K → Spec K` is the identity. -/
theorem toUnit_ptObj_left (K : Type) [Field K] :
    (toUnit (PkgI3.AbVar.ptObj (K := K) K)).left = 𝟙 _ := by
  have h := Over.w (toUnit (PkgI3.AbVar.ptObj (K := K) K))
  have h2 : (PkgI3.AbVar.ptObj (K := K) K).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rw [h2] at h
  exact (Category.comp_id _).symm.trans h

/-- **`BaseChangeClassUnique` holds (proved).** -/
theorem baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique := by
  intro ιe P Q Q' ⟨g, hpb, hι, hη⟩ ⟨g', hpb', hι', hη'⟩
  set e := hpb.isoIsPullback _ _ hpb' with he
  have he1 : e.hom ≫ g' = g := hpb.isoIsPullback_hom_fst _ _ hpb'
  have he2 : e.hom ≫ Q'.A.X.hom = Q.A.X.hom := hpb.isoIsPullback_hom_snd _ _ hpb'
  have hext : ∀ {T : Scheme} (u v : T ⟶ Q'.A.X.left), u ≫ g' = v ≫ g' →
      u ≫ Q'.A.X.hom = v ≫ Q'.A.X.hom → u = v := fun u v h1 h2 => hpb'.hom_ext h1 h2
  let E : Q.A.X ⟶ Q'.A.X := Over.homMk e.hom he2
  let Ei : Q'.A.X ⟶ Q.A.X := Over.homMk e.inv (by rw [Iso.inv_comp_eq, he2])
  have hEEi : E ≫ Ei = 𝟙 _ := by ext; simp [E, Ei]
  have hEiE : Ei ≫ E = 𝟙 _ := by ext; simp [E, Ei]
  have hlev : ∀ a, Additive.toMul (Q.e.eta a) ≫ E = Additive.toMul (Q'.e.eta a) := by
    intro a
    apply Over.OverMorphism.ext
    apply hext
    · simp only [Over.comp_left, Over.homMk_left, Category.assoc, E, he1]
      rw [hη a, hη' a]
    · simp only [Over.comp_left, Over.homMk_left, Category.assoc, E, he2, Over.w]
  have h0 : η[Q.A.X] ≫ E = η[Q'.A.X] := by
    have h := congrArg CommaMorphism.left (hlev 0)
    simp only [map_zero, toMul_zero, Hom.one_def, Over.comp_left, Category.assoc,
      toUnit_ptObj_left] at h
    exact Over.OverMorphism.ext h
  have h0' : η[Q'.A.X] ≫ Ei = η[Q.A.X] := by
    rw [← h0, Category.assoc, hEEi, Category.comp_id]
  have hE : IsMonHom E := isMonHom_of_pointed Q.A Q'.A E h0
  have hEi : IsMonHom Ei := isMonHom_of_pointed Q'.A Q.A Ei h0'
  have hequiv : ∀ a, (Q.q.iota a).hom ≫ E = E ≫ (Q'.q.iota a).hom := by
    intro a
    apply Over.OverMorphism.ext
    apply hext
    · simp only [Over.comp_left, Over.homMk_left, Category.assoc, E, he1, hι' a]
      rw [hι a, ← Category.assoc, he1]
    · simp only [Over.comp_left, Over.homMk_left, Category.assoc, E, he2, Over.w]
  refine Quotient.sound ⟨{
    φ := PkgI3.AbVar.Hom.mk' E
    ψ := PkgI3.AbVar.Hom.mk' Ei
    left := by simpa using hEEi
    right := by simpa using hEiE
    equivariant := fun a => by simpa using hequiv a
    level := fun a => by
      rw [PkgI3.AbVar.Hom.hom_mk', hlev a, ofMul_toMul] }⟩

end HSyn.G0Split.FibreQM.PeriodGlueH

end

#print axioms HSyn.G0Split.FibreQM.PeriodGlueH.baseChangeClassUnique_proof

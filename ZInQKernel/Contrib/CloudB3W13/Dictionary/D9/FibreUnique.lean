/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D9.Rigidity

/-!
# Fibre uniqueness for kernel QM families (W13, dictionary lane D9)

Two kernel objects that are both fibres (`LeafQM.AV.IsFibreOf`) of the same family at the same
field point are isomorphic: the pullback isomorphism respects `ι` and the level points, and it is a
homomorphism of abelian varieties by rigidity (`isMonHom_of_comp_eq`, it preserves the identity
`η 0`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

section

variable {S : Scheme.{0}} (𝒜 : LeafQM.AV.QMFamily S) {K : Type} [Field K]
  {y : Spec (CommRingCat.of K) ⟶ S}

theorem fibre_point_eq {P P' : LeafQM.AV.QML3 K} {g : P.A.X.left ⟶ 𝒜.F.left}
    {g' : P'.A.X.left ⟶ 𝒜.F.left}
    (hpb : IsPullback g P.A.X.hom 𝒜.F.hom y) (hpb' : IsPullback g' P'.A.X.hom 𝒜.F.hom y)
    (hη : ∀ a : LeafQM.O, (Additive.toMul (P.e.eta a)).left ≫ g = y ≫ 𝒜.eta a)
    (hη' : ∀ a : LeafQM.O, (Additive.toMul (P'.e.eta a)).left ≫ g' = y ≫ 𝒜.eta a) (a : LeafQM.O) :
    (Additive.toMul (P.e.eta a)).left ≫ (hpb.isoIsPullback _ _ hpb').hom =
      (Additive.toMul (P'.e.eta a)).left := by
  apply hpb'.hom_ext
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst, hη, hη']
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd, Over.w, Over.w]

theorem fibre_iota_comm {P P' : LeafQM.AV.QML3 K} {g : P.A.X.left ⟶ 𝒜.F.left}
    {g' : P'.A.X.left ⟶ 𝒜.F.left}
    (hpb : IsPullback g P.A.X.hom 𝒜.F.hom y) (hpb' : IsPullback g' P'.A.X.hom 𝒜.F.hom y)
    (hι : ∀ a : LeafQM.O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a)
    (hι' : ∀ a : LeafQM.O, (P'.q.iota a).hom.left ≫ g' = g' ≫ 𝒜.iota a) (a : LeafQM.O) :
    (P.q.iota a).hom.left ≫ (hpb.isoIsPullback _ _ hpb').hom =
      (hpb.isoIsPullback _ _ hpb').hom ≫ (P'.q.iota a).hom.left := by
  apply hpb'.hom_ext
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst, hι, Category.assoc, hι',
      ← Category.assoc, IsPullback.isoIsPullback_hom_fst]
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd, Over.w, Category.assoc, Over.w,
      IsPullback.isoIsPullback_hom_snd]

end

theorem toUnit_ptObj_left (K : Type) [Field K] :
    (toUnit (PkgI3.AbVar.ptObj (K := K) K)).left = 𝟙 _ := by
  simp [PkgI3.AbVar.ptObj]

/-- **Fibre uniqueness.** Two kernel objects that are fibres of the same family at the same field
point are isomorphic. -/
theorem isFibreOf_unique {S : Scheme.{0}} (𝒜 : LeafQM.AV.QMFamily S) {K : Type} [Field K]
    {y : Spec (CommRingCat.of K) ⟶ S} {P P' : LeafQM.AV.QML3 K}
    (hP : LeafQM.AV.IsFibreOf 𝒜 y P) (hP' : LeafQM.AV.IsFibreOf 𝒜 y P') :
    Nonempty (LeafQM.AV.QML3.Iso P P') := by
  obtain ⟨g, hpb, hι, hη⟩ := hP
  obtain ⟨g', hpb', hι', hη'⟩ := hP'
  let e := hpb.isoIsPullback _ _ hpb'
  have hes : e.hom ≫ P'.A.X.hom = P.A.X.hom := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hes' : e.inv ≫ P.A.X.hom = P'.A.X.hom := by
    rw [← hes, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let φo : P.A.X ⟶ P'.A.X := Over.homMk e.hom hes
  let ψo : P'.A.X ⟶ P.A.X := Over.homMk e.inv hes'
  have hpt := fibre_point_eq 𝒜 hpb hpb' hη hη'
  have h0 : η[P.A.X] ≫ φo = η[P'.A.X] := by
    have h := hpt 0
    simp only [map_zero, toMul_zero, Hom.one_def, Over.comp_left, toUnit_ptObj_left] at h
    erw [Category.id_comp, Category.id_comp] at h
    ext1
    exact h
  have h0' : η[P'.A.X] ≫ ψo = η[P.A.X] := by
    rw [← h0, Category.assoc]
    convert Category.comp_id _
    ext1
    simp [φo, ψo, e]
  have : IsMonHom φo := isMonHom_of_comp_eq φo h0
  have : IsMonHom ψo := isMonHom_of_comp_eq ψo h0'
  refine ⟨⟨PkgI3.AbVar.Hom.mk' φo, PkgI3.AbVar.Hom.mk' ψo, ?_, ?_, ?_, ?_⟩⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk']; ext1; simp [φo, ψo, e]
  · simp only [PkgI3.AbVar.Hom.hom_mk']; ext1; simp [φo, ψo, e]
  · intro a
    simp only [PkgI3.AbVar.Hom.hom_mk']
    ext1
    simpa [φo, e] using fibre_iota_comm 𝒜 hpb hpb' hι hι' a
  · intro a
    simp only [PkgI3.AbVar.Hom.hom_mk']
    rw [← ofMul_toMul (P'.e.eta a)]
    congr 1
    ext1
    simpa [φo, e] using hpt a

end ZInQ.Contrib.CloudB2Shimura.Dictionary

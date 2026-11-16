/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.InterfaceD6D7

/-!
# D6, part 1: group-law transport between FLT relative group laws and kernel group objects

For relative group laws `G`, `G'` on `f : A ⟶ Spec K`, `f' : A' ⟶ Spec K` and a morphism
`φ : Over.mk f ⟶ Over.mk f'` over `Spec K`:

* `isMonHom_of_mulCompat`: if `φ` is compatible with the FLT multiplications on **all** test points
  (`mapPt φ.left (G.mul t P Q) = G'.mul t …` for every `T`, `t : T ⟶ Spec K`), then `φ` is a monoid
  morphism for the group objects `G.grpObjOverMk`, `G'.grpObjOverMk` (the ones used by
  `Dictionary.abVarOfFakeEC`);
* `mulCompat_of_isMonHom`: conversely.

Also: the `N = 1` level subscheme detects exactly the identity on every test scheme
(`factorsThrough_lev_iff_one`, from the structure fields `lev_torsion`, `lev_one` and the group law —
the same argument as FLT's `FakeEllipticCurve.factorsThrough_lev_iff_eq_one_of_level_one`), and the
level point at `1` is the FLT full-level point.

Nothing here assumes `D5_Obligation`, `D2_Obligation` or `D34_Obligation`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D6

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped Quaternion CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.CerednikDrinfeld.QM

section General

variable {K : Type} [Field K] {A A' : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of K)} {f' : A' ⟶ Spec (CommRingCat.of K)}

/-- `overHomEquivSchemeHomOver` turns post-composition with `φ` into `mapPt φ.left`. -/
theorem equiv_comp (T : Over (Spec (CommRingCat.of K))) (a : T ⟶ Over.mk f)
    (φ : Over.mk f ⟶ Over.mk f') :
    overHomEquivSchemeHomOver T f' (a ≫ φ) =
      mapPt φ.left (Over.w φ) (overHomEquivSchemeHomOver T f a) :=
  Subtype.ext rfl

/-- Compatibility with all multiplications forces compatibility with the units. -/
theorem mapPt_one_of_mulCompat (G : RelativeGroupLaw K f) (G' : RelativeGroupLaw K f')
    (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (G.mul t P Q) = G'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) :
    mapPt φ hφ (G.one t) = G'.one t := by
  letI := G'.pointGroup t
  have h1 := hmul t (G.one t) (G.one t)
  rw [G.one_mul] at h1
  have h2 : (mapPt φ hφ (G.one t) : SchemeHomOver t f') * mapPt φ hφ (G.one t) =
      mapPt φ hφ (G.one t) * 1 := by
    rw [mul_one]; exact h1.symm
  exact mul_left_cancel h2

/-- **FLT multiplication-compatibility ⟹ monoid morphism** for the rebuilt group objects. -/
theorem isMonHom_of_mulCompat (G : RelativeGroupLaw K f) (G' : RelativeGroupLaw K f')
    (φ : Over.mk f ⟶ Over.mk f')
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      mapPt φ.left (Over.w φ) (G.mul t P Q) =
        G'.mul t (mapPt φ.left (Over.w φ) P) (mapPt φ.left (Over.w φ) Q)) :
    letI := G.grpObjOverMk; letI := G'.grpObjOverMk; IsMonHom φ := by
  letI := G.grpObjOverMk
  letI := G'.grpObjOverMk
  have hone := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) =>
    mapPt_one_of_mulCompat G G' φ.left (Over.w φ) hmul t
  constructor
  · apply (overHomEquivSchemeHomOver (𝟙_ (Over (Spec (CommRingCat.of K)))) f').injective
    rw [equiv_comp, G.grpObjOverMk_one_eq, hone, G'.grpObjOverMk_one_eq]
  · apply (overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f').injective
    rw [equiv_comp, G.grpObjOverMk_mul_eq, hmul,
      MonObj.mul_eq_mul (Over.mk f'),
      MonObj.comp_mul, tensorHom_fst, tensorHom_snd, G'.overHomEquivSchemeHomOver_mul,
      equiv_comp, equiv_comp]

/-- **Monoid morphism ⟹ FLT multiplication-compatibility on every test point.** -/
theorem mulCompat_of_isMonHom (G : RelativeGroupLaw K f) (G' : RelativeGroupLaw K f')
    (φ : Over.mk f ⟶ Over.mk f')
    (hφ : letI := G.grpObjOverMk; letI := G'.grpObjOverMk; IsMonHom φ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f) :
    mapPt φ.left (Over.w φ) (G.mul t P Q) =
      G'.mul t (mapPt φ.left (Over.w φ) P) (mapPt φ.left (Over.w φ) Q) := by
  letI := G.grpObjOverMk
  letI := G'.grpObjOverMk
  let a : Over.mk t ⟶ Over.mk f := (overHomEquivSchemeHomOver (Over.mk t) f).symm P
  let b : Over.mk t ⟶ Over.mk f := (overHomEquivSchemeHomOver (Over.mk t) f).symm Q
  have ha : overHomEquivSchemeHomOver (Over.mk t) f a = P := Equiv.apply_symm_apply _ _
  have hb : overHomEquivSchemeHomOver (Over.mk t) f b = Q := Equiv.apply_symm_apply _ _
  have e1 : G.mul t P Q = overHomEquivSchemeHomOver (Over.mk t) f (a * b) := by
    rw [G.overHomEquivSchemeHomOver_mul, ha, hb]; rfl
  have e2 : G'.mul t (mapPt φ.left (Over.w φ) P) (mapPt φ.left (Over.w φ) Q) =
      overHomEquivSchemeHomOver (Over.mk t) f' ((a ≫ φ) * (b ≫ φ)) := by
    rw [G'.overHomEquivSchemeHomOver_mul, equiv_comp, equiv_comp, ha, hb]; rfl
  rw [e1, e2, ← equiv_comp, MonObj.mul_comp]

end General

/-! ## FLT data of a fake elliptic curve with `N = 1` -/

section FLTData

variable {K : Type} [Field K]

/-- **The `N = 1` level subscheme detects exactly the identity, on every test scheme**
(from the actual structure fields `lev_torsion` (with `N = 1`) and `lev_one`, and the group law). -/
theorem factorsThrough_lev_iff_one (E : FakeEC K) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t E.f) :
    FactorsThrough E.lev P ↔ P = E.L.one t := by
  constructor
  · intro hP
    have h1 := E.lev_torsion t P hP
    change E.L.mul t (E.L.one t) P = E.L.one t at h1
    rwa [E.L.one_mul] at h1
  · rintro rfl
    exact E.lev_one t

theorem act_toΛ_one (E : FakeEC K) : E.act (toΛ 1) = 𝟙 E.A := E.act_one (toΛ 1).2

theorem fltLevelPoint_eq (u : FLTL3 K) (a : LeafQM.O) :
    fltLevelPoint u a = u.2.P.1 ≫ u.1.act (toΛ a) := rfl

theorem fltLevelPoint_one (u : FLTL3 K) : fltLevelPoint u 1 = u.2.P.1 := by
  rw [fltLevelPoint_eq, act_toΛ_one, Category.comp_id]

/-- A lattice element as a kernel order element (`order_bridge`, membership is `Iff.rfl`). -/
def ofΛ (x : ↥Λ) : LeafQM.O := ⟨(x : ℍ[ℚ, 2, -3]), (order_bridge.2.2 _).mp x.2⟩

@[simp] theorem toΛ_ofΛ (x : ↥Λ) : toΛ (ofΛ x) = x := rfl

end FLTData

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D6

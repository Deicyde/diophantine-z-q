/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D6.Transport

/-!
# D6, part 2: the isomorphism dictionary `Dictionary.D6_Obligation`

For two FLT objects `u u' : FLTL3 K` packaged as kernel objects with `IsPackaging` (`ι = act`,
`η = a · P`), an FLT isomorphism `WithFullLevel.Iso u u'` (a scheme isomorphism over `Spec K`
compatible with the multiplications on all test points, with `act`, with the level subschemes on all
test points, and carrying `P` to `P'`) is the same as a kernel `QML3.Iso` (an isomorphism of abelian
varieties, i.e. of group objects, equivariant for `ι` and carrying `η` to `η'`).

* `forward`: the FLT scheme isomorphism, as an isomorphism in `Over (Spec K)`, is a monoid morphism
  for the rebuilt group objects (`isMonHom_of_mulCompat`), its inverse too; equivariance from the
  `act`-compatibility and `IsPackaging`; the level equation from the point and `act` compatibility.
* `backward`: the kernel morphisms' underlying schemes give the scheme isomorphism; multiplication
  compatibility from `IsMonHom` (`mulCompat_of_isMonHom`); `act`-compatibility from equivariance and
  `IsPackaging`; level-subscheme compatibility on every test scheme from `factorsThrough_lev_iff_one`
  (`N = 1`) and unit preservation; the point from the level equation at `1`.

No hypothesis beyond those of `D6_Obligation`; `[CharZero K]` is not needed. No D2/D34/D5 input.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D6

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped Quaternion CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.CerednikDrinfeld.QM

variable {K : Type} [Field K]

/-- The FLT scheme isomorphism over `Spec K`, as an isomorphism in `Over (Spec K)`. -/
def overIso (u u' : FLTL3 K) (eI : u.1.A ≅ u'.1.A) (he : eI.hom ≫ u'.1.f = u.1.f) :
    Over.mk u.1.f ≅ Over.mk u'.1.f :=
  Over.isoMk eI he

/-- The inverse of the FLT scheme isomorphism, as an `Over` morphism, is a group-object morphism. -/
theorem isMonHom_isoMk_inv (u u' : FLTL3 K) (eI : u.1.A ≅ u'.1.A) (he : eI.hom ≫ u'.1.f = u.1.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t u.1.f),
      mapPt eI.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt eI.hom he P) (mapPt eI.hom he Q)) :
    letI := u'.1.L.grpObjOverMk; letI := u.1.L.grpObjOverMk; IsMonHom (overIso u u' eI he).inv := by
  letI := u.1.L.grpObjOverMk
  letI := u'.1.L.grpObjOverMk
  haveI : IsMonHom (overIso u u' eI he).hom :=
    isMonHom_of_mulCompat u.1.L u'.1.L (overIso u u' eI he).hom (fun t P Q => hmul t P Q)
  infer_instance

/-- **DATA (FLT ⟹ kernel).** The kernel isomorphism determined by FLT isomorphism data: `φ` is the FLT
scheme isomorphism `eI` itself, as an isomorphism in `Over (Spec K)` (a group-object morphism by
`isMonHom_of_mulCompat`), and `ψ` is its inverse. (The FLT level-subscheme clause is not used in
this direction: for `N = 1` it is implied by the multiplication clause.) -/
def qml3IsoOfFLT (u u' : FLTL3 K) (h : AbVarProps u.1) (h' : AbVarProps u'.1)
    (hs : (abVarOfFakeEC u.1 h).dim = 2) (hs' : (abVarOfFakeEC u'.1 h').dim = 2)
    (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q)
    (q' : LeafQM.AV.QMStr (abVarOfFakeEC u'.1 h')) (e' : LeafQM.AV.Level3 q')
    (hp : IsPackaging u h q e) (hp' : IsPackaging u' h' q' e')
    (eI : u.1.A ≅ u'.1.A) (he : eI.hom ≫ u'.1.f = u.1.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t u.1.f),
      mapPt eI.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt eI.hom he P) (mapPt eI.hom he Q))
    (hact : ∀ x : ↥Λ, u.1.act x ≫ eI.hom = eI.hom ≫ u'.1.act x)
    (hpt : mapPt eI.hom he u.2.P = u'.2.P) :
    LeafQM.AV.QML3.Iso ⟨abVarOfFakeEC u.1 h, hs, q, e⟩ ⟨abVarOfFakeEC u'.1 h', hs', q', e'⟩ where
  φ := @PkgI3.AbVar.Hom.mk' K _ (abVarOfFakeEC u.1 h) (abVarOfFakeEC u'.1 h') (overIso u u' eI he).hom
    (isMonHom_of_mulCompat u.1.L u'.1.L (overIso u u' eI he).hom (fun t P Q => hmul t P Q))
  ψ := @PkgI3.AbVar.Hom.mk' K _ (abVarOfFakeEC u'.1 h') (abVarOfFakeEC u.1 h) (overIso u u' eI he).inv
    (isMonHom_isoMk_inv u u' eI he hmul)
  left := (overIso u u' eI he).hom_inv_id
  right := (overIso u u' eI he).inv_hom_id
  equivariant a := by
    apply Over.OverMorphism.ext
    change (q.iota a).hom.left ≫ eI.hom = eI.hom ≫ (q'.iota a).hom.left
    rw [hp.1 a, hp'.1 a]
    exact hact (toΛ a)
  level a := by
    change Additive.ofMul (Additive.toMul (e.eta a) ≫ (overIso u u' eI he).hom) = e'.eta a
    apply Additive.toMul.injective
    apply Over.OverMorphism.ext
    change (Additive.toMul (e.eta a)).left ≫ eI.hom = (Additive.toMul (e'.eta a)).left
    rw [hp.2 a, hp'.2 a, fltLevelPoint_eq, fltLevelPoint_eq]
    change (u.2.P.1 ≫ u.1.act (toΛ a)) ≫ eI.hom = u'.2.P.1 ≫ u'.1.act (toΛ a)
    rw [Category.assoc, hact (toΛ a), ← Category.assoc]
    exact congrArg (fun P => P.1 ≫ u'.1.act (toΛ a)) hpt

/-- FLT isomorphism ⟹ kernel `QML3.Iso`. -/
theorem forward (u u' : FLTL3 K) (h : AbVarProps u.1) (h' : AbVarProps u'.1)
    (hs : (abVarOfFakeEC u.1 h).dim = 2) (hs' : (abVarOfFakeEC u'.1 h').dim = 2)
    (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q)
    (q' : LeafQM.AV.QMStr (abVarOfFakeEC u'.1 h')) (e' : LeafQM.AV.Level3 q')
    (hp : IsPackaging u h q e) (hp' : IsPackaging u' h' q' e')
    (H : FakeEllipticCurve.WithFullLevel.Iso u u') :
    Nonempty (LeafQM.AV.QML3.Iso ⟨abVarOfFakeEC u.1 h, hs, q, e⟩ ⟨abVarOfFakeEC u'.1 h', hs', q', e'⟩) := by
  obtain ⟨eI, he, hmul, hact, -, hpt⟩ := H
  exact ⟨qml3IsoOfFLT u u' h h' hs hs' q e q' e' hp hp' eI he hmul hact hpt⟩

/-- **DATA (kernel ⟹ FLT).** The scheme isomorphism underlying a kernel `QML3.Iso`: the `left`
components of its two `Over` morphisms. -/
def schemeIsoOfQML3 {u u' : FLTL3 K} {h : AbVarProps u.1} {h' : AbVarProps u'.1}
    {hs : (abVarOfFakeEC u.1 h).dim = 2} {hs' : (abVarOfFakeEC u'.1 h').dim = 2}
    {q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)} {e : LeafQM.AV.Level3 q}
    {q' : LeafQM.AV.QMStr (abVarOfFakeEC u'.1 h')} {e' : LeafQM.AV.Level3 q'}
    (I : LeafQM.AV.QML3.Iso ⟨abVarOfFakeEC u.1 h, hs, q, e⟩ ⟨abVarOfFakeEC u'.1 h', hs', q', e'⟩) :
    u.1.A ≅ u'.1.A where
  hom := I.φ.hom.left
  inv := I.ψ.hom.left
  hom_inv_id := congrArg (fun g => g.left) I.left
  inv_hom_id := congrArg (fun g => g.left) I.right

/-- Kernel `QML3.Iso` ⟹ FLT isomorphism. -/
theorem backward (u u' : FLTL3 K) (h : AbVarProps u.1) (h' : AbVarProps u'.1)
    (hs : (abVarOfFakeEC u.1 h).dim = 2) (hs' : (abVarOfFakeEC u'.1 h').dim = 2)
    (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q)
    (q' : LeafQM.AV.QMStr (abVarOfFakeEC u'.1 h')) (e' : LeafQM.AV.Level3 q')
    (hp : IsPackaging u h q e) (hp' : IsPackaging u' h' q' e')
    (I : LeafQM.AV.QML3.Iso ⟨abVarOfFakeEC u.1 h, hs, q, e⟩ ⟨abVarOfFakeEC u'.1 h', hs', q', e'⟩) :
    FakeEllipticCurve.WithFullLevel.Iso u u' := by
  let φ : Over.mk u.1.f ⟶ Over.mk u'.1.f := I.φ.hom
  have hmon : letI := u.1.L.grpObjOverMk; letI := u'.1.L.grpObjOverMk; IsMonHom φ :=
    (inferInstance : IsMonHom I.φ.hom)
  let eI : u.1.A ≅ u'.1.A := schemeIsoOfQML3 I
  have he : eI.hom ≫ u'.1.f = u.1.f := Over.w φ
  have hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t u.1.f),
      mapPt eI.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt eI.hom he P) (mapPt eI.hom he Q) :=
    fun t P Q => mulCompat_of_isMonHom u.1.L u'.1.L φ hmon t P Q
  have hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)),
      mapPt eI.hom he (u.1.L.one t) = u'.1.L.one t :=
    fun t => mapPt_one_of_mulCompat u.1.L u'.1.L eI.hom he hmul t
  have hinj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t u.1.f),
      mapPt eI.hom he P = mapPt eI.hom he Q → P = Q := by
    intro T t P Q hPQ
    apply Subtype.ext
    exact (Iso.cancel_iso_hom_right _ _ eI).mp (congrArg Subtype.val hPQ)
  refine ⟨eI, he, hmul, fun x => ?_, fun t P => ?_, ?_⟩
  · have h1 := congrArg (fun g => g.left) (I.equivariant (ofΛ x))
    change (q.iota (ofΛ x)).hom.left ≫ φ.left = φ.left ≫ (q'.iota (ofΛ x)).hom.left at h1
    rw [hp.1, hp'.1, toΛ_ofΛ] at h1
    exact h1
  · rw [factorsThrough_lev_iff_one, factorsThrough_lev_iff_one]
    constructor
    · rintro rfl; exact hone t
    · intro h2; exact hinj t _ _ (h2.trans (hone t).symm)
  · apply Subtype.ext
    have h1 := congrArg (fun g => (Additive.toMul g).left) (I.level 1)
    change (Additive.toMul (e.eta 1)).left ≫ φ.left = (Additive.toMul (e'.eta 1)).left at h1
    rw [hp.2 1, hp'.2 1, fltLevelPoint_one, fltLevelPoint_one] at h1
    exact h1

/-- **D6.** The isomorphism dictionary. -/
theorem d6_obligation : D6_Obligation := by
  intro K _ _ u u' h h' hs hs' q e q' e' hp hp'
  exact ⟨fun H => forward u u' h h' hs hs' q e q' e' hp hp' H,
    fun ⟨I⟩ => backward u u' h h' hs hs' q e q' e' hp hp' I⟩

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D6

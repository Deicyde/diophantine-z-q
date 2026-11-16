/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.Interfaces

/-!
# W13 dictionary interfaces D6, D7 (UNPROVED obligations, stated as `Prop`s)

Separate from the frozen `Dictionary/Interfaces.lean` (which is imported unchanged). Nothing here is a
proof; the `def … : Prop` are the obligations handed to the D6/D7 lanes.

* **D6** (isomorphism dictionary): over a field of characteristic zero, for two FLT objects with full
  level-3 data packaged as kernel objects exactly as in D3/D4 (`act`/`P` equations), FLT isomorphism
  `WithFullLevel.Iso` is equivalent to the existence of a kernel `QML3.Iso`.
* **D7** (universal family): for any fine moduli scheme `M → Spec 𝒪` of the FLT problem
  `(Λ, N = 1, m = 3)` (with the further properties the FLT companion
  `exists_isFineModuli_of_isUnit_two_of_isUnit_three` provides), there is a kernel `QMFamily` over `M`
  whose fibre at every characteristic-zero field point `(ptF K s u).1 : Spec K ⟶ M` is the packaged
  kernel object of `u`, in the sense of `LeafQM.AV.IsFibreOf` (pullback square
  `P.A.X.left → 𝒜.F.left` over `(ptF K s u).1`, carrying `ι` and `η`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj

/-- The D3/D4 compatibility of a kernel packaging `(q, e)` of `u` with the FLT data `act`, `P`. -/
def IsPackaging {K : Type} [Field K] (u : FLTL3 K) (h : AbVarProps u.1)
    (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q) : Prop :=
  (∀ a : LeafQM.O, (q.iota a).hom.left = u.1.act (toΛ a)) ∧
    (∀ a : LeafQM.O, (Additive.toMul (e.eta a)).left = fltLevelPoint u a)

/-- **D6 (UNPROVED obligation; isomorphism dictionary).** -/
def D6_Obligation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (u u' : FLTL3 K)
    (h : AbVarProps u.1) (h' : AbVarProps u'.1)
    (hs : (abVarOfFakeEC u.1 h).dim = 2) (hs' : (abVarOfFakeEC u'.1 h').dim = 2)
    (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q)
    (q' : LeafQM.AV.QMStr (abVarOfFakeEC u'.1 h')) (e' : LeafQM.AV.Level3 q'),
    IsPackaging u h q e → IsPackaging u' h' q' e' →
      (FLT.CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.Iso u u' ↔
        Nonempty (LeafQM.AV.QML3.Iso ⟨abVarOfFakeEC u.1 h, hs, q, e⟩ ⟨abVarOfFakeEC u'.1 h', hs', q', e'⟩))

/-- The type of the FLT moduli point map `ptF` for `(Λ, 1, 3)` over `𝒪`, with target `πM`. -/
abbrev PtF (𝒪 : Type) [CommRing 𝒪] {M : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of 𝒪)) : Type 1 :=
  ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FLT.CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ 1 3 S → FLT.NeronModelInfra.SchemeHomOver s πM

/-- **D7 (UNPROVED obligation; universal family over the actual fine moduli scheme).** The
hypotheses are exactly the conclusions of the FLT companion
`CerednikDrinfeld.QM.exists_isFineModuli_of_isUnit_two_of_isUnit_three` (with `N = 1`, `m = 3`) plus
the unit hypotheses of that companion; the conclusion asks for a genuine family over `M`
(not only field-point bijections). -/
def D7_Obligation : Prop :=
  ∀ (𝒪 : Type) [CommRing 𝒪], IsUnit ((2 : ℕ) : 𝒪) → IsUnit ((3 : ℕ) : 𝒪) →
  ∀ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ptF : PtF 𝒪 πM),
    FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF →
    IsSeparated πM → QuasiCompact πM → LocallyOfFiniteType πM →
    (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) →
    ∃ 𝒜 : LeafQM.AV.QMFamily M,
      ∀ (K : Type) [Field K] [CharZero K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of 𝒪))
        (u : FLTL3 K) (h : AbVarProps u.1) (hs : (abVarOfFakeEC u.1 h).dim = 2)
        (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q),
        IsPackaging u h q e →
          LeafQM.AV.IsFibreOf 𝒜 (ptF K s u).1 ⟨abVarOfFakeEC u.1 h, hs, q, e⟩

end ZInQ.Contrib.CloudB2Shimura.Dictionary

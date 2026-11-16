/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D34.Basic

/-!
# W13 dictionary D3/D4, part 4: the kernel level-3 structure `a ↦ a · P`

For any kernel QM structure `q` whose `ι` is `iota` (the FLT action), `η a := a · P`
(`ptHom`, i.e. `fltLevelPoint`) is a kernel `Level3 q`:

* additive (`act_add`);
* `𝒪`-linear (`act_mul`);
* kernel exactly `3𝒪`: `3 · P = 0` by `FullLevel.torsion`, and `a · P = 0 ⇒ a ∈ 3𝒪` by
  `FullLevel.annihilator` at `K → K̄`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D34

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped Quaternion CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudB2Shimura.Dictionary

variable {K : Type} [Field K] (u : FLTL3 K) (h : AbVarProps u.1)

/-- `a ↦ a · P` as an additive map `𝒪 → A(K)`. -/
def etaHom : LeafQM.O →+ Additive ((abVarOfFakeEC u.1 h).Pt K) :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (ptHom u a))
    (fun a b => congrArg Additive.ofMul (ptHom_add u a b))

@[simp] lemma etaHom_apply (a : LeafQM.O) : etaHom u h a = Additive.ofMul (ptHom u a) := rfl

lemma ptHom_eq_one_of_mem_three (b : LeafQM.O) :
    letI := u.1.L.grpObjOverMk
    ptHom u (3 * b) = 1 := by
  letI := u.1.L.grpObjOverMk
  haveI := isMonHom_actHom u.1 (toΛ b)
  rw [show (3 : LeafQM.O) * b = b * 3 from (Nat.cast_commute 3 b).eq, ptHom_mul, ptHom_three, MonObj.one_comp]

/-- **The kernel level-3 structure** `η a = a · P`. -/
def level3 (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (hq : q.iota = iota u.1 h) :
    LeafQM.AV.Level3 q where
  eta := etaHom u h
  linear a b := by
    rw [LeafQM.AV.qmAct, RingHom.comp_apply, hq]
    change Additive.ofMul (ptHom u (a * b)) = Additive.ofMul (ptHom u b ≫ actHom u.1 (toΛ a))
    rw [ptHom_mul]
  ker a := by
    rw [etaHom_apply]
    constructor
    · intro ha
      exact mem_three_of_ptHom_eq_one u a (Additive.ofMul.injective ha)
    · rintro ⟨b, rfl⟩
      exact congrArg Additive.ofMul (ptHom_eq_one_of_mem_three u b)

@[simp] lemma level3_eta_left (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (hq : q.iota = iota u.1 h)
    (a : LeafQM.O) : (Additive.toMul ((level3 u h q hq).eta a)).left = fltLevelPoint u a := rfl

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D34

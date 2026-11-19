import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Assembly

/-!
# Theorem 5.3, Lane RC0: the base-zero leaf with the conductor-one factorization proved

Lane RC25's base-zero leaf model (`BaseZeroAssembly.BaseZeroLeafModel`) carries the conductor-one
Heegner data `HeegnerData`, whose last conjunct is the factorization
`L(E/K, s) = L(E, s) L(E^{(k)}, s)` (GLUE, tex 4345–4346, 5736). Here the model carries
`HeegnerDataSqrt` instead: the same data with the factorization replaced by the conditions on
`K` that the text imposes (tex 2599: "Fix `k` and `K = ℚ(√k)`"; tex 2720: `K = ℚ(√k)` is
imaginary and split at `2N`): `2` splits in `K`, and `K` contains a square root of `k` outside
`ℚ`. The factorization is PROVED from the Artin factorization of the ring-class `L`-functions
(lane RC27's `lFactorizationConductorOne_of_artin`, through `heegnerData_of_sqrt`), which the
headline proves from the `ModularNewform` print (`RCLeaves.artin`).

* `BaseZeroLeafModelSqrt`, `BaseZeroLeafInputsSqrt` (the new leaf);
* `baseZeroLeafInputs_of_sqrt` (PROVED): the old leaf from the new one and `ArtinFactorization`;
* non-vacuity of the new conditions on `K` (`baseZeroSqrt_field_conditions_nonvacuous`, PROVED):
  `K = ℚ(√−7)`, `k = −7` meets them together with every other condition on `K` in
  `HeegnerDataSqrt` except the splitting of the level (lane RC27's
  `artinG2_field_hypotheses_nonvacuous`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.BaseZeroAssembly
  ZInQ.Contrib.CloudB3RC53

/-- **The base-zero leaf model with the conditions on `K`** (tex 4330–4376): lane RC25's
`BaseZeroLeafModel` with the conductor-one Heegner data in the form `HeegnerDataSqrt` (`K = ℚ(√k)`
split at `2`, the factorization not an input; definition + GLUE, lanes RC19 / batch 3). -/
structure BaseZeroLeafModelSqrt {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) : Type 1 where
  /-- `E_ℓ` is elliptic (`ℓ ≠ 0`) -/
  hE : (Ecurve ℓ).IsElliptic
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  /-- the conductor-one Heegner point -/
  P : ((Ecurve ℓ).baseChange K).toAffine.Point
  /-- its Heegner data, with `K = ℚ(√k)` split at `2` in place of the factorization -/
  heegner : HeegnerDataSqrt (Ecurve ℓ) hE (D.kfin : ℚ) K P
  /-- the model at the base -/
  core : BaseZeroCore D Fam P

attribute [instance] BaseZeroLeafModelSqrt.fieldK BaseZeroLeafModelSqrt.nfK
  BaseZeroLeafModelSqrt.decK

/-- **The base-zero leaf inputs with the conditions on `K`** (Lemma `ex:arith-base-zero`, tex
4330–4376), quantified as lane RC25's `BaseZeroLeafInputs`. -/
def BaseZeroLeafInputsSqrt {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → Nonempty (BaseZeroLeafModelSqrt D F)

/-- **Lane RC25's leaf from the new one and the Artin factorization** (tex 5736; PROVED: lane RC27's
`lFactorizationConductorOne_of_artin` through `heegnerData_of_sqrt`). -/
theorem baseZeroLeafInputs_of_sqrt {ℓ : ℕ} {D : RCData ℓ} (hA : GenusOdd.ArtinFactorization)
    (h : BaseZeroLeafInputsSqrt D) : BaseZeroLeafInputs D := fun hSel hk Co Ce F hF => by
  obtain ⟨M⟩ := h hSel hk Co Ce F hF
  exact ⟨BaseZeroLeafModel.mk M.hE M.K M.P (heegnerData_of_sqrt hA M.heegner) M.core⟩

/-- **Non-vacuity of the new conditions on `K`** (PROVED: lane RC27's
`artinG2_field_hypotheses_nonvacuous`, at `K = ℚ(√−7)`, `k = −7`). -/
theorem baseZeroSqrt_field_conditions_nonvacuous :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (k : ℚ) (t : K),
      Module.finrank ℚ K = 2 ∧ NumberField.IsTotallyComplex K ∧ NumberField.discr K ≠ -3 ∧
        NumberField.discr K ≠ -4 ∧ CST.SplitsIn K 2 ∧ t ∉ (algebraMap ℚ K).range ∧
          t ^ 2 = algebraMap ℚ K k :=
  Height.artinG2_field_hypotheses_nonvacuous

end ZInQ.Manuscript.RC.Wiring

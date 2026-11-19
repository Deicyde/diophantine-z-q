import ZInQKernel.Contrib.OneProof.RC.Wiring.BaseZeroSqrt
import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.LamBridge
import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.NonVacuity

/-!
# Theorem 5.3, Lane RC0: the base-zero leaf on the text's named steps

Lemma `ex:arith-base-zero` (tex 4330–4376). The leaf `BaseZeroLeafInputsSqrt` (`BaseZeroSqrt.lean`)
carries lane RC25's `BaseZeroCore`, whose fields `hcentral`, `boundary` (with its limit statement
`hlim`), `lam`, `hlam` and `hu` state conclusions of steps of the text.
Here the core records weaker algebraic inputs named after those steps. The fields do not
identify `CU` with the actual primitive complex, `cz` with conjugate transport of `z`, or `ψ`
with the inverse of the orthogonal comparison:

| field of `BaseZeroCore` | replaced by | how the field is recovered | tex |
|---|---|---|---|
| `hcentral : rank ρ(Dm) = m` | `central`: the central degree-one cohomology is `V₂ Sel_{2^∞}(E/ℚ) × V₂ Sel_{2^∞}(E^{(k)}/ℚ)` (`CentralSelmerComparison`; ELLIOT + GLUE) | PROVED from the lemma's own hypothesis `SelmerCorankOneOverK` (lane RC30's `hcentral_of_selmer`) | 4350–4352, 3952–3962, 5305–5311 |
| `boundary` (its `hlim : z̄ = lim_i L κ(W_i)`) | `limit`: the retained inner-limit data of (4.5) at the base (`InnerLimit45Base`; the stage boundaries ELLIOT, the inner limit PROVED, the comparison definitions) | PROVED (lane RC30's `InnerLimit45Base.toBoundary45Base`) | 3912–3921, 3952–3968 |
| `lam`, `hlam` | the pairing `pd1`, `pd2` with its Leibniz identity `hL1` (GLUE), a chain map `ψ` (in the proposition a homotopy inverse of `j`) and the cocycle `c z` (`hcz`); `lam` is the paired functional `PD(·, ψ(c z))` (definition) | `hlam` PROVED from `hL1` and `hcz` (the RC53 group's `baseLam_closed`), as in the text | 3742–3749, 3845–3849, 3860–3863 |
| `hu` (for every row representing `lam`) | `hu`: the coordinate statement for the single row of the paired functional (Definition `ex:arith-coordinate`) | PROVED (uniqueness of the row, `BaseZeroCore.ofClosed`) | 3877–3892 |

The conductor-one Heegner data stay in the form `HeegnerDataSqrt` (`K = ℚ(√k)` split at `2`; the
factorization `L(E/K, s) = L(E, s) L(E^{(k)}, s)` PROVED from the Artin factorization).

* `BaseZeroCoreText`, `BaseZeroLeafModelText`, `BaseZeroLeafInputsText` (the new leaf);
* `BaseZeroCoreText.toCore` (PROVED, lane RC30's `coreOfPaired`), `baseZeroLeafInputsSqrt_of_text`
  and `baseZeroLeafInputs_of_text` (PROVED): the previous leaves from the new one;
* non-vacuity (PROVED): `baseZeroCoreText_nonvacuous`. Under the lemma's hypothesis
  `SelmerCorankOneOverK`, for interface data whose base coordinate is the image of `f ∈ Λ`, there
  is a core whose degree-one/two matrix window is `[A --0--> A]`; its stored `exCU` has `A`
  in every integer degree and zero differentials. It uses the multiplication pairing, `ψ = 𝟙` and
  `c z = 1`, with generic coordinate `f` and central cycle `f(0)`; with `f = 1` neither is zero
  (`baseZeroCoreText_not_forced`). As for lanes RC25 and RC30, the Heegner data are not
  constructed here. The example lives at the infinite-order point `1 ∈ ℤ` of `G = ℤ` (not a
  point of `E(K)`; the Heegner data are not constructed). At a torsion point the core forces
  `u_{prim,0}(0) = 0`.

As abstract inputs the new fields are equivalent to those they replace: an `InnerLimit45Base`
exists iff `z̄ = L κ(P)` with `L ≠ 0` (lane RC30's `nonempty_innerLimit45Base_iff`), the central
comparison exists iff the central kernel has the Selmer dimension
(`nonempty_centralSelmerComparison_iff`), and a closed functional is the paired functional of a
degenerate pairing (`ε = 0`). The gain is that `hcentral`, `hlim` and `hlam` are proofs from the
steps of the text, and each remaining input is a named step with its kind.

What remains of the leaf is an existential matrix model and pairing data, the Heegner data,
the central dimension comparison, the inner-limit compatibility equations, and `hprimId`.
The fields `CU`, `e1`, `e2`, `hd` specify only the degree-one/two differential; they impose
neither two-term support nor an identification with the actual primitive complex. The cocycle
`cz` is independent of `z`, and `ψ` is an arbitrary chain map. Supplying the genuine retained
complex, class, duality and comparison maps remains an arithmetic discharge obligation.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC
  ZInQ.Manuscript.RC.BaseZeroAssembly ZInQ.Manuscript.RC.BaseZeroLimit ZInQ.Manuscript.RC.Uniform
  ZInQ.Manuscript.RC.Rings
open CategoryTheory Matrix

/-- **The base-zero core on the text's named steps** (tex 4330–4376), for a specified point
`P : G`. Fields, with tex lines and kinds:

* `m`, `Dm`, `z`, `hz`, `CU`, `e1`, `e2`, `hd`: the two-term model of the primitive complex at the
  base over `A = Λ_(t)` and its retained cycle (tex 4341–4369; ELLIOT + GLUE, as lane RC25);
* `central`: the central degree-one cohomology is the rational full Selmer group
  (`CentralSelmerComparison`; tex 4350–4352, 3952–3962, 5305–5311; ELLIOT + GLUE);
* `C'`, `C`, `pd1`, `pd2`, `ε`, `hL1`, `ψ`, `cz`, `hcz`: the pairing between `CU` and `C'` with its
  Leibniz identity, the chain map `ψ : C → C'` and the cocycle `c z` of
  Proposition `ex:arith-paired-functional` (tex 3704–3880; GLUE for the pairing, definitions);
* `uprim`, `hu`: the generic class-functional coordinate and the coordinate statement for the row
  of the paired functional `PD(·, ψ(c z))` (Definition `ex:arith-coordinate`, tex 3877–3892);
* `limit`: the retained inner-limit data of (4.5) for the central cycle `z̄ = ρ(z)`
  (`InnerLimit45Base`; tex 3912–3921, 3952–3968);
* `hprimId`: the interface's `u_{prim,0}` is the `t`-expansion of the generic coordinate
  (definition). -/
structure BaseZeroCoreText {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type} [AddCommGroup G]
    (P : G) : Type 1 where
  /-- the rank of the two-term model -/
  m : ℕ
  /-- the differential of the two-term model, over `A = Λ_(t)` -/
  Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT
  /-- An abstract equivalence from the central matrix kernel to the rational full Selmer
  product; under `SelmerCorankOneOverK`, its existence is equivalent to the central rank
  condition. No naturality or actual cohomology-map compatibility is required. -/
  central : CentralSelmerComparison (selmerTwoPower (Ecurve ℓ))
    (selmerTwoPower (Etw ℓ D.kfin)) Dm
  /-- the retained integral cycle -/
  z : Fin (m + 1) → Rings.LambdaT
  /-- it is a cycle -/
  hz : Dm *ᵥ z = 0
  /-- A complex with the specified degree-one/two matrix window. Other degrees and the
  incoming differential are not constrained by this structure. -/
  CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ
  /-- the complex paired with it -/
  C' : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ
  /-- the complex of the class -/
  C : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ
  /-- degree one is `A^{m+1}` -/
  e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT)
  /-- degree two is `A^{m+1}` -/
  e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT)
  /-- in these coordinates the differential is `Dm` -/
  hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y
  /-- the pairing in degrees `(1, 2)` -/
  pd1 : CU.X 1 →ₗ[Rings.LambdaT] C'.X 2 →ₗ[Rings.LambdaT] Rings.LambdaT
  /-- the pairing in degrees `(2, 1)` -/
  pd2 : CU.X 2 →ₗ[Rings.LambdaT] C'.X 1 →ₗ[Rings.LambdaT] Rings.LambdaT
  /-- the sign of the Leibniz identity -/
  ε : Rings.LambdaT
  /-- the Leibniz identity of the pairing -/
  hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y)
  /-- An arbitrary chain map; the structure does not require an orthogonal-comparison
  homotopy inverse. -/
  ψ : C ⟶ C'
  /-- An independent cocycle. Identification with conjugate transport of the retained
  cycle `z` is not a field of this structure. -/
  cz : C.X 1
  /-- it is a cocycle -/
  hcz : (C.d 1 2).hom cz = 0
  /-- the generic class-functional coordinate, in `F = Frac Λ` -/
  uprim : FractionRing Uniform.Lambda
  /-- it is the coordinate of `[z] ⊗ [PD(·, ψ(c z))]` -/
  hu : Central.IsClassFunctionalCoord
    (Dm.map (algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)))
    (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (z i))
    (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)
      (BaseZeroLam.rowOf (BaseZeroLam.baseLam pd2 ψ cz) e2 i)) uprim
  /-- the retained inner-limit data of (4.5) at the base -/
  limit : InnerLimit45Base P (m + 1) (fun i => Rings.rhoT (z i))
  /-- the interface's `u_{prim,0}` is the `t`-expansion of the generic coordinate -/
  hprimId : IsTExpansion uprim (D.uPrim Fam 0)

/-- **Lane RC25's core from the core on the text's steps** (PROVED: lane RC30's `coreOfPaired`,
under the lemma's hypothesis `SelmerCorankOneOverK ℓ D.kfin`). -/
def BaseZeroCoreText.toCore {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {G : Type} [AddCommGroup G]
    {P : G} (M : BaseZeroCoreText D Fam P) (hSel : SelmerCorankOneOverK ℓ D.kfin) :
    BaseZeroCore D Fam P :=
  coreOfPaired D Fam P M.m M.Dm hSel M.central M.z M.hz M.CU M.C' M.C M.e1 M.e2 M.hd M.pd1 M.pd2
    M.ε M.hL1 M.ψ M.cz M.hcz M.uprim M.hu M.limit M.hprimId

/-- The bridged core keeps the model, the cycle, the coordinate, and has the paired functional as
its field `lam`. PROVED. -/
theorem BaseZeroCoreText.toCore_spec {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {G : Type}
    [AddCommGroup G] {P : G} (M : BaseZeroCoreText D Fam P)
    (hSel : SelmerCorankOneOverK ℓ D.kfin) :
    (M.toCore hSel).m = M.m ∧ (M.toCore hSel).uprim = M.uprim ∧
      (M.toCore hSel).lam = BaseZeroLam.baseLam M.pd2 M.ψ M.cz :=
  ⟨rfl, rfl, rfl⟩

/-- **The base-zero leaf model on the text's named steps** (tex 4330–4376): the conductor-one
Heegner data in the form `HeegnerDataSqrt` and a `BaseZeroCoreText` for the specified point. -/
structure BaseZeroLeafModelText {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) : Type 1 where
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
  /-- the model at the base, on the text's named steps -/
  core : BaseZeroCoreText D Fam P

attribute [instance] BaseZeroLeafModelText.fieldK BaseZeroLeafModelText.nfK
  BaseZeroLeafModelText.decK

/-- **The base-zero leaf inputs on the text's named steps** (Lemma `ex:arith-base-zero`, tex
4330–4376), quantified as lane RC25's `BaseZeroLeafInputs`. -/
def BaseZeroLeafInputsText {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → Nonempty (BaseZeroLeafModelText D F)

/-- **`BaseZeroLeafInputsSqrt D` from the new leaf** (PROVED; the Selmer hypothesis used by the core
bridge is the leaf's own first premise). -/
theorem baseZeroLeafInputsSqrt_of_text {ℓ : ℕ} {D : RCData ℓ} (h : BaseZeroLeafInputsText D) :
    BaseZeroLeafInputsSqrt D := fun hSel hk Co Ce F hF =>
  (h hSel hk Co Ce F hF).map fun M => ⟨M.hE, M.K, M.P, M.heegner, M.core.toCore hSel⟩

/-- **Lane RC25's leaf from the new one and the Artin factorization** (PROVED). -/
theorem baseZeroLeafInputs_of_text {ℓ : ℕ} {D : RCData ℓ} (hA : GenusOdd.ArtinFactorization)
    (h : BaseZeroLeafInputsText D) : BaseZeroLeafInputs D :=
  baseZeroLeafInputs_of_sqrt hA (baseZeroLeafInputsSqrt_of_text h)

/-! ## Non-vacuity -/

/-- **The core on the text's steps is satisfiable** (PROVED), under the lemma's hypothesis
`SelmerCorankOneOverK ℓ D.kfin`: if `D.uPrim F 0` is the image of `f ∈ Λ`, there is a
`BaseZeroCoreText D F 1` whose degree-one/two matrix window is `[A --0--> A]`; the stored
`exCU` has `A` in every integer degree. It uses the multiplication pairing (Leibniz identity
with `ε = 1`), `ψ = 𝟙`, an independent cocycle `cz = 1`, and the retained cycle `z = f`, with
generic coordinate `f`, central cycle `f(0)`, the central comparison of lane RC30's
`centralSelmerComparison_of_selmer` and the inner-limit data `constLimit`. The example lives at
the infinite-order point `1 ∈ ℤ` of `G = ℤ` (not a point of `E(K)`; the Heegner data are not
constructed). At a torsion point the core forces `u_{prim,0}(0) = 0`. -/
theorem baseZeroCoreText_nonvacuous {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (hSel : SelmerCorankOneOverK ℓ D.kfin) (f : Uniform.Lambda) (hf : D.uPrim Fam 0 = lamIncl f) :
    ∃ M : BaseZeroCoreText D Fam (1 : ℤ),
      M.uprim = algebraMap Uniform.Lambda (FractionRing Uniform.Lambda) f ∧
        ∀ i, Rings.rhoT (M.z i) = lambdaEvalZero f := by
  classical
  refine ⟨{
    m := 0
    Dm := 0
    central := (centralSelmerComparison_of_selmer hSel).some
    z := fun _ => algebraMap Uniform.Lambda LambdaT f
    hz := by simp
    CU := BaseZeroLam.exCU
    C' := BaseZeroLam.exCU
    C := BaseZeroLam.exCU
    e1 := BaseZeroLam.exE 1
    e2 := BaseZeroLam.exE 2
    hd := BaseZeroLam.exHd
    pd1 := BaseZeroLam.exPd 1 2
    pd2 := BaseZeroLam.exPd 2 1
    ε := 1
    hL1 := BaseZeroLam.exHL1
    ψ := 𝟙 BaseZeroLam.exCU
    cz := (1 : LambdaT)
    hcz := BaseZeroLam.exCz
    uprim := algebraMap LambdaT (FractionRing Uniform.Lambda) (algebraMap Uniform.Lambda LambdaT f)
    hu := ?_
    limit := ?_
    hprimId := by
      rw [hf]
      exact isTExpansion_algebraMap_lambdaT f }, ?_, ?_⟩
  · rw [BaseZeroLam.exRow]
    unfold Central.IsClassFunctionalCoord
    ext i k
    obtain rfl : i = k := Subsingleton.elim i k
    simp [vecMulVec_apply, adjugate_fin_one]
  · have hz : (fun i : Fin (0 + 1) => Rings.rhoT (algebraMap Uniform.Lambda LambdaT f)) =
        fun _ => lambdaEvalZero f := by
      funext i
      exact rhoT_algebraMap f
    exact hz ▸ constLimit (lambdaEvalZero f)
  · exact algebraMap_lambdaT_lambda f
  · intro i
    exact rhoT_algebraMap f

/-- **The core does not force the conclusion** (PROVED): with `f = 1` the generic coordinate and
the central cycle are `1 ≠ 0`; the specified point `1 ∈ ℤ` has infinite order. The example lives
at the infinite-order point `1 ∈ ℤ` of `G = ℤ` (not a point of `E(K)`; the Heegner data are not
constructed). At a torsion point the core forces `u_{prim,0}(0) = 0`. -/
theorem baseZeroCoreText_not_forced {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (hSel : SelmerCorankOneOverK ℓ D.kfin) (hf : D.uPrim Fam 0 = lamIncl 1) :
    ∃ M : BaseZeroCoreText D Fam (1 : ℤ), M.uprim ≠ 0 ∧ ∀ i, Rings.rhoT (M.z i) ≠ 0 := by
  obtain ⟨M, hu, hz⟩ := baseZeroCoreText_nonvacuous D Fam hSel 1 hf
  refine ⟨M, ?_, fun i => ?_⟩
  · rw [hu, map_one]
    exact one_ne_zero
  · rw [hz i, map_one]
    exact one_ne_zero

end ZInQ.Manuscript.RC.Wiring

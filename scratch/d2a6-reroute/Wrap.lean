import ZInQKernel.Contrib.OneProof.D2WildNF
import ZInQKernel.Contrib.OneProof.A6IntModel

/-!
# d2a6-reroute: the replacement `R6U` for R6 on the manuscript's route, and its readers

The kernel's R6 (`PkgI2.RaynaudCriterionNF`: `(σ - 1)² = 0` on `A[ℓⁿ]` for every inertia element, from SGA 7 IX 3.5
through the bundle field `sga7_IX_3_5_ForwardGeom_Def34`) has three readers on the chain: D2 (wild inertia of
`F = L_v(A[3])`, through TailH's `raynaudPlace_of_R6`, `torsFix_of_descent`, `tateWildK_of_R6`), A6 (G3 on G7's
model, TailI's `modelG3G6_of_leaves3`) and the kernel field (TailC's `good_of_QML3`, good reduction of the model
outside `T(u)`). On the manuscript's route these use two statements, bundled here as

* `R6U := SZRaynaud.RaynaudWildNF ∧ SGRSplit.ShimuraIntegralModelRep`:
  - `RaynaudWildNF` is diophantine_zq.tex L814-818 (sz-raynaud, from Silverberg–Zarhin Thm 3.5 and the ELLIOT
    sentence at L817-818); D2 needs only it;
  - `ShimuraIntegralModelRep` is the proper model of L443-477 with its universal abelian scheme (sgr-split's
    statement, `p > 324`); A6 and the kernel field need only it (L529-530).

The wrappers below have the signatures of the originals with `hR6 : R6U` in place of
`hR6 : PkgI2.RaynaudCriterionNF.{0}` (and, for `good_of_QML3U`, `T324 ⊆ T` in place of `3 ∈ T`), so the generated
chain (`D2A6Chain.lean`) calls them where the originals were called. No `sorry`; never imports
`ZInQKernel.OneProof.Main`. Report: docs/research/d2a6-reroute.md.
-/

set_option linter.style.longLine false

namespace HDec

/-- **R6 on the manuscript's route**: L814-818 (wild inertia of `F` acts trivially on `V_ℓ(A)`) and the proper model
of `Y₃` with its universal abelian scheme (L443-477, used at L529-530). -/
def D2A6.R6U : Prop := _root_.SZRaynaud.RaynaudWildNF ∧ _root_.SGRSplit.ShimuraIntegralModelRep

noncomputable section

namespace G15Ram

open _root_.PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj
open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]

attribute [local instance] RQ.numberField_of_fd

/-- `raynaudPlace_of_R6` on `R6U` (D2; through `RaynaudWildNF`, `raynaudPlace_of_wildNF`). -/
theorem raynaudPlace_of_R6U (hR6 : D2A6.R6U)
    (hTors : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) : RaynaudPlace (p := p) A m :=
  raynaudPlace_of_wildNF hR6.1 hTors A hdim hm3 hpm

/-- `tateWildK_of_R6` on `R6U` (D2; `tateWildK_of_wildNF`). -/
theorem tateWildK_of_R6U (hR6 : D2A6.R6U) (hTors : ObjBridge.TorsionStructure)
    {A : PkgI3.AbVar K} (hdim : A.dim = 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p) :
    TateWildK (p := p) A ℓ :=
  tateWildK_of_wildNF hR6.1 hTors hdim hℓp h7

/-- `torsFix_of_descent` on `R6U` (D2; `torsFix_of_wildNF`: L817-818 directly, no unipotence). -/
theorem torsFix_of_R6U (hR6 : D2A6.R6U)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q) (hpq : q ≠ p)
    (M : Fld p) [FiniteDimensional ℚ_[p] M] (hLvM : Lv (p := p) L ≤ M) :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ M ≤ E ∧
      Module.finrank ℚ_[p] E ≤
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) * Module.finrank ℚ_[p] M ∧
      ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
        G0Galois.resQ K σ' = decomp p σ →
          ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P :=
  torsFix_of_wildNF hR6.1 hTors hD hℓp q hq3 hpq M hLvM

end G15Ram

end

section D2A6WrapA6

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

/-- `modelG3G6_of_leaves3` on `R6U` (A6, L529-530; `D2A6.modelG3G6_of_leavesU` from the integral model; T5 unused). -/
theorem modelG3G6_of_leaves3U (hFS : G0Split.FibreSimple) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : D2A6.R6U) (hTors : PkgI2.TorsionStructure.{0}) :
    G0AssembleMod.ModelG3G6 :=
  D2A6.modelG3G6_of_leavesU hFS hNOS hRay.2

end HSyn

end

end D2A6WrapA6

section D2A6WrapKF

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

/-- `good_of_QML3` on `R6U` (the kernel field's `hgood`; L529-530): good reduction of a `QML3` object at every place
over every `p ∉ T` when `T` contains the primes `≤ 324` (`D2A6.hasGoodReduction_of_intModel`). -/
theorem good_of_QML3U (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (K : IF) [FiniteDimensional ℚ K] (PK : QML3 K)
    (T : Finset ℕ) (hT : D2A6.T324 ⊆ T) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, GlueB3Unram.LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar,
        PkgI2.HasGoodReduction (ObjBridge.toGrp PK.A) (w.comap (e : K →+* Qbar)) := by
  intro p hp hpT w hw e
  haveI : Fact p.Prime := ⟨hp⟩
  refine _root_.D2A6.hasGoodReduction_of_intModel hRay.2 PK _ p
    (D2A6.lt_of_notMem_T324 hp (fun h => hpT (hT h))) ?_
  intro hu
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hu
  have hc' : (p : Qbar) * e (c : K) = 1 := by
    have := congrArg (fun z : w.comap (e : K →+* Qbar) => e (z : K)) hc
    simpa using this
  have hcw : e (c : K) ∈ w := c.2
  have h1 : w.valuation (e (c : K)) ≤ 1 := (w.valuation_le_one_iff _).mpr hcw
  have h2 : w.valuation (p : Qbar) < 1 := hw
  have h3 := congrArg w.valuation hc'
  rw [map_mul, map_one] at h3
  have h4 : w.valuation (p : Qbar) * w.valuation (e (c : K)) < 1 :=
    mul_lt_one_of_lt_of_le h2 h1
  exact absurd h3 (ne_of_lt h4)

end G0ModField.KernelField

end D2A6WrapKF

end HDec

#print axioms HDec.G15Ram.raynaudPlace_of_R6U
#print axioms HDec.G15Ram.torsFix_of_R6U
#print axioms HDec.G15Ram.tateWildK_of_R6U
#print axioms HDec.HSyn.modelG3G6_of_leaves3U
#print axioms HDec.G0ModField.KernelField.good_of_QML3U

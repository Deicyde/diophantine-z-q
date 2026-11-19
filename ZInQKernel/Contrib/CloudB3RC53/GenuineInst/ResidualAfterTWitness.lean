import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterT2
import ZInQKernel.Contrib.RC53Assist.ResidualWitnessActive.Witness

/-!
# Genuine instantiations, part 23: the repaired after-`t` inputs at the peer's active witness

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4593–4647.

The peer's active witness (`RC53Assist/ResidualWitnessActive/Witness.lean`) builds the
smaller-support free model `afterP = 𝔽₂[[t]] ⊗ (residual cone)` over `𝔽₂[[t]]` (`bcG`) and its base
change `afterP' = 𝔽₂((t)) ⊗ afterP`. Here the inputs of `residualRankCounts_afterT'` /
`residualRankCounts_afterT''` (part 22) that concern these models are built:

* `bcG_toCC_iso_baseChangeCx`: for `C : GCx 𝔽₂[[t]]`, `(bcG 𝔽₂((t)) C).toCC` is isomorphic,
  **as a complex**, to `baseChangeCx (algebraMap 𝔽₂[[t]] 𝔽₂((t))) C.toCC` (identity components:
  Mathlib's algebra `𝔽₂[[t]] → 𝔽₂((t))` is the one induced by the ring map);
* `reductionIso`: for `C : GCx 𝔽₂`, the reduction `𝔽₂ ⊗_{𝔽₂[[t]]} (𝔽₂[[t]] ⊗_{𝔽₂} C)` of
  `bcG 𝔽₂[[t]] C` along `constantCoeff` is isomorphic **as a complex** to `C` (`cancelBaseChange`
  and `lid`, natural in the differentials: `reductionEquiv_natural`);
* at the witness: `witness_ered : baseChangeCx constantCoeff afterP ≅ (selCx actSel).toCC` and
  `witness_ebc : afterP' ≅ baseChangeCx (𝔽₂[[t]] → 𝔽₂((t))) afterP`;
* **the degree-`3` facts**: `witness_globalDegreeThreeVanishes` (`GlobalDegreeThreeVanishes actSel`,
  from Milne ADT I.4.10 through the peer's all-degree comparison `allGenHEquiv`, which this tree
  otherwise lacks) and `witness_eG3` (the identification of `actSel.G.X 3` with Mathlib's continuous
  `H³` used by `residualRankCounts_afterT''`). The rank of `afterP` in degree `3`
  (`2 · |Places(S)|`, the local `H²`) is the local part, counted by part 22's full degree range; it
  is not constrained by these facts.

**Remaining inputs for the full application** (not built here): `residualRankCounts_afterT'` sums
`hUm`, `hLm` over `[0, 3]` and needs `eG` over `[0, 2]`; the peer's `act_hUm`, `act_hLm` are over
their degrees `{0, 1, 2}`, so the degree-`3` terms (`actSel.U.X 3`, a subsingleton, and
`actSel.L.X 2`, the local `H²`) must be added to the bounds, together with the supports
`[0, 3]` of `afterP'` and of the generic minimal model `L`, and the finiteness instances of `L`, `P'`.

**Classification.** Definitions and PROVED statements.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open CategoryTheory TensorProduct ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.RC53Assist.ResidualWitnessActive

section General

/-- **`bcG` is `baseChangeCx` along the algebra map**, as complexes, for `𝔽₂[[t]] → 𝔽₂((t))` (whose
algebra structure is the one induced by the ring map). -/
def bcG_toCC_iso_baseChangeCx (C : GCx Rt) :
    (bcG Kt C).toCC ≅ baseChangeCx (algebraMap Rt Kt) C.toCC :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    have h : i + 1 = j := hij
    have hd : (C.toCC.d i j).hom = C.d i j h := LinearMap.ext (GCx.toCC_d_hom C i j h)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((C.toCC.d i j).hom.baseChange Kt) x = ((bcG Kt C).toCC.d i j).hom x
    rw [hd]
    exact (GCx.toCC_d_hom (bcG Kt C) i j h x).symm)

/-- `ε = constantCoeff` retracts `𝔽₂ → 𝔽₂[[t]]`. -/
theorem constantCoeff_algebraMap (x : ZMod 2) :
    (PowerSeries.constantCoeff : Rt →+* ZMod 2) (algebraMap (ZMod 2) Rt x) = x := by
  simp

/-- The degreewise reduction `𝔽₂ ⊗_{𝔽₂[[t]]} (𝔽₂[[t]] ⊗_{𝔽₂} X) ≅ X`. -/
def reductionEquiv (X : Type) [AddCommGroup X] [Module (ZMod 2) X] :
    letI := (PowerSeries.constantCoeff : Rt →+* ZMod 2).toAlgebra
    ZMod 2 ⊗[Rt] (Rt ⊗[ZMod 2] X) ≃ₗ[ZMod 2] X :=
  letI := (PowerSeries.constantCoeff : Rt →+* ZMod 2).toAlgebra
  haveI : IsScalarTower (ZMod 2) Rt (ZMod 2) :=
    IsScalarTower.of_algebraMap_eq fun x => (constantCoeff_algebraMap x).symm
  (AlgebraTensorModule.cancelBaseChange (ZMod 2) Rt (ZMod 2) (ZMod 2) X).trans
    (TensorProduct.lid (ZMod 2) X)

theorem reductionEquiv_tmul (X : Type) [AddCommGroup X] [Module (ZMod 2) X] (c : ZMod 2) (a : Rt)
    (x : X) :
    letI := (PowerSeries.constantCoeff : Rt →+* ZMod 2).toAlgebra
    reductionEquiv X (c ⊗ₜ (a ⊗ₜ x)) =
      ((PowerSeries.constantCoeff : Rt →+* ZMod 2) a * c) • x := by
  let := (PowerSeries.constantCoeff : Rt →+* ZMod 2).toAlgebra
  have : IsScalarTower (ZMod 2) Rt (ZMod 2) :=
    IsScalarTower.of_algebraMap_eq fun x => (constantCoeff_algebraMap x).symm
  change TensorProduct.lid (ZMod 2) X
    (AlgebraTensorModule.cancelBaseChange (ZMod 2) Rt (ZMod 2) (ZMod 2) X (c ⊗ₜ (a ⊗ₜ x))) = _
  rw [AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.lid_tmul, Algebra.smul_def]
  rfl

/-- The degreewise reduction is natural: `f ∘ e_X = e_Y ∘ (id ⊗ (id ⊗ f))`. PROVED. -/
theorem reductionEquiv_natural {X Y : Type} [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y]
    [Module (ZMod 2) Y] (f g : X →ₗ[ZMod 2] Y) (hg : g = f)
    (g' : Rt ⊗[ZMod 2] X →ₗ[Rt] Rt ⊗[ZMod 2] Y) (hg' : g' = f.baseChange Rt) :
    letI := (PowerSeries.constantCoeff : Rt →+* ZMod 2).toAlgebra
    g ∘ₗ (reductionEquiv X).toLinearMap = (reductionEquiv Y).toLinearMap ∘ₗ g'.baseChange (ZMod 2) := by
  let := (PowerSeries.constantCoeff : Rt →+* ZMod 2).toAlgebra
  subst hg hg'
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c y =>
    induction y using TensorProduct.inductionOn with
    | tmul a x =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
        LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, reductionEquiv_tmul,
        reductionEquiv_tmul, map_smul]
    | add y y' hy hy' =>
      rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- **The reduction modulo `t` of `bcG 𝔽₂[[t]] C` is `C`, as complexes.** -/
def reductionIso (C : GCx (ZMod 2)) :
    baseChangeCx (PowerSeries.constantCoeff : Rt →+* ZMod 2) (bcG Rt C).toCC ≅ C.toCC :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (reductionEquiv (C.X n)).toModuleIso)
    (fun i j hij => by
      have h : i + 1 = j := hij
      apply ModuleCat.hom_ext
      exact reductionEquiv_natural (C.d i j h) _ (LinearMap.ext (GCx.toCC_d_hom C i j h)) _
        (LinearMap.ext (GCx.toCC_d_hom (bcG Rt C) i j h)))

end General

section Witness

open ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.Limits

/-- **The reduction comparison at the witness** (`ered` of `residualRankCounts_afterT'`): the
reduction modulo `t` of the peer's `afterP` is the residual cone, as complexes. -/
def witness_ered :
    baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) afterP ≅
      (selCx actSel).toCC :=
  reductionIso (selCx actSel)

/-- **The base-change comparison at the witness** (`ebc` of `residualRankCounts_afterT'`): the peer's
`afterP'` is the base change of `afterP` to `𝔽₂((t))`, as complexes. -/
def witness_ebc :
    afterP' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) afterP :=
  bcG_toCC_iso_baseChangeCx afterP_G

/-- **The degree-`3` global vanishing holds at the witness** (`hG3` of `residualRankCounts_afterT'`):
from Milne ADT I.4.10 through the peer's all-degree comparison of genuine and Mathlib cohomology
(`smallGlobal_off`). PROVED. -/
theorem witness_globalDegreeThreeVanishes (h410 : MilneADT_I_4_10_totallyComplex) :
    GlobalDegreeThreeVanishes actSel := by
  have : Subsingleton (actSel.G.X 3) := smallGlobal_off h410 3 (Or.inr (by norm_num))
  exact Module.finrank_zero_of_subsingleton

/-- **The degree-`3` identification at the witness** (`eG3` of `residualRankCounts_afterT''`):
both sides vanish (the global term by `smallGlobal_off`, Mathlib's `H³` by Milne ADT I.4.10). -/
def witness_eG3 (h410 : MilneADT_I_4_10_totallyComplex) :
    actSel.G.X 3 ≃ₗ[ZMod 2]
      continuousCohomology 3 (Wrep SmallK (primesAboveSet SmallK (chargedPrimes 66 5 actD))) :=
  haveI : Subsingleton (actSel.G.X 3) := smallGlobal_off h410 3 (Or.inr (by norm_num))
  haveI : Subsingleton (continuousCohomology 3
      (Wrep SmallK (primesAboveSet SmallK (chargedPrimes 66 5 actD)))) :=
    h410 SmallK smallK_complex SmallS smallS_finite smallS_above_two
      (Wrep SmallK SmallS) inferInstance inferInstance
      (continuous_trivialRepS_action (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2)) 3
      (by norm_num)
  LinearEquiv.ofSubsingleton _ _

end Witness

end ZInQ.Contrib.CloudB3RC53.GenuineInst

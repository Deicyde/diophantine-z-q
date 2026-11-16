# mtcm-polar: the main theorem of CM for every lattice, from the polarized, maximal-order print

Task mtcm-polar (2026-11-15/16). Branch `wip/mtcm-polar` (base 43513d87 + merges of `wip/qmrec-printed` a05c57ef and
`wip/hcm-printed` 15055182, both clean). Contributor file: `ZInQKernel/Contrib/OneProof/MainCMPolar.lean` (50 KB,
namespace `MainCMPolar`; imports `ZInQKernel.Contrib.OneProof.ShimuraMainCMPrinted`, `ZInQKernel.Contrib.FrobChain.Rigidity`,
`Mathlib.Analysis.Complex.Cardinality`). Log: `scratch/mtcm-polar/log.md`.

## Result

`HcmPrinted.MainTheoremCMArith` (hcm-printed) and `QMRecPrinted.MainTheoremCM` (qmrec-printed) are proved in Lean, for
**every** lattice `𝔞 ⊂ E` and **without** a polarization hypothesis. They follow from:

* the main theorem in the strict reading: only polarized structures `(A, C, θ)` of type `(E, Φ; 𝔞, ζ)` with `𝔞` a
  fractional `𝓞_E`-ideal (`MainTheoremCMPolMax`, sign `ε = 1`; or `MainTheoremCMPol`, sign existential);
* Shimura's existence theorem for polarized CM abelian varieties of a given type (`CMAbVarExists`);
* the textbook leaves `UniformizationLeafAll` and `GAGAMorphism` (already bundle fields; they give `HomLatticeCorr` by
  `AvSplit.Final.h69`).

The task's three steps:
1. The print is stated in `MainTheoremCMPolMax` / `MainTheoremCMPol`.
2. Every lattice of the leaf's shape gets a Riemann form, in Lean: `exists_zeta` (ζ̄ = −ζ, Im φᵢ(ζ) > 0, by weak
   approximation) scaled into `𝓞_E`.
3. Arbitrary multiplier rings reduce to `𝓞_E`, in Lean (`mainTheoremCMSign_of_polar`), through the isogeny
   `μ : B₀ = ℂ^g/Φ(N𝓞_E) → A` and its conjugate `μ^σ : B₀^σ → A^σ`.

All theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound` (VERIFIED). No statement of the kernel or
of the merged files was changed.

### New leaves

`MainTheoremCMPolSign ε` is, by `diff`, exactly `HcmPrinted.MainTheoremCMSign ε` with one added line (VERIFIED):
`IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →`. `MainTheoremCMPolMax` is its `ε = 1` instance with `N(s)` written
for `N(s)^((1:ℤˣ):ℤ)` (`polSign_one_of_polMax`).

```lean
def IsOLattice (𝔞 : AddSubgroup E) : Prop :=
  (∀ o : 𝓞 E, ∀ x ∈ 𝔞, (o : E) * x ∈ 𝔞) ∧
  (∃ c : ℕ, 0 < c ∧ ∀ o : 𝓞 E, (c : E) * o ∈ 𝔞) ∧
  (∃ d : ℕ, 0 < d ∧ ∀ x ∈ 𝔞, IsIntegral ℤ ((d : E) * x))

def IsRiemannDatum {g : ℕ} (Φ : Fin g → E →+* ℂ) (𝔞 : AddSubgroup E) (ζ : E) : Prop :=
  IsCMField.complexConj E ζ = -ζ ∧ (∀ i, 0 < (Φ i ζ).im) ∧
  ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ∃ n : ℤ, Algebra.trace ℚ E (ζ * x * IsCMField.complexConj E y) = n

def MainTheoremCMPolMax : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞))
      θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈
          latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

def MainTheoremCMPolSign (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

def MainTheoremCMPol : Prop := ∃ ε : ℤˣ, MainTheoremCMPolSign ε

def CMAbVarExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ 𝔟 : AddSubgroup E, IsOLattice 𝔟 → (∃ ζ : E, IsRiemannDatum Φ 𝔟 ζ) →
  ∃ (B : PkgI3.AbVar ℂ) (θ : (Fin g → ℂ) → CPts B (RingHom.id ℂ)),
    B.dim = (g : WithBot ℕ∞) ∧ IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔟) θ
```

**Ratings.**

| leaf | rating | reason |
| --- | --- | --- |
| `MainTheoremCMPol` | printed form | Shimura 1971 Thm 5.15 (§5.5), Shimura 1998 Thm 18.6, restricted to polarized structures of type `(E, Φ; 𝔞, ζ)` with `𝔞` an `𝓞_E`-ideal: the strictest reading the review raised. Further weakenings: the sign is existential; the polarization `C` enters through its Riemann form `Tr(ζ x ȳ)` (Riemann forms on `A(ℂ)` ↔ polarizations, Mumford *Abelian varieties* §2–3); the clauses on `C^σ`, on the type of `(A^σ, θ')` and on the uniqueness of `θ'` are dropped. Implied by the old leaf (`mainTheoremCMPol_of_mainTheoremCM`). Flag **reading risk**: is Thm 18.6 / 5.15 printed for arbitrary (non-primitive) CM types? The consumers use the induced type of `E = K(√2)`. I believe the theorem is general, because Shimura proves it for every structure of type `(K, Φ)`, but this is UNVERIFIED (no network). |
| `MainTheoremCMPolMax` | printed form, with hcm-printed's flag | `MainTheoremCMPol` at `ε = 1`. It keeps hcm-printed's **pending reading** of the normalization of `[s, K]` against Tau Ceti's arithmetic Artin map, which `T5Glue.ShimuraMainCM` already assumes, plus the same primitivity reading risk. Needed only for the `hCM` route, which fixes the arithmetic direction. |
| `CMAbVarExists` | printed form | Shimura 1998 §6.2 (Shimura–Taniyama §6.2): existence of a polarized abelian variety of type `(K, Φ; 𝔞, ζ)`. Equivalently, Riemann's theorem (a complex torus with a Riemann form is an abelian variety, Mumford §3) plus GAGA. Weaker than the print: only `𝓞_E`-ideal lattices, and only `B`, `dim B = g` and a uniformization by `Φ(𝔟)` are kept (`C` and `θ` are dropped). It is an existence statement, so it is not vacuous, and it is true for every lattice. |

Sign conventions do not matter here. The conclusions never mention `ζ`, and the integrality clause is symmetric under
`ζ ↦ −ζ`. So `∃ ζ, IsRiemannDatum` is equivalent to the existence of a Riemann datum under the opposite sign convention.

### Theorems (statements verbatim; all in namespace `MainCMPolar`)

```lean
theorem mainTheoremCMSign_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    HcmPrinted.MainTheoremCMSign ε

theorem mainTheoremCMArith_of_polar (hP : MainTheoremCMPolMax) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    HcmPrinted.MainTheoremCMArith

theorem mainTheoremCM_of_pol (hP : MainTheoremCMPol) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    QMRecPrinted.MainTheoremCM

theorem mainTheoremCM_of_polar (hP : MainTheoremCMPolMax) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    QMRecPrinted.MainTheoremCM

theorem qmReciprocityL3_of_pol (hP : MainTheoremCMPol) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3

theorem rayClassCMAb_of_polar (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : MainTheoremCMPol)
    (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) :
    ShimuraGlue.Ray.RayClassCMAb

theorem shimuraMainCM_of_polar (hP : MainTheoremCMPolMax) (hX : CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization) (hWP : HcmPrinted.WeierstrassParam)
    (hWA : HcmPrinted.WeierstrassAbVar) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) : T5Glue.ShimuraMainCM

theorem mainTheoremCMPolMax_of_arith (h : HcmPrinted.MainTheoremCMArith) : MainTheoremCMPolMax

theorem mainTheoremCMPol_of_mainTheoremCM (h : QMRecPrinted.MainTheoremCM) : MainTheoremCMPol

theorem mainTheoremCMPol_of_polMax (h : MainTheoremCMPolMax) : MainTheoremCMPol

theorem exists_zeta {g : ℕ} (Φ : Fin g → E →+* ℂ)
    (hinj : Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i))) :
    ∃ ζ : E, IsCMField.complexConj E ζ = -ζ ∧ ∀ i, 0 < (Φ i ζ).im

theorem lattice_of_unif (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) {g : ℕ}
    (Φ : Fin g → E →+* ℂ) (hg : 0 < g) (hdeg : Module.finrank ℚ E = 2 * g)
    {A : PkgI3.AbVar ℂ} {𝔞 : AddSubgroup E} {θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)}
    (hθ : IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ) :
    (∃ N : ℕ, 0 < N ∧ ∀ o : 𝓞 E, (N : E) * o ∈ 𝔞) ∧
    (∃ d : ℕ, 0 < d ∧ ∀ x ∈ 𝔞, IsIntegral ℤ ((d : E) * x))
```

### `#print axioms` (`scratch/mtcm-polar/Axioms.lean`, output `axioms.txt`)

```
'MainCMPolar.mainTheoremCMSign_of_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.mainTheoremCMArith_of_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.mainTheoremCM_of_pol' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.mainTheoremCM_of_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.qmReciprocityL3_of_pol' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.rayClassCMAb_of_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.shimuraMainCM_of_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.mainTheoremCMPolMax_of_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.mainTheoremCMPol_of_mainTheoremCM' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.mainTheoremCMPol_of_polMax' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.exists_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainCMPolar.lattice_of_unif' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `#discharges` (`scratch/mtcm-polar/Discharges.lean`, output `discharges.txt`)

```
DISCHARGES [OpenResearchLeaves22.gonzalezRotgerProp56X6] by GRCountX6.prop56X6_of_r5fpCount
  still assumes: [LeafQM.AV.R5fpCount]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.neronBaseChangeStrictHenselization] by GapSHPair.neronBaseChangeStrictHenselization_of_unramified
  still assumes: [ReductGlue.NeronBaseChangeUnramifiedDVR]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.elkiesX6StarPrinted] by HDec.QMSplit.Moduli.ElkiesX6Star.elkiesX6StarPrinted_of_ab
  still assumes: [HDec.QMSplit.Moduli.ElkiesEquationsX6Ab]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hCM] by HcmPrinted.shimuraMainCM_of_printed
  still assumes: [HcmPrinted.MainTheoremCMArith,
 HcmPrinted.WeierstrassUniformization,
 HcmPrinted.WeierstrassParam,
 HcmPrinted.WeierstrassAbVar,
 ZInQ.HomUnify.HomLatticeCorr]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hCM] by HcmPrinted.shimuraMainCM_of_textbook
  still assumes: [HcmPrinted.MainTheoremCMArith,
 HcmPrinted.WeierstrassUniformization,
 HcmPrinted.WeierstrassParam,
 HcmPrinted.WeierstrassAbVar,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hCM] by MainCMPolar.shimuraMainCM_of_polar
  still assumes: [MainCMPolar.MainTheoremCMPolMax,
 MainCMPolar.CMAbVarExists,
 HcmPrinted.WeierstrassUniformization,
 HcmPrinted.WeierstrassParam,
 HcmPrinted.WeierstrassAbVar,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.r16CoreY] by R16Split.coreY_of_r16
  still assumes: [LeafModCurves.R16_EichlerShimuraJ1']
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.sga7_IX_3_3_SH] by SGA7PersistsNF.sga7_IX_3_3_SH_of_field
  still assumes: [CToPrinted.SGA7_IX_3_3]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.sga7_IX_3_5_ForwardGeom] by UnipotentForward.forwardGeom_of_forward
  still assumes: [UnipotentForward.SGA7_IX_3_5_Forward, UnipotentForward.SemiAbelianDescendsSepClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.mumfordGroupLaw] by ZInQ.Contrib.MumfordRigidity.mumfordGroupLaw_of_core
  still assumes: [LeafQM.AV.R1UnivRigid.MumfordRigidityCore]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 2196 theorems checked, 10 discharge one
```

On this base no bundle field consumes `MainTheoremCM`. `rayClassCMAb` was removed by leaf-fold22 (TailZ34.lean:7), and
`qmReciprocityL3` enters only with shimura-split2's fold. So the one current discharge is `hCM`, a `frozenTarget`
argument.

## Fold

`python3 scripts/one_proof/autofold.py SPEC --dry-run` refuses all three specs (VERIFIED, outputs `*-dryrun.txt`):
* `scratch/mtcm-polar/autofold.json`: field `hCM`; refused with "not a field of the current bundles: ['hCM']".
* `autofold-after-split2.json`: field `qmReciprocityL3`, replacing qmrec-printed's spec of the same name.
* `autofold-after-qmrec.json`: field `mainTheoremCM`, after qmrec-printed's fold.

The last two name fields that exist only after those folds. So the fold of `hCM` is manual.

**Manual fold of `hCM`** (one consumer):
* `ZInQKernel/OneProof/Main.lean:64`: delete the binder `(hCM : _root_.T5Glue.ShimuraMainCM)` and add
  `(hP : MainCMPolar.MainTheoremCMPolMax) (hE : MainCMPolar.CMAbVarExists) (hWU : HcmPrinted.WeierstrassUniformization)
  (hWP : HcmPrinted.WeierstrassParam) (hWA : HcmPrinted.WeierstrassAbVar)`.
* `ZInQKernel/OneProof/Main.lean:70`: replace `hCM` in `_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX` with
  `(MainCMPolar.shimuraMainCM_of_polar hP hE hWU hWP hWA t.uniformizationLeafAll t.gagaMorphism)`.

The three Weierstrass leaves are hcm-printed's, with their ratings and flags; their spec rows are copied into
`autofold.json`. The check `scratch/mtcm-polar/FoldCheck.lean` compiles with standard axioms (VERIFIED,
`foldcheck_output.txt`):

```lean
import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.MainCMPolar

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus in
/-- `frozenTarget` with `hCM` replaced by mtcm-polar's two leaves, hcm-printed's three Weierstrass leaves and the
bundle's textbook fields (`shimuraMainCM_of_polar`). -/
theorem frozenTarget_mtcmPolar
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hP : MainCMPolar.MainTheoremCMPolMax) (hE : MainCMPolar.CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization)
    (hWP : HcmPrinted.WeierstrassParam) (hWA : HcmPrinted.WeierstrassAbVar)
    (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29
    (MainCMPolar.shimuraMainCM_of_polar hP hE hWU hWP hWA t.uniformizationLeafAll t.gagaMorphism)
    hX h33 hFH hL3

#print axioms frozenTarget_mtcmPolar
```

If hcm-printed's manual fold lands first (`hCM` replaced by `hM : HcmPrinted.MainTheoremCMArith` and the Weierstrass
leaves), replace the binder `hM` by `hP hE` and the term `hM` by
`(MainCMPolar.mainTheoremCMArith_of_polar hP hE t.uniformizationLeafAll t.gagaMorphism)`.

On the qmrec route, after shimura-split2's fold use `autofold-after-split2.json`, which proves `qmReciprocityL3` by
`qmReciprocityL3_of_pol {n}.mainTheoremCMPol {n}.cmAbVarExists {t}.uniformizationLeafAll {t}.gagaMorphism`; it
supersedes qmrec-printed's spec. If qmrec-printed's `mainTheoremCM` is already a field, use `autofold-after-qmrec.json`.

## Independent statement review

A read-only reviewer subagent checked the statements without running Lean (`scratch/mtcm-polar/review.md`). It found
no soundness problem: all three leaves are true, and each is weaker than its print.
* `IsOLattice` holds exactly for nonzero fractional ideals.
* `∃ ζ, IsRiemannDatum` is never vacuous, by `exists_zeta`.
* No coercion traps (`1 ⊗ₜ y` is `includeRight y`).
* The `MainTheoremCMPolSign` diff matches `MainTheoremCMSign` plus the one added line.
* `CMAbVarExists` follows from Shimura §6.2 or from Riemann's theorem plus GAGA.

It made one wording point: nothing ties `ζ` to a given polarization of `A`. The `MainTheoremCMPolMax` docstring now says
"`A` admits, via `θ`, a polarization of type `ζ`". It also suggested citing Milne, *Complex multiplication*, §9
(UNVERIFIED locator), for the non-primitive case, and that citation was added to the docstring.

## Method

**(2) Riemann form** (`exists_zeta`, §3):
* `E` is CM, so `complexConj E ≠ 1`, and some `β = α − ᾱ ≠ 0` has `β̄ = −β`. Each `φᵢ(β)` is then purely imaginary and
  nonzero (Mathlib's `complexEmbedding_complexConj`).
* The places `wᵢ = mk(φᵢ)` are pairwise distinct: by `InfinitePlace.mk_eq_iff`, `mk φ = mk ψ` means `ψ = φ` or
  `ψ = φ̄`, which the type's injectivity hypothesis excludes.
* Weak approximation (`AbsoluteValue.denseRange_algebraMap_pi`) gives `x ∈ E` with `|φᵢ(x) − ±φᵢ(β)| < |Im φᵢ(β)|/2`,
  signs chosen so that every `Im φᵢ(x) > 0`.
* Take `ζ = x − x̄`. In the main proof `ζ` is scaled by `y²` (`y ≠ 0`, `y • ζ` integral) into `𝓞_E`. Then
  `Tr(ζ x ȳ) ∈ ℤ` on `N𝓞_E` (`Algebra.isIntegral_trace`; `ℤ` is integrally closed).

**The lattice of a uniformization** (`lattice_of_unif`, §2). Start from `ψ : ℂ^{g'} → A(ℂ)` with full lattice `Λ'`
(`UniformizationLeafAll`, `exists_isUniformization_of_leaf`):
* `analyticHomLiftC_of_leaf` gives linear `M`, `M'` with `θ ∘ M = ψ` and `ψ ∘ M' = θ`.
* `M'M − 1` and `MM' − 1` take values in the countable sets `Λ'` and `Φ(E)`, so they vanish
  (`linear_eq_zero_of_countable`). Hence `Φ(𝔞) = M(Λ')`.
* `Λ'` is finitely generated, so `𝔞` is (`fg_of_fg_map_injective`), and `d𝔞 ⊆ 𝓞_E` (`exists_integral_multiples`).
* `span_ℝ Φ(𝔞) = ℂ^g` gives `dim_ℚ span_ℚ 𝔞 ≥ 2g`, by `finrank_range_le_card` on a ℚ-basis. So `span_ℚ 𝔞 = E`, and
  `N𝓞_E ⊆ 𝔞` via an integral basis.

**(3) The isogeny argument** (`mainTheoremCMSign_of_polar`, §5). Put `𝔟 = N𝓞_E ⊆ 𝔞` and `m = Nd`, so `m𝔞 ⊆ 𝔟`.
* `𝔟` is an `𝓞_E`-lattice with Riemann datum `y²ζ`. `CMAbVarExists` gives `B₀` with `θ_B : ℂ^g/Φ(𝔟) ≅ B₀(ℂ)`.
* `HomLatticeCorr` (realization) gives the type of `B₀` (`IsOfType`, from multiplication by `Φ(e)`) and the isogeny
  `μ : B₀ → A` with `μ ∘ θ_B = θ` (from `M = id`, since `Φ(𝔟) ⊆ Φ(𝔞)`).
* The print applied to `B₀` and `B₀^σ = bcC B₀ σ` (hcm-printed's `isPullback_bc`, `one_left_bc`) gives `θ'_B`.
* `μ^σ : B₀^σ → A'` is the lift through the given pullback square of `A'`. It preserves the identity (`one_left`,
  `hone`), so it is a homomorphism by rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`).
* Put `θ' = μ^σ ∘ θ'_B`. `key` gives `θ'(u)` over `A`: `σ(dd(θ'_B u) ≫ μ)`.
  * Analytic: `isAnalyticHom_comp`.
  * Surjective: from that of `θ`, of `dd` and of `θ'_B`.
  * Torsion relation: `𝔞̂ = 𝔞 + 𝔟̂` (`latHat_decomp`) moves `x` by an element of `𝔞` into `x₀` with `ty − x₀ ∈ 𝔟̂`; then
    the relation for `B₀` applies.
  * Kernel, `⊇`: the same argument.
  * Kernel, `⊆`: `dd(θ'_B z)` lies in `ker μ = θ_B(Φ(𝔞))` and is `m`-torsion. So `mz ∈ Φ(t⁻¹𝔟)` and `z = Φ(y)`. The
    density of `E` in `𝔸_f ⊗ E` mod `𝔟̂` (`exists_approx_latHat`) gives `x` with `ty − x ∈ 𝔟̂`, and comparing
    `θ_B(Φx) = θ_B(Φx₀)` gives `ty ∈ 𝔞̂`.
* The sign `ε` plays no role: `t` is any unit. So the same proof gives every `MainTheoremCMSign ε`, hence both the
  `ε = 1` form and the existential form.

## What remains

* The reading of the primitivity question for `MainTheoremCMPol` / `MainTheoremCMPolMax`: are Shimura's Thm 18.6 / 5.15
  printed for non-primitive CM types? If not, a reduction from an induced type `(E, Φ) = Ind(K, Ψ)` to `(K, Ψ)` is
  needed. That means `A ∼ B^m`, products of uniformizations, and the reflex norm of an induced type. It is not done.
* hcm-printed's normalization reading (`ε = 1`), only for the `hCM` route.
* The folds (integration lead).

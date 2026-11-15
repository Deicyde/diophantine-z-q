# sgr-split: `shimuraGoodReductionNoGuard` reduced to the printed integral model of the Shimura curve

## 1. Result

The added field `shimuraGoodReductionNoGuard` (`HDec.CurveSplitGR.ShimuraGoodReductionNoGuard`,
`ZInQKernel/OneProof/H/TailW.lean` line 739; kind composite, strict GLUE) is now **proved in Lean from one
printed leaf** (compiled, standard axioms):

```lean
theorem SGRSplit.shimuraGoodReductionNoGuard_of_printed (hRep : ShimuraIntegralModelRep) :
    HDec.CurveSplitGR.ShimuraGoodReductionNoGuard
```

in `ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean` (the one file this task adds under
`ZInQKernel/`). The leaf:

| new hypothesis | what it says | kind | strict |
|---|---|---|---|
| `SGRSplit.ShimuraIntegralModelRep` | for every prime `p > 324`, the moduli problem of abelian surfaces with QM by the maximal order `𝒪` of the quaternion algebra of discriminant 6 and full level-3 structure, on locally noetherian `ℤ_(p)`-schemes, is representable by a proper smooth curve over `ℤ_(p)` (Kottwitz 1992 §5; Buzzard 1997; Morita 1981) | published, flagged **pending reading** (§2.2) | GLUE until read |

Everything else is proved here, from Mathlib and the kernel: the clause-by-clause glue (Yoneda for the Hecke
clauses, uniqueness for injectivity, existence for surjectivity), uniqueness of fibres up to isomorphism,
objects over a field as abelian schemes over `Spec K`, fibres of a QM abelian scheme at field points as
objects, and three general facts that Mathlib v4.35 does not state but the kernel's contributions make
provable: an abelian surface is smooth of relative dimension 2; a smooth, geometrically connected scheme over a
field is geometrically integral; `End` of an abelian variety in characteristic 0 is torsion-free (§4).

**Verdict on curve-split §3.6** ("not statable in published form today"): no longer true. The printed
theorem, representability of the integral moduli problem, is statable over genuine definitions now that the
kernel has r1univ-rigid's `LeafQM.AV.R1UnivRigid.QMAbScheme S`: an abelian scheme over any scheme `S` (a group
object of `Over S`, proper, smooth of relative dimension 2, geometrically connected) with a unital ring map
`𝒪 → End_S(A)` and a level-3 map `η : 𝒪 → A(S)`. Of the five missing definitions listed in curve-split §3.6,
four now exist or have a faithful encoding (§3); the fifth, polarizations over a base, is not needed for the
polarization-free form (it enters only the comparison with Kottwitz's PEL form).

**The other routes named in the task do not give the field.** The Néron–Ogg–Shafarevich leaf `r7a`
(`PkgI2.NeronOggShafarevich`) and the Néron/BLR leaves are statements about models of *abelian varieties*
over a DVR (or a Dedekind base); VERIFIED by reading the Lean statements (`ZInQKernel/HDecomp/Objects.lean`
lines 861 and 1377). The field's core content is a smooth proper model of the *curve* `Y₃` over `ℤ_(p)`
carrying the family. NOS cannot produce the model of the curve, and even given one, extending the universal
abelian surface over the 2-dimensional regular base `𝒴` needs purity for abelian schemes (Faltings–Chai V.6.8,
Vasiu–Zink; UNVERIFIED), which is not in the bundle. Morita, Buzzard and Carayol obtain good reduction from the
moduli interpretation, i.e. from representability (SPECULATIVE as a description of their proofs, which this
task could not read).

**Counts.** The fold that discharges the field (autofold spec `scratch/sgr-split/autofold.json`) replaces the
composite GLUE row by the printed leaf, which counts GLUE while it is flagged pending reading: strict counts
46 LEAF / 13 GLUE on 59 fields before and after (strictest 45/14 before and after), so `autofold.py` accepts it
without `--allow-rise` (dry run checked, §5). When a reading clears the flag, the strict GLUE count drops to 12.

## 2. The printed leaf

### 2.1 Statement (`ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean`)

```lean
def QMFamFibre {S T : Scheme.{0}} (𝒜 : QMFamily T) (g : S ⟶ T) (𝒜' : QMFamily S) : Prop :=
  ∃ h : 𝒜'.F.left ⟶ 𝒜.F.left, IsPullback h 𝒜'.F.hom 𝒜.F.hom g ∧
    (∀ a : O, 𝒜'.iota a ≫ h = h ≫ 𝒜.iota a) ∧ (∀ a : O, 𝒜'.eta a ≫ h = g ≫ 𝒜.eta a)

def ShimuraIntegralModelRepAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMAbScheme 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of (Zloc p)))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbScheme S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

def ShimuraIntegralModelRep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraIntegralModelRepAt p
```

`QMFamFibre 𝒜 g 𝒜'` says `𝒜' ≅ g^*𝒜` compatibly with `ι` and `η` (it is the kernel's `IsFibreOf` over an
arbitrary base). For abelian schemes it is the isomorphism relation of the moduli problem: the isomorphism
carries `η'(0)` (the identity) to `η(0)`, so it is a homomorphism by rigidity (Mumford, *GIT*, Cor. 6.4;
UNVERIFIED number). So `ShimuraIntegralModelRepAt p` says: every object over a locally noetherian
`ℤ_(p)`-scheme `S` is the pullback of the universal object along exactly one `ℤ_(p)`-morphism `S → 𝒴`.

### 2.2 Sources and form (locators UNVERIFIED; no network)

* R. Kottwitz, *Points on some Shimura varieties over finite fields*, J. AMS 5 (1992), 373–444, §5: the PEL
  moduli problem with neat `K^p` and hyperspecial `K_p` is representable by a smooth quasi-projective scheme
  over `𝒪_E ⊗ ℤ_(p)`, proper when `B` is a division algebra. Here `E = ℚ`, `p ∤ 6`, `K_p = 𝒪_p^× ≅ GL₂(ℤ_p)`,
  `K^p = K₃ × ∏ 𝒪_ℓ^×` with `K₃` the full level-3 subgroup at `3 ∣ D` (allowed: `3 ≠ p`). The bibliographic
  identity is established in `docs/research/locators.md` row R1; §5 is unread.
* K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), 591–612, §§1–4: the
  polarization-free problem `(A, ι, level)` is representable by a smooth proper curve away from `D·level`.
* Y. Morita, *Reduction modulo 𝔓 of Shimura curves*, Hokkaido Math. J. 10 (1981), 209–238: good reduction of
  the curve and its QM abelian surfaces at `p ∤ D·level`.
* H. Carayol, Compositio Math. 59 (1986), 151–230: its construction is for totally real `F ≠ ℚ`; secondary.

The Lean statement is a consequence of these, never stronger:

1. only `p > 324` (printed: `p ∤ 6`), only locally noetherian `S` in universe 0;
2. `QMAbScheme`'s `η` (with `eta_three`, `eta_ker`) is the same datum as an `𝒪`-linear isomorphism
   `(𝒪/3𝒪)_S ≅ A[3]` when `3` is invertible on `S`: a fibrewise injective map of finite étale group schemes of
   degree 81 is an isomorphism (STANDARD);
3. the determinant condition of the PEL problem is automatic since `𝒪 ⊗ ℤ_p ≅ M₂(ℤ_p)` (STANDARD);
4. polarizations: Kottwitz's objects carry a polarization; by the relative Lemma P (for the fixed Rosati type
   the principal polarization of `(A, ι)` exists and is unique; Boutot–Carayol, Astérisque 196–197 (1991),
   III §1, UNVERIFIED) the two functors agree; Buzzard's form has no polarization.

Flag (pending reading): whether Buzzard's or Morita's printed level structures include a prime dividing `D`
(Kottwitz's do: only `K_p` must be hyperspecial), and the comparison 4 for Kottwitz's PEL form, including the
passage from Kottwitz's `K^p`-orbits of rational level structures to integral ones. This is the human check
curve-split §3.6 already asked for.

### 2.3 Not vacuous, not stronger

The leaf asserts an object `𝒴` with a universal property over all objects; objects exist (e.g. the CM objects
over `ℚ̄` from `R1R2fp`, converted by `qml3AsQMAb_of`), so `𝒴` has `ℚ̄`-points. It quantifies over genuine
abelian schemes (`QMAbScheme`, group law included), not over `QMFamily` (curve-split's objection to a
`QMFamily` universal property, which would assert more than the printed functor, does not apply).

## 3. Status of curve-split's five missing definitions

| curve-split §3.6 item | now |
|---|---|
| 1. abelian schemes over `S` | `QMAbScheme S`: `GrpObj F`, proper, smooth of relative dimension 2, `GeometricallyConnected` |
| 2. `𝒪 → End_S(A)` | `iota_hom`, `iota_one`, `iota_mul`, `iota_add` |
| 3. `A[3] ≅ (𝒪/3𝒪)_S` | encoded by `η : 𝒪 → A(S)` with `eta_three`, `eta_ker` (equivalent when `3 ∈ 𝒪_S^×`, §2.2 item 2) |
| 4. polarizations over `S` | not defined; not needed for the polarization-free form; enters the form argument only |
| 5. moduli functor, representability | `QMFamFibre` + `∃!` (`ShimuraIntegralModelRepAt`) |

## 4. The Lean reduction

All in `ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean` (namespace `SGRSplit`). The scratch
files hold the same proofs in pieces: `scratch/sgr-split/SGR.lean` (namespace `HDec.SGRSplit`: the reduction,
G2, G3, `abVarSurfaceRelDim`), `G1.lean` (G1 from the two general facts), `L1.lean` and `L2.lean` (the two
general facts).

* `shimuraGoodReductionNoGuard_of_rep : ShimuraIntegralModelRep → QMAbFieldFibre → QML3AsQMAb →
  FibreClassUnique → ShimuraGoodReductionNoGuard`. Clause by clause, with `(𝒴, 𝒜)` from the leaf and the
  family `𝒜.toQMFamily`:
  - proper, smooth: from the leaf;
  - fibre clause: G1 (`QMAbFieldFibre`);
  - injectivity on `ℚ̄`-points: convert `P` to a `QMAbScheme` over `Spec ℚ̄` (G2); both `y` and `y'` classify it
    (`isFibreOf_of_iso` transports `IsFibreOf` along `P ≅ P'`; `spec_to_Zloc_ext`: maps `Spec R → Spec ℤ_(p)`
    are unique), so `y = y'` by uniqueness;
  - surjectivity: existence for the `QMAbScheme` of `P` over `Spec ℚ̄` (structure map `zlocTo`);
  - Hecke clauses (Yoneda): `twistAb 𝒜 α` (`ι ∘ α`, `η ∘ α`) and `rightMulAb 𝒜 u` (`η(· u)`) are
    `QMAbScheme`s over `𝒴`; their classifying maps `g_α`, `g_{α⁻¹}` are inverse (uniqueness against the
    identity, `qmFamFibre_comp`, `qmFamFibre_id`), and pasting pullback squares shows the fibre at `y ≫ g_α` is
    `P.twist α` (resp. `P.rightMul u`); G3 identifies it with the given `P'`.
* `fibreClassUnique : FibreClassUnique` (G3): the pullback isomorphism of two fibres is `𝒪`-equivariant and
  respects `η` (pullback uniqueness) and carries the identity to the identity (`eta_left_comp`, after
  r1univ-rigid's `isGrpFibre_of_rigidity`), so it is a homomorphism by `G0FibreSimple.rigidityHom`.
* `qml3AsQMAb_of : AbVarSurfaceRelDim → QML3AsQMAb` (G2): `P.A.X` with `ι`, `η` is a `QMAbScheme` over `Spec K`;
  `GeometricallyConnected` from `GeometricallyIrreducible`; the ring and level identities from `QMStr`,
  `Level3`; `eta_ker` at an arbitrary field point `Spec K' → Spec K` because that map is an epimorphism
  (`epi_spec_field`, Mathlib's `Flat.epi_of_flat_of_surjective`).
* `abVarSurfaceRelDim : AbVarSurfaceRelDim`: at `x`, Mathlib's `Smooth.exists_isStandardSmooth` gives a standard
  smooth chart of some relative dimension `d`; the chart has a closed point `z` (`A` is Jacobson); `d =
  dim 𝒪_{A,z}` (`ZInQ.Contrib.Dim.ringKrullDim_stalk_of_chart`) `= dim A`
  (`topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth`, `A` irreducible) `= 2`.
* `smoothGeomConnIntegral : SmoothGeomConnIntegral`: a base change `Z` of a smooth, geometrically connected
  `X → Spec K` to a field is smooth and connected; its stalks are domains (the kernel's vendored
  `Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`,
  `ZInQKernel/Contrib/CloudW03NeronSurj/Vendor/Theorems/`), so it is irreducible (Tau Ceti's
  `irreducibleSpace_of_connected_of_isDomain_stalk`) and reduced (r1univ-rigid's `isReduced_of_smooth`), hence
  integral.
* `abVarEndTorsionFree : AbVarEndTorsionFree` (characteristic 0): `n • f = 0` gives `[n] ≫ f = [n] ≫ 1`;
  `[n]` is surjective (the kernel's `ZInQ.Contrib.AbVarBC.mulIsogeny`, proved from Mathlib), hence dominant,
  and `A` is reduced, so `f = 1` (`ext_of_isDominant_of_isSeparated`).
* `qmAbFieldFibre_of : SmoothGeomConnIntegral → AbVarEndTorsionFree → QMAbFieldFibre` (G1): the fibre
  `A_y = (Over.pullback y).obj A` with Mathlib's `Functor.grpObjObj` group law is an abelian variety
  (`fibreAbVar`: proper and smooth of relative dimension 2 by base change, geometrically connected by base change
  of `geomConn`, geometrically integral by `SmoothGeomConnIntegral`) of dimension 2
  (`ringKrullDim_stalk_of_smoothOfRelativeDimension` at a closed point); `ι` pushes forward to a ring map
  `𝒪 → End(A_y)` (`Functor.map_comp`, `Functor.map_mul`, `Functor.map_one` for the monoidal functor
  `Over.pullback y`; `ι(0) = 1` from `iota_add`); the level points are `cpt ≫ (Over.pullback y).map (η(a))`
  (additive by `MonObj.comp_mul`, `0 ↦ 1` by `one_eq`, kernel `3𝒪` by `eta_ker` at `y`); `ι` is injective
  because `ι(d) = 0 ⇒ η(d) = η(1) ∘ ι(d) = 0 ⇒ d ∈ 3𝒪`, and `End` is torsion-free, so the kernel lies in
  `⋂_k 3^k 𝒪 = 0` (`O_eq_zero_of_forall_dvd`, in the `ofInt` coordinates); the fibre square is
  `IsPullback.of_hasPullback`. `qmAbFieldFibre` applies it to the two proved facts.
* `shimuraGoodReductionNoGuard_of_printed`, the discharge: `_of_rep` with `qmAbFieldFibre`,
  `qml3AsQMAb_of abVarSurfaceRelDim` and `fibreClassUnique`.

### What remains

* The reading flagged in §2.2 (level structure at `3 ∣ D` in the printed theorems; the PEL comparison). Until
  then the leaf counts GLUE.
* Nothing else: no glue of this reduction is open.

## 5. What compiles (all VERIFIED by compiling)

| file | contents | result |
|---|---|---|
| `ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean` | the deliverable | `lake build +ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard`: success |
| `scratch/sgr-split/SGR.lean` | same development in `HDec.SGRSplit` | `lake env lean`: no errors |
| `scratch/sgr-split/G1.lean` | G1 from `SmoothGeomConnIntegral`, `AbVarEndTorsionFree` (namespace `SGRG1`) | no errors; `#print axioms`: standard |
| `scratch/sgr-split/L1.lean`, `L2.lean` | the two general facts | `#print axioms`: standard |
| `scratch/sgr-split/StatementCopy.lean` | verbatim copy of the field's statement, checked `Iff.rfl` against the chain's | no errors |
| `scratch/sgr-split/Discharges.lean` | `#discharges` | output below |
| `scratch/sgr-split/AutofoldDryRun.lean` | `autofold.py --dry-run --allow-rise` output, line 1 stripped | `sixContactMin_of_open26`, standard axioms |

`#discharges` (`scratch/sgr-split/discharges.txt`; the other lines are other contributions already in the tree):

```
DISCHARGES [OpenAddedLeaves16.shimuraGoodReductionNoGuard] by SGRSplit.shimuraGoodReductionNoGuard_of_printed
  still assumes: [SGRSplit.ShimuraIntegralModelRep]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves16.shimuraGoodReductionNoGuard] by SGRSplit.shimuraGoodReductionNoGuard_of_rep
  still assumes: [SGRSplit.ShimuraIntegralModelRep,
 SGRSplit.QMAbFieldFibre,
 SGRSplit.QML3AsQMAb,
 SGRSplit.FibreClassUnique]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 66 open hypotheses, 1266 theorems checked, 5 discharge one
```

Autofold: `scratch/sgr-split/autofold.json` discharges `shimuraGoodReductionNoGuard` with proof
`_root_.SGRSplit.shimuraGoodReductionNoGuard_of_printed {n}.shimuraIntegralModelRep` and one new row,
`shimuraIntegralModelRep` (published, flag "pending reading: ..."). `--dry-run` (`scratch/sgr-split/autofold-dryrun.txt`) reports
`strict count: 46/13 on 59 -> 46/13 on 59; strictest 45/14 -> 45/14` (no rise); its module, line 1 stripped
(`scratch/sgr-split/AutofoldDryRun.lean`), compiles: `sixContactMin_of_open26` with standard axioms.

Build note: the worktree reused a prebuilt build tree of the same commit (`6edf020d`), then built
`ZInQKernel.OneProof.Main`, `ZInQKernel.OneProof.Discharges` (up to date except `TailZ28`–`TailZ31`, `Main`)
and the new module (59 to 86 s).

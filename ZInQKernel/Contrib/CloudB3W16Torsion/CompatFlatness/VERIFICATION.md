# H102 exclusive flatness port — full kernel and AX3 verification

## Ownership, snapshots, and scope

The assignment is exactly the 22 exclusive modules in `provider-split.json` entry 2:
11 P2M solution modules and 11 theorem wrappers. The root is
`Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite`;
the canonical import prefix remains
`ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT`.
The primary owns all common dependencies, Native/final cardinality work, and H102.

Started from primary WIP `5e899848136fc41778ede328abadc36098ed85bd` and consumed
primary snapshots `052a8863b7f5cb722e97e4774a557b109ec1b73f`,
`5306edfdd8c7828cd7cac2560ac62fdb684aae97`, and finally
`3accb111f31ce25060b92ebbb5289bb8e1107eb0` unchanged. The last includes the
primary's unchanged consumption of this lane's earlier `ad29515b` repair patch
(as `3e94f9f5d`). Its common-depth fix unblocked the final four owned modules.
The original baseline tree was checked against restored main `2dc949d68`.

Dedicated private checkout: `devvm18927`, `~/cloud-b3/w16/h102-flat`.
GitHub operations only occur in the private `devvm19064` broker checkout.
Both clones use `push.default=nothing`; only the explicit own branch refspec is pushed.
The previously verified finite-group helper `7b22028e` remains frozen and unchanged.

## Exact root API

Import:

```lean
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
```

The exported type is the original source type, not a restated H102 target:

```lean
theorem GoodReductionJacobian.AbelianSchemePropertyBundle.flat_of_isFinite
    (K : Type u) [Field K] {A : AlgebraicGeometry.Scheme.{u}}
    {f : A ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)}
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle K f)
    (β : NeronModelInfra.SchemeHomOver f f) [AlgebraicGeometry.IsFinite β.1] :
    AlgebraicGeometry.Flat β.1
```

The local algebra export is also compiled in its exact original type:

```lean
theorem Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hfib : ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) = 0)
    (hdim : ringKrullDim S = ringKrullDim R) : Module.Flat R S
```

All 22 source-solution/public-wrapper declaration headers were compared with the
initial primary snapshot and remain textually unchanged. No wrapper was edited.
No extra hypothesis or axiom was added.

## Compatibility repairs and preserved source

This lane repaired only four owned solution modules, plus new CompatFlatness support:

* `S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero`: replace the old
  zero-based TFAE lookup with Mathlib's actual `map_maximalIdeal_lt_top` theorem.
* `S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral`: supply polynomial
  normality using the named `UniqueFactorizationMonoid.instIsIntegrallyClosed`
  instance. Generic inference looped even with two million heartbeats.
* `S_IsLocalRing_isRegular_of_systemOfParameters`: qualify the actual `Module.depth`
  definition; supply quotient-ring module finiteness before finite basis indices;
  keep private helpers local instead of erroneous self-exports; update the remaining
  TFAE lookup to one-based. The exported mathematical statement stays unchanged.
* `S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite`: keep the
  private noetherianity helper local and remove its erroneous self-export. This was
  the final source-level failure after the primary common dependencies were repaired.
* `CompatFlatness/QuotSMulTop.lean`: ordinary theorems supplying the quotient scalar
  tower and finite module instance by the original quotient-surjectivity and
  restrict-scalars proof. No new global instance, syntax, macro, or elaborator.

Source revision remains anthropics/fermats-last-theorem
`6e837e75355538c7f80bab5b956861e86c4eacc2`. Vendor manifests, original copyrights,
NOTICE, ATTRIBUTION, and LICENSE remain untouched. Compatibility changes are
marked `[port]`; the new helper identifies its original source proof.

## Actual successful checks

Lean 4.35.0 / Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
All Lean invocations serialized under the private `lane-build.lock`, at most one
Lean process, `LEAN_NUM_THREADS=4`, `lean -M18000`, no virtual-memory limit.
Host available memory was checked before each invocation (at least 30 GiB).
Maximum final cone compile-log RSS: **7429532 KiB** (below the 20 GiB bound).

The original 52-module cone plus one new compatibility helper was compiled
in import order with commands of the following form:

```sh
lake env lean -M18000 -o .lake/build/lib/lean/<module>.olean <module>.lean
```

The final root build is **53/53 successful, 22/22 owned successful, zero failures
or blocked modules**. Cache reuse was keyed by source SHA256 and the recursively
computed dependency signatures; changed common sources forced dependent rebuilds.

Fresh `CheckAll.lean` imports only the root, checks the two exact APIs above, and
prints axioms for all 11 public wrapper exports, all 11 P2M `solution` proofs,
and both new compatibility lemmas. Actual exit **0**, **4.67 seconds**, peak RSS
**7185892 KiB**. All **24** printed lists were parsed and checked and are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Actual root output:

```text
'GoodReductionJacobian.AbelianSchemePropertyBundle.flat_of_isFinite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The nine other public exports are AlgHom injectivity, quotient transcendence-degree
strictness, finite stalk quotient dimension zero, finite-endomorphism stalk dimension,
the two integral height-equality results, regularity of systems of parameters,
local flatness from residue-field Tor vanishing, and regular-sequence Tor vanishing.
They and the two flatness exports all have AX3-clean source solutions and wrappers.

Actual full AX3 log SHA256:
`db8becb0b03dc96a4659211e5fe54969b37c1317015948305d1c883e8c1e4de8`.
Private raw evidence is `flat-stage.json`, `flat-logs/`, `flat-all-axioms.log`,
`CheckAll.lean`, and the earlier prerequisite logs/checks in the dedicated checkout;
final summary/log bytes are also brokered to `devvm19064` for the primary.
Ordinary source linter/deprecation warnings remain visible; they are not hidden.

## Failed attempts and boundary

Initial actual failures included the old TFAE indices, the polynomial normality
instance search, and private-helper self-export / quotient-finiteness sites.
The initial common smooth carrier and common-depth failures were reported to the
primary, never edited by this lane, and resolved by consuming their verified
snapshots unchanged. The final root private-helper failure was repaired only in
its owned source module. Earlier failed runs remain failures, not passes.

No Main build, source-manifest/config/pin/root-import edit, upstream/issue/comment/PR,
main push, merge, degree API, final cardinality proof, or H102 closure claim was made.
The result is the exact-source flatness helper cone, ready for the primary's use.

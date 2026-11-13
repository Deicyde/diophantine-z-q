# G1-adelic: actual normalizer quotients for the manuscript order

Status: arithmetic contribution, 2026-11-13. The two G1-adelic bookkeeping targets are proved by closed Lean declarations on the actual objects. This is not manuscript incorporation, a registered-provider discharge, an official Protocol_D coverage decision, or Astra acceptance. Serving model identity: unknown. Required independent Astra review remains pending.

Base: main `a5937595cde3e3db00975b81e5171cdef92c801a`. Lean: `leanprover/lean4:v4.35.0`. Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`. No research branch is used as the production base.

## Result and exact scope

For the actual rational quaternion algebra and order

\[
 B=(2,-3),\qquad
 \mathcal O=\mathbb Z\langle1,i,(1+j)/2,(i+ij)/2\rangle,
\]

let `Af = IsDedekindDomain.FiniteAdeleRing ℤ ℚ`, let `N` normalize the completed order in actual adelic quaternion units, let `K0` be its order-unit subgroup, and let `K3` be the actual principal-level-three reduction kernel. The contribution proves

\[
 N/(\mathbb A_f^\times K_0)
 \simeq \prod_p' N(\mathcal O_p)/(\mathbb Q_p^\times\mathcal O_p^\times),
 \qquad |N/(\mathbb A_f^\times K_0)|=4,
\]

and

\[
 \Gamma'=N/(\mathbb A_f^\times K_3),\qquad
 |\Gamma'|=|N/(\mathbb A_f^\times K_0)|\,
 |K_0/(\widehat{\mathbb Z}^{\times}K_3)|
 =4\cdot36=144.
\]

`GammaPrime` is defined as the actual quotient `N ⧸ D3`, never as the product in this formula. The formula does not assert that the extension splits or that Gamma is a group direct product. Neither cardinality factor is defined by its desired value.

The actual `O/3O` unit group has order 72; its central scalar residue subgroup has order 2. Thus 144 is stronger than the arithmetic upper bounds 288 and 324. The current manuscript, `manuscripts/quartic_v16.tex`, A3 lines 790–827, still gives the coarse bound 324. That passage and its geometry were not edited. The separate discriminant-210 computation is outside this contribution.

All source changes are confined to `ZInQKernel/Contrib/AdelicNormalizer/*.lean` and this note. No original root, checker, registry, toolchain, manifest pin, policy, manuscript, or acceptance record was edited. No staging, commit, push, pull request, merge, issue comment, or human outreach was performed by this worker. The modules now occupy the configured `ZInQKernel` library and contribution-selection path; that path correction alone is not full normal candidate validation. Headline-provider registration, full-root validation, and integration are outside this scoped handoff.

## Object, API, and scalar-quotient contract

Contribution filenames below are relative to `ZInQKernel/Contrib/AdelicNormalizer/`.

1. **Actual scalar extension.** `Objects.scalarEquiv` transports Mathlib's finite adeles, indexed by every `HeightOneSpectrum ℤ`, to the padic restricted-product scalar ring, checking the integral carriers in both directions. `ScalarExtension.scalarExtensionEquiv` is an `Af`-algebra isomorphism `Af ⊗[ℚ] GlueRepo.A1.B ≃ₐ[Af] BA`; `scalarExtensionEquiv'` handles the factor order `B ⊗[ℚ] Af`. They are constructed from the actual tensor algebra map and its action on a basis, not a type-level tuple equivalence.
2. **Actual integral structure.** `IntegralComparison.range_integralComb`, `integralComb_eq_sum`, and `mem_completedOrder_iff_tensor` identify the completed order with the full `Zhat`-span of the actual A1 ordered basis. Inverse coordinates are `re-imJ`, `imI-imK`, `2*imJ`, `2*imK`, integral at every place. No integrality of `1/2` is assumed at two. `Objects.rationalToLocal_basis` fixes the rational-to-local basis maps.
3. **Actual adelic units and normalizer.** `Adelic.quaternionEquiv` identifies `BA` with the restricted product of local quaternion rings relative to the actual order. Mathlib's `RestrictedProduct.unitsEquiv` supplies both value and inverse restrictedness. `N` is first defined by conjugating the actual completed order. `singlePlace` tests arbitrary local order elements, and `mem_N` then proves its componentwise characterization. Only afterward is `normalizerEquiv` constructed.
4. **Actual scalar denominator.** `globalDenom = scalarSubgroup ⊔ K0`, where `scalarSubgroup` is the image of actual `Afˣ`. `mem_globalDenom` proves equality with the coordinate denominator. In the reverse direction its scalar witness is one wherever the original unit is an order unit. Those places are cofinite, so the scalar family is a genuine finite idele. Unrestricted independent local scalar choices are not substituted for `Afˣ`.
5. **Actual quotient map.** `RestrictedQuotient.quotientHom` maps a restricted product of groups to the restricted product of local quotients relative to the identity subgroup. It is surjective by choosing identity representatives at trivial coordinates. `GlobalQuotient.normalizerQuotientHom` applies this to actual `N`; its kernel is proved equal to actual `D0`. `normalizerQuotientEquiv` is the induced quotient isomorphism. `local_quotient_card` covers every prime: 2 at two and three, 1 everywhere else.
6. **Actual residue and level maps.** `Residue3` is a new ring with A1's `mul3` and `one3`, not the pointwise ring on four copies of `ZMod 3`. `IntegralComparison.rationalReduction` is a surjective ring map from actual A1 `O`, with kernel exactly `3O`, and agrees with actual local reduction. Local unit surjectivity has explicit norm-certified integral lifts and a two-sided inverse. Single-place adelic unit lifts make `reduction3 : K0 →* Residue3ˣ` surjective. `K3` is its kernel embedded in `BAˣ`; `Congruence.mem_K3_iff_congruence` proves equality with units in `1+3 completedOrder` at all finite places.
7. **Actual scalar intersection and count.** `Z0_eq_integralScalars` proves `scalarSubgroup ∩ K0 = image(ZhatUnits)`. `range_reduction3_integralScalar` proves that image reduces onto exactly the central `F₃ˣ` subgroup. `intersect_levelDenom_K0` identifies `(Afˣ K3) ∩ K0` with `Z0 K3`. `projectiveReduction` has precisely that kernel. `levelQuotientEquiv` gives cardinality 36. The relative-index tower is applied inside `N`, where level normality is proved; it does not assume `K3` is normal in all `BAˣ`.

The final source/consumer statements are also checked without abbreviated product definitions in `Checks.lean`:

```lean
theorem exact_normalizer_count : Nat.card (N ⧸ D0) = 4
theorem exact_level_count : Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0) = 36
theorem exact_manuscript_factorization :
    Nat.card (N ⧸ D3) = Nat.card (N ⧸ D0) *
      Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0)
theorem exact_manuscript_count : Nat.card (N ⧸ D3) = 144
```

## The nine application obligations

These are addressed by the closed arithmetic maps and proofs below. “Addressed” does not mean independently accepted under the Astra policy.

### 1. Source hypotheses

- **Required:** local primality; all ramified/unramified cases; normality and containment for the restricted quotient; commuting tensor scalar maps; the index-tower containments.
- **Constructed:** actual prime facts from the prime/place equivalence, `localH ≤ localS`, proved `localS.Normal`, canonical rational/adelic scalar maps, `D3 ≤ D0`, and level normality inside `N`.
- **Derivation:** the generic quotient assumptions are instantiated by proved subgroup facts. The final count has no extra premise, section hypothesis, or target-shaped `Fact`.
- **Evidence:** `Objects.lean`; `LocalQuotient.localH_le_localS`; `GlobalQuotient.ker_normalizerQuotientHom`; `ScalarExtension.toBA_bijective`; `LevelThree.K3_in_N_normal`; `Cardinality.D3_le_D0`.

### 2. Constructed objects

- **Required:** the manuscript's rational order, finite-adelic scalar extension, completed order, order units, normalizer, and principal level.
- **Constructed:** actual `GlueRepo.A1.B`, `O`, `e`, and `comb`; actual Mathlib `Af`; their tensor algebra equivalence; the full integral span; conjugation normalizer `N`; kernel-defined `K3`.
- **Derivation:** scalar extension, integral span, and rational/local reduction identities are proved separately. A related order or a product merely having the desired cardinality is not used.
- **Evidence:** `ScalarExtension.lean`; `IntegralComparison.range_integralComb`, `mem_completedOrder_iff_tensor`, `rationalQuotientEquiv`; `Adelic.N`; `LevelThree.K3`.

### 3. Domain and index coverage

- **Required:** every rational finite prime and every permitted local quotient class, not only a diagonal or exceptional-prime subfamily.
- **Constructed:** all height-one places, equivalent to `Nat.Primes`; cofinite restrictedness; arbitrary single-place order elements; identity-supported quotient and unit/scalar lifts.
- **Derivation:** quotient surjectivity supplies independent local classes. The exceptional set is proved exactly the two distinct places over 2 and 3; all other local denominators are the whole normalizer.
- **Evidence:** `RestrictedQuotient.quotientHom_surjective`; `Adelic.mem_N`; `GlobalQuotient.mem_ramifiedPlaces`, `localQuotientsEquiv`; `PrimeEvaluation.K0AtPrime_surjective`; `ScalarLifting.liftIntegralScalar`.

### 4. Transition and comparison maps

- **Required:** actual compatible algebra, unit, normalizer, residue, scalar, and quotient maps with their directions, kernels, and images.
- **Constructed:** tensor map `toBA`, scalar/quaternion evaluations, restricted-product equivalences, `normalizerQuotientHom`, rational/local reductions, explicit unit/scalar lifts, and `projectiveReduction`.
- **Derivation:** the first-isomorphism maps use proved kernels and surjectivity. The global kernel factorization builds a finite idele; unit lifting proves inverse integrality rather than inferring it from ring surjectivity.
- **Evidence:** `GlobalQuotient.mem_globalDenom`; `Residue.unitReduction_surjective`; `IntegralComparison.rationalReduction_eq_localReduction`; `ScalarLifting.range_reduction3_integralScalar`; `Cardinality.ker_projectiveReduction`.

### 5. Identity of the consumed object

- **Required:** the consumed cardinalities concern actual `N/D0`, actual `N/D3`, and actual `O/3O`.
- **Constructed:** `normalizerQuotientEquiv` starts from actual `N ⧸ D0`; the rational quotient map identifies the actual residue ring; `GammaPrime` is literally `N ⧸ D3`; the intermediate level quotient comes from actual reduction.
- **Derivation:** the exact scalar intersection and projective kernel identify the factor consumed by the index tower. `Checks.lean` expands the source and consumer quotient types.
- **Evidence:** `GlobalQuotient.normalizerQuotientEquiv`; `IntegralComparison.rationalQuotientEquiv`; `Cardinality.levelQuotientEquiv`, `card_GammaPrime_eq_indices`; `Checks.exact_manuscript_count`.
- **Integration limit:** no claim is made that the 144 refinement or its geometric consumer has been incorporated into the manuscript.

### 6. Coefficients and normalization conventions

- **Required:** match `ℚ`, `Af`, `ℚ_p`, `ℤ_p`, `Zhat`, `F₃`, A1's ordered basis, and the reduced-norm convention.
- **Constructed:** ring/algebra coefficient maps; structure constants exactly equal to `A1.combMul` and `A1.mul3`; the same half-integral basis; local norm convention `‖p‖=p⁻¹`.
- **Derivation:** the local scalar denominator uses even reduced-norm valuation. Negating the valuation exponent does not change parity. The scalar residue factor is the actual `F₃ˣ` image, of order two.
- **Evidence:** `Objects.coordMul_int`, `coordMul_mod3`, `rationalToLocal_basis`; unchanged `Local.lean`; `IntegralComparison.integralComb_eq_sum`; `Residue.card_scalarUnits_range`.

### 7. Local conditions

- **Required:** integrality of both value and inverse almost everywhere for adelic units, everywhere for order units, and correct congruence at each prime.
- **Constructed:** Mathlib unit restricted products; `K0`; actual scalar intersection; principal congruence assembled by the central inverse of three.
- **Derivation:** the kernel scalar is one off a finite set. At three, the local reduction kernel supplies divisibility; away from three, including two, three is an integral local unit. This proves global congruence rather than silently ignoring other primes.
- **Evidence:** `Adelic.unitEquiv`, `ideleEquiv`, `mem_K0`; `GlobalQuotient.mem_globalDenom`; `PrimeEvaluation.scalarIdeles_mem_K0`; `Congruence.mem_K3_iff_congruence`.

### 8. Exceptional cases

- **Required:** handle two, three, nonunits, zero reduced norm, rational denominators, and the infinite-type convention for `Nat.card`.
- **Constructed:** the actual order lattice at two; explicit mod-three unit lifts; proof of nonzero reduced norm before inversion; genuine rational adelic scalars `1/2` and `1/3`; finite quotient equivalences.
- **Derivation:** no integrality of `1/2` at two or `1/3` at three is assumed. Unit lifting checks a two-sided inverse. Cardinalities 4 and 36 are established by actual equivalences; nonzero cardinality then supplies `Finite` instances, so zero-on-infinite conventions cannot masquerade as a finite count.
- **Evidence:** `IntegralComparison.orderCoord_mem`; `Residue.nrd_liftOrder_ne_zero`, `liftUnit`; `Congruence.inverseThree_mem_away`; `GlobalQuotient.normalizerQuotient_finite`; `Cardinality.GammaPrime_finite`.

### 9. Downstream consumption

- **Required:** provide exactly the two G1-adelic arithmetic targets and the resulting finite group cardinality.
- **Constructed:** actual quotient isomorphism, count four, projective-level quotient count 36, exact index factorization, and count 144.
- **Derivation:** the index tower inside `N` gives the required product; the weaker 288 and 324 arithmetic bounds follow. No group splitting, geometric orbit, Hecke action, or degree assertion is inferred from the count alone.
- **Evidence:** `GlobalQuotient.card_normalizer_quotient`; `Cardinality.card_level_quotient`, `card_GammaPrime_eq_indices`, `card_GammaPrime`, `GammaPrime_card_bounds`.

## Verification and exact bindings

The initial repository-root `Contrib/AdelicNormalizer` snapshot and its separate preliminary review are preserved byte-unchanged as history. Its scoped 849-declaration PASS concerns those old module prefixes only; it is not a pass of the registered candidate's full normal validation.

All fifteen current files have been relocated to `ZInQKernel/Contrib/AdelicNormalizer`. Exactly 19 import headers in 13 files changed from `Contrib.AdelicNormalizer.*` to `ZInQKernel.Contrib.AdelicNormalizer.*`. `Local.lean` and `RestrictedQuotient.lean` changed path but not bytes. All namespaces and all non-import source bytes are unchanged. Reversing only those import-header edits reproduces every archived source SHA-256; `body-equivalence.json` records both source hashes and the identical body hashes.

All fifteen relocated modules, including `Checks.lean`, were freshly compiled with Lean 4.35.0, `LEAN_NUM_THREADS=2`, processor affinity limited to four CPUs, and the V2 IPC resource gate. The unchanged main A1 supplier remained pinned. No full-root build, dependency-package fetch, or shared Mathlib source/cache write was performed.

The unchanged `scripts/audit_kernel.lean` was then run with a **relocated contribution-only** specification: the fifteen `ZInQKernel.Contrib.AdelicNormalizer.*` modules plus the actual A1 supplier. It replayed 849 distinct declarations, checked 850 raw occurrences and two duplicate theorem bodies, and reported:

- status: passed;
- runtime declarations excluded from replay: none;
- allowed axioms used: exactly `propext`, `Classical.choice`, `Quot.sound`;
- headline type: `Eq (Nat.card G1.GammaPrime) 144`;
- protocol acceptance: false.

`Checks.lean` supplies 19 Lean-emitted declaration/type blocks and 20 axiom checks, all with the same standard three axioms. The emitted declarations and axiom log are byte-identical to the archived log despite the module relocation. A bounded source check found no admitted proofs or prohibited proof mechanisms. `python3 -B scripts/check_target.py` checks the unchanged original frozen target. This is fresh scoped verification under the correct module prefixes, not the official full-root provider audit or a full normal candidate-checker result.

Review-packet companions contain the full type blocks, old/new source and serialized `.olean` hashes, body-equivalence record, relocated replay specification/output, axiom log, and separate review/relocation-acknowledgment evidence. The current replay hashes are:

```text
ffcdfbc50598970839ea4f782a38a8c95336c9303950323c4c17b5ab5d8a2263  relocated-evidence.json
a73cef6724e8a913ed825a25f9fe49ba5e6b7f5868a4424a29fb81cc32845958  relocated-kernel-replay.json
e8d794a90d84beef4f3a08fc915d60f5831ecd7a3ae0fa616aa3496234e5fd64  body-equivalence.json
b2b447ff68ff41242ea4c480a3ed44ee58c838057caaa1a5ea2c56460077ad44  axioms.log
```

The archived pre-relocation evidence and replay retain SHA-256 `17eda01ae98ae224470a1948cada62fc00a80a79a026fdf3a458b254c3d8e8d0` and `66e6ab3fe9543490de39b5578fbb52b14a80edc156b1303cbe780eca7d6e8512`, respectively. They are historical scoped checks, not evidence that full normal candidate validation has run.

The following statement hashes are SHA-256 of the exact UTF-8 LF block emitted by Lean, including declaration name, pretty-printed elaborated type and terminal LF. They are **not** hashes of proof expressions; source and `.olean` hashes bind the proof bodies.

```text
88eeeacca27cfc2ea103af8ef38621b1a370c525e999e30beb8f3a999e7172f1  G1.normalizerQuotientEquiv
7793eb07bbac7bc1cd26a7512280b6fc242a08701ac527fb1a3ea2dde5b600a7  G1.Checks.exact_normalizer_count
2fa20cbbb28a329cc7ccfaef0a8c533c23b01e5928e46e6eae1b44433d46b841  G1.Checks.exact_level_count
6802d30c4102c953de56c8e26fb1c317c8f6ea2c33e7c368517664c7f0625027  G1.Checks.exact_manuscript_factorization
7edd4631cccd46d1476f3000b7ed31a46f310200fbb11600ca6eebc4aa16c38b  G1.Checks.exact_manuscript_count
```

### Sources and provenance

The following raw-byte SHA-256 map binds the import-prefix relocation. Filenames mean the old `Contrib/AdelicNormalizer/<file>.lean` and current `ZInQKernel/Contrib/AdelicNormalizer/<file>.lean`. The companion body-equivalence record verifies that removing import lines gives identical bytes for every pair. Public namespaces, mathematical definitions, proof bodies, and the actual `N ⧸ D3` cardinality formula are unchanged.

```text
Local: 0cbf0b62c69d36f1069eddca86833468c2729756a7b09d2e01889c5ae6b92988 -> 0cbf0b62c69d36f1069eddca86833468c2729756a7b09d2e01889c5ae6b92988
Objects: 22a2ca47986af15a105128d6a195602026ad26f4ff4587cbb7739a77f9987438 -> 0c540dbc919093bf35473fcf23e366e14407372f422c7a9167fa0b89d8d9c445
Adelic: 779b5ba532fd86ac18217750101185ac78eef8d944d4d02a1c331e97778ba88c -> 93fbbca509c51851217323dd0c004c9db1bb137aba3d3cf2a324da55550ab5fd
RestrictedQuotient: 6ee76aeaa962fd42cc0212395e58ecac351d08b7fb53582dc140fa6ac2cba2a8 -> 6ee76aeaa962fd42cc0212395e58ecac351d08b7fb53582dc140fa6ac2cba2a8
LocalQuotient: e83826f2b0c7e4b5f3168845aeb09dc0d6703ea956da2959f7212215fc2af469 -> 2ebb66893fc51765e456d15ac310f0e89da472c99dfda0617724f9497067aaab
GlobalQuotient: 1050f5b41cc8f3ece242a811925d3e924d0b16817e9b5c5d49450eb018ffd9af -> aeb62f354ddee6b86253ef633244abaf11634b3a1412b2eca373cd038bd8bb2d
PrimeEvaluation: 103fb49374354e038a3b72460adbe7833a741ee09a38d8d1f5f658843fd3bb6f -> 3bf318d029746c9f5ab4a9e60e2f2e69025b5987bd7aa75aa4327284450d69a1
Residue: dda5641435c875639b920cd3b64ad04d5094d69fd43f14a56873ce0baaf6cb8b -> bf9c54f9d1fa4e9d642256244c13e8eb988bc1de0798eb74c80283cab8332217
ScalarExtension: 0be56dfce8501406b01c76e41a2c666e5f1b3bc15cbba613f72e36af699ac09e -> f299b780f80dc9c52378cab6857e9e3e4f5c615bfac6f1816c43732ae8a4c63c
IntegralComparison: 13e4494ccab7bf709b65bdb00738cb4235dd7a4ecaa41df0553dac8b3dd3d2f5 -> 479e64ecf6b5fc881da29cb55c8742b81ff129878cc3b8518c665534580e27a1
LevelThree: 822801e69c953ba078e2abacecc380e2d4a6138f389dd35fd9ecabce0865ee00 -> babbda787bfbbe2db597a1a2f7d52df889328e47cdf75e9591ede56bef93bcdb
ScalarLifting: a336f8e2545af4578a1656b6b4b93cd5a9a22ae5bfe978263e2ab131afa46ea7 -> 620f7af48b268a8384a0a84dc5a36d69045e703f8de977b41bbaa00d4ffe4328
Cardinality: dfba231427b87343fbdd4cc6d2757e399560432065627e20b97667c0fe7dc513 -> c0489a232bb2873ef33e52b535f45ce31220ac44afa09639d89c1db3b22d9689
Congruence: e147e61b384e3094742186cfdfc2ddde4daf556d6e878a8f75f198b60eb56c05 -> d16af4cba65a37a654c6b620afbb7e26b2a9fa2a2062b9aae9ddfd25e0b0a6ee
Checks: 5e8abe6c418a3d82f6124f09668baa4670086bbb02bade168a3dc837dd1d7346 -> bf4e8a63c8ff6e71e6c1eeee88c8484fe1b89661db435b5b694bb503c542fc6a
```

The archived and relocated source hashes are different bindings where import headers changed; no old acceptance or old-root validation result is relabeled as current. The public declaration/type blocks and their hashes above are unchanged because the mathematical namespaces and statements are unchanged.

Main A1 supplier SHA-256: `fe9db75c5e43321de34265b6b7ca60fcdb33800cdb6ea9fc9fd2957f6b41f3e6`.

`Local.lean` is copied **byte for byte** from the versioned `scratch/glue-vigneras/Local.lean` proof source, SHA-256 `0cbf0b62c69d36f1069eddca86833468c2729756a7b09d2e01889c5ae6b92988`. The local normalizer proofs are reused, not rederived here. The source is now included in the contribution, so reproducing the new proof does not require checking out a research branch. The existing `docs/research/glue-vigneras.md` distinguishes those prior local proofs from the then-open adelic bookkeeping. No mathematical priority or broader historical-coverage claim is made.

The actual Mathlib API sources read are:

- `Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean`: restrictedness, evaluations, maps, single-place elements;
- `Mathlib/Topology/Algebra/RestrictedProduct/Units.lean`: unit equivalence and inverse restrictedness;
- `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean`: actual scalar ring and finite-idele conditions;
- `Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean`: complete prime/place and integral completion comparisons;
- `Mathlib/GroupTheory/Index.lean`: subgroup transport, intersection and normal-sup relative indices, tower multiplication.

These uses do not assume a Vignéras or Voight theorem as a new leaf. The exact local instances are supplied by the reused closed Lean proofs; general published locators not checked by this contribution are not promoted to verified citations.

## Preliminary review and reconciliation

A separate non-author, read-only source review read all fourteen mathematical contribution files and the actual A1 supplier in the archived pre-relocation snapshot, with zero compiler processes. It froze an initial reconstruction S01–S19 before consulting any declared inventory. Its SHA-256, for the exact preserved UTF-8 text without a terminal newline, is `29168d8e693acd26c990e400d3db8ce664fd1c86a8d7e3736aeba89d0fd3a5ce`. That original report is preserved unchanged as a review-packet companion. The task brief and source comments were visible; it is not called blind review. A separate relocation acknowledgment must check the new import prefixes, source hashes, identical mathematical bodies, and this frozen note; the old report alone does not cover a new source binding. Such acknowledgments remain separate evidence, not Astra or full normal validation acceptance.

The authored reconciliation with this note's object/API inventory is:

- S01–S04: actual A1 datum, all-place scalars, tensor algebra and integral basis; contract items 1–2.
- S05–S06: units, single-place tests and actual normalizer; item 3.
- S07–S10: local denominators, all-prime factors, finite-idele kernel and actual quotient; items 4–5.
- S11–S15: prime transport, actual rational/local residue rings, norm-certified unit lifts, level normality and full principal congruence; item 6.
- S16–S18: scalar intersection/image, projective kernel and the index tower; item 7.
- S19: arithmetic consumption and the unchanged manuscript/geometric scope; Result and exact scope, and obligation 9.

No genuine arithmetic source use in that reconstruction is left without a supplier in the scoped inventory. Unused generic quotient variants and the supplier's matrix presentation are alternatives/background, not required hidden applications. `Checks.lean`, added as an observational type/axiom companion, introduces no additional arithmetic route. This authored reconciliation and the preliminary source assessment are **not** an official independent inventory-coverage acceptance.

The preliminary review found no substantive arithmetic objection. It did not inspect the compiler/replay certificate and did not supply Astra or assembled-manuscript acceptance. Its bounded related-use check distinguished the separate discriminant-210 Gamma computation from the discriminant-six target; no unrelated count was changed to 144.

## Reproduction

Use the stated main and toolchain/Mathlib pins, with the pinned dependency `.olean` cache already available read-only. Keep outputs and packet companions in the private build cache. No root target or registry edit is needed.

```sh
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/AdelicNormalizer .lake/build/g1-relocated
export LEAN_NUM_THREADS=2
lake env lean \
  -o .lake/build/lib/lean/ZInQKernel/HDecomp/Repo/A1Quaternion.olean \
  -i .lake/build/lib/lean/ZInQKernel/HDecomp/Repo/A1Quaternion.ilean \
  ZInQKernel/HDecomp/Repo/A1Quaternion.lean
for m in Local Objects Adelic RestrictedQuotient LocalQuotient GlobalQuotient \
  PrimeEvaluation Residue ScalarExtension IntegralComparison LevelThree \
  ScalarLifting Cardinality Congruence Checks; do
  lake env lean \
    -o ".lake/build/lib/lean/ZInQKernel/Contrib/AdelicNormalizer/$m.olean" \
    -i ".lake/build/lib/lean/ZInQKernel/Contrib/AdelicNormalizer/$m.ilean" \
    "ZInQKernel/Contrib/AdelicNormalizer/$m.lean" || exit 1
done
python3 -B scripts/check_target.py
# Place the packet's replay-spec.json at .lake/build/g1-relocated/spec.json.
lake env lean --run scripts/audit_kernel.lean \
  .lake/build/g1-relocated/spec.json .lake/build/g1-relocated/audit.json
```

The local resource wrapper used for verification only bounds concurrent work; the portable commands above preserve the actual compiler/replay arguments. The replay specification is evidence for this contribution only, not a replacement for project policy or the official registry.

## What remains outside this contribution

No actual-order, finite-idele kernel, local-factor, residue-unit-lifting, scalar-intersection, or index-factorization map required by the two arithmetic G1-adelic targets remains open in these modules.

The geometric Hecke/normalizer action, trivial central action on the curve, positive-normalizer comparison, generic-orbit/degree assertion, and connection to actual Shimura/moduli objects are not proved here. None of the original five headline hypotheses is discharged. The 144 refinement is not incorporated into the manuscript. Required Astra application/coverage/assembly acceptance, official CI/provider registration, and integration remain pending. This non-release contribution does not promote a new polynomial record or change any manuscript/PDF release artifact.

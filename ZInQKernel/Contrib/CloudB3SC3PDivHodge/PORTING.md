# Port of Tate's Hodge–Tate decomposition for p-divisible groups (Anthropic FLT) to Lean 4.35 / Mathlib v4.35.0

## What is here

`Vendor/AnthropicFLT/` holds the import cone of

```
PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
```

from anthropics/fermats-last-theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(Lean 4.33.1, Mathlib `db584cd6`, Apache-2.0). This is Tate's Hodge–Tate decomposition for
p-divisible groups (Tate, *p-divisible groups*, Driebergen 1967, §4, Cor. 2 of Thm 3):
for `K` a finite extension of `ℚ_p` inside `PadicAlgCl p` and `G` a p-divisible group of height `h` and
dimension `n` over the ring of integers of `K`, `n ≤ h`, and `ℂ_p ⊗ V_p(G)` has a `ℂ_p`-basis on which
every `σ` fixing `K` acts by `χ(σ)` on `n` basis vectors and trivially on the other `h - n`.
Here `χ` is the cyclotomic character.

`PDivisibleHodgeTate.lean` restates this theorem verbatim and proves it from the vendored copy.
It compiles only once the whole cone does (see Status).

The theorem is about p-divisible groups over `O_K`. It is **not** a proof of the kernel's open
statement `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`, which covers every abelian variety over `F`,
with no reduction hypothesis, and uses the kernel's own `AbVar`. It is supporting material only.

The upstream cone has 232 modules. They are provided as follows.

* **Already vendored on main (4 modules).** `Def_EllipticCurve_FrobeniusTrace`, `Def_FLTPrelim_FreyPackage`,
  `Def_FLTPrelim_GaloisRep` and `Def_FLTPrelim_Ramification` are imported unchanged from
  `ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/Definitions/`. Those copies are upstream's
  bytes apart from the vendoring header, import relocation and `set_option` lines that the earlier vendoring
  recorded in their headers and in that directory's NOTICE.
* **Already ported by the Tate-theorems work (PR #29, head `fefce8ef`; included in main `c1e4ed1b8765f016c8fd5808e79bb0124b364952`).** This port
  reuses those providers instead of declaring the same root names a second time:

  | upstream module | provided by (W11) |
  |---|---|
  | `Definitions.Def_PadicComplex_GaloisAction` | `CloudB3W11AxCompletion.GaloisAction` (same declarations; W11 omits `smul_coe_padicEmbedding`, which this cone does not use) |
  | `Definitions.Def_PadicAlgCl_CyclotomicTower` | `CloudB3W11Cyclotomic.TowerDefinition` (same definition) |
  | `Definitions.Def_PadicComplex_TateTrace` | `CloudB3W11TateTrace.TraceModel` (same definitions) |
  | `Theorems.Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup` | `CloudB3W11Cyclotomic.TowerDegree` (same root theorem) |
  | `Theorems.Thm_PadicComplex_forall_smul_eq_self_iff_mem_closure` | `CloudB3W11AxCompletion.AxClosure` (same root theorem) |

  Five upstream solutions that W11 ported under `ZInQ.Contrib.CloudB3W11TateTrace.<X>.solution` are not
  ported again. The upstream-named `Theorems` wrapper is kept with upstream's statement and proved by W11's
  solution:
  Reused solutions include:
  * `norm_sum_pow_apply_le_of_mem_cyclotomicTower` by `TraceNormBound`;
  * `exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul` by `TensorTwist`;
  * `exists_isTateTrace_cyclotomicTower` by `CyclotomicTrace`;
  * `exists_isTateTrace_of_norm_sum_pow_apply_le` by `TraceConstruction`.
  `TwistWholeGroup` is used directly as described next; its upstream-named wrapper is dropped.

  Because W11's `TwistWholeGroup.solution` states Tate's `ℂ_p(k)^G = 0` with the local cyclotomic character,
  while upstream's `PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul` uses the global one
  composed with `localGaloisToGlobal`, the upstream wrapper is not kept. Its one user, `hH0` in the root
  solution, calls W11's theorem directly, a two-line proof change marked `-- [port]`.

  The following upstream modules then became unreachable from the root and are not ported:
  * `Thm`/`S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le`
    (W11 declares a different theorem under this root name);
  * `Thm`/`S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower`;
  * `Thm`/`S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul`;
  * `Thm`/`S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le`;
  * `Thm`/`S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul`;
  * `S_PadicComplex_exists_isTateTrace_cyclotomicTower`, `S_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup`
    and `S_PadicComplex_forall_smul_eq_self_iff_mem_closure`.
* **`P2M.Util`** is not ported. It only defines elaborators, which are replaced by standard Lean (T4–T9).
* **Everything else** is ported here with its upstream path under `Vendor/AnthropicFLT/`.
  `Vendor/AnthropicFLT/SOURCE_MANIFEST.json` gives each module's upstream path, sha256 and git blob id.

## Transformations

Every vendored file has a header naming its upstream module and the commit. The mechanical changes,
made by a script from the upstream bytes, are:

| id | change |
|---|---|
| T1 | header comment (upstream module, commit, licence, modification notice) |
| T2 | imports relocated to `ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.*`; the 4 shared modules are imported from the CloudB2X0Transitive copy; `import P2M.Util` dropped |
| T3 | upstream lakefile options as `set_option` lines after the imports (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`, `autoImplicit false`) |
| T4 | each `Theorems/Thm_*.lean` wrapper ended `:= by p2m_exact_reverting @P2MW.S_….solution`. It now ends with the explicit application `@P2MW.S_….solution x₁ … xₖ` of the same constant to the theorem's binders. Anonymous instance binders `[C]` are named `[inst_tN : C]` so they can be passed. The statement text is otherwise unchanged; the elaborated type is the same |
| T5 | `p2m_open "A B"` → `open _root_.A _root_.B`; `p2m_open_scoped "A"` → `open scoped _root_.A` (also the `… in` form). P2M resolved these names from the root, so `_root_.` keeps that meaning |
| T6 | `p2m_export "NS" "a b"` → `export _root_.NS (a b)` (P2M added exactly these aliases) |
| T7 | `p2m_reactivate "NS"` → `open scoped _root_.NS` |
| T8 | `local notation "tok" => rhs` → removed; every use of `tok` up to the end of its scope is replaced by `(rhs)`. Notation is build-time syntax, which the kernel's contribution rules exclude |
| T9 | `p2m_alias …`, `p2m_export_all …` and `p2m_export "" …` → removed. They only added aliases of private names that the files reach by dot notation or full name |

Error-driven repairs, each marked `-- [port]` in place:

* **T5/T7, namespace not yet declared.** P2M could open a namespace before any declaration existed in it;
  Lean 4.35 rejects `open` of an unknown namespace. Such a name is dropped from the `open` line. Where
  later code needs it, the `open` is repeated right after the namespace is first closed.
* **T6, export of a private `_root_.X` declaration** (`FrobKer.cast_eq_zero`). The export becomes a comment
  and the later unqualified uses are written `X.name`.
* **Tensor-product induction.**
  * In Mathlib v4.35.0 the `induction` eliminator of `⊗` has no `zero` case, so the upstream
    `| zero => …` alternatives are removed.
  * `TensorProduct.induction_on` is now deprecated and no longer `@[elab_as_elim]`. Uses of it as an
    eliminator call `TensorProduct.induction_on_of_zero` instead. That lemma, in `Compat.lean`, restates
    the upstream statement with the upstream attribute and is proved from Mathlib's `TensorProduct.inductionOn`.
* **Lemma and API changes in Mathlib v4.35.0:**
  * `TensorProduct.dualDistribEquiv` is no longer definitionally `dualDistrib`; proofs use
    `TensorProduct.toLinearMap_dualDistribEquiv`.
  * `List.TFAE.out` is 1-indexed.
  * `Equiv.setCongr` (for a set equality) is now `Set.equivOfEq`.
  * `isIntegral_algebraMap_iff` takes a `FaithfulSMul` instance instead of an injectivity argument; where an
    injectivity proof is passed, its proof `isIntegral_algHom_iff (IsScalarTower.toAlgHom …)` is used instead.
  * `Valuation.norm_def` now unfolds to `RankLeOne.hom'`.
  * `SubalgebraClass.seminormedRing` and `SubalgebraClass.normedRing` no longer exist, so they are dropped
    from `attribute [-instance]` lists.
* **"No goals"**: a tactic that Mathlib v4.35.0 already finishes is removed.
* **Instance name**: the anonymous `instance : IsScalarTower R F (F ⊗[R] G)` in
  `Def_FiniteFlat_SchematicClosure` is given its upstream auto-generated name
  `instIsScalarTowerTensorProduct_definitions`, because downstream `attribute [-instance]` lines refer to it.
* **Parser change**: a set singleton `{a …}` whose element spans several lines no longer parses, so the
  element is parenthesized `{(a …)}`. This is the same term.

No declaration statement changes except as listed (T4 binder names, parenthesized singletons).
The audit diff against the script output, and the script output against upstream, is in the private
evidence bundle available to the maintainer.

## Checks

See the private evidence bundle for partial build logs (one Lean process per module,
`-M16000`), the failed kernel checks, and the source manifest. The root theorem is
not compiled, so no root `#print axioms` or discharge pass is available.

The source is untrusted input. `grep` finds no `sorry`, `axiom`, `native_decide`, `extern`,
`implemented_by` or `unsafe` in the vendored files, and no build-time commands
(`#eval`, `run_cmd`, `initialize`, `syntax`, `macro`, `elab`, `notation`, `infix`, `prefix`, `postfix`).

## Licence

`Vendor/AnthropicFLT/LICENSE` is upstream's Apache-2.0 licence, byte-identical.
`NOTICE.upstream` and `ATTRIBUTION.upstream.md` are upstream's NOTICE and ATTRIBUTION.md, byte-identical.
`NOTICE` is upstream's NOTICE followed by the modification notice for this port.
Two cone modules carry material that upstream's ATTRIBUTION.md credits to the Imperial College London FLT
project: `Def_FLTPrelim_FreyPackage` and `Def_FLTPrelim_GaloisRep`. Both are the copies already vendored on
main.

## Status (2026-11-16): BLOCKED on one kernel check

The native record includes 216 successful module compilations before the final
canonical-provider rewire, plus a partial post-rewire rebuild. It is not a final
whole-cone pass. Under `-M16000`, the blocking module is
`P2M/Sol/S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower.lean`.
Four downstream continuous-cocycle chain modules, the root solution and theorem
wrapper, and `PDivisibleHodgeTate.lean` remain uncompiled.
Its lemma `TP9.coe_trace_adjoin_simple_eq` elaborates, upstream gives it `maxHeartbeats 6400000`, and then
the kernel check fails with `(kernel) excessive memory consumption detected`.
* As ported: 411 s.
* With an explicit `Algebra.smul_def` rewrite in place of one `rfl`: 12 min 19 s, peak RSS 16.4 GB.

The module feeds Tate's continuous-cocycle (H¹) chain, which the root solution imports:
`exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower` →
`exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq` →
`exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle`.
So the root theorem, and with it `PDivisibleHodgeTate.lean`, is not yet compiled. The FLT README reports that
a few modules needed up to 36 GB.

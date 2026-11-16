# R1fpAb: verified order prerequisites (partial contribution)

This contribution proves the exact maximal-order and ramification prerequisites
for the project quaternion datum. **It does not prove
`LeafQM.AV.R1UnivRigid.R1fpAb` and discharges no fine-moduli witness.**

Claim: [upstream issue 86, W28 witness/order scope](https://github.com/elliotglazer/diophantine-z-q/issues/86#issuecomment-6912048312).
The other clauses of Baba–Granath, González–Rotger, Elkies, Deligne components,
and Shimura reciprocity are outside this contribution.

## Exact proved statements

Namespace: `ZInQ.Contrib.CloudB4W28`.

- `orderLattice : Submodule ℤ LeafQM.B`, with
  `(orderLattice : Set LeafQM.B) = (LeafQM.O : Set LeafQM.B)` by `rfl`.
- `isMaximalOrder_orderLattice : QuaternionAlgebra.IsMaximalOrder orderLattice`.
  The definition is the exact upstream order predicate: an order that is equal
  to every overorder. No maximality or ramification assumption is supplied.
- `isIndefiniteRamifiedExactlyAt_two_neg_three :
  QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt (2 : ℚ) (-3 : ℚ) 2 3`.
  This is the exact upstream four-argument predicate, including both directions
  of the all-finite-places division criterion.
- `division_two` and `division_three`: every nonzero element of the actual
  quaternion algebra over `ℚ_[2]` or `ℚ_[3]` is a unit.
- `split_real : Nonempty ((ℝ ⊗[ℚ] QuaternionAlgebra ℚ 2 0 (-3)) ≃ₐ[ℝ]
  Matrix (Fin 2) (Fin 2) ℝ)`.
- `flt_order_trace_discriminant`: the reduced-trace Gram determinant on the
  original four order vectors is `(-36 : ℚ)`.

The entry module is
`ZInQKernel.Contrib.OneProof.R1fpAbOrderBridges`. Its three closed exports are
`r1fpAb_maximalOrder_bridge`, `r1fpAb_ramification_bridge`, and
`r1fpAb_order_bridges` (the conjunction). It imports the actual order-defining
module `ZInQKernel.HDecomp.QM.Structures`; it does not import `OneProof.Main`.

## Proofs and source preservation

Maximality uses the existing `GlueRepo.A1` vectors and determinant calculation,
not a replacement order. For any overorder, integral reduced norm and the four
integral trace pairings imply membership in the original integer lattice:
first use `u²-uv+v²` modulo 2, then modulo 3, then reconstruct the four integer
coordinates. The two finite congruence facts use kernel `decide`, not
`native_decide`. The only imported order-integrality result has its genuine
109-line minpoly proof in the licensed vendor cone.

Ramification uses genuine local isotropy criteria. The 2-adic norm bounds and
the nonsquare residue of 2 modulo 3 give anisotropy at 2 and 3; the local-unit
criterion gives isotropy at every other finite place. The actual completion
map is transported at its `primesEquiv` index by equality elimination and an
algebra equivalence, without generic topology-cast instances.

Upstream: `anthropics/fermats-last-theorem` at
`6e837e75355538c7f80bab5b956861e86c4eacc2` (Lean 4.33.1 / Mathlib `db584cd6…`).
The final arithmetic cone is **25 modules**, not the full fine-moduli cone.
`NOTICE.md`, `Vendor/AnthropicFLT/SOURCE_MANIFEST.json`, and the byte-preserved
`LICENSE`, `NOTICE.upstream`, and `ATTRIBUTION.upstream.md` record every move and
compatibility edit. No new Lake dependency is added.

## Frozen and refreshed inputs

- Frozen task input: `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`, dated
  `2026-11-16T07:44:03Z` (under one day old when work began).
- Refreshed review base: `e22df37cdef936f5b0f29ec09501854bea6c7316`.
- Lean 4.35.0: `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- The original target module `TailZ16.lean`, order-defining `QM/Structures.lean`,
  Lean toolchain and dependency pins are unchanged at the refreshed base.
  The target source SHA-256 is
  `b8fdc7e7c9c70411a952f5384c7b219c1db84cd8d34a586a060bbde8a0d6c4b1`;
  the order source SHA-256 is
  `0ee93924ff4f1b2ff63dc0562a2a3be166b950663bcbd423f19c9f9488a63441`.

No target, existing assembly, other contribution, root configuration, or pin is
edited. Only this helper/vendor directory and the new OneProof entry are added.

## Verification actually run

Heavy compilation ran on a fresh session-owned 32 GiB Linux node. The authorized
host was used only for its host-local GitHub login, public source/cache downloads
and source-only authors/reviewers. No credentials were transferred.

The frozen-input build compiled all 25 vendor modules and both bridge modules.
Closed-type examples, the literal carrier equality, the actual real tensor
splitting, and all eight axiom prints passed with kernel checking enabled.

The refreshed-base build compiled a 32-module focused source graph: four
unchanged baseline modules reused only after transitive source-fingerprint and
complete-facet copy checks, and **28 fresh contribution modules** (25 vendor,
two bridges, and the entry). Exit code 0, no failed or blocked modules.
The refreshed `ProofCheck.lean` and `EntryProofCheck.lean` both exited 0.
All eleven axiom prints contain exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Actual focused-build command:

```sh
python3 <REDACTED_WORKDIR>/direct_build.py \
  --root <REDACTED_WORKDIR>/current-repo \
  --out <REDACTED_WORKDIR>/build-current \
  --reuse-result <REDACTED_WORKDIR>/build-base/RESULT.json \
  --reuse-lib <REDACTED_WORKDIR>/build-base/lib/lean \
  --toolchain <REDACTED_WORKDIR>/toolchains/leanprover--lean4---v4.35.0 \
  --jobs 2 --max-failures 1 --module-timeout 300 \
  ZInQKernel.Contrib.OneProof.R1fpAbOrderBridges
```

Each dispatched compiler command was the actual Lean 4.35 executable with
`--threads=2 -Ddebug.skipKernelTC=false -R <source-root> -o <module.olean>`.
The full argv, selected `LEAN_PATH`, per-source hashes, all emitted facets,
original warnings/errors and command outputs are retained in the verification
packet. Original failed attempts are retained; they are not counted as passes.

Actual final axiom/type-check commands used `run_check.py` with the refreshed
source root and output library, on `checks/ProofCheck.lean` and
`checks/EntryProofCheck.lean`. Their underlying commands were:

```sh
LEAN_PATH=<recorded refreshed libraries> \
  <REDACTED_WORKDIR>/toolchains/leanprover--lean4---v4.35.0/bin/lean \
  --threads=2 -Ddebug.skipKernelTC=false -R <REDACTED_WORKDIR>/checks \
  <REDACTED_WORKDIR>/checks/ProofCheck.lean
# Same command on EntryProofCheck.lean.
```

For reproduction in an ordinary clean checkout (these are reproduction
instructions, not a claim they were the commands executed above):

```sh
lake exe cache get
lake build +ZInQKernel.Contrib.OneProof.R1fpAbOrderBridges
# Import the entry in a scratch file and run the same #check/examples/#print axioms.
lake env lean ProofCheck.lean
```

These are focused compiler/type/axiom checks, not a new imported-library kernel
replay, a hosted-CI acceptance, an integration into `frozenTarget`, or a merge.

## #discharges: unavailable, not a claimed discharge

**`#discharges` was NOT RUN successfully.** An attempt to build the original
`OneProof.Main`/`TailZ16` import closure stopped after 823 of 4,639 source modules
because an existing baseline module exceeded its 360-second bound:

```text
ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.
S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
```

The exact raw failure and original source binding are retained. The unrelated
baseline file was not modified. A bounded public-cache check found only
incomplete Main/TailZ16 facets and no validated source-bound replacement, so
these markers were not admitted as a verified cache.

The partial exports are closed arithmetic prerequisites; none supplies a
fine-moduli witness or proves an open field containing it. The entry therefore
imports the actual order-defining module rather than dragging unused TailZ16
through that baseline timeout. This is the explicitly permitted partial-PR
pivot, **not** a substituted target or a forged discharge receipt.

Because the PR also adds files outside `Contrib/OneProof`, it is out of scope for
the automatic contribution discharge workflow. Default green CI would not
establish a witness discharge either.

## Concrete fine-moduli drift pivot

The actual three fine-moduli roots reach **8,788 upstream source modules**.
The isolated Lean 4.35 probe had no missing external imports; it compiled 83
modules and failed in five independent components, then stopped at the
requested five-failure bound:

- `Def_AlgebraicCurve_SymmetricPower.lean:55–116`: `Aut` now has `asIso`, not
  `hom`, `inv`, `hom_inv_id`, `inv_hom_id` structure fields.
- `Def_AlgebraicCurve_DivisorClassGroup.lean:372`: old injectivity argument to
  `Finsupp.mapDomain_apply` no longer matches its map/summation signature.
- `Def_AlgebraicGeometry_ProjSpace.lean:364,369`: missing `coeff_zero`/`coeff`.
- `Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean:549`: missing
  `MvPolynomial.coeff`.
- `Def_Compat_Mathlib430.lean:61,68`: the old mapDomain simplification leaves
  the new Finsupp summation goal unsolved.

The user's explicit drift pivot was applied: no further full FLT modernization.
The universal QM family, object/level-3 comparison (including trace and 81-point
arguments), affine-to-global gluing, all-field point equivalences, and the actual
`R1fpAb` existential witness are **not supplied by this PR**.

## Review and AI assistance

AI-assisted source work used three disjoint single-writer lanes for
maximality, ramification, and cone/reuse analysis. Source-agent model requests
were `gpt-6.1-sol`; the effective serving identity is not asserted. The parent
coordinator separately obtained read-only independent mathematical/source
reviews. The final agent source/receipt review passed on 2026-11-16: the
coordinator independently matched all 28 owned Lean hashes, closed examples,
11 standard-three axiom outputs, successful compiler receipts, and the final
32/32 graph. This is an agent's review pass, not human reading or acceptance.
Static source review is distinguished from the actual compiler results above.
No human mathematical acceptance is claimed. No merge, landing, or human ping
is requested or authorized by this contribution.

## Public evidence sanitization

Public sanitization: private runtime paths and execution-service identifiers are omitted. Command representations use redacted placeholders and are not literal original argv. Mathematical source hashes, toolchain pins, actual result counts, axiom outputs and limitations are unchanged; unsanitized raw originals remain in private evidence. No new-head compilation or CI pass is inferred from this documentation-only change. License text and source attribution remain complete and unchanged. Historical metadata now records a sanitized projection, not byte-exact public raw receipts.

# CloudB3 W16 H102: verified pure finite-abelian helper

## Scope and API

Import `ZInQKernel.Contrib.CloudB3W16FiniteGroup.TorsionStructure`.

```lean
theorem ZInQ.Contrib.CloudB3W16FiniteGroup.nonempty_torsionBy_addEquiv_pi_zmod
    {M : Type*} [AddCommGroup M] {n r : ℕ}
    (hn : 0 < n)
    (hcard : ∀ d : ℕ, d ∣ n →
      Nat.card (Submodule.torsionBy ℤ M (d : ℤ)) = d ^ r) :
    Nonempty (Submodule.torsionBy ℤ M (n : ℤ) ≃+ (Fin r → ZMod n))
```

`AddSubgroup.torsionBy M (n : ℤ)` has definitionally the same carrier and additive
structure as `Submodule.torsionBy ℤ M (n : ℤ)`. Membership is equivalent to
`n • x = 0` by Mathlib's `AddSubgroup.torsionBy.nsmul_iff`.
The ambient group need not be finite. The rank is arbitrary, including zero;
the modulus may be one. There are no geometry, characteristic, degree, or
Mumford hypotheses/conclusions in this helper. The parent owns the bridge
from the existing PkgI2 multiplicative torsion object and the geometric counts.

The reusable prime-power API in `TorsionByCard` is:

```lean
theorem ZInQ.Contrib.CloudB3W16FiniteGroup.AddCommGroup.nonempty_addEquiv_pi_zmod_prime_pow
    {M : Type*} [AddCommGroup M] [Finite M]
    {p : ℕ} [Fact p.Prime] {k r : ℕ}
    (hexp : ∀ x : M, p ^ k • x = 0)
    (hcard : Nat.card M = p ^ (k * r))
    (htors : Nat.card (AddSubgroup.torsionBy M (p : ℤ)) = p ^ r) :
    Nonempty (M ≃+ (Fin r → ZMod (p ^ k)))
```

## Source and proof

Ported from AxiomMath/Stacks, immutable revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/GroupTheory/FiniteAbelian/TorsionByCard.lean` (AI-authored Frontier).
The original documentation/references remain in the port and Apache-2.0 `LICENSE`
is included. There is no individual author/copyright notice in the source file.

Before work, read the contribution guide and the actual original target
`ZInQKernel/OneProof/H/TailQ.lean:1257`, inspected pinned Mathlib
`GroupTheory/FiniteAbelian/Basic.lean`, the existing exponent-two FLT source,
and both Stacks `TorsionByCard.lean` and `TorsionCounts.lean`.

The chosen source proof is Nakayama plus CRT: multiplication by p has kernel
M[p], so M/pM has p^r elements; a lifted vector-space basis generates because
p is nilpotent, and a surjection from (Z/p^k)^r is bijective by counting.
Coprime torsion splits via Bezout and coordinatewise CRT. No new axiom or
assumed classification statement was introduced.

Compatibility edits: source module/public/expose wrappers removed; source
declarations isolated in the local helper namespace; explicit original
Mathlib imports plus Abel/Ring tactic imports; root AddSubgroup opened inside
the local subgroup namespace; autoImplicit disabled. No source proof argument
was changed. `TorsionStructure.lean` adds only the definitionally equivalent
Submodule API above.

## Verified checks (2026-11-16)

Base: `2dc949d688c407e32823c4e751679d66b2f40e65`, locally verified tree-identical
to original requested good base `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`.
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

All successful Lean commands serialized through
a shared local build lock, with
`LEAN_NUM_THREADS=2` and `lean -M 3072`:

```sh
lake env lean -M 3072 -o .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W16FiniteGroup/TorsionByCard.olean ZInQKernel/Contrib/CloudB3W16FiniteGroup/TorsionByCard.lean
lake env lean -M 3072 -o .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W16FiniteGroup/TorsionStructure.olean ZInQKernel/Contrib/CloudB3W16FiniteGroup/TorsionStructure.lean
lake env lean -M 3072 ProofCheck.lean
```

All three exit 0, no compiler warnings. Source: 2.87 seconds, peak RSS
2357976 KiB; wrapper: 2.15 seconds, peak RSS 2312920 KiB; check: 2.16 seconds,
peak RSS 2316500 KiB. Free memory at invocation: 60, 60, and 58 GiB respectively.
Local `ProofCheck.lean` imports only this support family, checks both signatures,
prints source and public theorem axioms, and elaborates the exact Submodule
signature from the source subgroup theorem. It is not a tracked build-time module.

Actual public axiom output:

```text
'ZInQ.Contrib.CloudB3W16FiniteGroup.nonempty_torsionBy_addEquiv_pi_zmod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Source general theorem and prime-power theorem both print exactly the same three
standard axioms. The subgroup membership-iteration lemma prints only `propext`;
no nonstandard axiom appears in any printed helper check.

Failed/interrupted attempts are not passes: an initial 6 GiB virtual-address
limit caused import to fail while reading an existing toolchain `.olean.private`;
an umbrella `import Mathlib` with `-M4096` exceeded the memory threshold at
6311772 KiB RSS before elaboration. The narrow imports reduced peak RSS below
2.3 GiB. The first narrow-import attempt exposed unresolved unqualified
`torsionBy` names in the relocated namespace; opening root AddSubgroup fixed
this compatibility issue. A nonlocked trial was cancelled when the parent
required every Lean invocation to use the lock.

Only new support files in this family were authored. A static scan of both Lean
files found no `sorry`, `axiom`, `native_decide`, `#eval`, `run_cmd`, `initialize`,
new syntax/notation/macros, or elaborators. `git diff --check` passed. An explicit
source-body comparison after removing only the local namespace-open line was
identical to upstream. Upstream source SHA256:
`10b4aed4fe3842d672b139eda9936174574162e9768db8ec8cbc66a7a834365e`;
local port SHA256:
`9fb0609bb69d82307825ed9d90b063c0f7d2718e903718a91484c713117bca6a`.

No Main build,
`#discharges`, geometric proof, target/config/pin edit, PR, issue/comment,
main push, or merge was performed. This helper alone does not discharge H102.

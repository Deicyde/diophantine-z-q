# Verification of the ingested derivative-switch packet

**Development profile: MET for the six listed abstract research theorems.**
This is a local native Lean verification and semantic review by the current
Codex assistant, not independent arithmetic acceptance or a release audit.
Date: 8 November 2026. Branch: `codex/derivative-switch-boundary-v13`.
Inherited baseline: `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`.

## Exact scope and inputs

The received ZIP SHA-256 is
`7242ed88ac6e93a30aed751f53b3bf252b4be332382011280e3d4f2d85afeb75`.
It and the original per-file hashes are retained in [PROVENANCE.json](PROVENANCE.json).
The ingested Lean source changes only its broad `import Mathlib` to the two
required imports; the six proof bodies are unchanged from the supplied packet.
The Python normalization check was strengthened from assigned ratios to actual
cycle, closed-functional and cofactor computations. A reusable native checker,
documentation and evidence were added.

The frozen reviewed specification is [CONTRACT.md](CONTRACT.md), SHA-256
`33e6ff462a61dac95afc27a016efc118cb75a0d550e33a206daca66055da96cb`.
The checked Lean source SHA-256 is
`63a9215fa55568069d2d1a7b2c3a7345ec21c7ad6a82203f42c5451ee4b8bbea`.
[RESULT.json](evidence/RESULT.json) binds both to the checker, Python model,
toolchain, dependency lock, and fresh target artifact hash.

Lean: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
`arm64-apple-darwin24.6.0`. Lake: `5.0.0-src+eb6cafb`.
Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
All nine dependency revisions matched the existing lock and their tracked
sources were clean. Only the 808-file closure of the two needed imports was
downloaded from the official Mathlib master cache. These are trusted published
artifacts, not independently rebuilt dependencies.

## Elaborated-statement crosswalk and proof review

The actual exported declarations and `AxesKernel` definition were inspected in
[statements-compact.log](evidence/statements-compact.log); the more explicit
types and transitive axioms are in [axioms-and-statements.log](evidence/axioms-and-statements.log).
All theorem names below have prefix `Research.DerivativeSwitch`.

| Declaration | Checked formal statement and proof connection |
| --- | --- |
| `finite_kernel_line` | For arbitrary fields and modules, the exact `AxesKernel` hypothesis implies `dF x = 0` iff `x` is a scalar multiple of `v`. Set the singular coordinate to zero in the combined kernel, and conversely insert the displayed scalar representation. |
| `singular_kernel_line` | The analogous equivalence for `dS y` and scalar multiples of `J v`, by setting the finite coordinate to zero. |
| `boundary_images_meet_zero` | Given `dF x = dS y`, apply `AxesKernel` to `(x,-y)`. The finite kernel equivalence makes the common image zero; the supplied equality gives both conclusions. |
| `no_identity_strict_square` | Under an explicit vector outside the scalar line of `v`, the universal equality `dF x = dS (J x)` contradicts `AxesKernel` applied to `(x,-J x)`. This excludes precisely the fixed-strict boundary square. |
| `Volume.area_action` | For arbitrary commutative rings, expand the two-by-two coordinate action and its signed area. The ring normalization proof establishes multiplication by the actual determinant. |
| `Volume.area_neg_one` | Specialize the previous identity to determinant `-1` and input area `1`; the result is area `-1`. No primitivity or division is used. |

The first four do not formalize dimensions, nonzero arithmetic classes,
characteristic-zero restrictions, or the occurrence of `AxesKernel` in an actual
Selmer complex. Their algebraic conclusions are valid at the greater formal
generality. Obtaining dimension one additionally requires nonzero `v` and the
actual exact sequences. The volume declarations concern pairs over a ring;
fractional DVR complements, quotient modules and Fitting ideals are ordinary
algebra bridges explained in the contract, not additional formal declarations.

The generic nonidentity eta construction and the impossibility at a test with
`U=F` are retained in the contract as ordinary algebra. They are not promoted
into claims about the Lean module. Actual integral class-functional tensors,
Poitou–Tate boundary–cup adjunctions and arithmetic normalization remain open.

## Checks and axioms

The [logged commands](evidence/commands.json) were run through
[verify.py](verify.py), with a fresh project output tree and
`-Ddebug.skipKernelTC=false`. Both target compilation and the explicit
statement/axiom audit exited zero without diagnostics requiring a repair.
The earlier direct `lake env lean` invocation also passed; the evidence-bearing
run compiles the named target explicitly and does not substitute the default
`ZInQ` build for it.

Every one of the six theorems uses exactly `propext` and `Quot.sound`.
`Classical.choice` was permitted by the predeclared conventional allowlist but
was not used. No `sorryAx`, custom axiom, native-evaluation assertion, or kernel
bypass was found. The frozen quarantined target still contains its inherited
single `sorry` and was neither changed nor imported.

The Python checks passed 3,800 exact integral-volume trials over divisibility
exponents 0 through 18, one equal-rank fixed-strict countermodel, and 132
normalization cases over the displayed common-strict complexes. Each tensor
coordinate is now computed from all cofactors; the wrong-functional control
recomputes the coordinate after multiplying only the singular functional by
two and detects its nonunit ratio. These finite checks do not prove a universal
arithmetic assertion.

The source guard reports 48 byte-identical inherited helper modules and retains
the quarantined target. The audit-history checker reports the preserved
historical and current bindings and rejects its 7 and 19 negative controls.
Those checks are structural; the [raw logs](evidence/audit-history.log) say so.

Boundary review also checked the meaning of the hypotheses. For `v=0`, the
kernel equivalences assert zero kernels; they do not assert dimension one. The
outside-vector hypothesis is necessary: for one-dimensional `F=S=K`, `v=1`,
`J=id`, and zero boundaries into the zero space, `AxesKernel` holds and the
boundary equality holds, while that outside-vector hypothesis is false. The
nontrivial two-dimensional countermodel in the contract supplies a consistent
ordinary-algebra realization of the intended no-go assumptions. The volume
identities remain valid in characteristic two and in the zero ring; no
nontriviality assertion is inferred from them.

## Assurance gates

| Gate | Status | Evidence and scope |
| --- | --- | --- |
| A01 Scope and snapshot | PASS | Received archive, original hashes, pinned baseline, final source hashes, dependency revisions and fresh artifact recorded. |
| A02 Frozen specification | PASS | Reviewed contract hash above; explicit assumptions, six declarations and exclusions. |
| A03 Semantic review | PASS | Actual elaborated types and referenced definitions inspected against the crosswalk, by the current assistant. |
| A04 Reviewable proof | PASS | Four elementary kernel arguments and two ring-identity arguments mapped above; original proof bodies retained. |
| A05 Build and lint | PASS | Explicit pinned target compilation, source escape scan, relevant Python models, frozen-source and audit-history guards. No full helper rebuild claimed. |
| A06 Transitive axioms | PASS | All six audited; exactly `propext` and `Quot.sound`; allowlist enforced by the Lean audit. |
| A07 Boundary analysis | PASS | Zero vector, necessary outside-vector hypothesis, divisibility, common strict torsion, exact localization relation and rescaled-functional controls. |
| A08 Native export replay | NOT_RUN | Optional for this development profile; source compilation with native kernel checking is the observed A05 result. |
| A09 Protected statement comparator | NOT_RUN | Semantic source/type comparison is A03; no separately protected challenge comparison claimed. |
| A10 External checking | NOT_RUN | Local macOS run without `--paranoid`, as requested. |
| A11 Release clean reproduction | NOT_RUN | Fresh local target outputs and pinned caches are recorded; no release environment reproduction claimed. |
| A12 Independent mathematics review | NOT_RUN | Current-assistant review only; non-author acceptance remains pending. |
| A13 Evidence and claim discipline | PASS | Bound logs, source hashes, provenance and explicit open arithmetic obligations. |

Required development gates A01–A07 and A13 pass. This does not satisfy or claim
the release or critical profiles. No acceptance record has been authored on
behalf of another reviewer.

## Tool documentation and limitations

Consulted on 8 November 2026: the [Lean 4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/),
[Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/),
[proof validation reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/),
and the exact pinned Mathlib [cache README](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Cache/README.md)
and [cache IO source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Cache/IO.lean).
Installed 4.35 help and the pinned cache implementation controlled the commands;
mutable latest documentation was not used to upgrade the toolchain. The cache
source documents the dedicated `MATHLIB_CACHE_DIR`, so setup kept cache writes
inside this task's writable workspace.

No `--paranoid`, external kernel, Linux bubblewrap isolation, human acceptance,
hosted CI, manuscript integration, remote push, PR publication, or merge is
claimed. No main-theorem or arithmetic determinant-switch status was promoted.
Reproduce the scoped checks using [README.md](README.md).

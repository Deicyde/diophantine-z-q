# Lean: local conjugation and boundary interfaces for derivative switches

Proposed destination: `elliotglazer/diophantine-z-q:main`, from the owner's fork
branch `codex/local-boundary-interfaces-v13`. **Prepared locally only; no new
push or PR is authorized.** This text is for review of the exact bounded package.

This adds four Lean modules proving lower-level compatibility deductions used
in the derivative-switch functional construction:

- derive the common local conjugation unit from the twisted representation,
  and descend the identity to Mathlib's actual H¹ with conjugate coefficients;
- compute the cup coboundary correcting a local-condition representative to
  global localization, and remove it under a chain trace;
- prove the degreewise cone comparison and show that a supplied right homotopy
  inverse preserves the common global projection and its localizations on homology.

The [application table](APPLICATION.md) links each premise and theorem to exact
V13 consumers and records the arithmetic data still needed. These results do
not construct global arithmetic duality, every localized inverse or the stored
paired functionals. They do not prove the full determinant switch, restricted
converse or main Diophantine theorem. The finite tame congruence is not asserted
for a fixed characteristic-zero prime; the two cone-sign conventions are
translated explicitly.

All four mathematical files are unchanged selections from
`33483f751e6dcd3f91fb303969838aca33ad0458`, based directly on upstream
`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`. The support includes a reproducible
runner, exact source bindings, adverse controls, concise application/specification
and separately authored model reviews. No bulk integration commit, unrelated
research packet or raw source archive is included.

Native Lean 4.35.0 freshly compiled the four modules and audited all 41 selected
proof roots. Their transitive axioms are confined to `propext`, `Quot.sound`
and `Classical.choice`; elaborated statements were reviewed. Focused controls
detect wrong signs, nonclosed directions, non-chain traces, unsupported
inverse/localization inference, coefficient mismatch, extra J and arbitrary
functional rescaling. A separate reviewer reproduced the controls. Imported
dependency caches remain trusted; no paranoid or external-checker pass is
claimed. A fresh checkout of the frozen preparation commit reproduced the
native receipts byte for byte and all finite-control results; the sole
author-control receipt difference was Python-version metadata, disclosed in
the evidence. See [VERIFICATION.md](VERIFICATION.md).

The foundation PR #15 and frozen 39-target package are unchanged, unimported
and supported by their own evidence. This is a non-release addition: it does
not amend the manuscript, PDFs, construction artifacts, catalogs, historical
acceptances or mirrors, so their release-regeneration duties do not apply.
The wider arithmetic bridge and parked four-term theorem remain separate.

The proof and preparation used Codex agents under Chey Loveday's direction.
Source/context attribution is retained in [ORIGIN.json](ORIGIN.json) and the
application note. Distinct model reviewers supply bounded nonauthor reviews;
they are not independent human specialists and may share reasoning/toolchain
failure modes. Repository-required hosted CI and the independent-agent-audit
check remain pending on any eventual authorized PR. Open as a draft until those
requirements are satisfied; no maintainer acceptance is claimed here.

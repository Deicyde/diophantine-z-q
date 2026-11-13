# aut-o-finite (fleet note)

**Verdict: `AutOInnerFinite` (from scratch/mobius-glue/MobiusGlue.lean §4) is PROVED. It needs no
leaves and no glue Props, only the standard axioms.** The explicit computation is also compiled:
`Aut(𝒪)/Inn(𝒪^×)` has exactly four classes, represented by conjugation by 1, i, j, ij
(`Exact.autO_mod_inner_exact`).

- File: `scratch/aut-o-finite/AutOFinite.lean`. It imports only `ZInQKernel.HDecomp.QM.Structures`
  and `ZInQKernel.HDecomp.Textbook.SkolemNoether`.
  - Target copied verbatim (diff empty).
  - §7 and §8 are mobius-glue's proof: an extension of α to B, Skolem–Noether from the kernel's
    theorem `TSkolemKW.leafSkolemNoether`, and the normalizer descent on |nrd|.
  - §9 is new: `rep_cover` and `rep_distinct`, the latter via reduced norms 1, −2, 3, −6 and the
    fact that ±2, ±3, ±6, ±12, ±18 are not rational squares.
- Compiles: `lake env lean` gives 0 errors and 9 linter warnings. `#print axioms` for
  `autOInnerFinite`, `normalizerFinite`, `autOInnerFinite_of_normalizer`, `autO_mod_inner_exact` and
  `autOInnerFinite'` all give [propext, Classical.choice, Quot.sound] (VERIFIED, run2.txt).
- Remains: nothing for this Prop. It is ready to adopt as one kernel module under
  `ZInQKernel/HDecomp/QM/`. The consumers in mobius-glue still rest on `CurveRatFactor`,
  `CurveSurj` and `TorsionStructure`, which are not part of this task.
- Report: docs/research/aut-o-finite.md. Log: scratch/aut-o-finite/log.md.

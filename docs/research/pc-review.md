# pc-review: host build and review of the cloud deliverables for fork issue #83, with round 2

Task pc-review, 2026-11-17, branch `wip/pc-review` (= `wip/pc-from-rc` at 5404a9fe3 + the cloud
branch `rc/s12-descent-inputs-20261117` at f13d7a5ad + fork main at f3402e89; merge commit
807515d42). Sources: `diophantine_zq.tex` L1019–1121; Elliot's supplement S12
(`parity-frozen-4eaee875.tex`, md5 5b8d6f645f240603135c536001dd4756, read from
`~/dzq-wt/pc-from-rc/scratch/upstream/`, not copied). Log: `scratch/pc-review/log.md`.

## Verdict

@@VERDICT@@

## The integrated main theorem

`ZInQKernel/Contrib/OneProof/PoleCompletenessIntegrated.lean` (new; imports the cloud's
`PoleCompletenessFromRCCore2` and round 2's `PoleCompletenessFromRCGenuine`, not
`ZInQKernel.OneProof.Main`):

```
theorem ZInQ.Manuscript.PCReview.poleCompleteness_of_restrictedConverseGenuine_integrated
    (hRC  : SelmerTwoPower.RestrictedConverseGenuine) -- Theorem 5.3 over the genuine Selmer condition
    (h54  : PoleS12.Lemma54)       -- Lemma 5.4 over Tau Ceti's Sel₂ and Sel_{2^∞}
    (hKum : PoleS12.KummerSelmerM) -- #Sel₂(E_ℓ/ℚ) = #SelM ℓ
    (hB   : PoleS12.BCDTThmA)      -- modularity
    (hK   : PoleS12.KolyvaginThm1) -- Kolyvagin, r = 1
    : Manuscript.PoleCompleteness  -- Theorem 5.2
```

Proof: the cloud's `poleCompleteness_of_restrictedConverse_core2` at `P := SelmerCorankOne`, with
round 2's `lemma54At_of_printed h54 hKum` for `Lemma54At` and `kolyvaginRankOne_of_printed hB hK`
for `KolyvaginRankOne`. Against round 2's final theorem
(`poleCompleteness_of_restrictedConverseGenuine`), the hypothesis **`MordellWeil` is gone**: the
cloud proves Mordell's theorem for every `E_ℓ`, `ℓ ∈ ℚ ∖ {0}` (`PoleRC.mordellWeil_curve`), and
that is the only place the route used it. A second form
(`…_integrated'`) runs round 2's own `PoleS12.simultaneousConstruction` with the cloud's
`mordellWeilM`; same hypotheses.

| hypothesis | status | kind |
| --- | --- | --- |
| `RestrictedConverseGenuine` | **open** | Theorem 5.3 of the manuscript itself (Sections 7–9, App. E–G); not a published result |
| `Lemma54` | leaf (cited) | the manuscript's `lem:corank` over genuine definitions; a consequence of Poonen–Stoll (Cassels–Tate pairing alternating) and the Kummer sequence; not a single printed statement |
| `BCDTThmA` | printed leaf | consequence of BCDT Theorem A (modularity); `IsModular` keeps less than the print |
| `KolyvaginThm1` | printed leaf (preprint) | the `r = 1` case of Kolyvagin's Theorem 1 as cited (MPIM preprint 90-69); locator UNVERIFIED; only the rank is used |
| `KummerSelmerM` | textbook glue | Silverman X.1.4 specialised to `E_ℓ` and the x-form `LocM`; not a printed statement; not in Lean |

Proved in Lean on the way (no hypothesis): bookkeeping and rescaling (round 1), the complete
2-descent with the count `descentGlueM` (round 1), `MatrixRealization` (twice: round 2 and cloud),
`DimThreeCount` (twice), the four local images `LocalTwo/Three/Bad/Good` (cloud) and
`LocalGoodUnram`, `NecAt` (round 2), Mordell–Weil for `E_ℓ` (cloud).

@@BODY@@

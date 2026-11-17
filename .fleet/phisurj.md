# phisurj (2026-11-16)

**Verdict: −2, no new leaf.** On base wip/leaf-fold33b (H `13/20 on 33`), `mumfordPhiSurjectiveAC` is removed by
rerouting its readers and `weilPairingMumford` is proved. After the fold, H is `12/19 on 31`. The only inputs are
fields that are already open: L1 `picRepresentableAbVar`, L2 `picZeroAbVar`, and the textbook leaf
`mumfordTorsionAlgClosed` (proved on origin/proof/picard-fibres-20261116, not merged here).
Report: `docs/research/phisurj.md`.

**What compiles.** All of the following compile with axioms `propext`, `Classical.choice`, `Quot.sound`, no `sorry`
and no build-time code. Each file under `ZInQKernel/Contrib/OneProof/` builds with `lake build`.
- `PhiAmpleIsogenyOpen.lean`, main theorem `PhiSurj.phiAmpleIsogeny_of_open : L1 → L2 → torsion →
  T09Pic.PhiAmpleIsogeny`. It uses no cohomology:
  - `AVDesc.formula_nondeg_right`: Mumford §20, right kernel, by fpqc descent along `[n]`;
  - `card_isDT_le`: `#{c translation-invariant, cⁿ = 1} ≤ n^{2g}`;
  - `dim Pic⁰ ≤ dim A`;
  - a dimension-count surjectivity lemma.
- `PhiSurjDescent.lean`: generic descent of an invariant trivialization.
- `WeilPairingMumfordOpen.lean`: `PhiSurj.weilPairingMumford_of_open : L1 → L2 → torsion →
  T09Pic.WeilPairingMumford`. It is pic-dict's assembly with every input now a theorem. The left kernel is proved by
  counting, which removes the use of §8 Thm 1.
- `MumfordSquareMulN.lean`: `MumfordSquareAC` and `MumfordMulNPicZeroAC` from L1 and L2.
- `PhiAmpleIsogenyWeil.lean`: earlier variants, plus the named Prop (a) `TIClassesInPicZeroAC`. With it,
  `mumfordPhiSurjectiveAC_of_ti_open` proves the field's exact statement.
- `#discharges` lists `OpenAddedLeaves20.weilPairingMumford` as discharged by `weilPairingMumford_of_open`; it still
  assumes `[PicRepresentableAbVar, PicZeroAbVar, MumfordTorsionAlgClosed]`.
- Autofold dry run (`scratch/phisurj/autofold-weil.json`): `13/20 on 33 -> 13/19 on 32`; the printed module
  compiles.
- Hand fold for both fields (`scratch/phisurj/FoldTailZ49.lean`, `OpenAddedLeaves21 = {L1, L2}`) and
  `FrozenTargetDryRun.lean`: both compile.
- origin/wip/weil-proof is merged; `WeilFormula*.lean` are needed by the new files.

**What remains.**
- `MumfordPhiSurjectiveAC` itself is not proved. Its statement quantifies over translation-invariant classes, so it
  also contains (a): every such class is a point of `Pic⁰`, i.e. NS injectivity. (a) for torsion classes follows
  from the counts here. For non-torsion classes no cohomology-free route was found. No reader needs it.
- The integrator steps: the hand fold (a reroute is not autofoldable), the Main switch, and dropping the kinds.tsv
  and claims.tsv rows. They are not done here.

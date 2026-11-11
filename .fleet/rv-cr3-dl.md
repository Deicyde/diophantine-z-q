# rv-cr3-dl: final report

Adversarial review of `RouteK/RankDL.lean` (cr3-dl, `feb18a7b`, KERNEL_PLAN `fec256b4`) and of the
rv-cr3-rank follow-up (`350f7798`), at main `d549dabb`. Full report: `docs/research/rv-cr3-dl.md`. No
Lean file was edited.

## Verdict

- **Lean: no blocker.**
- **Documentation: one blocker, B1**, `KERNEL_PLAN.md:152–155`. "… so
  `…_of_sixContactMin_certifiedRankRk` assumes the least" is false. `CertifiedRankRk → CertifiedRankDLRk`
  holds (12-line proof in report §1.4, elaborated with standard axioms), so the `…_certifiedRankDLRk`
  variant assumes no more. Lean proves no comparison between `Rk` and `DLRk`. Fix: "the least of these
  three", and preferably add `certifiedRankDLRk_of_certifiedRankRk` to `RankDL.lean`.

## Item 1: CertifiedRankDLRk and CertifiedRankDLAdmRk

- **Curves.** The curves are exactly those of `poleCompleteness_of_certifiedRank` / `descent_lemma`:
  `C_{D.d₁}` and `C_{|D.d₁ θ|} = C_{D.d₁ θ.natAbs} = C_{D.d₂}`. Only the quantifiers differ: `∀` over
  all `Inputs` triples (stronger than needed, which is why `DLAdmRk` exists) and `∃ D` (weaker, which
  is legitimate because `poleSoluble_of_slots_infinite_order` works for any `D`).
- **Vacuity.** `Inputs (-7) 1 7` holds (proved in a probe), and `Slots` is nonempty whenever `Inputs`
  holds (`exists_slots` uses only `Inputs` fields; instantiated in the probe). Every `D` has
  `d₁ ≡ 5 (mod 8)`, squarefree, `d₁ ≥ 21`, `#Sel₂ = 8` on both curves, so no slot choice is degenerate.
  At `(−7, 1, 7)` the claim reads "`7q₀` is congruent for some prime `q₀ ≡ 3 (mod 8)` with
  `(q₀/7) = 1`".
- **Main variant.** Same `assembly_AP` term as `…_sixContactMin_certifiedRank` with only the PC argument
  replaced. No extra hypothesis.
- **Docstrings.** Nothing is called "narrowest", and the dependence on `Inputs`, `Slots`, `betaOf`,
  `thetaOf` and `Admissible` is stated. Remark R1: the `DLRk` docstring's "or Kriz's 2-converse" and its
  literature list without Rédei's formula do not follow from the cited `TYZRk → DLRk`. Adding
  `Rk → DLRk` fixes this.

## Item 2: follow-up 350f7798

- `certifiedRankRk_of_certifiedRankTYZRk` is genuine (Corollary 4.4 `det_M5b_eq_one` and Theorem 3.6
  `det_M5b_eq_T5b`).
- **Corank lemma.** The citation is correct as stated and matches manuscript `lem:corank` (line 1072).
  Cassels–Tate on `Ш/Ш_div` is nondegenerate and alternating; alternation is what makes the finite part
  `F ≅ A × A` at 2. So `dim F[2]` is even and the corank is 1, with no finiteness of `Ш` assumed. The
  circular "when finite" wording is gone everywhere.
- **TYZ chain.** Accurate. For the Sel₂ forms the chain is Corollary 4.4, Theorem 3.6, then the
  `RedeiFormula` Prop, then TYZ Proposition 1.1, then Gross–Zagier. `CertifiedRank` needs Proposition 0
  first, and its bullet includes it. Remark R4: the wording could be read as placing Proposition 0 in
  tyz-5b.
- **KERNEL_PLAN.** The DL paragraph states only proved facts. The Rk paragraph has B1.

## Item 3: build and axioms

- `lake build ZInQKernel`: success (9913 jobs), no errors, no `sorry`.
- `lake env lean scripts/print_axioms.lean`: 45/45 entries exactly `[propext, Classical.choice, Quot.sound]`.
- Evidence: `scratch/rv-cr3-dl/` (build-tail.txt, axioms.txt, probe.txt, log.md).

## Suggestions

1. Fix B1 (one sentence in KERNEL_PLAN.md).
2. Add `certifiedRankDLRk_of_certifiedRankRk` (report §1.4) to `RankDL.lean` and print_axioms. Then
   reword the `CertifiedRankDLRk` docstring's literature sentence (R1), and add a pointer to `DLRk` from
   the `CertifiedRank` docstring's "as narrow as the proof allows" sentence (R3).

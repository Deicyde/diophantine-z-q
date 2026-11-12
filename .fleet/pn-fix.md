# pn-fix: rv-pn-encoding and tyz-t1 applied to the Lean encoding of Proposition N

Branch `wip/pn-fix` (from integrate-w26). Files: `ZInQKernel/Hypotheses/TYZInputs.lean` (docstrings
only; comment-stripped code identical), `ZInQKernel/RouteK/PropN.lean` (docstrings plus new Witness
declarations; stripped diff: 0 lines removed, 179 added), `scripts/print_axioms.lean` (+3). Log:
`scratch/pn-fix/log.md`.

**TB-1, F2 (docstrings).** `M` is now described as the ℤ[i]-span in A(ℍ'_n) of A[(1+i)³] and the
Z(e) (e | n, e ≡ 5, 7). Z(e) ∈ A(ℍ'_n) by L1321 for e ≡ 5 and L2558 for e ≡ 7. `β` is the restriction
of one lifting β' to M. β' maps M into itself by L2581/L2184, Lemma 3.21(1),(4) (any lifting, L2500)
and F4 ([i] is defined over ℚ(i); standard, not printed). So F5 (ℍ'_n/ℚ Galois) is not needed. Where
F5 is still mentioned as the alternative, it is credited to Prop 3.2(1) with Cox, Lemma 9.3, and
marked as not printed by TYZ (they use it at L2594–2595). The module and `TYZInputs` docstrings now
list the two unprinted standard facts: Hecke's continuation of L(C_n, s) (CM; assumed by TYZ, not
proved; the I7 conjunct) and F4. The line locators listed in the I1-lines and TB-2 nits are corrected.

**F1 (Lean).** Witness section: `Pw_congr`, `Pw_fst`, `Sw`, `Sw_fst`, `Φw`, `Φw_Sw`, and
`witnessData₀` (Z := update Zw n (Sw L n), P := update (Pw L) n 0). From these,
`genusData_nonempty_iff_parities`: for squarefree n ≡ 5 (mod 8) with L 1 = 1 and L n = 0,
`Nonempty (GenusData L n)` holds iff Σ_{e≡5} L(n/e)g(e) and Σ_{e≡7} L(n/e)g(e) are even. The forward
direction is lemmaN2 plus finalStep. `genusData_nonempty_of_parities` (the theorem the task asked
for) is the backward direction. The review's construction worked with one cosmetic change: k =
−N/2 − x.re + x.im, which differs from the review's k by a multiple of mk 4 = 0. lemmaN2 is already
proved on this base, so nothing here depends on sorry. Together with `genusData_nonempty` (the
L n ≠ 0 case), this shows that GenusData's content is exactly the conclusion of Proposition N's final
step. Not done: the review's optional `tyzInputs_iff` / `tyzInputs_of_readingA` (outside step 2's
list). The Witness docstring says this assembly is not written in Lean.

**T1.** Both module docstrings now give tyz-t1's result. Theorem 3.3 holds as printed. The constant
does not depend on d₁ for fixed d₀: this is written out from TYZ's Theorem A.9 and checked on 30
values of n (73 pairs) from Heegner points on X₀(32). What remains external is Theorem A.9 itself
(Yuan–Zhang–Zhang made explicit by TYZ, deduction omitted at L3079).

**Nits.** Applied to these docstrings: I1-eps-proof-cite and F4 (eps_53: cite multiples1 and note
that lemmaN2 needs it); i2-b1 (LemmaTwoEight stated as a congruence, plus the w_K = 3 remark);
i7-hecke option 2; L-integrality (Theorem 1.2 dropped); I1-Z7. TB-4/F3/g-beta7-mod4: the statement is
unchanged, and the docstring says the exact form needs integer g. lemmaN2: X ∈ M.

**Checks.** `lake build ZInQKernel` succeeds. `print_axioms`: 91 entries (88 + 3 new), all
[propext, Classical.choice, Quot.sound]. `check_target.py`: FrozenTarget matches.

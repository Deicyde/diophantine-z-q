# rv-cr3-trust (fleet report)

Adversarial review of `docs/research/cr3-trust.md`. Note: `docs/research/rv-cr3-trust.md`; log, scripts
and Lean check: `scratch/rv-cr3-trust/`.

**Verdict: adopt after the listed repairs.** I found no gap in the mathematical route:
- TYZ inputs give Proposition N;
- Proposition N gives `ord_{s=1} L(C_d,s) = 1`;
- Gross–Zagier with an auxiliary field gives a point of infinite order;
- RK9 and Mordell–Weil in Lean give the Selmer forms.

Repairs:
1. **False Lean claim** (§0.2, Summary 1, §3 docstring draft). cr3-trust says `CertifiedRankTYZClRk`
   does not imply the three forms with the premise `#Sel₂ = 8` (TYZ, TYZCl, 5b). In fact it implies all
   three, and also DLAdmRk. VERIFIED in Lean (`Check.lean`, standard axioms). So it implies every form,
   and the docstring clause "except the three…" must go.
2. **§0.3 out of date.** Both "missing" variants exist: `…_sixContactMin_certifiedRank5b` (no 22P) and
   `…_sixContactMin_certifiedRankDLAdmRk`. Both use only the standard axioms (VERIFIED). That makes 14
   forms, not 13.
3. **D2 supplier.** Analytic rank 1 needs `L(C_d^K,1) ≠ 0`. Murty–Murty (derivatives) is the
   analytic-rank-0 input, so cite Bump–Friedberg–Hoffstein, Waldspurger or Friedberg–Hoffstein 1995.
   Add "level `32d²` allowed?" to the locator check.
4. **After rv-prop-n.** Proposition N (C1–C3) has two model reviews [M2] and no human review. A1 has two
   reviews, A2 three. In B5 the inclusion `ℍ'_{d₀} ⊂ ℍ'_n` is a quoted fact; in B8 one lift `β'`
   serves all `Z(e)`.
5. **Minor:**
   - locators for Shimura 1971 (modularity of CM curves) and for the conjugation sign of Heegner points;
   - a sentence that Mathlib's `Point` law is the chord-tangent law (the `Inf` forms avoid the question);
   - A6: on the 6 curves with no point, `ellrank`'s lower bound 1 lists no point, so it is not certified;
   - rv-cr3-rank (supplier of A5/E3) is still unmerged;
   - KERNEL_PLAN.md and the docstrings of CertifiedRank, CertifiedRankRk and CertifiedRank5b still lead
     with Kriz or "GZ–Kolyvagin", and KERNEL_PLAN lacks the two new variants.

Checks:
- The analytic step is right as used. For every `d` in the forms, `N = 32d²`, the Heegner hypothesis
  (`D ≡ 1 (8)`, all `p | d` split) can be met, and the twist has root number +1.
- Kolyvagin's published papers remain on the route inside TYZ (B4, B9). cr3-trust says so.
- Independent recheck of A6 (exact class numbers, PARI `ell2cover`):
  - 386 values with `T5bCl = 1`, as cr3-trust found;
  - on a new sample of 30: `#Sel₂ = 8`, root number −1 and conductor `32d²`, all 30;
  - a Heegner field with `L(C_d^D,1) ≠ 0` (numerical) on 16 of them.

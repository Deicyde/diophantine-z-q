# cr3-adopt: adopt the reviewed trust statement for CR₃

Branch `wip/cr3-adopt`, from `81bb5d8f` (integrate-w19). Log: `scratch/cr3-adopt/log.md`.

## What changed

1. **`docs/research/cr3-trust.md`**: every repair of `rv-cr3-trust.md` §6 applied, with a
   changelog at the end:
   - `CertifiedRankTYZClRk` implies **every** form. That includes the three with the premise
     `#Sel₂ = 8` (TYZ, TYZCl, 5b) and DLAdmRk. Summary 1 and §0.2 give the chains of existing
     theorems (`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`,
     `certifiedRankTYZ_of_certifiedRankTYZRk'`, `certifiedRankTYZCl_of_certifiedRankTYZClRk'`,
     `certifiedRank5b_of_certifiedRankTYZ`, `certifiedRankDLRk_of_certifiedRankTYZRk`,
     `certifiedRankDLAdmRk_of_certifiedRankDLRk`), citing `scratch/rv-cr3-trust/Check.lean`. No new
     declarations were added.
   - There are 14 forms, and each has a SixContactMin variant. §0.1 and §0.3 now list
     `…_sixContactMin_certifiedRank5b` (`Rank5bSec3.lean:51`) and
     `…_sixContactMin_certifiedRankDLAdmRk` (`RankDL.lean:232`). Locations were rechecked at
     `81bb5d8f`.
   - D2 (nonvanishing of the central value `L(C_d^K, 1)`): the supplier is
     Bump–Friedberg–Hoffstein, or Waldspurger, or Friedberg–Hoffstein 1995. Murty–Murty is dropped
     as the supplier because it covers the derivative case. The question whether level `32d²` is
     allowed is added to §2.4 item 3, and §2.2 and §3 are changed to match.
   - Review counts after rv-prop-n:
     - C1–C3 are [M2] (two model reviews, no human review);
     - A1 is [M2] and A2 is [M3] (a new mark, defined in the header);
     - §2.1, §2.6 and the Summary are updated to match.
   - B5: the inclusion `ℍ'_{d₀} ⊂ ℍ'_n` is a fact quoted from TYZ. B8: a single lift `β'` serves
     all `Z(e)`. C3: the proof uses only the `ε`-classes (5,1), (7,1) and (7,3).
   - Minor items:
     - locators added: Shimura 1971 (D1), and Gross–Zagier 1986 and Gross 1984 for the
       complex-conjugation sign of Heegner points (D3); both are also in §2.4;
     - A5: one sentence that Mathlib's group law on points is the chord-tangent law, and that the
       Inf forms avoid the group law;
     - A6 and Summary 4: on the 6 curves without a certified point, `ellrank`'s lower bound is
       not certified;
     - rv-cr3-rank is now merged and is cited as the supplier of A5 and E3.
   - §3: the drafts are repaired as rv-cr3-trust §5.2 asks. §4 is updated.
2. **`docs/research/nt-tyz.md`**: a dated note at the end with rv-prop-n's corrections: F4 is
   not used in §4.4; one lift `β'` serves all `Z(e)`; the inclusion is quoted; the list of
   `ε`-classes used. The text above the note is unchanged.
3. **Lean docstrings and comments only**, in 11 files:
   - `Hypotheses/CertifiedRank.lean`: the docstring of `ZInQ.CertifiedRank` is now the §3 draft.
   - `RouteK/Rank/Statements.lean`: the trust paragraphs of `CertifiedRankRk` and
     `CertifiedRankTYZClRk` are now the drafts; `CertifiedRankTYZRk` now names the auxiliary field.
   - Aligned to the published route (TYZ + Proposition N + Gross–Zagier with an auxiliary field;
     Kriz is an alternative that is not needed):
     - `Rank5b/Row5b.lean` (`CertifiedRank5b`: Gross–Zagier gives rank ≥ 1 in place of "GZ and
       Kolyvagin (Lemma 5.5)");
     - `Selmer/Covering.lean` (`CertifiedRankSel`: TYZ route first, Kriz second as an
       alternative);
     - `Sec3/TYZ.lean` and `Sec3/RedeiStatement.lean` (Murty–Murty dropped; rv-prop-n cited);
     - the `RankVariants.lean` module docstring;
     - the variant docstring in `Rank5b.lean` (now points to the variant without 22P);
     - two passages in `Main.lean`;
     - `RankInf.lean` and `RankDL.lean`.
   - `Hypotheses/Pole.lean` is unchanged: its "Gross–Zagier–Kolyvagin" describes the
     manuscript's own proof of the restricted converse.
4. **`KERNEL_PLAN.md`**, CR₃ passages only:
   - the PC row of the table and the CR₃ paragraph now lead with the published route, with a
     pointer to `cr3-trust.md` and `rv-cr3-trust.md`;
   - the two new variants are listed;
   - one sentence says that `CertifiedRankTYZClRk` implies all 14 forms.

## Build and axioms

- `lake build ZInQKernel`: success (9919 jobs).
- `lake env lean scripts/print_axioms.lean`: all 61 entries show only `[propext, Classical.choice,
  Quot.sound]`.
- Comment-only check: `scratch/cr3-adopt/strip_check.py 81bb5d8f HEAD` strips line comments and
  nested block comments and docstrings (it respects string and char literals). After stripping,
  all 11 changed `.lean` files are identical. A mutation test shows that the script detects a
  changed term and ignores a changed docstring.

## What is left

- The checks that need the network, in cr3-trust §2.4:
  - the journal text of TYZ;
  - the Gross–Zagier hypotheses for `N = 32d²`;
  - the theorem number in BFH / Friedberg–Hoffstein and whether level `32d²` is allowed;
  - Birch–Stephens;
  - Shimura 1971;
  - the locator for the conjugation sign.
- A human or source-holding check of the three quotations that Proposition N is sensitive to
  (rv-prop-n §9).
- Optional: drop the older CR₃^5b variant that assumes 22P (`Rank5b.lean:37`).

## Problems and suggestions

- No problems. The build emits many warnings (790 lines matching "warning"). They are not caused
  by this task, since the Lean code itself is unchanged, but I did not compare them against a base
  build.
- Suggestion: the blueprint, if it repeats the Kriz-first wording for CR₃, should be aligned in a
  separate task. This task's scope excluded `blueprint/`, and I did not check it.

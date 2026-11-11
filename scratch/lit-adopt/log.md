# lit-adopt log

## Step 1: ZInQKernel/Hypotheses/CR3Literature.lean
- From scratch/wk-cr3/Literature.lean, namespace ZInQ.Literature; #print axioms lines and
  frozenTarget_of_sixContactMin_literature dropped (main theorem moves to MainLiterature.lean).
- (a) FunctionalEquation5 restricted to 0 < s.re < 2; docstring explains the Gamma junk value
  at 0, -1, ...; rootNumberVanishing_of_functionalEquation passes `by norm_num` twice at s = 1.
- (b) GrossZagierKolyvagin renamed GrossZagier; supplier for L(E^K,1) ≠ 0 is BFH 1990 (via
  Waldspurger) or Friedberg-Hoffstein 1995; Murty-Murty removed; Kolyvagin remark kept.
- (c) module docstring with a Trust section (one item per Prop, L-series, IsLContinuation.eq).
- Deviation: import ZInQKernel.RouteK.RankVariants dropped (only the main theorem used it).
- Deviation: IsLContinuation.eq's last step split into two `have`s (100-char line limit).
- `lake build ZInQKernel.Hypotheses.CR3Literature`: success (only "module system" import
  warnings from Mathlib's per-module imports).

## Step 2: ZInQKernel/Hypotheses/JHeight.lean
- From scratch/wk-h/BackToU.lean, namespace ZInQ.JHeight, imports Hypotheses.HeightMin; #print
  axioms line dropped. Kept Fh, Gh, Jmap, cert_x, cert_y, G_ne_zero, C0, dvd_C0,
  abs_monomial_le, lower_bound, twelve_mul_ratHeight_le, heightX, JHeightBound, heightH6_eq.
- sixContactMin_of_jHeightBound : JHeightBound Mult.S_mul → SixContactMin (proof as drafted).
- Dropped SixContactMinAt (no general-S form of SixContactMin exists in Height/HeightMin;
  SixContactMin is stated directly) and contactSupport_pos' (HeightMin's contactSupport_pos).
- JHeightBound docstring rewritten as specified; module docstring rewritten (no Tier 2).
- Three proof lines rewrapped to ≤ 100 characters.
- `lake build ZInQKernel.Hypotheses.JHeight`: success, no warnings in the new file.

## Step 3: ZInQKernel/MainLiterature.lean, imports, print_axioms
- Three variants (sixContactMin_tyzRow5b_functionalEquation5_grossZagier,
  jHeightBound_certifiedRankTYZClRk, jHeightBound_tyzRow5b_functionalEquation5_grossZagier),
  each proved directly from ..._of_sixContactMin_certifiedRankTYZClRk.
- ZInQKernel.lean: imports CR3Literature, JHeight, MainLiterature appended.
- scripts/print_axioms.lean: 3 variants (new comment section after the variants) and 5
  reductions (new section at the end).
- Two lines over 100 characters: the `theorem` lines of the two variants whose prescribed names
  are 109 and 108 characters long (unavoidable).

## Step 4: checks
- `lake build ZInQKernel`: success (9922 jobs).
- `lake env lean scripts/print_axioms.lean`: 69 entries (61 before + 8), all
  [propext, Classical.choice, Quot.sound].
- `python3 scripts/check_target.py`: FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean.
- No sorry / native_decide / implemented_by / extern / axiom in the new files.

## Step 5: .fleet/lit-adopt.md written

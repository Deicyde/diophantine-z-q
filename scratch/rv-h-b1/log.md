# rv-h-b1 work log

Object under review: origin/wip/h-b1 (commit d7d8d78f) docs/research/h-b1.md, scratch/h-b1/.
Manuscript: diophantine_zq.tex in this worktree (last touched 97cec7fd, "November 5"), = N5.

## 1. Inputs read
- h-b1.md (363 lines), scratch/h-b1/b1_checks.py and its saved output (sections A-E).
- N5 L377-570 (Theorem 4.1 setup, integral model L441-507, pullback L509-523, K and A L524-530,
  conjugates and W_0 L532-566), N5 L800-857 (L814 Raynaud step, L847-850 p > R).
- N5 L436-438 itself already says Y_3 "with all its determinant components"; N5 L475-477 says
  the b11 quotient "represents exactly the full-three moduli problem, so its generic fiber is Y_3".

## 2. Rerun of scratch/h-b1/b1_checks.py
- Copied verbatim to scratch/rv-h-b1/b1_checks_rerun.py; ran with ~/pyenv/bin/python -I (0.7 s CPU).
- Output scratch/rv-h-b1/b1_checks_rerun.output.txt is byte-identical to h-b1's saved output.
- What the script does NOT check: maximality of O (asserted in N5 L405); local normalizer
  index 2 (printed as "standard"); completeness of the list of elliptic types in M9 (it only
  finds one element of each wanted (trd,nrd)); §E computes inertia FROM the Prop. TS formula, so
  it checks the case analysis of PR(i) steps 2-3, not Prop. TS itself.

## 3. Uses of good reduction / the model in N5 (grep, lines < 1200)
- grep "integral model|proper model|good reduction|stable model|X_{35}|universal abelian|
  smooth projective|semistable|potentially good": hits L443, 464, 473-474, 483, 529, 558,
  596 (CM elliptic curve, unrelated), 740 (p-adic Hodge, unrelated), 753, 781, 817, 849.
- Locator error in h-b1 §5 (and in the task text): the conjugate good-reduction sentence is
  N5 L557-558, not L563-566 (L563-566 is the Milne Hodge-endomorphism paragraph).
- h-b1 §5 omits two downstream uses: L753 ("unramified outside T ∪ {ℓ}, since there ... A has
  good reduction") and L781 ("L_v/Q_p unramified and A has good reduction", p ∉ T ∪ {3,5}).
  Both are uses of the L529-530 statement at primes outside T; Lemma PR(ii) covers them
  (3 ∈ S ⊂ T). So h-b1's "nothing downstream of L530 uses the integral model" is true in
  substance (they use only the L529-530 conclusion) but the table is incomplete.
- L814: adjoins A[3] (A[5] at p = 3) and applies Raynaud's criterion [Silverberg-Zarhin 3.5]
  for semistability: no model used. CONFIRMED h-b1's claim.
- L848-849 "the surface has good reduction" for p > R: p may lie in supp M_S(u) ⊂ T, so this
  needs good reduction also where K ramifies; PR(ii) (all v ∤ 3) gives it.

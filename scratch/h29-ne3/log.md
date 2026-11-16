# h29-ne3 results log

Base 0f61e9c0 (h29-fix head). Task: replace leaf TYZLemma29Printed (w_K form) by
(a) TYZLemma29PrintedNe3 (printed Lemma 2.9, n != 3, no w_K) and (b) TYZThm21At31 (Theorem 2.1 at (3,1),
w = torsionOrder (QNeg 3) / 2); prove TYZLemma29Printed from (a), (b) as glue.

## Step 0. Locators (VERIFIED, read in ~/tyz-src/Period7.tex)
- Theorem 2.1 L554-559 (2w_K = number of roots of unity: L558); P(d1,d2) = sum over Cl_n of f_n chi (L551-552);
  chi_{d1,1} = 1 convention L510.
- Lemma 2.9 L1062-1066, proof L1068-1077.
- Theorem 2.4 begins L613, item (1) L615-623.
- Lemma 2.5 L645-661; uniform Tamagawa measure printed L654-661, proved L694-705.
- Legendre and [JP, Theorem 5] cited at L533 (one line).
- pi_Z defined at L542. A_0, pi in A_0: L715-720; restriction to 1+2x, orthogonality to 1, (-1)^tr: L722-727;
  dim A_0^U = 6: L760.

## Step 1. Drop-in `scratch/h29-ne3/TYZLemma29Mod2.lean` (VERIFIED: compiles, `lake env lean`, no warnings)
New leaves (defs, namespace ZInQ.Contrib.TYZDecomp.H29Split):
- `TYZLemma29PrintedNe3`: ∀ n [NeZero n], Squarefree n → 1 < n → n ≠ 3 → (n%8=1 ∨ n%8=3) → ∀ τ admissible,
  ∀ f test vector, ∀ ℓ IsLcalSign, ∃ ε : ℕ → ℤ, (∀ d, ε d = ±1) ∧ Σ_{d ∈ pairIdx n} ε d * (ℓ (n/d) * ℓ d)
  = genusPeriodTV n τ f. (No w_K.)
- `TYZThm21At31`: ∀ τ admissible (n = 3), ∀ f test vector, ∀ ℓ IsLcalSign, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
  Σ_{t : ClassGroup (𝓞 (QNeg 3))} f (τ̂ (clLift 3 t)) = ε * ((torsionOrder (QNeg 3) / 2 : ℕ) : ℤ) * (ℓ 3 * ℓ 1).
  No vanishing clause.
`TYZLemma29Printed` (w_K form) kept as an intermediate def, now proved.
Glue proved: `torsionOrder_qNeg_three` (= 6, IsCyclotomicExtension.Rat.torsionOrder_eq + TYZLcal
isCyclotomicExtension_three), `wK_three_eq_torsionOrder`, `subsingleton_classGroup_three` (TYZLcal.pid_three),
`sqClasses_three` (= univ), `genusPeriodTV_three`, `pairIdx_three_eq` (= {1}, decide), `lemma29At_three`,
`tyzLemma29Printed_of_ne3_thm21`, `tyzLemma29Mod2_of_sixLeaves`.
Import added: ZInQKernel.Contrib.TYZChain.Lcal (no cycle: Lcal does not import the contribution).
Docstring/locator fixes (review §5): Thm 2.4(1) L615-623; Lemma 2.5 measure printed L654-661, proved L694-705;
Legendre and JP cited at L533; π_ℤ defined at L542; JP docstring no longer asserts regularity; deprecated
dif_pos/if_neg replaced.
Env note: worktree lacked lean/.lake (unknown module prefix 'ZInQ'); copied from ~/dzq-prune (identical lean/ZInQ).

## Step 2. Module build, MainEdit (VERIFIED)
- Copied the drop-in to ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean (worktree only, not committed);
  `lake build ZInQKernel.Contrib.OneProof.TYZLemma29Mod2`: success.
- `scratch/h29-ne3/MainEdit.lean` (Main.lean with h29 replaced by the six leaves): compiles;
  `ZInQ.OneProof.frozenTarget` axioms [propext, Classical.choice, Quot.sound] (MainEdit-output.txt).
- First #discharges run failed at the frozenTarget example: the copied .lake/build Main.olean was built from a newer
  source (OpenResearchLeaves20) than this worktree's Main.lean (OpenResearchLeaves19). Rebuilding Main and
  Discharges from the worktree source.
- kinds-rows.tsv (six rows, published, LEAF/LEAF, flags 'restricted: ...; unread' or 'unread') and autofold.json written.

## Step 3. #discharges (VERIFIED)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` from the worktree sources (19.5 min, success),
  then rebuilt the module, then `lake env lean scratch/h29-ne3/DischargesH29Ne3.lean` (exit 0):
  DISCHARGES [h29] by H29Split.tyzLemma29Mod2_of_sixLeaves, still assumes the six leaves
  (LegendreThreeSquares, JonesPallX2Y2Z16, TYZTestVectorExists, TYZLemma29PrintedNe3, TYZThm21At31,
  TYZProp23Printed); axioms [propext, Classical.choice, Quot.sound].
  `#discharges: 66 open hypotheses, 1307 theorems checked, 7 discharge one`.
- `h29ne3_frozenTarget` and MainEdit's `ZInQ.OneProof.frozenTarget`: axioms [propext, Classical.choice, Quot.sound].
- ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean restored to the tracked version (not committed).

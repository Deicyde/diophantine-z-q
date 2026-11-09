# aud-ap log

## Step 0 (start)
- Worktree at c399a64 (ap-lean report commit). No .lake; need `lake exe cache get` + build.

## Step 1 (scope)
- Diff merge-base(main)..HEAD in ZInQKernel/, lean/, scripts/: only new files (PrimeAP.lean, AP/*.lean, AP.lean)
  plus Main.lean (+23: imports, docstring bullet, new theorem) and ZInQKernel.lean (+1 import). Target.lean,
  SixContactMin, CertifiedRank, FrozenTarget untouched. CORRECT.
- Variant signature: (hH : SixContactMin) (hCR : CertifiedRank) (hAP : GoodPrimeAP) : FrozenTarget — same
  conclusion and same two other hypotheses as `exists_bounded_integer_polynomial_defining_integers_of`. CORRECT.
- S_b = S_ht ∪ catalogue, S_ht = primes ≤ 324 (filter of range 325), catalogue = catalogueFinset W 22 324 (Finset,
  so finite; nonempty since contains 2). Coe to catalogueSet proved (Syntax.catalogueSet_eq). No junk: S_b is the
  paper's S_b. CORRECT (to double-check catalogueFinset def).
- Build: started `lake build ZInQKernel` (Mathlib packages copied from a sibling worktree, cache get had no network).

## Step 2 (definitions read; grep)
- grep of PrimeAP.lean, AP.lean, AP/*.lean for sorry|admit|axiom|native_decide|implemented_by|extern|set_option|
  unsafe|partial|opaque|csimp|macro|elab|run_cmd|#eval: no hits (one false hit: "Lean." in a docstring). Main.lean
  diff: no hits. CORRECT.
- GoodSlopeAP = GoodSlope with field `old` replaced by `OldBounds p t ∨ (0 < F(t) ∧ PoleAbsorbHyp p t)`; fields
  not_mem_contactSet, ne_one, contact, few verbatim. OldBounds = old field verbatim. Matches note 2′. CORRECT.
- PoleAbsorbHyp ℓ t: 1 ≤ v_ℓ(den t), ℓ=2 → 3 ≤ v_ℓ(den), ℓ ∤ num − c·den for c ∈ patternShifts = 𝒞∪{1}.
  Lowest terms automatic (num/den). F(t)>0 carried by field 2′. Matches Lemma P hypotheses. CORRECT.
  (ℓ prime not in the def; only used at ℓ ∈ S_b, all prime.)
- SlopeRepresentationAP = SlopeRepresentation with GoodSlopeAP 0. Chain slopes_of_int_AP … assembly_AP: same
  statements as originals with h22 : SlopeRepresentationAP; assembly_AP gives ⟨specPstar c3, …⟩ = same P_*. CORRECT.
- slope_complete_AP: same conclusion as slope_complete (SlopePred t ell certShifts), hypothesis GoodSlopeAP. CORRECT.
- lemmaP_three, pole_input_valuations_AP statements read; match note §3.2 (3) (e : ℕ allowed 0: more general). CORRECT.
- Prop AP (slopeRepresentationAP_of_goodPrimeAP): K=(mx−mn).toNat, mx=max(1,A′+60), mn=min(−60,A′−1), u=x+mx·v,
  t=(u/v, (A′v−u)/v, −10). Matches §3.3. CORRECT.
- Observation: internal definitions cannot weaken the variant: its conclusion is FrozenTarget and its hypotheses
  are SixContactMin, CertifiedRank (unchanged) and GoodPrimeAP, which mentions only GoodSlopePrime, S_b (and
  pointCount, catalogue). The only way the variant could "say less" is if GoodPrimeAP were false or not what GT+D give.

## Step 3 (independent computation: scratch/aud-ap/goodprimes.py, output goodprimes.out)
- Own transcription of the Lean GoodSlopePrime (point counts over F_p, ∃ root r of r²=2, d(±r) ≠ 0, gcd = 4)
  vs the CM description of nt-22p §2.1, all primes 324 < p < 20000: 240 good, 0 mismatches. CORRECT.
- Literal predicate below 324: {17, 41, 73, 97, 241, 257, 313}; 2 and 7 are not good (p = 2: r = 0, counts 3, 3).
- Relative density in (324, 2·10⁶): 15821/148867 = 0.1063; Euler product (l < 10⁶) 0.1060. Consistent with Prop D.
- Longest AP of good primes in (324, 3·10⁵) found: length 10 (x = 53681, v = 9240). No local obstruction seen.

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

## Step 4 (sources)
- Green–Tao arXiv math/0404188v6 TeX (fetched): second theorem of §1, label sz-primes, "Let A be any subset of the
  primes of positive relative upper density, limsup π(N)^{-1}|A∩[1,N]| > 0 ... Then A contains infinitely many
  arithmetic progressions of length k for all k." Numbered 1.2. Line ~1947 (§10): "our method also extends to prove
  Theorem 1.2 ... The only significant change ... pigeonhole ... residue class b mod W" (outline only). CORRECT as
  quoted in the GoodPrimeAP docstring; caveat present.
- Conlon–Fox–Zhao exposition arXiv:1403.2957: complete proof of Theorem 1.1 only; dense-subset form listed as an
  extension (§ "Szemerédi's theorem in the primes"). Confirms referee caveat F3.
- Referees: rv-nt22p-ap (F1–F6; F4 = formalization status, now addressed by ap-lean), rv-nt22p-proof (findings 5, 6,
  9–11). ap-lean statements agree: PoleAbsorbHyp keeps the redundant seven-numerator clause (cosmetic, finding 6);
  field 2′ (not 2″); pole_input_valuations_AP concludes ≥ 4 on S_b (rv says conclusions could stay ≥ 103C+8; ≥ 4 is
  what PoleCompleteness uses — kernel-checked chain, so harmless).

## Step 5 (Lean runs, one at a time)
- `lake build ZInQKernel`: Build completed successfully (9593 jobs), 7m01s; no "declaration uses 'sorry'". CORRECT.
- `python3 scripts/check_target.py`: "FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean". CORRECT.
- scratch/aud-ap/Axioms.lean (output axioms.out): variant type
  SixContactMin → CertifiedRank → GoodPrimeAP → FrozenTarget (main: … → FixedPrimePattern → FrozenTarget);
  #print axioms variant and slopeRepresentationAP_of_goodPrimeAP: [propext, Classical.choice, Quot.sound]. CORRECT.
- scratch/aud-ap/Derive.lean (output derive.out): Lean forms GreenTaoDense (GT 2008 Thm 1.2, one progression,
  d ∈ ℤ \ {0}) and PropDUpper (positive relative upper density of GoodSlopePrime);
  theorem goodPrimeAP_of_greenTao_propD : GreenTaoDense → PropDUpper → ZInQ.GoodPrimeAP compiles against the branch,
  axioms [propext, Classical.choice, Quot.sound]. (First attempt: decidability-instance mismatch, fixed by `convert`.)
  So GoodPrimeAP follows from GT 1.2 + Prop D with no extra condition. CORRECT.

## Step 6 (complete proof of the dense form; section numbers)
- Tao–Ziegler arXiv math/0610050 (Acta Math. 201 (2008)) TeX: main theorem (label mainthm, "Polynomial Szemerédi
  theorem for the primes"): A ⊂ primes with limsup |A∩[N]|/|P∩[N]| > 0, P_i ∈ ℤ[m], P_i(0)=0 ⇒ infinitely many
  x+P_1(m),…,x+P_k(m) in A with m > 0. With P_i = (i−1)m this is GT 1.2 with v > 0 directly. The general A is
  handled in the proof (§2, pigeonholed class b mod W, footnote says b=1 possible only for A = P). Statement VERIFIED;
  proof not refereed here. Gives the citation repair for the GT caveat.
- GT arXiv v6 section list: the "our method also extends to prove Theorem 1.2" remark is in §11 "Further remarks"
  (sections: 1 Intro … 7 Bohr sets, 8 Furstenberg tower, 9 measure, 10 correlation, 11 Further remarks). Docstring
  and rv-nt22p-ap say §10. Cosmetic (published numbering unchecked).

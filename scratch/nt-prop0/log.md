# nt-prop0 log

## Step 0 (sources read)
- CR3: ZInQKernel/Hypotheses/CertifiedRank.lean (`ZInQ.CertifiedRank`), system in
  ZInQKernel/RouteK/System/Selmer.lean (`Config.IsSol`, `E1`, `E2`, `D`, `twoAdicRows`),
  configuration of d in RouteK/Assembly/Realize.lean (`natConfig`, `natClass`, `primeCfg`),
  `legBit p a = if IsSquare (a : ZMod p) then 0 else 1` (RouteK/Slots/Symbols.lean:17).
- Prop 0: descent-alt §4.1; referee proof rv-slot-k-descent §1.1-1.5 (place 2 by x = 1/4, all 4
  classes); slot-k §2.1, §4.1, §4.3 (estimate "months", SPECULATIVE).
- Mathlib: same rev 56a0058 as ~/dzq-wt/cr3-check/.lake/packages/mathlib; grep there (no fetch).

## Step 1 (design of the definition; restart after interruption)
- Mathlib at ~/dzq/.lake/packages/mathlib (rev 56a0058 = manifest rev). Inventory delegated, output
  to scratch/nt-prop0/mathlib-inventory.md.
- Definition chosen: projective 2-covering D_{a,b}: a z1² − b z2² = d w², a z1² − ab z3² = −d w²
  (z ≠ 0) over a field K. Sel₂(d) := {(a,b) squarefree integers : D_{a,b}(ℝ) ≠ ∅ ∧ ∀ p, D_{a,b}(ℚ_p) ≠ ∅}.
- Field-generic lemma K (VERIFIED on paper): (a,b) ∈ δ_K(E(K)) ⟺ D_{a,b}(K) ≠ ∅, with explicit
  points (1,1,1,0), (0,1,1,1), (1,0,1,1), (1,1,0,1) for the four torsion classes; w = 0 ⟺ trivial class.
- Local analysis plan: p | d odd by valuation of x (cases v<0, v=0, v=1 with t≡±1, v≥2); ∞ by sign of x;
  2 for d≡5 by v(x) and x mod 8 (8 classes; non-torsion ones need √(1−16d²) ∈ ℚ₂);
  p ∤ 2d: necessity by valuations, sufficiency needs δ_{F_p} surjective (group law + halving) + Hensel.

## Step 2 (tests of the local computations; scripts in scratch/nt-prop0/)
- t_two_adic.py: for 13 d ≡ 5 (8), the points x = 1/4, −4d², d(1+4d)/(1−4d), −d(1−4d)/(1+4d) lie on
  C_d(ℚ₂) and have classes (1,5),(7,7),(5,10),(3,14) exactly; sampling rational x (v₂ ∈ [−6,6],
  odd part < 2^12) on 6 curves gives exactly the 8 classes {(1,1),(1,5),(7,7),(7,3),(5,10),(5,2),(3,6),(3,14)}.
- t_fp_surj.py: δ_{F_p} onto (F_p*/F_p*²)² for all odd p < 400 and all d mod p (13808 pairs, 0 fail).
- t_charsum.py: Jacobsthal S(n)² + S(gn)² = 4p (p ≡ 1 mod 4), S ≡ 0 (p ≡ 3 mod 4), p < 600: 0 fail.
  Fibre bound 8N ≥ p − 15 − |S(d²)| and N > 0 for p ≥ 29 / p ≥ 19 (p < 200, all d): 0 fail.
- KEY FINDING: the good-prime sufficiency (unit pairs locally soluble at p ∤ 2d) needs neither the
  group law nor Hasse: x-form of the covering + character-sum count + Jacobsthal's identity
  (Σ_n S(n)² = p(p−1)(1+χ(−1)), elementary) + unit-square Hensel lift. Small p < 29 by finite check.

## Step 3 (end-to-end test, inventory, routes)
- t_prop0.py: 30 random d ≡ 5 (8) (1–4 primes < 60; a few repeats), every pair in the box
  ⟨−1,2,p|d⟩²: local solubility in x-form at ∞, 2, p | d (classes of sampled points ∪ torsion)
  ⟺ system E1,E2,R,D(c=5): 40512 pairs, 0 mismatches.
- Inventory (scratch/nt-prop0/mathlib-inventory.md): Hensel (hensels_lemma, Hensel.lean:460),
  unitCoeff_spec, toZMod, toZModPow, Padic.valuation, Rat.isSquare_iff_even_factorization,
  quadraticChar_sum_zero, jacobiSum_nontrivial_inv, Subgroup.index_range; MISSING: unit-square criteria
  in ℚ_p, Hilbert symbol, Σχ(quadratic), Kummer/2-descent, Fintype of E(F_q), Hasse.
  Repo: Model/Descent/Kummer.lean has SqClass, sqc, kummer (x-coordinate class on shortCurve b,
  homomorphism kummer_add), kummer_eq_one_iff, phi; MW via AddCommGroup.fg_of_descent'.
  (Agent suggested Chevalley–Warning at p ∤ 2d: wrong, degrees 2+2 = 4 = number of variables.)
- Route R3 idea: hypothesis "C_d(ℚ) infinite" (d congruent) suffices with only the NECESSITY half of
  Prop 0 + δ hom/injective + MW for C_d/ℚ (repo machinery). Bigger investment.

## Step 4 (note §2.1–2.5 written)
- t_witness_sympy.py (run with uv + sympy): the 7 witnesses of Lemma T give exactly the quotients of
  the table (symbolic), and every quotient is a square in ℚ₂ for 250 values d ≡ 5 (8): 0 failures.
- Lemma B (p | d) and Lemma T (2) written in the uniform form "∃ i j (k), a d^i (−1)^j and
  b 2^i (−d)^j (5^k) are squares", which turns into bits in §2.6.

## Step 5 (Lean probe; note §3 written)
- scratch/nt-prop0/Probe.lean (run with `lake env lean` from ~/dzq, Mathlib 56a0058, imports
  Padics.Hensel + Padics.RingHoms only, ~3 s per run, 4 runs one at a time, load < 4):
  `probe_isSquare_of_toZModPow_three` (u ∈ ℤ₂, toZModPow 3 u = 1 ⇒ IsSquare u) and
  `probe_isSquare_of_toZMod` (p odd, u unit, residue square ⇒ IsSquare u), both via `hensels_lemma`.
  ~75 lines total, axioms propext/Classical.choice/Quot.sound. So SQ(a)(⇐), SQ(b)(⇐) are cheap.
- scratch/nt-prop0/ProbeQ.lean: Lemma Q (Σ_ξ χ((ξ−e)(ξ−e′)) = −1, e ≠ e′, any finite field of odd
  characteristic) from `jacobiSum_nontrivial_inv`, `IsQuadratic.inv`, `quadraticChar_sq_one'`:
  compiles first try, ~35 lines, standard axioms.

# rv-pd-paper log

## Step 1 (read note, section 1 by hand, Mathlib Dirichlet statement)
- Lean def GoodSlopePrime read (PrimePattern.lean): pointCount = Nat.card{(x,y): y^2=x^3+ax}+1, gcd = 4. Matches note 1.1.
- Lemma 1.1 CORRECT (sum of 1+chi). Lemma 1.2 CORRECT. Lemma 1.3 CORRECT. Lemma 1.4 CORRECT (second moment 2p(p-1), phi(0)=0, square classes).
- Lemma 1.5 CORRECT: g(-D^2/x) = (D^2/x^2)^2 g(x) recomputed; roots +-D swapped by tau, not in X; fixed points +-iD, g(iD) = -2iD^3 != 0, both-or-neither by oddness; m even.
- Prop 1.6 (1)-(4) CORRECT: chi(id)chi(id') = chi(-7) = chi(7) = (p/7) = -1; v2(2(p+1)) = 2 as p = 1 mod 8; odd part argument; n_- = 0 case harmless.
- Lemma 2.1 CORRECT. delta_L = (1/8) prod (l-2)/(l-1) >= 3/(8(L-1)) CORRECT (telescoping over integers 5..floor L).
- Mathlib 56a00585 PrimesInAP.lean:348 LSeries_residueClass_lower_bound: statement exactly as quoted. Lemma 3.1 CORRECT
  (classes disjoint, prime-power contribution <= sum log p/(p(p-1)); Lean needs summability at x>1, dominated by x=1 case).

# mcheck-22p (manuscript check of prop:fixed-prime-pattern, tex L1267-1704, and the L954 step)

**Verdict: no error found.** Report: docs/research/mcheck-22p.md (23-row Manuscript check table, Known issues).

- gcd(d1,d2)=4 and p∤d1d2 (first priority): secured correctly. p≡1 (8), p≡3 (7) make the two reductions opposite
  quadratic twists (N(75-53√2)=7, (7/p)=-1), so d1,d2 = p+1∓2a with a²+b²=p; the 2-part of the gcd is 4 and p∤d1d2
  (Hasse); an odd ℓ divides the gcd iff ℓ | gcd(a,p+1). The progression rules out ℓ≤L (p≢-1 mod ℓ; the text
  compresses this, gap filled); ℓ>L is handled by a Selberg-sieve count of bad primes, O(X/(L log X)), beaten by the
  (log L)^-44 loss by choosing L first. Numerics: 60 small primes counted directly; 30 primes of ~450 bits in the full
  residue pattern (orders via Cornacchia + point checks), all gcd=4; 3 pattern primes built with 337 | gcd(a,p+1)
  have gcd=1348, so congruences alone cannot give gcd=4 and the sieve step is necessary.
- Rest of the proof: finite data, local densities (exact counts at q=331,337), Green-Tao hypotheses (pairwise
  non-proportional forms, complexity <= 20, local factors positive and uniformly bounded below), the two Selberg sieve
  applications, the fibre bound and the order of choices all check. log β_q >= -484/q² filled in (true constant ~242).
- L954: h(u) <= h(j)+log(2·4000^6) < h(j)+74 is correct; proved in Lean (scratch/mcheck-22p/L954.lean, standard axioms).
- Compiles (Mathlib only): Statement.lean (the Prop), Finite.lean (minors, residues, Dirichlet), L954.lean.
- Remains / UNVERIFIED (no network): GT/MN/GTZ locators; the manuscript's reliance on a "2026 corrected" GTZ arXiv v5 +
  erratum should be confirmed to leave GTZ Thm 1.3 unchanged; Silverman locator V.2.3.1(b) for integrality of Frobenius
  looks wrong (fact standard).

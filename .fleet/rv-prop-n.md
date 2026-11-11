# rv-prop-n — second review of Proposition N (nt-tyz §4) and F1, F2

**Verdict: holds as stated** (relative to the TYZ inputs I1–I7 as quoted). Each inference of nt-tyz §§4.3–4.4
was re-derived by hand. Lemmas N1 and N2 and the bracket identification were recomputed with independent code:
453 abstract configurations with 1–9 primes, I2 used only modulo 2, 0 mismatches. The inputs are consistent
with one another. The proof uses Lemma 2.8 (I2) only modulo 2, so rv-nt-tyz's finding that Lemma 2.8 is off
by the odd factor 3 at `m = 3` does no harm. On the `ε`-classes, N2 needs only `ε = ±1` at `(5,1), (7,1),
(7,3)`. The value at `(5,3)` is irrelevant; mutation tests confirm both points. Numerics (PARI, 51 inputs in
two runs): 22 curves of analytic rank 3 (up to 7 primes, mixed classes 3 and 7) all have `T_5a = T_5b = 0`.
All 19 values with an odd genus sum have analytic rank 1. Rédei bits and class groups agree on every sample.
Proposition N's conclusion is exactly what `CertifiedRankTYZClRk` needs (`T5bCl` is TYZ's `T_5b` with
`g = #Cl²`), and through the proved `RedeiFormula` also what `CertifiedRankTYZRk` needs. The step to a
point of infinite order is Gross–Zagier, outside Proposition N.

Minor corrections to nt-tyz (none changes the logic):
- F4 is not used in §4.4.
- nt-tyz should say that one lift `β'` serves all `Z(e)`.
- nt-tyz should list which `ε`-classes are used.

rv-nt-tyz agrees on every point. No disagreement.

**Most serious issue:** not a gap but the basis. The proof rests on quotations of the recursion of TYZ §3.1
(coefficient `ε𝓛(d₁)`), Lemma 3.21(1), (4) and Theorem 3.5's first assertion. These were checked against
the source once (rv-nt-tyz) and never by a human. The numbers support them indirectly. Seven rank-3 values
have `g(n) = 1`, which refutes any even-coefficient variant of the recursion. They also give six new
counterexamples to the literal Theorem 1.2: 134805, 141141, 887565, 2379405, 2422245, 13498485.

**For cr3-trust:** cite Proposition N as now. Add four things: two model reviews, no human review; I2 is used
only mod 2; Theorem 1.2 and Proposition 3.4 are not used; the quotations are from arXiv v1 only.

**Single next step:** a human (or source-holding) referee checks those three quotations against TYZ.

Report: `docs/research/rv-prop-n.md`; scripts and log: `scratch/rv-prop-n/`.

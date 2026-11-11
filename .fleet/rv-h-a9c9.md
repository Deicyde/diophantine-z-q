# rv-h-a9c9 (second review of A9's Milne paragraph and C9's Li–Shimura sentence)

**Verdict.**
- A9, N5 L564-577: **holds as stated**. VERIFIED: the full argument, plus an exact computation
  (`scratch/rv-h-a9c9/a9_centralizer.py`). In `B = (−1,3)_ℚ` (discriminant 6), the commutant of
  `R_J` has dimension 4 for generic `J`, and 8, isomorphic to `M₂(k)`, for `k = ℚ(i)` and
  `k = ℚ(√−3)`. Repairs are citation-level only: swap the course notes for Mumford §§1-3 with
  GAGA; name the "fixed by `Aut(ℂ/ℚ̄)` ⇒ defined over `ℚ̄`" step; the `milne-av` bibliography
  entry names Thm 12.1(a), not 2.8-2.9.
- C9, N5 L768-774: **holds after expository repairs**.
  - Li's formula makes the conjugate span Fricke-stable for any nebentypus: argued, and checked
    numerically on 30 newforms (`c9_li_fricke.py`, agreement to 1e-95).
  - The span is stable under Hecke, `Aut(ℂ)` and Fricke, so Shimura 1973 Thm 1's hypothesis is
    met whatever its exact form. That form is Fricke stability according to the upstream audit,
    which I could not check against the paper. This settles the provision rv-h-trust left open.
  - Duality side and conductor invariance are checked.

**Most serious issue.** In C9, "Shimura's … Euler-factor identity therefore show that `r₅` is a
constituent of `V₅(A_f)`" is an incomplete inference. A total characteristic-polynomial identity
does not give a constituent: Klein-four counterexample in `c9_charpoly_divisibility.py`. The
missing input is standard: the `K_f`-linear Eichler–Shimura relation (`V_λ(A_f)` of rank 2,
`tr Frob_p = a_p`), then Chebotarev, Brauer–Nesbitt and Faltings. On that route Li's Fricke step
is not even needed. The conclusion is not refuted.

**Consequence.** No disagreement with rv-h-trust. All four passages new in N5 now have two model
reviews, so h-trust item (vii) can be closed. Statuses are unchanged (A9 [M], C9 [R]/[M]).

**Single next step.** Check Shimura 1973 Thm 1 (p.526) and Li 1975 p.296 against copies of the
papers. That turns the two AUDIT-READ locators into VERIFIED ones, and adds the `K_f`-linear
Eichler–Shimura citation to h-trust C9.

Report: `docs/research/rv-h-a9c9.md`. Log and scripts: `scratch/rv-h-a9c9/`.

# cr3-trust report: a trust statement for CR₃

Note: docs/research/cr3-trust.md (h-trust format). Log and scripts: scratch/cr3-trust/. No Lean,
blueprint or other note was edited.

1. **Forms (§0).** There are 13 Lean forms in main-theorem variants. Each has a one-line meaning,
   its file:line and the Lean theorem that connects it to the others. `CertifiedRankTYZClRk`
   implies every form except TYZ, TYZCl and 5b, which have the extra premise `#Sel₂ = 8`; each of
   those follows from its own Rk form. Finding: the CR₃^5b variant (`RouteK/Rank5b.lean:37`) still
   takes 22P, and `CertifiedRankDLAdmRk` has no main-theorem variant (it gives PC only).
2. **Outline (§1)** for `CertifiedRankTYZClRk`: 26 steps, each with a supplier and a status.
   - A: the match of the Lean statement. `gCl`, `T5bCl`, the premises, the curve `E_n ≅ C_n` and the
     conclusion, covered by rv-redei, rv-cr5b-sec3, rv-cr3-rank (branch) and reading here.
   - B: TYZ I1-I7. Theorems 2.1, 3.3 and 3.5 (first assertion), Lemma 2.8, Propositions 2.3 and
     3.2, Lemmas 3.16, 3.18 and 3.21, the recursion, 𝓛(n) and the root number, Waldspurger and
     Yuan–Zhang–Zhang. Status [R], with locators read only in arXiv v1.
   - C: Lemmas N1, N2 and Proposition N [M1].
   - D: Gross–Zagier with an auxiliary field (Bump–Friedberg–Hoffstein, Murty–Murty) and CM
     modularity [R]. No Kolyvagin preprint, BCDT or Kriz.
   - E: Lean steps [L].
3. **Check run here (A6).** 30 values of `d` with `T5b = 1`, 3 to 5 primes, `d < 30000`.
   - `T5bCl` from bnfcertify-certified class groups is 1 on all 30.
   - Root number −1 and analytic rank 1 (numerical) on all 30.
   - An explicit non-torsion point on 24 curves. The other 6 have generators too large for ellrank
     or a 2-cover search; ellheegner was too slow.
   - A scan of all 386 such `d`: `#Sel₂ = 8` in every case, so the Selmer premise removed nothing
     (an open point of rv-cr5b-sec3 §1.6).
4. **Outside refereed sources and Lean (§2).**
   - (i) Proposition N: one model review (rv-nt-tyz). rv-prop-n ran in parallel and is not used.
   - (ii) The definition match: `gCl` and the Rk conclusion have one review each; `T5bCl` and the
     premises have two; the Inf reading has none besides this task.
   - (iii) The TYZ journal text was never read. arXiv v1 Theorem 1.2 is false as printed; the
     journal numbering may differ (Zhang's "Cor. 1.3").
   - (iv) About 9 groups of UNVERIFIED locators (GZ hypotheses, the theorem numbers of BFH and
     Murty–Murty, Birch–Stephens, Waldspurger, YZZ, Cox 9.3, ...).
   - (v) The scripts.
5. **Drafts (§3).** A replacement docstring for `ZInQ.CertifiedRank` (TYZ route first; GZ with its
   auxiliary input; Kriz is an alternative that is not needed), and trust paragraphs for
   `CertifiedRankTYZClRk` and `CertifiedRankRk`. Lines are at most 100 characters; not applied.

Next: fold in rv-prop-n; the network checks of §2.4 items 1-4; apply §3 and align the
Sel/5b/TYZ docstrings.

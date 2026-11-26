---
article_id: af_646c91cf37e91550d742a3f3
---

# Appendix F: the odd theta forms and their operators

Appendix F builds the odd coefficient source used in the proof of
[Theorem 5.3](../restricted-converse.md) and proves the arithmetic facts that Section 7 needs about it,
for the genus partner $h_*$, the fixed witness $D_w$ and the multiplier $L$ of Section 7:

1. **The witness and the stages.** Proposition F.1 chooses $h_*$, $D_w$ and $L$ and one sequence of
   detecting stages at which the stage map of $Q=LP_{D_w}$ has a fixed valuation $c_w$ (O.2). The
   points compared are the conductor-one points $P_D$ (O.1).
2. **The odd forms.** At each stage a weighted quaternionic theta sum (O.4) gives a form of weight $3/2$
   whose coefficients satisfy a Hecke recurrence (O.6) (Proposition F.2).
3. **Comparison and visibility.** The coefficients are congruent to $c_0\,2^{\omega(N)}$ times the stage
   map of $LP_D$ (O.7, Proposition F.3), so a coefficient of valuation below the precision forces a
   simple zero and bounds the genus index (O.8, Proposition F.4). After phase removal (O.7) is
   [(3.8)](../section-7/equation-3-8-theta-coefficients.md).
4. **The coefficient rules.** Integer divisions of operator coefficients (O.9)–(O.11) and an inertia
   identity (O.12) give the coefficient rules of [Lemma 7.6](../section-7/lemma-7-6-coefficient-rules.md)
   for the actual even and odd symbols (Proposition F.5). In the reduction of Theorem 5.3,
   Proposition F.2, the theorems of Proposition F.5 and (O.9)–(O.12) are proved but unused: the
   division and trace content enters only as ELLIOT and GLUE fields of `PostLeaves.address`, and the
   theta side with the comparison argument in `PreLeaves.odd_staged` amounts to (O.7).

## Definitions

**Admissible parameters.** An admissible $D$ is positive, squarefree, prime to the fixed support and in
the prescribed unit classes; then $K_D=\mathbb Q(\sqrt{Dh_*})$ is imaginary, split at $2N$, has no extra
units, and $Dh_*$ is an odd fundamental discriminant. In Lean the admissible parameters at a stage are
interface data, the prepared filter cut by $(D/\ell_0)=1$ for the stage's prime (`StagesFrom`), and
`AdmissiblePrepared` places them in the prepared filter.

**The stage maps.** At a stage of precision $M$ with detecting prime $\ell_0$, put $n=2^M$ and let $F$
be Frobenius on the reduction of $E$. For $P\in E(\mathbb F_{\ell_0^2})$ choose $R$ with $nR=P$ and set
$\kappa_M(P)=F^2R-R\in E[n]$; this is additive and onto, with kernel $nE(\mathbb F_{\ell_0^2})$, and
$\lambda_M=b\circ\kappa_M$ for the fixed row $b$. In Lean the stage maps on the points over the Hilbert
class field, reduction at the chosen place followed by $\lambda_M$, are interface data (`StageKummer`),
equal to the actual map only at the selected datum of $D_w$ (`actualStageMapOn`); the integer
$\lambda_\theta(D)$ is the lift `lamOf` of $\lambda_{M_\theta}(\overline{LP_D})$.

**The operators.** For a finite set $U$ of good primes, $n_U=\lceil\delta+w(U)\rceil$ and
$B_U=2^{-n_U}\prod_{p\in U}(U_p-\eta(p)V_p)\,g$, where $U_p(\sum a(n)q^n)=\sum a(pn)q^n$ and
$V_pg(\tau)=g(p\tau)$. In the full two-torsion family $n_U=\delta+|U|$. In Lean the undivided product
acts on coefficient functions (`Odd.TL`).

## The items

- [(O.1): the conductor-one point $P_D$](equation-o-1-genus-point.md)
- Proposition F.1, one witness and a compatible detecting sequence: no single declaration states it
  (see below); its display has its own page,
  [(O.2): the stage valuation at the fixed witness](equation-o-2-witness-valuation.md)
- [Proposition F.2: the odd theta form and its recurrence](proposition-f-2-odd-theta-form.md), with
  (O.3)–(O.6)
- [Proposition F.3: the unaveraged theta comparison (O.7)](proposition-f-3-theta-comparison.md)
- [Proposition F.4: visibility and the genus index (O.8)](proposition-f-4-visibility.md)
- [Proposition F.5: the arithmetic realization of the coefficient
  rules](proposition-f-5-coefficient-rules.md)
- [(O.9): the valuation of the operator coefficients](equation-o-9-divided-operators.md)
- [(O.10): the parity of the divided shells](equation-o-10-shell-parity.md)
- [(O.11): the halved operator $H_U$](equation-o-11-halved-operator.md)
- [(O.12): the inertia identity at a ramified prime](equation-o-12-inertia-identity.md)

The displays (O.7) and (O.8) are the conclusions of Propositions F.3 and F.4 and share their pages;
(O.3), (O.4), (O.5a)–(O.5c), (O.5) and (O.6) are on the page of Proposition F.2. The admissible
parameters, the stage maps and the operators $B_U$ are on this page. The displays (F.1)–(F.8) belong to
Appendix G.

## Items with no Lean statement

- **Proposition F.1.** No single declaration states it. Its parts are: the genus partner $h_*$, which
  the Lean proof obtains from Hoffstein–Luo, the twist sign and modularity (`exists_genusPartner`)
  rather than from clause (ii) of Bump–Friedberg–Hoffstein; the witness $D_w$ with an exact witness
  and the detector outputs, fields of `PreLeaves.odd_staged`; the stage construction, which is
  [(3.7)](../section-7/equation-3-7-advanced-stages.md) given Serre's open image theorem; and (O.2).
- **(O.3) and (O.5b).** The condition on the local weight characters and the eigenvalue of the theta
  multiplier have no Lean statement; see the page of Proposition F.2.

## Remaining hypotheses that cover Appendix F

These fields of [the remaining hypotheses](../remaining-hypotheses.md) cite lines of Appendix F in their
docstrings, with the kind each docstring gives:

- `PreLeaves.stage_support` (definitions): the fixed support, containing the primes of $h_*$, and the
  prepared filter, with unit tests only at the intrinsic support.
- `PreLeaves.odd_staged` (ELLIOT, GLUE, PRINT and definitions): the witness $D_w$ with its exact
  witness, the detector outputs and the stages of Proposition F.1, the stage maps at the selected datum,
  the multiplier $L$ killing native torsion (ELLIOT with a print of Silverman in the leaf's docstring,
  GLUE in that of `MultiplierKillsNativeTorsion`), the odd sign of admissible parameters, and the theta side
  and comparison argument of (O.7), which together amount to (O.7) itself.
- `PostLeaves.address` (ELLIOT and GLUE): the intrinsic odd filter and the density models of the odd
  stage source and of the transported even source behind Proposition F.5, with the readings, (O.12) at
  coefficient one, Kummer theory, and the openness and unramifiedness of $N_U$.

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)

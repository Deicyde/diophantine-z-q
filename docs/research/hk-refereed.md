# Kolyvagin's pole-completeness input: stage 1

**Verdict.** The headline needs only an infinite-order rational point on each of its
analytic-rank-one pole curves, at calls where the explicit 2-Selmer group has eight
classes. It does not read the rank upper bound, the rank-zero case, or finiteness of
Sha. Both candidate readings below have a different premise: a non-torsion Heegner
trace over an imaginary quadratic field. Neither draft closes the headline input.
Both locators are **UNVERIFIED**; the two application gaps are named in Lean.

## The consumed statement

**VERIFIED (source trace).** `ZInQ.OneProof.frozenTarget` passes `hK` and BCDT modularity
through `poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing` to
`poleCompleteness_of_restrictedConverseGenuine_casselsTate`. The latter calls
`PoleS12.kolyvaginRankOne_of_printed`, which uses projection `.1` of
`hK E hE hM hA`. In `PoleRC.crm_of_restrictedConverse_M`, the rank equality is used
only by `exists_not_isOfFinAddOrder_of_rank`. The point it supplies lets
`PoleRC.descentGlueM` count at least eight elements in the rational Kummer image;
the ambient Selmer group has exactly eight. The scratch log records other callers
found in the import closure.

`ZInQ.Manuscript.HKRefereed.HKConsumed` says: for positive squarefree
`ℓ ≡ 11 (mod 12)` with `(PoleRC.SelM ℓ).ncard = 8`, if `E_ℓ` is modular in the
sense of `PoleS12.IsModular` and `AnalyticRankOne E_ℓ`, then there exists
`P : E_ℓ(ℚ)` with `¬ IsOfFinAddOrder P`. The modularity premise permits the
standalone implication `hkConsumed_of_hK`; the headline already supplies it from
BCDT. The family conditions and count are already in scope in the pole proof.
`poleCompleteness_of_hkConsumed` uses that witness directly. The scratch substitution
checks the final assembly and the printed BCDT adapter with their actual types.
It abstracts over the unchanged height supplier: instantiate `height` with
`HDec.HSyn.sixContactMin_of_open91` from
`ZInQKernel/OneProof/H/TailZ98.lean`, of type
`OpenResearchLeaves72 → OpenTextbookLeaves18 → OpenAddedLeaves28 → ZInQ.SixContactMin`.

**VERIFIED (Lean).** The three new modules and
`scratch/hk-refereed/Substitution.lean` pass `lake env lean` after building their
imports. All four new theorems report only `propext`, `Classical.choice` and
`Quot.sound`. The full height chain is outside this factored dry run.

## Candidate printed forms, pending a reading

The two drafts have the same proposed **rank projection**. For a modular elliptic
curve over ℚ, take an imaginary quadratic field `K` in which every prime of the
conductor splits, write `H` for its Hilbert class field, and let
`P = Tr_{H/K}(φ(x)) ∈ E(K)` for a conductor-one Heegner point `x` on `X₀(N)`.
If `P` has infinite order, `rank E(K) = 1`. The drafts restrict to non-CM curves
and `disc K ≠ −3, −4`. They omit any separate Sha conclusion or index formula. The
trace is an actual Galois sum over the class field in Lean, and its summand is pinned
to the image of a primitive Heegner form by the existing analytic parametrization.
This uses the existing analytic dictionary for `X₀(N)`, `φ`, the conductor, and
the CM point; the comparison with the algebraic print is still GLUE. In particular,
a page that assumes an optimal quotient needs an explicit comparison from the
tree's weak Weil parametrization, including the effect on the trace.

1. **`KolyvaginEulerSystemsRankDraft` — SPECULATIVE; locator UNVERIFIED.**
   V. A. Kolyvagin, *Euler systems*, in *The Grothendieck Festschrift*, Vol. II,
   Progr. Math. 87, Birkhäuser (1990). Look for the arithmetic rank-one statement
   for Heegner points; exact theorem number and page unknown. Check that the
   chapter states the conductor-one trace result over `K` itself, and verify the
   hypotheses on the parametrization, level, discriminant and splitting. If the
   page supplies prime-dependent descent or an index bound, identify the
   hypotheses and the argument giving the characteristic-zero rank consequence
   before using this draft.
2. **`GrossHeegnerRankDraft` — SPECULATIVE; locator UNVERIFIED.**
   B. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and
   Arithmetic* (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge
   Univ. Press (1991). The opening arithmetic theorem, possibly Theorem 1.1
   (**UNVERIFIED**), is the intended locator. Check whether it says rank one
   or that `E(K)/ℤP` is finite, and look separately at the proof's
   prime-specific hypotheses, which may restrict the result actually proved
   there. Check the standing modularity, parametrization and splitting assumptions
   and whether the cited passage proves the result or attributes it to another
   source. The candidate is the arithmetic theorem from a non-torsion trace.
   An analytic-rank corollary obtained via Gross–Zagier is outside this route.

## Application gaps

- **`PoleNonTorsionHeegnerTrace` (GLUE).** At a call to `HKConsumed`, produce a split
  imaginary quadratic field, parametrization, CM point and their actual
  non-torsion trace. Analytic rank one on its own is the headline input, not a
  witness satisfying the candidate theorem. In particular, simply choosing a
  field satisfying the splitting condition does not prove non-torsion.
- **`PoleHeegnerRankDescent` (GLUE).** For a trace supplied at such a call, transport
  rank one over `K` to rank one on the untwisted curve over ℚ. Arithmetic rank
  one over a quadratic field does not distinguish the two conjugation eigenspaces.
  A sufficient orientation is that the non-torsion trace is fixed modulo torsion
  by complex conjugation. A positive integer multiple descending to `E(ℚ)` would already give the
  headline's witness, even without the rank bound. This is why finding an
  arithmetic Euler-system theorem alone may not reduce the consumed conclusion.

The shared conditional Lean wiring is `hkConsumed_of_heegnerRank`. Each draft is
definitionally the `HeegnerRankStatement` input of that theorem; the two gap Props
remain premises. No stage-2 argument from the candidates to the original `hK`
is attempted.

## Known issues

- **VERIFIED (repository audit and sources).** MPI/90-69 is an unrefereed preprint,
  distinct from the Festschrift chapter. `audit-pole-hypotheses.md` records its
  weak Weil parametrization premise on p. 3 and Theorem 1 on p. 4. The manuscript
  cites the preprint; the candidate prints were not read. An existing module name
  or docstring calling the preprint form “printed” does not make it a refereed LEAF.
- **VERIFIED (Lean source).** `PoleS12.IsModular` is a coefficient identity at
  some positive level. `bcdtThmA_of_printed` gives that predicate; it does not
  give an algebraic `X₀(N) → E` or a CM trace. The existing route to the analytic
  `ModularToWeakWeil` is conditional (see
  `ZInQKernel/Contrib/RC53Assist/NewformGlues/AllPrints.lean`); converting the
  algebraic and analytic parametrizations is another dictionary issue. This is
  the implicit premise in the manuscript's short appeal at L1092–1093.
- **VERIFIED (TeX and Lean source).** At L1111–1113 the manuscript has both rank one
  and 2-Selmer dimension three, so the Kummer sequence and full rational
  2-torsion give `Sha[2] = 0`. Finiteness of all of Sha is surplus there.
  This is a difference in proof route, not an error in the manuscript conclusion.
  No mathematical error was found in the rank-one steps checked.

## Manuscript check

All locations refer to `diophantine_zq.tex`. Each verdict concerns the indicated
step only.

| TeX lines | Step | Verdict |
| --- | --- | --- |
| L1001–1011 | Statement of pole completeness and the restricted converse supplying analytic rank one. | **OK** — the restricted converse stays a headline input. |
| L1033–1069 | Both parameters lie in the restricted family and have 2-Selmer dimension three. | **OK** — the existing simultaneous construction and Kummer identification give the eight-class call. |
| L1072–1084 | Pass from 2-Selmer dimension three to corank one. | **OK** — existing `lemma54At_of_casselsTatePairing` uses the retained pairing input. |
| L1086–1089 | Forward-rank lemma includes rank zero, rank one and finiteness of Sha. | **OK** — only the rank-one clause is needed for this task. |
| L1092–1093; L1779–1788 | Pass from modularity to the parametrization premise. | **unverified** — the latter lines give the mathematical construction for `E_ℓ`; the comparison from the Lean predicate to the algebraic parametrization is not closed by the headline BCDT adapter. |
| L1093–1097; L11163–11167 | Cite the auxiliary-field route and Theorem 1 of MPI/90-69. | **unverified** — prior audit identifies the preprint; no candidate print was checked in this stage. |
| L1111–1115 | Apply the restricted converse twice and get actual Kummer representatives. | **gap filled** — the Lean proof counts the Kummer image using the consumed infinite-order point, so the replacement needs no Sha finiteness. |
| L1116–1121 | Rescale the points and finish pole completeness. | **OK** — the existing `poleCompleteness_of_crm` carries out this reduction. |

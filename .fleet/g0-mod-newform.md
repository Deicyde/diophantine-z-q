# g0-mod-newform (fleet note)

**Result.** Glue steps G13-G16 of `ModularConstituent` are proved in Lean:
`scratch/g0-mod-newform/NewForm.lean`, with new code in `part_new.lean`, namespace `G0ModNewform`.
The file compiles with exit 0, no `sorry`, and standard axioms for all 19 printed declarations
(VERIFIED).

The headline is `modularConstituent_tail_G`. Its input is G8-G12's data `D` (model `A/L'`,
`r₅`, `r₃`, embeddings) satisfying `G12Spec D`, plus two open Props on the same `D`. Its output
is the last conjuncts of `ModularConstituent`: a level `0 < N ≤ Q_D M²`, a `J₁(N)` `J`, and
`CommonConstituent A (J_{L'})`.
- G13 `g13`: the newform `f` (T24, T25), and `r₅|G_{L'} ≅ ρ_{f,5}|G_{L'} ⊆ V₅(J_{L'})` (R16,
  Faltings, T18, T19; one `A_f` shared by C9 and E1).
- G14 `g14`: `r₃`, `r₅` isomorphic to R14's representations of `f`.
- G15 `g15`: Carayol (`CarayolR17'`), with conductors invariant under isomorphism (proved).
  Glazer's arithmetic `a ≤ 2(1+U₀) ≤ E₀` is proved from L8.
- G16 `g16`: `GlueConductor.level_le`.

**Bridges.**
- From g0-mod-galois's draft interface, proved: `g12Spec_of_galois`. Its `GalG8Out` gives the
  constituent. Its `GalG12Out` gives `PanOutput` through the named Prop `DirichletOfFinite`
  (Kronecker–Weber at Frobenius).
- Global to local inertia, proved: `localUnram_of_unramifiedAt`. With it, clause (iii) of G15 is
  exactly G11's output.

**What remains** (all named Props, no new leaf):
- `G14TraceCompat D`: trace compatibility of `r₃`, `r₅` (T7 on the reduction).
- `G15RamG D u` clauses (i)-(ii): upper groups above `U₀` act trivially for `p ≤ D`, and wild
  inertia acts trivially for `p > D`.

  Both are statements about G8's construction of `r_ℓ`. Stated over arbitrary constituents they
  would be false: a twist by a character of `Gal(L'/ℚ)` gives another constituent.
- `DirichletOfFinite` (from T17).
- The kernel glue Props `SwanIndependent`, `SwanIntegral`, `AdaptedExists`, `X1ModelExists`.
- Integration across object layers: my file uses the kernel's objects; `Split.lean` uses
  `Leaves.lean`'s copies. The remaining check is that `LeafAdopt.abVarEquiv` commutes with
  `baseChange`.

Report: `docs/research/g0-mod-newform.md` (§3 gives the feed into `ModularConstituent`). Log:
`scratch/g0-mod-newform/log.md`.

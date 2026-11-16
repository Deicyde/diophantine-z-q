# dict-galois (fleet summary)

**Result:** all four rows the 11-16 dictionary pass rated *consequence* are now restated as printed leaves. Each
old field is proved in Lean from the new leaves. No `sorry`; only the standard axioms. `#discharges` reports all
four fields discharged.

- `tateTwistInvariants` ← `TateTwistInvariantsPrinted`, the disjunction of Tate 1967 §3.3 Thm 2's cyclotomic and
  general-character wordings. Proved in Lean: `χ^i(G_K ∩ I_{ℚ_p})` is infinite for `i ≠ 0`, via Tau Ceti local
  CFT.
- `hodgeTateDecompAbVar` ← `HodgeTateDecompAbVarPrinted`: `ℂ_p(1)^g ⊕ ℂ_p^b` with `b` unnamed. `b = g` comes from
  T26, which follows from the textbook field `mumfordTorsionAlgClosed`, so the dual abelian variety is not needed.
- `deRhamH1AbVarT` ← `DeRhamVpAbVarT` (`V_p A` de Rham, Berger I.3) and `BdRInvariantsOver` (`B_dR^{G_F} = F`,
  dimension form). The dual of a de Rham representation being de Rham is proved in Lean, from `B_dR` being a field.
- `r7a` ← `NeronOggShafarevichSep`: Serre–Tate Thm 1 over any `IsSepClosure`. The `K̄` form is proved from
  MulEtale and an inertia transfer between `K^s` and `K̄`.

**What compiles:** four contribution files under `ZInQKernel/Contrib/OneProof/` (`TateTwistInvariants`,
`HodgeTateDecompAbVar`, `DeRhamH1AbVarT`, `NeronOggShafarevichSep`). The autofold spec is
`scratch/dict-galois/autofold.json`. Its dry-run module compiles and gives `sixContactMin_of_open35` with standard
axioms. GLUE stays at 8 (strict) and 9 (strictest); the count goes from 48 to 49 fields (`deRhamH1AbVarT` becomes two
leaves).

**What remains:** all locators are UNVERIFIED (no sources on this host): Tate 1967, Fontaine 1982, Berger 2004 I.3,
Fontaine Astérisque 223, Serre–Tate 1968. The new leaves need statement checks against the prints. Rows for
`docs/research/locators.md` are proposed in `docs/research/dict-galois.md` but not added. The fold itself
(`autofold.py` without `--dry-run`) is left to the integrator.

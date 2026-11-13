# c9-rhof (2026-11-12)

**Result: glue C9 is proved in Lean from leaves** (`scratch/c9-rhof/C9.lean`, report
`docs/research/c9-rhof.md`). `lake env lean scratch/c9-rhof/C9.lean` exits 0 with no warnings and
no `sorry`. Every headline theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

What compiles (namespace `C9Rhof`):
- `rhoF_semisimple`: R16's `ρ_{f,ι}` is semisimple. Inputs: Faltings Satz 3, I3.M0, and the
  kernel's proved base change of semisimplicity. `ρ_{f,ι}` is an equivariant quotient of
  `V_ℓ(A) ⊗ ℚ̄_ℓ` (`quotMap`).
- `rhoF_continuous`: the matrix coefficients are continuous in any basis (I3.M0 plus the kernel's
  glue-rho-cont).
- `c9`: from R16′, Faltings, I3.M0, T18 (Frobenius density) and T19 (Brauer–Nesbitt). Every
  continuous semisimple `r` with `f`'s arithmetic-Frobenius traces satisfies:
  - `r ≅ ρ_{f,ι}`;
  - `tr r = tr ρ_{f,ι}` on all of `G_ℚ`, which is `c10`'s `h₅`;
  - `tr ρ_{f,ι}(g) = ι(a_p)` at every `IsFrobAt g p`, which is `hρ₅`.
- `c9_R14`: R14's representation ≅ `ρ_{f,ι}`.
- `c9_r5`: C8's `r₅` (Pan's trace form `AttachedUpToTwist`, with the twisting character a
  Dirichlet character), combined with T24 (twisting) and T25 (newforms), gives a newform `f` of
  level `N ∣ Mm²` with `r₅ ≅ ρ_{f,ι}`, `h₅` and `hρ₅`.
- `c10_via_c9`: C9's outputs plug directly into `GlueC10.c10`.
- Also: the `GaloisRep` → `Representation` bridge (`toRep`), and
  `isSemisimple_of_isIrreducible`, which discharges `r₅`'s semisimplicity using Pan's own
  irreducibility hypothesis.

Findings:
- `c10` consumes only `h₅`, never the isomorphism itself. `h₅` needs only T18 and continuity;
  T19 and semisimplicity are needed only for `r₅ ≅ ρ_{f,5}`.
- T18 is used in its `IsArithFrob` form, because the kernel lacks `IsFrobAt ⇒ IsArithFrob`.
- One model review found no defects; its single fix (a weaker `hatt`) is applied.

What remains, not done here:
- C8 must supply three things:
  - `r₅` as an irreducible `GaloisRep 5 2` (passing from C2's subrepresentation to a matrix
    representation);
  - `hψ`: the twisting character is a Dirichlet character at Frobenius, from T17 and
    `twist_finite` (medium);
  - weight `k = 2`.
- The abelian-variety traces `hr₅` and `hr₃` of C10 (G14).
- `X1ModelExists`, which the `∀ J` quantifier needs in order to be non-vacuous.

# glue-assembly (fleet report)

**Main result (VERIFIED: compiled, standard axioms only).**
`GlueAssembly.sixContactMinAt_of_glueOutputs : GlueOutputs S → SixContactMinAt S`
(`scratch/glue-assembly/GlueAssembly.lean`, built by `build.sh`). `SixContactMinAt Mult.S_mul` is
`ZInQ.SixContactMin` word for word. The theorem machine-checks the whole Arakelov half and the
final constant:
- F2 on Mathlib's genuine Weil height: `h(Φ(z)) ≤ 40h(z) + log 3779136`, and N5's `+22` follows.
- New: the height of a rational number is unchanged in any number field (missing from Mathlib).
- The E2-E4 arithmetic from `N ≤ QM²`, and the CM-branch arithmetic (`h_F(A) ≤ C_cm`).
- The F3 arithmetic, F4, and the assembly into `H₆(D)·M²⁴`.

`GlueOutputs` takes the outputs of Javanpeykar, GR14, Faltings Lemma 5, Bost and Pazuki as real
inequalities, since Faltings heights do not exist in Mathlib. It is a numerical shadow (a height
bound in disguise), not a faithful leaf. It fixes the contract each leaf must meet
(`docs/research/glue-assembly.md` §1.2).

**Also proved (compiled, no `sorry`):**
- C8 glue: the Hodge–Tate weight comparison in both normalizations, and the determinant
  argument (finiteness of the twist) as group theory.
- E1 glue: invariants commute with extension of scalars.
- E2 glue: `[SL₂(ℤ):Γ₁(N)] ≤ N²` over Mathlib's `Gamma1`.
- F3 normalizations: the L² height dominates the sup height; zero coordinates and roots of unity
  do not change the height.

**Leaves of the cluster.** 18 published inputs (§3 of the report):
- Faltings 1983 (Hom theorem, semisimplicity, Lemma 5);
- additivity, Poincaré reducibility, GR14 Thm 1.4, Bost, Javanpeykar, Pazuki;
- eigenform Hodge–Tate weights, Deligne–Serre, the Weil pairing;
- the Néron mapping property, Serre–Tate, Mumford §19 Thm 4, Eichler–Shimura;
- Chebotarev, Brauer–Nesbitt, Kronecker–Weber.

Only two can be stated over Mathlib's objects today: `KroneckerWeber` (proved in Tau Ceti) and
`BrauerNesbittCharZero` (`Leaves.lean`).

**Biggest obstacle.** The object layer: abelian varieties over number fields with isogeny
degrees, the stable Faltings height and Tate modules (E1-E4), and ℓ-adic representations of
`G_ℚ` with Frobenius and Hodge–Tate conditions (C8, C10). Inside the cluster, every step that
Mathlib can state is proved. Scratch files cannot import `JHeight`/`HeightMin` (the upstream
`lean/` is unbuilt), so F4 is copied; adopting the file under `ZInQKernel/` removes the copy.

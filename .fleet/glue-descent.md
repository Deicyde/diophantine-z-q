# glue-descent (2026-11-11): fleet report

Full note: `docs/research/glue-descent.md`. Lean: `scratch/glue-descent/` (8 files, 1713 lines,
build with `build.sh`, ~45 s). Log: `scratch/glue-descent/log.md`.

**Main result.** B2 and B3 of h-trust (N5 L665-716) are now **Lean theorems over genuine
Mathlib objects**, proved from four stated leaves. Everything compiles with no `sorry`, and the
axioms are `propext`, `Classical.choice`, `Quot.sound`. The objects:
- `G_ℚ = Field.absoluteGaloisGroup ℚ`;
- `absoluteGaloisGroup.map : G_{ℚ_p} → G_ℚ`;
- `modularCyclotomicCharacter`, `DirichletCharacter`, `IntermediateField`, `𝓞 L`.

The theorems:
- `b2_of_leaves`. Input: a sign cocycle `ε` inflated from a finite Galois `L` unramified
  outside `T`. Output: `χ` with `ord χ ≤ 2∏_{p∈T,p≠2}(p−1)`, and a continuous `β` with
  `β² = χ` and `dβ = ε`.
- `b3_of_leaves`. With any quadratic twist, the kernel field `L' ⊇ L` is Galois,
  `G_{L'} = ker β|_{G_L}`, and `[L':ℚ] ≤ 2·ord χ·[L:ℚ]`.
- `b3_degree_le_QM`: `[L':ℚ] ≤ heightQ R · contactSupport S u`, against the repository's own
  constants, with `D` never evaluated.

**B1 and C1.** All the algebra is proved over arbitrary groups, fields and vector spaces:
- the cocycle identity of `c`;
- `a_σ a_τ c = sign(c) a_στ` for `a = deg^{−1/4}`;
- `ρ = β^{−1} a T` is a representation;
- `ρ` commutes with `B ⊗ E` and equals the Tate action on `G_{L'}`;
- matrix units give `ρ ≅ r ⊕ r` with `dim r = 2`.

N5's `B = (2,−3)` is proved central and simple (anisotropic norm form), with centralizer `ℚ`, so
Skolem–Noether applies to it.

**Leaves (7)**, stated as `def … : Prop` where marked; the first five elaborate in Lean:
- L-B1 Skolem–Noether (stated);
- L-B2a Hasse for `H²(G_ℚ,±1)` at the finite places (stated);
- L-B2b `|H²(G_{ℚ_p},±1)| ≤ 2` (stated);
- L-B2c explicit local square-root criterion for Dirichlet characters (stated);
- L-B2d unramified classes vanish locally (stated);
- L-B3a unique quadratic character of tame inertia (not stated);
- L-B3b ramification of quadratic Dirichlet characters (not stated).

L-B2c and L-B2d package some glue: local CFT plus the structure of `ℚ_p^×`, and inflation. They
can be split into pkg-I6's `LocalKroneckerWeber` and glue.

**Not formalized.**
- B3's "`L'` unramified outside `T`". Its group core is proved (`twist_kills_inertia`); the
  rest needs inertia subgroups of `G_ℚ` and L-B3a/b.
- The abelian-variety instantiation of B1 and C1: conjugates `^σA`, the transport
  `V_ℓ(A) → V_ℓ(^σA)`, and isogeny degrees, on top of pkg-I3's `AbVar`.

**Biggest obstacle.** The objects B1 and C1 act on: the QM surface `A`, its conjugates and
`End⁰(A_ℚ̄) = B`. Mathlib cannot build a nonzero abelian variety, so B1 and C1 wait on I1/I3,
whereas B2 and B3 are done modulo their leaves.

# pkg-I3 (2026-11-11): fleet report

Full note: `docs/research/pkg-I3.md`. Lean: `scratch/pkg-I3/I3.lean` (694 lines, Mathlib only,
compiles, **no `sorry`**; axioms `propext`, `Classical.choice`, `Quot.sound`). Log:
`scratch/pkg-I3/log.md`.

**Main result.** Package I3 (Faltings 1983; Mumford's structure theorems; steps A9, C2, C10, E1)
can be stated faithfully in Lean today. This corrects wk-h §3, which said Tate modules were
missing. The missing objects are small and are *defined* on Mathlib's genuine group schemes,
with every law proved:
- `AbVar K`: a proper, smooth, geometrically integral `GrpObj` over `Spec K`. Commutativity
  comes from Mathlib's Stacks 0BFD theorem.
- `Hom A B` and the ring `End A`, and `End⁰ = ℚ ⊗ End`.
- `A(K̄)` with its `G_K`-action (left action proved).
- `T_ℓ(A) = lim A[ℓⁿ]` as a `ℤ_ℓ`-module, and `V_ℓ = ℚ_ℓ ⊗ T_ℓ`.
- `ρ_ℓ` as a Mathlib `Representation`, and `ℤ_ℓ ⊗ Hom → Hom(T_ℓ, T_ℓ)`.
- base change, and `AbVar.zero`.

**Leaves (7)**, as `def … : Prop` and bundled in `I3Leaves`. Locators: Faltings AUDIT-READ
(p. 360) and ASTRA-READ (pp. 360-361); Mumford and Milne UNVERIFIED.
- `FaltingsSemisimple`: Satz 3.
- `FaltingsTate`: Satz 4 and Korollar 1, integral form.
- `TateModuleFree`: `T_ℓ` free of rank `2g`, Mumford §6.
- `HomFreeFinite`: Mumford §19 Thm 3.
- `CharPolyIndepOfEll`: Mumford §19 Thm 4, used for C10 over `𝔽_q`.
- `PoincareReducibility`: §19 Thm 1, in the form E1 uses, characteristic 0.
- `QMDichotomy`: A9, `End⁰(A_ℚ̄) ∈ {B, M₂(k)}`. It replaces N5's complex-analytic argument
  (GAGA), which cannot be stated. It follows from Mumford §19, §21 and AEC III.9.4, but still
  needs **one refereed locator**, or else it must be split.

**Glue proved in Lean.**
- `range_tateHomZl_subset`: the easy inclusion holds outright, so `FaltingsTate` asserts
  exactly Faltings' content.
- `exists_hom_ne_zero_of_equivariant`, E1's Faltings step: a nonzero equivariant map
  `V_ℓA → V_ℓB` gives a nonzero `A → B`.
- `finrank_equivEnd`, C2's Faltings step: `dim End_{G_K}(V_ℓ A) = rank End_K(A)`.

Still to be written, all linear algebra or base change, none of it a literature leaf:
- C2's commutant argument;
- semisimplicity and invariants under coefficient extension;
- `T_ℓ` under base change of the field;
- the application of `PoincareReducibility`.

**Biggest obstacle.** Mathlib v4.35 cannot construct any *nonzero* abelian variety. There is no
projective group scheme, and no elliptic curve as a scheme (VERIFIED by grep). So applying the
leaves to Glazer's `A`, `J₁(N)` and `A_f` requires those to be supplied as `PkgI3.AbVar`
objects by the I1 leaves (moduli) and the I4 leaves (Shimura's `A_f ⊂ J₁(N)`). **The
synthesis should make `PkgI3.AbVar` (or Tau Ceti's `AbelianVariety`, with these `T_ℓ`/`ρ_ℓ`)
the shared type.** A "Jacobians of explicit curves" formulation does not help: `J₁(N)` and
`A_f` have no usable equations, and Jacobians would need more infrastructure, not less.

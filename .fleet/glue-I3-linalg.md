# glue-I3-linalg: fleet report

**Verdict.** The glue of package I3 for C2 and E1 is proved in Lean over pkg-I3's object layer. The one
exception is `SemisimpleBaseChange` (semisimplicity survives extension of scalars in characteristic 0),
standard algebra that is stated as a Prop and not proved. Nothing contains `sorry`, and every theorem uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`. Report: `docs/research/glue-I3-linalg.md`. Lean
files: `scratch/glue-I3-linalg/`.

**Compiles (VERIFIED, `lake env lean`, last runs 22:46-22:47 PST, 2026-11-11):**
- `Commutant.lean` (Mathlib only):
  - `isIrreducible_of_commutant_scalar`: semisimple with a scalar commutant ⇒ irreducible;
  - the block-map dimension count `dim End_G(r ⊕ r) ≤ 4` ⇒ `End_G r = k`;
  - invariants under extension of coefficients: `commOf_baseChange_le_range`, `finrank_commOf_baseChange_le`
    and `scalar_commOf_baseChange`;
  - `exists_equivariant_ne_zero_of_baseChange`: descent of a nonzero equivariant map;
  - `exists_equivariant_ne_zero_of_common`: E1's projection step;
  - `isSemisimple_of_surjective`;
  - `absolutelyIrreducible_of_finrank_commOf_prod_le_four`, which uses `SemisimpleBaseChange`.
- `TateBC.lean`: `Tate.map_bijective`. An injective group map with equal Tate ranks gives a bijection on
  `T_ℓ` (saturation plus rank–nullity over `ℤ_ℓ`). This is the algebraic core of `T_ℓ` under base change.
- `C2.lean` (pkg-I3's `I3.lean` verbatim plus the material above):
  - `PkgI3.C2_absolutelyIrreducible`: `r_ℓ` is absolutely irreducible. It uses the leaves
    `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree` and `HomFreeFinite`, the Prop
    `SemisimpleBaseChange`, A9's output `rank End A = 4`, and an equivariant `E ⊗ V_ℓ A ≅ r ⊕ r`;
  - `PkgI3.E1_exists_hom_ne_zero`: a common constituent of `V_ℓ A ⊗ E` and `V_ℓ J ⊗ E` gives a nonzero
    `Hom_K(A, J)`. It uses `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree` and `SemisimpleBaseChange`.

**Remains (with reason):**
1. A proof of `SemisimpleBaseChange`. Mathlib v4.35.0 has no "separable semisimple algebra stays semisimple
   after base change" (grep found none), so building it would be a real development, beyond this run (which
   started at 22:24).
2. `E ⊗ V_ℓ A ≅ r ⊕ r` from `B ⊗ E ≅ M₂(E)`. It is a hypothesis of the C2 theorem; routine, but there was no
   time.
3. Applying `PoincareReducibility` in E1. It needs `EndDivision A`, and A9's output (`End⁰ ≃ₐ B`) does not
   give "nonzero ⇒ isogeny" without an isogeny-category fact. Recommendation: have A9 or the QMDichotomy leaf
   output `EndDivision`.
4. The geometric half of `T_ℓ` under base change: `A(K̄) ↪ A(L̄) = A_L(L̄)`, Galois compatibility, and
   `dim A_L = dim A`.

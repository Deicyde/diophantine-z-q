# glue-I3-linalg: fleet report

**Verdict.** The linear-algebra glue of package I3 for C2 and E1 is proved in Lean over pkg-I3's object
layer, apart from two unproved textbook linear-algebra statements. Nothing contains `sorry`, and every
theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. Report:
`docs/research/glue-I3-linalg.md`. Lean files: `scratch/glue-I3-linalg/`.

**Compiles (VERIFIED, `lake env lean`, 2026-11-11, 22:29-22:43 PST):**
- `Commutant.lean` (Mathlib only):
  - `isIrreducible_of_commutant_scalar`: semisimple with a scalar commutant ⇒ irreducible;
  - `finrank_commOf_eq_one_of_prod_le_four` and `isIrreducible_of_finrank_commOf_prod_le_four`: the block-map
    dimension count, `dim End_G(r ⊕ r) ≤ 4` ⇒ `End_G r` is scalar;
  - `absolutelyIrreducible_of_finrank_commOf_prod_le_four`;
  - `exists_equivariant_ne_zero_of_common`: E1's projection step;
  - `isSemisimple_of_surjective`;
  - `exists_equivariant_ne_zero_of_baseChange`: descent of a nonzero equivariant map along a field extension.
- `TateBC.lean`: `Tate.map_bijective`. An injective group map with equal Tate ranks induces a bijection on
  `T_ℓ` (saturation plus rank–nullity over `ℤ_ℓ`). This is the algebraic core of `T_ℓ` under base change.
- `C2.lean` (`I3.lean` together with the material above):
  - `PkgI3.C2_absolutelyIrreducible`: `r_ℓ` is absolutely irreducible, from the I3 leaves, `rank End A = 4`
    and an equivariant `E ⊗ V_ℓ A ≅ r ⊕ r`;
  - `PkgI3.E1_exists_hom_ne_zero`: a common constituent over `E` gives a nonzero `Hom A J`;
  - `equivariantDescent`.

**Remains (with reason):**
1. `InvariantsBaseChange` (`dim End_G` is stable under extension of scalars) and `SemisimpleBaseChange`
   (semisimplicity survives extension of scalars in characteristic 0). Both are stated as Props and not proved.
   They are standard algebra, but needed more time than this run had (it started at 22:24).
   `InvariantsBaseChange` also hit a Lean 4.35 `Submodule` instance-path problem with `finrank`.
2. `E ⊗ V_ℓ A ≅ r ⊕ r` from `B ⊗ E ≅ M₂(E)`. It is a hypothesis of the C2 theorem.
3. Applying `PoincareReducibility` in E1. It needs `EndDivision A`, and A9's output (`End⁰ ≃ₐ B`) does not
   give "nonzero ⇒ isogeny" without an isogeny-category fact. Recommendation: have A9 or the QMDichotomy leaf
   output `EndDivision`.
4. The geometric half of `T_ℓ` under base change: `A(K̄) ↪ A(L̄) = A_L(L̄)`, Galois compatibility, and
   `dim A_L = dim A`.

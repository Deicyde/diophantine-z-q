# glue-rho-cont results log

- RhoCont.lean sections 1-2: copy of scratch/pkg-I3/I3.lean lines 15-335 (defs of Tate.T, AbVar, Pt, galAct, galT, galRep).
- 3a `continuous_act`: discrete action with open stabilizers (open subgroups) is jointly continuous. COMPILED.
- 3b `coord_eq_zero_iff`: x_n = 0 ↔ x ∈ ℓⁿ·T_ℓ(M) (kernel of n-th coordinate = ℓⁿT). COMPILED.
- 3b `continuous_of_linearMap_padicInt`: every ℤ_ℓ-linear T_ℓ(M) → ℤ_ℓ is continuous for the inverse-limit topology (M discrete). COMPILED.
- 3b `continuous_map_action`: continuous action on discrete M ⇒ continuous induced action on T_ℓ(M). COMPILED.
- 3c `exists_openSubgroup_galAct_eq`: every K̄-point of A (any K-scheme loc. of finite type) is fixed by Gal(K̄/E), E = K(finitely many algebraic elts), open. Proof via stalk map 𝒪_{A,x} → K̄, EssFiniteType of stalk maps (LocallyOfFiniteType.stalkMap), RingHom.EssFiniteType.ext, IntermediateField.fixingSubgroup_isOpen. COMPILED (Lean 4.35 / Mathlib v4.35, 2026-11-11 23:59).
- 3d `continuous_galT`: G_K × T_ℓ(A) → T_ℓ(A) continuous (Krull × inverse-limit topology). UNCONDITIONAL. COMPILED, axioms [propext, Classical.choice, Quot.sound].
- 3d `continuous_one_tmul`, `continuous_galRep`: with [Module.Free ℤ_ℓ T_ℓ(A)] [Module.Finite ℤ_ℓ T_ℓ(A)], G_K × V_ℓ(A) → V_ℓ(A) continuous, V_ℓ with Mathlib's moduleTopology ℚ_ℓ. COMPILED (00:0x).
- 3e `continuous_galRep_of_tateModuleFree` (from I3.M0 leaf, ℓ ≠ char K). Compiles; trace part temporarily sorry (whnf timeout in trace proof) — being fixed.

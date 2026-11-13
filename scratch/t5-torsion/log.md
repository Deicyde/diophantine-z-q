# t5-torsion results log

## Statement (VERIFIED, read in ZInQKernel/HDecomp/Objects.lean:993 and :1486)
- `PkgI2.TorsionStructure.{u}`: ∀ K field (any characteristic), A : Grp (Over (Spec K)) with
  `[IsAbelianVariety A]` (proper, smooth, geometrically integral), g n : ℕ,
  topologicalKrullDim A.X.left = g → 0 < n → (n : K) ≠ 0 →
  ∃ e : torsion A K̄ n ≃ (Fin (2g) → ZMod n), additive.
  `torsion A K̄ n = {x : specOver K K̄ ⟶ A.X | x ^ n = 1}` (K-morphisms Spec K̄ → A).
- `ObjBridge.TorsionStructure` is the same in Type 0 (`torsionStructure_iff : … ↔ PkgI2.TorsionStructure.{0}`, Iff.rfl).
- Demands: all characteristics (p ∤ n), all fields K (no cardinality bound). Consumers
  (Mobius/Glue.lean level3_finite, QM/Structures.lean, A6) apply it with [CharZero K].

## Build
- 12:10 lake build of TauCeti group modules, AbVarBC.Main, LeafPush2.T started.
- 12:04 build done (3 min).

## Compile outcomes
- GroupGlue.lean: `T5Torsion.nonempty_torsionBy_addEquiv_pi` (A abelian group, N ≠ 0, ∀ m ∣ N, #A[m] = m^r ⇒ A[N] ≃+ (Fin r → ZMod N)) and rank-r prime-power lemma. COMPILES, axioms propext/Classical.choice/Quot.sound. (VERIFIED)
- Torus.lean: `T5Torsion.natCard_pow_eq_one` (Φ : E → P additive-to-multiplicative, surjective, kernel a full ℤ-lattice Λ of a fin-dim real normed space E ⇒ #{x : P | xⁿ = 1} = n^(dim_ℝ E)), `finrank_real_fin_complex` (dim_ℝ ℂ^g = 2g). COMPILES, standard axioms. (VERIFIED)

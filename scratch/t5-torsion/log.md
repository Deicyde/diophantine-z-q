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

# shimura-split results log

## Setup
- `.lake/build` and `lean/.lake/build` copied (reflink) from ~/dzq-check2 (same commit 5da857b0; OneProof chain
  built through TailX, Main). Kernel-only scratch files load in ~45 s.

## Step 1: uniqueness of base change (Bridge.lean §1-§2) — COMPILED (lake env lean, kernel imports)
- `pt_one_left`: `(1 : A.Pt L).left = η[A.X].left`.
- `bc_core`: two pullbacks of `A` along `Spec f` whose identity sections lie over `η_A` are isomorphic by
  mutually inverse homomorphisms over `A` (rigidity: kernel `MulRigidity.isMonHom_of_geometricallyIntegral`).
- `bc_unique3 : IsBaseChangeOf f P Q → IsBaseChangeOf f P Q' → Nonempty (Q.Iso Q')`;
  `bc_transport3 : IsBaseChangeOf f P Q → Q'.Iso Q → IsBaseChangeOf f P Q'`;
  `bc_uniquePair`, `bc_transportPair` (the same for `QMPair`, `QMIso`).
- Finding: leaf-qm-fp §2.4 kept `R1rec` as a separate leaf because this uniqueness "needs rigidity, which
  Mathlib does not have"; the kernel now has rigidity, so the bridge is provable.

## Step 2: Galois correspondence and the bridge (Bridge.lean §3-§5) — COMPILED, standard axioms
- `fixing_iff : Spec.map σ ≫ y = y ↔ σ ∈ (residueImage y).fixingSubgroup` (y : Spec ℚ̄ ⟶ X).
- `fieldOfModuli3_eq_residueImage : R1fpProps Y Φ → Φ ℚ̄ y = M3.mk P → fieldOfModuli3 P = residueImage y.left`.
- `fieldOfModuliPair_eq_residueImage : X6Props Y Φ X Ψ fY → Ψ x = ⟦P⟧ → fieldOfModuliPair P = residueImage x.left`.
  (uses bc_unique/bc_transport, naturality / Galois clause, `InfiniteGalois.fixedField_fixingSubgroup`).
- `r1rec_of_point : (∃ Y Φ, R1fpProps Y Φ ∧ R1recProps Y Φ) → R1rec`; `point_of_r1rec` (converse on any fine witness).
- `r5fp_of_point : (∃ Y Φ X Ψ fY, X6Props Y Φ X Ψ fY ∧ R5ptProps X Ψ) → R5fp`; `point_of_r5fp` (converse).
- `#print axioms`: [propext, Classical.choice, Quot.sound] for all six.

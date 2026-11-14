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

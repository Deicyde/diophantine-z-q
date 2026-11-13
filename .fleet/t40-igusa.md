# t40-igusa (fleet summary)

**Main result.** T40 (`X1Belyi.X1RationalCusp`) and T39 now follow from ONE published leaf,
`ZInQ.RLeaf.X0Transitive` (Galois transitivity on cyclic subgroups of order `N` of `E_j`, i.e.
irreducibility of `X₀(N)`): `x1RationalCusp_of_x0Transitive`, `x1ConstantField_of_x0Transitive`,
and `igusaTransitive_iff_x0Transitive : IgusaTransitive ↔ X0Transitive` (T40.lean). Route: this
task proved `igusaTransitive_iff : IgusaTransitive ↔ X0Transitive ∧ TateMuN` (all glue) and the
transfer `tateMuN_of_at` / `tateMuN_of_over` (TateMuN may be checked over any algebraically
closed `Ω ⊇ ℚ(j)`, per level); task t40-tate then proved `tateMuN : TateMuN` through it and
`tateCuspLaurent`. Also `igusaTransitive_of_igusaGL2` / `_of_igusaSL2X` (Igusa 1959 / Shimura
Thm 6.6 as alternative leaves).

**T40.lean** (written here, t40-tate finished first): T40/T39 from `X0Transitive`, from
`X0Transitive ∧ TateMuN`, and from `IgusaGL2` / `IgusaSL2X`.

**What compiles.** `lake build ZInQKernel.Contrib.RLeaf.T40` succeeds (9395 jobs, includes t40-tate's TateCusp, TateCuspMuN); all
`#print axioms` = `[propext, Classical.choice, Quot.sound]`. Files (all new, namespace `ZInQ.RLeaf`):
`ZInQKernel/Contrib/RLeaf/{IgusaSL2,IgusaX0,IgusaLocal,T40}.lean`.

**Declarations proved.** `exists_det_eq_one_of_addOrderOf`, `exists_SL2_first_column`,
`igusaTransitive_of_igusaSL2X`, `igusaSL2X_of_igusaGL2`, `igusaTransitive_of_igusaGL2`,
`xCoord_neg`, `eq_or_eq_neg_of_xCoord_eq`, `addOrderOf_galPt`, `xCoord_galPt`,
`igusaTransitive_of_x0_tateMuN`, `x0Transitive_of_igusaTransitive`, `tateMuN_of_igusaTransitive`,
`igusaTransitive_iff`, `xCoord_map_alg`, `exists_map_eq_of_nsmul_eq_zero`, `exists_restrict`,
`tateMuNOver_iff`, `tateMuNAt_kbar`, `tateMuN_of_over`, `tateMuN_of_at`, `transcendental_X`,
`transcendental_X_inv`, `jInv_X`, `jInvLaurent_X`, `tateMuN_of_local`,
`igusaTransitive_of_x0_tateMuNLocal`, `x1RationalCusp_of_x0_tateMuN`,
`x1ConstantField_of_x0_tateMuN`, `x1RationalCusp_of_x0_tateMuNLocal`,
`igusaTransitive_iff_x0Transitive`, `x1RationalCusp_of_x0Transitive`, `x1ConstantField_of_x0Transitive`,
`x1RationalCusp_of_igusaGL2`, `x1RationalCusp_of_igusaSL2X`, `x1ConstantField_of_igusaSL2X`.

**What remains.** `X0Transitive` (published: Lang, *Elliptic functions*, Ch. 5 §2; Cox Thm 11.18;
numbers UNVERIFIED). Needs a global input (complex uniformization / moduli irreducibility); no
proof route exists in Mathlib or Tau Ceti (decision recorded in docs/research/t40-igusa.md §2).
`TateMuN` is done (t40-tate's `ZInQ.RLeaf.tateMuN`, merged).

Report: docs/research/t40-igusa.md. Log: scratch/t40-igusa/log.md.

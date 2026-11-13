# x1-dirichlet (fleet summary)

**Result: both glue Props are proved, and no statement was changed.**

- `DirichletOfFinite`, copied verbatim from scratch/g0-mod-newform/part_new.lean L727-738, is
  proved from the leaf T17 in its cyclic form `TSkolemKW.KW.KroneckerWeberCyclic`
  (TextbookLeaves field `t17`):
  `X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic` in `scratch/x1-dirichlet/Dirichlet.lean`
  (imports only `ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`). New glue: roots of unity of
  `ℚ̄_ℓ` lie in `ιL(ℚ̄)`; an arithmetic Frobenius at `p ∤ m` has mod-`m` cyclotomic character `p`
  (`cycChar_frob`, by a valuation and geometric-sum argument); then assembly with the kernel's
  C8 glue `dirichletCharacter_of_kroneckerWeberCyclic`.
- `X1ModelExists`: g0-mod-newform's `hX` is `LeafModCurves.X1ModelExists`, which x1-belyi already
  proved (`X1Belyi.x1ModelExists_and_belyiX1`, from `x1 : X1Belyi.X1Leaves`, TextbookLeaves field
  `x1`). `scratch/x1-dirichlet/Connect.lean` (assembled by `build.sh` from a copy of
  NewForm.lean) restates g0-mod-newform's theorems with both hypotheses discharged:
  `modularConstituent_tail_G_leaves`, `modularConstituent_tail_leaves`, `g16Out_with_J1_leaves`,
  `g12Spec_of_galois_kw`, `panOutput_of_G12Out_kw`, plus `dirichletOfFinite_iff` (`Iff.rfl`
  between the two copies).

**What compiles (VERIFIED):** `lake env lean` exits 0, with no `sorry`, on Dirichlet.lean (2
prints) and Connect.lean (10 prints). Every printed declaration depends only on
[propext, Classical.choice, Quot.sound].

**What remains:** nothing for these two targets. g0-mod-newform's other open glue Props
(G14TraceCompat, G15RamG (i)-(ii), SwanIndependent, SwanIntegral, AdaptedExists) were out of
scope. Integration: adopt Dirichlet.lean as a kernel module and replace g0-mod-newform's copy of
`DirichletOfFinite` with it. Report: docs/research/x1-dirichlet.md.

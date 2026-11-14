# av-b1 (2026-11-13): leaf-fold3 fields t6, t7, t8 (textbook abelian varieties)

**Result.** All three fields are reduced to strictly smaller named Props, with all the glue proved
(no sorry, axioms `[propext, Classical.choice, Quot.sound]`). None is proved outright: each
reduced Prop is still a theorem about abelian varieties that Mathlib 4.35 cannot reach.
- T6 `PkgI3.HomFreeFinite` ⇐ `HomFreeFiniteAlgClosed` (the same statement for `[IsAlgClosed k]`:
  Mumford §19 Thm 3 verbatim, in Mumford's setting): `ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed`.
- T7 `PkgI3.CharPolyIndepOfEll` ⇐ `CharPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4, consequence,
  for `[IsAlgClosed k]`): `ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed`.
- T8 `PkgI3.PoincareReducibility` ⇐ `PoincareComplement` (Poincaré's theorem in Milne's complement
  form, Prop. 12.1, weakened) ∧ `SimpleImageIsogeny` (GLUE: a nonzero homomorphism out of a simple
  abelian variety is an isogeny onto its image), `poincareReducibility_of_simpleImage`. Or ⇐
  `PoincareComplement` ∧ `ImageFactorization` ∧ `SimpleSurjIsogeny`, `poincareReducibility_of_pieces`.

**Glue proved** (new Mathlib-level file `ZInQKernel/Contrib/AVB1/BaseChange.lean`): injective base
change of homomorphisms `bcHom_injective` (`A_{K̄} → A` is flat and surjective, so an epimorphism);
naturality `tateBC_homT`; `T_ℓ(A) ≅ T_ℓ(A_{K̄})` with no hypothesis (`tateBC_bijective_closure`);
`ℤ_ℓ` flat over `ℤ`. T8 glue (`Poincare.lean`): `(f, g) = (i, g) ∘ (h × 1)`, and `h × 1` is finite and
surjective by base change.

**Compiles.** `lake build ZInQKernel.Contrib.AVB1.{BaseChange,AlgClosed,Poincare}` succeeds;
`#print axioms` in `scratch/av-b1/Axioms1.lean` gives the standard three. The flat single file
`scratch/av-b1/AVB1Check.lean` (built by `mk_check.py`: leaf-fold3's `Leaves3.lean` + the AVB1 files
renamed onto `HDec.PkgI3` + `check_tail.lean`) proves leaf-fold3's own fields:
`HDec.AVB1Check.t6_of_algClosed`, `t7_of_algClosed`, `t8_of_pieces`, `t8_of_simpleImage`,
`t6_t7_t8_of_avb1`, `t6_t7_t8_of_avb1'`. It exited 0 in ~1030 s, with no sorry and only standard
axioms; the run log is in `scratch/av-b1/log.md`. `verbatim_check.py`: the 26 declarations behind
t6-t8 have the same text in `HDecomp/Objects.lean`, `scratch/pkg-I3/I3.lean` and `Leaves3.lean`.

**Remains open.** `HomFreeFiniteAlgClosed`, `CharPolyIndepOfEllAlgClosed`, `PoincareComplement` are
published theorems (LEAF; locators UNVERIFIED, from memory). `SimpleImageIsogeny`, or
`ImageFactorization` with `SimpleSurjIsogeny`, is GLUE that needs scheme-theoretic images, kernels
and Cartier's theorem, none of which exists for the kernel's `AbVar`. No statement change is
proposed: t6-t8 are true and never stronger than the published theory. Report:
docs/research/av-b1.md.

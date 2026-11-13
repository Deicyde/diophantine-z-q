# x1-dirichlet results log

## Targets
- `DirichletOfFinite` (copied verbatim from scratch/g0-mod-newform/part_new.lean L727-738;
  diff of the docstring+def block: identical, VERIFIED).
- `X1ModelExists` as g0-mod-newform consumes it: `hX : X1ModelExists` in
  `G0ModNewform.g16Out_with_J1`, `modularConstituent_tail`, `modularConstituent_tail_G`; NewForm.lean
  has no local `X1ModelExists`, so the name is `LeafModCurves.X1ModelExists` (open LeafModCurves),
  the target of `X1Belyi.x1ModelExists_of_leaves` (ZInQKernel/HDecomp/ModCurves/X1Belyi.lean)
  (VERIFIED by grep; compile check pending).

## Dirichlet.lean (04:13-04:22)
- `lake build ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`: success (2m44s).
- run1: errors (`pow_eq_one_iff` is the group-with-zero-free version; `mul_le_mul_left'` gone;
  `pow_card_eq_one` rewrite; `MulChar.map_mul` unknown).
- run2: exit 0, no error, no sorry. `#print axioms` of `X1Dirichlet.cycChar_frob` and
  `X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic`: [propext, Classical.choice, Quot.sound]
  (VERIFIED).
- Result: `dirichletOfFinite_of_kroneckerWeberCyclic : KroneckerWeberCyclic → DirichletOfFinite`
  (leaf T17 narrowed, bundle field `t17`). New glue lemmas: `exists_preimage_of_pow_eq_one`,
  `valuation_eq_one_of_pow`, `cycChar_frob` (Frobenius at `p ∤ m` has cyclotomic character `p`;
  argument: if `ζ^a ≠ ζ^p` then `η = ζ^a/ζ^p ≠ 1`, `v(η-1) < 1`, `Σ_{i<m} η^i = 0` gives
  `v(m) < 1`, contradicting `v(p) < 1` and `gcd(p,m) = 1`).
- `S = m.primeFactors`, `ψD = ofUnitHom (ιC ∘ ιL⁻¹ ∘ χ)` where `χ` is the Dirichlet character
  over `ℚ̄_ℓ` of the kernel's `dirichletCharacter_of_kroneckerWeberCyclic`.

## Connect.lean (04:22-04:30)
- `lake build` of NewForm's imports + `ZInQKernel.HDecomp.ModCurves.X1Belyi`: success (5m54s).
- Connect.lean (build.sh: NewForm.lean copy + Dirichlet body + part_connect.lean, 2750 lines):
  run1 `lake env lean scratch/x1-dirichlet/Connect.lean`: exit 0, no error, no sorry (1m05s).
  Output in compile.out. The 10 `#print axioms` lines (cycChar_frob,
  dirichletOfFinite_of_kroneckerWeberCyclic, dirichletOfFinite_iff, g0_dirichletOfFinite,
  g0_x1ModelExists, panOutput_of_G12Out_kw, g12Spec_of_galois_kw, g16Out_with_J1_leaves,
  modularConstituent_tail_leaves, modularConstituent_tail_G_leaves) all report
  [propext, Classical.choice, Quot.sound] (VERIFIED).
- `G0ModNewform.DirichletOfFinite ↔ X1Dirichlet.DirichletOfFinite := Iff.rfl` compiles (VERIFIED):
  same Prop in g0-mod-newform's context.
- `TSkolemKW.KW.KroneckerWeberCyclic` in the kernel and in scratch/h-decomposition/Leaves.lean
  (field `t17` of TextbookLeaves): identical text (VERIFIED by diff). `x1 : X1Belyi.X1Leaves` is a
  field of TextbookLeaves (VERIFIED, Leaves.lean L33086).

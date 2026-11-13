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

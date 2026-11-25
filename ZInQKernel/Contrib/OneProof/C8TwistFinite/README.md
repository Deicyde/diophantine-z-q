# C8 without `conradAppB` (work in progress)

Goal: remove the hypothesis `conradAppB` (Conrad, *Lifting global representations with local
properties*, App. B; GLUE) from `ZInQ.OneProof.frozenTarget` by proving in Lean what its only
consumer needs, with no new leaf. Count 24 → 23; strict and strictest GLUE each down by one;
LEAF unchanged.

## Where `conradAppB` is used (base `3f2a7111`)

`OpenAddedLeaves28.conradAppB` (`TailZ87`) is read only by `c8Leaves_of_OpenAddedLeaves28`,
which feeds `C8Conrad.c8Inputs_of_leaves` in `sixContactMin_of_open82_nos`
(`NOSNarrowChain.lean`, the live copy chain under `sixContactMin_of_open83_nos`, reached from
`sixContactMin_of_open95` through `TailZ102`–`TailZ91`). The C8 inputs travel as the argument `c8`
of `GR9.sixContactMin_of_open45_pz_eb_sf_u_hm_cm_y3c_nos`, then as the field `c8` of the added
bundles `OpenAddedLeaves18PZC8` … `OpenAddedLeaves12PZC8` (`C8Chain.lean`) and
`OpenAddedLeaves9PZC8_y3c` … `OpenAddedLeaves4PZC8_y3c` (`Y3Copy5.lean`), into the field `c8` of
`GaloisPiecesC8` built in `sixContactMin_of_open4_cm_u_c8_y3c_nos`. Its only reader is
`g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c_nos`:
`C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10`, which uses `conradAppB` only through
`c8TwistFinite_of_conradB`, i.e. for `C8Conrad.C8TwistFinite` (the twist `ψ` has finite image).

## The glue (this directory)

* `LocalUnits.lean` (no H-chain import): for a continuous character `f` of `G_{ℚ_p}` into a
  commutative T₁ group, `unitChar f : ℤ_p^× →* M`, continuous, with `f σ = unitChar f (χ σ)` for
  every representative `σ` of the Artin symbol of a unit (Tau Ceti's local class field theory of
  `ℚ_p`; continuity because `χ` restricted to the compact inertia group is a quotient map).
* `TensorEigen.lean` (no H-chain import): a weight-0 Hodge–Tate splitting (`PureHT'`, word for word
  `C8Conrad.Bridges.PureHT`) gives a nonzero `t ∈ ℂ_p ⊗ E` with `(σ ⊗ 1) t = (1 ⊗ ψ(σ)⁻¹) t`; if
  `ψ^d` is trivial on the kernel of `χ`, then `ψ` has finite order (`ℂ_p ⊗ E` is reduced, so `t^d ≠
  0`, and `TensorTwist.solution` with `CyclotomicTrace.solution` applies, as in
  `TwistWholeGroup`).
* `GlobalSplit.lean` (no H-chain import): `ψ = β · (φ ∘ χ_ℚ)` with `φ = unitChar (ψ ∘ decomp)` and
  `β` trivial on Artin symbols of units at `p`; with class field theory over `ℚ` in unit form
  (`NoRamUnits`), `β^d = 1`, then Tate's theorem and the surjectivity of `χ` give `ψ^{Nd} = 1`
  (`range_finite_of_pureHT`).
* `Adapter.lean`: `ZInQ.Contrib.C8TwistFinite.c8TwistFinite_proof (hR : EigenformRepExists)
  (hHT : EigenformHT) : C8Conrad.C8TwistFinite` from `twistCharHTWt0_proof`,
  `Bridges.pureHT_of_hasHTWeights` and `finiteOfLocAlgTrivialQNoRam_of_dicts inertiaAtPDecomp_proof
  minkowskiInertiaQ_proof` (at `k = 0`), and `g12DetPZ_proof (hR) (hHT) (h9) (hdR) : G12DetPZ`.

## The copy reroute (`Chain.lean`, generated)

Generated from `C8Chain.lean`, `TailZ87`, `Y3Copy5`, `NOSNarrowChain.lean` and `TailZ91`–`TailZ102`
by a text-level generator in the style of the earlier fold generators: parse the live route's
files into declarations, keep those reachable by name from `sixContactMin_of_open95`, taint by name
from the carriers of `conradAppB` (`OpenAddedLeaves28`, `C8Inputs`, the bundles with a field `c8`,
`GaloisPiecesC8`), and copy the tainted ones with the suffix `C8TF` (structures) / `_c8tf`
(theorems). 85 declarations are copied; `c8Leaves_of_OpenAddedLeaves28` is dropped. Edits in the
copies:

* the field `conradAppB` of `OpenAddedLeaves28C8TF` and every field `c8` (with its docstring) are
  deleted, together with the lines `c8 := …` and the anonymous-constructor entry `l.c8`;
* the argument `(c8 : C8Inputs)` of `GR9.sixContactMin_of_open45_…_nos_c8tf` and of
  `openAddedLeaves18_hm_c8tf` is deleted, with the call `c8Inputs_of_leaves
  (c8Leaves_of_OpenAddedLeaves28 l)` in `sixContactMin_of_open82_nos_c8tf`;
* the reader becomes `ZInQ.Contrib.C8TwistFinite.g12DetPZ_proof r.r14 r.r13 h9 r.r10`;
* `set_option maxHeartbeats` lines are dropped and long lines wrapped at 100 columns.

New top: `HDec.HSyn.sixContactMin_of_open95_c8tf (r : OpenResearchLeaves76)
(t : OpenTextbookLeaves18) (l : OpenAddedLeaves28C8TF) : ZInQ.SixContactMin`.

This reroute is built against current main, independently of the `dsThm965AtPrimes` reroute
(#197). The generator takes the list of live-route files and the top theorem as parameters, so it
can be re-run after #197 is folded, on the then-live files (#197's copies and the new top
generation), to give the same reroute on top of it.

## `FoldCheck.lean`

* `addedLeaves28C8TF_ofLive (l : OpenAddedLeaves28) : OpenAddedLeaves28C8TF`, by field projections
  only (the new bundle has the fields `scholzeH1AbVar`, `t10TateDuality`).
* `example : OpenResearchLeaves76 → OpenTextbookLeaves18 → OpenAddedLeaves28C8TF → SixContactMin :=
  sixContactMin_of_open95_c8tf`.
* `frozenTarget_without_conradAppB`: `frozenTarget`'s body from `Main.lean` at `3f2a7111`, verbatim,
  with `sixContactMin_of_open95` replaced by `sixContactMin_of_open95_c8tf` and the binder `l` of
  type `OpenAddedLeaves28C8TF`; `#print axioms` for it and the glue.

## The fold (integrator)

1. `OneProof/H/TailZ103.lean`: `structure OpenAddedLeaves29` with the fields of
   `OpenAddedLeaves28C8TF` (`OpenAddedLeaves28` without `conradAppB`), the field-by-field
   conversion `openAddedLeaves28C8TF_of_OpenAddedLeaves29`, and
   `theorem sixContactMin_of_open96 (r : OpenResearchLeaves76) (t : OpenTextbookLeaves18)
   (l : OpenAddedLeaves29) : ZInQ.SixContactMin :=
   sixContactMin_of_open95_c8tf r t (openAddedLeaves28C8TF_of_OpenAddedLeaves29 l)`.
2. `Main.lean`: `frozenTarget (… (l : HDec.HSyn.OpenAddedLeaves29) …)` through
   `sixContactMin_of_open96`; `FoldCheck.frozenTarget_without_conradAppB` is this body.
3. Remove the `kinds.tsv` row of `conradAppB`; regenerate `open-statements.json` and OPEN.md.
4. No existing constant changes; only `frozenTarget`'s statement loses the field.

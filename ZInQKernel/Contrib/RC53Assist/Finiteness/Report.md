# Finiteness of compact Kummer cohomology and of finite-level Selmer cohomology

## Shipped edition (2026-11-18, second edition)

One module, `ZInQKernel.Contrib.RC53Assist.Finiteness.GaloisFiniteness`, compiled as a single
file against the integration head that contains the inner-limit stage inputs
(`ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageInputs`) and the stage residual module
(`ZInQKernel.Contrib.RC53Assist.ResidualFiniteness.StageResidual`). It imports both and
restates none of their definitions. `StatementsAndAxioms.txt` records the statement and the kernel
axiom output of each of its 83 declarations; the union of the axioms used is exactly `propext`,
`Classical.choice`, `Quot.sound`.

## The printed inputs

The only inputs are the two finiteness prints of the stage inputs, used as stated there,
`ZInQ.Contrib.RC53Assist.InnerLimitArith.MilneLocalFiniteness` and
`ZInQ.Contrib.RC53Assist.InnerLimitArith.MilneGlobalFiniteness`. Their locators in the print
(Milne, *Arithmetic Duality Theorems*, second edition, 2006) are:

* local finiteness: Chapter I, Theorem 2.1, last sentence of the statement (p. 27), under the
  standing hypothesis of I §2 (p. 26): "The groups `Ext^r_G(M, Kˢ)` and `H^r(G, M)` are finite for
  all `r` if `M` is of finite order prime to `char(K)`";
* global finiteness: Chapter I, Corollary 4.15 (p. 62), under the standing hypotheses of I §4
  (p. 48): "If `S` is finite and `M` is a finite `G_S`-module whose order is a unit in `R_{K,S}`,
  then the groups `H^r(G_S, M)` are finite for all `r`." The opening of I §5 (p. 66) recalls it.

All-degree finiteness is not in Corollary 2.3 (local duality, whose finiteness clause is for `H¹`
only) nor in Theorem 4.10 (Poitou–Tate). The docstrings of the stage residual module still cite
I.2.3 and I.4.10 for these two inputs.

## Compact Kummer cohomology

* `kummerCohomologyFinite_of_prints ℓ k S hFull hloc hglob hS h2` and
  `kummerCohomologyFinite_of_comparison ℓ k S hFull hloc hglob I h2`: the input
  `KummerCohomologyFinite ℓ k S hFull` of the universal-coefficient construction, for the genuine
  compact Kummer complex, with `h2 : ∀ v, (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ S` (the
  finiteness of `S` is the field `finite_support` of the coefficient comparison `I`).
* `moduleFinite_compactKummer_homology`: every cohomology group of `compactKummerComplex S W hFull`
  is a finitely generated `ℤ₂`-module, for every number field, finite `S` containing the primes
  above `2` and elliptic curve with full `2`-power torsion over `K_S`.
* `centralSelmerComparisonOfPrints`, `hcentral_of_prints`: the central comparison and the
  base-zero rank with this input discharged.

Route: the continuous cochains with values in `T_2E = lim E(K_S)[2^k]` are the inverse limit of
the continuous cochains with values in the levels (`IsTwoAdicLimit`, `isTwoAdicLimit_tate`; the
reduction is surjective with kernel `2^k`, and the cochains are two-adically complete and
separated). The global print at every level bounds their cohomology modulo every `2^k`
(`TwoPowResidualFinite`). The Mittag-Leffler step (`exists_eq_of_forall_two_pow`, by Kőnig's
lemma) and complete Nakayama over `ℤ₂` (`moduleFinite_of_two_adic`) give
`moduleFinite_globalTateCohomology` and `moduleFinite_localTateCohomology`. The exact sequences of
the Selmer cone over the noetherian ring `ℤ₂` (`moduleFinite_homology_selCx`), with the `2`-adic
Kummer condition controlled in every degree (`moduleFinite_tateKummerCondition_homology`), give the
compact complex.

## Finite-level and stage cohomology

* `finite_galoisSelmer_homology` (the stage input `galoisSelmerCohomologyFinite_of_prints`, read
  degreewise), `moduleFinite_galoisSelmer_homology`, `moduleFinite_stageSelmer_homology` (the stage
  input `stageSelmerCohomologyFinite`, as finite generation over `A_i`).
* `finite_actualSelData_homology`, `moduleFinite_actualSelData_homology`,
  `finite_kummerSelData_homology`: finiteness of the cohomology of the actual stage complexes and of
  the finite-level Kummer Selmer complexes.
* `residualCohomologyFinite_kummerSelData`: finite residual cohomology of the finite-level Kummer
  Selmer complexes, from `actualStageSelmer_residualCohomologyFinite` and
  `residualCohomologyFinite_cocycleCondition` of the stage residual module.
* Local conditions: `finite_cocycleCondition_homology`, `finite_kummerAt_homology`,
  `finite_urAt_homology`, `finite_zeroAt_homology`, `finite_strictConditions_homology`.

## Changes from the first edition

* The restated `MilneLocalFiniteness`, `MilneGlobalFiniteness`, `gcxBaseChange` and
  `ResidualCohomologyFinite` are removed; the originals of the stage inputs are used.
* Removed as duplicates of the stage inputs: `subquot`, `finite_subquot_congr`, `finite_of_exact`,
  `finite_gcx_homology_iff`, `ker_d_congr`, `finite_homology_shiftDown`, `finite_homology_piCx`,
  the generic finite Selmer lemma, the two-power order of `M_i`, and the finiteness of the relaxed
  and full conditions (`localCohomology_finite`).
* Removed as duplicates of the stage residual module: the whole residual development
  (`IdealResidualFinite`, the residual finiteness of the Selmer cone, of finite products and of
  continuous cochains, the residual finiteness of the Galois and stage Selmer complexes and of the
  local conditions, the reduced action on `M / 𝔪M`), the finiteness of the terms of two-term
  complexes, and the finiteness of homology from finite terms.
* `finite_galoisSelmer_homology`, `moduleFinite_stageSelmer_homology`,
  `finite_cocycleCondition_homology`, `finite_urAt_homology` and
  `residualCohomologyFinite_kummerSelData` are now short uses of the stage inputs and of the stage
  residual module.
* The two-adic residual notion is renamed `TwoPowResidualFinite` (with
  `twoPowResidualFinite_of_levels`), to avoid confusion with residual cohomology.

## Precisely still open

1. The two printed statements remain inputs.
2. The support hypothesis `h2` (the primes above `2` lie in `S`) is kept. It is implied by full
   `2`-power torsion over `K_S` (through the Weil pairing and the ramification of two-power
   cyclotomic extensions above `2`), which is not formalized here.
3. For general local conditions, the finiteness of their cohomology is a hypothesis; it is proved
   for the standard conditions listed above.

## Verification

The module compiles with the prescribed single-file command, six threads and the prescribed CPU
affinity and niceness, with no warning. No existing file was edited; no build, update,
executable or version-control command was run for this edition.

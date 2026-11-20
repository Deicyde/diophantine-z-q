# Stage 1 sizing

Base: `2792b59cf602398df77fb012a408cc7f0c0689e2`.

- VERIFIED (TeX): `diophantine_zq.tex` L1086–1104 states both low analytic ranks and full Sha finiteness; the two pole applications at L1111–1121 have analytic rank one, from L1005–1011 and L1033–1035. L1092–1097 invokes BCDT and MPI/90-69; L11163–11167 identifies that preprint. L1779–1788 describes the modular parametrization for this family.
- VERIFIED (Lean sources): `OneProof.frozenTarget` passes `hK` to `poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing`, then to `poleCompleteness_of_restrictedConverseGenuine_casselsTate`. The latter calls `kolyvaginRankOne_of_printed` with `bcdtThmA_of_printed hB`. The adapter reads only `.1` of `hK E hE hM hA`. `crm_of_restrictedConverse_proved` calls `crm_of_restrictedConverse_M`, which uses that rank equality only via `exists_not_isOfFinAddOrder_of_rank`. The call has positive, squarefree `ℓ ≡ 11 (mod 12)`, eight explicit Selmer classes, and analytic rank one. `descentGlueM` takes the infinite-order witness and proves surjectivity by counting, without a Sha hypothesis.
- VERIFIED (Lean sources): the other calls to `kolyvaginRankOne_of_printed` in the import tree (the `Genuine` and `GenuineMW` routes and their wrappers) are alternate assemblies. They also use the same first projection. `Prints/Kolyvagin.lean` has a separate preprint interface allowing both low ranks, with an analytic stand-in for the weak Weil parametrization. `Wiring/KolyvaginBridge.lean` specializes it to one and uses `ModularToWeakWeil` as an explicit premise. These bridges are not on the headline's proof path.
- VERIFIED (source inspection): `HKConsumed` restricts the input to that family and the eight-class call, retains the modularity premise supplied by the separate BCDT hypothesis, and asks only for an infinite-order point. No rank-zero, upper-rank, or Sha assertion is required. The stop rule for a stronger-than-rank-one use does not trigger.

## Candidate statements and checks

- SPECULATIVE (locators UNVERIFIED): the two candidate rank projections start with an infinite-order conductor-one Heegner trace over a split imaginary quadratic field. Neither candidate is a verified LEAF.
- VERIFIED (Lean): `HKRefereedConsumed.lean` and `HKRefereedPrintDrafts.lean` passed with `lake env lean` after building their imports. `hkConsumed_of_hK` and `hkConsumed_of_heegnerRank` each report precisely `[propext, Classical.choice, Quot.sound]`.
- VERIFIED (base source): the unchanged height supplier `HDec.HSyn.sixContactMin_of_open91` has type `OpenResearchLeaves72 → OpenTextbookLeaves18 → OpenAddedLeaves28 → ZInQ.SixContactMin`. The dry run abstracts only that supplier; it uses the actual printed BCDT adapter, pole reduction, and final assembly.
- OPEN: `PoleNonTorsionHeegnerTrace` supplies the point required by either candidate; `PoleHeegnerRankDescent` or an equivalent orientation argument identifies the rational line. Neither is offered as a printed theorem.

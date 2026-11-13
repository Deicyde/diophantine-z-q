# g15-decomp results log

## Setup
- Merged origin/main and origin/wip/diff-bridge (ZInQKernel/Contrib/Different/*). VERIFIED (git).
- G15 transports in the kernel are informal (docstrings of ZInQKernel/HDecomp/Conductor/D1Local.lean,
  Breaks.lean §D1; h-decomposition.md G15 row): no `def … : Prop` states them. VERIFIED (git grep
  G15|decomposition group|Krasner|completion over ZInQKernel/HDecomp, scratch/h-decomposition).
- Mathlib has Krasner's lemma (`IsKrasner`, Mathlib/Analysis/Normed/Field/Krasner.lean) and
  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv : v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v]`. VERIFIED (read).

## ZInQKernel/Contrib/G15/Transport.lean
- 04:12 compiles (`lake env lean`, 5 s): ramGroup_eq_ramificationGroup, ramGroup_le_decompGroup,
  mem_ramGroup_iff_decompositionHom_mem, decompEquiv (D_P ≃* Gal(L_w/ℚ_v)), decompEquiv_algebraMap,
  map_ramGroup_decompEquiv, ramCard_eq_card_localRam(_fun), ramGroup_ne_bot_iff,
  card_decompGroup_eq_finrank. VERIFIED (compiled).
- 04:18 Intermediate section compiles (`lake env lean`): completionAlgHom_algebraMap, inclQv, localField,
  localFieldEquiv, finrank_localField, algebraMap_mem_localField, mem_localSub_iff,
  map_localSub_decompEquiv (D_P ∩ Gal(L/K) ↦ fixingSubgroup of K_u in L_w), index_localSub_eq_finrank
  ([K_u:ℚ_v] = index), normalCore_fixingSubgroup_eq_bot, normalCore_eq_bot_of_map_equiv,
  normalCore_localSub_eq_bot. VERIFIED (compiled).

## ZInQKernel/Contrib/G15/D1Completion.lean
- 04:24 compiles: exists_prime_liesOver, ramificationIdx_le_factorial_completion,
  D1_completion_ramGroup, D1_completion (φ_{L_w/ℚ_v}(b) ≤ 4a² from [K_u:ℚ_v] ≤ a and
  normalClosure(K_u ⊂ L_w) = ⊤; closed via Different.D1_genuine_closed). VERIFIED (compiled).
- Finding: G15RamG (g0-mod-newform NewForm.lean L2459) is stated on LadicCond objects
  (`Fld p` = IntermediateField ℚ_[p] (PadicAlgCl p), `ramSet`/`ramCard` defined by norms with a
  uniformizer, `upperAbs`). Transport global ramGroup ↔ LadicCond.ramSet is the link g15-ram needs
  beyond L_w. VERIFIED (read).

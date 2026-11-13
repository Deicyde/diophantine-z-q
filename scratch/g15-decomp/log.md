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

## ZInQKernel/Contrib/G15/LadicBridge.lean (namespace ZInQ.Contrib.G15.Ladic)
- 04:50 §1-4 compile: nv (x ↦ ‖j x‖₊), norm_le_one (𝓞 L ↦ unit ball), primeOf j : HeightOneSpectrum (𝓞 L)
  ({x | ‖j x‖ < 1}), primeOf_liesOver (over span{p}), isEquiv_nv (P-adic valuation ~ ‖j ·‖),
  unif, norm_le_unif_pow_iff (‖j y‖ ≤ ‖jπ‖^k ↔ y ∈ P^k), Lj j := adjoin ℚ_[p] (j L) : Fld p,
  isUnif_unif, norm_eq_of_isUnif, mem_ramSet_iff (σ ∈ LadicCond.ramSet (Lj j) i ↔ τ ∈ ramGroup L P i
  when j ∘ τ = σ ∘ j). VERIFIED (compiled). Density from TauCeti.exists_mem_norm_sub_lt_of_mem_adjoin.
- 04:45 §5-10 compile: eq_of_isEquiv, norm_j_apply_of_mem_stabilizer (D_P preserves ‖j·‖), tauOf, tauOf_spec,
  eq_tauOf, exists_lift (D_P → G_Qp, via TauCeti.exists_algEquiv_apply_eq_of_norm_apply_eq),
  card_image_eq_of_fibres, restr_eq_iff, ramCard_Lj_eq (LadicCond.ramCard (Lj j) i = ramCard L P i),
  exists_Lj_eq_adjoin_simple, finiteDimensional_Lj, normal_Lj, isFinGal_Lj, mem_upperSet_of_mem_upperAbs,
  mem_stabilizer_of_spec, range_tauOf, card_restr_univ, mem_ramSetR_iff, decompFilt, card_decompFilt,
  ramCardR_Lj_eq, phiAt_Lj_eq (= TDifferent.phiF of the D_P-filtration), mem_upperSet_iff,
  decomp_spec, tauOf_eq_restrictNormal, mem_ramSet_iff_decomp, mem_upperSet_iff_decomp,
  galLjHom, decompEquivLj : Gal(Lj/ℚ_p) ≃* D_P, decompEquivLj_spec, decompEquivLj_mem_ramGroup_iff.
  VERIFIED (compiled; `lake build ZInQKernel.Contrib.G15.LadicBridge` ok).

## ZInQKernel/Contrib/G15/LadicD1.lean
- 04:50 compiles: phiF_natCast (TDifferent.phiF Γ m = ∑_{i∈Icc 1 m} |Γ_i|/|Γ_0|), phiAt_Lj_natCast,
  ramCard_Lj_ne_one_iff, ramCard_Lj_zero (g_0 = e(P|p)), D1_Lj (g_0 ≤ a!, 1 ≤ a, g_b ≠ 1 ⇒
  LadicCond.phiAt (Lj j) b ≤ 4a²; closed). VERIFIED (compiled).

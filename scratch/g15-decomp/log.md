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

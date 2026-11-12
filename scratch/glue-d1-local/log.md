# glue-d1-local results log

## Local.lean (Breaks.lean of glue-conductor copied verbatim, minus its #print lines, plus namespace GlueD1Local)
- `card_le_factorial_index_of_normalCore_eq_bot`: H ≤ D finite, core_D(H) = ⊥ → |D| ≤ [D:H]!. VERIFIED (compiled 23:31).
- `index_normalCore_le_factorial_index`: [D:core_D H] ≤ [D:H]!. VERIFIED.
- `ramificationIdx_le_card_decompGroup`: e(P|p) ≤ |Stab_{Gal(L/ℚ)}(P)|. VERIFIED.
- `ramificationIdx_le_factorial_local`: core_{D_P}(D_P ∩ Gal(L/K)) = ⊥ and [D_P : D_P ∩ Gal(L/K)] ≤ a → e(P|p) ≤ a!. VERIFIED.
- `D1_local`: D1_genuine with hea replaced by the two local hypotheses. VERIFIED.
- #print axioms: propext, Classical.choice, Quot.sound (23:31 PST).
- `card_decompGroup`: |D_P| = e(P|p)·f(P|p). VERIFIED (compiled 23:38).
- `localSubEquiv`: D_P ∩ Gal(L/K) ≃ Stab_{Gal(L/K)}(P). VERIFIED.
- `index_localSub`: [D_P : D_P ∩ Gal(L/K)] = e(w|p)·f(w|p), w = P ∩ 𝓞K (Mathlib card_stabilizer_eq over 𝓞K with G = K.fixingSubgroup, ramificationIdx_tower, inertiaDeg_tower). VERIFIED.
  Instance note: `IsGaloisGroup K.fixingSubgroup (𝓞 K) (𝓞 L)` is not found automatically; build it by
  `IsGaloisGroup.intermediateField Gal(L/ℚ) ℚ L K` then `IsGaloisGroup.of_isFractionRing _ (𝓞 K) (𝓞 L) K L`.
  `rw [Ideal.card_stabilizer_eq]` fails on the subgroup's action on ideals (instance path differs); `have … ; exact` works (defeq).
- `D1_local'`: D1 with hypotheses core_{D_P}(D_P ∩ Gal(L/K)) = ⊥ and e(w|p) f(w|p) ≤ a. VERIFIED.
- `normalCore_subgroupOf_eq_bot`: G = H·D and core_G(H) = ⊥ → core_D(H ∩ D) = ⊥. VERIFIED (23:45).
- `fixingSubgroup_mul_decompGroup`: K has one prime over p → Gal(L/ℚ) = Gal(L/K)·D_P. VERIFIED.
- `ramificationIdx_le_factorial_of_unique`, `D1_krasner`. VERIFIED.
- `normalCore_fixingSubgroup_eq_bot`: normalClosure ℚ K L = ⊤ → core(Gal(L/K)) = ⊥. VERIFIED (23:49).
- `D1_krasner'`. VERIFIED. All #print axioms: propext, Classical.choice, Quot.sound; 0 warnings.

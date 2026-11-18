import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Rules
import ZInQKernel.Contrib.OneProof.RC.Symbols.Stabilization
import ZInQKernel.Contrib.OneProof.RC.Symbols.Forest
import ZInQKernel.Contrib.OneProof.RC.KSplit.TwoPrimary
import ZInQKernel.Contrib.OneProof.RC.KSplit.Ap

/-!
# Lane RC24: the genuine symbols

Manuscript `diophantine_zq.tex`: Definition `ex:sec7-typed-graph` (tex 2015–2066), Definition
`ex:sec7-symbol` (tex 2068–2100), Lemma `ex:sec7-coefficient-rules` (tex 2102–2149), App F
(tex 9585, 9593–9594, 9670–9704, 9884–9976) and Proposition `ex:app-odd-stabilization`
(tex 10508–10552).

1. **`a_p` at good primes** (tex 9585: "For a split prime `a_p ≡ p + 1 (mod 4)`"; tex 9593–9594:
   "Here every prime is split in the rational two-torsion field, so `a_p ≡ p + 1 (mod 4)`").
   `apModFour_curve`, `apEven_curve`: for `E_m : y² = x(x − m)(x + 3m)` and a prime `p` prime to
   a modulus `M` containing every prime factor of `6m`, the Dirichlet coefficient at `p` of
   Mathlib's `L(E_m, s)` is `≡ p + 1 (mod 4)`, hence even. From lane RC3's
   `KSplit.LFunction_curve_apply_prime` (`a_p = p + 1 − |Ẽ_m(𝔽_p)|`) and `KSplit.four_dvd_card`
   (the subgroup `Ẽ_m(𝔽_p)[2]` of order four). `apEven_of` is batch 3's hypothesis `ApEven`
   (stated there as GLUE) for any type data whose conductor contains the prime factors of `6m`.
2. **Restriction of a symbol along a homomorphism of alphabets** (tex 2023–2024: "Additional
   fixed splitting conditions restrict us to their actual realizable types"; tex 2060–2065):
   `Config.mapType` commutes with flips and contractions, preserves isomorphism, compatibility
   (for the restricted sign coordinate) and primary types, and transports total types; hence
   `coefficientRules_comp`, `rulesUpTo_comp`, `isUnitSeed_comp_iff`.
3. **The stage symbol** (Definition `ex:sec7-symbol`, tex 2068–2100; App F tex 9670–9704):
   `stageSymbol T R Γ` is one exactly when `Γ` has a prime realization and every prime
   realization reads one. Within a budget where batch 3's fixed-`U` factorization holds it is
   batch 3's `symb` (`stageSymbol_eq_symb`), hence it obeys the coefficient rules
   (`rulesUpTo_stageSymbol`, `coefficientRules_stageSymbol`).

All statements are PROVED.
-/

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

/-! ### 1. `a_p ≡ p + 1 (mod 4)` at good primes -/

/-- A prime prime to a modulus `M` containing every prime factor of `6m` does not divide `6m`
(tex 9585, 9593: the good primes, outside the support). Kind: PROVED (helper). -/
theorem not_dvd_six_mul_of_coprime {m : ℤ} {M : ℕ}
    (hM : ∀ q : ℕ, q.Prime → q ∣ 6 * m.natAbs → q ∣ M) {p : ℕ} (hp : p.Prime)
    (hpM : Nat.Coprime p M) : ¬ (p : ℤ) ∣ 6 * m := by
  intro h
  have h' : p ∣ 6 * m.natAbs := by
    have := Int.ofNat_dvd_left.mp h
    rwa [Int.natAbs_mul] at this
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hpM (hM p hp h')

/-- **`a_p ≡ p + 1 (mod 4)` at a good prime** (tex 9585: "For a split prime
`a_p ≡ p + 1 (mod 4)`"; tex 9593–9594: "Here every prime is split in the rational two-torsion
field, so `a_p ≡ p + 1 (mod 4)`"). Kind: PROVED. For `E_m : y² = x(x − m)(x + 3m)` (`curve m`)
and a prime `p` prime to a modulus `M` containing every prime factor of `6m`: by lane RC3's
`KSplit.LFunction_curve_apply_prime`, the coefficient at `p` of Mathlib's `L(E_m, s)` is
`p + 1 − |Ẽ_m(𝔽_p)|`, and `4` divides `|Ẽ_m(𝔽_p)|` by lane RC3's `KSplit.four_dvd_card` (the
subgroup `Ẽ_m(𝔽_p)[2] = {O, (0, 0), (m, 0), (−3m, 0)}` has order four, all of `E_m[2]` being
rational). -/
theorem apModFour_curve (m : ℤ) (M : ℕ) (hM : ∀ q : ℕ, q.Prime → q ∣ 6 * m.natAbs → q ∣ M) :
    ∀ p : ℕ, p.Prime → Nat.Coprime p M →
      (ZInQ.Manuscript.curve (m : ℚ)).LFunction p ≡ (p : ℤ) + 1 [ZMOD 4] := by
  intro p hp hpM
  have := Fact.mk hp
  have hp6 := not_dvd_six_mul_of_coprime hM hp hpM
  have hp2 : p ≠ 2 := fun h => hp6 (by rw [h]; exact ⟨3 * m, by push_cast; ring⟩)
  have hp3 : p ≠ 3 := fun h => hp6 (by rw [h]; exact ⟨2 * m, by push_cast; ring⟩)
  have hnd : ∀ q : ℕ, q.Prime → q ≠ p → ((q : ℕ) : ZMod p) ≠ 0 := fun q hq hqp h => by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := hnd 2 Nat.prime_two (Ne.symm hp2); exact_mod_cast this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := hnd 3 Nat.prime_three (Ne.symm hp3); exact_mod_cast this
  have hm0 : ((m : ℤ) : ZMod p) ≠ 0 := fun h =>
    hp6 (Dvd.dvd.mul_left ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp h) 6)
  rw [KSplit.LFunction_curve_apply_prime m p hp6, Int.modEq_iff_dvd, sub_sub_cancel]
  exact_mod_cast KSplit.four_dvd_card h2 h3 hm0

/-- **`a_p` is even at a good prime** (tex 9585, 9593–9594). Kind: PROVED, from
`apModFour_curve`: `p` is odd (`2 ∣ M`), so `p + 1`, and hence `a_p`, is even. -/
theorem apEven_curve (m : ℤ) (M : ℕ) (hM : ∀ q : ℕ, q.Prime → q ∣ 6 * m.natAbs → q ∣ M) :
    ∀ p : ℕ, p.Prime → Nat.Coprime p M →
      Even ((ZInQ.Manuscript.curve (m : ℚ)).LFunction p) := by
  intro p hp hpM
  have h4 := Int.modEq_iff_dvd.mp (apModFour_curve m M hM p hp hpM)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hpM
      (hM 2 Nat.prime_two (dvd_mul_of_dvd_left (by norm_num) _))
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  rw [even_iff_two_dvd]
  have h2 : (2 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve (m : ℚ)).LFunction p :=
    dvd_trans ⟨2, by norm_num⟩ h4
  have h2p : (2 : ℤ) ∣ (p : ℤ) + 1 := ⟨k + 1, by rw [hk]; push_cast; ring⟩
  have := dvd_sub h2p h2
  rwa [sub_sub_cancel] at this

/-- **Batch 3's `ApEven` for the curve `E_m`** (the hypothesis `ApEven` of batch 3's
`rulesUpTo_symb`, stated there as GLUE; tex 9585, 9593–9594). Kind: PROVED: for type data whose
conductor `T.m` contains every prime factor of `6m`, every good prime `p` (prime, prime to `T.m`)
has `a_p(E_m)` even. -/
theorem apEven_of {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} (T : TypeData L ε) {m : ℤ}
    (h : ∀ p : ℕ, p.Prime → p ∣ 6 * m.natAbs → p ∣ T.m) :
    ApEven T (fun p => (ZInQ.Manuscript.curve (m : ℚ)).LFunction p) :=
  fun p hp => apEven_curve m T.m h p hp.1 hp.2

/-- Non-vacuity of `apEven_curve` (tex 9585): for `m = 1` and `M = 6` the hypothesis holds, and
the conclusion concerns the good prime `5`. Kind: PROVED. -/
theorem apEven_curve_one_five : Even ((ZInQ.Manuscript.curve ((1 : ℤ) : ℚ)).LFunction 5) :=
  apEven_curve 1 6 (fun q _ hq => by simpa using hq) 5 (by norm_num) (by norm_num)

/-! ### 2. Restriction of a symbol along a homomorphism of alphabets -/

section Restriction

variable {L L' : Type*} [AddCommGroup L] [AddCommGroup L']

/-- **Total types are transported** (tex 2042–2044, 2060–2065): the total type of the restricted
graph is the image of the total type. Kind: PROVED. -/
theorem total_mapType (ι : L' →+ L) (Γ : Config L') : (Γ.mapType ι).total = ι Γ.total := by
  show ∑ v ∈ Γ.V, ι (Γ.t v) = ι (∑ v ∈ Γ.V, Γ.t v)
  exact (map_sum ι _ _).symm

/-- **Restriction commutes with flips** (tex 2119–2122). Kind: PROVED. -/
theorem mapType_flip (ι : L' →+ L) (Γ : Config L') (v w : ℕ) :
    (Γ.flip v w).mapType ι = (Γ.mapType ι).flip v w := rfl

/-- **Restriction commutes with contractions** (tex 2050–2054; tex 2060–2065: the projections
"commute with the product and external-incidence rules"). Kind: PROVED. -/
theorem mapType_contract (ι : L' →+ L) (Γ : Config L') (v w : ℕ) :
    (Γ.contract v w).mapType ι = (Γ.mapType ι).contract v w := by
  refine ForestAux.config_ext rfl ?_ rfl
  funext u
  simp only [Config.mapType, Config.contract]
  by_cases huv : u = v
  · subst huv; simp [map_add]
  · simp [Function.update_of_ne huv]

/-- **Restriction preserves isomorphism of typed graphs** (tex 2102–2110). Kind: PROVED. -/
theorem isIso_mapType (ι : L' →+ L) {Γ Δ : Config L'} (h : Γ.IsIso Δ) :
    (Γ.mapType ι).IsIso (Δ.mapType ι) := by
  obtain ⟨e, ht, hz⟩ := h
  exact ⟨e, fun v => congrArg ι (ht v), hz⟩

/-- **Compatibility for the restricted sign coordinate** `ε ∘ ι` (tex 2037–2041, 2060–2065).
Kind: PROVED. -/
theorem compatible_mapType_iff (ι : L' →+ L) {ε : L →+ ZMod 2} {Γ : Config L'} :
    (Γ.mapType ι).Compatible ε ↔ Γ.Compatible (ε.comp ι) := Iff.rfl

/-- **Restriction of a symbol along a homomorphism of alphabets** (Definition
`ex:sec7-typed-graph`, tex 2023–2024: "Additional fixed splitting conditions restrict us to their
actual realizable types", tex 2060–2065; Lemma `ex:sec7-coefficient-rules`, tex 2102–2136).
Kind: PROVED. If `A` obeys the coefficient rules on `Config L`, then `Γ ↦ A (Γ.mapType ι)` obeys
them on `Config L'` for the restricted sign coordinate `ε ∘ ι`: restriction preserves
compatibility, isomorphism and primary types and commutes with flips and contractions. -/
theorem coefficientRules_comp (ι : L' →+ L) {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (h : CoefficientRules ε A) : CoefficientRules (ε.comp ι) (fun Γ => A (Γ.mapType ι)) :=
  h.mapType ι fun _ => rfl

/-- **Restriction of the rules within one budget** (tex 2023–2024, 2060–2065, 2104–2107;
tex 10533–10538). Kind: PROVED: restriction keeps the vertex set, so the cutoff `W + 1` is
unchanged. -/
theorem rulesUpTo_comp (ι : L' →+ L) {ε : L →+ ZMod 2} {A : Config L → ZMod 2} {W : ℕ}
    (h : RulesUpTo ε A W) : RulesUpTo (ε.comp ι) (fun Γ => A (Γ.mapType ι)) W where
  graph_dependence Γ Δ hc hΓ hiso :=
    h.graph_dependence _ _ hc ((compatible_mapType_iff ι).mpr hΓ) (isIso_mapType ι hiso)
  contraction Γ hc hΓ v hv w hw hvw := by
    show A (Γ.mapType ι) + A ((Γ.flip v w).mapType ι) = A ((Γ.contract v w).mapType ι)
    rw [mapType_flip, mapType_contract]
    exact h.contraction _ hc ((compatible_mapType_iff ι).mpr hΓ) v hv w hw hvw
  primary_isolation Γ hc hΓ v hv ht hz :=
    h.primary_isolation _ hc ((compatible_mapType_iff ι).mpr hΓ) v hv
      (show ι (Γ.t v) = 0 by rw [ht, map_zero]) hz

/-- **Unit seeds of the restricted symbol** (tex 2177, 2060–2065): exactly the graphs whose
restriction is a unit seed. Kind: PROVED. -/
theorem isUnitSeed_comp_iff (ι : L' →+ L) {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    {Γ : Config L'} :
    IsUnitSeed (ε.comp ι) (fun Δ => A (Δ.mapType ι)) Γ ↔ IsUnitSeed ε A (Γ.mapType ι) :=
  Iff.rfl

/-- **A unit seed of the restricted symbol restricts to a unit seed** (tex 2177, 2060–2065).
Kind: PROVED. -/
theorem isUnitSeed_comp (ι : L' →+ L) {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    {Γ : Config L'} (h : IsUnitSeed (ε.comp ι) (fun Δ => A (Δ.mapType ι)) Γ) :
    IsUnitSeed ε A (Γ.mapType ι) :=
  (isUnitSeed_comp_iff ι).mp h

/-- **Filter transport** (tex 2042–2044, 2079, 2060–2065): if every unit seed of `A` has total
type `τ`, every unit seed of the restricted symbol has total type mapping to `τ`. Kind: PROVED. -/
theorem total_of_isUnitSeed_comp (ι : L' →+ L) {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    {τ : L} (hfilt : ∀ Γ : Config L, IsUnitSeed ε A Γ → Γ.total = τ) {Γ : Config L'}
    (h : IsUnitSeed (ε.comp ι) (fun Δ => A (Δ.mapType ι)) Γ) : ι Γ.total = τ := by
  rw [← total_mapType]
  exact hfilt _ (isUnitSeed_comp ι h)

/-- **Filter transport along an inclusion** (tex 2023–2024, 2042–2044, 2079): for injective `ι`
(a subgroup of realizable types), a total-zero filter for `A` gives a total-zero filter for the
restricted symbol. Kind: PROVED. -/
theorem total_eq_zero_of_isUnitSeed_comp (ι : L' →+ L) (hι : Function.Injective ι)
    {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hfilt : ∀ Γ : Config L, IsUnitSeed ε A Γ → Γ.total = 0) {Γ : Config L'}
    (h : IsUnitSeed (ε.comp ι) (fun Δ => A (Δ.mapType ι)) Γ) : Γ.total = 0 :=
  (injective_iff_map_eq_zero ι).mp hι _ (total_of_isUnitSeed_comp ι hfilt h)

end Restriction

/-! ### 3. The stage symbol -/

section Stage

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- In `𝔽₂` a value other than one is zero (tex 2071–2077: the two cases of the symbol).
Kind: PROVED (helper). -/
private theorem zmod2_eq_zero_of_ne_one : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide

open Classical in
/-- **The stage symbol** (Definition `ex:sec7-symbol`, tex 2068–2100; App F "Reading an added
vertex", tex 9670–9704: the normalized valuation symbol `𝒜` is read on the tested range of one
valid actual stage). Kind: definition. For type data `T` and a reading `R` of finite sets of
primes (the symbol at the Fourier index `∏ p`), `stageSymbol T R Γ` is one exactly when the typed
graph `Γ` has a prime realization and every prime realization of `Γ` reads one, and zero
otherwise. -/
noncomputable def stageSymbol (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (Γ : Config L) :
    ZMod 2 :=
  if (∃ f, IsReal T Γ f) ∧ ∀ f, IsReal T Γ f → R (Γ.V.image f) = 1 then 1 else 0

/-- **When the stage symbol is one** (tex 2068–2079, 9670–9704): a realized graph whose every
prime realization reads one. Kind: PROVED. -/
theorem stageSymbol_eq_one_iff (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (Γ : Config L) :
    stageSymbol T R Γ = 1 ↔ (∃ f, IsReal T Γ f) ∧ ∀ f, IsReal T Γ f → R (Γ.V.image f) = 1 := by
  unfold stageSymbol
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 zero_ne_one, fun h' => absurd h' h⟩

/-- **A unit of the stage symbol is read by every realization** (tex 9670–9704). Kind: PROVED. -/
theorem stageSymbol_reads {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {Γ : Config L}
    (h : stageSymbol T R Γ = 1) {f : ℕ → ℕ} (hf : IsReal T Γ f) : R (Γ.V.image f) = 1 :=
  ((stageSymbol_eq_one_iff T R Γ).mp h).2 f hf

/-- **A unit of the stage symbol is realized by primes** (tex 2031–2034, 2068–2079). Kind:
PROVED. -/
theorem stageSymbol_realized {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {Γ : Config L}
    (h : stageSymbol T R Γ = 1) : ∃ f, IsReal T Γ f :=
  ((stageSymbol_eq_one_iff T R Γ).mp h).1

/-- **Within the factorization budget, the stage symbol is the reading of any realization**
(tex 9955–9974; batch 3's `reading_eq_of_real`). Kind: PROVED. -/
theorem stageSymbol_eq_reading (T : TypeData L ε) (R : Finset ℕ → ZMod 2) {B : ℕ}
    (hswap : FixedUFactorization T R B) {Γ : Config L} (hΓ : Γ.Compatible ε)
    (hB : Γ.V.card ≤ B) {f : ℕ → ℕ} (hf : IsReal T Γ f) :
    stageSymbol T R Γ = R (Γ.V.image f) := by
  unfold stageSymbol
  split_ifs with h
  · exact (h.2 f hf).symm
  · by_cases h1 : R (Γ.V.image f) = 1
    · exact absurd ⟨⟨f, hf⟩, fun g hg => (reading_eq_of_real T R hswap hΓ hB hg hf).trans h1⟩ h
    · exact (zmod2_eq_zero_of_ne_one _ h1).symm

/-- **The stage symbol is batch 3's symbol within the budget** (tex 2093–2096, 9955–9974; batch
3's `exists_real`, `reading_eq_of_real`, `symb_eq`). Kind: PROVED. -/
theorem stageSymbol_eq_symb (T : TypeData L ε) (R : Finset ℕ → ZMod 2) {B : ℕ}
    (hswap : FixedUFactorization T R B) {Γ : Config L} (hΓ : Γ.Compatible ε)
    (hB : Γ.V.card ≤ B) : stageSymbol T R Γ = symb T R Γ := by
  obtain ⟨f, hf⟩ := exists_real T hΓ
  rw [stageSymbol_eq_reading T R hswap hΓ hB hf, symb_eq T R hswap hΓ hB hf]

/-- **The coefficient rules for the stage symbol within one budget** (Lemma
`ex:sec7-coefficient-rules`, tex 2104–2107: "At an odd stage a rule is asserted only when all its
inputs, outputs and coefficient divisions lie in the chosen finite budget"; Proposition
`ex:app-odd-stabilization`, tex 10533–10538). Kind: PROVED, from batch 3's `rulesUpTo_symb` and
`stageSymbol_eq_symb` on every graph a rule evaluates: isomorphic graphs (same size,
compatibility transported), flips (`flip_compatible`, same vertices) and contractions
(`contract_compatible`, one vertex fewer). -/
theorem rulesUpTo_stageSymbol (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (W : ℕ)
    (hswap : FixedUFactorization T R (W + 1)) (hO12 : O12Reading T R ap (W + 1))
    (hap : ApEven T ap) (hprim : PrimaryReading T R (W + 1)) :
    RulesUpTo ε (stageSymbol T R) W := by
  have hs := rulesUpTo_symb T R ap W hswap hO12 hap hprim
  refine ⟨fun Γ Δ hB hΓ hiso => ?_, fun Γ hB hΓ v hv w hw hvw => ?_,
    fun Γ hB hΓ v hv ht hz => ?_⟩
  · have hΔ : Δ.Compatible ε := ForestAux.compatible_of_iso hiso hΓ
    have hΔB : Δ.V.card ≤ W + 1 := (ForestAux.card_eq_of_iso hiso).symm.le.trans hB
    rw [stageSymbol_eq_symb T R hswap hΓ hB, stageSymbol_eq_symb T R hswap hΔ hΔB]
    exact hs.graph_dependence Γ Δ hB hΓ hiso
  · have hct : (Γ.contract v w).V.card ≤ W + 1 := by
      show (Γ.V.erase w).card ≤ W + 1
      exact card_erase_le.trans hB
    rw [stageSymbol_eq_symb T R hswap hΓ hB,
      stageSymbol_eq_symb T R hswap (flip_compatible hΓ v w) hB,
      stageSymbol_eq_symb T R hswap (ForestAux.contract_compatible hΓ hv hw) hct]
    exact hs.contraction Γ hB hΓ v hv w hw hvw
  · rw [stageSymbol_eq_symb T R hswap hΓ hB]
    exact hs.primary_isolation Γ hB hΓ v hv ht hz

/-- **The coefficient rules for the stage symbol** (Lemma `ex:sec7-coefficient-rules`, tex
2102–2149; App F `ex:app-coefficient-rules`, tex 9884–9976). Kind: PROVED, from the readings at
every budget (the even source) via batch 3's `coefficientRules_symb` and `stageSymbol_eq_symb`
(each graph within the budget of its own size). -/
theorem coefficientRules_stageSymbol (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ)
    (hswap : ∀ B, FixedUFactorization T R B) (hO12 : ∀ B, O12Reading T R ap B)
    (hap : ApEven T ap) (hprim : ∀ B, PrimaryReading T R B) :
    CoefficientRules ε (stageSymbol T R) := by
  have hs := coefficientRules_symb T R ap hswap hO12 hap hprim
  have he : ∀ Γ : Config L, Γ.Compatible ε → stageSymbol T R Γ = symb T R Γ :=
    fun Γ hΓ => stageSymbol_eq_symb T R (hswap Γ.V.card) hΓ le_rfl
  refine ⟨fun Γ Δ hΓ hiso => ?_, fun Γ hΓ v hv w hw hvw => ?_, fun Γ hΓ v hv ht hz => ?_⟩
  · rw [he Γ hΓ, he Δ (ForestAux.compatible_of_iso hiso hΓ)]
    exact hs.graph_dependence Γ Δ hΓ hiso
  · rw [he Γ hΓ, he _ (flip_compatible hΓ v w), he _ (ForestAux.contract_compatible hΓ hv hw)]
    exact hs.contraction Γ hΓ v hv w hw hvw
  · rw [he Γ hΓ]
    exact hs.primary_isolation Γ hΓ v hv ht hz

end Stage

end ZInQ.Manuscript.RC.AddressGenuine

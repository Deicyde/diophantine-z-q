import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Dictionary
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.NonVacuity

/-!
# Theorem 5.3, Lane RC0: the partitionable auxiliary factor from the dictionary

The leaf `PreLeaves.aux_factor` (App G, Proposition `ex:app-rough-companion`, tex 10055–10150; the
input `hdummy` of lane RC13's `roughCompanion`, tex 2343–2401) is `AuxFactorInputs W`: the
specifications of the data on which the dictionary argument (batch 3's, adapted here to the
prepared types) proves `AuxFactor W A₀`. They are, with tex lines and kinds:

1. the type data `T` of the coefficient dictionary over a finite elementary two-group `𝓛`
   (definition + GLUE; Definition `ex:sec7-typed-graph`, tex 2015–2044, and the proof of Lemma
   `ex:sec7-realization`, tex 2162–2168): the type of a prime is read from its reduced residue class
   modulo a conductor `m` with `2 ∣ m`, and the sign coordinate of the type is `(p − 1)/2 mod 2`;
2. the type conductor is supported on the fixed support `S` (definition; tex 2016–2020: types are
   read by characters at the fixed support, which contains two);
3. one even source `A τ` for every total type `τ` (finitely many: `𝓛` is finite; tex
   10131–10132), with
   * the coefficient rules (ELLIOT; Lemma `ex:sec7-coefficient-rules`, tex 2102–2136, realized in
     App F, Proposition `ex:app-coefficient-rules`, tex 9447–9976);
   * zero off its filter (definition; Definition `ex:sec7-symbol`, tex 2068–2079);
   * at every **prepared** total type (`PreparedType`: the total type of a negative squarefree
     `d ≡ 1 (mod 8)` prime to the support with `L(E^{(d)},1) ≠ 0`, the types of the companions
     `hk'` actually produced, tex 10096–10098, 10131–10132), a unit seed (ELLIOT; tex 10131–10132:
     "Prepare these sources and nonempty seeds for every total type at the fixed support"). Prepared
     types are negative (`ε τ = 1`, `preparedType_eps`), so their unit seeds are nonempty (tex
     10089–10091);
4. the meaning of `W.Partitionable` on the filter (definition; Definition `ex:sec7-seed-partition`,
   tex 2181–2185, 2296–2297, read through the dictionary, tex 2031–2044): a negative squarefree `d`
   prime to the support whose typed graph of primes is a partitionable list for the source of its
   total type is partitionable. Only this direction is required.

`auxFactor_of_inputs : SupportSpec W → AuxFactorInputs W → ∃ A₀, AuxFactor W A₀` (PROVED) is the
dictionary argument with dummies only for the prepared types: one dummy for each anchor of a minimum
seed of every prepared total type plus one reserve, realized after `h` and the exclusions by
distinct primes in prescribed reduced residue classes (CRT and Dirichlet, batch 3's
`dummy_realization`), the anchors matched by RC2's `partitionable_of_anchors` (tex 10096–10105,
10131–10139). The total type of `h(au)` is prepared: `h` is a prepared parameter (positive,
squarefree, `≡ 1 (mod 8)`, prime to the support; tex 2344–2346, 10059–10061), and `au` is a
companion with `L(E^{(h·au)},1) ≠ 0`. `SupportSpec W` comes from the data specification
(`preFields_of_dataSpec`); of it only "the support consists of primes" and `2 ∈ S` are used.

The restrictions to the filter (clause 4, the negative squarefree `d` prime to the support; the
prepared `h`; the prepared types) are the text's: the earlier form, which read only the prime set of
`|d|` and quantified over every `h > 0` and every total type, forced `Partitionable` at `d³`, `q²d`
and `−d` and asked for unit seeds at types of root number `−1`, and was inconsistent with the cube
clause of the even upper bound.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- **A prepared total type** (tex 10096–10098, 10131–10132): the total type (for the dictionary's
type data `T`) of the typed graph of the primes of a negative squarefree `d ≡ 1 (mod 8)` prime to
the support with `L(E^{(d)},1) ≠ 0`, i.e. the type of a companion `hk'` actually produced. -/
def PreparedType {ℓ : ℕ} (W : WData ℓ) {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
    (T : CoefficientDictionary.TypeData L ε) (τ : L) : Prop :=
  ∃ d : ℤ, d < 0 ∧ d % 8 = 1 ∧ Squarefree d ∧ (∀ p ∈ W.S, ¬ (p : ℤ) ∣ d) ∧
    AnalyticRank (Etw ℓ d) 0 ∧ (Symbols.primeConfig d.natAbs.primeFactors T.typ).total = τ

/-- **The inputs of the partitionable auxiliary factor** (App G, proof of
`ex:app-rough-companion`, tex 10096–10105, 10131–10139), as specifications of the data `W`: a
finite elementary two-group `𝓛` of types (`Fintype`: "There are finitely many", tex 10132) with
sign coordinate `ε`, the dictionary's type data `T` (definition + GLUE: types read from reduced
residue classes, the sign coordinate; tex 2015–2044, 2162–2168; owner batch 3
CoefficientDictionary), and one even source `A τ` for each total type `τ`, such that
1. the type conductor `T.m` is supported on `W.S` (definition: the types are read at the fixed
   support, tex 2016–2020; owner RC0, construction of the data);
2. each `A τ` satisfies the coefficient rules (ELLIOT; Lemma `ex:sec7-coefficient-rules`, tex
   2102–2136, realized in App F, tex 9447–9976; owner RC2 with batch 3 CoefficientDictionary);
3. each `A τ` is zero off its filter `τ` (definition; tex 2068–2079; owner RC2);
4. each prepared total type `τ` has a unit seed for `A τ` (ELLIOT; tex 10131–10132; nonemptiness
   is automatic for these negative types, tex 10089–10098; owner RC2 / batch 3 AuxFactor);
5. a negative squarefree `d` prime to the support whose typed graph of primes is a partitionable
   list for the source of its total type satisfies `W.Partitionable d` (definition; Definition
   `ex:sec7-seed-partition`, tex 2181–2185, 2296–2297, with the dictionary, tex 2031–2044; a
   requirement on the construction of `W`, owner RC0). -/
def AuxFactorInputs {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (L : Type) (_ : AddCommGroup L) (_ : Fintype L) (ε : L →+ ZMod 2)
    (T : CoefficientDictionary.TypeData L ε) (A : L → Symbols.Config L → ZMod 2),
    (∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S) ∧
    (∀ τ : L, Symbols.CoefficientRules ε (A τ)) ∧
    (∀ τ : L, Symbols.VanishesOffFilter (A τ) τ) ∧
    (∀ τ : L, PreparedType W T τ → ∃ Γ : Symbols.Config L, Symbols.IsUnitSeed ε (A τ) Γ) ∧
    ∀ d : ℤ, d < 0 → Squarefree d → (∀ p ∈ W.S, ¬ (p : ℤ) ∣ d) →
      Symbols.IsPartitionable ε (A (Symbols.primeConfig d.natAbs.primeFactors T.typ).total)
        (Symbols.primeConfig d.natAbs.primeFactors T.typ) → W.Partitionable d

/-! ## The sign coordinate of a prepared type -/

/-- `n ↦ ⌊n/2⌋ mod 2` is additive on odd numbers (PROVED). -/
theorem half_mul_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    (((a * b) / 2 : ℕ) : ZMod 2) = ((a / 2 : ℕ) : ZMod 2) + ((b / 2 : ℕ) : ZMod 2) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have h1 : (2 * x + 1) * (2 * y + 1) = 1 + 2 * (2 * x * y + x + y) := by ring
  have h2 : (2 * x + 1) / 2 = x := by omega
  have h3 : (2 * y + 1) / 2 = y := by omega
  rw [h1, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), h2, h3]
  have h22 : (2 : ZMod 2) = 0 := rfl
  push_cast
  rw [h22]
  simp

/-- `⌊n/2⌋ mod 2` of a product of odd numbers is the sum of the factors' (PROVED). -/
theorem half_prod_odd (V : Finset ℕ) (hV : ∀ p ∈ V, Odd p) :
    (((∏ p ∈ V, p) / 2 : ℕ) : ZMod 2) = ∑ p ∈ V, ((p / 2 : ℕ) : ZMod 2) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | insert a V ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hVo : ∀ p ∈ V, Odd p := fun p hp => hV p (Finset.mem_insert_of_mem hp)
    have hprod : Odd (∏ p ∈ V, p) :=
      Finset.prod_induction _ Odd (fun _ _ hx hy => hx.mul hy) odd_one hVo
    rw [half_mul_odd (hV a (Finset.mem_insert_self a V)) hprod, ih hVo]

/-- **A prepared total type is negative** (PROVED): if `d < 0` is squarefree, `≡ 1 (mod 8)` and
prime to the type conductor, the sign coordinate of the total type of its primes is `1` (an odd
number of prime factors `≡ 3 (mod 4)`), so the total type is nonzero. -/
theorem total_ne_zero_of_neg {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
    (T : CoefficientDictionary.TypeData L ε) {d : ℤ} (hd : d < 0) (h8 : d % 8 = 1)
    (hsf : Squarefree d) (hgood : ∀ p ∈ d.natAbs.primeFactors, Nat.Coprime p T.m) :
    (Symbols.primeConfig d.natAbs.primeFactors T.typ).total ≠ 0 := by
  intro h0
  set V := d.natAbs.primeFactors with hV
  have hεt : ε (Symbols.primeConfig V T.typ).total = ∑ p ∈ V, ((p / 2 : ℕ) : ZMod 2) := by
    show ε (∑ v ∈ V, T.typ v) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact T.sign p (Nat.prime_of_mem_primeFactors hp) (hgood p hp)
  have hodd : ∀ p ∈ V, Odd p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    rcases hp'.eq_two_or_odd' with h2 | ho
    · exfalso
      have h2d : (2 : ℤ) ∣ d := by
        have := Nat.dvd_of_mem_primeFactors hp
        rw [h2] at this
        exact Int.natCast_dvd.mpr this
      omega
    · exact ho
  have hprod : ∏ p ∈ V, p = d.natAbs :=
    Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hsf)
  have habs : (d.natAbs : ℤ) = -d := by
    rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by omega)
  have h7 : d.natAbs % 8 = 7 := by omega
  have hhalf : ((d.natAbs / 2 : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, show d.natAbs / 2 % 2 = 1 by omega]
    rfl
  rw [← half_prod_odd V hodd, hprod, hhalf, h0, map_zero] at hεt
  exact zero_ne_one hεt

/-! ## The dictionary argument at the prepared types -/

open ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
  ZInQ.Contrib.CloudB3RC53.AuxFactor Finset in
/-- **`AuxFactor` from the dictionary, with dummies only for the prepared types** (tex
10089–10098, 10131–10139; the argument of batch 3's `auxFactor_of_dictionary` restricted to the
types of the companions actually produced). PROVED. -/
theorem auxFactor_of_prepared {ℓ : ℕ} (W : WData ℓ) (hS : ∀ p ∈ W.S, p.Prime) (hS2 : 2 ∈ W.S)
    {L : Type} [AddCommGroup L] [Fintype L] {ε : L →+ ZMod 2} (T : TypeData L ε)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ, CoefficientRules ε (A τ))
    (hoff : ∀ τ, VanishesOffFilter (A τ) τ)
    (hseed : ∀ τ, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ)
    (hspec : ∀ d : ℤ, d < 0 → Squarefree d → (∀ p ∈ W.S, ¬ (p : ℤ) ∣ d) →
      IsPartitionable ε (A (primeConfig d.natAbs.primeFactors T.typ).total)
        (primeConfig d.natAbs.primeFactors T.typ) → W.Partitionable d) :
    ∃ A₀ : ℕ, AuxFactor W A₀ := by
  classical
  -- primes prime to the support are prime to the type conductor
  have hcopS : ∀ p : ℕ, p.Prime → p ∉ W.S → Nat.Coprime p T.m := fun p hp hpS =>
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hpm => hpS (hmS p hp hpm)
  -- a prepared type is nonzero, so its unit seeds are nonempty; minimum seeds and a vertex
  have hmin : ∀ τ, PreparedType W T τ → ∃ Γ₀ : Config L, IsMinSeed ε (A τ) Γ₀ := by
    intro τ hτ
    obtain ⟨Γ, hΓ⟩ := hseed τ hτ
    obtain ⟨d, hd, h8, hsf, hdS, -, rfl⟩ := hτ
    have hne : (primeConfig d.natAbs.primeFactors T.typ).total ≠ 0 := by
      refine total_ne_zero_of_neg T hd h8 hsf fun p hp => hcopS p (Nat.prime_of_mem_primeFactors hp)
        fun hpS => hdS p hpS ?_
      exact Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    exact exists_minSeed ⟨Γ, hΓ, negative_unitSeed_nonempty (hoff _) hne hΓ⟩
  haveI : Nonempty (Config L) := ⟨⟨∅, fun _ => 0, fun _ _ => 0⟩⟩
  choose! Γ₀ hΓ₀ using hmin
  have hsv : ∀ τ, PreparedType W T τ → ∃ v, v ∈ (Γ₀ τ).V := fun τ hτ => (hΓ₀ τ hτ).2.1
  choose! s hs using hsv
  -- the dummy supply: one dummy per anchor of every prepared seed, plus a reserve
  let P : Finset (Σ _ : L, ℕ) := (univ.filter fun τ => PreparedType W T τ).sigma
    fun τ => (Γ₀ τ).V.erase (s τ)
  let e : P ≃ Fin P.card := P.equivFin
  let A₀ := P.card + 1
  choose cl hcl htyp using fun ℓ' : L => T.classes ℓ'
  let tyOf : ℕ → L := fun i =>
    if h : i < P.card then (Γ₀ (e.symm ⟨i, h⟩).1.1).t (e.symm ⟨i, h⟩).1.2 else 0
  let cls : ℕ → ZMod T.m := fun i => cl (tyOf i)
  refine ⟨A₀, fun h hh0 hhsf hh8 hhS X hX => ?_⟩
  obtain ⟨q, hqinj, hq, ha0, hasf, haω, haSX, hah⟩ :=
    dummy_realization T.m T.m_pos T.two_dvd A₀ cls (fun i => hcl _) W.S X h
  set a : ℤ := ∏ i ∈ range A₀, (q i : ℤ) with ha
  refine ⟨a, ha0, hasf, haω, fun p hp => ?_, hah hh0.ne', fun u hu h8 hsfu hsq hcn => ?_⟩
  · rcases mem_union.mp hp with hp' | hp'
    · exact haSX p hp (hS p hp')
    · exact haSX p hp (hX p hp')
  -- the typed graph of `d = h k'`
  set d : ℤ := h * (a * u) with hd
  have hau0 : a * u ≠ 0 := fun h0 => by rw [h0] at hu; exact lt_irrefl 0 hu
  have hd0 : d ≠ 0 := mul_ne_zero hh0.ne' hau0
  set V := d.natAbs.primeFactors with hV
  have hmemV : ∀ p, p ∈ V ↔ p.Prime ∧ (p : ℤ) ∣ d := fun p => by
    rw [hV, Nat.mem_primeFactors, ← Int.natCast_dvd]
    exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, Int.natAbs_ne_zero.mpr hd0⟩⟩
  -- `d` is negative, `≡ 1 (mod 8)`, squarefree and prime to the support
  have hdneg : d < 0 := mul_neg_of_pos_of_neg hh0 hu
  have hd8 : d % 8 = 1 := by
    rw [hd, Int.mul_emod, hh8, h8]; rfl
  have hdS : ∀ p ∈ W.S, ¬ (p : ℤ) ∣ d := by
    intro p hpS hpd
    rcases (Int.Prime.dvd_mul' (hS p hpS) hpd) with hph | hpau
    · exact hhS p hpS hph
    · exact not_dvd_of_isSquareAt (hS p hpS) hsfu (hsq p (mem_union_left _ hpS)) hpau
  have hcop : IsCoprime h (a * u) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have hph : (p : ℤ) ∣ h := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_left _ _)
    have hpk : (p : ℤ) ∣ a * u :=
      (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_right _ _)
    have hmem : p ∈ W.S ∪ h.natAbs.primeFactors := mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hph, Int.natAbs_ne_zero.mpr hh0.ne'⟩)
    exact not_dvd_of_isSquareAt hp hsfu (hsq p hmem) hpk
  have hdsf : Squarefree d :=
    (squarefree_mul_iff.mpr ⟨hcop.isRelPrime, hhsf, hsfu⟩)
  -- no prime of `d` lies in the support
  have hnotS : ∀ p ∈ V, p ∉ W.S := fun p hpV hpS => hdS p hpS ((hmemV p).mp hpV).2
  have hgood : ∀ p ∈ V, T.Good p ∧ p ≠ 2 := by
    intro p hpV
    have hp := ((hmemV p).mp hpV).1
    exact ⟨⟨hp, hcopS p hp (hnotS p hpV)⟩, fun h2 => hnotS p hpV (h2 ▸ hS2)⟩
  set Γ := primeConfig V T.typ with hΓdef
  have hΓ : Γ.Compatible ε := primeConfig_compatible ε V (fun p hp => ⟨(hgood p hp).1.1,
    (hgood p hp).2⟩) T.typ fun p hp => T.sign p (hgood p hp).1.1 (hgood p hp).1.2
  set τ := Γ.total
  -- the total type of `d` is prepared
  have hτ : PreparedType W T τ := ⟨d, hdneg, hd8, hdsf, hdS, hcn, rfl⟩
  -- the dummies lie in `V`
  have hqV : ∀ i < A₀, q i ∈ V := by
    intro i hi
    refine (hmemV _).mpr ⟨(hq i hi).1, ?_⟩
    have : (q i : ℤ) ∣ a := ha ▸ Finset.dvd_prod_of_mem _ (mem_range.mpr hi)
    exact (this.trans (dvd_mul_right a u)).trans (dvd_mul_left _ h)
  -- the anchors of the seed of `τ`
  have hmemP : ∀ v ∈ (Γ₀ τ).V.erase (s τ), (⟨τ, v⟩ : Σ _ : L, ℕ) ∈ P := fun v hv =>
    mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hτ⟩, hv⟩
  let idx : ℕ → ℕ := fun v => if hv : v ∈ (Γ₀ τ).V.erase (s τ) then (e ⟨⟨τ, v⟩, hmemP v hv⟩ : ℕ)
    else 0
  have hidx_lt : ∀ v ∈ (Γ₀ τ).V.erase (s τ), idx v < P.card := fun v hv => by
    show (if hv : v ∈ (Γ₀ τ).V.erase (s τ) then (e ⟨⟨τ, v⟩, hmemP v hv⟩ : ℕ) else 0) < P.card
    rw [dif_pos hv]; exact (e _).2
  let anc : ℕ → ℕ := fun v => q (idx v)
  have hidx_inj : Set.InjOn idx ((Γ₀ τ).V.erase (s τ) : Set ℕ) := by
    intro v hv w hw hvw
    change (if hv : v ∈ (Γ₀ τ).V.erase (s τ) then (e ⟨⟨τ, v⟩, hmemP v hv⟩ : ℕ) else 0) =
      (if hw : w ∈ (Γ₀ τ).V.erase (s τ) then (e ⟨⟨τ, w⟩, hmemP w hw⟩ : ℕ) else 0) at hvw
    rw [dif_pos (Finset.mem_coe.mp hv), dif_pos (Finset.mem_coe.mp hw)] at hvw
    have := e.injective (Fin.ext hvw)
    simpa using congrArg (fun x : P => x.1.2) this
  have hanc_inj : Set.InjOn anc ((Γ₀ τ).V.erase (s τ) : Set ℕ) := by
    intro v hv w hw hvw
    refine hidx_inj hv hw (hqinj _ ?_ _ ?_ hvw)
    · exact Nat.lt_succ_of_lt (hidx_lt v hv)
    · exact Nat.lt_succ_of_lt (hidx_lt w hw)
  have hancV : ∀ v ∈ (Γ₀ τ).V.erase (s τ), anc v ∈ Γ.V := fun v hv =>
    hqV _ (Nat.lt_succ_of_lt (hidx_lt v hv))
  have hanct : ∀ v ∈ (Γ₀ τ).V.erase (s τ), Γ.t (anc v) = (Γ₀ τ).t v := by
    intro v hv
    have hlt := hidx_lt v hv
    have hc := (hq (idx v) (Nat.lt_succ_of_lt hlt)).2.2.2.2
    show T.typ (q (idx v)) = (Γ₀ τ).t v
    rw [htyp _ _ (hq _ (Nat.lt_succ_of_lt hlt)).1 hc]
    simp only [tyOf, dif_pos hlt]
    have he : e.symm ⟨idx v, hlt⟩ = ⟨⟨τ, v⟩, hmemP v hv⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply]
      ext
      show (if hv : v ∈ (Γ₀ τ).V.erase (s τ) then (e ⟨⟨τ, v⟩, hmemP v hv⟩ : ℕ) else 0) = _
      rw [dif_pos hv]
    rw [he]
  -- the reserve lies in the remainder
  have hrem : (Γ.V \ ((Γ₀ τ).V.erase (s τ)).image anc).Nonempty := by
    refine ⟨q P.card, mem_sdiff.mpr ⟨hqV _ (Nat.lt_succ_self _), fun hm => ?_⟩⟩
    obtain ⟨v, hv, hvq⟩ := mem_image.mp hm
    have := hqinj _ (Nat.lt_succ_of_lt (hidx_lt v hv)) _ (Nat.lt_succ_self _) hvq
    exact absurd this (Nat.ne_of_lt (hidx_lt v hv))
  have htot : Γ.total = (Γ₀ τ).total := (hoff τ (Γ₀ τ) (hΓ₀ τ hτ).1.2).symm
  have hpart := partitionable_of_anchors (hA τ) (hΓ₀ τ hτ) hΓ htot (s τ) (hs τ hτ) anc hanc_inj
    hancV hanct hrem
  exact hspec d hdneg hdsf hdS hpart

/-- **The partitionable auxiliary factor** (App G, `ex:app-rough-companion`, tex 10055–10150;
PROVED from `SupportSpec W` and `AuxFactorInputs W` by `auxFactor_of_prepared`). -/
theorem auxFactor_of_inputs {ℓ : ℕ} (W : WData ℓ) (hS : SupportSpec W)
    (h : AuxFactorInputs W) : ∃ A₀ : ℕ, AuxFactor W A₀ := by
  obtain ⟨L, iL, fL, ε, T, A, hmS, hA, hoff, hseed, hspec⟩ := h
  exact @auxFactor_of_prepared ℓ W hS.1 hS.2.1 L iL fL ε T hmS A hA hoff hseed hspec

/-! ## Non-vacuity -/

/-- **The leaf does not involve `h_*`** (PROVED): it reads only the support and `Partitionable`,
so it is unchanged when RC0 substitutes the genus partner (`WData.withHstar`). -/
theorem auxFactorInputs_hstar {ℓ : ℕ} (W : WData ℓ) (h : ℤ) (hA : AuxFactorInputs W) :
    AuxFactorInputs ({ W with hstar := h } : WData ℓ) :=
  hA

/-- The zero symbol satisfies the coefficient rules for every sign coordinate (PROVED). -/
theorem coefficientRules_zero {L : Type} [AddCommGroup L] (ε : L →+ ZMod 2) :
    Symbols.CoefficientRules ε (fun _ => (0 : ZMod 2)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ => rfl⟩

/-- **Every clause but the prepared seeds is satisfiable** (PROVED): for every `W` with
`SupportSpec W`, batch 3's sign type data (`𝓛 = ZMod 2`, conductor `4`) and the zero symbol
satisfy clauses 1, 2, 3 and 5 of `AuxFactorInputs` (clause 5 vacuously: no list is partitionable
for the zero symbol). The seed clause 4 fails for the zero symbol, which has no unit; it carries,
with its coupling to `W.Partitionable` through clause 5, the content of the leaf. -/
theorem auxFactorInputs_clauses_but_seeds {ℓ : ℕ} (W : WData ℓ) (hS : SupportSpec W) :
    (∀ p : ℕ, p.Prime → p ∣ CoefficientDictionary.signTypeData.m → p ∈ W.S) ∧
    (∀ _τ : ZMod 2, Symbols.CoefficientRules (AddMonoidHom.id (ZMod 2))
      (fun _ : Symbols.Config (ZMod 2) => (0 : ZMod 2))) ∧
    (∀ τ : ZMod 2, Symbols.VanishesOffFilter (fun _ : Symbols.Config (ZMod 2) => (0 : ZMod 2)) τ) ∧
    ∀ d : ℤ, d < 0 → Squarefree d → (∀ p ∈ W.S, ¬ (p : ℤ) ∣ d) →
      Symbols.IsPartitionable (AddMonoidHom.id (ZMod 2))
        (fun _ : Symbols.Config (ZMod 2) => (0 : ZMod 2))
        (Symbols.primeConfig d.natAbs.primeFactors CoefficientDictionary.signTypeData.typ) →
      W.Partitionable d := by
  refine ⟨fun p hp hpm => ?_, fun _ => coefficientRules_zero _, fun _ Γ h => ?_,
    fun d _ _ _ hpart => ?_⟩
  · have hm : CoefficientDictionary.signTypeData.m = 2 ^ 2 := rfl
    rw [hm] at hpm
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpm)
    rw [hp2]
    exact hS.2.1
  · exact absurd h zero_ne_one
  · obtain ⟨_, _, _, h1⟩ := hpart
    exact absurd h1 zero_ne_one

end ZInQ.Manuscript.RC.Wiring

import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Wiring
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Rules

/-!
# AuxFactor, part 5: `hDict` from the coefficient dictionary — RC0's `AuxFactor` leaf

Manuscript `diophantine_zq.tex`, App G, proof of Proposition `ex:app-rough-companion`, tex
10089–10098 and 10131–10139: "For the negative types used in the rough companion … every unit seed
is nonempty. A seed of least positive size has no dependence on internal edge bits … If a list
with the same total label contains the first `r − 1` seed anchors and a nonempty remainder,
contract that remainder into the last anchor … Prepare these sources and nonempty seeds for every
total type at the fixed support. There are finitely many. A bounded supply of dummy anchors and
reserves works for all of them. For each `h` realize that supply by distinct primes avoiding the
entire fixed support and `h` … For the total type that actually occurs, `hk'` is partitionable."

`auxFactor_of_dictionary` (`PROVED`) produces RC0's leaf `Wiring.AuxFactor W A₀` (for an explicit
`A₀`: one dummy per anchor of every prepared seed, plus one reserve) from:

* the type data `T` of the coefficient dictionary (`CoefficientDictionary.TypeData`: types read
  from residue classes, the sign coordinate);
* the prepared even sources `A τ`, one for each total type `τ` (finitely many: `Fintype L`), with
  RC2's coefficient rules (`hA`), vanishing off their filter (`hoff`), and a prepared unit seed
  (`hseed`), nonempty when the type is not negative (for negative types, `ε τ = 1`, nonemptiness is
  automatic: `negative_unitSeed_nonempty`);
* `hspec` — the meaning of `W.Partitionable` (Definition `ex:sec7-seed-partition`, tex
  2144–2185, read through the dictionary): `d` is partitionable when the typed graph of its primes
  (`primeConfig`, RC2) is a partitionable list for the source of its total type;
* `hmS` — the type conductor is supported on `S` (the types live at the fixed support), and
  `SupportSpec` (`hS`, `hS2`).

The arithmetic of the realization (CRT and Dirichlet) is RC2's `finite_realization_nat`, through
`dummy_realization`; the combinatorics is RC2's `partitionable_of_anchors` with the minimum seeds
of `exists_minSeed`.
-/

namespace ZInQ.Contrib.CloudB3RC53.AuxFactor

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Symbols
  ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

/-- A square of `ℚ_p` has even valuation, so a squarefree integer that is a square at `p` is prime
to `p`. `PROVED`. -/
theorem not_dvd_of_isSquareAt {p : ℕ} (hp : p.Prime) {x : ℤ} (hsf : Squarefree x)
    (hsq : Nonvanishing.IsSquareAt p (x : ℚ)) : ¬ (p : ℤ) ∣ x := by
  haveI := Fact.mk hp
  intro hpx
  have hx0 : x ≠ 0 := by rintro rfl; exact not_squarefree_zero hsf
  obtain ⟨y, hy⟩ := hsq (Fact.mk hp)
  have hxq : ((x : ℚ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hx0
  have hy0 : y ≠ 0 := by rintro rfl; rw [mul_zero] at hy; exact hxq hy
  have hv := congrArg Padic.valuation hy
  rw [Padic.valuation_mul hy0 hy0, Padic.valuation_ratCast, padicValRat.of_int] at hv
  -- `v_p(x) = 1`
  have h1 : padicValInt p x = 1 := by
    have hn : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0
    have hle : x.natAbs.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hn).mp (Int.squarefree_natAbs.mpr hsf) p
    have hge : 1 ≤ padicValNat p x.natAbs :=
      one_le_padicValNat_of_dvd hn (Int.natCast_dvd.mp hpx)
    rw [← Nat.factorization_def _ hp] at hge
    rw [show padicValInt p x = padicValNat p x.natAbs from rfl, ← Nat.factorization_def _ hp]
    omega
  rw [h1] at hv
  omega

variable {L : Type} [AddCommGroup L] [Fintype L] {ε : L →+ ZMod 2}

/-- **RC0's leaf `AuxFactor` from the coefficient dictionary** (tex 10089–10098, 10131–10139),
`PROVED` (see the module docstring for the inputs). -/
theorem auxFactor_of_dictionary {ℓ : ℕ} (W : Wiring.WData ℓ) (hS : ∀ p ∈ W.S, p.Prime)
    (hS2 : 2 ∈ W.S) (T : TypeData L ε) (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ, CoefficientRules ε (A τ))
    (hoff : ∀ τ, VanishesOffFilter (A τ) τ)
    (hseed : ∀ τ, ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ ∧ (ε τ = 0 → Γ.V.Nonempty))
    (hspec : ∀ d : ℤ, d ≠ 0 →
      IsPartitionable ε (A (primeConfig d.natAbs.primeFactors T.typ).total)
        (primeConfig d.natAbs.primeFactors T.typ) → W.Partitionable d) :
    ∃ A₀ : ℕ, Wiring.AuxFactor W A₀ := by
  classical
  -- the minimum seeds and a vertex of each
  have hmin : ∀ τ, ∃ Γ₀ : Config L, IsMinSeed ε (A τ) Γ₀ := by
    intro τ
    obtain ⟨Γ, hΓ, hne⟩ := hseed τ
    refine exists_minSeed ⟨Γ, hΓ, ?_⟩
    by_cases hτ : ε τ = 0
    · exact hne hτ
    · exact negative_unitSeed_nonempty (hoff τ) (fun h => hτ (by rw [h, map_zero])) hΓ
  choose Γ₀ hΓ₀ using hmin
  choose s hs using fun τ => (hΓ₀ τ).2.1
  -- the dummy supply: one dummy per anchor of every seed, plus a reserve
  let P : Finset (Σ _ : L, ℕ) := univ.sigma fun τ => (Γ₀ τ).V.erase (s τ)
  let e : P ≃ Fin P.card := P.equivFin
  let A₀ := P.card + 1
  choose cl hcl htyp using fun ℓ' : L => T.classes ℓ'
  let tyOf : ℕ → L := fun i =>
    if h : i < P.card then (Γ₀ (e.symm ⟨i, h⟩).1.1).t (e.symm ⟨i, h⟩).1.2 else 0
  let cls : ℕ → ZMod T.m := fun i => cl (tyOf i)
  refine ⟨A₀, fun h hh0 _ _ hhS X hX => ?_⟩
  obtain ⟨q, hqinj, hq, ha0, hasf, haω, haSX, hah⟩ :=
    dummy_realization T.m T.m_pos T.two_dvd A₀ cls (fun i => hcl _) W.S X h
  set a : ℤ := ∏ i ∈ range A₀, (q i : ℤ) with ha
  refine ⟨a, ha0, hasf, haω, fun p hp => ?_, hah hh0.ne', fun u hu h8 hsfu hsq _ => ?_⟩
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
  -- no prime of `d` lies in the support
  have hnotS : ∀ p ∈ V, p ∉ W.S := by
    intro p hpV hpS
    obtain ⟨hp, hpd⟩ := (hmemV p).mp hpV
    rcases (Int.Prime.dvd_mul' hp hpd) with hph | hpau
    · exact hhS p hpS hph
    · exact not_dvd_of_isSquareAt hp hsfu (hsq p (mem_union_left _ hpS)) hpau
  have hgood : ∀ p ∈ V, T.Good p ∧ p ≠ 2 := by
    intro p hpV
    have hp := ((hmemV p).mp hpV).1
    refine ⟨⟨hp, (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hpm =>
      hnotS p hpV (hmS p hp hpm)⟩, fun h2 => hnotS p hpV (h2 ▸ hS2)⟩
  set Γ := primeConfig V T.typ with hΓdef
  have hΓ : Γ.Compatible ε := primeConfig_compatible ε V (fun p hp => ⟨(hgood p hp).1.1,
    (hgood p hp).2⟩) T.typ fun p hp => T.sign p (hgood p hp).1.1 (hgood p hp).1.2
  set τ := Γ.total
  -- the dummies lie in `V`
  have hqV : ∀ i < A₀, q i ∈ V := by
    intro i hi
    refine (hmemV _).mpr ⟨(hq i hi).1, ?_⟩
    have : (q i : ℤ) ∣ a := ha ▸ Finset.dvd_prod_of_mem _ (mem_range.mpr hi)
    exact (this.trans (dvd_mul_right a u)).trans (dvd_mul_left _ h)
  -- the anchors of the seed of `τ`
  have hmemP : ∀ v ∈ (Γ₀ τ).V.erase (s τ), (⟨τ, v⟩ : Σ _ : L, ℕ) ∈ P := fun v hv =>
    mem_sigma.mpr ⟨mem_univ _, hv⟩
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
  have htot : Γ.total = (Γ₀ τ).total := (hoff τ (Γ₀ τ) (hΓ₀ τ).1.2).symm
  have hpart := partitionable_of_anchors (hA τ) (hΓ₀ τ) hΓ htot (s τ) (hs τ) anc hanc_inj
    hancV hanct hrem
  exact hspec d hd0 hpart

end ZInQ.Contrib.CloudB3RC53.AuxFactor

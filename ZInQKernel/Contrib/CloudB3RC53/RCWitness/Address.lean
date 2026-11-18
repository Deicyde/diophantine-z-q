import ZInQKernel.Contrib.OneProof.RC.Wiring.AddressDict6

/-!
# RC inhabitability witnesses, group A: the address leaf `AddressPackageLeaf6`

Probe witnesses (PROVED, standard axioms) for `AddressPackageLeaf6` (`RC/Wiring/AddressDict6.lean`)
and the structures it carries.

* `addressLeaf6_vacuous`: `AddressPackageLeaf6 exW` for data `exW` (at `ℓ = 11`) whose odd limit
  symbol is a unit at the empty configuration (`OddEmptyUnit`), so the leaf holds vacuously. Its
  other hypotheses (`F3At`, `Gz34CompAt`, `Eq35At`, `VisAt`) are all satisfiable (`exW` has no
  prepared and no admissible discriminants), so `OddEmptyUnit` is the only escape: a non-vacuous
  instance is an instance of `AddressPackage6`.
* `addressHead_example`: conjuncts (1)–(4) of `AddressPackage6` at `ℓ = 11`, `k = −3`.
* `kSplitTypeData`, `kCharacter_m3`: the `K`-character conjunct (7k) for `k = −3`, with a type
  datum recording the sign and `(−3/q)` (conductor `12`).
* `alphabet_example`: conjuncts (6), (7⁶) (common alphabet, the two surjective projections, the
  even projection onto `ker χ_k`).
* `evenReading_example`: conjunct (18⁶) for suitable free data.
* `symb_zero`: the zero constituent model (`ConstituentModelRel.zero`, RC0) has the zero symbol,
  so with it the bounded-weight witness (11′) fails: a non-vacuous instance of (8⁗) + (11′)
  needs a constituent model with a nonzero odd reading at every budget.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RCWitness.Address

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53

/-- Data at `ℓ = 11` with no prepared or admissible discriminants and `v₂ a(1) = δ_o = 0`. -/
def exW : WData 11 where
  S := ∅
  prepared _ := False
  Lstar _ := 0
  jgen _ := 0
  jrc _ _ := 0
  hstar := -1
  stages := pure 0
  Mθ _ := 0
  aθ _ _ := 1
  admissible _ _ := False
  δo := 0
  kfin := -3
  uPrim _ _ := 0
  uTilde _ _ := 0
  Partitionable _ := False

theorem exW_oddEmptyUnit : exW.OddEmptyUnit := by
  refine Filter.Eventually.of_forall fun θ => ?_
  show vZ 1 = ((0 : ℤ) : WithTop ℤ)
  simp [vZ, v2]

/-- **`AddressPackageLeaf6` is inhabited (vacuously).** -/
theorem addressLeaf6_vacuous : AddressPackageLeaf6 exW :=
  fun _ _ _ _ _ _ _ _ _ hU => absurd exW_oddEmptyUnit hU

/-- The other hypotheses of the leaf hold for `exW` (so they do not make it vacuous). -/
theorem exW_hyps : F3At exW 0 0 ∧ Gz34CompAt exW 0 ∧ Eq35At exW 0 0 ∧ VisAt exW 0 :=
  ⟨fun _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim⟩

/-- Conjuncts (1)–(4) at `ℓ = 11`, `k = −3`. -/
theorem addressHead_example :
    Adm 11 ∧ Odd (-3 : ℤ) ∧ Squarefree (-3 : ℤ) ∧
      ∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ (-3 : ℤ) ∧ ¬ q₀ ∣ 2 * 11 := by
  refine ⟨⟨by norm_num, (by norm_num : Nat.Prime 11).squarefree, by norm_num⟩, ⟨-2, by norm_num⟩, ?_, 3, Nat.prime_three,
    ⟨-1, by norm_num⟩, by norm_num⟩
  exact (Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree

/-- The type of `q` recording the sign and `(−3/q)`. -/
def typM3 (q : ℕ) : ZMod 2 × ZMod 2 :=
  (((q / 2 : ℕ) : ZMod 2), if jacobiSym (-3) q = 1 then 0 else 1)

theorem typM3_of_mod {p c : ℕ} (hp : p.Prime) (h3 : p ≠ 2) (hc : (p : ZMod 12) = c)
    (hc12 : c < 12) : typM3 p = typM3 c := by
  have hpc : p % 12 = c := by
    rw [← Nat.mod_eq_of_lt hc12]
    exact (ZMod.natCast_eq_natCast_iff' p c 12).mp (by simpa using hc)
  unfold typM3
  have hodd : Odd p := hp.odd_of_ne_two h3
  rw [jacobiSym.mod_right (-3) hodd]
  have h12 : 4 * (-3 : ℤ).natAbs = 12 := rfl
  rw [h12, hpc]
  congr 1
  have : p / 2 % 2 = c / 2 % 2 := by omega
  rw [ZMod.natCast_eq_natCast_iff', this]

/-- **A type datum for `k = −3`**: `L₂ = 𝔽₂²` (sign, `(−3/q)`), conductor `12`. -/
def kSplitTypeData : CoefficientDictionary.TypeData (ZMod 2 × ZMod 2)
    (AddMonoidHom.fst (ZMod 2) (ZMod 2)) where
  m := 12
  m_pos := by norm_num
  two_dvd := by norm_num
  typ := typM3
  classes ℓ := by
    obtain ⟨a, b⟩ := ℓ
    have key : ∀ c : ℕ, c < 12 → IsUnit (c : ZMod 12) → typM3 c = (a, b) →
        ∃ c' : ZMod 12, IsUnit c' ∧ ∀ p : ℕ, p.Prime → (p : ZMod 12) = c' → typM3 p = (a, b) := by
      intro c hc hu ht
      refine ⟨c, hu, fun p hp hpc => ?_⟩
      have h2 : p ≠ 2 := by
        rintro rfl
        have : IsUnit ((2 : ℕ) : ZMod 12) := hpc ▸ hu
        exact absurd this (by decide)
      rw [typM3_of_mod hp h2 hpc hc, ht]
    fin_cases a <;> fin_cases b
    · exact key 1 (by norm_num) (by decide) (by simp [typM3]; rfl)
    · exact key 5 (by norm_num) (by decide) (by
        simp only [typM3]; norm_num [jacobiSym.mod_right]; decide)
    · exact key 7 (by norm_num) (by decide) (by
        simp only [typM3]; norm_num [jacobiSym.mod_right]; decide)
    · exact key 11 (by norm_num) (by decide) (by
        simp only [typM3]; norm_num [jacobiSym.mod_right]; decide)
  sign _ _ _ := rfl

/-- **Conjunct (7k) for `k = −3`**: `χ_k = snd` reads `(−3/q)`. -/
theorem kCharacter_m3 : ∀ q : ℕ, kSplitTypeData.Good q →
    ((AddMonoidHom.snd (ZMod 2) (ZMod 2)) (kSplitTypeData.typ q) = 0 ↔
      jacobiSym (-3 : ℤ) q = 1) := by
  intro q _
  show (if jacobiSym (-3) q = 1 then (0 : ZMod 2) else 1) = 0 ↔ _
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

/-- The even projection onto `ker snd`. -/
def π₂ex : ZMod 2 →+ (AddMonoidHom.snd (ZMod 2) (ZMod 2)).ker where
  toFun a := ⟨(a, 0), rfl⟩
  map_zero' := rfl
  map_add' _ _ := Subtype.ext (Prod.ext rfl (by simp))

/-- **Conjuncts (6), (7⁶)**: `L = L₁ = 𝔽₂` (sign), `L₂ = 𝔽₂²`, `χ_k = snd`. -/
theorem alphabet_example :
    (∀ x : ZMod 2, x + x = 0) ∧ Function.Surjective (AddMonoidHom.id (ZMod 2)) ∧
      Function.Surjective π₂ex ∧
      (∀ x, (AddMonoidHom.id (ZMod 2)) ((AddMonoidHom.id (ZMod 2)) x) =
        (AddMonoidHom.id (ZMod 2)) x) ∧
      (∀ x, (AddMonoidHom.fst (ZMod 2) (ZMod 2)) (π₂ex x : ZMod 2 × ZMod 2) =
        (AddMonoidHom.id (ZMod 2)) x) := by
  refine ⟨by decide, Function.surjective_id, fun ⟨⟨a, b⟩, hb⟩ => ⟨a, ?_⟩, fun _ => rfl,
    fun _ => rfl⟩
  have : b = 0 := hb
  subst this
  rfl

/-- **Conjunct (18⁶)** for free data: `inF = {1}`, `anew 1 = 1`, `L_*(k) = 1`. -/
theorem evenReading_example (Lstar : ℤ → ℚ) (k : ℤ) (hk : Lstar k = 1)
    {L : Type} (Realizes : ℕ → Symbols.Config L → ℤ → Prop)
    (A : Symbols.Config L → ZMod 2) (hA : ∀ Δ, A Δ ≠ 1) :
    ∃ (inF : ℤ → Prop) (anew : ℤ → ℚ) (κ c : ℤ),
      (∀ D, inF D → (Lstar (D * k) ≠ 0 ↔ anew D ≠ 0) ∧
        (anew D ≠ 0 → padicValRat 2 (Lstar (D * k)) = 2 * padicValRat 2 (anew D) + κ)) ∧
      (∀ D, inF D → anew D ≠ 0 → c ≤ padicValRat 2 (anew D) - (AppGEndpoints.omega D : ℤ)) ∧
      (∃ D, inF D ∧ anew D ≠ 0) ∧
      (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Realizes θ Δ D → A Δ = 1 →
        inF D ∧ anew D ≠ 0 ∧ ∀ D', inF D' → anew D' ≠ 0 →
          padicValRat 2 (anew D) - (AppGEndpoints.omega D : ℤ) ≤
            padicValRat 2 (anew D') - (AppGEndpoints.omega D' : ℤ)) := by
  refine ⟨fun D => D = 1, fun _ => 1, 0, -1, fun D hD => ?_, fun D hD _ => ?_, ⟨1, rfl, one_ne_zero⟩,
    fun _ Δ _ _ h => absurd h (hA Δ)⟩
  · subst hD
    refine ⟨by simp [hk], fun _ => by simp [hk]⟩
  · subst hD
    simp [AppGEndpoints.omega]

/-- **The zero constituent model has the zero symbol**, so it cannot carry the bounded-weight
witness (11′). -/
theorem symb_zero {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
    (T : CoefficientDictionary.TypeData L ε) (Γ : Symbols.Config L) :
    CoefficientDictionary.symb T (fun _ => 0) Γ = 0 := by
  unfold CoefficientDictionary.symb
  split_ifs <;> rfl

end ZInQ.Contrib.CloudB3RC53.RCWitness.Address

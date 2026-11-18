import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.FromPrintsAnalytic
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Parity

/-!
# Theorem 5.3, Lane RC0 round 2: the genus partner and the rough companion (lane RC13)

* `exists_genusPartner` (PROVED from lane RC13's `genusPartner`): with Hoffstein–Luo, BFH's twist
  sign and BCDT, root number `−1` for `E_ℓ` gives a genus partner `h_*` at the base support `S₀`
  (tex 2404–2408).
* `genusPartnerTarget_of` (PROVED): for data whose `h_*` is such a genus partner, the field
  `RCSteps.genus_partner` (`h_* < 0`, `L_*(h_*) ≠ 0`) from the normalization `lstar_ne_zero_iff`.
* `forward_corankZero` (PROVED from the blueprint's BCDT and Kolyvagin leaves and the Kummer glue):
  `L(E^{(d)}, 1) ≠ 0` gives `corank Sel_{2^∞}(E^{(d)}/ℚ) = 0` (`lem:forward-rank`, r = 0).
* `rootNumber_neg_one_of_simpleZero` (PROVED from lane RC8's `rootNumber_parity_of_analyticRank` and
  lane RC13's GLUE `RootNumberExists`): a twist with a simple zero has root number `−1`.
* `f3Target_of` (PROVED from lane RC13's `roughCompanion`): the rough companion with (F.3) in the
  form of batch 3's `FinalFamilyField`, from RC13's remaining inputs: the partitionable auxiliary
  factor (lane RC2) and the even upper bound (3.3b) (lane RC11), with the support and
  prepared-filter specifications (definitions).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53
  Filter Topology

attribute [local instance] Nat.fact_prime_two

/-! ## The genus partner -/

theorem mem_S0_prime {ℓ : ℕ} {p : ℕ} (hp : p ∈ S0 ℓ) : p.Prime := by
  simp only [S0, Finset.mem_insert, Nat.mem_primeFactors] at hp
  rcases hp with rfl | rfl | ⟨hp, -, -⟩
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact hp

/-- **A genus partner exists** (PROVED from lane RC13's `genusPartner`, tex 2404–2408): with
Hoffstein–Luo (`HoffsteinLuo`), BFH's twist sign (`BFHTwistSign`) and BCDT, root number `−1` for
`E_ℓ` gives `h_*` at the base support `S₀ = {2, 3} ∪ {p ∣ ℓ}`. -/
theorem exists_genusPartner (hHL : Nonvanishing.HoffsteinLuo) (hTS : Nonvanishing.BFHTwistSign)
    (hBCDT : BCDTThmA) {ℓ : ℕ} (hℓ : 0 < ℓ) (hw : RootNumber (Ecurve ℓ) (-1)) :
    ∃ h : ℤ, IsGenusPartner ℓ h := by
  obtain ⟨h, h1, h2, h3, h4, -, h6, h7⟩ := Nonvanishing.genusPartner hHL hTS hBCDT hℓ hw
    (S := S0 ℓ) (fun p hp => mem_S0_prime hp) (by simp [S0]) (by simp [S0])
    (fun p hp hpd => by simp [S0, Nat.mem_primeFactors, hp, hpd, hℓ.ne']) ∅ (by simp)
  exact ⟨h, h1, h2, h3, h4, h6, h7⟩

/-- `E_ℓ^{(h)}` as the curve of the family at `hℓ` (PROVED). -/
theorem Etw_eq_curve (ℓ : ℕ) (h : ℤ) : Etw ℓ h = curve ((h * ℓ : ℤ) : ℚ) := by
  rw [Etw_eq]; push_cast; rfl

/-- **The field `genus_partner`** (PROVED): for data whose `h_*` is a genus partner,
`h_* < 0` and `L_*(h_*) ≠ 0`, from the normalization of `L_*` (`lstar_ne_zero_iff`). -/
theorem genusPartnerTarget_of {ℓ : ℕ} {D : RCData ℓ} (hL : LstarTarget D)
    (hG : IsGenusPartner ℓ D.hstar) : GenusPartnerTarget D := by
  obtain ⟨hneg, -, -, -, -, hcn⟩ := hG
  refine ⟨hneg, (hL _ hneg.ne).mpr ?_⟩
  rw [Etw_eq_curve]
  exact hcn

/-! ## The forward theorem and root numbers of twists -/

/-- **The forward theorem in analytic rank zero for the twists** (PROVED from the blueprint's
BCDT and Kolyvagin leaves and the Kummer glue; `lem:forward-rank`, tex 1086–1108). -/
theorem forward_corankZero (P : Prints) (hKum : KummerCorankZero) {ℓ : ℕ} (hℓ : 0 < ℓ) {d : ℤ}
    (hd : d ≠ 0) (hL : AnalyticRank (Etw ℓ d) 0) : Z2Corank (selmerTwoPower (Etw ℓ d)) 0 := by
  have hE : (Etw ℓ d).IsElliptic := by
    rw [Etw_eq_curve]
    exact PoleRC.curve_isElliptic (by exact_mod_cast mul_ne_zero hd (by exact_mod_cast hℓ.ne'))
  obtain ⟨hrank, hsha⟩ := P.kolyvagin (Etw ℓ d) hE (P.bcdt _ hE) 0 (Nat.zero_le 1) hL
  exact hKum _ hE (by exact_mod_cast hrank) hsha

/-- **A twist with a simple zero has root number `−1`** (PROVED from lane RC8's parity lemma
`rootNumber_parity_of_analyticRank` and lane RC13's GLUE `RootNumberExists`). -/
theorem rootNumber_neg_one_of_simpleZero (hRN : Nonvanishing.FromRC8.RootNumberExists) {ℓ : ℕ}
    (hℓ : 0 < ℓ) {d : ℤ} (hd : d ≠ 0) (h1 : AnalyticRank (Etw ℓ d) 1) :
    RootNumber (Etw ℓ d) (-1) := by
  have hE : (Etw ℓ d).IsElliptic := by
    rw [Etw_eq_curve]
    exact PoleRC.curve_isElliptic (by exact_mod_cast mul_ne_zero hd (by exact_mod_cast hℓ.ne'))
  obtain ⟨w, hw⟩ := hRN _ hE
  have := PrintsAnalytic.rootNumber_parity_of_analyticRank hw h1
  rw [pow_one] at this
  rw [this]
  exact hw

/-! ## The rough companion with (F.3) -/

section RoughCompanion

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The fixed support** (definition, tex 1790–1793, 2678–2680): a finite set of primes containing
`2`, `3` and the primes of `ℓ` (hence the primes of `2N`). -/
def SupportSpec : Prop :=
  (∀ p ∈ W.S, p.Prime) ∧ 2 ∈ W.S ∧ 3 ∈ W.S ∧ ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ W.S

/-- **The prepared filter** (definition, tex 2344–2346, 2404–2410, 1836–1845, 10059–10061: the
prepared positive filter containing one; its members are positive, squarefree, `≡ 1 (mod 8)` ("Thus
`h ≡ 1 (mod 8)`", tex 2346) and prime to the fixed support). -/
def PreparedSpec : Prop :=
  ∀ h : ℤ, W.prepared h → 0 < h ∧ Squarefree h ∧ h % 8 = 1 ∧ ∀ p ∈ W.S, ¬ (p : ℤ) ∣ h

/-- **The partitionable auxiliary factor** (ELLIOT; lane RC2; the hypothesis `hdummy` of lane
RC13's `roughCompanion`, from App G `ex:app-rough-companion`, tex 10055–10150): for every positive
squarefree `h ≡ 1 (mod 8)` prime to the support (the prepared parameters, tex 2344–2346,
10059–10061) and every finite avoidance set, a positive squarefree `a` with `ω(a) = A₀`, prime to
the support, to the avoidance set and to `h`, such that every negative `au ≡ 1 (mod 8)`, squarefree
and square at the support and at the primes of `h`, with `L(E^{(h·au)},1) ≠ 0` (the companions
actually produced, tex 2380–2385), makes `h(au)` partitionable. -/
def AuxFactor (A₀ : ℕ) : Prop :=
  ∀ h : ℤ, 0 < h → Squarefree h → h % 8 = 1 → (∀ p ∈ W.S, ¬ (p : ℤ) ∣ h) →
    ∀ X : Finset ℕ, (∀ p ∈ X, p.Prime) →
    ∃ a : ℤ, 0 < a ∧ Squarefree a ∧ Nonvanishing.omega a = A₀ ∧
      (∀ p ∈ W.S ∪ X, ¬ (p : ℤ) ∣ a) ∧ IsCoprime a h ∧
      ∀ u : ℤ, a * u < 0 → (a * u) % 8 = 1 → Squarefree (a * u) →
        (∀ p ∈ W.S ∪ h.natAbs.primeFactors, Nonvanishing.IsSquareAt p ((a * u : ℤ) : ℚ)) →
        AnalyticRank (Etw ℓ (h * (a * u))) 0 →
          W.Partitionable (h * (a * u))

/-- **The even upper bound (3.3b)** (Proposition `ex:sec7-even-upper`, tex 2273–2318; ELLIOT;
lane RC11): at a partitionable `d ≠ 0` of Selmer corank zero, `L_*(d) ≠ 0` gives
`v₂L_*(d) ≤ 2ω(d) + s(d) + C₁`. (Stated with `d ≠ 0`; the text's `d` are nonzero.) -/
def EvenUpper33b (C₁ : ℤ) : Prop :=
  ∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
    padicValRat 2 (W.Lstar d) ≤ 2 * Nonvanishing.omega d + sFun ℓ d + C₁

theorem omega_eq_nonvanishing (n : ℤ) : omega n = Nonvanishing.omega n := rfl

/-- **The rough companion with (F.3)** (PROVED from lane RC13's `roughCompanion`, tex 2320–2401,
App G 10055–10150), in the form of batch 3's `FinalFamilyField`. Remaining inputs: the prints
(Hoffstein–Luo, BFH's twist sign; BCDT, Kolyvagin in `Prints`), the GLUE `RootNumberExists`, the
Kummer glue, the normalization of `L_*`, the support and prepared-filter specifications, the
partitionable auxiliary factor (RC2) and (3.3b) (RC11). -/
theorem f3Target_of (P : Prints) (hKum : KummerCorankZero) (hHL : Nonvanishing.HoffsteinLuo)
    (hTS : Nonvanishing.BFHTwistSign) (hRN : Nonvanishing.FromRC8.RootNumberExists) (hℓ : 0 < ℓ)
    (hL : LstarTarget W.toRCData) (hSupp : SupportSpec W) (hPrep : PreparedSpec W)
    {A₀ : ℕ} {C₁ : ℤ} (hAux : AuxFactor W A₀) (h33b : EvenUpper33b W C₁) : F3Target W := by
  obtain ⟨hSp, h2, h3, hℓS⟩ := hSupp
  have hE : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  have hbad : ∀ p : ℕ, p.Prime → ¬ Nonvanishing.GoodAt (Ecurve ℓ) p → p ∈ W.S := by
    have := Nonvanishing.bad_curve_mem (m := (ℓ : ℤ)) h2 h3
      (fun p hp hpd => hℓS p hp (Int.natCast_dvd_natCast.mp hpd))
    simpa [Ecurve] using this
  -- RC13's predicates: partitionable and nonzero; corank zero at nonzero twists.
  obtain ⟨A, CE, hRC⟩ := Nonvanishing.roughCompanion hHL hTS P.bcdt hE hSp h2 hbad
    (fun d => W.Partitionable d ∧ d ≠ 0)
    (fun d => d ≠ 0 → Z2Corank (selmerTwoPower (qtwist (Ecurve ℓ) (d : ℚ))) 0)
    (fun d => padicValRat 2 (W.Lstar d)) (sFun ℓ) C₁ A₀
    (fun h hh hsqf h8 hS X hX => by
      obtain ⟨a, ha, hsf, hω, hSX, hcop, hpart⟩ := hAux h hh hsqf h8 hS X hX
      refine ⟨a, ha, hsf, hω, hSX, hcop, fun u hu h8' hsfu hsq hcn =>
        ⟨hpart u hu h8' hsfu hsq hcn, ?_⟩⟩
      exact mul_ne_zero hh.ne' (by intro h0; rw [h0] at hu; simp at hu))
    (fun d hd hd0 => forward_corankZero P hKum hℓ hd0 hd)
    (fun d ⟨hpd, hd0⟩ hcz => h33b d hd0 hpd (hcz hd0))
  refine ⟨A, CE, fun h hprep hsz => ?_⟩
  obtain ⟨hpos, hsqf, h8, hprime⟩ := hPrep h hprep
  have hw := rootNumber_neg_one_of_simpleZero hRN hℓ hpos.ne' hsz
  obtain ⟨k', hk'neg, hk'8, hk'F, hloc, hX, ⟨hpart, -⟩, hcn, hωk, hvL⟩ :=
    hRC h hpos hsqf h8 hprime hw W.hstar.natAbs.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hhk : h * k' ≠ 0 := mul_ne_zero hpos.ne' hk'neg.ne
  refine ⟨k', ⟨hk'neg, hk'8, hk'F, hloc, hX, hpart, hcn⟩, by exact_mod_cast hωk,
    (hL _ hhk).mpr hcn, ?_⟩
  simpa [omega_eq_nonvanishing] using hvL

end RoughCompanion

end ZInQ.Manuscript.RC.Wiring

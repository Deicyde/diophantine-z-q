import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Realize
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Symbols

/-!
# Theorem 5.3, Lane RC24: the address package over genuine label alphabets and prime realizations

Manuscript `diophantine_zq.tex`: Definition `ex:sec7-typed-graph` (tex 2015–2066), Definition
`ex:sec7-symbol` (2068–2100), Lemma `ex:sec7-realization` (2151–2174), the final companion
(2595–2614), App F Proposition `ex:app-coefficient-rules` (9447–9976), App G Propositions
`ex:app-nonempty-seeds` (10258–10506), `ex:app-odd-stabilization` (10508–10552),
`ex:app-simultaneous-address` (10554–10790) and `ex:app-final-family` (10792–10861).

Lane RC0's `AddressPackageStaged W C` (`RC/Wiring/Address.lean`) asks for abstract alphabets
`L, L₁, L₂`, projections, odd stage tables `Aodd θ`, an even symbol `Aev`, a realization relation and
eighteen conjuncts. Here every abstract object is replaced by the genuine one, and the conjuncts are
PROVED from smaller inputs stated over actual primes and the data `W`:

* the alphabets are squareclass groups of residue classes (Lane RC24 `Types.lean`): the common
  alphabet `L` = the `K`-split squareclasses modulo the common label modulus `m`, with the Legendre
  bit at the moving theta prime; the intrinsic odd alphabet `L₁` = squareclasses modulo `m₁` with that
  bit; the even alphabet `L₂` = the `K`-split squareclasses modulo `m₂` (the support of the transported
  source, containing the primes of `k`);
* the realization relation is the genuine prime realization (`Realize.lean`): `D = ∏ q^*` over
  distinct good `K`-split primes with the prescribed classes and residue bits;
* the odd stage table at stage `θ` is the stage symbol (`Symbols.lean`) of the genuine reading
  `Rodd W θ U = [D admissible at θ ∧ v₂ a_θ(D) = δ_o + |U|]`, `D = ∏_{q ∈ U} q` (Definition
  `ex:sec7-symbol`, the coefficient symbol of the data at the positive Fourier index);
* the even symbol is the restriction to `K`-split labels of the symbol of the even reading `Rev`
  (tex 2023–2024: "Additional fixed splitting conditions restrict us to their actual realizable
  types").

**Why the restriction (a finding about the dictionary form).** Conjunct 15 forces every label of the
common alphabet to be `K`-split (`Family.Admissible` needs `(k/q) = 1` at every vertex prime), and
the even source of `E^{(k)}` has its support containing the primes of `k` (tex 10292–10293), so its
genuine type alphabet (squareclasses at its support, for ALL good primes, as batch 3's `TypeData`
requires) contains the character of `K`. The genuine projection from the `K`-split common alphabet
then lands in its kernel, and "`π₂` surjective" (conjunct 7) fails for the full even alphabet; on
the other hand batch 3's `TypeData` cannot carry the `K`-split alphabet, its good primes being all
primes prime to the conductor. Hence `AddressPackageDict` (and lane RC0's round-3 refinements, which
keep its conjuncts 7 and 9) cannot be discharged faithfully on the even side, while
`AddressPackageStaged` can: its conjunct 9 is `CoefficientRules` for the restricted symbol, which
follows from the rules of the full even symbol (`coefficientRules_comp`).

The inputs of `addressPackageStaged_of_genuine` (kinds and tex lines in their docstrings):
`LabelData` (definition), `FreshPrime` (ELLIOT), `OddReadings` (ELLIOT, App F), `OddWitness`
(ELLIOT), `OddFilter`, `PreparedFilter`, `EvenFilter` (definition), `EvenReadings` (ELLIOT, App F),
`KSplitSeed` (ELLIOT, App G), `EvenReading` (ELLIOT/PRINT, Waldspurger).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter Finset

/-! ## The label data -/

/-- **The label moduli and the moving theta prime** (definition; tex 2015–2025, 2162–2163,
2600–2603, 10288–10295, 10525–10532): the common label modulus `m` (supported on `S_lab`, containing
eight), the intrinsic odd modulus `m₁ ∣ m` (the old odd support), the even modulus `m₂ ∣ m` (the
support of the transported source, containing `4|k|`), the moving theta prime `ℓ₀ θ` of stage `θ`
(prime to `m`: "Choose every later moving theta prime `ℓ₀` away from `k`", tex 2602–2603), and the
bad primes of `E_ℓ` and `E^{(k)}` inside the respective supports. -/
structure LabelData {ℓ : ℕ} (W : WData ℓ) where
  /-- the common label modulus -/
  m : ℕ
  /-- the intrinsic odd modulus -/
  m₁ : ℕ
  /-- the even modulus -/
  m₂ : ℕ
  m_pos : 0 < m
  m₁_pos : 0 < m₁
  m₂_pos : 0 < m₂
  dvd₁ : m₁ ∣ m
  dvd₂ : m₂ ∣ m
  four₁ : 4 ∣ m₁
  four₂ : 4 ∣ m₂
  /-- the types record the class modulo eight (tex 2018–2020) -/
  eight₁ : 8 ∣ m₁
  eight₂ : 8 ∣ m₂
  kdvd : 4 * W.kfin.natAbs ∣ m₂
  /-- the primes of `6ℓ` are in the odd support -/
  bad₁ : ∀ p : ℕ, p.Prime → p ∣ 6 * ((ℓ : ℤ)).natAbs → p ∣ m₁
  /-- the primes of `6kℓ` are in the even support -/
  bad₂ : ∀ p : ℕ, p.Prime → p ∣ 6 * (W.kfin * ℓ).natAbs → p ∣ m₂
  /-- the moving theta prime of each stage -/
  ℓ₀ : ℕ → ℕ
  ℓ₀_prime : ∀ θ, (ℓ₀ θ).Prime
  ℓ₀_cop : ∀ θ, Nat.Coprime (ℓ₀ θ) m

namespace LabelData

variable {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)

theorem four : 4 ∣ D.m := D.four₁.trans D.dvd₁

theorem kdvdm : 4 * W.kfin.natAbs ∣ D.m := D.kdvd.trans D.dvd₂

theorem ℓ₀_cop₁ (θ : ℕ) : Nat.Coprime (D.ℓ₀ θ) D.m₁ :=
  Nat.Coprime.coprime_dvd_right D.dvd₁ (D.ℓ₀_cop θ)

instance neZero_m : NeZero D.m := ⟨D.m_pos.ne'⟩

instance neZero_m₁ : NeZero D.m₁ := ⟨D.m₁_pos.ne'⟩

instance neZero_m₂ : NeZero D.m₂ := ⟨D.m₂_pos.ne'⟩

/-- The common alphabet: `K`-split squareclasses modulo `m` and the bit at `ℓ₀`. -/
abbrev L : Type := CommonL D.m W.kfin D.kdvdm

/-- The intrinsic odd alphabet: squareclasses modulo `m₁` and the bit at `ℓ₀`. -/
abbrev L₁ : Type := SqClass D.m₁ × ZMod 2

/-- The even alphabet: the `K`-split squareclasses modulo `m₂`. -/
abbrev L₂ : Type := KSplitClass D.m₂ W.kfin D.kdvd

/-- The sign coordinate of the common alphabet. -/
def ε : D.L →+ ZMod 2 := commonSign D.m D.four W.kfin D.kdvdm

/-- The sign coordinate of the odd alphabet. -/
def ε₁ : D.L₁ →+ ZMod 2 := stageSign D.m₁ D.four₁

/-- The inclusion of the `K`-split even classes. -/
def ι₂ : D.L₂ →+ SqClass D.m₂ := (kSplitSub D.m₂ W.kfin D.kdvd).subtype

theorem ι₂_injective : Function.Injective D.ι₂ :=
  (kSplitSub D.m₂ W.kfin D.kdvd).subtype_injective

/-- The sign coordinate of the even alphabet. -/
def ε₂ : D.L₂ →+ ZMod 2 := (signChar D.m₂ D.four₂).comp D.ι₂

/-- The odd projection. -/
def π₁ : D.L →+ D.L₁ := oddProj D.dvd₁

/-- The even projection. -/
def π₂ : D.L →+ D.L₂ := (kSplitProj D.dvd₂ D.kdvd).comp (AddMonoidHom.fst _ _)

/-- The odd type data at stage `θ` (the reduction prime `ℓ₀ θ` is part of the support). -/
def T₁ (θ : ℕ) : TypeData D.L₁ D.ε₁ :=
  stageTypeData D.m₁ D.m₁_pos D.four₁ (D.ℓ₀ θ) (D.ℓ₀_prime θ) (D.ℓ₀_cop₁ θ)

/-- The even type data. -/
def T₂ : TypeData (SqClass D.m₂) (signChar D.m₂ D.four₂) := typeData D.m₂ D.m₂_pos D.four₂

/-- The realization relation at stage `θ`. -/
def Realizes (θ : ℕ) : Config D.L → ℤ → Prop := RealizesAt D.m W.kfin D.kdvdm (D.ℓ₀ θ) W.S

end LabelData

/-! ## The genuine readings -/

open Classical in
/-- **The odd reading of the data at stage `θ`** (Definition `ex:sec7-symbol`, tex 2068–2086,
2045–2046: the coefficient symbol `[v₂ a(D) = δ + ω(D)]` on the filter at the positive Fourier index
`D = ∏ p_v`; App F 9675–9678): one exactly when `D = ∏_{q ∈ U} q` is admissible at `θ` and
`v₂ a_{M_θ}(D) = δ_o + |U|`. -/
def Rodd {ℓ : ℕ} (W : WData ℓ) (θ : ℕ) (U : Finset ℕ) : ZMod 2 :=
  if W.admissible θ (∏ q ∈ U, (q : ℤ)) ∧
      vZ (W.aθ θ (∏ q ∈ U, (q : ℤ))) = (((U.card : ℤ) + W.δo : ℤ) : WithTop ℤ) then 1 else 0

/-- `a_p(E_ℓ)`, Mathlib's Dirichlet coefficient of `L(E_ℓ, s)` at `p`. -/
def apo (ℓ : ℕ) (p : ℕ) : ℤ := (ZInQ.Manuscript.curve (((ℓ : ℤ)) : ℚ)).LFunction p

/-- `a_p(E^{(k)}) = a_p(E_{kℓ})`. -/
def apk {ℓ : ℕ} (W : WData ℓ) (p : ℕ) : ℤ :=
  (ZInQ.Manuscript.curve (((W.kfin * ℓ : ℤ)) : ℚ)).LFunction p

/-! ## The inputs -/

section Inputs

variable {ℓ : ℕ} (W : WData ℓ) (D : LabelData W) (Rev : Finset ℕ → ZMod 2)

/-- **Fresh ramification of `K`** (ELLIOT, the choice of the companion; tex 2600–2601, 2605–2608,
10276–10286: "At least one prime ramified in `K` is outside all the old fixed label extensions and
torsion ramification"): a prime `q₀ ∣ k` outside the old odd support. -/
def FreshPrime : Prop := ∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ W.kfin ∧ ¬ q₀ ∣ D.m₁

/-- **App F's readings of the odd stage source within every budget, at the valid stages**
(ELLIOT; Proposition `ex:app-coefficient-rules`, tex 9447–9976, at the stages of tex 10533–10540):
the fixed-`U` factorization, (O.12) at coefficient one with the product-label rule, and primary
isolation, for the genuine stage types and the genuine odd reading. -/
def OddReadings : Prop :=
  ∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
    FixedUFactorization (D.T₁ θ) (Rodd W θ) (Wc + 1) ∧
      O12Reading (D.T₁ θ) (Rodd W θ) (apo ℓ) (Wc + 1) ∧ PrimaryReading (D.T₁ θ) (Rodd W θ) (Wc + 1)

/-- **The bounded-weight witness** (ELLIOT; tex 2588–2593, 10268–10270, 10501–10505, 10547): a
nonempty set of good primes whose odd reading is one on a set of stages of the ultrafilter. -/
def OddWitness : Prop :=
  ∃ U : Finset ℕ, U.Nonempty ∧ (∀ q ∈ U, q.Prime ∧ Nat.Coprime q D.m₁) ∧
    ∀ᶠ θ in (W.stages : Filter ℕ), (∀ q ∈ U, q ≠ D.ℓ₀ θ) ∧ Rodd W θ U = 1

/-- **The odd filter contains one** (definition; tex 2042–2044, 10236–10240, 10589–10591: "its
fixed unit squareclasses, positive sign, and moving condition `(D/ℓ₀) = 1` are those of `1`"). -/
def OddFilter : Prop :=
  ∀ θ : ℕ, ∀ D' : ℤ, W.admissible θ D' →
    0 < D' ∧ IsSquare (D' : ZMod D.m₁) ∧ IsSquare (D' : ZMod (D.ℓ₀ θ))

/-- **The prepared filter is the squareclass of one** (definition; tex 2404–2410, 2686,
10795–10804: "All fixed local types are retained"). -/
def PreparedFilter : Prop :=
  ∀ D' : ℤ, 0 < D' → Squarefree D' → IsSquare (D' : ZMod D.m) →
    (∀ p ∈ W.S, p.Prime → ¬ (p : ℤ) ∣ D') → W.prepared D'

/-- **App F's readings of the transported even source at every size** (ELLIOT; tex 9447–9976,
10288–10318). -/
def EvenReadings : Prop :=
  (∀ B, FixedUFactorization D.T₂ Rev B) ∧ (∀ B, O12Reading D.T₂ Rev (apk W) B) ∧
    (∀ B, PrimaryReading D.T₂ Rev B)

/-- **The even filter contains one** (definition; tex 10264–10265, 10293–10295, 10591–10594: the
source is "normalized in the unit filter containing `1`"): a unit of the even reading has its index
in the squareclass of one at the support. -/
def EvenFilter : Prop :=
  ∀ U : Finset ℕ, (∀ q ∈ U, q.Prime ∧ Nat.Coprime q D.m₂) → Rev U = 1 →
    IsSquare (((∏ q ∈ U, (q : ℤ) : ℤ)) : ZMod D.m₂)

/-- **The `K`-split seed** (ELLIOT; Lemma `ex:sec7-ksplit-seed`, tex 2628–2654, App G
10319–10481): if the even reading vanishes on every nonempty set of good `K`-split primes, then the
App G congruence `a_p(E^{(k)}) ≡ p + 1 (mod 8)` holds at the good `K`-split primes outside a finite
support (lane RC3's form; RC3 proves its contradiction). -/
def KSplitSeed : Prop :=
  ∃ Sev : Finset ℕ,
    (∀ U : Finset ℕ, U.Nonempty →
      (∀ q ∈ U, q.Prime ∧ Nat.Coprime q D.m₂ ∧ jacobiSym W.kfin q = 1) → Rev U = 0) →
    KSplit.AppGCongruenceB3 ℓ W.kfin Sev

/-- **The even reading** (ELLIOT/PRINT: Waldspurger comparison for the transported source,
(E.11), (F.1); tex 8136–8146, 10079–10094, 10288–10322, 10854–10855): at a unit of the even reading
on good `K`-split primes, `L_*(Dk) ≠ 0` and `v₂ L_*(Dk) ≤ 2ω(D) + C_{e,final}`, `D = ∏ q`. -/
def EvenReading : Prop :=
  ∃ CeFinal : ℤ, ∀ U : Finset ℕ,
    (∀ q ∈ U, q.Prime ∧ Nat.Coprime q D.m₂ ∧ jacobiSym W.kfin q = 1) → Rev U = 1 →
      W.Lstar ((∏ q ∈ U, (q : ℤ)) * W.kfin) ≠ 0 ∧
        padicValRat 2 (W.Lstar ((∏ q ∈ U, (q : ℤ)) * W.kfin)) ≤ 2 * (U.card : ℤ) + CeFinal

end Inputs

/-! ## Helpers -/

section Helpers

/-- A product of primes prime to `m` is a unit modulo `m`. -/
theorem isUnit_prod_of_coprime {m : ℕ} {Q : Finset ℕ} (hQ : ∀ q ∈ Q, Nat.Coprime q m) :
    IsUnit (((∏ q ∈ Q, (q : ℤ) : ℤ)) : ZMod m) := by
  have h : (∏ q ∈ Q, (q : ℤ)) = ((∏ q ∈ Q, q : ℕ) : ℤ) := by push_cast; rfl
  rw [h]
  exact isUnit_natCast_of_coprime (Nat.Coprime.prod_left hQ)

/-- **A product in the squareclass of one has total sign zero** (PROVED; tex 2037–2046). -/
theorem sign_zero_of_isSquare {m : ℕ} (h4 : 4 ∣ m) {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, Nat.Coprime q m) (hsq : IsSquare (((∏ q ∈ Q, (q : ℤ) : ℤ)) : ZMod m)) :
    ∑ q ∈ Q, signChar m h4 (sqClassOf m q) = 0 := by
  rw [← map_sum, ← sqClassOf_prod Q (fun q => (q : ℤ))
    (fun q hq => isUnit_natCast_of_coprime (hQ q hq)),
    (sqClassOf_eq_zero_iff (isUnit_prod_of_coprime hQ)).mpr hsq, map_zero]

/-- **On the squareclass of one, `∏ q^* = ∏ q`** (PROVED). -/
theorem prod_qstar_of_isSquare {m : ℕ} (h4 : 4 ∣ m) {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, Nat.Coprime q m) (hsq : IsSquare (((∏ q ∈ Q, (q : ℤ) : ℤ)) : ZMod m)) :
    ∏ q ∈ Q, qstar q = ∏ q ∈ Q, (q : ℤ) :=
  prod_qstar_eq_prod_of_sign_zero h4 hQ (sign_zero_of_isSquare h4 hQ hsq)

/-- A value `1` of batch 3's `symb` comes from a realization reading `1` (PROVED). -/
theorem symb_eq_one {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
    {R : Finset ℕ → ZMod 2} {Γ : Config L} (h : symb T R Γ = 1) :
    ∃ f, IsReal T Γ f ∧ R (Γ.V.image f) = 1 := by
  classical
  unfold symb at h
  split_ifs at h with hr
  · exact ⟨hr.choose, hr.choose_spec, h⟩
  · exact absurd h (by decide)

/-- A value `1` of the odd reading: admissibility and the exact valuation (PROVED; definition of
`Rodd`). -/
theorem rodd_eq_one {ℓ : ℕ} {W : WData ℓ} {θ : ℕ} {U : Finset ℕ} (h : Rodd W θ U = 1) :
    W.admissible θ (∏ q ∈ U, (q : ℤ)) ∧
      vZ (W.aθ θ (∏ q ∈ U, (q : ℤ))) = (((U.card : ℤ) + W.δo : ℤ) : WithTop ℤ) := by
  classical
  unfold Rodd at h
  split_ifs at h with hr
  · exact hr
  · exact absurd h (by decide)

end Helpers

section Assembly

variable {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)

/-- The odd type data have conductor `m₁ ℓ₀` and the stage types (PROVED, by definition). -/
theorem LabelData.T₁_m (θ : ℕ) : (D.T₁ θ).m = D.m₁ * D.ℓ₀ θ := by
  simp [LabelData.T₁, stageTypeData_m]

theorem LabelData.T₁_typ (θ p : ℕ) : (D.T₁ θ).typ p = (sqClassOf D.m₁ p, legBit p (D.ℓ₀ θ)) := by
  simp [LabelData.T₁, stageTypeData_typ]

theorem LabelData.T₂_m : D.T₂.m = D.m₂ := by simp [LabelData.T₂, typeData_m]

theorem LabelData.T₂_typ : D.T₂.typ = fun p : ℕ => sqClassOf D.m₂ (p : ℤ) := by
  funext p; simp [LabelData.T₂, typeData_typ]

/-- **`a_p(E_ℓ)` is even at the good primes of every stage** (PROVED: lane RC24 `apEven_of`;
the primes of `6ℓ` divide `m₁`). -/
theorem LabelData.apEven₁ (θ : ℕ) : ApEven (D.T₁ θ) (apo ℓ) :=
  apEven_of (D.T₁ θ) (m := (ℓ : ℤ)) fun p hp hd => by
    rw [D.T₁_m]; exact Dvd.dvd.mul_right (D.bad₁ p hp hd) _

/-- **`a_p(E^{(k)})` is even at the good primes of the even source** (PROVED). -/
theorem LabelData.apEven₂ : ApEven D.T₂ (apk W) :=
  apEven_of D.T₂ (m := W.kfin * ℓ) fun p hp hd => by rw [D.T₂_m]; exact D.bad₂ p hp hd

/-- **The total type of a stage realization in the odd filter is zero** (PROVED; tex 2042–2044,
10589–10596). -/
theorem LabelData.total_eq_zero_odd {θ : ℕ} {Γ : Config D.L₁} {f : ℕ → ℕ}
    (hf : IsReal (D.T₁ θ) Γ f)
    (hsq₁ : IsSquare (((∏ q ∈ Γ.V.image f, (q : ℤ) : ℤ)) : ZMod D.m₁))
    (hsqℓ : IsSquare (((∏ q ∈ Γ.V.image f, (q : ℤ) : ℤ)) : ZMod (D.ℓ₀ θ))) :
    Γ.total = 0 := by
  have hgood : ∀ q ∈ Γ.V.image f, q.Prime ∧ Nat.Coprime q D.m₁ ∧ ¬ (D.ℓ₀ θ : ℤ) ∣ (q : ℤ) := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp, hc⟩ := (hf.2.1 v hv).1
    rw [D.T₁_m] at hc
    refine ⟨hp, Nat.Coprime.coprime_mul_right_right hc, fun hdvd => ?_⟩
    have h1 : D.ℓ₀ θ ∣ f v := Int.natCast_dvd_natCast.mp hdvd
    have h2 : Nat.Coprime (f v) (D.ℓ₀ θ) := Nat.Coprime.coprime_mul_left_right hc
    exact (D.ℓ₀_prime θ).one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h2) h1)
  have htot : Γ.total = ∑ q ∈ Γ.V.image f, (sqClassOf D.m₁ q, legBit q (D.ℓ₀ θ)) := by
    unfold Config.total
    rw [Finset.sum_image (fun a ha b hb hab => hf.1 ha hb hab)]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← (hf.2.1 v hv).2, D.T₁_typ]
  rw [htot]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum, Prod.fst_zero]
    rw [← sqClassOf_prod _ (fun q => (q : ℤ))
      (fun q hq => isUnit_natCast_of_coprime (hgood q hq).2.1)]
    exact (sqClassOf_eq_zero_iff (isUnit_prod_of_coprime fun q hq => (hgood q hq).2.1)).mpr hsq₁
  · rw [Prod.snd_sum, Prod.snd_zero]
    rw [← legBit_prod _ (fun q => (q : ℤ)) (D.ℓ₀_prime θ) fun q hq => (hgood q hq).2.2]
    exact legBit_eq_zero_iff.mpr hsqℓ

/-- **The total type of an even unit is zero** (PROVED from the even filter; tex 2042–2044,
10264–10265, 10591–10594). -/
theorem LabelData.even_filter_total {Rev : Finset ℕ → ZMod 2} (hefilt : EvenFilter W D Rev) :
    ∀ Γ : Config (SqClass D.m₂), IsUnitSeed (signChar D.m₂ D.four₂) (symb D.T₂ Rev) Γ →
      Γ.total = 0 := by
  intro Γ ⟨_, h1⟩
  obtain ⟨f, hf, hR⟩ := symb_eq_one h1
  have hgood : ∀ q ∈ Γ.V.image f, q.Prime ∧ Nat.Coprime q D.m₂ := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp, hc⟩ := (hf.2.1 v hv).1
    rw [D.T₂_m] at hc
    exact ⟨hp, hc⟩
  have hsq := hefilt _ hgood hR
  unfold Config.total
  rw [show ∑ v ∈ Γ.V, Γ.t v = ∑ q ∈ Γ.V.image f, sqClassOf D.m₂ (q : ℤ) by
    rw [Finset.sum_image (fun a ha b hb hab => hf.1 ha hb hab)]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← (hf.2.1 v hv).2, D.T₂_typ]]
  rw [← sqClassOf_prod _ (fun q => (q : ℤ))
    (fun q hq => isUnit_natCast_of_coprime (hgood q hq).2)]
  exact (sqClassOf_eq_zero_iff (isUnit_prod_of_coprime fun q hq => (hgood q hq).2)).mpr hsq

/-- **The total type of a unit seed of the restricted even symbol is zero** (PROVED). -/
theorem LabelData.even_unit_total {Rev : Finset ℕ → ZMod 2} (hefilt : EvenFilter W D Rev)
    (Γ : Config D.L₂)
    (hΓ : IsUnitSeed ((signChar D.m₂ D.four₂).comp D.ι₂) (fun Δ => symb D.T₂ Rev (Δ.mapType D.ι₂)) Γ) :
    Γ.total = 0 :=
  total_eq_zero_of_isUnitSeed_comp (L := SqClass D.m₂) (L' := D.L₂) (ε := signChar D.m₂ D.four₂)
    (A := symb D.T₂ Rev) D.ι₂ D.ι₂_injective (D.even_filter_total hefilt) hΓ

open Classical in
/-- The even configuration of a set of good `K`-split primes. -/
def LabelData.evenConfig (U : Finset ℕ) : Config D.L₂ where
  V := U
  t := fun q => if h : sqClassOf D.m₂ q ∈ kSplitSub D.m₂ W.kfin D.kdvd then ⟨_, h⟩ else 0
  z := fun v w => legBit v w

/-- The even configuration of good `K`-split primes is realized by its own primes (PROVED). -/
theorem LabelData.evenConfig_real {U : Finset ℕ}
    (hU : ∀ q ∈ U, q.Prime ∧ Nat.Coprime q D.m₂ ∧ jacobiSym W.kfin q = 1) :
    IsReal D.T₂ ((D.evenConfig U).mapType D.ι₂) id := by
  refine ⟨Set.injOn_id _, fun v hv => ?_, fun v _ w _ _ => rfl⟩
  obtain ⟨hp, hc, hj⟩ := hU v hv
  refine ⟨⟨hp, by rw [D.T₂_m]; exact hc⟩, ?_⟩
  have hmem : sqClassOf D.m₂ v ∈ kSplitSub D.m₂ W.kfin D.kdvd :=
    mem_kSplitSub.mpr ((kChar_sqClassOf_eq_zero_iff D.kdvd hp hc).mpr hj)
  simp only [Config.mapType, LabelData.evenConfig, D.T₂_typ, id, LabelData.ι₂]
  rw [dite_eq_left hmem]
  rfl

end Assembly

/-! ## The address package -/

/-- **Lane RC0's `AddressPackageStaged` over the genuine objects** (PROVED from the inputs; tex
2015–2174, 2595–2672, App F 9447–9976, App G 10258–10861). -/
theorem addressPackageStaged_of_genuine {ℓ : ℕ} (W : WData ℓ) (D : LabelData W)
    (Rev : Finset ℕ → ZMod 2) (hℓ : Adm ℓ) (hk : Odd W.kfin) (hksf : Squarefree W.kfin)
    (hfresh : FreshPrime W D) (hodd : OddReadings W D) (hwit : OddWitness W D)
    (hofilt : OddFilter W D) (hprep : PreparedFilter W D) (hev : EvenReadings W D Rev)
    (hefilt : EvenFilter W D Rev) (hseed : KSplitSeed W D Rev) (hread : EvenReading W D Rev)
    (Ccoarse : ℚ) : AddressPackageStaged W Ccoarse := by
  classical
  obtain ⟨q₀, hq₀, hq₀k, hq₀m₁⟩ := hfresh
  obtain ⟨CeFinal, hCe⟩ := hread
  have hfin : Fintype D.L := Fintype.ofFinite _
  refine ⟨hℓ, hk, hksf, ⟨q₀, hq₀, hq₀k, fun hdvd => hq₀m₁ (D.bad₁ q₀ hq₀ ?_)⟩, CeFinal,
    D.L, D.L₁, D.L₂, inferInstance, hfin, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, D.ε, D.ε₁, D.ε₂, D.π₁, D.π₂,
    fun θ => stageSymbol (D.T₁ θ) (Rodd W θ), fun Γ => symb D.T₂ Rev (Γ.mapType D.ι₂),
    D.Realizes, ?h6, ?h7a, ?h7b, ?h7c, ?h7d, ?h8, ?h9, ?h11, ?h12, ?h13, ?h14, ?h15, ?h16, ?h17,
    ?h18⟩
  · -- q₀ ∣ 2ℓ ⇒ q₀ ∣ 6ℓ
    have : (q₀ : ℤ) ∣ 6 * (ℓ : ℤ) := by
      have h2 : (q₀ : ℤ) ∣ 2 * (ℓ : ℤ) := by exact_mod_cast hdvd
      exact h2.trans ⟨3, by ring⟩
    have h6 : q₀ ∣ 6 * ((ℓ : ℤ)).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr this
      simpa [Int.natAbs_mul] using this
    exact h6
  case h6 =>
    rintro ⟨a, b⟩
    refine Prod.ext (Subtype.ext (sqClass_add_self (a : SqClass D.m))) ?_
    show b + b = 0
    revert b; decide
  case h7a =>
    rintro ⟨y, b⟩
    obtain ⟨x, hx0, hxy⟩ := exists_kSplit_lift D.dvd₁ D.four₁ D.kdvdm hk hksf hq₀ hq₀k hq₀m₁ y
    exact ⟨(⟨x, mem_kSplitSub.mpr hx0⟩, b), by
      simp only [LabelData.π₁, oddProj_apply, hxy]⟩
  case h7b =>
    intro y
    obtain ⟨x, hx⟩ := kSplitProj_surjective D.dvd₂ D.kdvd y
    exact ⟨(x, 0), hx⟩
  case h7c => exact fun x => oddSign_oddProj D.dvd₁ D.four₁ D.four x
  case h7d =>
    exact fun x => evenSign_proj D.dvd₂ D.four₂ D.four (D.ι₂.comp D.π₂)
      (fun x => kSplitProj_coe D.dvd₂ D.kdvd x.1) x
  case h8 =>
    intro Wc
    filter_upwards [hodd Wc] with θ hθ
    exact rulesUpTo_stageSymbol (D.T₁ θ) (Rodd W θ) (apo ℓ) Wc hθ.1 hθ.2.1 (D.apEven₁ θ) hθ.2.2
  case h9 =>
    exact coefficientRules_comp (L' := D.L₂) D.ι₂
      (coefficientRules_symb D.T₂ Rev (apk W) hev.1 hev.2.1 D.apEven₂ hev.2.2)
  case h11 =>
    obtain ⟨U, hUne, hUgood, hUev⟩ := hwit
    obtain ⟨β, hβ⟩ := label_type_stabilizes W.stages
      (fun θ => fun q : U => legBit ((q : ℕ) : ℤ) (D.ℓ₀ θ))
    let Γ₁ : Config D.L₁ :=
      ⟨U, fun q => (sqClassOf D.m₁ q, if h : q ∈ U then β ⟨q, h⟩ else 0), fun v w => legBit v w⟩
    have hreal : ∀ θ, (∀ q ∈ U, q ≠ D.ℓ₀ θ) →
        (fun q : U => legBit ((q : ℕ) : ℤ) (D.ℓ₀ θ)) = β → IsReal (D.T₁ θ) Γ₁ id := by
      intro θ hne hb
      refine ⟨Set.injOn_id _, fun v hv => ⟨⟨(hUgood v hv).1, ?_⟩, ?_⟩, fun v _ w _ _ => rfl⟩
      · rw [D.T₁_m]
        exact Nat.Coprime.mul_right (hUgood v hv).2
          ((Nat.coprime_primes (hUgood v hv).1 (D.ℓ₀_prime θ)).mpr (hne v hv))
      · have hbv := congrFun hb ⟨v, hv⟩
        simp only [Γ₁, id, D.T₁_typ, dite_eq_left hv]
        exact Prod.ext rfl hbv
    have hevt := (hUev.and hβ).and (hodd U.card)
    obtain ⟨θ₀, hθ₀⟩ := hevt.exists
    have hcomp : Γ₁.Compatible D.ε₁ :=
      compatible_of_real (D.T₁ θ₀) (hreal θ₀ hθ₀.1.1.1 hθ₀.1.2)
    refine ⟨Γ₁, hcomp, hUne, ?_⟩
    filter_upwards [hevt] with θ hθ
    rw [stageSymbol_eq_reading (D.T₁ θ) (Rodd W θ) hθ.2.1 hcomp (Nat.le_succ _)
      (hreal θ hθ.1.1.1 hθ.1.2)]
    simpa [Γ₁] using hθ.1.1.2
  case h12 =>
    intro Γ _ hev1
    obtain ⟨θ, hθ⟩ := hev1.exists
    obtain ⟨f, hf⟩ := stageSymbol_realized hθ
    have hR := stageSymbol_reads hθ hf
    obtain ⟨hadm, -⟩ := rodd_eq_one hR
    obtain ⟨-, hsq₁, hsqℓ⟩ := hofilt θ _ hadm
    exact D.total_eq_zero_odd hf hsq₁ hsqℓ
  case h13 =>
    intro Γ hΓ
    exact D.even_unit_total hefilt Γ hΓ
  case h14 =>
    obtain ⟨Sev, hS⟩ := hseed
    refine ⟨Sev, fun hno => hS fun U hUne hU => ?_⟩
    by_contra hne
    have h1 : Rev U = 1 := zmod2_eq_one_of_ne_zero hne
    have hreal := D.evenConfig_real hU
    have hc : ((D.evenConfig U).mapType (L' := SqClass D.m₂) D.ι₂).Compatible
        (signChar D.m₂ D.four₂) := compatible_of_real D.T₂ hreal
    apply hno
    refine ⟨D.evenConfig U, ⟨hc, ?_⟩, hUne⟩
    show symb D.T₂ Rev ((D.evenConfig U).mapType D.ι₂) = 1
    rw [symb_eq D.T₂ Rev (hev.1 U.card) hc le_rfl hreal]
    simpa [LabelData.evenConfig, Config.mapType] using h1
  case h15 =>
    intro θ b Γ act' hΓ hact
    exact exists_family_realizesAt D.m_pos D.four (D.ℓ₀_prime θ) (D.ℓ₀_cop θ) W.S b Γ hΓ act' hact
  case h16 =>
    intro θ Δ D' _ hR
    refine ⟨realizesAt_omega hR, fun ht => ?_⟩
    obtain ⟨hpos, hsq, -⟩ := realizesAt_total_zero D.four (D.ℓ₀_prime θ) hR ht
    obtain ⟨hsf, havoid, -⟩ := realizesAt_squarefree_coprime hR
    exact hprep D' hpos hsf hsq havoid
  case h17 =>
    intro θ T Wb Δ D' _ hR _ _ _ _ _ _ hA
    obtain ⟨f, _, hDf, hcard, _, hodd', -⟩ := realizesAt_readings (D.ℓ₀_prime θ) hR
    have hreal := hodd' D.m₁ D.dvd₁ D.ε₁ (D.T₁ θ) (D.T₁_m θ) (D.T₁_typ θ)
    have h1 := stageSymbol_reads hA hreal
    obtain ⟨hadm, hval⟩ := rodd_eq_one h1
    obtain ⟨-, hsq, -⟩ := hofilt θ _ hadm
    have hcop : ∀ q ∈ Δ.V.image f, Nat.Coprime q D.m₁ := by
      intro q hq
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      have := (hreal.2.1 v hv).1.2
      rw [D.T₁_m] at this
      exact Nat.Coprime.coprime_mul_right_right this
    have hD' : D' = ∏ q ∈ Δ.V.image f, (q : ℤ) :=
      hDf.trans (prod_qstar_of_isSquare D.four₁ hcop hsq)
    have hω : (AppGEndpoints.omega D' : ℤ) = ((Δ.V.image f).card : ℤ) := by
      rw [realizesAt_omega hR, hcard]
    refine ⟨hD' ▸ hadm, ?_⟩
    rw [hω, hD']
    exact hval
  case h18 =>
    intro θ Δ D' _ hR hA
    obtain ⟨f, _, hDf, hcard, hK, -, heven⟩ := realizesAt_readings (D.ℓ₀_prime θ) hR
    have hreal := heven D.m₂ D.dvd₂ _ D.T₂ D.T₂_m D.T₂_typ (D.ι₂.comp D.π₂)
      (fun x => kSplitProj_coe D.dvd₂ D.kdvd x.1)
    have hc := compatible_of_real D.T₂ hreal
    have h1 : Rev (Δ.V.image f) = 1 := by
      have := symb_eq D.T₂ Rev (hev.1 Δ.V.card) hc le_rfl hreal
      exact this.symm.trans hA
    have hgood : ∀ q ∈ Δ.V.image f, q.Prime ∧ Nat.Coprime q D.m₂ ∧ jacobiSym W.kfin q = 1 := by
      intro q hq
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hp, hc'⟩ := (hreal.2.1 v hv).1
      rw [D.T₂_m] at hc'
      exact ⟨hp, hc', hK v hv⟩
    have hsq := hefilt _ (fun q hq => ⟨(hgood q hq).1, (hgood q hq).2.1⟩) h1
    have hD' : D' = ∏ q ∈ Δ.V.image f, (q : ℤ) :=
      hDf.trans (prod_qstar_of_isSquare D.four₂ (fun q hq => (hgood q hq).2.1) hsq)
    have hω : (AppGEndpoints.omega D' : ℤ) = ((Δ.V.image f).card : ℤ) := by
      rw [realizesAt_omega hR, hcard]
    obtain ⟨hL, hv⟩ := hCe _ hgood h1
    rw [hω, hD']
    exact ⟨hL, hv⟩

/-! ## Non-vacuity of the label data -/

/-- **Label data exist** for every `ℓ > 0` and `k ≠ 0` (PROVED): `m₁ = 24ℓ`, `m₂ = 24|k|ℓ`,
`m = m₁m₂`, and `ℓ₀ θ` a prime larger than `m`. -/
theorem LabelData.nonempty {ℓ : ℕ} (W : WData ℓ) (hℓ : 0 < ℓ) (hk : W.kfin ≠ 0) :
    Nonempty (LabelData W) := by
  have hka : 0 < W.kfin.natAbs := Int.natAbs_pos.mpr hk
  obtain ⟨p, hpm, hp⟩ := Nat.exists_infinite_primes ((24 * ℓ) * (24 * W.kfin.natAbs * ℓ) + 1)
  refine ⟨⟨(24 * ℓ) * (24 * W.kfin.natAbs * ℓ), 24 * ℓ, 24 * W.kfin.natAbs * ℓ,
    (by positivity), (by positivity), (by positivity), Dvd.intro _ rfl, Dvd.intro_left _ rfl,
    ⟨6 * ℓ, by ring⟩, ⟨6 * W.kfin.natAbs * ℓ, by ring⟩, ⟨3 * ℓ, by ring⟩,
    ⟨3 * W.kfin.natAbs * ℓ, by ring⟩, ⟨6 * ℓ, by ring⟩,
    fun q hq hd => ?_, fun q hq hd => ?_, fun _ => p, fun _ => hp, fun _ => ?_⟩⟩
  · have : 6 * ((ℓ : ℤ)).natAbs ∣ 24 * ℓ := ⟨4, by simp; ring⟩
    exact hd.trans this
  · have : 6 * (W.kfin * ℓ).natAbs ∣ 24 * W.kfin.natAbs * ℓ :=
      ⟨4, by rw [Int.natAbs_mul]; simp; ring⟩
    exact hd.trans this
  · exact (Nat.coprime_of_lt_prime (by positivity) (by omega) hp)

/-! ## The `K`-split seed input is not satisfied by a trivial reading -/

/-- A prime outside the odd support does not divide `2ℓ` (PROVED: the primes of `6ℓ` divide
`m₁`). -/
theorem LabelData.not_dvd_two_mul {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) {q₀ : ℕ}
    (hq₀ : q₀.Prime) (hq₀m₁ : ¬ q₀ ∣ D.m₁) : ¬ q₀ ∣ 2 * ℓ := by
  intro hdvd
  apply hq₀m₁ (D.bad₁ q₀ hq₀ ?_)
  have h2 : (q₀ : ℤ) ∣ 2 * (ℓ : ℤ) := by exact_mod_cast hdvd
  have h6 : (q₀ : ℤ) ∣ 6 * (ℓ : ℤ) := h2.trans ⟨3, by ring⟩
  have := Int.natAbs_dvd_natAbs.mpr h6
  simpa [Int.natAbs_mul] using this

/-- **The `K`-split seed input forces a nonempty `K`-split unit of the even reading** (PROVED from
lane RC3's `KSplit.ksplit_seed_b3`: the App G congruence fails at a fresh `K`-split prime with
`v₂(p + 1 − a_p(E^{(k)})) = 2`, tex 2643–2653, 10482–10500). In particular the input `KSplitSeed`
is not satisfied by the zero reading (`not_kSplitSeed_zero`): the inputs of
`addressPackageStaged_of_genuine` are not jointly trivial. -/
theorem exists_unit_of_kSplitSeed {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    {Rev : Finset ℕ → ZMod 2} (hℓ : Adm ℓ) (hk : Odd W.kfin) (hksf : Squarefree W.kfin)
    (hfresh : FreshPrime W D) (hseed : KSplitSeed W D Rev) :
    ∃ U : Finset ℕ, U.Nonempty ∧
      (∀ q ∈ U, q.Prime ∧ Nat.Coprime q D.m₂ ∧ jacobiSym W.kfin q = 1) ∧ Rev U = 1 := by
  obtain ⟨q₀, hq₀, hq₀k, hq₀m₁⟩ := hfresh
  obtain ⟨Sev, hS⟩ := hseed
  by_contra hno
  refine KSplit.ksplit_seed_b3 hℓ hk hksf hq₀ hq₀k (D.not_dvd_two_mul hq₀ hq₀m₁) Sev
    (∀ U : Finset ℕ, U.Nonempty →
      (∀ q ∈ U, q.Prime ∧ Nat.Coprime q D.m₂ ∧ jacobiSym W.kfin q = 1) → Rev U = 0) hS ?_
  intro U hU hq
  by_contra hne
  exact hno ⟨U, hU, hq, zmod2_eq_one_of_ne_zero hne⟩

/-- **The zero reading does not satisfy the `K`-split seed input** (PROVED). -/
theorem not_kSplitSeed_zero {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) (hℓ : Adm ℓ)
    (hk : Odd W.kfin) (hksf : Squarefree W.kfin) (hfresh : FreshPrime W D) :
    ¬ KSplitSeed W D (fun _ => 0) := fun h => by
  obtain ⟨U, -, -, h1⟩ := exists_unit_of_kSplitSeed D hℓ hk hksf hfresh h
  exact absurd h1 (by decide)

end ZInQ.Manuscript.RC.AddressGenuine

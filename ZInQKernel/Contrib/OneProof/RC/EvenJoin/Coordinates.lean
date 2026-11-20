import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Joined
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Descent

/-! Per-set coordinate descent through a supplied constituent inventory. The moving
block and the unary blocks are descended in their own level and character sectors. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion ModularForm O12 PrintsAnalytic ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped BigOperators ModularForm

private theorem map_moving {K : Type} [Field K] (κ : K →+* ℂ)
    (a phase : ℕ → K) (J : List ℕ) (n : ℕ) :
    κ (TL phase J a n) = TL (fun p => κ (phase p)) J (fun k => κ (a k)) n := by
  induction J generalizing n with
  | nil => rfl
  | cons p J ih =>
    simp only [TL_cons, Odd.Top, map_sub, map_mul, ih]
    unfold Odd.divCoeff
    split_ifs <;> simp [ih]

private theorem map_unary {K : Type} [Field K] (κ : K →+* ℂ)
    (good : ℕ → Prop) (phase : ℕ → K) (i : Fin 2) (j n : ℕ) :
    κ (unaryCoeff good phase i j n) = unaryCoeff good (fun p => κ (phase p)) i j n := by
  classical
  unfold unaryCoeff
  split <;> simp

private theorem map_theta {K : Type} [Field K] (κ : K →+* ℂ) (a : ℕ → K) (n : ℕ) :
    κ (timesTheta a n) = timesTheta (fun k => κ (a k)) n := by
  simp only [timesTheta, map_add, map_mul, map_sum, map_ofNat]

private theorem moving_zero {K : Type} [Field K] (phase a : ℕ → K) (J : List ℕ)
    (ha : a 0 = 0) : TL phase J a 0 = 0 := by
  induction J with
  | nil => exact ha
  | cons p J ih => simp [TL_cons, Odd.Top, Odd.divCoeff, ih]

private theorem unary_zero {K : Type} [Field K] (good : ℕ → Prop) (phase : ℕ → K)
    (i : Fin 2) {j : ℕ} (hj : j ≠ 0) : unaryCoeff good phase i j 0 = 0 := by
  unfold unaryCoeff
  rw [dite_eq_right]
  rintro ⟨k, hk, _, he⟩
  exact (Nat.mul_ne_zero hj (pow_ne_zero _ hk)) he.symm

private theorem unitCharacter_lift {K : Type} [Field K] {m : ℕ} (κ : K →+* ℂ)
    (ξ : (ZMod m)ˣ →* ℂˣ) (h : ∀ u, ∃ a : K, κ a = (ξ u : ℂ)) :
    ∃ χ : (ZMod m)ˣ →* Kˣ, (Units.map κ).comp χ = ξ := by
  classical
  choose a ha using h
  have hn (u) : a u ≠ 0 := by
    intro h0
    exact (ξ u).ne_zero ((ha u).symm.trans (by simp [h0]))
  let χ : (ZMod m)ˣ →* Kˣ :=
    { toFun := fun u => Units.mk0 (a u) (hn u)
      map_one' := by
        apply Units.ext
        apply κ.injective
        change κ (a 1) = κ 1
        rw [ha, map_one, Units.val_one, map_one]
      map_mul' := fun u v => by
        apply Units.ext
        apply κ.injective
        change κ (a (u * v)) = κ (a u * a v)
        rw [map_mul κ, ha, ha, ha, map_mul ξ, Units.val_mul] }
  refine ⟨χ, ?_⟩
  apply MonoidHom.ext
  intro u
  apply Units.ext
  exact ha u

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

private theorem movingCharacter_lift (C : SourceAtPlace P O K) (hS : SupportSpec W)
    (κ : K →+* ℂ) (hκ : κ.comp C.eK = C.eC) {U : Finset ℕ}
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    {ξ : DirichletCharacter ℂ (movingLevel P U)} (hξ : IsMovingCharacter P U ξ) :
    ∃ χ : (ZMod (movingLevel P U))ˣ →* Kˣ, (Units.map κ).comp χ = ξ.toUnitHom := by
  classical
  have hm : P.phaseData.N ∣ maskedLevel P :=
    (dvd_mul_right _ _).trans (dvd_pow_self _ (by decide))
  have hne : movingLevel P U ≠ 0 := by
    exact Nat.mul_ne_zero
      (pow_ne_zero _ (Nat.mul_ne_zero (even_level_ne_zero P) (conductor_pos hS.1).ne'))
      (Finset.prod_ne_zero_iff.mpr fun p hp => (hU p hp).1.ne_zero)
  let : NeZero (movingLevel P U) := ⟨hne⟩
  apply unitCharacter_lift κ
  intro u
  let n := (u : ZMod (movingLevel P U)).val
  have hn : n.Coprime (movingLevel P U) := ZMod.val_coe_unit_coprime u
  have hnN := hn.of_dvd_right (hm.trans (dvd_mul_right _ _))
  have hψ : P.phaseData.ψ n = P.phaseData.η n := by
    have h := P.phaseData.hψη n hnN
    simpa [kronecker, kroneckerTwo] using h.symm
  refine ⟨C.eK (C.η₀ n) * ∏ p ∈ U, (kronecker (p : ℤ) n : K), ?_⟩
  have hu : (n : ZMod (movingLevel P U)) = (u : ZMod (movingLevel P U)) :=
    ZMod.natCast_zmod_val _
  rw [MulChar.coe_toUnitHom, ← hu, hξ n hn]
  have hchange := DirichletCharacter.changeLevel_eq_cast_of_dvd' hm (χ := P.phaseData.ψ)
    (a := (n : ℤ)) ((hn.of_dvd_right (dvd_mul_right _ _)).isCoprime)
  simp only [Int.cast_natCast, hψ] at hchange
  have hmask : maskedCharacter P n = P.phaseData.η n := hchange
  rw [hmask, map_mul, map_prod, ← RingHom.comp_apply, hκ, C.complex_eta]
  simp only [map_intCast]

private theorem unaryCharacter_lift (C : SourceAtPlace P O K) (hS : SupportSpec W)
    (κ : K →+* ℂ) (hκ : κ.comp C.eK = C.eC) (i : Fin 2) {j : ℕ} (hj : j ≠ 0)
    {ξ : DirichletCharacter ℂ (maskedLevel P * j)} (hξ : IsUnaryCharacter P i j ξ) :
    ∃ χ : (ZMod (maskedLevel P * j))ˣ →* Kˣ, (Units.map κ).comp χ = ξ.toUnitHom := by
  have : NeZero (maskedLevel P * j) :=
    ⟨Nat.mul_ne_zero
      (pow_ne_zero _ (Nat.mul_ne_zero (even_level_ne_zero P) (conductor_pos hS.1).ne')) hj⟩
  apply unitCharacter_lift κ
  intro u
  let n := (u : ZMod (maskedLevel P * j)).val
  have hn : n.Coprime (maskedLevel P * j) := ZMod.val_coe_unit_coprime u
  have hu : (n : ZMod (maskedLevel P * j)) = (u : ZMod (maskedLevel P * j)) :=
    ZMod.natCast_zmod_val _
  refine ⟨C.eK (C.η₀ n) * (jacobiSym (-1) n : K) ^ i.val * (kronecker (-(j : ℤ)) n : K), ?_⟩
  rw [MulChar.coe_toUnitHom, ← hu, hξ n hn]
  simp only [map_mul, map_pow, map_intCast, ← RingHom.comp_apply, hκ, C.complex_eta]

private theorem blockCoordinates {I J : Type} [Fintype I]
    {L₀ : Type} [AddCommGroup L₀] {ε : L₀ →+ ZMod 2} {T : TypeData L₀ ε}
    {N m : ℕ} {avoid : Finset ℕ} (Y : Inventory I J K T N)
    (hc : ∀ q, Test T avoid q → q.Coprime N)
    (κ : K →+* ℂ) (hspan : SpansOverComplex Y κ) (hm : m ∣ N)
    {ξ : (ZMod m)ˣ →* ℂˣ} {χ : (ZMod m)ˣ →* Kˣ}
    (hχ : (Units.map κ).comp χ = ξ)
    (a : ℕ → K) (ha : a 0 = 0) (f : WeightTwo m) (hf : f ∈ modFormCharSpace 2 ξ)
    (hq : ∀ n, (qExpansion 1 f).coeff n = κ (a n)) :
    ∃ v : I → K, (∀ n, (Y.toBasis hc).eval n v = a n) ∧
      ∀ b, v b ≠ 0 → Y.level b ∣ m ∧ Y.χ (Y.origin b) = χ.comp (ZMod.unitsMap hm) := by
  apply coordinates_of_span Y hc
  apply spansAt_of_complex Y κ hspan m hm _ a ha
  exact ⟨ξ, f, by rw [← hχ, MonoidHom.comp_assoc], hf, fun n _ => hq n⟩

/-- Over a supplied inventory the actual moving and unary blocks have
coordinates over the source's coefficient place, supported in their intrinsic
levels and characters. Their formal combination evaluates to the actual form. -/
theorem evenCoordinates {I J : Type} [Fintype I] {N : ℕ} {avoid : Finset ℕ}
    (C : SourceAtPlace P O K) (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (Y : Inventory I J K (evenTypes W.S hS.1) N) (hm : movingLevel P U ∣ N)
    (hc : ∀ q, Test (evenTypes W.S hS.1) avoid q → q.Coprime N)
    (κ : K →+* ℂ) (hκ : κ.comp C.eK = C.eC) (hspan : SpansOverComplex Y κ) :
    let phase := fun p => C.eK (C.η₀ p)
    let a := fun n => C.eK (C.c n)
    let raw := TL phase U.toList a
    let good := (evenTypes W.S hS.1).Good
    ∃ (χB : (ZMod (movingLevel P U))ˣ →* Kˣ)
      (χJ : ∀ j : ↥(subscripts U), (ZMod (maskedLevel P * j.val))ˣ →* Kˣ)
      (b : I → K) (u : ↥(subscripts U) → I → K),
      (∀ n, (Y.toBasis hc).eval n b = timesTheta raw n) ∧
      (∀ j n, (Y.toBasis hc).eval n (u j) = timesTheta (unaryCoeff good phase i j.val) n) ∧
      (∀ x, b x ≠ 0 → Y.level x ∣ movingLevel P U ∧
        Y.χ (Y.origin x) = χB.comp (ZMod.unitsMap hm)) ∧
      (∀ j x, u j x ≠ 0 → Y.level x ∣ maskedLevel P * j.val ∧
        Y.χ (Y.origin x) = (χJ j).comp (ZMod.unitsMap ((unaryLevel_dvd P U j).trans hm))) ∧
      ∀ n, κ ((Y.toBasis hc).eval n
        ((2 : K) ^ (-(P.δ + U.card + 1)) •
          (b - ∑ j : ↥(subscripts U), raw j.val • u j))) =
        (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n := by
  classical
  dsimp only
  let phase : ℕ → K := fun p => C.eK (C.η₀ p)
  let a : ℕ → K := fun n => C.eK (C.c n)
  let raw := TL phase U.toList a
  let good := (evenTypes W.S hS.1).Good
  have hη (p : ℕ) : κ (phase p) = P.phaseData.η p := by
    rw [← RingHom.comp_apply, hκ, C.complex_eta]
  have ha (n : ℕ) : κ (a n) = P.sievedCoeff n := by
    rw [← RingHom.comp_apply, hκ, C.complex_coeff]
  have hz : a 0 = 0 := κ.injective (by rw [ha, map_zero]; simp [EvenSource.sievedCoeff])
  have hj (j : ↥(subscripts U)) : j.val ≠ 0 :=
    ((mem_subscripts (fun p hp => (hU p hp).1) j.val).mp j.property).1.ne_zero
  obtain ⟨ξB, ξJ, fB, fJ, _, _, hξB, hξJ, hfB, hfJ, _, hqB, hqJ, _⟩ :=
    evenWeightTwo hS i U hU (EvenMoving.evenMovingSieve P hS U hU) hodd
      (fun j hj' => EvenUnary.evenUnaryStageLaw P hS i (Nat.pos_of_ne_zero (hj ⟨j, hj'⟩)))
  obtain ⟨χB, hχB⟩ := movingCharacter_lift C hS κ hκ hU hξB
  have hχJ' (j : ↥(subscripts U)) := unaryCharacter_lift C hS κ hκ i (hj j) (hξJ j)
  choose χJ hχJ using hχJ'
  obtain ⟨b, hb, hb'⟩ := blockCoordinates Y hc κ hspan hm hχB (timesTheta raw)
    (by simpa [timesTheta, raw] using moving_zero phase a U.toList hz) fB hfB (fun n => by
      rw [hqB, map_theta]
      simp only [raw, map_moving, hη, ha])
  have hu' (j : ↥(subscripts U)) :=
    blockCoordinates Y hc κ hspan ((unaryLevel_dvd P U j).trans hm) (hχJ j)
      (timesTheta (unaryCoeff good phase i j.val))
      (by simpa [timesTheta] using unary_zero good phase i (hj j)) (fJ j) (hfJ j) (fun n => by
        rw [hqJ, map_theta]
        simp only [map_unary, hη, good])
  choose u hu hu_support using hu'
  refine ⟨χB, χJ, b, u, hb, hu, hb', hu_support, fun n => ?_⟩
  let un (j : ℕ) : I → K := if hj' : j ∈ subscripts U then u ⟨j, hj'⟩ else 0
  have hun (j : ℕ) (hj' : j ∈ subscripts U) :
      un j = u ⟨j, hj'⟩ := dite_eq_left hj'
  have hsum : (∑ j : ↥(subscripts U), raw j.val • u j) =
      ∑ j ∈ subscripts U, raw j • un j := by
    rw [← Finset.sum_attach (subscripts U) (fun j => raw j • un j), Finset.univ_eq_attach]
    exact Finset.sum_congr rfl fun j _ => by rw [hun j.val j.property]
  change κ ((Y.toBasis hc).eval n
    ((2 : K) ^ (-(P.δ + U.card + 1)) • (b - ∑ j : ↥(subscripts U), raw j.val • u j))) = _
  rw [hsum, evenVector_eval _ good phase a P.δ i U b un hb
    (fun j hj' n => by rw [hun j hj']; exact hu ⟨j, hj'⟩ n) n, joinedForm_coeff]
  rw [map_theta]
  congr 1
  funext k
  simp only [halfDivided, map_mul, map_zpow₀, map_ofNat,
    map_rawNumerator_scaled κ hη (fun n => (ha n).trans (one_mul _).symm), one_mul, good]


section Seed

variable {I J : Type} [Fintype I] {N : ℕ} {avoid : Finset ℕ}
variable (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (C : SourceAtPlace P O K)
variable (Y : Inventory I J K (evenTypes W.S hS.1) N) (hm : movingLevel P U ∣ N)
variable (hc : ∀ q, Test (evenTypes W.S hS.1) avoid q → q.Coprime N)
variable (κ : K →+* ℂ) (hκ : κ.comp C.eK = C.eC) (hspan : SpansOverComplex Y κ)

include hκ hm hspan in
private theorem exists_evenSeed :
    ∃ v : I → K, ∀ n, κ ((Y.toBasis hc).eval n v) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n := by
  obtain ⟨_, _, b, u, _, _, _, _, hv⟩ :=
    evenCoordinates C hS i U hU hodd Y hm hc κ hκ hspan
  exact ⟨_, hv⟩

/-- The coordinates of the joined form in the supplied inventory. -/
def evenSeed : I → K :=
  (exists_evenSeed hS i U hU hodd C Y hm hc κ hκ hspan).choose

theorem evenSeed_eval (n : ℕ) :
    κ ((Y.toBasis hc).eval n (evenSeed hS i U hU hodd C Y hm hc κ hκ hspan)) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n :=
  (exists_evenSeed hS i U hU hodd C Y hm hc κ hκ hspan).choose_spec n

end Seed

variable (hS : SupportSpec W) {B : ℕ} [NeZero (conductor W.S)]
variable {X : Model P hS B}

/-- A column comparison and a constructor's seed identity suffice for the
model match; the Fourier family is already compatible with the lattice. -/
theorem coordinate_match_of_seed {I J : Type} [Fintype I] {N : ℕ} {avoid : Finset ℕ}
    (A : FourierData X) (C : SourceAtPlace P X.O X.K)
    (i : Fin 2) (U : Finset ℕ) (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (Y : Inventory I J X.K (evenTypes W.S hS.1) N) (hm : movingLevel P U ∣ N)
    (hc : ∀ q, Test (evenTypes W.S hS.1) avoid q → q.Coprime N)
    (κ : X.K →+* ℂ) (hκ : κ.comp C.eK = C.eC) (hspan : SpansOverComplex Y κ)
    (ι : (I → X.K) →ₗ[X.K] (X.I → X.K))
    (hcolumn : ∀ v n, X.coefK (ι v) (A.index n) = (Y.toBasis hc).eval n.val v)
    (hseed : (X.F U).val = ι (evenSeed hS i U hU hodd C Y hm hc κ hκ hspan)) :
    ∀ n, n ≠ 0 →
      κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
        (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n := by
  intro n hn
  rw [← A.expand_coeff (X.F U) ⟨n, hn⟩, X.expand_spec, hseed, hcolumn]
  exact evenSeed_eval hS i U hU hodd C Y hm hc κ hκ hspan n

omit [NeZero (conductor W.S)] in
/-- An operator budget of size at least two includes singletons at
arbitrarily large primes. A single finite Gamma1 level cannot contain
all the intrinsic moving levels. -/
theorem no_common_level (N : ℕ) (hN : 0 < N) (hB : 2 ≤ B) :
    ¬ ∀ U : Finset ℕ, (∀ p ∈ U, (evenTypes W.S hS.1).Good p) →
      U.card + 1 ≤ B → movingLevel P U ∣ N := by
  classical
  intro h
  obtain ⟨p, hpLarge, hp⟩ := Nat.exists_infinite_primes (N + W.S.sup id + 1)
  have hpS : p ∉ W.S := by
    intro hpMem
    have hpLe := Finset.le_sup (f := id) hpMem
    change p ≤ W.S.sup id at hpLe
    omega
  have hU : ∀ q ∈ ({p} : Finset ℕ), (evenTypes W.S hS.1).Good q := by
    intro q hq
    rw [Finset.mem_singleton.mp hq]
    exact (good_iff hS p).mpr ⟨hp, hpS⟩
  have hpLevel : p ∣ movingLevel P {p} := by
    simpa only [movingLevel, Finset.prod_singleton] using dvd_mul_left p (maskedLevel P)
  have hpN := Nat.le_of_dvd hN (hpLevel.trans (h {p} hU (by simpa using hB)))
  omega

end ZInQ.Manuscript.RC.EvenJoin

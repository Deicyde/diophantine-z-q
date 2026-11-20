import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedSeed

/-! The integral diamond calculation on the actual divided vector.
The extra factor of two comes from the difference of two quadratic signs. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion EvenMoving
open IsDedekindDomain ModularForm NumberField PrintsAnalytic ThetaCoeff Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

set_option maxHeartbeats 1200000

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)

private abbrev repr {N : ℕ} (u : (ZMod N)ˣ) := (u : ZMod N).val

private theorem blockChar_on_representative (b : EvenBlock U) (u : (ZMod (movingLevel P U))ˣ) :
    (liftedBlockChar A (evenBlockLevel_dvd (P := P)) b u : ℂ) =
      (A b).χ (repr u : ℕ) := by
  have hu : ZMod.unitOfCoprime (repr u) (ZMod.val_coe_unit_coprime u) = u :=
    Units.ext (by rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val])
  calc
    (liftedBlockChar A (evenBlockLevel_dvd (P := P)) b u : ℂ) =
      (liftedBlockChar A (evenBlockLevel_dvd (P := P)) b
        (ZMod.unitOfCoprime (repr u) (ZMod.val_coe_unit_coprime u)) : ℂ) :=
      congrArg (fun v => (liftedBlockChar A (evenBlockLevel_dvd (P := P)) b v : ℂ)) hu.symm
    _ = _ := by
      simp [liftedBlockChar, ZMod.unitsMap_unitOfCoprime,
        ZMod.coe_unitOfCoprime]

private theorem quadValue (d : ℤ) (n : ℕ) (ho : Odd n) (hc : Nat.Coprime d.natAbs n) :
    (kronecker d n : ℂ) ^ 2 = 1 := by
  rw [kronecker_of_odd d ho]
  have hh : d.gcd n = 1 := hc
  rcases jacobiSym.eq_one_or_neg_one hh with h | h <;> simp [h]

/-- Both block characters have the same phase, times a sign on every
diamond unit. The lifted unary character is evaluated at its own level. -/
theorem even_blockChar_sign (hS : SupportSpec W)
    {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
      (evenBlockSeries P hS i b)}
    (hB : IsMovingCharacter P U (A none).χ)
    (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)
    (b : EvenBlock U) (u : (ZMod (movingLevel P U))ˣ) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (liftedBlockChar A (evenBlockLevel_dvd (P := P)) b u : ℂ) =
        P.phaseData.η (repr u : ℕ) * (s : ℂ) := by
  classical
  let n := repr u
  have hn := ZMod.val_coe_unit_coprime u
  have hmask : n.Coprime (maskedLevel P) := hn.of_dvd_right (dvd_mul_right _ _)
  have hN : P.phaseData.N ∣ maskedLevel P := (dvd_mul_right _ _).trans (dvd_pow_self _ (by decide))
  have hodd : Odd n := Nat.coprime_two_right.mp (hmask.of_dvd_right
    ((by decide : 2 ∣ 4).trans (evenMasked P hS).1))
  have hψ : maskedCharacter P n = P.phaseData.η n := by
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' hN (χ := P.phaseData.ψ)
      (a := (n : ℤ)) hmask.isCoprime
    rw [Int.cast_natCast, Int.cast_natCast] at h
    have hp := P.phaseData.hψη n (hmask.of_dvd_right hN)
    rw [show maskedCharacter P n = P.phaseData.ψ n from h]
    simpa [kronecker, kroneckerTwo] using hp.symm
  have fromSquare (z : ℂ) (hz : z ^ 2 = 1) :
      ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ z = (s : ℂ) := by
    have he : z ^ 2 = (1 : ℂ) ^ 2 := by simpa using hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  rw [blockChar_on_representative]
  cases b with
  | none =>
    change ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (A none).χ (n : ℕ) = P.phaseData.η (n : ℕ) * (s : ℂ)
    have he : (∏ p ∈ U, (kronecker (p : ℤ) n : ℂ)) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      apply Finset.prod_eq_one
      intro p hp
      exact quadValue p n hodd
        ((hn.of_dvd_right ((Finset.dvd_prod_of_mem id hp).trans (dvd_mul_left _ _))).symm)
    obtain ⟨s, hs, heq⟩ := fromSquare _ he
    refine ⟨s, hs, ?_⟩
    calc
      (A none).χ (n : ℕ) = maskedCharacter P n * ∏ p ∈ U, (kronecker (p : ℤ) n : ℂ) :=
        hB n hn
      _ = _ := by rw [hψ, heq]
  | some j =>
    have hc := hn.of_dvd_right (unaryLevel_dvd P U j)
    change ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (A (some j)).χ (n : ℕ) = P.phaseData.η (n : ℕ) * (s : ℂ)
    have he : ((jacobiSym (-1) n : ℂ) ^ i.val * (kronecker (-(j.val : ℤ)) n : ℂ)) ^ 2 = 1 := by
      have h₁ : (jacobiSym (-1) n : ℂ) ^ 2 = 1 := by
        rw [← kronecker_of_odd (-1 : ℤ) hodd]
        exact quadValue (-1 : ℤ) n hodd (Nat.coprime_one_left _)
      have h₂ := quadValue (-(j.val : ℤ)) n hodd
        (by simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
          (hc.of_dvd_right (dvd_mul_left j.val (maskedLevel P))).symm)
      rw [mul_pow, pow_right_comm, h₁, h₂, one_pow, one_mul]
    obtain ⟨s, hs, heq⟩ := fromSquare _ he
    refine ⟨s, hs, ?_⟩
    calc
      (A (some j)).χ (n : ℕ) = P.phaseData.η n * (jacobiSym (-1) n : ℂ) ^ i.val *
        (kronecker (-(j.val : ℤ)) n : ℂ) := hJ j n hc
      _ = _ := by rw [mul_assoc, heq]

variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hκ : D.κ.comp (D.fieldMap.comp C₀.eK) = C₀.eC)
variable (hLi : OldNewIndependenceWeightTwo)
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)

private theorem phase_ring (n : ℕ) :
    algebraMap (FixedRing D.w) (FixedField D.w) (D.ringMap (C₀.η n)) = D.phaseAt C₀ n := by
  rw [D.ringMap_agrees, C₀.integral_eta]
  rfl

include hκ hB hJ in
private theorem block_scalars (u : (ZMod (movingLevel P U))ˣ) :
    ∃ (ψ : FixedRing D.w) (r : ↥(subscripts U) → FixedRing D.w),
      (D.blockChar none u : FixedField D.w) = algebraMap _ _ ψ ∧
      ∀ j, (D.blockChar none u : FixedField D.w) - (D.blockChar (some j) u : FixedField D.w) =
        2 * algebraMap _ _ (r j) := by
  obtain ⟨s, hs, hsu⟩ := even_blockChar_sign hS hB hJ none u
  have hx (b : EvenBlock U) (t : ℤ)
      (ht : (liftedBlockChar A (evenBlockLevel_dvd (P := P)) b u : ℂ) =
        P.phaseData.η (repr u : ℕ) * (t : ℂ)) :
      (D.blockChar b u : FixedField D.w) = D.phaseAt C₀ (repr u) * (t : FixedField D.w) := by
    apply D.κ.injective
    rw [map_mul, map_intCast, D.blockChar_complex, D.phase_complex C₀ hκ, ht]
  let φ := D.ringMap (C₀.η (repr u))
  refine ⟨φ * (s : FixedRing D.w), ?_⟩
  have hj (j : ↥(subscripts U)) : ∃ r : FixedRing D.w,
      (D.blockChar none u : FixedField D.w) - (D.blockChar (some j) u : FixedField D.w) =
        2 * algebraMap _ _ r := by
    obtain ⟨t, ht, htu⟩ := even_blockChar_sign hS hB hJ (some j) u
    rw [hx none s hsu, hx (some j) t htu, ← phase_ring D C₀]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨φ, by simp only [Int.cast_one, Int.cast_neg]; ring⟩
    · exact ⟨-φ, by push_cast; ring⟩
    · exact ⟨0, by simp⟩
  choose r hr using hj
  exact ⟨r, by rw [hx none s hsu, map_mul, map_intCast, phase_ring], hr⟩

include hU in
private theorem scaled_shell (j : ↥(subscripts U)) :
    ∃ x : FixedRing D.w, algebraMap _ (FixedField D.w) x =
      (2 : FixedField D.w) ^ (-(P.δ + U.card)) *
        TL (D.phaseAt C₀) U.toList (D.rawSource C₀) j.val := by
  have hb := raw_bound (source_at_place C₀ hS Subtype.val_injective)
    U.toList U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) j.val
  have hd : (2 : FixedRing v) ^ (P.δ + C₀.k + U.card).toNat ∣
      TL C₀.η U.toList C₀.a j.val :=
    two_pow_dvd_of_le (by simp only [Finset.length_toList]; omega) hb
  obtain ⟨x, hx⟩ := scaled_witness (K := FixedField v) hd
  refine ⟨D.ringMap x, ?_⟩
  let f := D.fieldMap.comp (algebraMap (FixedRing v) (FixedField v))
  have hephase : f ∘ C₀.η = D.phaseAt C₀ := by
    funext n
    exact congrArg D.fieldMap (C₀.integral_eta n)
  have heraw (n : ℕ) : f (C₀.a n) = (2 : FixedField D.w) ^ C₀.k * D.rawSource C₀ n := by
    change D.fieldMap (algebraMap _ _ (C₀.a n)) = _
    rw [C₀.integral_coeff, map_mul, map_zpow₀, map_ofNat]
    rfl
  rw [D.ringMap_agrees, hx, map_mul, map_zpow₀, map_ofNat,
    show D.fieldMap (algebraMap _ _ (TL C₀.η U.toList C₀.a j.val)) =
      f (TL C₀.η U.toList C₀.a j.val) by rfl,
    TL_map_scaled f C₀.η C₀.a _ _ heraw, hephase, ← mul_assoc,
    ← zpow_add₀ (by norm_num : (2 : FixedField D.w) ≠ 0)]
  congr 2
  omega

private theorem unary_integral (j : ↥(subscripts U)) (n : ℕ) :
    (D.evenBasis hU hLi).eval n (D.vectors hU hLi C₀ hκ (some j)) =
      algebraMap (FixedRing D.w) (FixedField D.w)
        (D.ringMap (timesTheta (unaryCoeff (evenTypes W.S hS.1).Good C₀.η i j.val) n)) := by
  let f := D.fieldMap.comp (algebraMap (FixedRing v) (FixedField v))
  have hphase : f ∘ C₀.η = D.phaseAt C₀ := by
    funext k
    exact congrArg D.fieldMap (C₀.integral_eta k)
  rw [(D.vectors_spec hU hLi C₀ hκ).1 (some j), D.ringMap_agrees]
  change timesTheta (unaryCoeff (evenTypes W.S hS.1).Good (D.phaseAt C₀) i j.val) n =
    f (timesTheta (unaryCoeff (evenTypes W.S hS.1).Good C₀.η i j.val) n)
  simp only [timesTheta_map_ringHom, unaryCoeff_map_ringHom, hphase]

include hB hJ in
private theorem diamond_seed_vector (u : (ZMod (movingLevel P U))ˣ) :
    ∃ (ψ : FixedRing D.w) (c : ↥(subscripts U) → FixedRing D.w),
      (D.blockChar none u : FixedField D.w) = algebraMap _ _ ψ ∧
      (D.evenBasis hU hLi).diamond u (D.seed hU hLi C₀ hκ) =
        (algebraMap (FixedRing D.w) (FixedField D.w) ψ) • D.seed hU hLi C₀ hκ +
          ∑ j : ↥(subscripts U), (algebraMap (FixedRing D.w) (FixedField D.w) (c j)) •
            D.vectors hU hLi C₀ hκ (some j) := by
  classical
  obtain ⟨ψ, r, hψ, hr⟩ := block_scalars D C₀ hκ hB hJ u
  choose x hx using scaled_shell hU D C₀
  let O := FixedRing D.w
  let K := FixedField D.w
  let z := D.vectors hU hLi C₀ hκ
  let t : K := (2 : K) ^ (-(P.δ + U.card + 1))
  let raw := TL (D.phaseAt C₀) U.toList (D.rawSource C₀)
  let ch (b : EvenBlock U) : K := D.blockChar b u
  let φ : O →+* K := algebraMap O K
  have he (b : EvenBlock U) :
      (D.evenBasis hU hLi).diamond u (z b) = ch b • z b :=
    diamond_of_coordinates _ _ (fun x hx => ((D.vectors_spec hU hLi C₀ hκ).2 b x hx).2) u
  have ht : (2 : K) * t = (2 : K) ^ (-(P.δ + U.card)) := by
    change (2 : K) * (2 : K) ^ (-(P.δ + U.card + 1)) = _
    calc
      (2 : K) * (2 : K) ^ (-(P.δ + U.card + 1)) =
          (2 : K) ^ (1 : ℤ) * (2 : K) ^ (-(P.δ + U.card + 1)) := by rw [zpow_one]
      _ = _ := by
        rw [← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
        congr 1
        omega
  have hseed : D.seed hU hLi C₀ hκ =
      t • (z none - ∑ j : ↥(subscripts U), raw j.val • z (some j)) := by
    unfold PlacedCuspLists.seed placedEvenVector
    rw [← Finset.sum_attach (subscripts U), Finset.univ_eq_attach]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by rw [dite_eq_left j.property]
  refine ⟨ψ, fun j => x j * r j, hψ, ?_⟩
  rw [hseed, map_smul, map_sub, map_sum, he none, ← hψ]
  simp only [map_smul, he, smul_sub, Finset.smul_sum, smul_smul]
  have hterm (j : ↥(subscripts U)) :
      (t * (ch none * raw j.val)) • z (some j) -
        (t * (raw j.val * ch (some j))) • z (some j) =
        φ (x j * r j) • z (some j) := by
    rw [← sub_smul]
    congr 1
    rw [map_mul, hx j]
    have hdiff : ch none - ch (some j) = 2 * φ (r j) := hr j
    calc
      t * (ch none * raw j.val) - t * (raw j.val * ch (some j)) =
        (t * raw j.val) * (ch none - ch (some j)) := by ring
      _ = ((2 : K) * t) * raw j.val * φ (r j) := by rw [hdiff]; ring
      _ = _ := by rw [ht]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hterm j)
  rw [Finset.sum_sub_distrib] at hsum
  rw [← hsum]
  change (t * ch none) • z none - (∑ j : ↥(subscripts U),
    (t * (raw j.val * ch (some j))) • z (some j)) =
      (ch none * t) • z none - (∑ j : ↥(subscripts U),
        (ch none * (t * raw j.val)) • z (some j)) +
        ((∑ j : ↥(subscripts U), (t * (ch none * raw j.val)) • z (some j)) -
          ∑ j : ↥(subscripts U), (t * (raw j.val * ch (some j))) • z (some j))
  rw [mul_comm (ch none) t]
  simp only [← mul_assoc, mul_comm (ch none) t]
  abel

include hB hJ in
/-- Every diamond translate has integral coefficients, and its correction
is an integral linear combination of the separately undivided unary blocks. -/
theorem placed_diamond_eval (u : (ZMod (movingLevel P U))ˣ)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) :
    ∃ (ψ : FixedRing D.w) (c : ↥(subscripts U) → FixedRing D.w),
      (D.blockChar none u : FixedField D.w) = algebraMap _ _ ψ ∧ ∀ n,
      (D.evenBasis hU hLi).eval n ((D.evenBasis hU hLi).diamond u (D.seed hU hLi C₀ hκ)) =
        algebraMap (FixedRing D.w) (FixedField D.w)
          (ψ * D.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n) +
            ∑ j : ↥(subscripts U), c j * D.ringMap
              (timesTheta (unaryCoeff (evenTypes W.S hS.1).Good C₀.η i j.val) n)) := by
  obtain ⟨ψ, c, hψ, he⟩ := diamond_seed_vector hU D C₀ hκ hLi hB hJ u
  refine ⟨ψ, c, hψ, fun n => ?_⟩
  rw [he, map_add, map_smul, D.seed_integral hU hLi C₀ hκ hodd, map_add, map_mul]
  simp only [map_sum, map_smul, smul_eq_mul, unary_integral hU D C₀ hκ hLi, map_mul]

end ZInQ.Manuscript.RC.EvenJoin

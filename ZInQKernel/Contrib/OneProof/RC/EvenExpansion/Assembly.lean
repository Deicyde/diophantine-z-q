import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Mask
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Operators
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Ordinary
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Unary
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Realization
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Compare
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Fourier
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Cusps.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Degeneracy
import Mathlib.NumberTheory.ModularForms.NormTrace

/-! The fixed even operator set and its actual theta products. The half-integral
transformation inputs end before weight two and before constituent coordinates. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

open AddressGenuine AuxInputs BlocksPerU CongruenceSubgroup EvenBudget Matrix.SpecialLinearGroup
open ModularForm O12 PrintsAnalytic ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53
open scoped BigOperators MatrixGroups ModularForm

set_option maxHeartbeats 800000

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}

/-- The common Gamma1 level of the theta products for this particular operator set. -/
def movingLevel (P : EvenSource W L τ) (U : Finset ℕ) : ℕ :=
  maskedLevel P * ∏ p ∈ U, p

/-- Holomorphic weight two at the indicated Gamma1 level. -/
abbrev WeightTwo (m : ℕ) := ModularForm ((Gamma1 m).map (mapGL ℝ)) 2

/-- The moving character evaluated on the units of the common level. -/
def IsMovingCharacter (P : EvenSource W L τ) (U : Finset ℕ)
    (χ : DirichletCharacter ℂ (movingLevel P U)) : Prop :=
  ∀ n : ℕ, n.Coprime (movingLevel P U) →
    χ n = maskedCharacter P n * ∏ p ∈ U, (kronecker (p : ℤ) n : ℂ)

/-- The unary character evaluated on the units of the intrinsic level. -/
def IsUnaryCharacter (P : EvenSource W L τ) (i : Fin 2) (j : ℕ)
    (χ : DirichletCharacter ℂ (maskedLevel P * j)) : Prop :=
  ∀ n : ℕ, n.Coprime (maskedLevel P * j) →
    χ n = P.phaseData.η n * (jacobiSym (-1) n : ℂ) ^ i.val * (kronecker (-(j : ℤ)) n : ℂ)

/-- The remaining moving transformation on one exact half-integral series at
its intrinsic level. The character is specified on every unit. -/
def EvenMovingSieveLaw (P : EvenSource W L τ) (U : Finset ℕ) : Prop :=
  ∃ χ : DirichletCharacter ℂ (movingLevel P U),
    IsMovingCharacter P U χ ∧
    HasThreeHalvesExpansion (RingHom.id ℂ) (movingLevel P U) χ.toUnitHom
      (TL (fun p => P.phaseData.η p) U.toList P.sievedCoeff)

/-- The remaining unary Poisson law for one shell, at its intrinsic old
level times the shell index. The parity premise is on the character at -1. -/
def EvenUnaryStageLaw (P : EvenSource W L τ) (hS : SupportSpec W) (i : Fin 2) (j : ℕ) : Prop :=
  P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1 →
  ∃ χ : DirichletCharacter ℂ (maskedLevel P * j),
    IsUnaryCharacter P i j χ ∧
    HalfIntegralThreeHalves (maskedLevel P * j) χ.toUnitHom
      (unaryFun (evenTypes W.S hS.1).Good P.phaseData.η i j)

/-- Missing single-prime comparison for the actual dilation and additive
average. The coefficient calculation `movingOp_series` is already proved.
The scalar is the input character times the new quadratic character. -/
def MovingStepLaw (M p : ℕ) [NeZero p] (χ : DirichletCharacter ℂ M) (phase : ℂ)
    (g : ℍ → ℂ) : Prop :=
  ∃ ξ : DirichletCharacter ℂ (M * p),
    (∀ n : ℕ, n.Coprime (M * p) → ξ n = χ n * (kronecker (p : ℤ) n : ℂ)) ∧
      HalfIntegralThreeHalves (M * p) ξ.toUnitHom (movingOp p phase g)

/-- The moving law at the empty operator set is the actual masked App E form. -/
theorem moving_nil (P : EvenSource W L τ) (hS : SupportSpec W) :
    EvenMovingSieveLaw P ∅ := by
  have hm : movingLevel P ∅ = maskedLevel P := by simp [movingLevel]
  unfold EvenMovingSieveLaw IsMovingCharacter
  rw [hm]
  simp only [Finset.prod_empty, mul_one, Finset.toList_empty, TL_nil]
  exact ⟨maskedCharacter P, fun _ _ => rfl, evenMasked_expansion P hS⟩

/-- Iterate the single-prime comparison. At each step the prime is fresh
at the level at which its actual operator is applied. -/
theorem moving_of_step (P : EvenSource W L τ) (hS : SupportSpec W) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hstep : ∀ (M p : ℕ) (hp : p.Prime), letI : NeZero p := ⟨hp.ne_zero⟩
      Odd p → 4 ∣ M → ¬ p ∣ M →
      ∀ (χ : DirichletCharacter ℂ M) (g : ℍ → ℂ),
        HalfIntegralThreeHalves M χ.toUnitHom g →
        MovingStepLaw M p χ (P.phaseData.η p) g) :
    EvenMovingSieveLaw P U := by
  classical
  have hbase := evenMasked P hS
  have aux (J : List ℕ) (hJ : J.Nodup) (hg : ∀ p ∈ J, (evenTypes W.S hS.1).Good p) :
      ∃ χ : DirichletCharacter ℂ (movingLevel P J.toFinset),
        (∀ n : ℕ, n.Coprime (movingLevel P J.toFinset) →
          χ n = maskedCharacter P n *
            ∏ p ∈ J.toFinset, (kronecker (p : ℤ) n : ℂ)) ∧
        HasThreeHalvesExpansion (RingHom.id ℂ) (movingLevel P J.toFinset) χ.toUnitHom
          (TL (fun p => P.phaseData.η p) J P.sievedCoeff) := by
    induction J with
    | nil =>
      rw [List.toFinset_nil]
      simpa only [EvenMovingSieveLaw, IsMovingCharacter, Finset.toList_empty] using moving_nil P hS
    | cons p J ih =>
      obtain ⟨hpJ, hJ'⟩ := List.nodup_cons.mp hJ
      have hp := (good_iff hS p).mp (hg p (by simp))
      letI : NeZero p := ⟨hp.1.ne_zero⟩
      let M := movingLevel P J.toFinset
      have hM4 : 4 ∣ M := hbase.1.trans (dvd_mul_right _ _)
      have hpM : ¬ p ∣ M := by
        intro hd
        rcases hp.1.dvd_mul.mp hd with h | h
        · exact hp.2 (hbase.2.1 p hp.1 h)
        · obtain ⟨q, hq, hdq⟩ := (hp.1.prime.dvd_finsetProd_iff id).mp h
          have hqJ := List.mem_toFinset.mp hq
          have hqp := (Nat.prime_dvd_prime_iff_eq hp.1
            (hg q (List.mem_cons_of_mem _ hqJ)).1).mp hdq
          exact hpJ (by simpa only [hqp] using hqJ)
      obtain ⟨χ, hχ, g, hform, hq⟩ := ih hJ' (fun q hq => hg q (List.mem_cons_of_mem _ hq))
      obtain ⟨ξ, hξ, hmove⟩ := hstep M p hp.1
        (hp.1.odd_of_ne_two (fun e => hp.2 (e.symm ▸ hS.2.1))) hM4 hpM χ g hform
      have hpJ' : p ∉ J.toFinset := fun h => hpJ (List.mem_toFinset.mp h)
      have he : movingLevel P (p :: J).toFinset = M * p := by
        simp [movingLevel, M, List.toFinset_cons, Finset.prod_insert hpJ', mul_left_comm, mul_comm]
      rw [he]
      refine ⟨ξ, ?_, ?_⟩
      · simp only [List.toFinset_cons]
        intro n hn
        rw [hξ n hn, hχ n (hn.of_dvd_right (dvd_mul_right _ _)), Finset.prod_insert hpJ']
        ring
      · simp only [TL_cons]
        exact ⟨movingOp p (P.phaseData.η p) g, hmove,
          movingOp_series p _ hq⟩
  have h := aux U.toList U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp))
  rw [Finset.toList_toFinset] at h
  exact h

/-- A half-integral expansion supplies an actual product, its individual
diamond character, and its ordinary theta convolution at every index. -/
theorem weightTwoBlock {m : ℕ} {χ : (ZMod m)ˣ →* ℂˣ} {a : ℕ → ℂ}
    (hfour : 4 ∣ m) (hθ : OrdinaryThetaLaw)
    (h : HasThreeHalvesExpansion (RingHom.id ℂ) m χ a) :
    ∃ f : WeightTwo m, f ∈ modFormCharSpace 2 χ ∧
      ∀ n, (qExpansion 1 f).coeff n = timesTheta a n := by
  obtain ⟨g, hg, hq⟩ := h
  obtain ⟨f, hf, hmem⟩ := theta_product_modular hfour hθ hg
  refine ⟨f, hmem, fun n => ?_⟩
  change (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n = _
  rw [hf]
  exact qExpansion_theta_product (RingHom.id ℂ) hg.holo hq n

private theorem subscripts_dvd {U : Finset ℕ} {j : ℕ} (hj : j ∈ subscripts U) :
    j ∣ ∏ p ∈ U, p := by
  classical
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.prod_dvd_prod_of_subset _ _ id (Finset.mem_powerset.mp hJ)

theorem unaryLevel_dvd (P : EvenSource W L τ) (U : Finset ℕ) (j : ↥(subscripts U)) :
    maskedLevel P * j.val ∣ movingLevel P U :=
  Nat.mul_dvd_mul_left _ (subscripts_dvd j.property)

/-- View the unary product in the common level without changing its function. -/
def includeUnary (P : EvenSource W L τ) (U : Finset ℕ) (j : ↥(subscripts U))
    (f : WeightTwo (maskedLevel P * j.val)) : WeightTwo (movingLevel P U) :=
  f.restrict (Gamma1_map_le_Gamma1_map_of_dvd (unaryLevel_dvd P U j))

/-- The diamond character of the included unary product is lifted from
its intrinsic level, so missing primes have no primitive character. -/
theorem includeUnary_mem (P : EvenSource W L τ) (U : Finset ℕ) (j : ↥(subscripts U))
    {χ : (ZMod (maskedLevel P * j.val))ˣ →* ℂˣ} {f : WeightTwo (maskedLevel P * j.val)}
    (hf : f ∈ modFormCharSpace 2 χ) :
    includeUnary P U j f ∈ modFormCharSpace 2 (χ.comp (ZMod.unitsMap (unaryLevel_dvd P U j))) :=
  TauCeti.ModularForm.restrict_mem_modFormCharSpace χ (unaryLevel_dvd P U j) hf

private def thetaLinear (K : Type) [CommRing K] : (ℕ → K) →ₗ[K] (ℕ → K) where
  toFun a := timesTheta a
  map_add' a b := by
    ext n
    simp only [timesTheta, Pi.add_apply, Finset.sum_add_distrib, mul_add]
    ring
  map_smul' c a := by
    ext n
    simp only [RingHom.id_apply, timesTheta, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring

private def coeffLinear (m n : ℕ) : WeightTwo m →ₗ[ℂ] ℂ where
  toFun f := (qExpansion 1 f).coeff n
  map_add' f g := by
    change (qExpansion 1 (f + g)).coeff n = (qExpansion 1 f).coeff n + (qExpansion 1 g).coeff n
    rw [ModularForm.qExpansion_add one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map m), map_add]
  map_smul' c f := by
    change (qExpansion 1 (c • f)).coeff n = c • (qExpansion 1 f).coeff n
    simp only [ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map m),
      PowerSeries.coeff_smul, smul_eq_mul]

/-- The actual modular-form combination, retaining each unary block's
intrinsic level until it is included in the common space. -/
def assembleForm (P : EvenSource W L τ) (U : Finset ℕ)
    (fB : WeightTwo (movingLevel P U))
    (fJ : ∀ j : ↥(subscripts U), WeightTwo (maskedLevel P * j.val)) :
    WeightTwo (movingLevel P U) :=
  let raw := TL (fun p => P.phaseData.η p) U.toList P.sievedCoeff
  let s : ℂ := (2 : ℂ) ^ (-(P.δ + U.card + 1))
  s • (fB - ∑ j : ↥(subscripts U), raw j.val • includeUnary P U j (fJ j))

/-- Assemble the actual form at the common level. Each unary block comes
from its own space, and the sum need not have a single diamond character. -/
theorem evenWeightTwo (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hB : EvenMovingSieveLaw P U)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (hUnary : ∀ j ∈ subscripts U, EvenUnaryStageLaw P hS i j) :
    ∃ (χB : DirichletCharacter ℂ (movingLevel P U))
      (χJ : ∀ j : ↥(subscripts U), DirichletCharacter ℂ (maskedLevel P * j.val))
      (fB : WeightTwo (movingLevel P U))
      (fJ : ∀ j : ↥(subscripts U), WeightTwo (maskedLevel P * j.val))
      (f : WeightTwo (movingLevel P U)),
      f = assembleForm P U fB fJ ∧
      IsMovingCharacter P U χB ∧ (∀ j, IsUnaryCharacter P i j.val (χJ j)) ∧
      fB ∈ modFormCharSpace 2 χB.toUnitHom ∧
      (∀ j, fJ j ∈ modFormCharSpace 2 (χJ j).toUnitHom) ∧
      (∀ j, includeUnary P U j (fJ j) ∈ modFormCharSpace 2
        ((χJ j).toUnitHom.comp (ZMod.unitsMap (unaryLevel_dvd P U j)))) ∧
      (∀ n, (qExpansion 1 fB).coeff n =
        timesTheta (TL (fun p => P.phaseData.η p) U.toList P.sievedCoeff) n) ∧
      (∀ j n, (qExpansion 1 (fJ j)).coeff n =
        timesTheta (unaryCoeff (evenTypes W.S hS.1).Good (fun p => P.phaseData.η p) i j.val) n) ∧
      ∀ n, (qExpansion 1 f).coeff n =
        timesTheta (halfDivided (evenTypes W.S hS.1).Good
          (fun p => P.phaseData.η p) P.sievedCoeff P.δ i U.toList) n := by
  classical
  let phase : ℕ → ℂ := fun p => P.phaseData.η p
  let raw := TL phase U.toList P.sievedCoeff
  let good : ℕ → Prop := (evenTypes W.S hS.1).Good
  let un (j : ℕ) := unaryCoeff good phase i j
  have h4 := (evenMasked P hS).1
  have h4U : 4 ∣ movingLevel P U := h4.trans (dvd_mul_right _ _)
  obtain ⟨χ, hχ, hb⟩ := hB
  obtain ⟨fB, hBm, hBq⟩ := weightTwoBlock h4U ordinaryThetaLaw hb
  have hu (j : ↥(subscripts U)) : ∃ (ξ : DirichletCharacter ℂ (maskedLevel P * j.val))
      (f : WeightTwo (maskedLevel P * j.val)), IsUnaryCharacter P i j.val ξ ∧
        f ∈ modFormCharSpace 2 ξ.toUnitHom ∧
        ∀ n, (qExpansion 1 f).coeff n = timesTheta (un j.val) n := by
    obtain ⟨ξ, hξ, hx⟩ := hUnary _ j.property hodd
    haveI : NeZero P.phaseData.N := ⟨even_level_ne_zero P⟩
    have hj : 0 < j.val := by
      -- Positivity of the shell follows from its nonzero divisor of the common product.
      have hpos : 0 < ∏ p ∈ U, p := Finset.prod_pos
        (fun p hp => ((hU p hp).1).pos)
      exact Nat.pos_of_dvd_of_pos (subscripts_dvd j.property) hpos
    have hsum : HasThreeHalvesExpansion (RingHom.id ℂ) (maskedLevel P * j.val) ξ.toUnitHom
        (un j.val) :=
      ⟨_, hx, unary_hasSum _ _ _ hj⟩
    obtain ⟨f, hf, hq⟩ := weightTwoBlock (h4.trans (dvd_mul_right _ _)) ordinaryThetaLaw hsum
    exact ⟨ξ, f, hξ, hf, hq⟩
  choose χJ fJ hJχ hJm hJq using hu
  let lift (j : ↥(subscripts U)) : WeightTwo (movingLevel P U) :=
    includeUnary P U j (fJ j)
  let s : ℂ := (2 : ℂ) ^ (-(P.δ + U.card + 1))
  let f : WeightTwo (movingLevel P U) := s • (fB - ∑ j : ↥(subscripts U), raw j.val • lift j)
  refine ⟨χ, χJ, fB, fJ, f, rfl, hχ, hJχ, hBm, hJm,
    fun j => includeUnary_mem P U j (hJm j), hBq, hJq, fun n => ?_⟩
  have hl (j : ↥(subscripts U)) : coeffLinear (movingLevel P U) n (lift j) =
      timesTheta (un j.val) n := hJq j n
  have hbq : coeffLinear (movingLevel P U) n fB = timesTheta raw n := hBq n
  have hraw : halfDivided good phase P.sievedCoeff P.δ i U.toList =
      s • (raw - ∑ j : ↥(subscripts U), raw j.val • un j.val) := by
    funext k
    have hsum : (∑ j : ↥(subscripts U), raw j.val * un j.val k) =
        ∑ j ∈ subscripts U, raw j * un j k := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach (subscripts U) (fun j => raw j * un j k)
    simp only [halfDivided, rawNumerator, Finset.toList_toFinset, Finset.length_toList,
      Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
    change s * (raw k - ∑ j ∈ subscripts U, raw j * un j k) =
      s * (raw k - ∑ j : ↥(subscripts U), raw j.val * un j.val k)
    rw [hsum]
  change coeffLinear (movingLevel P U) n f =
    thetaLinear ℂ (halfDivided good phase P.sievedCoeff P.δ i U.toList) n
  simp only [f, hraw, map_smul, map_sum, map_sub, Pi.smul_apply, Pi.sub_apply,
    Finset.sum_apply, hbq, hl]
  rfl

/-- Assemble the even vector from separately realized blocks in a chosen
constituent basis. Here `d` is the source depth in the coefficient field,
so the place application takes `d = P.δ + C.k`. -/
theorem evenVector_eval {I K G : Type} [Fintype I] [Field K] [Group G] {Q : ℕ → Prop}
    (A : ThetaCoeff.Basis I K G Q) (good : ℕ → Prop) (phase a : ℕ → K)
    (d : ℤ) (i : Fin 2) (U : Finset ℕ) (b : I → K) (unary : ℕ → I → K)
    (hB : ∀ n, A.eval n b = timesTheta (TL phase U.toList a) n)
    (hJ : ∀ j ∈ subscripts U, ∀ n, A.eval n (unary j) =
      timesTheta (unaryCoeff good phase i j) n) (n : ℕ) :
    A.eval n ((2 : K) ^ (-(d + U.card + 1)) •
        (b - ∑ j ∈ subscripts U, TL phase U.toList a j • unary j)) =
      timesTheta (halfDivided good phase a d i U.toList) n := by
  let raw := TL phase U.toList a
  let un := unaryCoeff good phase i
  let s : K := (2 : K) ^ (-(d + U.card + 1))
  have he : halfDivided good phase a d i U.toList =
      s • (raw - ∑ j ∈ subscripts U, raw j • un j) := by
    funext k
    simp only [halfDivided, rawNumerator, Finset.length_toList, Finset.toList_toFinset, s,
      Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply, raw, un]
  change A.eval n (s • (b - ∑ j ∈ subscripts U, raw j • unary j)) =
    thetaLinear K (halfDivided good phase a d i U.toList) n
  have hs : A.eval n (∑ j ∈ subscripts U, raw j • unary j) =
      thetaLinear K (∑ j ∈ subscripts U, raw j • un j) n := by
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply]
    exact Finset.sum_congr rfl fun j hj => by rw [hJ j hj]; rfl
  rw [he, map_smul, map_sub, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, ← hs, hB]
  rfl

variable (hS : SupportSpec W) {B : ℕ} [NeZero (conductor W.S)]
variable {X : Model P hS B} [CharZero X.K] (A : FourierData X) (C : SourceAtPlace P X.O X.K)

/-- Transfer the expansion of the actual form from its complex constituent
coordinates to the lattice over the single chosen place. -/
theorem evenExpansion (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (f : WeightTwo (movingLevel P U))
    (hf : ∀ n, (qExpansion 1 f).coeff n =
      timesTheta (halfDivided (evenTypes W.S hS.1).Good
        (fun p => P.phaseData.η p) P.sievedCoeff P.δ i U.toList) n)
    (κ : X.K →+* ℂ) (hκ : κ.comp C.eK = C.eC)
    (hcoord : ∀ n, n ≠ 0 →
      κ (algebraMap X.O X.K (A.coeff n (X.F U))) = (qExpansion 1 f).coeff n) :
    ∀ n, n ≠ 0 → A.coeff n (X.F U) = timesTheta (evenH hS A C i U) n := by
  intro n hn
  apply A.integral_inclusion
  apply κ.injective
  rw [hcoord n hn]
  have hgood (p : ℕ) (hp : p ∈ U.toList) := hU p (Finset.mem_toList.mp hp)
  have hplace := commonCoeff_place C hS A.integral_inclusion i U.toList U.nodup_toList hgood n
  have heven : evenH hS A C i U =
      dividedCoeff (source_at_place C hS A.integral_inclusion) i U.toList U.nodup_toList hgood := by
    funext k
    rw [evenH, dite_eq_left hU]
  rw [heven, hplace, ← RingHom.comp_apply, hκ, commonCoeff_complex C hS i U.toList n]
  exact hf n


end ZInQ.Manuscript.RC.EvenExpansion

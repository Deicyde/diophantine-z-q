import ZInQKernel.Contrib.OneProof.RC.Wiring.EvenUpper3
import ZInQKernel.Contrib.OneProof.RC.Wiring.AuxFactor3
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Bridges
import ZInQKernel.Contrib.CloudB3RC53.Prints.Kolyvagin
import ZInQKernel.Contrib.RC53Assist.AuxFactor.GenuineEvenSource

/-!
# Conditional consequences for the fixed-level even upper estimate

The level is fixed to the newform level of the original elliptic curve,
with a separate functional-equation anchor. Formula (3.2) has one scalar
per binary family, with uniform constants and the guarded central zero
criterion. Formula (3.3b) is nonvanishing together with an upper bound;
its reverse corank-zero implication uses the separate forward theorem.

The table `A` below is an unrestricted function. `SourceUnit` and
`SourcePartitionable` are formal observations of that table, not
certificates that it is a normalized arithmetic coefficient symbol.
`SourceConsequenceInputs` records conditional numerical and cube
consequences. It asserts no coefficient rules, off-filter vanishing,
modular form, or equality with the actual original coefficient source.
Actual-source provenance is external to this interface.

Likewise, the predicates and values in `SuppliedMinimum` and
`SquareReading` are arbitrary numerical data. They do not identify
coefficients of an actual form; they can hold on a singleton predicate.
The supplied unit-membership implication remains a separate premise.
No new minimizer is chosen or identified with the specified `kfin`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenUpperText

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
  ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53

attribute [local instance] Nat.fact_prime_two

set_option maxHeartbeats 600000

/-- The level of the fixed curve, not a freely chosen family level. -/
def N₀ (ℓ : ℕ) : ℕ := CST.newformLevel (Ecurve ℓ)

/-- The fixed level is a level of the genuine functional equation. -/
def CurveLevel (ℓ : ℕ) : Prop :=
  ∃ w : ℤ, PrintsAnalytic.RootNumberAt (Ecurve ℓ) (N₀ ℓ) w

/-- Formula (3.2) with specified constants, uniform over all families at
    the fixed level. Both central zero implications are retained. -/
def Scalar32At {ℓ : ℕ} (W : WData ℓ) (Cev Cloc : ℕ) : Prop :=
  ∀ fam : Even.BinaryFamily (N₀ ℓ),
    ∃ u : (Fin fam.b → ZMod 2) → PowerSeries ℚ_[2],
      (∀ g, Even.InLam ((2 : ℚ_[2]) ^ Cev • u g)) ∧
      (∀ x, Even.CorankZero (Ecurve ℓ) (fam.h x) →
        (Even.central (Even.charEval u x) = 0 ↔ W.Lstar (fam.h x) = 0)) ∧
      (∀ x, Even.CorankZero (Ecurve ℓ) (fam.h x) → W.Lstar (fam.h x) ≠ 0 →
        |(Even.central (Even.charEval u x)).valuation -
          (padicValRat 2 (W.Lstar (fam.h x)) - 2 * (Even.omega (fam.h x) : ℤ) -
            (Even.shaLen (Ecurve ℓ) (fam.h x) : ℤ))| ≤ Cloc)

/-- The constants of (3.2) are chosen before any binary family. -/
def Scalar32 {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ Cev Cloc : ℕ, Scalar32At W Cev Cloc

/-- Numerical (3.3a) on an arbitrary supplied unit predicate. -/
def Units33a {ℓ : ℕ} (W : WData ℓ) (unitSym : ℤ → Prop) (C₀ : ℤ) : Prop :=
  ∀ p, unitSym p → p ≠ 0 ∧ W.Lstar p ≠ 0 ∧
    padicValRat 2 (W.Lstar p) ≤ 2 * omega p + C₀

/-- Arbitrarily large binary families are supplied at the fixed level.
    The construction is not certified here, and the parameter map need
    not be injective. -/
def CubeInputs {ℓ : ℕ} (W : WData ℓ) (unitSym : ℤ → Prop) : Prop :=
  ∀ d : ℤ, d ≠ 0 → W.Partitionable d →
    Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : Even.BinaryFamily (N₀ ℓ),
        b ≤ fam.b ∧ fam.h 0 = d ∧ ∀ x, x ≠ 0 → unitSym (fam.h x)

/-- The existing even upper input with its family level fixed. -/
def FixedLevelInputs {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (unitSym : ℤ → Prop) (C₀ : ℤ),
    Units33a W unitSym C₀ ∧ Scalar32 W ∧ CubeInputs W unitSym

/-- The negative squarefree support filter determined by `W`. This
    alone is not the local-squareclass filter of an actual coefficient form. -/
def NegativeFilter {ℓ : ℕ} (W : WData ℓ) (d : ℤ) : Prop :=
  d < 0 ∧ Squarefree d ∧ ∀ p ∈ W.S, ¬ (p : ℤ) ∣ d

/-- The formal contraction-certificate predicate for the unrestricted
    table `A`, tested on the negative squarefree support filter. It does
    not identify that table with an arithmetic coefficient source. -/
def SourcePartitionable {ℓ : ℕ} (W : WData ℓ) {L : Type} [AddCommGroup L]
    {ε : L →+ ZMod 2} (T : CoefficientDictionary.TypeData L ε)
    (A : L → Symbols.Config L → ZMod 2) (d : ℤ) : Prop :=
  NegativeFilter W d ∧
    Symbols.IsPartitionable ε
      (A (Symbols.primeConfig d.natAbs.primeFactors T.typ).total)
      (Symbols.primeConfig d.natAbs.primeFactors T.typ)

/-- Exact partitionability, rather than only a lower bound on its set
    of parameters. -/
def PartitionabilitySpec {ℓ : ℕ} (W : WData ℓ) {L : Type} [AddCommGroup L]
    {ε : L →+ ZMod 2} (T : CoefficientDictionary.TypeData L ε)
    (A : L → Symbols.Config L → ZMod 2) : Prop :=
  ∀ d, W.Partitionable d ↔ SourcePartitionable W T A d

/-- A formal unit is a value-one observation of the supplied table on
    the negative filter. No modular form, normalization, or coefficient
    reading is specified by this predicate. -/
def SourceUnit {ℓ : ℕ} (W : WData ℓ) {L : Type} [AddCommGroup L]
    {ε : L →+ ZMod 2} (T : CoefficientDictionary.TypeData L ε)
    (A : L → Symbols.Config L → ZMod 2) (d : ℤ) : Prop :=
  NegativeFilter W d ∧
    A (Symbols.primeConfig d.natAbs.primeFactors T.typ).total
      (Symbols.primeConfig d.natAbs.primeFactors T.typ) = 1

/-- A conditional cube relation for `A`: original primes remain in
    every constituent, total types agree, and nonzero addresses satisfy
    the formal value-one predicate. This does not certify a construction
    from an actual coefficient source. -/
def SourceCubeInputs {ℓ : ℕ} (W : WData ℓ) {L : Type} [AddCommGroup L]
    {ε : L →+ ZMod 2} (T : CoefficientDictionary.TypeData L ε)
    (A : L → Symbols.Config L → ZMod 2) : Prop :=
  ∀ d : ℤ, SourcePartitionable W T A d →
    Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : Even.BinaryFamily (N₀ ℓ),
        b ≤ fam.b ∧ fam.h 0 = d ∧
        (∀ x, ∀ p ∈ d.natAbs.primeFactors, (p : ℤ) ∣ fam.h x) ∧
        (∀ x, (Symbols.primeConfig (fam.h x).natAbs.primeFactors T.typ).total =
          (Symbols.primeConfig d.natAbs.primeFactors T.typ).total) ∧
        ∀ x, x ≠ 0 → SourceUnit W T A (fam.h x)

/-- Conditional source consequences at the fixed level. The table `A`
    is unrestricted; these fields certify neither coefficient rules nor
    identity with a normalized arithmetic coefficient source. Actual-source
    provenance must be supplied externally. -/
structure SourceConsequenceInputs {ℓ : ℕ} (W : WData ℓ) {L : Type} [AddCommGroup L]
    {ε : L →+ ZMod 2} (T : CoefficientDictionary.TypeData L ε)
    (A : L → Symbols.Config L → ZMod 2) : Prop where
  level : CurveLevel ℓ
  normalized : LstarNormalized W.toRCData
  partitionable : PartitionabilitySpec W T A
  scalar32 : Scalar32 W
  unit_bound : ∃ C₀ : ℤ, Units33a W (SourceUnit W T A) C₀
  cubes : SourceCubeInputs W T A

/-- The nonzero central value implication to full Selmer corank zero.
    This is separate from the scalar construction. -/
def Forward {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∀ d : ℤ, d ≠ 0 → W.Lstar d ≠ 0 →
    Z2Corank (selmerTwoPower (Etw ℓ d)) 0

/-- Both assertions of the displayed formula (3.3b). -/
def Upper33b {ℓ : ℕ} (W : WData ℓ) (C₁ : ℤ) : Prop :=
  ∀ d : ℤ, d ≠ 0 → W.Partitionable d →
    Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      W.Lstar d ≠ 0 ∧
        padicValRat 2 (W.Lstar d) - 2 * (omega d : ℤ) - sFun ℓ d ≤ C₁

/-- Formula (E.9), with a constant fixed before the parameter. -/
def LowerBound {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ C : ℤ, ∀ h : ℤ, Odd h → Squarefree h → W.Lstar h ≠ 0 →
    2 * (omega h : ℤ) + sFun ℓ h - C ≤ padicValRat 2 (W.Lstar h)

/-- A minimum of arbitrary supplied numerical values at the specified
    negative parameter. This does not bind those values to coefficients
    of an actual form or produce a minimizer. -/
def SuppliedMinimum {ℓ : ℕ} (W : WData ℓ) (aNZ : ℤ → Prop) (va : ℤ → ℤ) : Prop :=
  W.kfin < 0 ∧ aNZ W.kfin ∧
    ∀ p, aNZ p → va W.kfin - omega W.kfin ≤ va p - omega p

/-- An (E.11)-shaped numerical consequence on an arbitrary predicate.
    It does not certify that `aNZ`, `va`, or `κ` are readings of actual
    coefficients on the original local-squareclass filter. -/
def SquareReading {ℓ : ℕ} (W : WData ℓ) (aNZ : ℤ → Prop) (va : ℤ → ℤ)
    (κ : ℤ) : Prop :=
  ∀ p, aNZ p → W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) = 2 * va p + κ

/-- A genuine functional equation forces a positive fixed level. -/
theorem level_pos {ℓ : ℕ} (h : CurveLevel ℓ) : 0 < N₀ ℓ := by
  obtain ⟨w, hw⟩ := h
  exact hw.1

/-- Modularity also rules out the zero value of the least cusp-form level. -/
theorem level_pos_of_bcdt (hB : PoleS12.BCDTThmA) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    0 < N₀ ℓ := by
  have hE : (Ecurve ℓ).IsElliptic :=
    PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  obtain ⟨N, hN, f, hf⟩ := hB (Ecurve ℓ) hE
  have hs : {n : ℕ | 0 < n ∧ CST.HasCuspFormAtLevel (Ecurve ℓ) n}.Nonempty :=
    ⟨N, hN, f, hf⟩
  exact (Nat.sInf_mem hs).1

/-- The fixed level agrees with the level of any supplied genuine
    newform of the fixed curve, by uniqueness of the functional equation. -/
theorem level_eq_of_newform {ℓ M : ℕ} [NeZero M]
    {f : HeckeRing.GL2.Newform M 2}
    (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f) (h : CurveLevel ℓ) :
    N₀ ℓ = M := by
  obtain ⟨w, hw⟩ := h
  exact (PrintsAnalytic.eq_level_and_sign_of_rootNumberAt hf hw).1

/-- The scalar depends on the chosen normalization only through its
    central-value function. Periods are not changed by this comparison. -/
theorem scalar32_iff_even {ℓ : ℕ} {W : WData ℓ}
    (L : Even.CentralNormalization (Ecurve ℓ)) (hLW : L.Lstar = W.Lstar) :
    Scalar32 W ↔ Even.EvenScalar32 (Ecurve ℓ) (N₀ ℓ) L := by
  unfold Scalar32 Scalar32At Even.EvenScalar32
  rw [hLW]

/-- Appendix E supplies (3.2) at the fixed level, using the existing
    coefficientwise intersection and central-length calculations. The
    Appendix E outputs remain a separately stated construction input. -/
theorem scalar32_of_appE {ℓ : ℕ} {W : WData ℓ} (hN : N₀ ℓ ≠ 0)
    (L : Even.CentralNormalization (Ecurve ℓ)) (hLW : L.Lstar = W.Lstar)
    (hE : Even.AppEOutputs (Ecurve ℓ) (N₀ ℓ) L) : Scalar32 W :=
  (scalar32_iff_even L hLW).mpr (Even.evenScalar32_of_appE hN hE)

/-- The exact formal table predicate gives the existing auxiliary-factor
    implication without identifying the table with an arithmetic source. -/
theorem partitionability_forward {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (h : PartitionabilitySpec W T A) :
    ∀ d : ℤ, d < 0 → Squarefree d → (∀ p ∈ W.S, ¬ (p : ℤ) ∣ d) →
      Symbols.IsPartitionable ε
        (A (Symbols.primeConfig d.natAbs.primeFactors T.typ).total)
        (Symbols.primeConfig d.natAbs.primeFactors T.typ) → W.Partitionable d := by
  intro d hd hs ha hp
  exact (h d).mpr ⟨⟨hd, hs, ha⟩, hp⟩

/-- The reverse direction records the support filter and formal
    nonempty contraction certificate of every interface parameter. -/
theorem partitionability_reverse {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (h : PartitionabilitySpec W T A) :
    ∀ d : ℤ, W.Partitionable d → SourcePartitionable W T A d :=
  fun d hd => (h d).mp hd

/-- The conditional source interface supplies the fixed-level input. -/
theorem fixedLevelInputs_of_sourceConsequences {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (h : SourceConsequenceInputs W T A) :
    FixedLevelInputs W := by
  obtain ⟨C₀, hu⟩ := h.unit_bound
  refine ⟨SourceUnit W T A, C₀, hu, h.scalar32, ?_⟩
  intro d _ hd hcz b
  obtain ⟨fam, hb, hbase, _, _, hunit⟩ :=
    h.cubes d ((h.partitionable d).mp hd) hcz b
  exact ⟨fam, hb, hbase, hunit⟩

/-- The fixed-level version supplies the existing even upper input,
    taking precisely the level of the fixed curve as its witness. -/
theorem rc11Inputs_of_fixedLevel {ℓ : ℕ} {W : WData ℓ} (h : FixedLevelInputs W) :
    EvenUpperRC11Inputs W := by
  obtain ⟨unitSym, C₀, hu, hs, hc⟩ := h
  exact ⟨unitSym, C₀, N₀ ℓ, hu,
    fun L hLW => (scalar32_iff_even L hLW).mp hs, hc⟩

/-- Direct compatibility with the current even upper consumer. -/
theorem rc11Inputs_of_sourceConsequences {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (h : SourceConsequenceInputs W T A) :
    EvenUpperRC11Inputs W :=
  rc11Inputs_of_fixedLevel (fixedLevelInputs_of_sourceConsequences h)

/-- Forgetting nonvanishing recovers the current upper-bound predicate. -/
theorem currentUpper_of_upper33b {ℓ : ℕ} {W : WData ℓ} {C₁ : ℤ}
    (h : Upper33b W C₁) : EvenUpper33b W C₁ := by
  intro d hd hp hc
  have hb := (h d hd hp hc).2
  change padicValRat 2 (W.Lstar d) ≤
    2 * Nonvanishing.omega d + sFun ℓ d + C₁
  rw [← omega_eq_nonvanishing]
  linarith

/-- A parameter satisfying the formal value-one predicate is nonzero. -/
theorem sourceUnit_ne_zero {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} {d : ℤ} (h : SourceUnit W T A d) : d ≠ 0 :=
  h.1.2.1.ne_zero

/-- Only the modularity and analytic rank-zero finiteness leaves of the
    existing analytic interface enter the forward implication. The
    Kummer corank-zero calculation is already proved. The Kolyvagin
    argument here uses the existing consequence form; the weak-Weil
    parametrization passage is not discharged by this theorem. -/
theorem forward_of_analytic_leaves {ℓ : ℕ} {W : WData ℓ}
    (hB : PoleS12.BCDTThmA) (hK : KolyvaginThm1Printed)
    (hℓ : 0 < ℓ) (hL : LstarTarget W.toRCData) : Forward W := by
  intro d hd hLd
  have hE : (Etw ℓ d).IsElliptic := by
    rw [Etw_eq_curve]
    exact PoleRC.curve_isElliptic
      (by exact_mod_cast mul_ne_zero hd (by exact_mod_cast hℓ.ne'))
  obtain ⟨hr, hs⟩ := hK (Etw ℓ d) hE (hB _ hE) 0 (Nat.zero_le 1) ((hL d hd).mp hLd)
  exact ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof
    _ hE (by exact_mod_cast hr) hs

/-- BCDT and Kolyvagin with the weak-Weil premise suffice for the
    forward implication when the separate parametrization passage is
    supplied. No parity or height-formula leaf is used. The analytic
    description of the parametrization keeps its stated translation gap. -/
theorem forward_of_weil_leaves {ℓ : ℕ} {W : WData ℓ}
    (hB : PoleS12.BCDTThmA) (hG : ModularToWeakWeil) (hK : KolyvaginThm1WeilParam)
    (hℓ : 0 < ℓ) (hL : LstarTarget W.toRCData) : Forward W :=
  forward_of_analytic_leaves hB (kolyvaginThm1Printed_of_weilParam hG hK) hℓ hL

/-- A single congruence precision above a nonzero valuation bound
    transfers nonvanishing and the same bound to the base. -/
theorem single_precision_transfer (a b : ℚ_[2]) (B : ℤ)
    (ha : a ≠ 0) (hva : a.valuation ≤ B)
    (hc : a = b ∨ B + 1 ≤ (a - b).valuation) :
    b ≠ 0 ∧ b.valuation ≤ B := by
  by_contra hn
  rcases hc with he | hc
  · rw [he] at ha hva
    exact hn ⟨ha, hva⟩
  · have hsum : (a - b) + b ≠ 0 := by rwa [sub_add_cancel]
    have hmin := Padic.le_valuation_add hsum
    rw [sub_add_cancel] at hmin
    by_cases hb : b = 0
    · rw [hb, sub_zero] at hc
      linarith
    · have hvb : B < b.valuation := by
        by_contra hle
        exact hn ⟨hb, not_lt.mp hle⟩
      have hbd : B + 1 ≤ min (a - b).valuation b.valuation :=
        le_min hc (by omega)
      linarith

/-- The single-precision consumer proves the full displayed (3.3b),
    including nonvanishing, with constant C₀ + 2 C_loc. -/
theorem upper33b_of_inputsAt {ℓ : ℕ} {W : WData ℓ} (hf : Forward W)
    (h : ZInQ.Contrib.CloudB3RC53.EvenUpper.EvenUpperInputsAt W) :
    ∃ C₁ : ℤ, Upper33b W C₁ := by
  obtain ⟨C₀, Cloc, hd⟩ := h
  refine ⟨C₀ + 2 * Cloc, ?_⟩
  intro d hd0 hp hc
  obtain ⟨unitSym, u, hu, h32, x, hx, hcong⟩ := hd d hd0 hp hc
  obtain ⟨hx0, hLx, hvalx⟩ := hu x hx
  obtain ⟨hzerox, hboundx⟩ := h32 x hx0 (hf x hx0 hLx)
  have hux : u x ≠ 0 := fun h0 => hLx (hzerox.mp h0)
  have hvx : (u x).valuation ≤ C₀ + Cloc := by
    have he := (abs_le.mp (hboundx hLx)).2
    have hs : (0 : ℤ) ≤ shaLength (Etw ℓ x) := Int.natCast_nonneg _
    linarith
  have hb := single_precision_transfer (u x) (u d) (C₀ + Cloc) hux hvx hcong
  obtain ⟨hzerod, hboundd⟩ := h32 d hd0 hc
  have hLd : W.Lstar d ≠ 0 := fun h0 => hb.1 (hzerod.mpr h0)
  refine ⟨hLd, ?_⟩
  have he := (abs_le.mp (hboundd hLd)).1
  unfold sFun
  linarith [hb.2]

/-- The fixed-level (3.2), unit estimate, and realized cubes supply the
    full upper estimate through the existing Boolean comparison. -/
theorem upper33b_of_fixedLevel {ℓ : ℕ} {W : WData ℓ} (hf : Forward W)
    (hn : LstarNormalized W.toRCData) (h : FixedLevelInputs W) :
    ∃ C₁ : ℤ, Upper33b W C₁ := by
  obtain ⟨unitSym, C₀, hu, hs, hc⟩ := h
  obtain ⟨L, hLW⟩ := hn
  exact upper33b_of_inputsAt hf
    (ZInQ.Contrib.CloudB3RC53.EvenUpper.evenUpperInputsAt_of'
      W unitSym C₀ hu L hLW ((scalar32_iff_even L hLW).mp hs) hc)

/-- The conditional source interface yields both assertions of (3.3b). -/
theorem upper33b_of_sourceConsequences {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (hf : Forward W)
    (h : SourceConsequenceInputs W T A) : ∃ C₁ : ℤ, Upper33b W C₁ :=
  upper33b_of_fixedLevel hf h.normalized (fixedLevelInputs_of_sourceConsequences h)

/-- Forgetting the conditional nonvanishing conjunct supplies the
    old numerical upper-bound consumer. -/
theorem currentUpper_of_sourceConsequences {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (hf : Forward W)
    (h : SourceConsequenceInputs W T A) : ∃ C₁ : ℤ, EvenUpper33b W C₁ := by
  obtain ⟨C₁, hC⟩ := upper33b_of_sourceConsequences hf h
  exact ⟨C₁, currentUpper_of_upper33b hC⟩

/-- On the partitionable domain, the two assertions of (3.3b) are
    equivalent to corank zero. The reverse direction uses only the
    nonvanishing assertion and the separate forward theorem. -/
theorem corankZero_iff_upper33b {ℓ : ℕ} {W : WData ℓ} {C₁ : ℤ}
    (hf : Forward W) (h : Upper33b W C₁) (d : ℤ) (hd : d ≠ 0)
    (hp : W.Partitionable d) :
    Z2Corank (selmerTwoPower (Etw ℓ d)) 0 ↔
      W.Lstar d ≠ 0 ∧
        padicValRat 2 (W.Lstar d) - 2 * (omega d : ℤ) - sFun ℓ d ≤ C₁ :=
  ⟨h d hd hp, fun hL => hf d hd hL.1⟩

/-- A unit already satisfies an upper estimate directly. In particular,
    an empty unit requires no stationary address argument. -/
theorem upper_at_unit {ℓ : ℕ} {W : WData ℓ} {unitSym : ℤ → Prop} {C₀ : ℤ}
    (hu : Units33a W unitSym C₀) {d : ℤ} (hd : unitSym d) :
    W.Lstar d ≠ 0 ∧
      padicValRat 2 (W.Lstar d) - 2 * (omega d : ℤ) - sFun ℓ d ≤ C₀ := by
  obtain ⟨_, hL, hv⟩ := hu d hd
  refine ⟨hL, ?_⟩
  have hs : (0 : ℤ) ≤ shaLength (Etw ℓ d) := Int.natCast_nonneg _
  unfold sFun
  linarith

/-- Formula (E.9) follows already from (3.2) on the one-element family.
    No new minimizer and no continuation outside the nonzero constituents
    are needed for this deduction. -/
theorem lowerBound_of_scalar32 {ℓ : ℕ} {W : WData ℓ} (hf : Forward W)
    (h32 : Scalar32 W) : LowerBound W := by
  obtain ⟨Cev, Cloc, h32⟩ := h32
  refine ⟨(Cev : ℤ) + Cloc, ?_⟩
  intro h hodd hsq hL
  let fam := Even.BinaryFamily.single (N₀ ℓ) h hodd hsq
  obtain ⟨u, hu, hz, hb⟩ := h32 fam
  have : IsEmpty (Fin fam.b) := by
    change IsEmpty (Fin 0)
    infer_instance
  have : Unique (Fin fam.b → ZMod 2) := Pi.uniqueOfIsEmpty _
  have hc : Even.CorankZero (Ecurve ℓ) (fam.h 0) := hf h hsq.ne_zero hL
  have hLf : W.Lstar (fam.h 0) ≠ 0 := hL
  have hne : Even.central (Even.charEval u 0) ≠ 0 := fun h0 => hLf ((hz 0 hc).mp h0)
  have he := hb 0 hc hLf
  have hx : Even.charEval u 0 = u 0 := by
    simp only [Even.charEval]
    rw [Fintype.sum_unique]
    simp only [Even.chi, dotProduct, Finset.univ_eq_empty, Finset.sum_empty,
      ite_true, Int.cast_one, one_smul]
    exact congrArg u (Subsingleton.elim _ _)
  have hv : -(Cev : ℤ) ≤ (Even.central (Even.charEval u 0)).valuation := by
    rw [hx] at hne ⊢
    exact Even.valuation_central_ge (hu 0) hne
  change |(Even.central (Even.charEval u 0)).valuation -
    (padicValRat 2 (W.Lstar h) - 2 * (Even.omega h : ℤ) -
      (Even.shaLen (Ecurve ℓ) h : ℤ))| ≤ Cloc at he
  rw [ZInQ.Contrib.CloudB3RC53.EvenUpper.even_omega_eq] at he
  change |(Even.central (Even.charEval u 0)).valuation -
    (padicValRat 2 (W.Lstar h) - 2 * (omega h : ℤ) - sFun ℓ h)| ≤ Cloc at he
  have he' := (abs_le.mp he).2
  linarith

/-- A unit reaches the value of the already supplied minimum. This
    comparison does not choose an index or rename any new minimizer. -/
theorem unit_depth_of_supplied_minimum {ℓ : ℕ} {W : WData ℓ}
    {aNZ : ℤ → Prop} {va : ℤ → ℤ} (hm : SuppliedMinimum W aNZ va)
    {p : ℤ} (hp : ZInQ.Contrib.CloudB3RC53.EvenUpper.UnitMin aNZ va p) :
    va p - omega p = va W.kfin - omega W.kfin := by
  obtain ⟨_, hk, hmin⟩ := hm
  exact le_antisymm (hp.2 W.kfin hk) (hmin p hp.1)

/-- The numeric reading and minimum premises give an (F.1)-shaped
    unit value. This calculation establishes no coefficient provenance. -/
theorem unit_value_of_supplied_minimum {ℓ : ℕ} {W : WData ℓ}
    {aNZ : ℤ → Prop} {va : ℤ → ℤ} {κ : ℤ} (hm : SuppliedMinimum W aNZ va)
    (hr : SquareReading W aNZ va κ) {p : ℤ}
    (hp : ZInQ.Contrib.CloudB3RC53.EvenUpper.UnitMin aNZ va p) :
    W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) =
      2 * (omega p : ℤ) + (2 * (va W.kfin - omega W.kfin) + κ) := by
  obtain ⟨hL, hv⟩ := hr p hp.1
  have hd := unit_depth_of_supplied_minimum hm hp
  exact ⟨hL, by linarith⟩

/-- The numerical unit value gives (3.3a) with the explicit constant
    determined by the supplied values at `kfin`. -/
theorem units33a_of_supplied_minimum {ℓ : ℕ} {W : WData ℓ}
    {aNZ : ℤ → Prop} {va : ℤ → ℤ} {κ : ℤ} (hm : SuppliedMinimum W aNZ va)
    (hr : SquareReading W aNZ va κ) (hNZ : ∀ p, aNZ p → p ≠ 0) :
    Units33a W (ZInQ.Contrib.CloudB3RC53.EvenUpper.UnitMin aNZ va)
      (2 * (va W.kfin - omega W.kfin) + κ) := by
  intro p hp
  obtain ⟨hL, hv⟩ := unit_value_of_supplied_minimum hm hr hp
  exact ⟨hNZ p hp.1, hL, hv.le⟩

/-- Supplied numerical reading and minimum consequences feed the
    fixed-level consumer. The scalar and cubes remain explicit inputs;
    none of these numeric data is certified as an actual coefficient. -/
theorem fixedLevelInputs_of_supplied_readings {ℓ : ℕ} {W : WData ℓ}
    {aNZ : ℤ → Prop} {va : ℤ → ℤ} {κ : ℤ} (hm : SuppliedMinimum W aNZ va)
    (hr : SquareReading W aNZ va κ) (hNZ : ∀ p, aNZ p → p ≠ 0)
    (h32 : Scalar32 W)
    (hc : CubeInputs W (ZInQ.Contrib.CloudB3RC53.EvenUpper.UnitMin aNZ va)) :
    FixedLevelInputs W :=
  ⟨_, 2 * (va W.kfin - omega W.kfin) + κ,
    units33a_of_supplied_minimum hm hr hNZ, h32, hc⟩

/-- A single-predicate constructor consumes the formal unit-membership
    implication and numeric reading/minimum premises. This implication is
    essential and is not derived from actual-source provenance here. -/
theorem sourceConsequenceInputs_of_supplied_readings {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} {aNZ : ℤ → Prop} {va : ℤ → ℤ} {κ : ℤ}
    (hl : CurveLevel ℓ) (hn : LstarNormalized W.toRCData)
    (hp : PartitionabilitySpec W T A) (h32 : Scalar32 W)
    (hm : SuppliedMinimum W aNZ va) (hr : SquareReading W aNZ va κ)
    (hNZ : ∀ p, aNZ p → p ≠ 0)
    (hu : ∀ p, SourceUnit W T A p →
      ZInQ.Contrib.CloudB3RC53.EvenUpper.UnitMin aNZ va p)
    (hc : SourceCubeInputs W T A) : SourceConsequenceInputs W T A := by
  have hunit := units33a_of_supplied_minimum hm hr hNZ
  exact ⟨hl, hn, hp, h32,
    ⟨2 * (va W.kfin - omega W.kfin) + κ, fun p hp => hunit p (hu p hp)⟩, hc⟩

/-- Finitely many supplied numerical unit bounds give one uniform bound.
    Only constants are combined; no coefficient provenance or minimum is
    produced by this finite arithmetic operation. -/
theorem units33a_of_finite_sources {ℓ : ℕ} {W : WData ℓ} {I : Type}
    [Fintype I] (unitSym : I → ℤ → Prop) (C : I → ℤ)
    (hu : ∀ i, Units33a W (unitSym i) (C i)) :
    Units33a W (fun p => ∃ i, unitSym i p) (∑ i, max (C i) 0) := by
  classical
  intro p hp
  obtain ⟨i, hi⟩ := hp
  obtain ⟨hp0, hL, hv⟩ := hu i p hi
  have hC : C i ≤ ∑ j, max (C j) 0 :=
    le_trans (le_max_left _ _) (Finset.single_le_sum
      (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i))
  exact ⟨hp0, hL, by linarith⟩

/-- Finite numerical unit bounds and the formal classification relation
    supply the conditional interface once its other consequences are
    supplied. Different constants are allowed; source identity is external. -/
theorem sourceConsequenceInputs_of_finite_readings {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} {I : Type} [Fintype I]
    (hl : CurveLevel ℓ) (hn : LstarNormalized W.toRCData)
    (hp : PartitionabilitySpec W T A) (h32 : Scalar32 W)
    (unitSym : I → ℤ → Prop) (C : I → ℤ)
    (hu : ∀ i, Units33a W (unitSym i) (C i))
    (hr : ∀ p, SourceUnit W T A p → ∃ i, unitSym i p)
    (hc : SourceCubeInputs W T A) : SourceConsequenceInputs W T A := by
  have hb := units33a_of_finite_sources unitSym C hu
  exact ⟨hl, hn, hp, h32, ⟨∑ i, max (C i) 0, fun p hp => hb p (hr p hp)⟩, hc⟩

/-- On the formal `A`-specific partitionable domain, the conditional
    upper statement has both directions when `Forward W` is supplied.
    This is not an identification with the actual source's domain. -/
theorem sourceConsequence_upper_equivalence {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (hf : Forward W)
    (h : SourceConsequenceInputs W T A) :
    ∃ C₁ : ℤ, ∀ d : ℤ, SourcePartitionable W T A d →
      (Z2Corank (selmerTwoPower (Etw ℓ d)) 0 ↔
        W.Lstar d ≠ 0 ∧
          padicValRat 2 (W.Lstar d) - 2 * (omega d : ℤ) - sFun ℓ d ≤ C₁) := by
  obtain ⟨C₁, hC⟩ := upper33b_of_sourceConsequences hf h
  refine ⟨C₁, fun d hd => ?_⟩
  exact corankZero_iff_upper33b hf hC d hd.1.1.ne ((h.partitionable d).mpr hd)

/-! ## Adapter from the supplied genuine prepared even sources -/

open ZInQ.Contrib.RC53Assist.AuxFactor ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- Zero extension of the unprepared tables implies that every observed
    unit has a prepared total type. This is a conditional table specification,
    not a coefficient-source construction. -/
theorem sourceUnit_type_prepared_of_zero_unprepared {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2}
    (hzero : ∀ τ : L, ¬ PreparedType W T τ → ∀ Γ, A τ Γ = 0) :
    ∀ d : ℤ, SourceUnit W T A d →
      PreparedType W T (Symbols.primeConfig d.natAbs.primeFactors T.typ).total := by
  intro d hd
  by_contra hn
  have hz := hzero _ hn (Symbols.primeConfig d.natAbs.primeFactors T.typ)
  exact zero_ne_one (hz.symm.trans hd.2)

/-- A value-one observation of the actual dictionary symbol gives the
    original squareclass filter, a nonzero phase-removed coefficient, and
    its value at the already specified depth. The supplied genuine source
    and its normalization are used unchanged. -/
theorem unit_reading_of_genuine_source {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} (T : TypeData L ε)
    {A : L → Symbols.Config L → ZMod 2} {τ : L}
    (C : Even.CentralNormalization (Ecurve ℓ)) (hW : PrintsAnalytic.WaldspurgerCor2)
    (hE : (Ecurve ℓ).IsElliptic) {D₀ : ℕ}
    (P : Even.EvenPhaseData (Ecurve ℓ) C (-1) W.S D₀)
    (h₀ : C.Lstar (-1 * (D₀ : ℤ)) ≠ 0)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : Even.EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (hfactor : ∀ B : ℕ, FixedUFactorization T
      (coeffReading (genuineEvenCoefficient hW hE P h₀ hcont h9)
        (genuineEvenNormalization hW hE P h₀ hcont h9).2 (Even.S0Filter W.S D₀)) B)
    (hA : A τ = genuineEvenSymbol T hW hE P h₀ hcont h9)
    {d : ℤ} (hd : SourceUnit W T A d)
    (ht : (Symbols.primeConfig d.natAbs.primeFactors T.typ).total = τ) :
    let M := genuineEvenNormalization hW hE P h₀ hcont h9
    let a := genuineEvenCoefficient hW hE P h₀ hcont h9
    Even.S0Filter W.S D₀ d.natAbs ∧ a d.natAbs ≠ 0 ∧
      Padic.valuation (a d.natAbs) = M.2 + (d.natAbs.primeFactors.card : ℤ) := by
  classical
  let M := genuineEvenNormalization hW hE P h₀ hcont h9
  let a := genuineEvenCoefficient hW hE P h₀ hcont h9
  let F := Even.S0Filter W.S D₀
  have hgood : ∀ p ∈ d.natAbs.primeFactors, T.Good p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hprime, (Nat.Prime.coprime_iff_not_dvd hprime).mpr ?_⟩
    intro hpm
    exact hd.1.2.2 p (hmS p hprime hpm)
      (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  have hr := hd.2
  rw [ht, hA] at hr
  change symb T (coeffReading a M.2 F)
    (Symbols.primeConfig d.natAbs.primeFactors T.typ) = 1 at hr
  rw [symb_primeConfig T a M.2 F (hfactor _) d.natAbs.primeFactors hgood le_rfl] at hr
  change Symbols.coeffSymbol a M.2 F (∏ p ∈ d.natAbs.primeFactors, p) = 1 at hr
  rw [Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hd.1.2.1)] at hr
  unfold Symbols.coeffSymbol at hr
  split_ifs at hr with hu
  · exact hu
  · exact False.elim (zero_ne_one hr)

/-- The coefficient-square identity of the supplied genuine source gives
    its exact unit-value formula. Its existing depth is consumed; no new
    minimizer is selected and no attained index is identified with `kfin`. -/
theorem unit_value_of_genuine_source {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} (T : TypeData L ε)
    {A : L → Symbols.Config L → ZMod 2} {τ : L}
    (C : Even.CentralNormalization (Ecurve ℓ)) (hCW : C.Lstar = W.Lstar)
    (hW : PrintsAnalytic.WaldspurgerCor2) (hE : (Ecurve ℓ).IsElliptic) {D₀ : ℕ}
    (P : Even.EvenPhaseData (Ecurve ℓ) C (-1) W.S D₀)
    (h₀ : C.Lstar (-1 * (D₀ : ℤ)) ≠ 0)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : Even.EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (hfactor : ∀ B : ℕ, FixedUFactorization T
      (coeffReading (genuineEvenCoefficient hW hE P h₀ hcont h9)
        (genuineEvenNormalization hW hE P h₀ hcont h9).2 (Even.S0Filter W.S D₀)) B)
    (hA : A τ = genuineEvenSymbol T hW hE P h₀ hcont h9)
    {d : ℤ} (hd : SourceUnit W T A d)
    (ht : (Symbols.primeConfig d.natAbs.primeFactors T.typ).total = τ) :
    W.Lstar d ≠ 0 ∧ padicValRat 2 (W.Lstar d) = 2 * (omega d : ℤ) +
      (2 * (genuineEvenNormalization hW hE P h₀ hcont h9).2 +
        padicValRat 2 (C.Lstar (-1 * (D₀ : ℤ)))) := by
  let M := genuineEvenNormalization hW hE P h₀ hcont h9
  obtain ⟨hF, ha, hv⟩ := unit_reading_of_genuine_source T C hW hE P h₀ hcont h9
    hmS hfactor hA hd ht
  have hr : M.1 d.natAbs ≠ 0 := by
    change (M.1 d.natAbs : ℚ_[2]) ≠ 0 at ha
    exact_mod_cast ha
  have hvc : padicValRat 2 (M.1 d.natAbs) =
      M.2 + (d.natAbs.primeFactors.card : ℤ) := by
    change Padic.valuation (M.1 d.natAbs : ℚ_[2]) = _ at hv
    rwa [Padic.valuation_ratCast] at hv
  have hsq := (genuineEvenNormalization_spec hW hE P h₀ hcont h9).1
    d.natAbs (P.filter_mem d.natAbs hF)
  have hsquare : M.1 d.natAbs ^ 2 =
      C.Lstar (-1 * (d.natAbs : ℤ)) / C.Lstar (-1 * (D₀ : ℤ)) := hsq.2
  have hneg : d < 0 := hd.1.1
  have habs : (d.natAbs : ℤ) = -d := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have heqd : (-1 : ℤ) * (d.natAbs : ℤ) = d := by rw [habs]; ring
  rw [heqd] at hsquare
  have hLd : C.Lstar d ≠ 0 := by
    intro h0
    have hpow : M.1 d.natAbs ^ 2 = 0 := by rw [hsquare, h0, zero_div]
    exact (pow_ne_zero 2 hr) hpow
  have hval := congrArg (padicValRat 2) hsquare
  rw [padicValRat.pow, padicValRat.div hLd h₀] at hval
  have hval' : 2 * padicValRat 2 (M.1 d.natAbs) =
      padicValRat 2 (C.Lstar d) - padicValRat 2 (C.Lstar (-1 * (D₀ : ℤ))) := by
    exact_mod_cast hval
  have hω : (d.natAbs.primeFactors.card : ℤ) = (omega d : ℤ) :=
    ZInQ.Contrib.CloudB3RC53.EvenUpper.even_omega_eq d
  rw [← hCW]
  exact ⟨hLd, by dsimp [M] at hvc; linarith [hvc, hω]⟩

/-- Prepared genuine sources give a uniform bound for all observed units
    whose total types are prepared. The finite choice selects constants
    only, from the already supplied sources and their existing depths. -/
theorem units33a_of_preparedGenuineSources {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] [Fintype L] {ε : L →+ ZMod 2} (T : TypeData L ε)
    (C : Even.CentralNormalization (Ecurve ℓ)) (hW : PrintsAnalytic.WaldspurgerCor2)
    (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : Even.EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Symbols.Config L → ZMod 2)
    (hG : PreparedGenuineEvenSource W T C hW hE hcont h9 A)
    (hactive : ∀ d : ℤ, SourceUnit W T A d →
      PreparedType W T (Symbols.primeConfig d.natAbs.primeFactors T.typ).total) :
    ∃ C₀ : ℤ, Units33a W (SourceUnit W T A) C₀ := by
  classical
  let U : L → ℤ → Prop := fun τ d => SourceUnit W T A d ∧
    (Symbols.primeConfig d.natAbs.primeFactors T.typ).total = τ
  have hbounds : ∀ τ : L, ∃ B : ℤ, Units33a W (U τ) B := by
    intro τ
    by_cases hτ : PreparedType W T τ
    · obtain ⟨D₀, P, h₀, _, _, hfactor, hA⟩ := hG.2 τ hτ
      refine ⟨2 * (genuineEvenNormalization hW hE P h₀ hcont h9).2 +
        padicValRat 2 (C.Lstar (-1 * (D₀ : ℤ))), ?_⟩
      intro d hd
      obtain ⟨hLd, hval⟩ := unit_value_of_genuine_source T C hG.1 hW hE P h₀ hcont h9
        hmS hfactor hA hd.1 hd.2
      exact ⟨sourceUnit_ne_zero hd.1, hLd, hval.le⟩
    · refine ⟨0, fun d hd => False.elim ?_⟩
      exact hτ (hd.2 ▸ hactive d hd.1)
  choose B hB using hbounds
  have hb := units33a_of_finite_sources U B hB
  refine ⟨∑ τ : L, max (B τ) 0, fun d hd => ?_⟩
  exact hb d ⟨(Symbols.primeConfig d.natAbs.primeFactors T.typ).total, hd, rfl⟩

/-- Adapter from the genuine prepared-source binding to the conditional
    consequence interface. Only the actual-source unit bound and original
    normalization are derived here; level, scalar, exact partitionability,
    unit-type eligibility, and parameter cubes remain explicit inputs. -/
theorem sourceConsequenceInputs_of_preparedGenuineSources
    {ℓ : ℕ} {W : WData ℓ} {L : Type} [AddCommGroup L] [Fintype L]
    {ε : L →+ ZMod 2} (T : TypeData L ε)
    (C : Even.CentralNormalization (Ecurve ℓ)) (hW : PrintsAnalytic.WaldspurgerCor2)
    (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : Even.EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Symbols.Config L → ZMod 2)
    (hG : PreparedGenuineEvenSource W T C hW hE hcont h9 A)
    (hactive : ∀ d : ℤ, SourceUnit W T A d →
      PreparedType W T (Symbols.primeConfig d.natAbs.primeFactors T.typ).total)
    (hl : CurveLevel ℓ) (hs : Even.EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C)
    (hp : PartitionabilitySpec W T A) (hc : SourceCubeInputs W T A) :
    SourceConsequenceInputs W T A := by
  exact ⟨hl, ⟨C, hG.1⟩, hp, (scalar32_iff_even C hG.1).mpr hs,
    units33a_of_preparedGenuineSources T C hW hE hcont h9 hmS A hG hactive, hc⟩

/-- The genuine prepared-source adapter supplies the exact existing
    RC11 consumer. It does not discharge its remaining scalar or cube
    construction premises or choose any new minimum. -/
theorem rc11Inputs_of_preparedGenuineSources
    {ℓ : ℕ} {W : WData ℓ} {L : Type} [AddCommGroup L] [Fintype L]
    {ε : L →+ ZMod 2} (T : TypeData L ε)
    (C : Even.CentralNormalization (Ecurve ℓ)) (hW : PrintsAnalytic.WaldspurgerCor2)
    (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : Even.EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Symbols.Config L → ZMod 2)
    (hG : PreparedGenuineEvenSource W T C hW hE hcont h9 A)
    (hactive : ∀ d : ℤ, SourceUnit W T A d →
      PreparedType W T (Symbols.primeConfig d.natAbs.primeFactors T.typ).total)
    (hl : CurveLevel ℓ) (hs : Even.EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C)
    (hp : PartitionabilitySpec W T A) (hc : SourceCubeInputs W T A) :
    EvenUpperRC11Inputs W :=
  rc11Inputs_of_sourceConsequences
    (sourceConsequenceInputs_of_preparedGenuineSources T C hW hE hcont h9 hmS A hG hactive
      hl hs hp hc)

end ZInQ.Manuscript.RC.EvenUpperText

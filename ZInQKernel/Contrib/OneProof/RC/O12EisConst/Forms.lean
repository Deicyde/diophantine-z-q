import ZInQKernel.Contrib.OneProof.RC.O12Eisenstein.LocalBlocks
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Degeneracy

/-! The primitive weight-two Eisenstein form (ELLIOT, tex 9647–9654,
9762–9771, 9862–9864), its actual level raises, and the comparison of
their positive coefficients over a common field of definition. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12EisConst

open AddressGenuine O12 O12Eisenstein PrintsArith TauCeti UpperHalfPlane
open CongruenceSubgroup Matrix.SpecialLinearGroup
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {D K : Type*} [Field D] [Field K] {p : ℕ} [Fact p.Prime]

/-- The product of the two moduli, each to be taken at the conductor. -/
def pairLevel (E : CharacterPair D p) : ℕ := (p * E.awayLevel) * E.unramLevel

/-- Coefficient change on the ordered pair; it keeps the local factor and the position
of the weight twist. -/
abbrev mapPair (E : CharacterPair D p) (f : D →+* K) : CharacterPair K p where
  unramLevel := E.unramLevel
  awayLevel := E.awayLevel
  unramCoprime := E.unramCoprime
  awayCoprime := E.awayCoprime
  unram := E.unram.ringHomComp f
  away := E.away.ringHomComp f
  twistUnramified := E.twistUnramified

private theorem map_ramified (E : CharacterPair D p) (f : D →+* K) :
    (mapPair E f).ramified = E.ramified.ringHomComp f := by
  apply MulChar.ext
  intro u
  simp only [CharacterPair.ramified, MulChar.mul_apply, MulChar.ringHomComp_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, mapPair, quadraticDirichlet,
    map_mul, Int.coe_castRingHom, map_intCast]

private theorem map_divisorCoeff {m₁ m₂ : ℕ} (f : D →+* K)
    (a : DirichletCharacter D m₁) (b : DirichletCharacter D m₂) (n : ℕ) :
    divisorCoeff (a.ringHomComp f) (b.ringHomComp f) n = f (divisorCoeff a b n) := by
  simp [divisorCoeff, map_sum, map_mul]

theorem mapPair_coeff (E : CharacterPair D p) (f : D →+* K) (n : ℕ) :
    (mapPair E f).coeff n = f (E.coeff n) := by
  unfold CharacterPair.coeff
  rw [map_ramified]
  cases E.twistUnramified <;> simp only [mapPair, Bool.false_eq_true, ite_false, ite_true] <;>
    exact map_divisorCoeff f _ _ n

theorem coeff_one (E : CharacterPair D p) : E.coeff 1 = 1 := by
  have h {m₁ m₂ : ℕ} (a : DirichletCharacter D m₁) (b : DirichletCharacter D m₂) :
      divisorCoeff a b 1 = 1 := by simp [divisorCoeff, Nat.divisorsAntidiagonal_one]
  unfold CharacterPair.coeff
  split <;> exact h _ _

/-- The product nebentypus at the product level, transported to complex coefficients. -/
def pairNebentypus (E : CharacterPair D p) (c : D →+* ℂ) : (ZMod (pairLevel E))ˣ →* ℂˣ :=
  ((((E.ramified.changeLevel (dvd_mul_right _ _)) *
    (E.unram.changeLevel (dvd_mul_left _ _))).ringHomComp c).toUnitHom)

/-- ELLIOT (uncited): the normalized primitive pair gives a holomorphic weight-two
modular form with the stated positive expansion and product nebentypus. The constant
term is part of the form; the positive expansion does not set it to zero. -/
structure BaseForm (E : CharacterPair D p) (c : D →+* ℂ) where
  unram_primitive : E.unram.IsPrimitive
  ram_primitive : E.ramified.IsPrimitive
  form : ModularForm ((Gamma1 (pairLevel E)).map (mapGL ℝ)) 2
  character : form ∈ modFormCharSpace 2 (pairNebentypus E c)
  positive_expansion : ∀ n : PosIndex, (qExpansion 1 form).coeff n.val = c (E.coeff n.val)

variable {E : CharacterPair D p} {c : D →+* ℂ}

/-- One old copy at the required level, with the analytic normalization `f(dz)`. -/
def BaseForm.atLevel (F : BaseForm E c) {d N : ℕ} [NeZero d]
    (h : d * pairLevel E ∣ N) : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2 :=
  TauCeti.ModularForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) F.form

theorem BaseForm.atLevel_character (F : BaseForm E c) {d N : ℕ} [NeZero d]
    (h : d * pairLevel E ∣ N) :
    F.atLevel h ∈ modFormCharSpace 2 ((pairNebentypus E c).comp
      (ZMod.unitsMap ((dvd_mul_left (pairLevel E) d).trans h))) :=
  TauCeti.ModularForm.levelRaise_mem_modFormCharSpace_of_dvd h _ F.character

/-- Positive coefficients of the scaled old copy are computed over the common
field of definition, before either the complex or the 2-adic embedding. -/
theorem BaseForm.atLevel_coeff (F : BaseForm E c) {d N : ℕ} [NeZero d]
    (h : d * pairLevel E ∣ N) (s : D) (n : PosIndex) :
    (qExpansion 1 (c s • F.atLevel h)).coeff n.val =
      c (s * degenerate d E.coeff n.val) := by
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N)]
  simp only [PowerSeries.coeff_smul, smul_eq_mul, BaseForm.atLevel, map_mul]
  rw [TauCeti.ModularForm.qExpansion_levelRaise_coeff
    (one_mem_strictPeriods_Gamma1_map (pairLevel E)) (one_mem_strictPeriods_Gamma1_map N)]
  unfold degenerate
  split
  · rename_i hd
    have hn : n.val / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd
      (Nat.pos_of_ne_zero n.property) hd) (Nat.pos_of_ne_zero (NeZero.ne d)))
    exact congrArg (c s * ·) (F.positive_expansion ⟨_, hn⟩)
  · simp

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L} {X : GaloisConstituentModel T R ap B chiType}
variable {A : FourierData X} {i : X.I}

/-- ELLIOT (tex 9649–9654, 9754–9771): the chosen model column and the actual scaled
old copy have the same lift of their positive coefficients. Only the column
identification is assumed, with no divisor-sum equation over the model field. -/
structure ColumnRealization (F : BaseForm E c) (k : D →+* X.K) {d N : ℕ} [NeZero d]
    (h : d * pairLevel E ∣ N) (s : D) (A : FourierData X) (i : X.I) where
  lift : PosIndex → D
  complex_coeff : ∀ n, c (lift n) = (qExpansion 1 (c s • F.atLevel h)).coeff n.val
  model_coeff : ∀ n, k (lift n) = X.coefK (column X i 1) (A.index n)

theorem ColumnRealization.expansion (F : BaseForm E c) (k : D →+* X.K)
    {d N : ℕ} [NeZero d] (h : d * pairLevel E ∣ N) (s : D)
    (C : ColumnRealization F k h s A i) (n : PosIndex) :
    X.coefK (column X i 1) (A.index n) =
      k s * degenerate d (mapPair E k).coeff n.val := by
  have hl := c.injective ((C.complex_coeff n).trans (F.atLevel_coeff h s n))
  rw [← C.model_coeff, hl, map_mul]
  unfold degenerate
  split <;> simp [mapPair_coeff]

#print axioms map_ramified
#print axioms map_divisorCoeff
#print axioms mapPair_coeff
#print axioms coeff_one
#print axioms BaseForm.atLevel_character
#print axioms BaseForm.atLevel_coeff
#print axioms ColumnRealization.expansion

end ZInQ.Manuscript.RC.O12EisConst

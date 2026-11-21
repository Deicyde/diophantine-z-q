import ZInQKernel.HDecomp.Analytic.Torus

/-!
# The quotient for the theta line

For a Siegel matrix `Ω`, use the period multipliers of the existing
`BPAnalytic.riemannTheta` to glue copies of the complex line over the
covering space. The cocycle identity makes the gluing an equivalence
relation. The theta function then defines a section of the quotient, and
its zero locus pulls back to the zero locus of the function.

The quotient provides the total space for constructing the analytic
bundle and algebraizing its theta section.
-/

open scoped ContDiff

noncomputable section

namespace BPAnalytic.ThetaLine

open Matrix Complex

variable {g : ℕ}

/-- Integer coordinates of a period `Ωm + n`. -/
abbrev PeriodCoordinates (g : ℕ) := (Fin g → ℤ) × (Fin g → ℤ)

@[simp] private theorem intVec_zero : intVec (0 : Fin g → ℤ) = 0 := by
  funext i
  simp [intVec]

private theorem intVec_add (m n : Fin g → ℤ) :
    intVec (m + n) = intVec m + intVec n := by
  funext i
  simp [intVec]

/-- The translation of the covering space associated with integer period coordinates. -/
def periodShift (Ω : Matrix (Fin g) (Fin g) ℂ) : PeriodCoordinates g →+ (Fin g → ℂ) where
  toFun x := Ω *ᵥ intVec x.1 + intVec x.2
  map_zero' := by
    change Ω *ᵥ intVec 0 + intVec 0 = 0
    simp
  map_add' x y := by
    change Ω *ᵥ intVec (x.1 + y.1) + intVec (x.2 + y.2) =
      (Ω *ᵥ intVec x.1 + intVec x.2) + (Ω *ᵥ intVec y.1 + intVec y.2)
    simp only [intVec_add, mulVec_add]
    abel

theorem periodShift_mem (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : (Ω.map Complex.im).det ≠ 0) (x : PeriodCoordinates g) :
    periodShift Ω x ∈ periodLattice Ω hΩ :=
  (mem_periodLattice_iff Ω hΩ _).mpr ⟨x.1, x.2, rfl⟩

private theorem sum_periodVec (Ω : Matrix (Fin g) (Fin g) ℂ) (x : PeriodCoordinates g) :
    (∑ i, Sum.elim (fun j => (x.1 j : ℝ)) (fun j => (x.2 j : ℝ)) i • periodVec Ω i) =
      periodShift Ω x := by
  funext k
  change _ = (Ω *ᵥ intVec x.1 + intVec x.2) k
  simp [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, Complex.real_smul, periodVec,
    Matrix.mulVec, dotProduct, Pi.single_apply, intVec, mul_comm]

/-- The basis of periods gives unique integer coordinates for each translation. -/
theorem periodShift_injective (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : (Ω.map Complex.im).det ≠ 0) : Function.Injective (periodShift Ω) := by
  intro x y hxy
  have hz : periodShift Ω (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  let c : Fin g ⊕ Fin g → ℝ :=
    Sum.elim (fun j => ((x - y).1 j : ℝ)) (fun j => ((x - y).2 j : ℝ))
  have hc : ∑ i, c i • periodVec Ω i = 0 := (sum_periodVec Ω (x - y)).trans hz
  have hc0 := (Fintype.linearIndependent_iff.mp (periodVec_linearIndependent Ω hΩ)) c hc
  apply sub_eq_zero.mp
  apply Prod.ext
  · funext j
    change (x - y).1 j = 0
    have hj : ((x - y).1 j : ℝ) = 0 := hc0 (Sum.inl j)
    exact_mod_cast hj
  · funext j
    change (x - y).2 j = 0
    have hj : ((x - y).2 j : ℝ) = 0 := hc0 (Sum.inr j)
    exact_mod_cast hj

private def phase (Ω : Matrix (Fin g) (Fin g) ℂ) (m : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  -(Real.pi * I * (intVec m ⬝ᵥ (Ω *ᵥ intVec m))) - 2 * Real.pi * I * (intVec m ⬝ᵥ z)

/-- The multiplier relating theta at `z + Ωm + n` to theta at `z`. -/
def factor (Ω : Matrix (Fin g) (Fin g) ℂ) (x : PeriodCoordinates g) (z : Fin g → ℂ) : ℂ :=
  exp (phase Ω x.1 z)

theorem factor_ne_zero (Ω : Matrix (Fin g) (Fin g) ℂ)
    (x : PeriodCoordinates g) (z : Fin g → ℂ) : factor Ω x z ≠ 0 :=
  exp_ne_zero _

@[simp] theorem factor_zero_period (Ω : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    factor Ω 0 z = 1 := by
  change exp (phase Ω 0 z) = 1
  simp [phase]

/-- A fixed period multiplier is holomorphic on the covering space. -/
theorem contDiff_factor (Ω : Matrix (Fin g) (Fin g) ℂ) (x : PeriodCoordinates g) :
    ContDiff ℂ ω (factor Ω x) := by
  unfold factor phase dotProduct
  fun_prop

/-- Successive translations multiply the theta factors. The extra term in the
sum of the exponents is an integral multiple of `2πi`. -/
theorem factor_cocycle (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ωᵀ = Ω)
    (x y : PeriodCoordinates g) (z : Fin g → ℂ) :
    factor Ω x (z + periodShift Ω y) * factor Ω y z = factor Ω (x + y) z := by
  unfold factor
  rw [← exp_add]
  have hp :
      phase Ω x.1 (z + periodShift Ω y) + phase Ω y.1 z =
        phase Ω (x + y).1 z + ((-(x.1 ⬝ᵥ y.2 : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    change phase Ω x.1 (z + (Ω *ᵥ intVec y.1 + intVec y.2)) + phase Ω y.1 z =
      phase Ω (x.1 + y.1) z + ((-(x.1 ⬝ᵥ y.2 : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I)
    simp only [phase, intVec_add, mulVec_add, add_dotProduct, dotProduct_add,
      dotProduct_mulVec_symm hΩ (intVec x.1) (intVec y.1), intVec_dotProduct, Int.cast_neg]
    ring
  rw [hp, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- Translation on the covering space together with its action on the line. -/
def translate (Ω : Matrix (Fin g) (Fin g) ℂ) (x : PeriodCoordinates g)
    (p : (Fin g → ℂ) × ℂ) : (Fin g → ℂ) × ℂ :=
  (p.1 + periodShift Ω x, factor Ω x p.1 * p.2)

private theorem translate_zero (Ω : Matrix (Fin g) (Fin g) ℂ) (p : (Fin g → ℂ) × ℂ) :
    translate Ω 0 p = p := by
  apply Prod.ext <;> simp [translate]

private theorem translate_add (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ωᵀ = Ω)
    (x y : PeriodCoordinates g) (p : (Fin g → ℂ) × ℂ) :
    translate Ω (x + y) p = translate Ω x (translate Ω y p) := by
  apply Prod.ext
  · change p.1 + periodShift Ω (x + y) = p.1 + periodShift Ω y + periodShift Ω x
    rw [map_add]
    abel
  · change factor Ω (x + y) p.1 * p.2 =
      factor Ω x (p.1 + periodShift Ω y) * (factor Ω y p.1 * p.2)
    rw [← factor_cocycle Ω hΩ, mul_assoc]

/-- The orbits of period translations and fibre multiplication. -/
def periodRel (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ωᵀ = Ω) :
    Setoid ((Fin g → ℂ) × ℂ) where
  r p q := ∃ x : PeriodCoordinates g, q = translate Ω x p
  iseqv := by
    constructor
    · intro p
      exact ⟨0, (translate_zero Ω p).symm⟩
    · rintro p q ⟨x, rfl⟩
      exact ⟨-x, by rw [← translate_add Ω hΩ, neg_add_cancel, translate_zero]⟩
    · rintro p q t ⟨x, rfl⟩ ⟨y, rfl⟩
      exact ⟨y + x, (translate_add Ω hΩ y x p).symm⟩

/-- The underlying quotient of the theta line over the Siegel torus. -/
abbrev TotalSpace (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ωᵀ = Ω) :=
  Quotient (periodRel Ω hΩ)

variable (Ω : Matrix (Fin g) (Fin g) ℂ) (h : Ω ∈ SiegelSpace g)

/-- The lattice of the Siegel point underlying the theta line. -/
abbrev lattice := periodLattice Ω (det_im_ne_zero_of_mem_siegelSpace h)

/-- Projection to the existing quotient torus. -/
def projection : TotalSpace Ω h.1 → Torus (lattice Ω h) :=
  Quotient.lift (fun p => proj (lattice Ω h) p.1) (by
    intro p q hpq
    rcases hpq with ⟨x, rfl⟩
    apply (proj_eq_iff (lattice Ω h)).mpr
    change p.1 - (p.1 + periodShift Ω x) ∈ lattice Ω h
    rw [show p.1 - (p.1 + periodShift Ω x) = -periodShift Ω x by abel]
    exact (lattice Ω h).neg_mem (periodShift_mem Ω _ x))

/-- Every lift of a torus point identifies its fibre with `ℂ`. -/
def fibreAtLift (z : Fin g → ℂ) :
    ℂ ≃ {p : TotalSpace Ω h.1 // projection Ω h p = proj (lattice Ω h) z} :=
  Equiv.ofBijective (fun c => ⟨Quotient.mk (periodRel Ω h.1) (z, c), rfl⟩) (by
    constructor
    · intro c d heq
      have hq : Quotient.mk (periodRel Ω h.1) (z, c) =
          Quotient.mk (periodRel Ω h.1) (z, d) := congrArg Subtype.val heq
      obtain ⟨x, hx⟩ := Quotient.exact hq
      have hxz : z = z + periodShift Ω x := congrArg Prod.fst hx
      have hx0 : periodShift Ω x = 0 := by
        have hz' : z + periodShift Ω x = z + 0 := by simpa only [add_zero] using hxz.symm
        exact add_left_cancel hz'
      have hzero : x = 0 :=
        periodShift_injective Ω (det_im_ne_zero_of_mem_siegelSpace h)
          (hx0.trans (map_zero (periodShift Ω)).symm)
      have hcd : d = factor Ω x z * c := congrArg Prod.snd hx
      simpa [hzero] using hcd.symm
    · rintro ⟨q, hq⟩
      revert hq
      refine Quotient.inductionOn q ?_
      intro p hq
      have hbase : proj (lattice Ω h) p.1 = proj (lattice Ω h) z := hq
      have hmem := (proj_eq_iff (lattice Ω h)).mp hbase.symm
      obtain ⟨m, n, hmn⟩ := (mem_periodLattice_iff Ω _ _).mp hmem
      refine ⟨factor Ω (m, n) p.1 * p.2, Subtype.ext ?_⟩
      symm
      apply Quotient.sound
      refine ⟨(m, n), Prod.ext ?_ rfl⟩
      change z = p.1 + (Ω *ᵥ intVec m + intVec n)
      rw [show Ω *ᵥ intVec m + intVec n = z - p.1 from hmn.symm]
      abel)

/-- A change of lift multiplies the fibre coordinate by the theta factor. -/
theorem fibreAtLift_change (z : Fin g → ℂ) (x : PeriodCoordinates g) (c : ℂ) :
    (fibreAtLift Ω h (z + periodShift Ω x) (factor Ω x z * c)).val =
      (fibreAtLift Ω h z c).val := by
  change Quotient.mk (periodRel Ω h.1) (z + periodShift Ω x, factor Ω x z * c) =
    Quotient.mk (periodRel Ω h.1) (z, c)
  symm
  apply Quotient.sound
  exact ⟨x, rfl⟩

/-- The theta function defines a section of the quotient over the torus. -/
def thetaSection : Torus (lattice Ω h) → TotalSpace Ω h.1 :=
  Quotient.lift (fun z => Quotient.mk (periodRel Ω h.1) (z, riemannTheta Ω z)) (by
    intro z z' hz
    have heq : proj (lattice Ω h) z = proj (lattice Ω h) z' := Quotient.sound hz
    have hmem := (proj_eq_iff (lattice Ω h)).mp heq.symm
    obtain ⟨m, n, hmn⟩ := (mem_periodLattice_iff Ω _ _).mp hmem
    have hshift : z + periodShift Ω (m, n) = z' := by
      change z + (Ω *ᵥ intVec m + intVec n) = z'
      rw [show Ω *ᵥ intVec m + intVec n = z' - z from hmn.symm]
      abel
    apply Quotient.sound
    refine ⟨(m, n), Prod.ext hshift.symm ?_⟩
    change riemannTheta Ω z' = factor Ω (m, n) z * riemannTheta Ω z
    rw [← hshift]
    exact riemannTheta_add_period Ω h.1 z m n)

@[simp] theorem projection_thetaSection (p : Torus (lattice Ω h)) :
    projection Ω h (thetaSection Ω h p) = p := by
  refine Quotient.inductionOn p ?_
  intro z
  rfl

/-- In a lift to the covering space, the section vanishes exactly at a zero
of the theta function. This criterion respects the orbit relation. -/
theorem thetaSection_eq_zero_iff (z : Fin g → ℂ) :
    thetaSection Ω h (proj (lattice Ω h) z) = Quotient.mk (periodRel Ω h.1) (z, 0) ↔
      riemannTheta Ω z = 0 := by
  change Quotient.mk (periodRel Ω h.1) (z, riemannTheta Ω z) =
    Quotient.mk (periodRel Ω h.1) (z, 0) ↔ riemannTheta Ω z = 0
  constructor
  · intro he
    obtain ⟨x, hx⟩ := Quotient.exact he
    have hz : 0 = factor Ω x z * riemannTheta Ω z := congrArg Prod.snd hx
    exact (mul_eq_zero.mp hz.symm).resolve_left (factor_ne_zero Ω x z)
  · intro hz
    rw [hz]

end BPAnalytic.ThetaLine

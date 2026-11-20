import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Neighbour
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Invariance
import ZInQKernel.Contrib.OneProof.RC.O12StageVal.PM
import ZInQKernel.Contrib.OneProof.RC.LineIndex.Neighbours

/-! Assemble the Appendix F input from the actual product and the separately
stated remaining local transport data. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler O12StageVal ThetaCoeff ZInQ.Manuscript.RC.Odd

variable {O : Type} [CommRing O] {ell N M m : ℕ} [Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N) (hcop : N.Coprime ell)
variable (C : LevelRoots O N) (hne : 2 * m * N * ell ≠ 0)

abbrev levelRing := levelOrder ell h N hN
abbrev phaseFor := schwartzPhase (ell := ell) C m hne
abbrev GoodPrime (p : ℕ) := p.Prime ∧ p ∉ (phaseFor C hne).support

theorem good_not_dvd {p : ℕ} (hp : GoodPrime C hne p) :
    ¬ p ∣ 2 * m * N * ell := fun hd =>
  hp.2 (((phaseFor C hne).mem_support ⟨p, hp.1⟩).mpr
    ((mem_exceptionalPlaces m N ell hne ⟨p, hp.1⟩).mpr hd))

theorem good_away {p : ℕ} (hp : GoodPrime C hne p) : ¬ p ∣ N * ell := by
  intro hd
  apply good_not_dvd C hne hp
  simpa only [mul_assoc] using dvd_mul_of_dvd_right hd (2 * m)

theorem good_not_two {p : ℕ} (hp : GoodPrime C hne p) : p ≠ 2 := by
  rintro rfl
  apply good_not_dvd C hne hp
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right 2 m) N) ell

theorem good_not_dvd_m {p : ℕ} (hp : GoodPrime C hne p) : ¬ p ∣ m := by
  intro hd
  exact good_not_dvd C hne hp
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) N) ell)

def lines (p : ℕ) (hp : GoodPrime C hne p) :
    LineIndex (levelRing h hN) p hp.1.ne_zero :=
  letI : Fact p.Prime := ⟨hp.1⟩
  LineIndex.lineIndex (levelOrder_isEichler ell h N hN hcop) (good_away C hne hp)

theorem level_neg : -(ell : ℚ) < 0 :=
  neg_lt_zero.mpr (Nat.cast_pos.mpr (Fact.out : ell.Prime).pos)

abbrev ActualFrameCoordinates :=
  ∀ p (hp : GoodPrime C hne p) z,
    FrameCoordinates (⟨p, hp.1⟩ : Prime) (classRepresentative (R := levelRing h hN) z)

def stageFrame (D : ActualFrameCoordinates h hN C hne) (p : ℕ)
    (hp : GoodPrime C hne p) (z : ClassSet (levelRing h hN)) :
    AppF.PFrame p (StageRing O M) :=
  (D p hp z).frame (stageReduction O M) (by norm_num) (level_neg (ell := ell))
    (phaseFor C hne) (localFactor h C m)

def normAtClass (χ : FiniteUnits (levelRing h hN) →* Oˣ)
    (z : ClassSet (levelRing h hN)) : O := (χ (classRepresentative z) : O)

/-- The remaining weighted comparison uses the individually indexed actual
neighbour, and keeps its norm factor inside the integral reduction. -/
def WeightedNeighbourComparison (χ : FiniteUnits (levelRing h hN) →* Oˣ)
    (D : ActualFrameCoordinates h hN C hne) : Prop :=
  ∀ p (hp : GoodPrime C hne p) z i n,
    let z' := nb (fun _ h => h.1) (lines h hN hcop C hne) p z i
    stageReduction O M (normAtClass h hN χ z' * inner (schwartz h C m hN hne) z' n) =
      (jacobiSym (-(m : ℤ)) p : StageRing O M) *
        stageReduction O M (normAtClass h hN χ z) *
        (stageReduction O M (((phaseFor C hne).phase p)⁻¹ : Oˣ) *
          (stageFrame (M := M) h hN C hne D p hp z).nbrSum i n)

/-- A single indexed line has a specific local generator. Its three
comparisons concern the double coset, individual lattice vectors, and the
norm of the local generator; none is an equality of weighted coefficients. -/
structure IndexedNeighbourTransport (χ : FiniteUnits (levelRing h hN) →* Oˣ)
    (D : ActualFrameCoordinates h hN C hne) where
  step : ∀ p (hp : GoodPrime C hne p), letI : Fact p.Prime := ⟨hp.1⟩
    ClassSet (levelRing h hN) → Option (ZMod p) → (Bp p (-1) (-(ell : ℚ)))ˣ
  class_match : ∀ p (hp : GoodPrime C hne p) z i,
    (doubleCosetRel (levelRing h hN)).r
      (classRepresentative (nb (fun _ h => h.1) (lines h hN hcop C hne) p z i))
      (classRepresentative z * single (levelRing h hN) ⟨p, hp.1⟩ (step p hp z i))
  lattice : ∀ p (hp : GoodPrime C hne p) z i, (D p hp z).NeighbourLattice (step p hp z i) i
  norm : ∀ p (hp : GoodPrime C hne p) z i,
    (χ (single (levelRing h hN) ⟨p, hp.1⟩ (step p hp z i)) : O) =
      (jacobiSym (-(m : ℤ)) p : O)

/-- Reduce the weighted comparison to the independent local line, class,
and norm statements on the chosen representative. -/
theorem weightedNeighbour_of_transport (χ : FiniteUnits (levelRing h hN) →* Oˣ)
    (cov : NormCovariance (phaseFor C hne) (localFactor h C m) χ)
    (D : ActualFrameCoordinates h hN C hne)
    (T : IndexedNeighbourTransport h hN hcop C hne χ D) :
    WeightedNeighbourComparison (M := M) h hN hcop C hne χ D := by
  intro p hp z i n
  let v := classRepresentative (R := levelRing h hN) z
  let w := classRepresentative (nb (fun _ h => h.1) (lines h hN hcop C hne) p z i)
  let e := single (levelRing h hN) (⟨p, hp.1⟩ : Prime) (T.step p hp z i)
  let A := phaseFor C hne
  let W := localFactor h C m
  have hc : (χ (v * e) : O) * coefficientAt A W (v * e) n =
      (χ w : O) * coefficientAt A W w n :=
    weightedCoefficient_eq (by norm_num) level_neg A W cov.eps cov.local_conj χ
      cov.diagonal cov.units (T.class_match p hp z i) n
  have hs := (D p hp z).frame_neighbour (stageReduction O M) (by norm_num) (level_neg (ell := ell))
    A W (fun q _ => localFactor_scale h C m hN q) hp.2 (T.step p hp z i) i (T.lattice p hp z i) n
  change stageReduction O M ((χ w : O) * coefficientAt A W w n) =
    (jacobiSym (-(m : ℤ)) p : StageRing O M) * stageReduction O M (χ v : O) *
      (stageReduction O M ((A.phase p)⁻¹ : Oˣ) *
        (stageFrame (M := M) h hN C hne D p hp z).nbrSum i n)
  change stageReduction O M (coefficientAt A W (v * e) n) =
    stageReduction O M ((A.phase p)⁻¹ : Oˣ) *
      (stageFrame (M := M) h hN C hne D p hp z).nbrSum i n at hs
  rw [← hc, map_mul, hs, map_mul, Units.val_mul, show (χ e : O) =
      (jacobiSym (-(m : ℤ)) p : O) from T.norm p hp z i, map_mul, map_intCast, mul_comm
    (stageReduction O M (χ v : O))]

/-- Conditional constructor for the actual finite Schwartz product; the
unproved transport laws occur as explicit parameters. -/
def pmLocal (χ : FiniteUnits (levelRing h hN) →* Oˣ)
    (cov : NormCovariance (phaseFor C hne) (localFactor h C m) χ)
    (D : ActualFrameCoordinates h hN C hne)
    (hNb : WeightedNeighbourComparison (M := M) h hN hcop C hne χ D) : PMLocal O (levelRing h hN) M N ell where
  ha := by norm_num
  hb := level_neg
  m := m
  support := (phaseFor C hne).support
  away := fun _ hp hs => good_away C hne ⟨hp, hs⟩
  neTwo := fun _ hp hs => good_not_two C hne ⟨hp, hs⟩
  goodM := fun _ hp hs => good_not_dvd_m C hne ⟨hp, hs⟩
  lines := lines h hN hcop C hne
  f := schwartz h C m hN hne
  f_conj := fun z u hu x => weight_conj (by norm_num) level_neg _ _ χ cov z u hu x
  χN := normAtClass h hN χ
  finiteSupp := schwartz_finiteSupp h C m hN hne
  thetaZero := schwartz_zero h C m hN hne
  s := fun p => (phaseFor C hne).phase p
  sinv := fun p => (((phaseFor C hne).phase p)⁻¹ : Oˣ)
  sUnit := fun p _ _ => (phaseFor C hne).phase_unit p
  sOrder := fun p hp hs => ⟨(phaseFor C hne).exponent, (phaseFor C hne).phase_order ⟨p, hp⟩ hs⟩
  η := (phaseFor C hne).eta m
  ηMul := (phaseFor C hne).eta_mul
    ⟨⟨ell, Fact.out⟩, (mem_exceptionalPlaces m N ell hne _).mpr (dvd_mul_left _ _)⟩ m
  ηOne := (phaseFor C hne).eta_one m
  ηGood := fun p hp hs => (phaseFor C hne).eta_good m ⟨p, hp⟩ hs
  parity := (phaseFor C hne).unaryParity
  frame := stageFrame h hN C hne D
  frameTheta := fun p hp z n => (D p hp z).frame_theta _ (by norm_num) level_neg _ _ n
  frameScale := fun p hp z x => (D p hp z).frame_scale _ (by norm_num) level_neg _ _
    (fun q _ => localFactor_scale h C m hN q) hp.2 x
  frameNb := hNb

variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}

variable (G : PM.Geometry K (levelRing h hN) N Ebar ap) (d : PM.Evaluation K Ebar M) (L : ℕ)
variable (χ : FiniteUnits (levelRing h hN) →* Oˣ)
variable (cov : NormCovariance (phaseFor C hne) (localFactor h C m) χ)
variable (D : ActualFrameCoordinates h hN C hne)
variable (hNb : WeightedNeighbourComparison (M := M) h hN hcop C hne χ D)

/-- Apply the existing stage constructor to the local join. -/
def actualStage : AppF.ThetaStage (StageRing O M) :=
  pmStage G d L (pmLocal h hN hcop C hne χ cov D hNb)

/-- Apply the existing valuation lift to the same stage and the same weights. -/
def actualValLift : Lift (actualStage h hN hcop C hne G d L χ cov D hNb) :=
  pmValLift G d L (pmLocal h hN hcop C hne χ cov D hNb)

end ZInQ.Manuscript.RC.ThetaJoin

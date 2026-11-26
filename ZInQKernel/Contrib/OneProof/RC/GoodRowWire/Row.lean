import ZInQKernel.Contrib.OneProof.RC.GoodRowWire.SamePlace
import ZInQKernel.Contrib.OneProof.RC.ModelTarget.Supply
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric5.StagePrimes
import ZInQKernel.Contrib.OneProof.RC.PMWire.CM
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.ActualFamily

/-! **The assembled `PMWire.GoodRow` at every stage prime** (tex 8476–8492).

For a stage setup `s`, a stage `i` with prime `p := (s.q.stage i).p`, the hypothesis
`hB : (N φ(N)).primeFactors ⊆ s.B` (with `N := StageKummer.level ℓ`) and the same-place data
`S`, `stageRow` is the `GoodRow` that `PMWire.oddStagedOfGoodRows` takes at stage `i`
(`RC/PMWire/Assembly.lean:120–122`), with `R := LocalIntegers p`:

* `closed`, `M`, `smoothM`, `reducedM`, `separatedM`, `denseGeneric`, `source`: the pinned
  integral model `Pinned.Y0Level h₅ htame h₂` of the levels lane (`RC/ModelLevels3`) and its
  generic source `ModelNeron.source` (neron lane, `RC/ModelNeron`);
* `E`, `groupE`, `neron`, `jE`, `properGenericE`, `geomIntGenericE`, `readComplex`,
  `readComplex_eq`, `read`, `read_frob`: the good cubic of `EcurveZ ℓ` over `ℤ_(p)`
  (target lane, `ModelTarget.goodTarget`, assembled through `GoodTarget.toGoodRow`);
* `extension`: `ModelGeneric5.goodRow_extension` (witness `Wint`, generic5 lane);
* `point`, `point_W`, `point_frob`, `frobenius_sq`: from `S : SamePlaceData …` (the same-place
  lane in the hCM lane); `point_W` through `SamePlaceData.point_W_choose`.

The stage-prime hypotheses are `h₅ := stagePrime_five_le s i`, `htame :=
stagePrime_not_dvd_tame s hN hB i`, `h₂ := two_le_level hN` (generic5), and `hΔ :=
StageKummer.goodAt s i`. `stage_coprime` derives the `hcop` of `oddStagedOfGoodRows` from `hB`.
Provenance: wiring only, on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels
open scoped WeierstrassCurve Classical
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.GoodRowWire

open PMGeometry (ResidueAt ReducedEquation)
open PreparedParam (projectiveOverQ)

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : StageKummer.Setup I L)
  (hN : 0 < StageKummer.level ℓ)
  (hB : (StageKummer.level ℓ * (StageKummer.level ℓ).totient).primeFactors ⊆ s.B)

include hN hB in
/-- **`hcop` of `PMWire.oddStagedOfGoodRows` from `hB`**: every stage prime is prime to the
level, since it does not divide `N φ(N)` (`ModelGeneric5.stagePrime_not_dvd_tame`). -/
theorem stage_coprime (i : ℕ) : (StageKummer.level ℓ).Coprime (s.q.stage i).p :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (s.q.stage i).prime).mpr
    fun h => ModelGeneric5.stagePrime_not_dvd_tame s hN hB i (dvd_mul_of_dvd_left h _))

variable [NeZero (StageKummer.level ℓ)]

/-- **The same-place input at stage `i`** (owner: the same-place lane in the hCM lane;
tex 8479–8492): `SamePlaceData` on the pinned model at `ell := (s.q.stage i).p`,
`N := StageKummer.level ℓ`, with the stage-prime hypotheses of generic5, over the residue field
`ResidueAt (StageKummer.place s i)` of the chosen place and the coarse fibre `X`. -/
abbrev StageSamePlace (X : PMAdelic.CoarseFibre) (i : ℕ) : Type :=
  SamePlaceData (ModelGeneric5.stagePrime_five_le s i) (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i)
    (ModelGeneric5.two_le_level hN) (ResidueAt (StageKummer.place s i)) X

variable [((EcurveZ ℓ)⁄ℚ).IsElliptic]
  (π : (X0Model3.model (StageKummer.level ℓ)).X ⟶ Proj ((EcurveZ ℓ)⁄ℚ).toProjective.grading)
  (hQ : π ≫ projectiveOverQ ((EcurveZ ℓ)⁄ℚ) = (X0Model3.model (StageKummer.level ℓ)).overQ)

/-- **The `GoodRow` at stage `i`** from the pinned integral model (levels and neron lanes), the
good cubic of `EcurveZ ℓ` (target lane, `hΔ := StageKummer.goodAt s i`), the integral
Atkin–Lehner extension (generic5 lane) and the same-place data `S` (same-place lane). Its type
is the type of `G i` in `PMWire.oddStagedOfGoodRows` (`RC/PMWire/Assembly.lean:120–122`) with
`R i := LocalIntegers (s.q.stage i).p`. -/
def stageRow {X : PMAdelic.CoarseFibre} (i : ℕ) (S : StageSamePlace s hN hB X i) :
    PMWire.GoodRow (LocalIntegers (s.q.stage i).p) (s.q.stage i).p (StageKummer.level ℓ)
      (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) X
      (PMWire.fixedMap (C := EcurveZ ℓ) π hQ) :=
  haveI := Pinned.Y0Level_smooth (ModelGeneric5.stagePrime_five_le s i)
    (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN)
  haveI := ModelNeron.reducedM (ModelGeneric5.stagePrime_five_le s i)
    (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN)
  haveI := ModelNeron.separatedM (ModelGeneric5.stagePrime_five_le s i)
    (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN)
  haveI : IsDominant (PMWire.genericProjection (Pinned.Y0Level (ModelGeneric5.stagePrime_five_le s i)
      (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN))) :=
    ModelNeron.denseGeneric (ModelGeneric5.stagePrime_five_le s i)
      (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN)
  (ModelTarget.goodTarget (s.q.stage i).p (EcurveZ ℓ) (ResidueAt (StageKummer.place s i))
      (ModelGeneric5.stagePrime_five_le s i) (StageKummer.goodAt s i)).toGoodRow
    (Pinned.Y0Level (ModelGeneric5.stagePrime_five_le s i)
      (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN))
    (ModelNeron.source (ModelGeneric5.stagePrime_five_le s i)
      (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN))
    S.point
    (ModelGeneric5.goodRow_extension (ModelGeneric5.stagePrime_five_le s i)
      (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN))
    (S.point_W_choose _) S.point_frob S.frobenius_sq

/-! ### Every field is the actual object of its lane -/

variable {X : PMAdelic.CoarseFibre} (i : ℕ) (S : StageSamePlace s hN hB X i)

theorem stageRow_closed : (stageRow s hN hB π hQ i S).closed = ModelNeron.closed (s.q.stage i).p :=
  rfl

theorem stageRow_M : (stageRow s hN hB π hQ i S).M =
    Pinned.Y0Level (ModelGeneric5.stagePrime_five_le s i)
      (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN) :=
  rfl

theorem stageRow_source : HEq (stageRow s hN hB π hQ i S).source
    (ModelNeron.source (ModelGeneric5.stagePrime_five_le s i)
      (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN)) :=
  HEq.rfl

theorem stageRow_E : (stageRow s hN hB π hQ i S).E =
    ModelTarget.detE (s.q.stage i).p (EcurveZ ℓ) :=
  rfl

theorem stageRow_point : HEq (stageRow s hN hB π hQ i S).point S.point :=
  HEq.rfl

/-- The integral Atkin–Lehner operator of the assembled row is generic5's `Wint`. -/
theorem stageRow_W (q : ℕ) (hq : q.Prime) (he : 0 < (StageKummer.level ℓ).factorization q) :
    HEq ((stageRow s hN hB π hQ i S).W q hq he)
      (ModelGeneric5.Wint (ModelGeneric5.stagePrime_five_le s i)
        (ModelGeneric5.stagePrime_not_dvd_tame s hN hB i) (ModelGeneric5.two_le_level hN)
        (TauCeti.Nat.isExactDivisor_primePow (N := StageKummer.level ℓ) (p := q))) :=
  heq_of_eq (ModelGeneric5.eq_Wint_of_extendsAtkin _ _ _ q
    ((stageRow s hN hB π hQ i S).extension q hq he).choose_spec)

#print axioms stage_coprime
#print axioms stageRow
#print axioms stageRow_closed
#print axioms stageRow_M
#print axioms stageRow_source
#print axioms stageRow_E
#print axioms stageRow_point
#print axioms stageRow_W

end ZInQ.Manuscript.RC.GoodRowWire

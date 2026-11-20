import ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LevelTheta
import ZInQKernel.Contrib.OneProof.RC.Adelic.Hecke

/-! Transport each line from the indexed ideal generator to the chosen adelic
representative. The lattice comparison and the class comparison use the
same one-place step. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaClose

open Adelic Eichler LineIndex ThetaJoin
open scoped Quaternion

set_option maxHeartbeats 1400000

variable {a b : ℚ} {R : Order a b}

private def conjugateChart (q : Prime) (r : (Bp q.val a b)ˣ) :
    Bp q.val a b ≃ₐ[ℚ_[q.val]] Bp q.val a b where
  toFun x := (r⁻¹ : (Bp q.val a b)ˣ).val * x * r.val
  invFun x := r.val * x * (r⁻¹ : (Bp q.val a b)ˣ).val
  left_inv x := by
    change r.val * (r.inv * x * r.val) * r.inv = x
    simp only [mul_assoc, ← mul_assoc r.val r.inv, Units.val_inv, one_mul, mul_one]
  right_inv x := by
    change r.inv * (r.val * x * r.inv) * r.val = x
    simp only [mul_assoc, ← mul_assoc r.inv r.val, Units.inv_val, one_mul, mul_one]
  map_mul' x y := by
    change (↑r⁻¹ * (x * y) * ↑r : Bp q.val a b) =
      (↑r⁻¹ * x * ↑r) * (↑r⁻¹ * y * ↑r)
    simp only [mul_assoc, ← mul_assoc (r : Bp q.val a b) (↑r⁻¹ : Bp q.val a b),
      Units.mul_inv, one_mul]
  map_add' x y := by simp only [mul_add, add_mul]
  commutes' t := by
    rw [← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one]

private theorem conjugateChart_mem (q : Prime) (r : localUnits R q) (x : Bp q.val a b) :
    conjugateChart q r.val x ∈ R.completion q.val ↔ x ∈ R.completion q.val := by
  let u : (Bp q.val a b)ˣ := r.val
  let T := R.completion q.val
  change u.inv * x * u.val ∈ T ↔ x ∈ T
  have hu : u.val ∈ T := r.prop.1
  have hi : u.inv ∈ T := r.prop.2
  constructor
  · intro hx
    have hh := T.mul_mem (T.mul_mem hu hx) hi
    simpa only [mul_assoc, ← mul_assoc u.val u.inv, Units.val_inv, one_mul, mul_one] using hh
  · intro hx
    exact T.mul_mem (T.mul_mem hi hx) hu

/-- Use the indexed generator's chart on vectors pulled back by the chosen
adelic representative. -/
def transportedSplit (q : Prime) (S : Split R q.val) (r : localUnits R q) : Split R q.val where
  alg := (conjugateChart q r.val).trans S.alg
  order_eq := by
    change (S.alg ∘ conjugateChart q r.val) '' (R.completion q.val : Set _) = _
    rw [Set.image_comp, show conjugateChart q r.val '' (R.completion q.val : Set _) =
      (R.completion q.val : Set _) from ?_, S.order_eq]
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact (conjugateChart_mem q r y).mpr hy
    · intro hx
      refine ⟨(conjugateChart q r.val).symm x, ?_, AlgEquiv.apply_symm_apply _ _⟩
      apply (conjugateChart_mem q r _).mp
      rwa [AlgEquiv.apply_symm_apply]

private theorem at_step (q : Prime) (v : FiniteUnits R) (u : (Bp q.val a b)ˣ)
    (x : B a b) :
    atRep (v * single R q u) q x =
      (u⁻¹ : (Bp q.val a b)ˣ).val * atRep v q x * u.val := by
  have hu : (v * single R q u).val q = v.val q * u := by
    change v.val q * (single R q u).val q = _
    rw [single_same]
  unfold atRep
  rw [hu, mul_inv_rev, Units.val_mul, Units.val_mul]
  noncomm_ring

private theorem local_step_iff (q : Prime) (v : FiniteUnits R) (S : Split R q.val)
    (r : localUnits R q) (L : Option (ZMod q.val)) (x : B a b) :
    atRep (v * single R q (r.val * heckeBasis q S L)) q x ∈ R.completion q.val ↔
      ∃ T : Mat ℤ_[q.val], (transportedSplit q S r).alg (atRep v q x) *
        matrixCast q.val (basisMatrix q.val L) =
          matrixCast q.val (basisMatrix q.val L * T) := by
  let k := heckeBasis q S L
  let u : (Bp q.val a b)ˣ := r.val
  let c := conjugateChart q r.val (atRep v q x)
  have hc : c = u.inv * atRep v q x * u.val := rfl
  have h : atRep (v * single R q (r.val * k)) q x = k.inv * c * k.val := by
    rw [at_step, mul_inv_rev, Units.val_mul, Units.val_mul, hc]
    change k.inv * u.inv * atRep v q x * (u.val * k.val) =
      k.inv * (u.inv * atRep v q x * u.val) * k.val
    simp only [mul_assoc]
  rw [h]
  change k.inv * c * k.val ∈ (R.completion q.val : Set _) ↔ _
  rw [← S.range_embed]
  have hk : S.alg k.val = matrixCast q.val (basisMatrix q.val L) := by
    rw [show k.val = S.embed (basisMatrix q.val L) from heckeBasis_val q S L]
    exact S.alg.apply_symm_apply _
  have hcast (T : Mat ℤ_[q.val]) : S.alg (S.embed T) = matrixCast q.val T :=
    S.alg.apply_symm_apply _
  change (∃ T, S.embed T = k.inv * c * k.val) ↔
    ∃ T, S.alg c * matrixCast q.val (basisMatrix q.val L) =
      matrixCast q.val (basisMatrix q.val L * T)
  constructor
  · rintro ⟨T, hT⟩
    have he : k.val * S.embed T = c * k.val := by
      rw [hT, ← mul_assoc k.val, ← mul_assoc k.val, Units.val_inv, one_mul]
    have hh := congrArg (fun y => S.alg y) he
    simp only [map_mul, hk, hcast] at hh
    refine ⟨T, ?_⟩
    rw [map_mul, ← hh]
  · rintro ⟨T, hT⟩
    have he : c * k.val = k.val * S.embed T := by
      apply S.alg.injective
      simp only [map_mul, hk, hcast] at *
      exact hT
    refine ⟨T, ?_⟩
    rw [mul_assoc, he, ← mul_assoc, Units.inv_val, one_mul]

private theorem scale_p_away_iff (q p : Prime) (hq : q ≠ p) (v : FiniteUnits R) (x : B a b) :
    atRep v q (p.val • x) ∈ R.completion q.val ↔ atRep v q x ∈ R.completion q.val := by
  let T := R.completion q.val
  have hd : ¬ q.val ∣ p.val := fun h =>
    hq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.prop p.prop).mp h))
  let u := PhaseData.natUnit q p.val hd
  rw [atRep_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[q.val], ← PhaseData.natUnit_val q p.val hd]
  constructor
  · intro h
    have hm := T.toSubmodule.smul_mem u.inv h
    exact (congrArg (fun y : Bp q.val a b => y ∈ T.toSubmodule)
      (localUnit_smul_cancel q u (atRep v q x))).mp hm
  · intro hx
    exact T.toSubmodule.smul_mem u.val hx

set_option maxHeartbeats 800000 in
/-- Rational intersection and the mod-p² test for the aligned one-place step. -/
theorem transportedNeighbourLattice (q : Prime) (v : FiniteUnits R) (S : Split R q.val)
    (r : localUnits R q) (L : Option (ZMod q.val))
    (hInt : ∀ y : Ternary v, ∃ n : ℕ, Visibility.nrd y.val = (n : ℚ)) :
    (GoodCoordinates.coordinates q v (transportedSplit q S r) hInt).NeighbourLattice
      (r.val * heckeBasis q S L) L := by
  let u := r.val * heckeBasis q S L
  let U := transportedSplit q S r
  let D := GoodCoordinates.coordinates q v U hInt
  let B := basisMatrix q.val L
  let f := matrixCast q.val
  have hp : (q.val : ℚ_[q.val]) ≠ 0 := Nat.cast_ne_zero.mpr q.prop.ne_zero
  have cast_smul (A : Mat ℤ_[q.val]) :
      f ((q.val : ℤ_[q.val]) • A) = (q.val : ℚ_[q.val]) • f A := by
    ext i j
    change (↑((q.val : ℤ_[q.val]) * A i j) : ℚ_[q.val]) =
      (q.val : ℚ_[q.val]) * (A i j : ℚ_[q.val])
    rw [PadicInt.coe_mul, PadicInt.coe_natCast]
  intro x hx
  let X := U.alg (atRep v q x)
  have scale : U.alg (atRep v q (q.val • x)) = (q.val : ℚ_[q.val]) • X := by
    rw [atRep_nsmul, ← Nat.cast_smul_eq_nsmul ℚ_[q.val], map_smul]
  have adj : f B * f B.adjugate = (q.val : ℚ_[q.val]) • 1 := by
    rw [← map_mul, Matrix.mul_adjugate, basisMatrix_det, cast_smul, map_one]
  constructor
  · intro h
    have hl : ∀ t : Prime, atRep (v * single R q u) t x ∈ R.completion t.val :=
      (mem_leftRing_iff _ _).mp h
    obtain ⟨T, hT⟩ := (local_step_iff q v S r L x).mp (hl q)
    change X * f B = f (B * T) at hT
    have hY : (q.val : ℚ_[q.val]) • X = f (B * T * B.adjugate) := by
      rw [map_mul, ← hT, Matrix.mul_assoc, adj, Matrix.mul_smul, Matrix.mul_one]
    have hy : (q.val • x) ∈ (fromAdelic v).val.leftRing := by
      apply (mem_leftRing_iff _ _).mpr
      intro t
      by_cases ht : t = q
      · subst t
        change atRep v q (q.val • x) ∈ (R.completion q.val : Set _)
        rw [← U.range_embed]
        refine ⟨B * T * B.adjugate, U.alg.injective ?_⟩
        change U.alg (U.alg.symm _) = _
        rw [AlgEquiv.apply_symm_apply, scale, hY]
      · apply (scale_p_away_iff t q ht v x).mpr
        simpa only [atRep_single_away v ht u x] using hl t
    have htr : (q.val • x).re = 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, QuaternionAlgebra.re_smul, hx, smul_zero]
    let y : Ternary v := ⟨q.val • x, hy, htr⟩
    refine ⟨y, rfl, (coord_memNbr_iff D y L).mpr ⟨T, ?_⟩⟩
    have hcast : f (D.matrix y) = (q.val : ℚ_[q.val]) • X :=
      (GoodCoordinates.cast_matrix q v U y).trans scale
    apply Matrix.map_injective (show Function.Injective
      (algebraMap ℤ_[q.val] ℚ_[q.val]) from Subtype.val_injective)
    change f (D.matrix y * B) = f ((q.val : ℤ_[q.val]) • (B * T))
    rw [map_mul, cast_smul, hcast, Matrix.smul_mul, hT]
  · rintro ⟨y, hy, ht⟩
    obtain ⟨T, hT⟩ := (coord_memNbr_iff D y L).mp ht
    have hcast : f (D.matrix y) = (q.val : ℚ_[q.val]) • X :=
      (GoodCoordinates.cast_matrix q v U y).trans (by rw [hy, scale])
    apply (mem_leftRing_iff _ _).mpr
    intro t
    by_cases htq : t = q
    · subst t
      apply (local_step_iff q v S r L x).mpr
      refine ⟨T, smul_right_injective _ hp ?_⟩
      have hh := congrArg f hT
      change f (D.matrix y * B) = f ((q.val : ℤ_[q.val]) • (B * T)) at hh
      rwa [map_mul, cast_smul, hcast, Matrix.smul_mul] at hh
    · change atRep (v * single R q u) t x ∈ R.completion t.val
      rw [atRep_single_away v htq u x]
      apply (scale_p_away_iff t q htq v x).mp
      rw [← hy]
      exact (mem_leftRing_iff _ _).mp y.prop.1 t

section Level

variable {O : Type} [CommRing O] {ell N m : ℕ} [Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N) (hcop : N.Coprime ell)
variable (C : LevelRoots O N) (hne : 2 * m * N * ell ≠ 0)

variable (q : Prime) (hq : ¬ q.val ∣ N * ell)
variable (z : ClassSet (levelRing h hN))

private abbrev chart :=
  LineIndex.chartAt (levelOrder_isEichler ell h N hN hcop) hq z

/-- The integral unit relating the two independently chosen generators. -/
def correction : localUnits (levelRing h hN) q := by
  let v := classRepresentative z
  let g := (chart h hN hcop q hq z).gen
  refine ⟨(v.val q)⁻¹ * g, (localRight_eq_iff q _ _).mp ?_⟩
  rw [← fromAdelic_completion, fromAdelic_classRepresentative]
  exact SetLike.coe_injective ((chart h hN hcop q hq z).ideal_eq.trans
    (localRight_set q g).symm)

variable (L : Option (ZMod q.val))

/-- The step has its correction on the left, so the resulting lattice has
the same indexed basis as the step formed on the aligned lift. -/
def indexedStep : (Bp q.val (-1) (-(ell : ℚ)))ˣ :=
  (correction h hN hcop q hq z).val *
    heckeBasis q (chart h hN hcop q hq z).split L

set_option maxHeartbeats 600000 in
theorem indexedStep_class :
    idealsEquiv (levelRing h hN)
      (Quotient.mk _ (classRepresentative z *
        single (levelRing h hN) q (indexedStep h hN hcop q hq z L))) =
      nbAt (LineIndex.lineIndex (levelOrder_isEichler ell h N hN hcop) hq) z L := by
  rw [← heckeStep_eq_nbAt q (levelOrder_isEichler ell h N hN hcop) hq]
  let R := levelRing h hN
  let v := classRepresentative z
  let k := heckeBasis q (chart h hN hcop q hq z).split L
  let w := v * single R q (indexedStep h hN hcop q hq z L)
  let v' := aligned q (levelOrder_isEichler ell h N hN hcop) hq z
  let w' := v' * single R q k
  change idealsEquiv R (Quotient.mk _ w) = idealsEquiv R (Quotient.mk _ w')
  rw [idealsEquiv_mk, idealsEquiv_mk]
  congr 1
  apply Subtype.ext
  apply RightIdeal.ext
  ext x
  change (∀ s : Prime, toLocal s.val x ∈ localRight R s (w.val s)) ↔
    (∀ s : Prime, toLocal s.val x ∈ localRight R s (w'.val s))
  apply forall_congr'
  intro s
  by_cases hs : s = q
  · subst s
    have hw : w.val q = w'.val q := by
      change v.val q * (single R q _).val q = v'.val q * (single R q _).val q
      rw [single_same, single_same, aligned_gen]
      change v.val q * ((v.val q)⁻¹ * _ * k) = _ * k
      rw [← mul_assoc, mul_inv_cancel_left]
    rw [hw]
  · have hw : w.val s = v.val s := by
      change v.val s * (single R q _).val s = _
      rw [single_away hs, mul_one]
    have hw' : w'.val s = v'.val s := by
      change v'.val s * (single R q _).val s = _
      rw [single_away hs, mul_one]
    rw [hw, hw', ← fromAdelic_completion, ← fromAdelic_completion,
      fromAdelic_classRepresentative, aligned_ideal]

private theorem heckeBasis_norm (S : Split (levelRing h hN) q.val) :
    (valHom q (localNormHom q (heckeBasis q S L))).toAdd = 1 := by
  change ((heckeBasis q S L : Bp q.val (-1) (-(ell : ℚ))) *
    star (heckeBasis q S L : Bp q.val (-1) (-(ell : ℚ)))).re.valuation = _
  rw [← (split_invariants _ _ S.alg _).2, heckeBasis_val]
  change (S.alg (S.alg.symm (matrixCast q.val (basisMatrix q.val L)))).det.valuation = _
  rw [AlgEquiv.apply_symm_apply]
  change (((algebraMap ℤ_[q.val] ℚ_[q.val]).mapMatrix (basisMatrix q.val L)).det).valuation = _
  rw [← RingHom.map_det (algebraMap ℤ_[q.val] ℚ_[q.val]), basisMatrix_det, map_natCast,
    Padic.valuation_p]

theorem indexedStep_valuation :
    (valHom q (localNormHom q (indexedStep h hN hcop q hq z L))).toAdd = 1 := by
  rw [indexedStep, map_mul, map_mul, val_localNorm_of_orderUnit h hN q, one_mul]
  exact heckeBasis_norm h hN q L _

/-- The transported coordinates keep the original representative for the
product and the original line labels for the stage. -/
def alignedFrame : ActualFrameCoordinates h hN C hne := fun p hp z =>
  letI : Fact p.Prime := ⟨hp.1⟩
  let q : Prime := ⟨p, hp.1⟩
  let hq := good_away C hne hp
  GoodCoordinates.coordinates q (classRepresentative z)
    (transportedSplit q (chart h hN hcop q hq z).split (correction h hN hcop q hq z))
    (lattice_norm_integral h hN (classRepresentative z))

/-- All three comparisons for the indexed neighbour on the transported frame. -/
def indexedTransport (hm : m % 4 = 3) (hms : Squarefree m) :
    IndexedNeighbourTransport h hN hcop C hne (levelNormCharacter h hN C hne)
      (alignedFrame h hN hcop C hne) where
  step p hp z L := indexedStep h hN hcop ⟨p, hp.1⟩ (good_away C hne hp) z L
  class_match p hp z L := by
    classical
    apply Quotient.exact
    apply (idealsEquiv (levelRing h hN)).injective
    rw [idealsEquiv_mk, fromAdelic_classRepresentative, indexedStep_class, nb, dite_eq_left hp]
    exact Quotient.out_eq _
  lattice p hp z L := transportedNeighbourLattice ⟨p, hp.1⟩ (classRepresentative z) _ _ L
    (lattice_norm_integral h hN (classRepresentative z))
  norm p hp z L := levelNormCharacter_single h hN C hne hp hm hms _
    (indexedStep_valuation h hN hcop ⟨p, hp.1⟩ (good_away C hne hp) z L)

end Level

end ZInQ.Manuscript.RC.ThetaClose

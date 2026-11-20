import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Admissible
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Global
import ZInQKernel.Contrib.OneProof.RC.Adelic.RightAction

/-! Adelic representatives of supported embeddings. The affine generator is
carried along the left rational translate, independently of any Picard fiber. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Normalizers

open Adelic Eichler O7Actual O7Orbits ThetaJoin Visibility

variable {a b : ℚ} {R : Order a b} {n : ℚ}

/-- The square-root vector attached to the integral affine generator. -/
def root (y : B a b) : B a b := 2 * y - 1

theorem root_injective : Function.Injective (root (a := a) (b := b)) := by
  intro x y h
  have h₂ : IsUnit (2 : B a b) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ (B a b))
  exact h₂.mul_left_cancel (sub_left_inj.mp h)

theorem rationalConj_apply (u : (B a b)ˣ) (x : B a b) :
    rationalConj u x = (u : B a b) * x * ↑u⁻¹ := rfl

theorem root_conj (u : (B a b)ˣ) (x : B a b) :
    root (rationalConj u x) = rationalConj u (root x) := by
  change 2 * unitConjRing u x - 1 = unitConjRing u (2 * x - 1)
  rw [map_sub, map_mul, map_ofNat, map_one]

theorem rationalConj_comp (u v : (B a b)ˣ) (x : B a b) :
    rationalConj u (rationalConj v x) = rationalConj (u * v) x :=
  unitConjRing_mul u v x

theorem atRep_root (z : FiniteUnits R) (q : Prime) (y : B a b) :
    atRep z q (root y) = 2 * atRep z q y - 1 := by
  let f := (unitConjRing (z.val q)⁻¹).comp (toLocal q.val)
  change f (2 * y - 1) = 2 * f y - 1
  simp only [map_sub, map_mul, map_ofNat, map_one]

/-- The difference between two representatives of an embedding is a rational
conjugation and an integral change of adelic basis. -/
structure AdelicPoint (R : Order a b) (n : ℚ) where
  z : FiniteUnits R
  y : B a b
  trace_zero : (root y).re = 0
  norm_eq : Visibility.nrd (root y) = n
  integral : ∀ q : Prime, atRep z q y ∈ R.completion q.val

theorem AdelicPoint.eq_of_fields {P Q : AdelicPoint R n} (hz : P.z = Q.z) (hy : P.y = Q.y) :
    P = Q := by
  cases P
  cases Q
  cases hz
  cases hy
  rfl

def pointRel (R : Order a b) (n : ℚ) : Setoid (AdelicPoint R n) where
  r P Q := ∃ u : (B a b)ˣ, ∃ r : integralUnits R,
    Q.z = diagonal R u * P.z * r.val ∧ Q.y = rationalConj u P.y
  iseqv := by
    constructor
    · intro P
      exact ⟨1, 1, by simp, by simp [rationalConj_apply]⟩
    · rintro P Q ⟨u, r, hz, hy⟩
      refine ⟨u⁻¹, r⁻¹, ?_, ?_⟩
      · rw [hz, map_inv]
        change P.z = (diagonal R u)⁻¹ * (diagonal R u * P.z * r.val) * r.val⁻¹
        group
      · rw [hy, rationalConj_comp]
        simp [rationalConj_apply]
    · rintro P Q T ⟨u, r, hz, hy⟩ ⟨v, s, hz', hy'⟩
      exact ⟨v * u, r * s, by rw [hz', hz]; simp [mul_assoc],
        by rw [hy', hy, rationalConj_comp]⟩

abbrev AdelicOrbits (R : Order a b) (n : ℚ) := Quotient (pointRel R n)

theorem pointRel_atRep {P Q : AdelicPoint R n} (h : (pointRel R n).r P Q) (q : Prime) :
    ∃ r : localUnits R q, atRep Q.z q Q.y =
      (↑r.val⁻¹ : Bp q.val a b) * atRep P.z q P.y * ↑r.val := by
  obtain ⟨u, r, hz, hy⟩ := h
  exact ⟨⟨r.val.val q, r.prop q⟩, by rw [hz, hy, atRep_right, atRep_left]⟩

/-- The only property needed of an adelic normalizer to transport the
integral affine condition. -/
def PreservesOrder (k : FiniteUnits R) : Prop :=
  ∀ q : Prime, ∀ x : Bp q.val a b,
    (↑(k.val q)⁻¹ : Bp q.val a b) * x * ↑(k.val q) ∈ R.completion q.val ↔
      x ∈ R.completion q.val

theorem preservesOrder_single (q : Prime) (v : (Bp q.val a b)ˣ)
    (hv : ∀ x : Bp q.val a b,
      (↑v⁻¹ : Bp q.val a b) * x * ↑v ∈ R.completion q.val ↔ x ∈ R.completion q.val) :
    PreservesOrder (single R q v) := by
  intro r x
  by_cases hr : r = q
  · subst r
    simpa only [single_same] using hv x
  · rw [single_away hr]
    simp

private theorem inverse_conj_mem {A : Type*} [Ring A] (S : Set A) (u : Aˣ)
    (hu : ∀ x : A, (↑u⁻¹ : A) * x * ↑u ∈ S ↔ x ∈ S) (x : A) :
    (↑((u⁻¹)⁻¹) : A) * x * ↑u⁻¹ ∈ S ↔ x ∈ S := by
  have hc : (↑u⁻¹ : A) * ((u : A) * x * ↑u⁻¹) * ↑u = x := by
    simp only [mul_assoc]
    rw [Units.inv_mul, mul_one, ← mul_assoc (↑u⁻¹ : A) (↑u : A) x, Units.inv_mul, one_mul]
  have hh := (hu ((u : A) * x * ↑u⁻¹)).symm
  rw [hc] at hh
  simpa only [inv_inv] using hh

theorem PreservesOrder.inv {k : FiniteUnits R} (hk : PreservesOrder k) :
    PreservesOrder k⁻¹ :=
  fun q x => inverse_conj_mem (R.completion q.val : Set (Bp q.val a b)) (k.val q) (hk q) x

theorem PreservesOrder.normalizes {k : FiniteUnits R} (hk : PreservesOrder k) : Normalizes k := by
  intro r
  exact forall_congr' (fun q => localUnits_conj q (k.val q) (hk q) (r.val q))

/-- Right multiplication leaves the rational embedding unchanged before
replacing the representative by the chosen one for its new class. -/
def stepPoint (k : FiniteUnits R) (hk : PreservesOrder k) (P : AdelicPoint R n) :
    AdelicPoint R n where
  z := P.z * k
  y := P.y
  trace_zero := P.trace_zero
  norm_eq := P.norm_eq
  integral q := by rw [atRep_right]; exact (hk q _).mpr (P.integral q)

theorem stepPoint_rel (k : FiniteUnits R) (hk : PreservesOrder k)
    {P Q : AdelicPoint R n} (H : (pointRel R n).r P Q) :
    (pointRel R n).r (stepPoint k hk P) (stepPoint k hk Q) := by
  obtain ⟨u, r, hz, hy⟩ := H
  refine ⟨u, ⟨k⁻¹ * r.val * k, (hk.normalizes r.val).mpr r.prop⟩, ?_, hy⟩
  change Q.z * k = diagonal R u * (P.z * k) * (k⁻¹ * r.val * k)
  rw [hz]
  group

def adelicMove (k : FiniteUnits R) (hk : PreservesOrder k) : Equiv.Perm (AdelicOrbits R n) where
  toFun := Quotient.map (stepPoint k hk) (fun _ _ => stepPoint_rel k hk)
  invFun := Quotient.map (stepPoint k⁻¹ hk.inv) (fun _ _ => stepPoint_rel k⁻¹ hk.inv)
  left_inv := by
    intro X
    induction X using Quotient.inductionOn with
    | _ P =>
      apply Quotient.sound
      exact ⟨1, 1, by change P.z = diagonal R 1 * (P.z * k * k⁻¹) * 1; simp,
        by simp [stepPoint, rationalConj_apply]⟩
  right_inv := by
    intro X
    induction X using Quotient.inductionOn with
    | _ P =>
      apply Quotient.sound
      exact ⟨1, 1, by change P.z = diagonal R 1 * (P.z * k⁻¹ * k) * 1; simp,
        by simp [stepPoint, rationalConj_apply]⟩

def adelicClass (P : AdelicPoint R n) : ClassSet R := idealsEquiv R (Quotient.mk _ P.z)

theorem stepPoint_class (k : FiniteUnits R) (hk : PreservesOrder k) (P : AdelicPoint R n) :
    adelicClass (stepPoint k hk P) = rightClassPerm k hk.normalizes (adelicClass P) := by
  rw [adelicClass, adelicClass, idealsEquiv_mk, idealsEquiv_mk, rightClassPerm_mk]
  rfl

section Actual

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D : ℤ}
variable (s : StageAt O N M hN m) (H : SupportBridge s D)

abbrev ActualPoint := AdelicPoint (ActualOrder s) (index s D)

/-- Reconstruct an actual vector from the affine generator using the proved
support bridge. -/
def supportOfPoint (z : ClassSet (ActualOrder s)) (P : ActualPoint s (D := D))
    (hz : P.z = classRepresentative z) : ActualSupport s D z :=
  ⟨root P.y, P.trace_zero, P.norm_eq, (H z _ P.trace_zero P.norm_eq).mpr
    ⟨⟨P.y, (classOrder_mem_adelic s.weights.ha s.weights.hb z P.y).mpr
      (hz ▸ P.integral)⟩, rfl⟩⟩

def pointOfSupport (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) : ActualPoint s (D := D) where
  z := classRepresentative z
  y := (H.half z x).choose.val
  trace_zero := by change (2 * _ - 1 : B (-1) (-(s.ell : ℚ))).re = 0; rw [(H.half z x).choose_spec]; exact x.prop.1
  norm_eq := by change Visibility.nrd (2 * _ - 1 : B (-1) (-(s.ell : ℚ))) = _; rw [(H.half z x).choose_spec]; exact x.prop.2.1
  integral := (classOrder_mem_adelic s.weights.ha s.weights.hb z _).mp (H.half z x).choose.prop

theorem pointOfSupport_root (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    root (pointOfSupport s H z x).y = x.val := (H.half z x).choose_spec

theorem pointOfSupport_generator (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z)
    (q : Prime) :
    atRep (pointOfSupport s H z x).z q (pointOfSupport s H z x).y =
      (localGenerator s H z x q).val := by
  rfl

theorem supportOfPoint_inverse (z : ClassSet (ActualOrder s)) (P : ActualPoint s (D := D))
    (hz : P.z = classRepresentative z) :
    pointOfSupport s H z (supportOfPoint s H z P hz) = P := by
  apply AdelicPoint.eq_of_fields hz.symm
  apply root_injective
  exact pointOfSupport_root s H z (supportOfPoint s H z P hz)

theorem chosen_pointRel_iff (z : ClassSet (ActualOrder s)) (x y : ActualSupport s D z) :
    (pointRel _ _).r (pointOfSupport s H z x) (pointOfSupport s H z y) ↔
      (@MulAction.orbitRel (s.visibility.G z) (ActualSupport s D z) _
        (ThetaStage.conjAction s.visibility z (index s D))).r x y := by
  change (∃ u : (B (-1) (-(s.ell : ℚ)))ˣ, ∃ r : integralUnits (ActualOrder s),
    classRepresentative z = diagonal _ u * classRepresentative z * r.val ∧
    (pointOfSupport s H z y).y = rationalConj u (pointOfSupport s H z x).y) ↔ _
  have hroot (u : (B (-1) (-(s.ell : ℚ)))ˣ) :
      (pointOfSupport s H z y).y = rationalConj u (pointOfSupport s H z x).y ↔
        y.val = rationalConj u x.val := by
    rw [← root_injective.eq_iff, root_conj, pointOfSupport_root, pointOfSupport_root]
  have hunit (u : (B (-1) (-(s.ell : ℚ)))ˣ) :
      (∃ r : integralUnits (ActualOrder s),
        classRepresentative z = diagonal _ u * classRepresentative z * r.val) ↔
        u ∈ s.visibility.G z := by
    rw [← fromAdelic_translate_iff, fromAdelic_classRepresentative, eq_comm]
    exact (RightIdeal.mem_G_iff_translate s.weights.ha s.weights.hb _ u).symm
  constructor
  · rintro ⟨u, r, hz, hy⟩
    let v : s.visibility.G z := ⟨u, (hunit u).mp ⟨r, hz⟩⟩
    refine ⟨v⁻¹, Subtype.ext ?_⟩
    have hh := congrArg (rationalConj u⁻¹) ((hroot u).mp hy)
    rw [rationalConj_comp, inv_mul_cancel] at hh
    change rationalConj u⁻¹ y.val = x.val
    simpa [rationalConj_apply] using hh
  · rintro ⟨u, hu⟩
    obtain ⟨r, hr⟩ := (hunit ((u : (B (-1) (-(s.ell : ℚ)))ˣ)⁻¹)).mpr u⁻¹.prop
    refine ⟨_, r, hr, (hroot _).mpr ?_⟩
    have hh := congrArg (rationalConj ((u : (B (-1) (-(s.ell : ℚ)))ˣ)⁻¹))
      (congrArg Subtype.val hu)
    change rationalConj _ (rationalConj (u : (B (-1) (-(s.ell : ℚ)))ˣ) y.val) =
      rationalConj _ x.val at hh
    rw [rationalConj_comp, inv_mul_cancel] at hh
    simpa [rationalConj_apply] using hh

def toAdelic : OrbitSet s.visibility (index s D) → AdelicOrbits (ActualOrder s) (index s D) :=
  fun P => Quotient.map (pointOfSupport s H P.1)
    (fun _ _ W => (chosen_pointRel_iff s H _ _ _).mpr W) P.2

theorem pointRel_class {P Q : ActualPoint s (D := D)} (W : (pointRel _ _).r P Q) :
    adelicClass P = adelicClass Q := by
  obtain ⟨u, r, hz, _⟩ := W
  exact congrArg (idealsEquiv _) (Quotient.sound ⟨u, r, hz⟩)

theorem pointOfSupport_class (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    adelicClass (pointOfSupport s H z x) = z := by
  change idealsEquiv _ (Quotient.mk _ (classRepresentative z)) = z
  rw [← classesEquiv_classRepresentative]
  exact (idealsEquiv _).apply_symm_apply _

/-- Actual support orbits are exactly the adelic pairs modulo change of
representatives. This equivalence involves no global torus comparison. -/
def adelicOrbitsEquiv : OrbitSet s.visibility (index s D) ≃ AdelicOrbits (ActualOrder s) (index s D) :=
  Equiv.ofBijective (toAdelic s H) ⟨by
    rintro ⟨z, x⟩ ⟨w, y⟩
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        intro h
        have W := Quotient.exact h
        change (pointRel _ _).r (pointOfSupport s H z x) (pointOfSupport s H w y) at W
        have hz := pointRel_class s W
        rw [pointOfSupport_class s H z x, pointOfSupport_class s H w y] at hz
        subst w
        exact congrArg (Sigma.mk z) (Quotient.sound ((chosen_pointRel_iff s H z x y).mp W)),
    by
      intro U
      induction U using Quotient.inductionOn with
      | _ P =>
        let z := adelicClass P
        have hz : Quotient.mk (doubleCosetRel (ActualOrder s)) P.z =
            Quotient.mk _ (classRepresentative z) := by
          rw [← classesEquiv_classRepresentative]
          exact ((idealsEquiv _).symm_apply_apply _).symm
        obtain ⟨u, r, hr⟩ := Quotient.exact hz
        let Q : ActualPoint s (D := D) :=
          ⟨classRepresentative z, rationalConj u P.y, by
            rw [root_conj, rationalConj_apply, quat_re_conj]; exact P.trace_zero, by
            rw [root_conj, rationalConj_apply, nrd_conj]; exact P.norm_eq, fun q => by
            rw [hr, atRep_right, atRep_left]
            exact (localUnit_conj_mem q ⟨r.val.val q, r.prop q⟩ _).mpr (P.integral q)⟩
        refine ⟨⟨z, Quotient.mk _ (supportOfPoint s H z Q rfl)⟩, ?_⟩
        change Quotient.mk _ (pointOfSupport s H z (supportOfPoint s H z Q rfl)) = _
        rw [supportOfPoint_inverse]
        exact (Quotient.sound (s := pointRel _ _) (show (pointRel _ _).r P Q from ⟨u, r, hr, rfl⟩)).symm⟩

def orbitMove (k : FiniteUnits (ActualOrder s)) (hk : PreservesOrder k) :
    Equiv.Perm (OrbitSet s.visibility (index s D)) :=
  (adelicOrbitsEquiv s H).trans ((adelicMove k hk).trans (adelicOrbitsEquiv s H).symm)

theorem orbitMove_rel (k : FiniteUnits (ActualOrder s)) (hk : PreservesOrder k)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (w : ClassSet (ActualOrder s))
    (y : ActualSupport s D w) (hy : orbitMove s H k hk ⟨z, Quotient.mk _ x⟩ = ⟨w, Quotient.mk _ y⟩) :
    (pointRel _ _).r (stepPoint k hk (pointOfSupport s H z x)) (pointOfSupport s H w y) := by
  apply Quotient.exact
  have hh := congrArg (adelicOrbitsEquiv s H) hy
  rw [orbitMove, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply] at hh
  exact hh

theorem orbitMove_class (k : FiniteUnits (ActualOrder s)) (hk : PreservesOrder k)
    (P : OrbitSet s.visibility (index s D)) :
    (orbitMove s H k hk P).1 = rightClassPerm k hk.normalizes P.1 := by
  obtain ⟨z, x⟩ := P
  induction x using Quotient.inductionOn with
  | _ x =>
    generalize he : orbitMove s H k hk ⟨z, Quotient.mk _ x⟩ = Q
    obtain ⟨w, y⟩ := Q
    induction y using Quotient.inductionOn with
    | _ y =>
      have hh := pointRel_class s (orbitMove_rel s H k hk z x w y he)
      rw [stepPoint_class, pointOfSupport_class s H z x, pointOfSupport_class s H w y] at hh
      exact hh.symm

end Actual

end ZInQ.Manuscript.RC.O7Normalizers

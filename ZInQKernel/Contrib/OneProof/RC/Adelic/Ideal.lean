import ZInQKernel.Contrib.OneProof.RC.Adelic.FiniteUnits

/-!
# The ideal correspondence and the adelic left order
Tex 8465–8468. The correspondence is proved by patching lattices, given here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler

variable {a b : ℚ} {R : Order a b}

/-- The lattice obtained by left multiplying the local order by a local unit of the algebra. -/
def localRight (R : Order a b) (p : Prime) (u : (Bp p.val a b)ˣ) :
    Submodule ℤ_[p.val] (Bp p.val a b) :=
  (R.completion p.val).toSubmodule.map (u.mulLeftLinearEquiv ℤ_[p.val] _).toLinearMap

theorem mem_localRight (p : Prime) (u : (Bp p.val a b)ˣ) (x : Bp p.val a b) :
    x ∈ localRight R p u ↔ (↑u⁻¹ : Bp p.val a b) * x ∈ R.completion p.val := by
  change (∃ y ∈ R.completion p.val, (u : Bp p.val a b) * y = x) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hy
  · intro hx
    exact ⟨_, hx, by simp only [← mul_assoc, Units.mul_inv, one_mul]⟩

theorem localRight_set (p : Prime) (u : (Bp p.val a b)ˣ) :
    (localRight R p u : Set _) = (fun x : Bp p.val a b => (u : Bp p.val a b) * x) ''
      (R.completion p.val : Set _) :=
  Submodule.map_coe (u.mulLeftLinearEquiv ℤ_[p.val] _).toLinearMap (R.completion p.val).toSubmodule

theorem localRight_eq_iff (p : Prime) (u v : (Bp p.val a b)ˣ) :
    localRight R p u = localRight R p v ↔ u⁻¹ * v ∈ localUnits R p := by
  have hu : (u : Bp p.val a b) ∈ localRight R p u :=
    (mem_localRight p u _).mpr (by simp)
  have hv : (v : Bp p.val a b) ∈ localRight R p v :=
    (mem_localRight p v _).mpr (by simp)
  constructor
  · intro he
    exact ⟨(mem_localRight p u _).mp (he.symm ▸ hv),
      by simpa only [mul_inv_rev, inv_inv, Units.val_mul] using (mem_localRight p v _).mp (he ▸ hu)⟩
  · intro he
    have he' : v⁻¹ * u ∈ localUnits R p := by simpa using (localUnits R p).inv_mem he
    have h (s t : (Bp p.val a b)ˣ) (hst : s⁻¹ * t ∈ localUnits R p) :
        localRight R p t ≤ localRight R p s := by
      intro x hx
      apply (mem_localRight p s _).mpr
      have ht := (mem_localRight p t _).mp hx
      have hs : (↑s⁻¹ : Bp p.val a b) * (t : Bp p.val a b) ∈ R.completion p.val := hst.1
      have hh := (R.completion p.val).mul_mem hs ht
      rwa [mul_assoc, ← mul_assoc (t : Bp p.val a b) (↑t⁻¹ : Bp p.val a b),
        Units.mul_inv, one_mul] at hh
    exact le_antisymm (h v u he') (h u v he)

theorem localRight_one (p : Prime) : localRight R p 1 = localLattice p.val R.lattice := by
  rw [← R.completion_toSubmodule]
  ext x
  rw [mem_localRight]
  simp only [inv_one, Units.val_one, one_mul]
  rfl

private theorem localRight_full (p : Prime) (u : (Bp p.val a b)ˣ) :
    (localRight R p u).IsLattice ℚ_[p.val] := by
  unfold localRight
  have h := localLattice_full p R.full
  rw [← R.completion_toSubmodule] at h
  exact isLattice_map h (u.mulLeftLinearEquiv ℚ_[p.val] _)

private theorem adelic_patch (z : FiniteUnits R) :
    let A := fun p => localRight R p (z.val p)
    FullLattice (intersection A) ∧ ∀ p, localLattice p.val (intersection A) = A p :=
  patch R.full _ (fun p => localRight_full p _) (z.prop.subset fun p hp hp' =>
    hp ((localRight_eq_iff p 1 (z.val p)).mpr (by simpa using hp') ▸ localRight_one p))

/-- The rational intersection of the local principal right ideals z_p R_p. -/
def fromAdelic (z : FiniteUnits R) : LPIdeal R := by
  let I : RightIdeal R := {
    lattice := intersection (fun p => localRight R p (z.val p))
    full := (adelic_patch z).1
    mul_mem := by
      intro x r hx hr p
      rw [map_mul, mem_localRight, ← mul_assoc]
      exact (R.completion p.val).mul_mem ((mem_localRight p _ _).mp (hx p))
        (Algebra.subset_adjoin (Set.mem_image_of_mem _ hr)) }
  refine ⟨I, fun p hp => ?_⟩
  let q : Prime := ⟨p, hp.out⟩
  refine ⟨z.val q, ?_⟩
  change (localLattice q.val (intersection (fun r => localRight R r (z.val r))) : Set (Bp q.val a b)) =
    (fun x : Bp q.val a b => (z.val q : Bp q.val a b) * x) '' (R.completion q.val : Set _)
  rw [(adelic_patch z).2 q, localRight_set]

theorem mem_fromAdelic (z : FiniteUnits R) (x : B a b) :
    x ∈ (fromAdelic z).val.lattice ↔ ∀ p : Prime, toLocal p.val x ∈ localRight R p (z.val p) :=
  Iff.rfl

theorem fromAdelic_completion (z : FiniteUnits R) (p : Prime) :
    localLattice p.val (fromAdelic z).val.lattice = localRight R p (z.val p) :=
  (adelic_patch z).2 p

theorem exists_adelic_representative (I : LPIdeal R) :
    ∃ z : FiniteUnits R, fromAdelic z = I := by
  classical
  have hh (p : Prime) : ∃ u : (Bp p.val a b)ˣ,
      localLattice p.val I.val.lattice = localRight R p u := by
    obtain ⟨u, hu⟩ := I.prop p.val
    exact ⟨u, SetLike.coe_injective (hu.trans (localRight_set p u).symm)⟩
  choose u hu using hh
  let z0 (p : Prime) := if localLattice p.val I.val.lattice = localLattice p.val R.lattice
    then 1 else u p
  let z : FiniteUnits R := ⟨z0, (finite_localLattice_ne I.val.full R.full).subset (by
    intro p hp he
    exact hp (by simp [z0, he]))⟩
  have hz (p : Prime) : localLattice p.val I.val.lattice = localRight R p (z.val p) := by
    change _ = localRight R p (z0 p)
    by_cases hp : localLattice p.val I.val.lattice = localLattice p.val R.lattice
    · rw [show z0 p = 1 from ite_eq_left hp, localRight_one, hp]
    · rw [show z0 p = u p from ite_eq_right hp, ← hu]
  refine ⟨z, Subtype.ext (RightIdeal.ext ?_)⟩
  ext x
  change (∀ p, toLocal p.val x ∈ localRight R p (z.val p)) ↔ x ∈ I.val.lattice
  simp_rw [← hz, ← mem_iff_all_local I.val.full x]

theorem fromAdelic_mul_diagonal (z : FiniteUnits R) (u : (B a b)ˣ) :
    (fromAdelic (diagonal R u * z)).val = (fromAdelic z).val.translate u := by
  apply RightIdeal.ext
  ext x
  rw [RightIdeal.mem_translate]
  change (∀ p, toLocal p.val x ∈ localRight R p ((diagonal R u * z).val p)) ↔
    (∀ p, toLocal p.val ((↑u⁻¹ : B a b) * x) ∈ localRight R p (z.val p))
  apply forall_congr'
  intro p
  rw [mem_localRight, mem_localRight, map_mul]
  change (↑((Units.map (toLocal p.val).toMonoidHom u * z.val p)⁻¹) : Bp p.val a b) *
    toLocal p.val x ∈ R.completion p.val ↔
    (↑(z.val p)⁻¹ : Bp p.val a b) * (toLocal p.val (↑u⁻¹ : B a b) * toLocal p.val x) ∈ _
  rw [mul_inv_rev, Units.val_mul, mul_assoc]
  rfl

/-- Exact fixed-u double coset criterion for equality of the corresponding ideals. -/
theorem fromAdelic_translate_iff (z w : FiniteUnits R) (u : (B a b)ˣ) :
    (fromAdelic w).val = (fromAdelic z).val.translate u ↔
      ∃ r : integralUnits R, w = diagonal R u * z * r.val := by
  rw [← fromAdelic_mul_diagonal]
  let v := diagonal R u * z
  change (fromAdelic w).val = (fromAdelic v).val ↔ ∃ r : integralUnits R, w = v * r.val
  constructor
  · intro he
    have hunit : v⁻¹ * w ∈ integralUnits R := by
      intro p
      apply (localRight_eq_iff p (v.val p) (w.val p)).mp
      rw [← fromAdelic_completion v p, ← fromAdelic_completion w p, he]
    exact ⟨⟨_, hunit⟩, by simp⟩
  · rintro ⟨r, rfl⟩
    apply RightIdeal.ext
    ext x
    change (∀ p, toLocal p.val x ∈ localRight R p (v.val p * r.val.val p)) ↔
      (∀ p, toLocal p.val x ∈ localRight R p (v.val p))
    apply forall_congr'
    intro p
    have he := (localRight_eq_iff p (v.val p) (v.val p * r.val.val p)).mpr
      (by simpa [← mul_assoc] using r.prop p)
    rw [he]

/-- The double coset space maps bijectively to the existing ideal class set. -/
def idealsEquiv (R : Order a b) : DoubleCosets R ≃ ClassSet R := by
  let f : DoubleCosets R → ClassSet R := Quotient.map (fromAdelic (R := R)) (by
    rintro z w ⟨u, r, he⟩
    exact ⟨u, ((fromAdelic_translate_iff z w u).mpr ⟨r, he⟩).symm⟩)
  apply Equiv.ofBijective f
  constructor
  · intro z w
    induction z using Quotient.inductionOn with
    | _ z =>
      induction w using Quotient.inductionOn with
      | _ w =>
        intro h
        obtain ⟨u, hu⟩ := Quotient.exact (show Quotient.mk _ (fromAdelic z) =
          Quotient.mk _ (fromAdelic w) from h)
        obtain ⟨r, hr⟩ := (fromAdelic_translate_iff z w u).mp hu.symm
        exact Quotient.sound ⟨u, r, hr⟩
  · intro I
    induction I using Quotient.inductionOn with
    | _ I =>
      obtain ⟨z, hz⟩ := exists_adelic_representative I
      exact ⟨Quotient.mk _ z, congrArg (Quotient.mk _) hz⟩

/-- The ideal class set identified with the adelic double coset space. -/
def classesEquiv (R : Order a b) : ClassSet R ≃ DoubleCosets R := (idealsEquiv R).symm

theorem idealsEquiv_mk (z : FiniteUnits R) :
    idealsEquiv R (Quotient.mk _ z) = Quotient.mk _ (fromAdelic z) := rfl

/-- The left order is the rational intersection of the conjugate local orders. -/
theorem mem_leftRing_iff (z : FiniteUnits R) (x : B a b) :
    x ∈ (fromAdelic z).val.leftRing ↔ ∀ p : Prime,
      (↑(z.val p)⁻¹ : Bp p.val a b) * toLocal p.val x * (z.val p : Bp p.val a b) ∈
        R.completion p.val := by
  change (∀ y ∈ (fromAdelic z).val.lattice, x * y ∈ (fromAdelic z).val.lattice) ↔ _
  constructor
  · intro hx p
    let u := z.val p
    have hU : (u : Bp p.val a b) ∈ localLattice p.val (fromAdelic z).val.lattice := by
      rw [fromAdelic_completion]
      exact (mem_localRight p u _).mpr (by simp)
    have hm (y : Bp p.val a b) (hy : y ∈ localLattice p.val (fromAdelic z).val.lattice) :
        toLocal p.val x * y ∈ localLattice p.val (fromAdelic z).val.lattice := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, hv, rfl⟩ := hy
        rw [← map_mul]
        exact Submodule.subset_span (Set.mem_image_of_mem _ (hx v hv))
      | zero => simp
      | add y v _ _ hy hv => simpa only [mul_add] using Submodule.add_mem _ hy hv
      | smul t y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hy
    have hu := hm _ hU
    rw [fromAdelic_completion, mem_localRight, ← mul_assoc] at hu
    exact hu
  · intro hx y hy p
    rw [map_mul, mem_localRight]
    have hy' := (mem_localRight p (z.val p) _).mp (hy p)
    let u := z.val p
    have hm := (R.completion p.val).mul_mem (hx p) hy'
    rwa [mul_assoc _ (u : Bp p.val a b),
      ← mul_assoc (u : Bp p.val a b) (↑u⁻¹ : Bp p.val a b),
      Units.mul_inv, one_mul, mul_assoc] at hm

/-- An adelic representative matching the chosen ideal representative of a class. -/
def classRepresentative (i : ClassSet R) : FiniteUnits R :=
  (exists_adelic_representative (representative i)).choose

theorem fromAdelic_classRepresentative (i : ClassSet R) :
    fromAdelic (classRepresentative i) = representative i :=
  (exists_adelic_representative (representative i)).choose_spec

theorem classesEquiv_classRepresentative (i : ClassSet R) :
    classesEquiv R i = Quotient.mk _ (classRepresentative i) := by
  apply (idealsEquiv R).injective
  change (idealsEquiv R) ((idealsEquiv R).symm i) = _
  rw [Equiv.apply_symm_apply, idealsEquiv_mk, fromAdelic_classRepresentative]
  exact (Quotient.out_eq i).symm

/-- The stabilizer group used by RC is the unit group of the adelic left order,
with the adelic representative chosen compatibly with the ideal representative. -/
def classGEquiv (ha : a < 0) (hb : b < 0) (i : ClassSet R) :
    classG ha hb i ≃* (fromAdelic (classRepresentative i)).val.leftRingˣ := by
  rw [fromAdelic_classRepresentative]
  let L := (representative i).val.leftOrder ha hb
  exact (MulEquiv.ofBijective L.unitsHom.rangeRestrict
    ⟨fun _ _ h => L.unitsHom_injective (congrArg Subtype.val h),
      fun ⟨_, u, hu⟩ => ⟨u, Subtype.ext hu⟩⟩).symm


end ZInQ.Manuscript.RC.Adelic

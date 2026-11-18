import ZInQKernel.Contrib.OneProof.RC.Eichler.ClassSet

/-!
# Finiteness of the definite ideal class set

On-the-spot (c), for tex 8466. Normalize by a shortest vector. The normalized ideal contains
the order and its nonzero vectors have norm at least one. A fine grid in an order fundamental
parallelepiped bounds the index of the order in every such ideal. Thus a fixed factorial clears
all normalized ideals into the order, giving bounded-index integral representatives as well.
-/

open Module

namespace ZInQ.Manuscript.RC.Eichler

variable {a b : ℚ}

private noncomputable def round (e : Basis (Fin 4) ℚ (B a b)) (x : B a b) : B a b :=
  e.equivFun.symm fun i => (⌊e.repr x i⌋ : ℤ)

private theorem repr_round (e : Basis (Fin 4) ℚ (B a b)) (x : B a b) (i : Fin 4) :
    e.repr (round e x) i = (⌊e.repr x i⌋ : ℤ) := by
  change e.equivFun (e.equivFun.symm (fun i => (⌊e.repr x i⌋ : ℤ))) i = _
  rw [e.equivFun.apply_symm_apply]

private theorem round_mem (e : Basis (Fin 4) ℚ (B a b)) (x : B a b) :
    round e x ∈ Submodule.span ℤ (Set.range e) := by
  exact (e.mem_span_iff_repr_mem ℤ _).mpr fun i => ⟨⌊e.repr x i⌋, (repr_round e x i).symm⟩

private theorem frac_coord (e : Basis (Fin 4) ℚ (B a b)) (x : B a b) (i : Fin 4) :
    e.repr (x - round e x) i ∈ Set.Ico (0 : ℚ) 1 := by
  rw [map_sub, Finsupp.sub_apply, repr_round]
  exact ⟨Int.fract_nonneg (e.repr x i), Int.fract_lt_one (e.repr x i)⟩

private theorem nrd_small (e : Basis (Fin 4) ℚ (B a b)) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : B a b, (∀ i, |e.repr x i| < 1 / (m : ℚ)) →
      Visibility.nrd x < 1 := by
  let Q (t : Fin 4 → ℚ) : ℚ :=
    ∑ j, weight a b j * (∑ i, t i * coord (e i) j) ^ 2
  have hQ (t) : Q t = Visibility.nrd (e.equivFun.symm t) := by
    rw [nrd_sum, Basis.equivFun_symm_apply]
    simp only [Q, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  have hc : Continuous Q := by
    unfold Q
    fun_prop
  have hc₀ : ContinuousAt Q 0 := hc.continuousAt
  have hcont := (Metric.continuousAt_iff.mp hc₀) 1 zero_lt_one
  obtain ⟨δ, hd, hδ⟩ := hcont
  obtain ⟨n, hn⟩ := exists_nat_gt δ⁻¹
  let m := n + 1
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.succ_pos n
  have hmδ : (1 : ℝ) / m < δ := (one_div_lt hm hd).mpr
    (by simpa only [one_div] using hn.trans (by exact_mod_cast Nat.lt_succ_self n))
  refine ⟨m, Nat.succ_pos n, fun x hx => ?_⟩
  have hd' : dist (e.equivFun x) (0 : Fin 4 → ℚ) < δ := by
    rw [dist_pi_lt_iff hd]
    intro i
    have hi : ((|e.repr x i| : ℚ) : ℝ) < (1 : ℝ) / m := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
        (Rat.cast_lt (K := ℝ)).mpr (hx i)
    rw [Rat.dist_eq]
    change |((e.repr x i : ℚ) : ℝ) - ((0 : ℚ) : ℝ)| < δ
    rw [Rat.cast_zero, sub_zero, ← Rat.cast_abs]
    exact hi.trans hmδ
  have h := hδ hd'
  rw [hQ, hQ, LinearEquiv.symm_apply_apply, map_zero] at h
  have hnrd : Visibility.nrd (0 : B a b) = 0 := by simp [Visibility.nrd_apply]
  rw [hnrd, Rat.dist_eq, Rat.cast_zero, sub_zero] at h
  have h' : ((|Visibility.nrd x| : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by
    simpa only [Rat.cast_abs, Rat.cast_one] using h
  exact (le_abs_self _).trans_lt ((Rat.cast_lt (K := ℝ)).mp h')

private noncomputable def cell (m : ℕ) (hm : 0 < m)
    (e : Basis (Fin 4) ℚ (B a b)) (x : B a b)
    (h : ∀ i, e.repr x i ∈ Set.Ico (0 : ℚ) 1) : Fin 4 → Fin m := fun i => by
  have hm' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  refine ⟨⌊(m : ℚ) * e.repr x i⌋₊, (Nat.floor_lt (mul_nonneg hm'.le (h i).1)).mpr ?_⟩
  simpa only [mul_one] using mul_lt_mul_of_pos_left (h i).2 hm'

private theorem cell_diff {m : ℕ} (hm : 0 < m) (e : Basis (Fin 4) ℚ (B a b))
    {x y : B a b} {hx : ∀ i, e.repr x i ∈ Set.Ico (0 : ℚ) 1}
    {hy : ∀ i, e.repr y i ∈ Set.Ico (0 : ℚ) 1}
    (h : cell m hm e x hx = cell m hm e y hy) (i : Fin 4) :
    |e.repr (x - y) i| < 1 / (m : ℚ) := by
  have hp : (0 : ℚ) < m := by exact_mod_cast hm
  let u := (m : ℚ) * e.repr x i
  let v := (m : ℚ) * e.repr y i
  have h' : ⌊u⌋₊ = ⌊v⌋₊ := congrArg (fun f : Fin 4 → Fin m => (f i).val) h
  have hu := Nat.floor_le (show 0 ≤ u from mul_nonneg hp.le (hx i).1)
  have hv := Nat.floor_le (show 0 ≤ v from mul_nonneg hp.le (hy i).1)
  have hu' := Nat.lt_floor_add_one u
  have hv' := Nat.lt_floor_add_one v
  rw [h'] at hu hu'
  rw [map_sub, Finsupp.sub_apply, abs_lt]
  constructor
  · rw [← neg_div, div_lt_iff₀ hp]
    change -1 < (e.repr x i - e.repr y i) * (m : ℚ)
    calc -1 < u - v := by linarith
         _ = _ := by dsimp [u, v]; ring
  · rw [lt_div_iff₀ hp]
    calc (e.repr x i - e.repr y i) * (m : ℚ) = u - v := by dsimp [u, v]; ring
         _ < 1 := by linarith

/-- A uniform denominator for all normalized over-lattices of an order. -/
theorem exists_normalized_denominator (R : Order a b) :
    ∃ d : ℕ, 0 < d ∧ ∀ J : Submodule ℤ (B a b), R.lattice ≤ J →
      (∀ x ∈ J, x ≠ 0 → 1 ≤ Visibility.nrd x) → ∀ x ∈ J, d • x ∈ R.lattice := by
  classical
  let e := R.full.ratBasis (QuaternionAlgebra.basisOneIJK a 0 b)
  have he : Submodule.span ℤ (Set.range e) = R.lattice := R.full.span_ratBasis _
  obtain ⟨m, hm, hsmall⟩ := nrd_small e
  let d := Fintype.card (Fin 4 → Fin m)
  refine ⟨d.factorial, Nat.factorial_pos _, fun J hRJ hJ x hx => ?_⟩
  let f := R.lattice.mkQ
  let T := J.map f
  have hrep (q : T) : ∃ y ∈ J, f y = q.val ∧ ∀ i, e.repr y i ∈ Set.Ico (0 : ℚ) 1 := by
    obtain ⟨v, hv, hq⟩ := q.prop
    have hr : round e v ∈ R.lattice := he ▸ round_mem e v
    exact ⟨v - round e v, J.sub_mem hv (hRJ hr),
      by have hz : f (round e v) = 0 := (Submodule.Quotient.mk_eq_zero R.lattice).mpr hr
         rw [map_sub, hz, sub_zero, hq], frac_coord e v⟩
  let y (q : T) := (hrep q).choose
  have hy (q : T) := (hrep q).choose_spec
  let g : T → Fin 4 → Fin m := fun q => cell m hm e (y q) (hy q).2.2
  have hg : Function.Injective g := by
    intro s t hst
    apply Subtype.ext
    have hzero : y s - y t = 0 := by
      by_contra hn
      exact (not_lt_of_ge (hJ _ (J.sub_mem (hy s).1 (hy t).1) hn))
        (hsmall _ (cell_diff hm e hst))
    have h' := congrArg f (sub_eq_zero.mp hzero)
    exact (hy s).2.1.symm.trans (h'.trans (hy t).2.1)
  let := Fintype.ofInjective g hg
  have hd : Fintype.card T ∣ d.factorial :=
    Nat.dvd_factorial Fintype.card_pos (Fintype.card_le_of_injective g hg)
  obtain ⟨k, hk⟩ := hd
  let x' : T := ⟨f x, Submodule.mem_map_of_mem hx⟩
  have hkill : d.factorial • x' = 0 := by
    rw [hk, Nat.mul_comm, mul_nsmul, card_nsmul_eq_zero]
  apply (Submodule.Quotient.mk_eq_zero R.lattice).mp
  change f (d.factorial • x) = 0
  rw [map_nsmul]
  exact congrArg (fun v : T => v.val) hkill

/-- Finite lattice interval: there are finitely many over-lattices between a full lattice
and a fixed rational dilate of it. -/
theorem finite_overlattices (L : Submodule ℤ (B a b)) (hL : FullLattice L) (d : ℕ) (hd : 0 < d) :
    Finite {J : Submodule ℤ (B a b) // L ≤ J ∧ ∀ x ∈ J, d • x ∈ L} := by
  classical
  let e := hL.ratBasis (QuaternionAlgebra.basisOneIJK a 0 b)
  have he : Submodule.span ℤ (Set.range e) = L := hL.span_ratBasis _
  let S := {x : B a b | d • x ∈ L ∧ ∀ i, e.repr x i ∈ Set.Ico (0 : ℚ) 1}
  have hS : Finite S := by
    have hInt (x : S) (i : Fin 4) :
        (⌊(d : ℚ) * e.repr x.val i⌋ : ℚ) = (d : ℚ) * e.repr x.val i := by
      have hx := x.prop.1
      rw [← he] at hx
      obtain ⟨z, hz⟩ := (e.mem_span_iff_repr_mem ℤ _).mp hx i
      change (z : ℚ) = e.repr (d • x.val) i at hz
      have hz' : (z : ℚ) = (d : ℚ) * e.repr x.val i := by
        simpa only [← Nat.cast_smul_eq_nsmul ℚ, map_smul, Finsupp.smul_apply, smul_eq_mul] using hz
      simp [← hz']
    let f (x : S) : Fin 4 → Fin d := cell d hd e x.val x.prop.2
    apply Finite.of_injective f
    intro x y hxy
    apply Subtype.ext
    apply e.ext_elem
    intro i
    have h := congrArg (fun g : Fin 4 → Fin d => ((g i).val : ℤ)) hxy
    have hd' : (0 : ℚ) ≤ d := Nat.cast_nonneg d
    have h' : (⌊(d : ℚ) * e.repr x.val i⌋ : ℤ) = ⌊(d : ℚ) * e.repr y.val i⌋ := by
      change (⌊(d : ℚ) * e.repr x.val i⌋₊ : ℤ) = (⌊(d : ℚ) * e.repr y.val i⌋₊ : ℤ) at h
      rwa [Int.natCast_floor_eq_floor (mul_nonneg hd' (x.prop.2 i).1),
        Int.natCast_floor_eq_floor (mul_nonneg hd' (y.prop.2 i).1)] at h
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hd.ne' : (d : ℚ) ≠ 0)
    rw [← hInt x i, ← hInt y i, h']
  let := hS
  let f : {J : Submodule ℤ (B a b) // L ≤ J ∧ ∀ x ∈ J, d • x ∈ L} → Set S :=
    fun J => {x | x.val ∈ J.val}
  apply Finite.of_injective f
  intro J K hJK
  apply Subtype.ext
  apply le_antisymm
  · intro x hx
    have hr : round e x ∈ L := he ▸ round_mem e x
    have hy : x - round e x ∈ J.val := J.val.sub_mem hx (J.prop.1 hr)
    let y : S := ⟨_, J.prop.2 _ hy, frac_coord e x⟩
    have hh : y ∈ f J := hy
    rw [hJK] at hh
    have hh' : x - round e x ∈ K.val := hh
    simpa only [sub_add_cancel] using K.val.add_mem hh' (K.prop.1 hr)
  · intro x hx
    have hr : round e x ∈ L := he ▸ round_mem e x
    have hy : x - round e x ∈ K.val := K.val.sub_mem hx (K.prop.1 hr)
    let y : S := ⟨_, K.prop.2 _ hy, frac_coord e x⟩
    have hh : y ∈ f K := hy
    rw [← hJK] at hh
    have hh' : x - round e x ∈ J.val := hh
    simpa only [sub_add_cancel] using J.val.add_mem hh' (J.prop.1 hr)

/-- There are finitely many normalized over-lattices of an order. -/
theorem finite_normalized (R : Order a b) :
    Finite {J : Submodule ℤ (B a b) // R.lattice ≤ J ∧
      ∀ x ∈ J, x ≠ 0 → 1 ≤ Visibility.nrd x} := by
  obtain ⟨d, hd, hden⟩ := exists_normalized_denominator R
  let := finite_overlattices R.lattice R.full d hd
  exact Finite.of_injective
    (fun J => (⟨J.val, J.prop.1, hden J.val J.prop.1 J.prop.2⟩ :
      {K : Submodule ℤ (B a b) // R.lattice ≤ K ∧ ∀ x ∈ K, d • x ∈ R.lattice}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun K : {K : Submodule ℤ (B a b) // R.lattice ≤ K ∧ ∀ x ∈ K, d • x ∈ R.lattice} =>
        K.val) h))

/-- The locally principal right ideal class set of a definite order is finite. -/
theorem finite_classSet (R : Order a b) (ha : a < 0) (hb : b < 0) : Finite (ClassSet R) := by
  classical
  let T := {I : LPIdeal R // R.lattice ≤ I.val.lattice ∧
    ∀ x ∈ I.val.lattice, x ≠ 0 → 1 ≤ Visibility.nrd x}
  let S := {J : Submodule ℤ (B a b) // R.lattice ≤ J ∧
    ∀ x ∈ J, x ≠ 0 → 1 ≤ Visibility.nrd x}
  let : Finite S := finite_normalized R
  let f (I : T) : S := ⟨I.val.val.lattice, I.prop⟩
  let : Finite T := Finite.of_injective f fun I J h =>
    Subtype.ext (Subtype.ext (RightIdeal.ext (congrArg Subtype.val h)))
  let g (I : T) : ClassSet R := Quotient.mk _ I.val
  apply Finite.of_surjective g
  intro z
  let I := representative z
  obtain ⟨u, hu, hmin⟩ := I.val.exists_normalized ha hb
  let J : LPIdeal R := ⟨I.val.translate u, I.val.locallyPrincipal_translate I.prop u⟩
  refine ⟨⟨J, hu, hmin⟩, ?_⟩
  exact (Quotient.sound (s := idealRel R) (show idealRel R |>.r I J from ⟨u, rfl⟩)).symm.trans
    (Quotient.out_eq z)

/-- The class set instance in the shape of both theta stage fields. -/
@[instance_reducible] noncomputable def classFintype (R : Order a b) (ha : a < 0) (hb : b < 0) :
    Fintype (ClassSet R) :=
  letI := finite_classSet R ha hb
  Fintype.ofFinite _

end ZInQ.Manuscript.RC.Eichler

/-! Axiom audit -/

#print axioms ZInQ.Manuscript.RC.Eichler.repr_round
#print axioms ZInQ.Manuscript.RC.Eichler.round_mem
#print axioms ZInQ.Manuscript.RC.Eichler.frac_coord
#print axioms ZInQ.Manuscript.RC.Eichler.nrd_small
#print axioms ZInQ.Manuscript.RC.Eichler.cell_diff
#print axioms ZInQ.Manuscript.RC.Eichler.exists_normalized_denominator
#print axioms ZInQ.Manuscript.RC.Eichler.finite_overlattices
#print axioms ZInQ.Manuscript.RC.Eichler.finite_normalized
#print axioms ZInQ.Manuscript.RC.Eichler.finite_classSet
#print axioms ZInQ.Manuscript.RC.Eichler.classFintype

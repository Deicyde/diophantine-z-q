import ZInQKernel.Contrib.OneProof.RC.Adelic.RightAction
import ZInQKernel.Contrib.OneProof.RC.Adelic.HeckeMatrix
import ZInQKernel.Contrib.OneProof.RC.LineIndex.Neighbours

/-!
# Good-prime adelic Hecke neighbours
Tex 8480–8487, 9040–9042. The comparison is given here and uses the
same lattice kernels as the ideal line indexing.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler

variable {a b : ℚ} {R : Order a b} {ell N : ℕ}

section Local

variable (p : Prime) (S : LineIndex.Split R p.val)

/-- A matrix basis in the good-prime model, viewed as a local quaternion unit. -/
def heckeBasis (L : Option (ZMod p.val)) : (Bp p.val a b)ˣ :=
  Units.map S.alg.symm.toMonoidHom (LineIndex.basisMatrix_isUnit L).unit

theorem heckeBasis_val (L : Option (ZMod p.val)) :
    (heckeBasis p S L : Bp p.val a b) = S.embed (LineIndex.basisMatrix p.val L) := by
  change S.alg.symm ↑(LineIndex.basisMatrix_isUnit L).unit = _
  rw [IsUnit.unit_spec]
  rfl

private theorem localUnits_split :
    localUnits R p = (Units.map S.embed.toMonoidHom).range := by
  rw [localUnits_eq_range]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Units.map S.orderEquiv.symm.toMonoidHom u, Units.ext ?_⟩
    change S.embed (S.orderEquiv.symm u.val) = u.val.val
    exact congrArg Subtype.val (S.orderEquiv.apply_symm_apply u.val)
  · rintro ⟨u, rfl⟩
    exact ⟨Units.map S.orderEquiv.toMonoidHom u, Units.ext rfl⟩

/-- The good-prime Hecke double coset in the local unit group of the algebra. -/
def InHeckeDoubleCoset (u : (Bp p.val a b)ˣ) : Prop :=
  ∃ v w : localUnits R p, u = v.val * heckeBasis p S none * w.val

/-- Index the right cosets of the double coset by the same choices as the ideal neighbours. -/
theorem heckeLocal_cosets (u : (Bp p.val a b)ˣ) :
    InHeckeDoubleCoset p S u ↔
      ∃! L : Option (ZMod p.val), ∃ w : localUnits R p, u = heckeBasis p S L * w.val := by
  let f := Units.map S.embed.toMonoidHom
  have hF : ∀ v, f v ∈ localUnits R p := fun v => (localUnits_split p S).symm ▸ ⟨v, rfl⟩
  have hTo {L : Option (ZMod p.val)} {v : (M2 ℤ_[p.val])ˣ} {A : M2 ℤ_[p.val]}
      (hA : A = LineIndex.basisMatrix p.val L * (v : M2 ℤ_[p.val]))
      (hu : (u : Bp p.val a b) = S.embed A) :
      u = heckeBasis p S L * f v := by
    apply Units.ext
    rw [hu, Units.val_mul, heckeBasis_val, hA, map_mul]
    rfl
  have hFrom {L : Option (ZMod p.val)} {v : (M2 ℤ_[p.val])ˣ} {A : M2 ℤ_[p.val]}
      (hv : u = heckeBasis p S L * f v) (hA : (u : Bp p.val a b) = S.embed A) :
      A = LineIndex.basisMatrix p.val L * (v : M2 ℤ_[p.val]) := by
    apply S.embed_injective
    rw [← hA, map_mul, ← heckeBasis_val]
    exact congrArg Units.val hv
  constructor
  · rintro ⟨v, w, he⟩
    obtain ⟨V, hV⟩ := (localUnits_split p S ▸ v.prop : v.val ∈ f.range)
    obtain ⟨W, hW⟩ := (localUnits_split p S ▸ w.prop : w.val ∈ f.range)
    let A := (V : M2 ℤ_[p.val]) * LineIndex.basisMatrix p.val none * (W : M2 ℤ_[p.val])
    have hA : (u : Bp p.val a b) = S.embed A := by
      rw [he, ← hV, ← hW, Units.val_mul, Units.val_mul, heckeBasis_val]
      simp only [A, map_mul]
      rfl
    obtain ⟨L, ⟨M, hM⟩, huniq⟩ := (hecke_matrix_cosets A).mp ⟨V, W, rfl⟩
    refine ⟨L, ⟨⟨f M, hF M⟩, hTo hM hA⟩, ?_⟩
    rintro L' ⟨w', h'⟩
    obtain ⟨W', hW'⟩ := (localUnits_split p S ▸ w'.prop : w'.val ∈ f.range)
    exact huniq _ ⟨W', hFrom (hW'.symm ▸ h') hA⟩
  · rintro ⟨L, ⟨w, he⟩, -⟩
    obtain ⟨v, v', h⟩ := basis_in_hecke_double L
    have h' : heckeBasis p S L = f v * heckeBasis p S none * f v' := by
      apply Units.ext
      simp only [Units.val_mul, heckeBasis_val, h, map_mul]
      rfl
    exact ⟨⟨f v, hF v⟩, ⟨_, (localUnits R p).mul_mem (hF v') w.prop⟩,
      by rw [he, h', mul_assoc]⟩

private theorem heckeBasis_mem_double (L : Option (ZMod p.val)) :
    InHeckeDoubleCoset p S (heckeBasis p S L) := by
  let f := Units.map S.embed.toMonoidHom
  have hF : ∀ v, f v ∈ localUnits R p := fun v => (localUnits_split p S).symm ▸ ⟨v, rfl⟩
  obtain ⟨u, v, h⟩ := basis_in_hecke_double L
  refine ⟨⟨f u, hF u⟩, ⟨f v, hF v⟩, Units.ext ?_⟩
  simp only [Units.val_mul, heckeBasis_val, h, map_mul]
  rfl

/-- Apply the right cosets to an adelic lift, retaining all multiplicities. -/
def heckeAtRep (z : FiniteUnits R) : Multiset (DoubleCosets R) :=
  (Finset.univ : Finset (Option (ZMod p.val))).val.map
    (fun L => Quotient.mk _ (z * single R p (heckeBasis p S L)))

set_option maxHeartbeats 1200000 in
/-- Left multiplication by an integral unit permutes the right cosets in the Hecke
double coset. It therefore leaves the resulting multiset unchanged when the lift changes. -/
theorem heckeAtRep_eq_of_rel {z w : FiniteUnits R} (hzw : (doubleCosetRel R).r z w) :
    heckeAtRep p S z = heckeAtRep p S w := by
  classical
  obtain ⟨u, r, rfl⟩ := hzw
  let v : localUnits R p := ⟨r.val.val p, r.prop p⟩
  let B := heckeBasis p S
  have hex (L : Option (ZMod p.val)) :
      ∃ T : Option (ZMod p.val), ∃ a : localUnits R p, v.val * B L = B T * a.val := by
    have hm : InHeckeDoubleCoset p S (v.val * B L) := by
      obtain ⟨c, d, he⟩ := heckeBasis_mem_double p S L
      refine ⟨v * c, d, ?_⟩
      change v.val * heckeBasis p S L = (v.val * c.val) * heckeBasis p S none * d.val
      rw [he]
      simp only [mul_assoc]
    exact ((heckeLocal_cosets p S _).mp hm).exists
  choose t a ht using hex
  have htinj : Function.Injective t := by
    intro L M he
    obtain ⟨T, _, huniq⟩ := (heckeLocal_cosets p S (B L)).mp (heckeBasis_mem_double p S L)
    have hL := huniq L ⟨1, by simp [B]⟩
    have hm : v.val * B L = (v.val * B M) * ((a M)⁻¹ * a L : localUnits R p).val := by
      rw [ht L, ht M, he]
      change _ = _ * ((a M).val⁻¹ * (a L).val)
      group
    have hM := huniq M ⟨(a M)⁻¹ * a L, mul_left_cancel (by simpa only [mul_assoc] using hm)⟩
    exact hL.trans hM.symm
  let σ : Equiv.Perm (Option (ZMod p.val)) :=
    Equiv.ofBijective t ⟨htinj, Finite.surjective_of_injective htinj⟩
  let F (L : Option (ZMod p.val)) := Quotient.mk (doubleCosetRel R) (z * single R p (B L))
  let G (L : Option (ZMod p.val)) :=
    Quotient.mk (doubleCosetRel R) ((diagonal R u * z * r.val) * single R p (B L))
  have hFG (L : Option (ZMod p.val)) : F (σ L) = G L := by
    let k := single R p (B (t L))
    let l := single R p (B L)
    let v' := k⁻¹ * (r.val * l)
    have hv' : v' ∈ integralUnits R := by
      intro q
      change (k.val q)⁻¹ * (r.val.val q * l.val q) ∈ localUnits R q
      by_cases hq : q = p
      · subst q
        change ((single R p (B (t L))).val p)⁻¹ *
          (v.val * (single R p (B L)).val p) ∈ _
        rw [single_same, single_same, ht L, inv_mul_cancel_left]
        exact (a L).prop
      · change ((single R p (B (t L))).val q)⁻¹ *
          (r.val.val q * (single R p (B L)).val q) ∈ _
        rw [single_away hq, single_away hq, mul_one, inv_one, one_mul]
        exact r.prop q
    apply Quotient.sound
    refine ⟨u, ⟨v', hv'⟩, ?_⟩
    change (diagonal R u * z * r.val) * l = diagonal R u * (z * k) * v'
    dsimp only [v']
    group
  change Finset.univ.val.map F = Finset.univ.val.map G
  calc
    _ = (Finset.univ.val.map σ).map F := by rw [Multiset.map_univ_val_equiv]
    _ = Finset.univ.val.map G := by
      rw [Multiset.map_map]
      congr 1
      funext L
      exact hFG L

end Local

section Global

variable (p : Prime) (h : IsEichler ell N R) (hp : ¬ p.val ∣ N * ell)

private theorem exists_aligned (i : ClassSet R) :
    ∃ z : FiniteUnits R, fromAdelic z = representative i ∧
      z.val p = (LineIndex.chartAt h hp i).gen := by
  let v := classRepresentative i
  let g := (LineIndex.chartAt h hp i).gen
  have hv : fromAdelic v = representative i := fromAdelic_classRepresentative i
  have hl : localRight R p (v.val p) = localRight R p g := by
    rw [← fromAdelic_completion, hv]
    exact SetLike.coe_injective ((LineIndex.chartAt h hp i).ideal_eq.trans (localRight_set p g).symm)
  let r := single R p ((v.val p)⁻¹ * g)
  have hu : r ∈ integralUnits R := by
    intro q
    by_cases hq : q = p
    · subst q
      change (single R p _).val p ∈ localUnits R p
      rw [single_same]
      exact (localRight_eq_iff p _ _).mp hl
    · change (single R p _).val q ∈ localUnits R q
      rw [single_away hq]
      exact (localUnits R q).one_mem
  refine ⟨v * r, Subtype.ext ?_, ?_⟩
  · rw [← hv]
    exact (fromAdelic_translate_iff v (v * r) 1).mpr ⟨⟨r, hu⟩, by simp⟩ |>.trans
      ((fromAdelic v).val.translate_one)
  · change v.val p * (single R p _).val p = g
    rw [single_same, mul_inv_cancel_left]

/-- A lift of the chosen ideal representative with its chart's local generator at p. -/
def aligned (i : ClassSet R) : FiniteUnits R := (exists_aligned p h hp i).choose

theorem aligned_ideal (i : ClassSet R) :
    fromAdelic (aligned p h hp i) = representative i :=
  (exists_aligned p h hp i).choose_spec.1

theorem aligned_gen (i : ClassSet R) :
    (aligned p h hp i).val p = (LineIndex.chartAt h hp i).gen :=
  (exists_aligned p h hp i).choose_spec.2

/-- A single right coset in the good-prime double coset acting on the chosen lift.
Line labels are retained even when their resulting double cosets agree. -/
def heckeStep (i : ClassSet R) (L : Option (ZMod p.val)) : DoubleCosets R :=
  Quotient.mk _ (aligned p h hp i * single R p (heckeBasis p (LineIndex.chartAt h hp i).split L))

set_option maxHeartbeats 1200000 in
/-- The adelic step has exactly the local spans of the corresponding ideal neighbour. -/
theorem heckeStep_eq_nbAt (i : ClassSet R) (L : Option (ZMod p.val)) :
    idealsEquiv R (heckeStep p h hp i L) = nbAt (LineIndex.lineIndex h hp) i L := by
  let I := representative i
  let C := LineIndex.chartAt h hp i
  let J := (C.neighbourEquiv p.prop.ne_zero I.prop L).val
  let w := aligned p h hp i * single R p (heckeBasis p C.split L)
  have hJ : J.val.lattice = C.preimage (LineIndex.columns (LineIndex.line L)) :=
    C.neighbourEquiv_lattice p.prop.ne_zero I.prop L
  change Quotient.mk _ (fromAdelic w) = Quotient.mk _ J
  congr 1
  apply Subtype.ext
  apply RightIdeal.ext
  ext x
  rw [mem_iff_all_local (fromAdelic w).val.full x, mem_iff_all_local J.val.full x]
  apply forall_congr'
  intro q
  rw [fromAdelic_completion]
  by_cases he : q = p
  · subst q
    have hw : w.val p = C.gen * heckeBasis p C.split L := by
      change (aligned p h hp i).val p * (single R p _).val p = _
      rw [single_same, aligned_gen]
    rw [hw]
    have hk (y : Bp p.val a b) :
        y ∈ localRight R p (C.gen * heckeBasis p C.split L) ↔
          y ∈ localLattice p.val J.val.lattice := by
      have h₁ := C.scalar_le_preimage p.prop.ne_zero (LineIndex.columns (LineIndex.line L))
      have h₂ := C.preimage_le (LineIndex.columns (LineIndex.line L))
      have hmem (A : M2 ℤ_[p.val]) :
          C.embed A ∈ localLattice p.val J.val.lattice ↔
            LineIndex.reduce p.val A ∈ LineIndex.columns (LineIndex.line L) := by
        rw [hJ]
        exact C.localLattice_preimage p.prop.ne_zero h₁ h₂ _ (C.mem_preimage _) A
      rw [← SetLike.mem_coe, localRight_set, ← C.split.range_embed]
      constructor
      · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
        rw [Units.val_mul, heckeBasis_val]
        dsimp only
        rw [mul_assoc, ← map_mul]
        change C.embed (LineIndex.basisMatrix p.val L * A) ∈ _
        exact (hmem _).mpr ((LineIndex.reduce_mem_columns_iff L _).mpr ⟨A, rfl⟩)
      · intro hy
        have hyI : y ∈ localLattice p.val I.val.lattice :=
          localLattice_mono p (hJ.symm ▸ h₂) hy
        obtain ⟨A, rfl⟩ := C.range_embed.symm ▸ hyI
        obtain ⟨B, hB⟩ := (LineIndex.reduce_mem_columns_iff L A).mp ((hmem A).mp hy)
        refine ⟨_, ⟨B, rfl⟩, ?_⟩
        rw [Units.val_mul, heckeBasis_val]
        dsimp only
        rw [mul_assoc, ← map_mul, ← hB]
        rfl
    exact hk _
  · have haway : w.val q = (aligned p h hp i).val q := by
      change (aligned p h hp i).val q * (single R p _).val q = _
      rw [single_away he, mul_one]
    rw [haway, ← fromAdelic_completion, aligned_ideal, hJ,
      LineIndex.localLattice_eq_away p.prop.ne_zero (C.scalar_le_preimage _ _)
        (C.preimage_le _) q.val (fun he' => he (Subtype.ext he'))]

theorem heckeStep_eq_neighbours (i : ClassSet R) (L : Option (ZMod p.val)) :
    idealsEquiv R (heckeStep p h hp i L) = LineIndex.neighbours h p.val i L := by
  rw [LineIndex.neighbours_at h hp, heckeStep_eq_nbAt]

/-- The good-prime action on the adelic class set with its p+1 terms and multiplicities. -/
def hecke : DoubleCosets R → Multiset (DoubleCosets R) :=
  let S := (LineIndex.nonempty_split h hp).some
  Quotient.lift (heckeAtRep p S) (fun _ _ => heckeAtRep_eq_of_rel p S)

theorem hecke_mk (z : FiniteUnits R) :
    hecke p h hp (Quotient.mk _ z) = heckeAtRep p (LineIndex.nonempty_split h hp).some z := rfl

theorem hecke_eq_neighbours (z : DoubleCosets R) :
    (hecke p h hp z).map (idealsEquiv R) =
      (Finset.univ : Finset (Option (ZMod p.val))).val.map
        (nbAt (LineIndex.lineIndex h hp) (idealsEquiv R z)) := by
  let i := idealsEquiv R z
  have hz : z = Quotient.mk _ (aligned p h hp i) := by
    apply (idealsEquiv R).injective
    rw [idealsEquiv_mk, aligned_ideal]
    exact (Quotient.out_eq i).symm
  have hm : hecke p h hp z = Finset.univ.val.map (heckeStep p h hp i) := by
    calc
      _ = hecke p h hp (Quotient.mk _ (aligned p h hp i)) := congrArg (hecke p h hp) hz
      _ = _ := rfl
  rw [hm, Multiset.map_map]
  congr 1
  funext L
  exact heckeStep_eq_nbAt p h hp _ L

end Global


end ZInQ.Manuscript.RC.Adelic

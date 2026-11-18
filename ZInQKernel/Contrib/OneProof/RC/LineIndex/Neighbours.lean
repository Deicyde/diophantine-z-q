import ZInQKernel.Contrib.OneProof.RC.LineIndex.LocalPrincipal

/-!
# From column lines to the actual ideal correspondence

Tex 9040–9042, 9067–9071. Integral preimages give the actual neighbour ideals
(on-the-spot, c). Arrow reversal and the weighted count are supplied by the Eichler layer.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LineIndex

open Eichler Module

variable {a b : ℚ} {R : Order a b} {I : RightIdeal R}
variable {p : ℕ} [Fact p.Prime]

namespace Chart

variable (C : Chart I p)

/-- The integral preimage, viewed in the ambient rational algebra. -/
def preimage (S : Submodule (ZMod p) (Mat (ZMod p))) : Submodule ℤ (B a b) :=
  (S.toAddSubgroup.comap C.residue).toIntSubmodule.map I.lattice.subtype

theorem mem_preimage (S : Submodule (ZMod p) (Mat (ZMod p))) (x : I.lattice) :
    x.val ∈ C.preimage S ↔ C.residue x ∈ S := by
  change (∃ y : I.lattice, C.residue y ∈ S ∧ y.val = x.val) ↔ _
  refine ⟨?_, fun h => ⟨x, h, rfl⟩⟩
  rintro ⟨y, hy, e⟩
  exact (Subtype.ext e : y = x) ▸ hy

theorem preimage_le (S : Submodule (ZMod p) (Mat (ZMod p))) : C.preimage S ≤ I.lattice := by
  rintro _ ⟨y, _, rfl⟩
  exact y.prop

theorem scalar_le_preimage (hp : p ≠ 0) (S : Submodule (ZMod p) (Mat (ZMod p))) :
    (I.translate (RightIdeal.scalarUnit p hp)).lattice ≤ C.preimage S := by
  rintro _ ⟨x, hx, rfl⟩
  change (↑(RightIdeal.scalarUnit (a := a) (b := b) p hp) : B a b) * x ∈ C.preimage S
  rw [RightIdeal.scalar_mul]
  apply (C.mem_preimage S (p • (⟨x, hx⟩ : I.lattice))).mpr
  have h : (p • (⟨x, hx⟩ : I.lattice)) ∈ C.residue.ker := by
    rw [C.ker_residue hp]
    exact (mem_scalarSubgroup hp _).mpr ⟨_, rfl⟩
  rw [AddMonoidHom.mem_ker.mp h]
  exact S.zero_mem

theorem preimage_index (S : Submodule (ZMod p) (Mat (ZMod p))) :
    (C.preimage S).toAddSubgroup.relIndex I.lattice.toAddSubgroup = S.toAddSubgroup.index := by
  have h : (C.preimage S).toAddSubgroup.comap I.lattice.subtype.toAddMonoidHom =
      S.toAddSubgroup.comap C.residue := by
    ext x
    exact C.mem_preimage S x
  change ((C.preimage S).toAddSubgroup.comap I.lattice.subtype.toAddMonoidHom).index = _
  rw [h, AddSubgroup.index_comap_of_surjective _ C.residue_surjective]

private theorem index_eq_iff (S : Submodule (ZMod p) (Mat (ZMod p))) :
    S.toAddSubgroup.index = p^2 ↔ finrank (ZMod p) S = 2 := by
  classical
  have hc : Nat.card S = p ^ finrank (ZMod p) S := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hm := S.toAddSubgroup.card_mul_index
  change Nat.card S * S.toAddSubgroup.index = Nat.card (Mat (ZMod p)) at hm
  rw [hc, card_residueMatrices, show p^4 = p^2 * p^2 by ring] at hm
  have hp₂ : 0 < p^2 := pow_pos (Fact.out : p.Prime).pos _
  constructor
  · intro h
    rw [h] at hm
    exact Nat.pow_right_injective (Fact.out : p.Prime).one_lt
      (Nat.eq_of_mul_eq_mul_right hp₂ hm)
  · intro h
    rw [h] at hm
    exact Nat.eq_of_mul_eq_mul_left hp₂ hm

private theorem full_preimage (hp : p ≠ 0) (S : Submodule (ZMod p) (Mat (ZMod p))) :
    FullLattice (C.preimage S) := by
  refine ⟨?_, ?_⟩
  · let : Module.Finite ℤ I.lattice := Module.Finite.of_fg I.full.fg
    exact (IsNoetherian.noetherian _).map _
  · refine top_unique ?_
    rw [← I.full.span_eq_top]
    refine Submodule.span_le.mpr fun x hx => ?_
    have hpx : p • x ∈ C.preimage S :=
      C.scalar_le_preimage hp S ⟨x, hx, RightIdeal.scalar_mul _ _ _⟩
    have hmem := Submodule.subset_span (R := ℚ)
      (s := (C.preimage S : Set (B a b))) hpx
    rw [← Nat.cast_smul_eq_nsmul ℚ] at hmem
    have h := (Submodule.span ℚ (C.preimage S : Set (B a b))).smul_mem (p : ℚ)⁻¹ hmem
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
    rwa [smul_smul, inv_mul_cancel₀ hpQ, one_smul] at h

/-- The preimage of a right plane is a full right ideal. -/
def preimageIdeal (hp : p ≠ 0) (S : RightPlanes (ZMod p)) : RightIdeal R where
  lattice := C.preimage S.val
  full := C.full_preimage hp S.val
  mul_mem := by
    intro x r hx hr
    let y : I.lattice := ⟨x, C.preimage_le S.val hx⟩
    let z : I.lattice := ⟨x * r, I.mul_mem y.prop hr⟩
    apply (C.mem_preimage S.val z).mpr
    change C.residue ⟨y.val * r, I.mul_mem y.prop hr⟩ ∈ S.val
    rw [C.residue_mul y ⟨r, hr⟩]
    exact S.prop.1 _ ((C.mem_preimage S.val y).mp hx) _

theorem preimageIdeal_isNeighbour (hp : p ≠ 0) (S : RightPlanes (ZMod p)) :
    RightIdeal.IsNeighbour p hp I (C.preimageIdeal hp S) :=
  ⟨C.scalar_le_preimage hp S.val, C.preimage_le S.val,
    (C.preimage_index S.val).trans ((index_eq_iff S.val).mpr S.prop.2)⟩

private def image (J : RightIdeal R) :
    Submodule (ZMod p) (Mat (ZMod p)) where
  carrier := {A | ∃ x : I.lattice, x.val ∈ J.lattice ∧ C.residue x = A}
  zero_mem' := ⟨0, J.lattice.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, J.lattice.add_mem hx hy, map_add _ _ _⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    exact ⟨n • x, J.lattice.smul_mem n hx, by rw [map_zsmul, Int.cast_smul_eq_zsmul]⟩

private theorem image_right (J : RightIdeal R)
    (A : Mat (ZMod p)) (hA : A ∈ C.image J) (B : Mat (ZMod p)) :
    A * B ∈ C.image J := by
  obtain ⟨x, hx, rfl⟩ := hA
  obtain ⟨r, rfl⟩ := C.split.orderResidue_surjective B
  exact ⟨⟨x.val * r.val, I.mul_mem x.prop r.prop⟩, J.mul_mem hx r.prop, C.residue_mul x r⟩

/-- The subideal between `pI` and `I` is recovered from its reduction. -/
theorem preimage_image (hp : p ≠ 0) (J : RightIdeal R)
    (h₁ : (I.translate (RightIdeal.scalarUnit p hp)).lattice ≤ J.lattice)
    (h₂ : J.lattice ≤ I.lattice) : C.preimage (C.image J) = J.lattice := by
  ext x
  constructor
  · intro hx
    let x' : I.lattice := ⟨x, C.preimage_le _ hx⟩
    obtain ⟨y, hy, e⟩ := (C.mem_preimage _ x').mp hx
    have he : x' - y ∈ C.residue.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, ← e, sub_self]
    rw [C.ker_residue hp] at he
    exact (J.lattice.sub_mem_iff_left hy).mp (h₁ he)
  · intro hx
    exact (C.mem_preimage _ (⟨x, h₂ hx⟩ : I.lattice)).mpr ⟨⟨x, h₂ hx⟩, hx, rfl⟩

/-- The integral preimages of right planes are exactly the index-`p²` neighbours. -/
def preimageEquiv (hp : p ≠ 0) :
    RightPlanes (ZMod p) ≃ {J : RightIdeal R // RightIdeal.IsNeighbour p hp I J} :=
  Equiv.ofBijective (fun S => ⟨C.preimageIdeal hp S, C.preimageIdeal_isNeighbour hp S⟩) (by
    constructor
    · intro S T h
      have eq : C.preimage S.val = C.preimage T.val :=
        congrArg (fun J : {J : RightIdeal R // RightIdeal.IsNeighbour p hp I J} => J.val.lattice) h
      apply Subtype.ext
      ext A
      obtain ⟨x, rfl⟩ := C.residue_surjective A
      rw [← C.mem_preimage, ← C.mem_preimage, eq]
    · rintro ⟨J, h₁, h₂, hidx⟩
      let S := C.image J
      have hrec := C.preimage_image hp J h₁ h₂
      have hS : finrank (ZMod p) S = 2 :=
        (index_eq_iff S).mp ((C.preimage_index S).symm.trans (by rw [hrec, hidx]))
      exact ⟨⟨S, C.image_right J, hS⟩, Subtype.ext (RightIdeal.ext hrec)⟩)

/-- The neighbour at a line is locally principal at every prime. -/
theorem preimage_locallyPrincipal (hp : p ≠ 0) (hI : I.LocallyPrincipal)
    (L : Option (ZMod p)) : (C.preimageIdeal hp (rightPlanes L)).LocallyPrincipal := by
  let S := (rightPlanes L : RightPlanes (ZMod p)).val
  have h₁ := C.scalar_le_preimage hp S
  have h₂ := C.preimage_le S
  intro q hq
  by_cases he : q = p
  · subst q
    exact C.localPrincipal_at hp h₁ h₂ L (C.mem_preimage S)
  · rw [show (C.preimageIdeal hp (rightPlanes L)).lattice = C.preimage S from rfl,
      localLattice_eq_away hp h₁ h₂ q he]
    exact hI q

/-- The equivalence with the *locally principal* actual neighbours, preserving kernels. -/
def neighbourEquiv (hp : p ≠ 0) (hI : I.LocallyPrincipal) :
    Option (ZMod p) ≃ {J : LPIdeal R // RightIdeal.IsNeighbour p hp I J.val} :=
  (rightPlanes.trans (C.preimageEquiv hp)).trans
    (Equiv.ofBijective
      (fun J =>
        ⟨⟨J.val, by
          obtain ⟨L, hL⟩ := (rightPlanes.trans (C.preimageEquiv hp)).surjective J
          rw [← hL]
          exact C.preimage_locallyPrincipal hp hI L⟩, J.prop⟩)
      ⟨fun x y h => Subtype.ext
        (congrArg (fun z : {J : LPIdeal R // RightIdeal.IsNeighbour p hp I J.val} =>
          z.val.val) h), fun J => ⟨⟨J.val.val, J.prop⟩, rfl⟩⟩)

theorem neighbourEquiv_lattice (hp : p ≠ 0) (hI : I.LocallyPrincipal)
    (L : Option (ZMod p)) :
    ((C.neighbourEquiv hp hI L).val.val).lattice = C.preimage (columns (line L)) := rfl

end Chart

variable {ell N : ℕ}

/-- Fix the local coordinates used for a chosen class representative at a good prime. -/
def chartAt (h : IsEichler ell N R) (hp : ¬ p ∣ N * ell) (i : ClassSet R) :
    Chart (representative i).val p :=
  let u := (representative i).prop p
  ⟨(nonempty_split h hp).some, u.choose, u.choose_spec⟩

/-- The line indexing of the chosen representatives in the Eichler class set. -/
def lineIndex (h : IsEichler ell N R) (hp : ¬ p ∣ N * ell) :
    Eichler.LineIndex R p (Fact.out : p.Prime).ne_zero := fun i =>
  (chartAt h hp i).neighbourEquiv (Fact.out : p.Prime).ne_zero (representative i).prop

/-- The actual neighbour classes in the type of `AppF.ThetaStage.nb`. -/
def neighbours (h : IsEichler ell N R) :
    (p : ℕ) → ClassSet R → Option (ZMod p) → ClassSet R :=
  Eichler.nb (Good := fun q => q.Prime ∧ ¬ q ∣ N * ell) (fun _ hq => hq.1)
    (fun q hq => letI : Fact q.Prime := ⟨hq.1⟩; lineIndex h hq.2)

/-- At a good prime the total map uses the ideal at the specified line index. -/
theorem neighbours_at (h : IsEichler ell N R) (hp : ¬ p ∣ N * ell)
    (i : ClassSet R) (L : Option (ZMod p)) :
    neighbours h p i L = Eichler.nbAt (lineIndex h hp) i L := by
  classical
  exact dite_eq_left ⟨(Fact.out : p.Prime), hp⟩

/-- At every good prime, the actual ideal correspondence satisfies the App F adjoint identity. -/
theorem adjoint_good (h : IsEichler ell N R) (ha : a < 0) (hb : b < 0)
    (p : ℕ) (hp : p.Prime) (hg : ¬ p ∣ N * ell) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ i j, AppF.nbrCount (neighbours h p) i j * classWeight ha hb j =
      AppF.nbrCount (neighbours h p) j i * classWeight ha hb i :=
  Eichler.adjoint (Good := fun q => q.Prime ∧ ¬ q ∣ N * ell) ha hb (fun _ hq => hq.1)
    (fun q hq => letI : Fact q.Prime := ⟨hq.1⟩; lineIndex h hq.2) p ⟨hp, hg⟩

#print axioms Chart.mem_preimage
#print axioms Chart.preimage_le
#print axioms Chart.scalar_le_preimage
#print axioms Chart.preimage_index
#print axioms Chart.index_eq_iff
#print axioms Chart.full_preimage
#print axioms Chart.preimageIdeal
#print axioms Chart.preimageIdeal_isNeighbour
#print axioms Chart.image_right
#print axioms Chart.preimage_image
#print axioms Chart.preimageEquiv
#print axioms Chart.preimage_locallyPrincipal
#print axioms Chart.neighbourEquiv
#print axioms Chart.neighbourEquiv_lattice
#print axioms chartAt
#print axioms lineIndex
#print axioms neighbours
#print axioms neighbours_at
#print axioms adjoint_good

end ZInQ.Manuscript.RC.LineIndex

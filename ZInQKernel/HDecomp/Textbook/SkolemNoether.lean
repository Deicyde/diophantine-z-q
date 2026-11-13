import Mathlib
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.Descent.B1Quat

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5b from
`scratch/t-skolem-kw/SkolemNoether.lean` (T13).
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-!
# t-skolem-kw: leaf T13 (Skolem–Noether), proved

The statement `SkolemNoether` is copied verbatim from `scratch/h-decomposition/Leaves.lean`
(`PkgI6.SkolemNoether`; `HSyn.SkolemNoether` is the same Prop up to the name of a bound
variable).  The automorphism form `LeafSkolemNoether` (`Leaves.lean`, glue-descent section) is
derived at the end.

Proof (the standard one, e.g. Farb–Dennis, *Noncommutative algebra*, Thm 3.14 (UNVERIFIED
locator)):
1. `isSimpleRing_tensor`: `C ⊗[K] B` is simple when `C` is central simple and `B` is simple
   (minimal-length argument in a basis of `B`).
2. `nonempty_linearEquiv_of_finrank_eq`: over a simple Artinian `K`-algebra `R`, two modules of
   the same finite `K`-dimension are isomorphic (both are powers of the unique simple module).
3. `A` is a module over `R = Aᵐᵒᵖ ⊗[K] B` in two ways, `(a ⊗ b) • x = f b * x * a` and
   `(a ⊗ b) • x = g b * x * a`; an `R`-isomorphism between them is left multiplication by a unit
   `u` with `u * f b = g b * u`.
-/

open TensorProduct

/-! `SkolemNoether` and `LeafSkolemNoether` (verbatim copies
in the draft) are `PkgI6.SkolemNoether` (`Conductor.I6Base`) and
`GlueDescent.LeafSkolemNoether` (`Descent.B1Quat`). -/
open PkgI6 (SkolemNoether)
open GlueDescent (LeafSkolemNoether)

namespace TSkolemKW

/-! ## The statements (verbatim from `scratch/h-decomposition/Leaves.lean`) -/

/-- **L14. Skolem–Noether.** Verbatim `HSyn.SkolemNoether`. -/
def HSynSkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

/-! ## Step 1. `C ⊗ B` is simple for `C` central simple and `B` simple -/

section TensorSimple

variable {K C B : Type*} [Field K] [Ring C] [Algebra K C] [Algebra.IsCentral K C]
  [IsSimpleRing C] [Ring B] [Algebra K B] [IsSimpleRing B]

theorem isSimpleRing_tensor : IsSimpleRing (C ⊗[K] B) := by
  classical
  let e := Module.Free.chooseBasis K B
  let E := TensorProduct.equivFinsuppOfBasisRight (M := C) e
  have hmul : ∀ (a a' : C) (x : C ⊗[K] B) i,
      E ((a ⊗ₜ (1 : B)) * x * (a' ⊗ₜ (1 : B))) i = a * E x i * a' := by
    intro a a' x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, E]
      rw [mul_smul_comm, smul_mul_assoc]
    | add x y hx hy => simp only [mul_add, add_mul, map_add, Finsupp.add_apply, hx, hy]
  have hE0 : ∀ x, E x = 0 → x = 0 := fun x h => E.map_eq_zero_iff.1 h
  have hnt : Nontrivial (C ⊗[K] B) := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have h1 : E (1 : C ⊗[K] B) ≠ 0 := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.equivFinsuppOfBasisRight_apply_tmul]
      intro h0
      have hr : e.repr (1 : B) ≠ 0 := by
        rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
      apply hr
      ext i
      have := congrArg (fun d => d i) h0
      simpa using this
    exact h1 (by rw [h, map_zero])
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ x ∈ I, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hI (eq_bot_iff.2 fun x hx => (TwoSidedIdeal.mem_bot _).2 (hcon x hx))
  have H : ∃ n, ∃ x ∈ I, x ≠ 0 ∧ (E x).support.card = n := by
    obtain ⟨x, hx, hx0⟩ := hex
    exact ⟨_, x, hx, hx0, rfl⟩
  obtain ⟨x, hxI, hx0, hxn⟩ := Nat.find_spec H
  have hmin : ∀ y ∈ I, y ≠ 0 → Nat.find H ≤ (E y).support.card :=
    fun y hy hy0 => Nat.find_min' H ⟨y, hy, hy0, rfl⟩
  obtain ⟨i0, hi0⟩ : (E x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun h => hx0 (hE0 x h)
  -- the two-sided ideal of `C` of `i0`-coefficients of elements of `I` supported in `supp x`
  let J : TwoSidedIdeal C := TwoSidedIdeal.mk'
    {a | ∃ y ∈ I, (E y).support ⊆ (E x).support ∧ E y i0 = a}
    ⟨0, I.zero_mem, by simp, by simp⟩
    (by
      rintro _ _ ⟨y, hy, hys, rfl⟩ ⟨y', hy', hys', rfl⟩
      refine ⟨y + y', I.add_mem hy hy', ?_, by simp⟩
      rw [map_add]
      exact Finsupp.support_add.trans (Finset.union_subset hys hys'))
    (by
      rintro _ ⟨y, hy, hys, rfl⟩
      refine ⟨-y, I.neg_mem hy, ?_, by simp⟩
      rw [map_neg, Finsupp.support_neg]
      exact hys)
    (by
      rintro a _ ⟨y, hy, hys, rfl⟩
      refine ⟨(a ⊗ₜ (1 : B)) * y * ((1 : C) ⊗ₜ (1 : B)),
        I.mul_mem_right _ _ (I.mul_mem_left _ _ hy), fun j hj => hys ?_, by rw [hmul, mul_one]⟩
      rw [Finsupp.mem_support_iff] at hj ⊢
      intro h
      apply hj
      rw [hmul, h, mul_zero, zero_mul])
    (by
      rintro _ a ⟨y, hy, hys, rfl⟩
      refine ⟨((1 : C) ⊗ₜ (1 : B)) * y * (a ⊗ₜ (1 : B)),
        I.mul_mem_right _ _ (I.mul_mem_left _ _ hy), fun j hj => hys ?_, by rw [hmul, one_mul]⟩
      rw [Finsupp.mem_support_iff] at hj ⊢
      intro h
      apply hj
      rw [hmul, h, mul_zero, zero_mul])
  have h1J : (1 : C) ∈ J := by
    refine IsSimpleRing.one_mem_of_ne_zero_mem J (Finsupp.mem_support_iff.1 hi0) ?_
    rw [TwoSidedIdeal.mem_mk']
    exact ⟨x, hxI, le_rfl, rfl⟩
  rw [TwoSidedIdeal.mem_mk'] at h1J
  obtain ⟨y, hyI, hys, hy1⟩ := h1J
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy1
  -- every coefficient of `y` is central
  have hcomm : ∀ (a : C) j, a * E y j = E y j * a := by
    intro a
    let z := (a ⊗ₜ (1 : B)) * y * ((1 : C) ⊗ₜ (1 : B)) -
      ((1 : C) ⊗ₜ (1 : B)) * y * (a ⊗ₜ (1 : B))
    have hzc : ∀ j, E z j = a * E y j - E y j * a := by
      intro j
      simp only [z, map_sub, Finsupp.sub_apply, hmul, mul_one, one_mul]
    have hzI : z ∈ I := I.sub_mem (I.mul_mem_right _ _ (I.mul_mem_left _ _ hyI))
      (I.mul_mem_right _ _ (I.mul_mem_left _ _ hyI))
    have hzs : (E z).support ⊆ (E y).support.erase i0 := by
      intro j hj
      rw [Finsupp.mem_support_iff, hzc] at hj
      rw [Finset.mem_erase, Finsupp.mem_support_iff]
      constructor
      · rintro rfl
        apply hj
        rw [hy1, mul_one, one_mul, sub_self]
      · intro h
        apply hj
        rw [h, mul_zero, zero_mul, sub_self]
    have hz0 : z = 0 := by
      by_contra hz0
      have h1 := hmin z hzI hz0
      have h2 := Finset.card_le_card hzs
      have h3 : ((E y).support.erase i0).card < (E y).support.card :=
        Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.2 (by rw [hy1]; exact one_ne_zero))
      have h4 := Finset.card_le_card hys
      omega
    intro j
    have := hzc j
    rw [hz0, map_zero, Finsupp.zero_apply] at this
    exact (sub_eq_zero.1 this.symm)
  have hcen : ∀ j, ∃ k : K, E y j = algebraMap K C k := fun j =>
    (Algebra.IsCentral.mem_center_iff K).1 (Subalgebra.mem_center_iff.2 fun a => hcomm a j)
  choose k hk using hcen
  have hinj : Function.Injective (algebraMap K C) := (algebraMap K C).injective
  let d : Module.Free.ChooseBasisIndex K B →₀ K := Finsupp.onFinset (E y).support k (by
    intro j hj
    rw [Finsupp.mem_support_iff, hk]
    intro h
    exact hj (hinj (by rw [h, map_zero])))
  let b : B := e.repr.symm d
  have hyb : (1 : C) ⊗ₜ b = y := by
    apply E.injective
    ext j
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, hk, Algebra.algebraMap_eq_smul_one]
    simp [b, d]
  have hb0 : b ≠ 0 := by
    rintro hb
    rw [hb, TensorProduct.tmul_zero] at hyb
    exact hy0 hyb.symm
  let J' : TwoSidedIdeal B := TwoSidedIdeal.comap (Algebra.TensorProduct.includeRight (R := K)
    (A := C) (B := B)) I
  have hbJ : b ∈ J' := by
    rw [TwoSidedIdeal.mem_comap]
    simpa [hyb] using hyI
  have h1J' := IsSimpleRing.one_mem_of_ne_zero_mem J' hb0 hbJ
  rw [TwoSidedIdeal.mem_comap, map_one] at h1J'
  exact eq_top_iff.2 fun z _ => by simpa using I.mul_mem_left z 1 h1J'

end TensorSimple

/-! ## Step 2. Modules over a simple Artinian algebra are classified by their dimension -/

theorem nonempty_linearEquiv_of_finrank_eq {K R M N : Type*} [Field K] [Ring R] [Algebra K R]
    [IsSimpleRing R] [IsArtinianRing R]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M] [FiniteDimensional K M]
    [AddCommGroup N] [Module K N] [Module R N] [IsScalarTower K R N] [FiniteDimensional K N]
    (h : Module.finrank K M = Module.finrank K N) : Nonempty (M ≃ₗ[R] N) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton N := by
      rw [← Module.finrank_zero_iff (R := K), ← h]
      exact Module.finrank_zero_of_subsingleton
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  have hN : Nontrivial N := by
    rw [← Module.finrank_pos_iff (R := K), ← h]
    exact Module.finrank_pos
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite K R M
  have : Module.Finite R N := Module.Finite.of_restrictScalars_finite K R N
  obtain ⟨n, _, S, hS, ⟨eM⟩⟩ := (IsSimpleRing.isIsotypic R M).linearEquiv_fun
  obtain ⟨m, _, T, hT, ⟨eN⟩⟩ := (IsSimpleRing.isIsotypic R N).linearEquiv_fun
  -- the two simple modules are isomorphic
  have eST : Nonempty (S ≃ₗ[R] T) := by
    let S' := S.map (LinearMap.inl R M N)
    let T' := T.map (LinearMap.inr R M N)
    let eS : S ≃ₗ[R] S' := S.equivMapOfInjective _ LinearMap.inl_injective
    let eT : T ≃ₗ[R] T' := T.equivMapOfInjective _ LinearMap.inr_injective
    have : IsSimpleModule R S' := IsSimpleModule.congr eS.symm
    have : IsSimpleModule R T' := IsSimpleModule.congr eT.symm
    obtain ⟨e'⟩ := IsSimpleRing.isIsotypic R (M × N) S' T'
    exact ⟨(eS.trans e'.symm).trans eT.symm⟩
  obtain ⟨eST⟩ := eST
  have : Module.Finite K S :=
    Module.Finite.of_injective (S.subtype.restrictScalars K) Subtype.val_injective
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  have hd : 0 < Module.finrank K S := Module.finrank_pos
  have hM' : Module.finrank K M = n * Module.finrank K S := by
    rw [(eM.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]
    simp
  have hN' : Module.finrank K N = m * Module.finrank K S := by
    rw [((eN.trans (LinearEquiv.piCongrRight fun _ => eST.symm)).restrictScalars K).finrank_eq,
      Module.finrank_pi_fintype]
    simp
  have hnm : n = m := Nat.eq_of_mul_eq_mul_right hd (hM'.symm.trans (h.trans hN'))
  subst hnm
  exact ⟨eM.trans ((LinearEquiv.piCongrRight fun _ => eST).trans eN.symm)⟩

/-! ## Step 3. `A` as a module through an algebra map to `End_K A` -/

/-- `A` viewed as an `R`-module through `ρ : R →ₐ[K] End_K A`. -/
def Twist {K R A : Type*} [CommRing K] [Ring R] [Algebra K R] [AddCommGroup A] [Module K A]
    (_ρ : R →ₐ[K] Module.End K A) : Type _ := A

namespace Twist

variable {K R A : Type*} [CommRing K] [Ring R] [Algebra K R] [AddCommGroup A] [Module K A]
  (ρ : R →ₐ[K] Module.End K A)

instance : AddCommGroup (Twist ρ) := inferInstanceAs (AddCommGroup A)
instance : Module K (Twist ρ) := inferInstanceAs (Module K A)
instance : Module R (Twist ρ) := Module.compHom A (ρ : R →+* Module.End K A)

/-- The identity `A → Twist ρ`. -/
def of : A ≃ₗ[K] Twist ρ := LinearEquiv.refl K A

theorem smul_of (r : R) (x : A) : r • of ρ x = of ρ (ρ r x) := rfl

instance isScalarTower : IsScalarTower K R (Twist ρ) :=
  ⟨fun k r x => by
    change ρ (k • r) x = k • ρ r x
    rw [map_smul]
    rfl⟩

end Twist

/-! ## The theorem -/

theorem skolemNoether : SkolemNoether := by
  intro K A B _ _ _ _ _ _ _ _ _ _ f g
  let R := Aᵐᵒᵖ ⊗[K] B
  have : IsSimpleRing R := isSimpleRing_tensor
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  let ρ : (B →ₐ[K] A) → R →ₐ[K] Module.End K A := fun h =>
    (AlgHom.mulLeftRight K A).comp
      ((Algebra.TensorProduct.map h (AlgHom.id K Aᵐᵒᵖ)).comp
        (Algebra.TensorProduct.comm K Aᵐᵒᵖ B).toAlgHom)
  have hρ : ∀ (h : B →ₐ[K] A) (a : A) (b : B) (x : A),
      ρ h (MulOpposite.op a ⊗ₜ b) x = h b * x * a := by
    intro h a b x
    change AlgHom.mulLeftRight K A ((Algebra.TensorProduct.map h (AlgHom.id K Aᵐᵒᵖ))
      ((Algebra.TensorProduct.comm K Aᵐᵒᵖ B) (MulOpposite.op a ⊗ₜ b))) x = _
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.mulLeftRight_apply]
    rfl
  have : FiniteDimensional K (Twist (ρ f)) := inferInstanceAs (FiniteDimensional K A)
  have : FiniteDimensional K (Twist (ρ g)) := inferInstanceAs (FiniteDimensional K A)
  have : IsScalarTower K R (Twist (ρ f)) := Twist.isScalarTower (ρ f)
  have : IsScalarTower K R (Twist (ρ g)) := Twist.isScalarTower (ρ g)
  obtain ⟨φ⟩ := @nonempty_linearEquiv_of_finrank_eq K R (Twist (ρ f)) (Twist (ρ g)) _ _ _ _ _
    _ _ _ (Twist.isScalarTower (ρ f)) _ _ _ _ (Twist.isScalarTower (ρ g)) _ rfl
  let Φ : A → A := fun x => Twist.of (ρ g) |>.symm (φ (Twist.of (ρ f) x))
  have hΦinj : Function.Injective Φ := fun x y hxy => by
    simpa [Φ] using hxy
  have hΦsurj : Function.Surjective Φ := fun y =>
    ⟨(Twist.of (ρ f)).symm (φ.symm (Twist.of (ρ g) y)), by simp [Φ]⟩
  have hΦact : ∀ (a : A) (b : B) (x : A), Φ (f b * x * a) = g b * Φ x * a := by
    intro a b x
    have h1 : Twist.of (ρ f) (f b * x * a) = (MulOpposite.op a ⊗ₜ b : R) • Twist.of (ρ f) x := by
      rw [Twist.smul_of, hρ]
    show (Twist.of (ρ g)).symm (φ (Twist.of (ρ f) (f b * x * a))) = g b * Φ x * a
    rw [h1, map_smul, ← hρ g a b]
    rfl
  let u := Φ 1
  have hΦx : ∀ x, Φ x = u * x := fun x => by
    simpa using hΦact x 1 1
  have hΦb : ∀ b, Φ (f b) = g b * u := fun b => by
    simpa using hΦact 1 b 1
  obtain ⟨v, hv⟩ := hΦsurj 1
  rw [hΦx] at hv
  have hvu : v * u = 1 := by
    apply hΦinj
    rw [hΦx, hΦx, ← mul_assoc, hv, one_mul, mul_one]
  refine ⟨⟨u, v, hv, hvu⟩, fun b => ?_⟩
  change g b = u * f b * v
  rw [← hΦx, hΦb, mul_assoc, hv, mul_one]

theorem hsynSkolemNoether : HSynSkolemNoether := skolemNoether

theorem leafSkolemNoether : LeafSkolemNoether := by
  intro K _ A _ _ _ _ _ φ
  obtain ⟨u, hu⟩ := skolemNoether K A A (AlgHom.id K A) φ.toAlgHom
  exact ⟨u, fun a => by simpa using hu a⟩

end TSkolemKW

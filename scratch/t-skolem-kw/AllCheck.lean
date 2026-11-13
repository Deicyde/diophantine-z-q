import Mathlib
import ZInQKernel.Compiler.Precision.HeightConstant

-- ===== SkolemNoether.lean =====

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

namespace TSkolemKW

/-! ## The statements (verbatim from `scratch/h-decomposition/Leaves.lean`) -/

/-- **Leaf I6.1 (Skolem–Noether).** Verbatim `PkgI6.SkolemNoether`. -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ u : Aˣ, ∀ b : B, g b = (u : A) * f b * ((u⁻¹ : Aˣ) : A)

/-- **L14. Skolem–Noether.** Verbatim `HSyn.SkolemNoether`. -/
def HSynSkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

/-- **Leaf L-B1 (Skolem–Noether, automorphism case).** Verbatim `LeafSkolemNoether`. -/
def LeafSkolemNoether : Prop :=
  ∀ (K : Type) [Field K] (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (φ : A ≃ₐ[K] A),
    ∃ u : Aˣ, ∀ a : A, φ a = u * a * (u⁻¹ : Aˣ)

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


-- ===== BrauerNesbitt.lean =====

/-!
# t-skolem-kw: leaf T19 (Brauer–Nesbitt in characteristic 0)

The statement `BrauerNesbittChar0` is copied verbatim from `scratch/h-decomposition/Leaves.lean`
(`PkgI6.BrauerNesbittChar0`, also `GlueC10.BrauerNesbittChar0`).

Proof (standard; cf. Curtis–Reiner (27.13), Lang, *Algebra* XVII Cor. 3.8, both UNVERIFIED
locators), for modules over an arbitrary `k`-algebra `R`:
1. `isNilpotent_of_trace_pow_eq_zero`: in characteristic 0 an endomorphism all of whose powers
   have trace 0 is nilpotent (Cayley–Hamilton gives `det = 0`; induct on the range).
2. `exists_injective_of_trace_eq`: if `M`, `N` have equal traces, `N` is semisimple and `S ⊆ M`
   is simple, then `S` embeds in `N`: the annihilator `J` of `N` acts nilpotently on `M` (1),
   hence kills `S` (if `t • s = s` for some `t ∈ J` then `s = 0`); so `S` is a quotient of
   `R / ann N ⊆ N^d`, hence (semisimplicity) a submodule of `N^d`, hence of `N`.
3. Induction on `dim M`: split off `S` from both sides.
-/

open Module

namespace TSkolemKW

/-! ## The statement (verbatim from `scratch/h-decomposition/Leaves.lean`) -/

/-- **Leaf I6.5 (Brauer–Nesbitt, characteristic 0, trace form).** Verbatim
`PkgI6.BrauerNesbittChar0`. -/
def BrauerNesbittChar0 : Prop :=
  ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
    (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)

/-! ## Step 1. Traces of powers vanish ⇒ nilpotent (characteristic 0) -/

theorem isNilpotent_of_trace_pow_eq_zero {k : Type*} [Field k] [CharZero k] :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    finrank k V = n → ∀ f : V →ₗ[k] V,
    (∀ j, 0 < j → LinearMap.trace k V (f ^ j) = 0) → IsNilpotent f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn f hf
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨1, Subsingleton.elim _ _⟩
  -- `f` is not injective: the constant term of the characteristic polynomial vanishes
  have hc0 : f.charpoly.coeff 0 = 0 := by
    have h0 := congrArg (LinearMap.trace k V) (LinearMap.aeval_self_charpoly f)
    rw [Polynomial.aeval_eq_sum_range, map_sum, map_zero, Finset.sum_range_succ'] at h0
    rw [Finset.sum_eq_zero (fun i _ => by rw [map_smul, hf (i + 1) (Nat.succ_pos i), smul_zero]),
      zero_add, pow_zero, map_smul, LinearMap.trace_one, smul_eq_mul] at h0
    have hpos : (finrank k V : k) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    exact (mul_eq_zero.1 h0).resolve_right hpos
  have hroot : f.charpoly.IsRoot 0 := by
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, hc0]
  obtain ⟨v, hv, hv0⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f 0).2 hroot).exists_hasEigenvector
  have hfv : f v = 0 := by
    have := Module.End.mem_eigenspace_iff.1 hv
    simpa using this
  -- restrict to the range
  let W := LinearMap.range f
  let g : W →ₗ[k] W := f.restrict (fun x _ => LinearMap.mem_range_self f x)
  have hgpow : ∀ j (w : W), (((g ^ j) w : W) : V) = (f ^ j) (w : V) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ihj =>
      intro w
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihj]
      rfl
  have hW : finrank k W < n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : 0 < finrank k (LinearMap.ker f) := by
      have : Nontrivial (LinearMap.ker f) := ⟨⟨⟨v, hfv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
      exact Module.finrank_pos
    change finrank k (LinearMap.range f) < n
    omega
  have hgtr : ∀ j, 0 < j → LinearMap.trace k W (g ^ j) = 0 := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e1 : g ^ (i + 1) = (f.rangeRestrict ∘ₗ (f ^ i)) ∘ₗ W.subtype := by
      ext w
      rw [hgpow, pow_succ', Module.End.mul_apply]
      rfl
    have e2 : f ^ (i + 1) = W.subtype ∘ₗ (f.rangeRestrict ∘ₗ (f ^ i)) := by
      ext x
      rw [pow_succ']
      rfl
    rw [e1, ← LinearMap.trace_comp_comm', ← e2]
    exact hf _ hj
  obtain ⟨m, hm⟩ := ih _ hW rfl g hgtr
  refine ⟨m + 1, ?_⟩
  ext x
  rw [pow_succ, Module.End.mul_apply, ← show (((g ^ m) ⟨f x, LinearMap.mem_range_self f x⟩ : W) : V)
    = (f ^ m) (f x) from hgpow m _, hm]
  rfl

/-! ## The action of `R` on a module, as `k`-linear maps -/

section Act

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

/-- `r : R` acting on `M`, as a `k`-linear endomorphism. -/
abbrev act (M : Type*) [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    (r : R) : M →ₗ[k] M :=
  DistribSMul.toLinearMap k M r

variable {M P A B : Type*} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [AddCommGroup P] [Module k P] [Module R P] [IsScalarTower k R P]
  [AddCommGroup A] [Module k A] [Module R A] [IsScalarTower k R A]
  [AddCommGroup B] [Module k B] [Module R B] [IsScalarTower k R B]

theorem act_pow (r : R) (j : ℕ) : act (k := k) M (r ^ j) = (act M r) ^ j := by
  induction j with
  | zero => ext x; rw [pow_zero, pow_zero, Module.End.one_apply]; exact one_smul R x
  | succ j ih =>
    ext x
    rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih]
    exact mul_smul (r ^ j) r x

theorem trace_act_equiv [FiniteDimensional k M] [FiniteDimensional k P] (e : M ≃ₗ[R] P) (r : R) :
    LinearMap.trace k M (act M r) = LinearMap.trace k P (act P r) := by
  rw [← LinearMap.trace_conj' (act M r) (e.restrictScalars k)]
  congr 1
  ext x
  change e (r • e.symm x) = r • x
  rw [map_smul, e.apply_symm_apply]

theorem trace_act_prod [FiniteDimensional k A] [FiniteDimensional k B] (r : R) :
    LinearMap.trace k (A × B) (act (A × B) r) =
      LinearMap.trace k A (act A r) + LinearMap.trace k B (act B r) := by
  rw [← LinearMap.trace_prodMap']
  rfl

end Act

/-! ## Step 2. A simple constituent of `M` embeds in `N` -/

section Main

variable {k R : Type*} [Field k] [CharZero k] [Ring R] [Algebra k R]

omit [CharZero k] in
theorem fd_sub {M : Type*} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    [FiniteDimensional k M] (S : Submodule R M) : FiniteDimensional k S :=
  Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective

theorem exists_injective_of_trace_eq {M N : Type*}
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [FiniteDimensional k N]
    [IsSemisimpleModule R N]
    (htr : ∀ r : R, LinearMap.trace k M (act M r) = LinearMap.trace k N (act N r))
    (S : Submodule R M) [IsSimpleModule R S] : ∃ j : S →ₗ[R] N, Function.Injective j := by
  classical
  -- the annihilator of `N` acts nilpotently on `M`
  have hnil : ∀ r : R, (∀ n : N, r • n = 0) → IsNilpotent (act (k := k) M r) := by
    intro r hr
    refine isNilpotent_of_trace_pow_eq_zero _ rfl _ fun j hj => ?_
    rw [← act_pow, htr, act_pow]
    have : act (k := k) N r = 0 := LinearMap.ext hr
    rw [this, zero_pow hj.ne', map_zero]
  -- the left ideal `ann N`
  let Jl : Submodule R R :=
    { carrier := {t | ∀ n : N, t • n = 0}
      add_mem' := fun {a b} ha hb n => by rw [add_smul, ha n, hb n, add_zero]
      zero_mem' := fun n => zero_smul R n
      smul_mem' := fun c t ht n => by
        change (c * t) • n = 0
        rw [mul_smul, ht n, smul_zero] }
  -- it kills `S`
  have hkill : ∀ r : R, (∀ n : N, r • n = 0) → ∀ s ∈ S, r • s = 0 := by
    intro r hr s hs
    by_contra hne
    let Jm : Submodule R M := Jl.map (LinearMap.toSpanSingleton R M s)
    have hle : Jm ≤ S := by
      rintro _ ⟨t, -, rfl⟩
      exact S.smul_mem t hs
    have hne' : Jm ≠ ⊥ := by
      intro h
      apply hne
      have : r • s ∈ Jm := ⟨r, hr, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot R).1 this
    have hatom : IsAtom S := isSimpleModule_iff_isAtom.1 ‹_›
    have hJS : Jm = S := ((hatom.le_iff).1 hle).resolve_left hne'
    have hsJ : s ∈ Jm := hJS ▸ hs
    obtain ⟨t, ht, hts⟩ := hsJ
    change t • s = s at hts
    obtain ⟨m, hm⟩ := hnil t ht
    have hpow : ∀ i, ((act (k := k) M t) ^ i) s = s := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Module.End.mul_apply, ih]; exact hts
    have := hpow m
    rw [hm, LinearMap.zero_apply] at this
    exact hne (by rw [← this, smul_zero])
  -- `S` is a quotient of `R / ann N ⊆ N^d`
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  let b := Module.finBasis k N
  let L : R →ₗ[R] (Fin (finrank k N) → N) :=
    LinearMap.pi fun i => LinearMap.toSpanSingleton R N (b i)
  have hker : ∀ t, L t = 0 → ∀ n : N, t • n = 0 := by
    intro t ht n
    have hti : ∀ i, t • b i = 0 := fun i => congrFun ht i
    rw [← b.sum_repr n, Finset.smul_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_comm, hti i, smul_zero]
  let ψ0 : R →ₗ[R] S := LinearMap.toSpanSingleton R S s
  have hle : LinearMap.ker L ≤ LinearMap.ker ψ0 := by
    intro t ht
    rw [LinearMap.mem_ker] at ht ⊢
    exact Subtype.ext (hkill t (hker t ht) s s.2)
  let φ := (LinearMap.ker L).liftQ ψ0 hle
  let e := L.quotKerEquivRange
  let ψ : LinearMap.range L →ₗ[R] S := φ ∘ₗ e.symm.toLinearMap
  have hψ : ψ ≠ 0 := by
    intro h
    apply hs
    have h1 : ψ (e (Submodule.Quotient.mk 1)) = s := by
      simp [ψ, φ, ψ0]
    rw [← h1, h, LinearMap.zero_apply]
  obtain ⟨T, ⟨eT⟩⟩ := LinearMap.linearEquiv_of_ne_zero hψ
  let g : S →ₗ[R] (Fin (finrank k N) → N) :=
    (LinearMap.range L).subtype ∘ₗ T.subtype ∘ₗ eT.toLinearMap
  have hg : Function.Injective g :=
    Subtype.val_injective.comp (Subtype.val_injective.comp eT.injective)
  have hg0 : g ≠ 0 := by
    intro h
    apply hs
    apply hg
    rw [h, map_zero, LinearMap.zero_apply]
  obtain ⟨i, hi⟩ : ∃ i, LinearMap.proj i ∘ₗ g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hg0
    ext x i
    exact congrArg (fun F => F x) (hcon i)
  exact ⟨_, LinearMap.injective_of_ne_zero hi⟩

/-! ## Step 3. Brauer–Nesbitt for modules over a `k`-algebra -/

theorem brauerNesbitt_module : ∀ (n : ℕ) (M N : Type*)
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [FiniteDimensional k N],
    finrank k M = n → IsSemisimpleModule R M → IsSemisimpleModule R N →
    (∀ r : R, LinearMap.trace k M (act M r) = LinearMap.trace k N (act N r)) →
    Nonempty (M ≃ₗ[R] N) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M N _ _ _ _ _ _ _ _ _ _ hn hM hN htr
  rcases subsingleton_or_nontrivial M with hMs | hMn
  · have h1 := htr 1
    have e1 : act (k := k) M (1 : R) = LinearMap.id := LinearMap.ext fun x => one_smul R x
    have e2 : act (k := k) N (1 : R) = LinearMap.id := LinearMap.ext fun x => one_smul R x
    rw [e1, e2, ← Module.End.one_eq_id, ← Module.End.one_eq_id, LinearMap.trace_one,
      LinearMap.trace_one, Module.finrank_zero_of_subsingleton, Nat.cast_zero, eq_comm,
      Nat.cast_eq_zero, Module.finrank_zero_iff] at h1
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule R M
  obtain ⟨j, hj⟩ := exists_injective_of_trace_eq htr S
  obtain ⟨M', hM'⟩ := exists_isCompl S
  obtain ⟨N', hN'⟩ := exists_isCompl (LinearMap.range j)
  have := fd_sub (k := k) S
  have := fd_sub (k := k) M'
  have := fd_sub (k := k) (LinearMap.range j)
  have := fd_sub (k := k) N'
  let eM := Submodule.prodEquivOfIsCompl S M' hM'
  let eN := Submodule.prodEquivOfIsCompl _ N' hN'
  let eS : S ≃ₗ[R] LinearMap.range j := LinearEquiv.ofInjective j hj
  have htr' : ∀ r : R, LinearMap.trace k M' (act M' r) = LinearMap.trace k N' (act N' r) := by
    intro r
    have h1 := htr r
    rw [← trace_act_equiv eM, ← trace_act_equiv eN, trace_act_prod, trace_act_prod,
      trace_act_equiv eS] at h1
    exact add_left_cancel h1
  have hdim : finrank k M' < n := by
    have h1 := (eM.restrictScalars k).finrank_eq
    rw [Module.finrank_prod] at h1
    have : Nontrivial S := IsSimpleModule.nontrivial R S
    have h2 : 0 < finrank k S := Module.finrank_pos
    omega
  obtain ⟨e'⟩ := ih _ hdim M' N' rfl inferInstance inferInstance htr'
  exact ⟨eM.symm.trans ((eS.prodCongr e').trans eN)⟩

end Main

/-! ## The leaf -/

theorem brauerNesbittChar0 : BrauerNesbittChar0 := by
  intro k G V W _ _ _ _ _ _ _ _ _ ρ σ hρ hσ htr
  refine brauerNesbitt_module (k := k) (R := MonoidAlgebra k G) _ ρ.asModule σ.asModule rfl hρ hσ ?_
  intro r
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    have e1 : ∀ (U : Type) [AddCommGroup U] [Module k U] [FiniteDimensional k U]
        (τ : Representation k G U),
        LinearMap.trace k τ.asModule (act τ.asModule (MonoidAlgebra.of k G g)) =
          LinearMap.trace k U (τ g) := by
      intro U _ _ _ τ
      rw [← LinearMap.trace_conj' _ τ.asModuleEquiv]
      congr 1
      ext x
      simp [LinearEquiv.conj_apply]
      rfl
    rw [e1, e1]
    exact htr g
  | add f g hf hg =>
    rw [show act (k := k) ρ.asModule (f + g) = act ρ.asModule f + act ρ.asModule g from
      LinearMap.ext fun x => add_smul f g x,
      show act (k := k) σ.asModule (f + g) = act σ.asModule f + act σ.asModule g from
      LinearMap.ext fun x => add_smul f g x, map_add, map_add, hf, hg]
  | smul c f hf =>
    rw [show act (k := k) ρ.asModule (c • f) = c • act ρ.asModule f from
      LinearMap.ext fun x => smul_assoc c f x,
      show act (k := k) σ.asModule (c • f) = c • act σ.asModule f from
      LinearMap.ext fun x => smul_assoc c f x, map_smul, map_smul, hf]


/-! ## The matrix form `HSyn.BrauerNesbitt` -/

/-- **L19. Brauer–Nesbitt.** Verbatim `HSyn.BrauerNesbitt`. -/
def HSynBrauerNesbitt : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

section Matrix

variable {G E : Type} [Group G] [Field E] {n : ℕ}

/-- The representation of `G` on `E^n` given by a homomorphism to `GL_n(E)`. -/
noncomputable def repOfGL (ρ : G →* GL (Fin n) E) : Representation E G (Fin n → E) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) E ≃ₐ[E] Module.End E (Fin n → E)).toAlgHom
    |>.toMonoidHom.comp ((Units.coeHom _).comp ρ)

theorem repOfGL_apply (ρ : G →* GL (Fin n) E) (g : G) :
    repOfGL ρ g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E) := rfl

theorem isSemisimpleModule_repOfGL (ρ : G →* GL (Fin n) E)
    (h : ∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ W') :
    IsSemisimpleModule (MonoidAlgebra E G) (repOfGL ρ).asModule := by
  rw [isSemisimpleModule_iff]
  refine (OrderIso.complementedLattice_iff (repOfGL ρ).mapSubmodule).1 ⟨fun ⟨p, hp⟩ => ?_⟩
  have hp' : ∀ g, p.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ p := fun g =>
    (Module.End.mem_invtSubmodule_iff_map_le _).1 ((repOfGL ρ).mem_invtSubmodule.1 hp g)
  obtain ⟨W', hc, hW'⟩ := h p hp'
  have hW'mem : W' ∈ (repOfGL ρ).invtSubmodule :=
    (repOfGL ρ).mem_invtSubmodule.2 fun g => (Module.End.mem_invtSubmodule_iff_map_le _).2 (hW' g)
  refine ⟨⟨W', hW'mem⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    apply Subtype.ext
    exact hc.inf_eq_bot
  · rw [codisjoint_iff]
    apply Subtype.ext
    exact hc.sup_eq_top

end Matrix

theorem hsynBrauerNesbitt : HSynBrauerNesbitt := by
  intro G _ E _ _ n ρ₁ ρ₂ h₁ h₂ htr
  obtain ⟨φ⟩ := brauerNesbittChar0 E G (Fin n → E) (Fin n → E) (repOfGL ρ₁) (repOfGL ρ₂)
    (isSemisimpleModule_repOfGL ρ₁ h₁) (isSemisimpleModule_repOfGL ρ₂ h₂)
    (fun g => by rw [repOfGL_apply, repOfGL_apply, Matrix.trace_toLin'_eq,
      Matrix.trace_toLin'_eq, htr g])
  let f : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
    ((repOfGL ρ₁).asModuleEquiv.symm.trans (φ.restrictScalars E)).trans
      (repOfGL ρ₂).asModuleEquiv
  have hf : ∀ g x, f (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E) x) =
      Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E) (f x) := by
    intro g x
    rw [← repOfGL_apply, ← repOfGL_apply]
    simp only [f, LinearEquiv.trans_apply, Representation.asModuleEquiv_symm_map_rho,
      LinearEquiv.restrictScalars_apply, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  let P : GL (Fin n) E :=
    ⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨P, fun g => Units.ext ?_⟩
  change (ρ₂ g : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' f.toLinearMap *
    (ρ₁ g : Matrix (Fin n) (Fin n) E) * LinearMap.toMatrix' f.symm.toLinearMap
  rw [← LinearMap.toMatrix'_toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E), ← LinearMap.toMatrix'_comp,
    ← LinearMap.toMatrix'_comp]
  conv_lhs => rw [← LinearMap.toMatrix'_toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hf, LinearEquiv.apply_symm_apply]

end TSkolemKW


-- ===== FrobeniusDense.lean =====

/-!
# t-skolem-kw: leaf T18 (Frobenius density) reduced to its finite form

`HSyn.FrobeniusDense` (verbatim below as `HS.FrobeniusDense`, over `HSyn`'s `Qbar`, `GQ`,
`LiesOver`, `IsArithFrob`, also verbatim) is proved from `PkgI6.ChebotarevExists`
(= `GlueC10.ChebotarevExists`, verbatim).  So T18 rests on the finite (existence) form of
Chebotarev's theorem alone.

Part C10 is copied verbatim from `scratch/h-decomposition/Leaves.lean`, section `GlueC10Sec`
(lines 11328-11333, 11375-11630, 11747-11750 at base 01267822): the lift of a finite-level
Frobenius to `G_ℚ` at a prime of `\bar ℤ`.  New here (`HS` section): the localization of `\bar ℤ`
at a prime `𝔓` is a valuation subring of `\bar ℚ` (`zbarLoc`, via the DVR `(𝓞_E)_{𝔓 ∩ 𝓞_E}` of
each finite layer), an arithmetic Frobenius at `𝔓` is an `IsArithFrob` at this place, and the
Krull-topology step.
-/

open NumberField

namespace TSkolemKW.C10

/-- **Leaf I6.4 (Chebotarev, existence form)** — verbatim from pkg-I6. -/
def ChebotarevExists : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q


/-! ## Part B. The absolute Galois group `G_ℚ` -/

/-- `\bar ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(\bar ℚ/ℚ)` with the Krull topology.  Definitionally Mathlib's
`GQ` (which is a non-reducible `def` of the same type). -/
abbrev GQ : Type := Qbar ≃ₐ[ℚ] Qbar

example : GQ = Field.absoluteGaloisGroup ℚ := rfl

/-- `\bar ℤ`, the integral closure of `ℤ` in `\bar ℚ`. -/
abbrev Zbar : Type := integralClosure ℤ Qbar

/-- `g ∈ G_ℚ` is an arithmetic Frobenius at the rational prime `p`: there is a prime `𝔓` of
`\bar ℤ` over `p` with `g x ≡ x^p (mod 𝔓)` for every `x ∈ \bar ℤ`. -/
def IsFrobAt (g : GQ) (p : ℕ) : Prop :=
  ∃ P : Ideal Zbar, P.IsPrime ∧ P.under ℤ = Ideal.span {(p : ℤ)} ∧
    ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P

/-- **Frobenius density (GLUE).** For every finite subextension `E/ℚ` of `\bar ℚ` and every
`g ∈ G_ℚ` there is a Frobenius `h` at a prime `p ∉ S` with `h = g` on `E`.  By
`krullTopology_mem_nhds_one_iff` this says that Frobenius elements at primes outside `S` are
dense in `G_ℚ`. -/
def FrobDense (S : Finset ℕ) : Prop :=
  ∀ (E : IntermediateField ℚ Qbar), FiniteDimensional ℚ E → ∀ g : GQ,
    ∃ h : GQ, ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ IsFrobAt h p ∧
      ∀ x ∈ E, h x = g x

/-- **The lift of a finite-level Frobenius to `G_ℚ` (GLUE, proved below: `frobLift`).**  For a finite
Galois `E ⊂ \bar ℚ` and `τ ∈ Gal(E/ℚ)` that is the Frobenius at a prime `Q` of `𝓞_E` over `p`
unramified in `E`, some `h ∈ G_ℚ` restricting to `τ` is a Frobenius at `p` in `G_ℚ`.
Proof sketch: choose `𝔓 | Q` in `\bar ℤ`; an arithmetic Frobenius `h ∈ D_𝔓` exists by
compactness of `G_ℚ` and `exists_isArithFrobAt` in every finite Galois layer; `h|_E` is a
Frobenius at `Q`, and Frobenius at an unramified prime is unique
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`). -/
def FrobLift : Prop :=
  ∀ (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E] [IsGalois ℚ E]
    (τ : E ≃ₐ[ℚ] E) (p : ℕ) (Q : Ideal (𝓞 E)) [Q.IsPrime], p.Prime →
    Q.under ℤ = Ideal.span {(p : ℤ)} → Algebra.IsUnramifiedAt ℤ Q → IsArithFrobAt ℤ τ Q →
      ∃ h : GQ, IsFrobAt h p ∧ AlgEquiv.restrictNormal h E = τ

/-! ### Proof of `FrobLift` (merged from `Lift.lean`) -/

/-- `𝓞_E → \bar ℤ`. -/
noncomputable def toZbar (E : IntermediateField ℚ Qbar) : 𝓞 E →+* Zbar :=
  RingHom.codRestrict ((algebraMap E Qbar).comp (algebraMap (𝓞 E) E)) (integralClosure ℤ Qbar)
    (fun x => (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E Qbar))

@[simp] lemma toZbar_coe (E : IntermediateField ℚ Qbar) (x : 𝓞 E) :
    ((toZbar E x : Zbar) : Qbar) = ((x : E) : Qbar) := rfl

lemma card_quot (p : ℕ) [Fact p.Prime] : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- **Step (c) of `FrobLift` (GLUE, proved).** -/
theorem restrictNormal_eq_of_frob (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E]
    [IsGalois ℚ E] (τ : E ≃ₐ[ℚ] E) (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) [Algebra.IsUnramifiedAt ℤ Q]
    (hτ : IsArithFrobAt ℤ τ Q) (h : GQ) (P : Ideal Zbar) (hPQ : P.comap (toZbar E) = Q)
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    AlgEquiv.restrictNormal h E = τ := by
  have : NumberField E := ⟨⟩
  set σ := AlgEquiv.restrictNormal h E
  have hσ : IsArithFrobAt ℤ σ Q := by
    intro x
    rw [hQp, card_quot, ← hPQ, Ideal.mem_comap]
    apply hh (toZbar E x)
    rw [map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
      toZbar_coe]
    congr 1
    exact AlgEquiv.restrictNormal_commutes h E (x : E)
  have hQ : Q.primeCompl ≤ nonZeroDivisors (𝓞 E) := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    exact hx Q.zero_mem
  have heq := hσ.eq_of_isUnramifiedAt hτ hQ
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have ha := congrArg (fun f => ((f a : 𝓞 E) : E)) heq
  have hb := congrArg (fun f => ((f b : 𝓞 E) : E)) heq
  simp only [MulSemiringAction.toAlgHom_apply] at ha hb
  have key : ∀ (g : E ≃ₐ[ℚ] E) (c : 𝓞 E), g (algebraMap (𝓞 E) E c) = ((g • c : 𝓞 E) : E) :=
    fun g c => rfl
  have e1 := (key σ a).trans (ha.trans (key τ a).symm)
  have e2 := (key σ b).trans (hb.trans (key τ b).symm)
  rw [map_div₀, map_div₀, e1, e2]

/-- **Step (b) of `FrobLift` (GLUE).** Every prime `𝔓` of `\bar ℤ` over a rational prime
`p` has an arithmetic Frobenius in `G_ℚ`.  (Compactness of `G_ℚ` and Mathlib's
`exists_isArithFrobAt` in each finite Galois layer.) -/
def FrobExistsAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∃ h : GQ, ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P


lemma toZbar_injective (E : IntermediateField ℚ Qbar) : Function.Injective (toZbar E) := by
  intro x y hxy
  have := congrArg (fun z : Zbar => (z : Qbar)) hxy
  simp only [toZbar_coe] at this
  exact RingOfIntegers.ext (Subtype.ext this)

/-- **`FrobLift` from step (b) (GLUE, proved): lying-over plus step (c).** -/
theorem frobLift_of_frobExistsAt (hb : FrobExistsAt) : FrobLift := by
  intro E _ _ τ p Q _ hp hQp hQu hτ
  have : Fact p.Prime := ⟨hp⟩
  let _ : Algebra (𝓞 E) Zbar := (toZbar E).toAlgebra
  have : Algebra.IsIntegral (𝓞 E) Zbar := Algebra.IsIntegral.tower_top ℤ
  obtain ⟨P, -, hP, hPQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal Zbar)
    (by
      intro x hx
      have : toZbar E x = 0 := hx
      rw [toZbar_injective E (this.trans (map_zero _).symm)]
      exact Q.zero_mem)
  have hPQ' : P.comap (toZbar E) = Q := hPQ
  have hPp : P.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hQp, Ideal.under, Ideal.under, ← hPQ', Ideal.comap_comap]
    congr 1
  obtain ⟨h, hh⟩ := hb p P hPp
  exact ⟨h, ⟨P, hP, hPp, hh⟩, restrictNormal_eq_of_frob E τ p Q hQp hτ h P hPQ' hh⟩

/-- The Frobenius condition at `𝔓` on the elements of `\bar ℤ` lying in `F`. -/
def FrobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar) : Set GQ :=
  {h | ∀ x y : Zbar, (x : Qbar) ∈ F → (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P}

/-- **Step (b), finite layer (GLUE, proved: `frobExistsFinite`; a consequence of Mathlib's
`IsArithFrobAt.exists_of_isInvariant` for `Gal(F/ℚ)` acting on `𝓞_F`, and the surjectivity
`G_ℚ → Gal(F/ℚ)`).** -/
def FrobExistsFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∀ (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [IsGalois ℚ F],
      (FrobOn p P F).Nonempty

lemma frobOn_anti {p : ℕ} {P : Ideal Zbar} {F F' : IntermediateField ℚ Qbar} (hF : F ≤ F') :
    FrobOn p P F' ⊆ FrobOn p P F :=
  fun _ hh x y hx hy => hh x y (hF hx) hy

lemma isClosed_frobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ F] : IsClosed (FrobOn p P F) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro h hh
  simp only [FrobOn, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hh
  obtain ⟨x, y, hx, hy, hyP⟩ := hh
  refine ⟨(fun k => h⁻¹ * k) ⁻¹' (F.fixingSubgroup : Set GQ), ?_, ?_, ?_⟩
  · intro k hk hk'
    have hfix := (IntermediateField.mem_fixingSubgroup_iff F _).mp hk (x : Qbar) hx
    change h⁻¹ (k (x : Qbar)) = (x : Qbar) at hfix
    have hkx : k (x : Qbar) = h (x : Qbar) := by
      have e := congrArg h hfix
      rwa [show h (h⁻¹ (k (x : Qbar))) = k (x : Qbar) from AlgEquiv.apply_symm_apply h _] at e
    exact hyP (hk' x y hx (by rw [hy, hkx]))
  · exact (IntermediateField.fixingSubgroup_isOpen F).preimage (continuous_const.mul continuous_id)
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact one_mem _

instance : IsGalois ℚ Qbar := ⟨⟩

/-- **Step (b) from its finite layer (GLUE, proved): compactness of `G_ℚ`.** -/
theorem frobExistsAt_of_finite (hf : FrobExistsFinite) : FrobExistsAt := by
  intro p _ P _ hP
  let ι := {F : IntermediateField ℚ Qbar // FiniteDimensional ℚ F}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  let t : ι → Set GQ := fun F => FrobOn p P F.1
  have htd : Directed (· ⊇ ·) t := by
    rintro ⟨F₁, h₁⟩ ⟨F₂, h₂⟩
    refine ⟨⟨F₁ ⊔ F₂, inferInstance⟩, frobOn_anti le_sup_left, frobOn_anti le_sup_right⟩
  have htn : ∀ F, (t F).Nonempty := by
    rintro ⟨F, hF⟩
    let N := IntermediateField.normalClosure ℚ F Qbar
    have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ F Qbar
    have : Normal ℚ N := normalClosure.normal ℚ F Qbar
    have : IsGalois ℚ N := ⟨⟩
    exact (hf p P hP N).mono (frobOn_anti F.le_normalClosure)
  have htcl : ∀ F, IsClosed (t F) := fun F => by
    have := F.2
    exact isClosed_frobOn p P F.1
  obtain ⟨h, hh⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun F => (htcl F).isCompact) htcl
  refine ⟨h, fun x y hy => ?_⟩
  have hxi : IsIntegral ℚ (x : Qbar) := Algebra.IsIntegral.isIntegral _
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(x : Qbar)}) :=
    IntermediateField.adjoin.finiteDimensional hxi
  exact Set.mem_iInter.mp hh ⟨IntermediateField.adjoin ℚ {(x : Qbar)}, this⟩ x y
    (IntermediateField.mem_adjoin_simple_self ℚ _) hy

/-- **Step (b), finite layer (GLUE, proved from Mathlib).** -/
theorem frobExistsFinite : FrobExistsFinite := by
  intro p _ P _ hP F _ _
  have : NumberField F := ⟨⟩
  set QF := P.comap (toZbar F) with hQF
  have hQFp : QF.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hP, Ideal.under, Ideal.under, hQF, Ideal.comap_comap]
    congr 1
  have hQFprime : QF.IsPrime := Ideal.comap_isPrime _ _
  have hQFne : QF ≠ ⊥ := by
    intro h0
    have hp : ((p : ℤ) : 𝓞 F) ∈ QF := by
      change algebraMap ℤ (𝓞 F) (p : ℤ) ∈ QF
      rw [← Ideal.mem_comap]
      change (p : ℤ) ∈ QF.under ℤ
      rw [hQFp]
      exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.mem_bot] at hp
    have : ((p : ℤ) : 𝓞 F) ≠ 0 := by
      have := (Fact.out : p.Prime).ne_zero
      exact_mod_cast this
    exact this hp
  have : QF.IsMaximal := hQFprime.isMaximal hQFne
  let _ := IsIntegralClosure.MulSemiringAction ℤ ℚ F (𝓞 F)
  have := Algebra.isInvariant_of_isGalois ℤ ℚ F (𝓞 F)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (F ≃ₐ[ℚ] F) QF
  obtain ⟨h, hres⟩ : ∃ h : GQ, AlgEquiv.restrictNormal h F = σ :=
    ⟨σ.liftNormal Qbar, σ.restrict_liftNormal Qbar⟩
  subst hres
  refine ⟨h, fun x y hx hy => ?_⟩
  have hxi : IsIntegral ℤ (⟨(x : Qbar), hx⟩ : F) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F Qbar) (algebraMap F Qbar).injective]
    exact x.2
  let x' : 𝓞 F := ⟨⟨(x : Qbar), hx⟩, hxi⟩
  have hmem := hσ x'
  rw [hQFp, card_quot, hQF, Ideal.mem_comap] at hmem
  convert hmem using 1
  apply Subtype.ext
  rw [hy, map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
    toZbar_coe]
  congr 1
  change h (x : Qbar) = ((algebraMap (𝓞 F) F (galRestrict ℤ ℚ F (𝓞 F) _ x')) : Qbar)
  rw [algebraMap_galRestrict_apply]
  exact (AlgEquiv.restrictNormal_commutes h F (algebraMap (𝓞 F) F x')).symm

/-- **`FrobLift` holds (GLUE, proved from Mathlib).** -/
theorem frobLift : FrobLift :=
  frobLift_of_frobExistsAt (frobExistsAt_of_finite frobExistsFinite)


/-- **Frobenius density from Chebotarev (GLUE, proved from I6.4 and `FrobLift`).** -/
theorem frobDense_of_chebotarev (hC : ChebotarevExists) (hL : FrobLift) (S : Finset ℕ) :
    FrobDense S := by
  intro E hE g
  set N := IntermediateField.normalClosure ℚ E Qbar
  have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ E Qbar
  have : Normal ℚ N := normalClosure.normal ℚ E Qbar
  have : IsGalois ℚ N := ⟨⟩
  have : NumberField N := ⟨⟩
  obtain ⟨p, hp, hpS, Q, hQ, hQp, hQu, hQf⟩ := hC N S (AlgEquiv.restrictNormal g N)
  obtain ⟨h, hh, hres⟩ := hL N _ p Q hp hQp hQu hQf
  refine ⟨h, p, hp, hpS, hh, fun x hx => ?_⟩
  have hxN : x ∈ N := E.le_normalClosure hx
  have e1 := AlgEquiv.restrictNormal_commutes h N ⟨x, hxN⟩
  have e2 := AlgEquiv.restrictNormal_commutes g N ⟨x, hxN⟩
  rw [hres] at e1
  simpa using e1.symm.trans e2


/-- Frobenius elements at primes outside `S` are dense in `G_ℚ` (from Chebotarev alone). -/
theorem frobDense (hC : ChebotarevExists) (S : Finset ℕ) : FrobDense S :=
  frobDense_of_chebotarev hC frobLift S


end TSkolemKW.C10

/-! ## `HSyn.FrobeniusDense` from the finite form -/

namespace TSkolemKW.HS

open scoped Pointwise
open TSkolemKW.C10 (ChebotarevExists FrobDense IsFrobAt Zbar toZbar toZbar_coe frobDense)

/-! ### Definitions (verbatim from `HSyn` §0-§1 of `scratch/h-decomposition/Leaves.lean`) -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- **L18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-! ### The localization of `\bar ℤ` at a prime is a valuation subring of `\bar ℚ` -/

variable (P : Ideal Zbar) [hP : P.IsPrime]

/-- Membership in `\bar ℤ_𝔓`. -/
def LocMem (x : Qbar) : Prop := ∃ a s : Zbar, s ∉ P ∧ x * (s : Qbar) = a

theorem one_notMem : (1 : Zbar) ∉ P := (Ideal.ne_top_iff_one P).1 hP.ne_top

omit hP in
theorem natCast_mem (p : ℕ) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) : (p : Zbar) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ Zbar (p : ℤ) ∈ P := h1
  simpa using h2

omit hP in
/-- In a number field `K`, for a nonzero prime `Q` of `𝓞_K`, every `x ∈ K` or its inverse is a
fraction `r / s` with `s ∉ Q` (the localization `(𝓞_K)_Q` is a DVR, hence a valuation ring). -/
theorem exists_frac_or_inv (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hQ0 : Q ≠ ⊥) (x : K) (hx0 : x ≠ 0) :
    ∃ r s : 𝓞 K, s ∉ Q ∧ (x * (s : K) = r ∨ x⁻¹ * (s : K) = r) := by
  let Aₘ := Localization.AtPrime Q
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hQ0 Aₘ
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : (b : K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have ha0 : (a : K) ≠ 0 := by
    intro h
    apply hx0
    rw [← hab]
    change (a : K) / (b : K) = 0
    rw [h, zero_div]
  obtain ⟨c, hc⟩ := PreValuationRing.cond (algebraMap (𝓞 K) Aₘ a) (algebraMap (𝓞 K) Aₘ b)
  obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl c
  have hinj := IsLocalization.injective Aₘ Q.primeCompl_le_nonZeroDivisors
  refine ⟨r, s, hs, ?_⟩
  rcases hc with hc | hc
  · right
    have e : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc]
      congr 1
      exact (IsLocalization.mk'_spec Aₘ r ⟨s, hs⟩).symm
    have eE : (a : K) * (r : K) = (b : K) * (s : K) := by
      exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) e
    rw [← hab]
    change ((a : K) / (b : K))⁻¹ * (s : K) = (r : K)
    field_simp
    linear_combination eE.symm
  · left
    have e : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc]
      congr 1
      exact (IsLocalization.mk'_spec Aₘ r ⟨s, hs⟩).symm
    have eE : (b : K) * (r : K) = (a : K) * (s : K) := by
      exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) e
    rw [← hab]
    change (a : K) / (b : K) * (s : K) = (r : K)
    field_simp
    linear_combination eE.symm

/-- Every `x ∈ \bar ℚ` or its inverse lies in `\bar ℤ_𝔓`: pass to the DVR `(𝓞_E)_{𝔓 ∩ 𝓞_E}`
for `E = ℚ(x)`. -/
theorem locMem_or_inv (p : ℕ) (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (x : Qbar) : LocMem P x ∨ LocMem P x⁻¹ := by
  by_cases hx0 : x = 0
  · left
    exact ⟨0, 1, one_notMem P, by simp [hx0]⟩
  have hxi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
  let E := IntermediateField.adjoin ℚ ({x} : Set Qbar)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxi
  have : NumberField E := ⟨⟩
  let Q := P.comap (toZbar E)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hpQ : ((p : ℤ) : 𝓞 E) ∈ Q := by
    change toZbar E ((p : ℤ) : 𝓞 E) ∈ P
    simpa using natCast_mem P p hPp
  have hQ0 : Q ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpQ
    exact (by exact_mod_cast hp.ne_zero : ((p : ℤ) : 𝓞 E) ≠ 0) hpQ
  let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨r, s, hs, h | h⟩ := exists_frac_or_inv E Q hQ0 x' hx'0
  · left
    refine ⟨toZbar E r, toZbar E s, hs, ?_⟩
    rw [toZbar_coe, toZbar_coe]
    have := congrArg (fun z : E => (z : Qbar)) h
    simpa using this
  · right
    refine ⟨toZbar E r, toZbar E s, hs, ?_⟩
    rw [toZbar_coe, toZbar_coe]
    have := congrArg (fun z : E => (z : Qbar)) h
    simpa using this

/-- `\bar ℤ_𝔓` as a valuation subring of `\bar ℚ`. -/
def zbarLoc (p : ℕ) (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) :
    ValuationSubring Qbar where
  carrier := {x | LocMem P x}
  mul_mem' := by
    rintro x y ⟨a, s, hs, ha⟩ ⟨b, t, ht, hb⟩
    refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    linear_combination (y * (t : Qbar)) * ha + (a : Qbar) * hb
  one_mem' := ⟨1, 1, one_notMem P, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, ha⟩ ⟨b, t, ht, hb⟩
    refine ⟨a * t + b * s, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    linear_combination (t : Qbar) * ha + (s : Qbar) * hb
  zero_mem' := ⟨0, 1, one_notMem P, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, ha⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast
    linear_combination -ha
  mem_or_inv_mem' := locMem_or_inv P p hp hPp

theorem mem_zbarLoc {p : ℕ} {hp : p.Prime} {hPp : P.under ℤ = Ideal.span {(p : ℤ)}} {x : Qbar} :
    x ∈ zbarLoc P p hp hPp ↔ LocMem P x := Iff.rfl

/-! ### An arithmetic Frobenius at `𝔓` is an `IsArithFrob` at `\bar ℤ_𝔓` -/

/-- `g ∈ G_ℚ` maps `\bar ℤ` to itself. -/
def gZ (g : GQ) (z : Zbar) : Zbar :=
  ⟨g z, (z.2 : IsIntegral ℤ (z : Qbar)).map ((g : Qbar →ₐ[ℚ] Qbar).restrictScalars ℤ)⟩

@[simp] theorem gZ_coe (g : GQ) (z : Zbar) : ((gZ g z : Zbar) : Qbar) = g z := rfl

theorem liesOver_and_isArithFrob (h : GQ) (p : ℕ) (hp : p.Prime)
    (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    LiesOver (zbarLoc P p hp hPp) p ∧ IsArithFrob h (zbarLoc P p hp hPp) p := by
  have hcong : ∀ z : Zbar, gZ h z - z ^ p ∈ P := fun z => hh z _ (by push_cast; rfl)
  have hmemP : ∀ z : Zbar, gZ h z ∈ P ↔ z ∈ P := by
    intro z
    constructor
    · intro hz
      have : z ^ p ∈ P := by
        have := P.sub_mem hz (hcong z)
        rwa [sub_sub_cancel] at this
      exact hP.mem_of_pow_mem p this
    · intro hz
      have := P.add_mem (hcong z) (P.pow_mem_of_mem hz p hp.pos)
      rwa [sub_add_cancel] at this
  have hpP := natCast_mem P p hPp
  refine ⟨?_, ?_, ?_⟩
  · -- `p` is a nonunit
    rw [LiesOver, ValuationSubring.mem_nonunits_iff_or]
    right
    rintro ⟨a, s, hs, ha⟩
    apply hs
    have : s = (p : Zbar) * a := by
      apply Subtype.ext
      push_cast
      rw [← ha, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero), one_mul]
    rw [this]
    exact P.mul_mem_right _ hpP
  · -- `h` stabilizes the place
    refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    constructor
    · rintro ⟨a, s, hs, ha⟩
      refine ⟨gZ h a, gZ h s, fun h' => hs ((hmemP s).1 h'), ?_⟩
      have := congrArg h ha
      rw [map_mul] at this
      simpa [AlgEquiv.aut_inv] using this
    · rintro ⟨a, s, hs, ha⟩
      have hts : gZ h (gZ h⁻¹ s) = s := by
        apply Subtype.ext
        simp [AlgEquiv.aut_inv]
      refine ⟨gZ h⁻¹ a, gZ h⁻¹ s, fun h' => hs (hts ▸ (hmemP _).2 h'), ?_⟩
      have := congrArg (fun y => (h⁻¹ : GQ) y) ha
      simp only [map_mul] at this
      simpa using this
  · -- the Frobenius congruence on the place
    rintro x ⟨a, s, hs, ha⟩
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases hd : h x - x ^ p = 0
    · exact Or.inl hd
    right
    rintro ⟨a', s', hs', hd'⟩
    let n : Zbar := gZ h a * s ^ p - a ^ p * gZ h s
    have hn : n ∈ P := by
      have : n = (gZ h a - a ^ p) * s ^ p - a ^ p * (gZ h s - s ^ p) := by ring
      rw [this]
      exact P.sub_mem (P.mul_mem_right _ (hcong a)) (P.mul_mem_left _ (hcong s))
    have e1 : h x * h (s : Qbar) = h (a : Qbar) := by rw [← map_mul, ha]
    have e2 : x ^ p * (s : Qbar) ^ p = (a : Qbar) ^ p := by rw [← mul_pow, ha]
    have e3 : (h x - x ^ p) * (h (s : Qbar) * (s : Qbar) ^ p) = (n : Qbar) := by
      simp only [n]
      push_cast
      simp only [gZ_coe]
      linear_combination ((s : Qbar) ^ p) * e1 - (h (s : Qbar)) * e2
    have e4 : (s' : Qbar) = (h x - x ^ p) * (a' : Qbar) := by
      rw [← hd', ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    have e5 : s' * (gZ h s * s ^ p) = a' * n := by
      apply Subtype.ext
      push_cast
      simp only [gZ_coe]
      rw [e4, ← e3]
      ring
    have hmem : s' * (gZ h s * s ^ p) ∈ P := e5 ▸ P.mul_mem_left _ hn
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hs' h1
    rcases hP.mem_or_mem h1 with h2 | h2
    · exact hs ((hmemP s).1 h2)
    · exact hs (hP.mem_of_pow_mem p h2)

/-! ### The reduction -/

/-- **T18 from its finite form, via `FrobDense` (GLUE, proved).** -/
theorem frobeniusDense_of_frobDense (hD : ∀ S, FrobDense S) : FrobeniusDense := by
  intro U hU σ S
  obtain ⟨E, hE, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ Qbar (U : Set GQ)).1 (hU.mem_nhds U.one_mem)
  obtain ⟨h, p, hp, hpS, ⟨P, hP, hPp, hh⟩, hhE⟩ := hD S E hE σ
  obtain ⟨hL, hF⟩ := liesOver_and_isArithFrob P h p hp hPp hh
  refine ⟨p, hp, hpS, zbarLoc P p hp hPp, h, hL, hF, hEU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, ← hhE x hx, AlgEquiv.symm_apply_apply]

/-- **T18 (`HSyn.FrobeniusDense`) from the finite form `PkgI6.ChebotarevExists` (GLUE,
proved).** -/
theorem frobeniusDense_of_chebotarev (hC : ChebotarevExists) : FrobeniusDense :=
  frobeniusDense_of_frobDense fun S => frobDense hC S

end TSkolemKW.HS


-- ===== KroneckerWeberUse.lean =====

/-!
# t-skolem-kw: leaf T17 (Kronecker–Weber) in the form the proof uses

T17 itself (`HSyn.KroneckerWeber`, verbatim below) is NOT proved here (see
`docs/research/t-skolem-kw.md`).  This file proves the glue that turns it into the form step C8
of h-trust uses ("the fixed field of `ker ψ` is finite abelian over `ℚ`, hence cyclotomic, so `ψ`
is a Dirichlet character"; glue-assembly §2.1 listed it as "not written"):

* `ker_ge_of_kroneckerWeber`: for a homomorphism `ψ : G_ℚ → G` to a commutative group with open
  kernel, there is `m ≥ 1` such that `ψ` kills every `σ` fixing all `m`-th roots of unity;
* `eq_of_agree_on_roots`: `ψ σ` depends only on the action of `σ` on the `m`-th roots of unity,
  i.e. `ψ` factors through `Gal(ℚ(μ_m)/ℚ) ≅ (ℤ/m)ˣ`;
* `isOpen_ker_of_continuous`: a continuous homomorphism with finite image to a `T1` group has
  open kernel (the hypothesis as it arises in C8, `ψ` with values in `\bar ℚ₅^×`);
* `KroneckerWeberCyclic` (T17 for cyclic `L/ℚ`, a consequence of T17:
  `kroneckerWeberCyclic_of_kroneckerWeber`) already suffices when `ψ` takes values in a field:
  `ker_ge_of_kroneckerWeberCyclic`, `eq_of_agree_on_roots_cyclic` (`Gal(L/ℚ) ≅ im ψ ⊆ Eˣ` is
  cyclic).
-/

namespace TSkolemKW.KW

/-- `ℚ̄` (as in `HSyn`). -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology (as in `HSyn`). -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- **L17. Kronecker–Weber** (Washington, *Cyclotomic fields*, Thm 14.1; Tau Ceti
`kroneckerWeber`). Exact.  Verbatim `HSyn.KroneckerWeber`. -/
def KroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

instance : IsGalois ℚ Qbar := ⟨⟩

/-- A normal subfield `L ⊆ \bar ℚ` that embeds in `ℚ(ζ_m)` lies in the field generated by the
`m`-th roots of unity, so every `σ` fixing them fixes `L`. -/
theorem fixes_of_embeds (L : IntermediateField ℚ Qbar) [Normal ℚ L] (m : ℕ+)
    (j : L →ₐ[ℚ] CyclotomicField (m : ℕ) ℚ) (σ : GQ)
    (hσ : ∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = ζ) (x : Qbar) (hx : x ∈ L) : σ x = x := by
  -- `L` is normal, so it is the image of `ι ∘ j` for any embedding `ι` of `ℚ(ζ_m)` into `ℚ̄`
  let ι : CyclotomicField (m : ℕ) ℚ →ₐ[ℚ] Qbar := IsAlgClosed.lift
  have hrange : (ι.comp j).fieldRange = L := AlgHom.fieldRange_of_normal (ι.comp j)
  have hxr : x ∈ (ι.comp j).fieldRange := by rw [hrange]; exact hx
  obtain ⟨y, rfl⟩ := hxr
  -- `σ` fixes the subalgebra generated by the `m`-th roots of unity
  let Eq := AlgHom.equalizer (σ : Qbar →ₐ[ℚ] Qbar) (AlgHom.id ℚ Qbar)
  have hT : Algebra.adjoin ℚ {w : Qbar | w ^ (m : ℕ) = 1} ≤ Eq :=
    Algebra.adjoin_le fun w hw => hσ w hw
  have : NeZero ((m : ℕ) : ℚ) := ⟨by exact_mod_cast m.ne_zero⟩
  have := CyclotomicField.isCyclotomicExtension (m : ℕ) ℚ
  have hy : j y ∈ Algebra.adjoin ℚ
      {b : CyclotomicField (m : ℕ) ℚ | ∃ n : ℕ, n ∈ ({(m : ℕ)} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} :=
    (CyclotomicField.isCyclotomicExtension (m : ℕ) ℚ).adjoin_roots (j y)
  have hιy : ι (j y) ∈ Algebra.adjoin ℚ {w : Qbar | w ^ (m : ℕ) = 1} := by
    have h1 : ι (j y) ∈ (Algebra.adjoin ℚ
        {b : CyclotomicField (m : ℕ) ℚ | ∃ n : ℕ, n ∈ ({(m : ℕ)} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1}).map ι :=
      Subalgebra.mem_map.2 ⟨_, hy, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    have h2 : (ι : CyclotomicField (m : ℕ) ℚ → Qbar) ''
        {b : CyclotomicField (m : ℕ) ℚ | ∃ n : ℕ, n ∈ ({(m : ℕ)} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} ⊆
        {w : Qbar | w ^ (m : ℕ) = 1} := by
      rintro _ ⟨b, ⟨n, hn, -, hb⟩, rfl⟩
      rw [Set.mem_singleton_iff] at hn
      subst hn
      change ι b ^ (m : ℕ) = 1
      rw [← map_pow, hb, map_one]
    exact Algebra.adjoin_mono h2 h1
  exact hT hιy

/-- **Finite-order characters of `G_ℚ` are Dirichlet characters (GLUE, proved from T17).** -/
theorem ker_ge_of_kroneckerWeber (hKW : KroneckerWeber) {G : Type*} [CommGroup G]
    (ψ : GQ →* G) (hψ : IsOpen (ψ.ker : Set GQ)) :
    ∃ m : ℕ+, ∀ σ : GQ, (∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = ζ) → ψ σ = 1 := by
  let H : ClosedSubgroup GQ := ⟨ψ.ker, Subgroup.isClosed_of_isOpen _ hψ⟩
  let L : IntermediateField ℚ Qbar := IntermediateField.fixedField (H : Subgroup GQ)
  have hLfix : L.fixingSubgroup = ψ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have hfin : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).1 (by
      change IsOpen (L.fixingSubgroup : Set GQ)
      rw [hLfix]
      exact hψ)
  have hgal : IsGalois ℚ L :=
    (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hLfix]; exact ψ.normal_ker)
  have : NumberField L := ⟨⟩
  have hab : ∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Qbar σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Qbar τ
    rw [← map_mul, ← map_mul, MonoidHom.eq_iff, L.restrictNormalHom_ker, hLfix,
      MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_comm (ψ τ') (ψ σ'),
      inv_mul_cancel]
  obtain ⟨m, ⟨j⟩⟩ := hKW L hab
  refine ⟨m, fun σ hσ => ?_⟩
  rw [← MonoidHom.mem_ker, ← hLfix, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact fixes_of_embeds L m j σ hσ x hx

/-! ## The case C8 uses: cyclic extensions -/

/-- **Kronecker–Weber for cyclic extensions** (the case step C8 uses: the fixed field of the kernel
of a finite-order character with values in a field).  A consequence of `KroneckerWeber`
(`kroneckerWeberCyclic_of_kroneckerWeber`), so never stronger than the published theorem. -/
def KroneckerWeberCyclic : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L], IsCyclic (L ≃ₐ[ℚ] L) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

theorem kroneckerWeberCyclic_of_kroneckerWeber (h : KroneckerWeber) : KroneckerWeberCyclic := by
  intro L _ _ _ hc
  let _ : CommGroup (L ≃ₐ[ℚ] L) := IsCyclic.commGroup
  exact h L fun σ τ => mul_comm σ τ

/-- **Finite-order characters of `G_ℚ` with values in a field are Dirichlet characters (GLUE,
proved from the cyclic case of T17).** -/
theorem ker_ge_of_kroneckerWeberCyclic (hKW : KroneckerWeberCyclic) {E : Type*} [Field E]
    (ψ : GQ →* Eˣ) (hψ : IsOpen (ψ.ker : Set GQ)) :
    ∃ m : ℕ+, ∀ σ : GQ, (∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = ζ) → ψ σ = 1 := by
  let H : ClosedSubgroup GQ := ⟨ψ.ker, Subgroup.isClosed_of_isOpen _ hψ⟩
  let L : IntermediateField ℚ Qbar := IntermediateField.fixedField (H : Subgroup GQ)
  have hLfix : L.fixingSubgroup = ψ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have hfin : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).1 (by
      change IsOpen (L.fixingSubgroup : Set GQ)
      rw [hLfix]
      exact hψ)
  have hgal : IsGalois ℚ L :=
    (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hLfix]; exact ψ.normal_ker)
  have : NumberField L := ⟨⟩
  -- `Gal(L/ℚ) ≅ G_ℚ / ker ψ ≅ im ψ ⊆ Eˣ` is cyclic
  have hker : (AlgEquiv.restrictNormalHom (K₁ := Qbar) L).ker = ψ.ker := by
    rw [L.restrictNormalHom_ker, hLfix]
  let e : (L ≃ₐ[ℚ] L) ≃* ψ.range :=
    ((QuotientGroup.quotientKerEquivOfSurjective _
      (AlgEquiv.restrictNormalHom_surjective Qbar)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans (QuotientGroup.quotientKerEquivRange ψ)
  have hcyc : IsCyclic (L ≃ₐ[ℚ] L) :=
    isCyclic_of_injective_ringHom ((Units.coeHom E).comp (ψ.range.subtype.comp e.toMonoidHom))
      (Units.val_injective.comp (Subtype.val_injective.comp e.injective))
  obtain ⟨m, ⟨j⟩⟩ := hKW L hcyc
  refine ⟨m, fun σ hσ => ?_⟩
  rw [← MonoidHom.mem_ker, ← hLfix, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact fixes_of_embeds L m j σ hσ x hx

/-- `ψ σ` depends only on the action of `σ` on the `m`-th roots of unity, i.e. `ψ` factors
through `Gal(ℚ(μ_m)/ℚ) ≅ (ℤ/m)ˣ` (GLUE, proved from T17). -/
theorem eq_of_agree_on_roots (hKW : KroneckerWeber) {G : Type*} [CommGroup G]
    (ψ : GQ →* G) (hψ : IsOpen (ψ.ker : Set GQ)) :
    ∃ m : ℕ+, ∀ σ τ : GQ, (∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = τ ζ) → ψ σ = ψ τ := by
  obtain ⟨m, hm⟩ := ker_ge_of_kroneckerWeber hKW ψ hψ
  refine ⟨m, fun σ τ h => ?_⟩
  have h1 : ψ (τ⁻¹ * σ) = 1 := hm _ fun ζ hζ => by
    rw [AlgEquiv.mul_apply, h ζ hζ, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

/-- The cyclic-case version of `eq_of_agree_on_roots`, for `ψ` with values in a field. -/
theorem eq_of_agree_on_roots_cyclic (hKW : KroneckerWeberCyclic) {E : Type*} [Field E]
    (ψ : GQ →* Eˣ) (hψ : IsOpen (ψ.ker : Set GQ)) :
    ∃ m : ℕ+, ∀ σ τ : GQ, (∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = τ ζ) → ψ σ = ψ τ := by
  obtain ⟨m, hm⟩ := ker_ge_of_kroneckerWeberCyclic hKW ψ hψ
  refine ⟨m, fun σ τ h => ?_⟩
  have h1 : ψ (τ⁻¹ * σ) = 1 := hm _ fun ζ hζ => by
    rw [AlgEquiv.mul_apply, h ζ hζ, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

/-! ## The Dirichlet character, through Mathlib's mod-`m` cyclotomic character -/

/-- A primitive `m`-th root of unity in `ℚ̄` (a root of the `m`-th cyclotomic polynomial). -/
theorem exists_isPrimitiveRoot_qbar (m : ℕ+) : ∃ ζ : Qbar, IsPrimitiveRoot ζ (m : ℕ) := by
  have : NeZero ((m : ℕ) : Qbar) := ⟨by exact_mod_cast m.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (m : ℕ) Qbar)
    (Polynomial.degree_cyclotomic_pos (m : ℕ) Qbar m.pos).ne'
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩

theorem card_rootsOfUnity_qbar (m : ℕ+) : Nat.card (rootsOfUnity (m : ℕ) Qbar) = m :=
  (exists_isPrimitiveRoot_qbar m).choose_spec.card_rootsOfUnity

/-- `G_ℚ → Aut(ℚ̄)` as rings. -/
noncomputable def toRingAut : GQ →* (Qbar ≃+* Qbar) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The mod-`m` cyclotomic character `G_ℚ → (ℤ/m)ˣ` (Mathlib's `modularCyclotomicCharacter`). -/
noncomputable def cycChar (m : ℕ+) : GQ →* (ZMod m)ˣ :=
  (modularCyclotomicCharacter Qbar (card_rootsOfUnity_qbar m)).comp toRingAut

theorem cycChar_spec (m : ℕ+) (σ : GQ) (ζ : Qbar) (hζ : ζ ^ (m : ℕ) = 1) :
    σ ζ = ζ ^ ((cycChar m σ : (ZMod m)ˣ) : ZMod m).val := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by exact_mod_cast m.ne_zero)] at hζ
    exact zero_ne_one hζ
  have ht : Units.mk0 ζ hζ0 ∈ rootsOfUnity (m : ℕ) Qbar := by
    rw [mem_rootsOfUnity]
    ext
    simpa using hζ
  exact modularCyclotomicCharacter.spec Qbar (card_rootsOfUnity_qbar m) σ.toRingEquiv ht

theorem agree_of_cycChar_eq (m : ℕ+) (σ τ : GQ) (h : cycChar m σ = cycChar m τ) (ζ : Qbar)
    (hζ : ζ ^ (m : ℕ) = 1) : σ ζ = τ ζ := by
  rw [cycChar_spec m σ ζ hζ, cycChar_spec m τ ζ hζ, h]

/-- The mod-`m` cyclotomic character of `G_ℚ` is surjective (irreducibility of the cyclotomic
polynomial over `ℚ`, Mathlib's `autEquivPow`, and lifting from `ℚ(ζ_m)` to `ℚ̄`). -/
theorem cycChar_surjective (m : ℕ+) : Function.Surjective (cycChar m) := by
  intro u
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot_qbar m
  let F : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {ζ₀}
  have := hζ₀.intermediateField_adjoin_isCyclotomicExtension ℚ
  let ζ := IsCyclotomicExtension.zeta (m : ℕ) ℚ F
  have hζ : IsPrimitiveRoot ζ (m : ℕ) := IsCyclotomicExtension.zeta_spec (m : ℕ) ℚ F
  let τ : F ≃ₐ[ℚ] F := (IsCyclotomicExtension.autEquivPow F
    (Polynomial.cyclotomic.irreducible_rat m.pos)).symm u
  have hτ : τ ζ = ζ ^ (u : ZMod m).val := by
    have h1 := hζ.autToPow_spec ℚ τ
    have h2 : hζ.autToPow ℚ τ = u := by
      have := (IsCyclotomicExtension.autEquivPow F
        (Polynomial.cyclotomic.irreducible_rat m.pos)).apply_symm_apply u
      rwa [IsCyclotomicExtension.autEquivPow_apply] at this
    rw [← h1, h2]
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {(m : ℕ)} ℚ F
  let σ : GQ := τ.liftNormal Qbar
  let ι : F →ₐ[ℚ] Qbar := F.val
  have hσζ : σ (ι ζ) = ι ζ ^ (u : ZMod m).val := by
    have h1 := AlgEquiv.liftNormal_commutes τ Qbar ζ
    change σ (ι ζ) = ι (τ ζ) at h1
    rw [h1, hτ, map_pow]
  refine ⟨σ, ?_⟩
  have hιζ : IsPrimitiveRoot (ι ζ) (m : ℕ) := hζ.map_of_injective ι.injective
  symm
  apply Units.ext
  refine modularCyclotomicCharacter.unique Qbar (card_rootsOfUnity_qbar m) σ.toRingEquiv ?_
  intro t ht
  have htm : (t : Qbar) ^ (m : ℕ) = 1 := by
    rw [mem_rootsOfUnity] at ht
    simpa using congrArg Units.val ht
  obtain ⟨i, -, hi⟩ := hιζ.eq_pow_of_pow_eq_one htm
  change σ (t : Qbar) = (t : Qbar) ^ _
  rw [← hi, map_pow, hσζ, ← pow_mul, ← pow_mul, mul_comm]

/-- **Finite-order characters of `G_ℚ` are Dirichlet characters (GLUE, proved from the cyclic
case of T17).** For `ψ : G_ℚ →* Eˣ` (`E` a field) with open kernel there are `m ≥ 1` and a
Dirichlet character `χ` mod `m` (Mathlib's `DirichletCharacter`) with `ψ = χ ∘ cyc_m`, where
`cyc_m` is the mod-`m` cyclotomic character. -/
theorem dirichletCharacter_of_kroneckerWeberCyclic (hKW : KroneckerWeberCyclic) {E : Type*}
    [Field E] (ψ : GQ →* Eˣ) (hψ : IsOpen (ψ.ker : Set GQ)) :
    ∃ (m : ℕ+) (χ : DirichletCharacter E (m : ℕ)),
      ∀ σ : GQ, (ψ σ : E) = χ ((cycChar m σ : (ZMod m)ˣ) : ZMod m) := by
  obtain ⟨m, hm⟩ := eq_of_agree_on_roots_cyclic hKW ψ hψ
  have hψc : ∀ σ τ : GQ, cycChar m σ = cycChar m τ → ψ σ = ψ τ := fun σ τ h =>
    hm σ τ (agree_of_cycChar_eq m σ τ h)
  let s := Function.surjInv (cycChar_surjective m)
  have hs : ∀ u, cycChar m (s u) = u := Function.surjInv_eq (cycChar_surjective m)
  let χu : (ZMod m)ˣ →* Eˣ :=
    { toFun := fun u => ψ (s u)
      map_one' := by
        rw [← map_one ψ]
        exact hψc _ _ (by rw [hs, map_one])
      map_mul' := fun u v => by
        rw [← map_mul ψ]
        exact hψc _ _ (by rw [hs, map_mul, hs, hs]) }
  refine ⟨m, MulChar.ofUnitHom χu, fun σ => ?_⟩
  rw [MulChar.ofUnitHom_coe]
  change (ψ σ : E) = (ψ (s (cycChar m σ)) : E)
  rw [hψc σ (s (cycChar m σ)) (hs _).symm]

/-- A continuous homomorphism with finite image to a `T1` topological group has open kernel. -/
theorem isOpen_ker_of_continuous {G : Type*} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : GQ →* G) (hc : Continuous ψ) (hfin : (Set.range ψ).Finite) :
    IsOpen (ψ.ker : Set GQ) := by
  have hcl : IsClosed (ψ ⁻¹' (Set.range ψ \ {1})) :=
    ((hfin.subset Set.sdiff_subset).isClosed).preimage hc
  have : (ψ.ker : Set GQ) = (ψ ⁻¹' (Set.range ψ \ {1}))ᶜ := by
    ext σ
    simp [MonoidHom.mem_ker]
  rw [this]
  exact hcl.isOpen_compl

end TSkolemKW.KW


#print axioms TSkolemKW.skolemNoether
#print axioms TSkolemKW.leafSkolemNoether
#print axioms TSkolemKW.brauerNesbittChar0
#print axioms TSkolemKW.hsynBrauerNesbitt
#print axioms TSkolemKW.HS.frobeniusDense_of_chebotarev
#print axioms TSkolemKW.KW.eq_of_agree_on_roots
#print axioms TSkolemKW.KW.eq_of_agree_on_roots_cyclic
#print axioms TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic

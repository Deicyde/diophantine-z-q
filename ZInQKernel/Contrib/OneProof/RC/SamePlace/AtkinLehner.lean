import ZInQKernel.Contrib.OneProof.RC.SamePlace.Supersingular
import ZInQKernel.Contrib.TauCeti.Data.Nat.ExactDivisor
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric6.CharFreeSeamTwo
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric6.Cyclicity
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_Algebra_IsSeparable_of_coprime_finrank_expChar

/-! # The moduli Atkin–Lehner map σ_Q on pair classes (rc-same-place1, item 6)

Let `K` be algebraically closed with `(N : K) ≠ 0` and `(2 : K) ≠ 0`, `q` a prime with
`Q = q^e ∥ N`.

* (a) `smulSubgroup_cyclic`: for a cyclic subgroup `C` of order `N`, the subgroup
  `(N/Q) • C` is cyclic of order `Q` (the `hH` input of `ModelGeneric6.exists_quotientSeam`).
* (b) `SepSeam E H n`: a **separable seam** to the vendored Vélu composite
  `E.cyclicQuotientCurve H n` (a seam `g` in the sense of `ModelGeneric6.IsSeam`, with
  `g.ker = H`, `FiniteAlong K ι` and `finrankAlong K ι = n`); `SepSeam.choose` picks one, from
  `ModelGeneric6.exists_quotientSeam`. `sigmaAt` sends the class of `(E, C)` (through the chosen
  representative `Quot.out`) to the class of
  `(E.cyclicQuotientCurve C_Q Q, g(E[Q] ⊔ C))`, `C_Q = (N/Q) • C`, for the chosen separable seam
  `g`, written with exactly the class expression of the INTERFACE block
  (`ModelGeneric6.atkinImage`). `sigmaQ q` is `sigmaAt` at `Q = q^(v_q N)`
  (`TauCeti.Nat.isExactDivisor_primePow`): the moduli-side `X.W q` (never `J ∘ atkin ∘ J⁻¹`).
  The choice of the separable seam does not change the class (uniqueness of separable quotients);
  that comparison is SP2's and is not used here.
* (c) `surjective_of_isSeam`: in characteristic `ell` with `finrankAlong K ι` prime to `ell`, a
  seam is surjective on `K`-points (`SeparableAlong` from the vendored
  `Algebra.IsSeparable.of_coprime_finrank_expChar`, then the vendored
  `AlgebraicCurve.Place.restrictAlong_surjective`, then the place–point bijection of the gate).
* (d) `sigmaAt_isSupersingular`: σ_Q preserves supersingularity, from the group lemma
  `torsionBy_eq_bot_of_surjective` (a surjection whose kernel has order prime to `ell` carries
  trivial `ell`-torsion to trivial `ell`-torsion). `sigmaQSS` is σ_Q on `ssPoint K ell N`.

Provenance: (a) is finite group theory, adapted from the order computation inside
`ModelGeneric6.isAddCyclic_map_atkinSum` (RC/ModelGeneric6/Cyclicity.lean:155-159, base
8b140cd2a); (b) is a definition; (c) is an assembly of vendored and Mathlib results, on the spot
(c); (d) is on the spot (c). Sketch of (d): if `ell • P' = 0` and `g P = P'`, then `ell • P ∈ ker g`,
so `Q • ell • P = 0`, so `Q • P ∈ E[ell] = 0`, so `Q • P' = 0`; as `Q` and `ell` are coprime,
`P' = 0`. -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ZInQ.Manuscript.RC.SamePlace

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.ModelLevels
open scoped TauCeti.ExactDivisor

/-! ### (a) The subgroup `C_Q = (N/Q) • C` -/

section Group

variable {A : Type*} [AddCommGroup A]

-- Adapted from the order computation in `ModelGeneric6.isAddCyclic_map_atkinSum`
-- (RC/ModelGeneric6/Cyclicity.lean:140-159, base 8b140cd2a).
/-- **`(N/Q) • C` is cyclic of order `Q`** for a cyclic subgroup `C` of order `N ≠ 0` and
`Q ∣ N`. -/
theorem smulSubgroup_cyclic {N Q : ℕ} (hN : N ≠ 0) (hQ : Q ∣ N) (C : AddSubgroup A)
    (hC : IsAddCyclic C ∧ Nat.card C = N) :
    IsAddCyclic (ModelGeneric6.smulSubgroup (N / Q) C) ∧
      Nat.card (ModelGeneric6.smulSubgroup (N / Q) C) = Q := by
  haveI := hC.1
  obtain ⟨⟨c, hcC⟩, hc⟩ := IsAddCyclic.exists_generator (α := C)
  have hCc : C = AddSubgroup.zmultiples c := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hc ⟨y, hy⟩)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, congrArg Subtype.val hn⟩
    · intro hy
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      exact C.zsmul_mem hcC n
  have hoc : addOrderOf c = N := by
    rw [← hC.2, hCc, Nat.card_zmultiples]
  have hQ0 : Q ≠ 0 := by rintro rfl; exact hN (zero_dvd_iff.mp hQ)
  have hM0 : N / Q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hQ)
    (Nat.pos_of_ne_zero hQ0)).ne'
  have hmap : ModelGeneric6.smulSubgroup (N / Q) C = AddSubgroup.zmultiples ((N / Q) • c) := by
    rw [ModelGeneric6.smulSubgroup, hCc, AddMonoidHom.map_zmultiples]
    rfl
  have hord : addOrderOf ((N / Q) • c) = Q := by
    rw [addOrderOf_nsmul' (x := c) hM0, hoc,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hQ), Nat.div_div_self hQ hN]
  rw [hmap, Nat.card_zmultiples, hord]
  exact ⟨inferInstance, rfl⟩

/-- **Trivial `ell`-torsion passes along a surjection whose kernel has order prime to `ell`.** -/
theorem torsionBy_eq_bot_of_surjective {B : Type*} [AddCommGroup B] (g : A →+ B)
    (hg : Function.Surjective g) {Q ell : ℕ} (hker : Nat.card g.ker = Q) (hcop : Q.Coprime ell)
    (hA : Submodule.torsionBy ℤ A (ell : ℤ) = ⊥) : Submodule.torsionBy ℤ B (ell : ℤ) = ⊥ := by
  rw [Submodule.eq_bot_iff] at hA ⊢
  intro y hy
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at hy
  obtain ⟨x, rfl⟩ := hg y
  have hk : ell • x ∈ g.ker := by
    rw [AddMonoidHom.mem_ker, map_nsmul, hy]
  have hQx : Q • ell • x = 0 := by
    have := card_nsmul_eq_zero' (G := g.ker) (x := ⟨ell • x, hk⟩)
    rw [hker] at this
    exact congrArg Subtype.val this
  have hQ : Q • x = 0 := by
    apply hA
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← mul_nsmul, mul_comm, mul_nsmul, hQx]
  have h1 : addOrderOf (g x) ∣ Q := addOrderOf_dvd_of_nsmul_eq_zero (by rw [← map_nsmul, hQ,
    map_zero])
  have h2 : addOrderOf (g x) ∣ ell := addOrderOf_dvd_of_nsmul_eq_zero hy
  have h3 : addOrderOf (g x) = 1 := Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
  exact AddMonoid.addOrderOf_eq_one_iff.mp h3

end Group

variable {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K]

/-! ### (c) Separable seams are surjective on points -/

/-- A finite map of function fields whose degree is prime to the characteristic `ell` is
separable (the vendored `Algebra.IsSeparable.of_coprime_finrank_expChar`). -/
theorem separableAlong_of_coprime (ell : ℕ) [Fact ell.Prime] [CharP K ell]
    {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F'] (ι : F →ₐ[K] F')
    (hfin : FiniteAlong K ι) (hcop : (finrankAlong K ι).Coprime ell) : SeparableAlong K ι := by
  letI := algebraAlong ι
  haveI : Module.Finite F F' := hfin
  haveI : ExpChar F ell := expChar_of_injective_algebraMap (algebraMap K F).injective ell
  exact Algebra.IsSeparable.of_coprime_finrank_expChar F F' ell hcop

/-- **A seam along a finite separable map of function fields is surjective on points.** -/
theorem surjective_of_isSeam {V W : WeierstrassCurve K} [V.IsElliptic] [W.IsElliptic]
    (ι : V.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (g : W.toAffine.Point →+ V.toAffine.Point) (hfin : FiniteAlong K ι)
    (hsep : SeparableAlong K ι) (hseam : ModelGeneric6.IsSeam ι hι g) :
    Function.Surjective g := by
  intro P'
  obtain ⟨w, hw⟩ := Place.restrictAlong_surjective ι hι hfin hsep (ModelGeneric6.pointPlace V P')
  letI := ModelGeneric6.gate W
  let P : W.toAffine.Point := (pointEquivPlace (W := W.toAffine)).symm w
  have hP : ModelGeneric6.pointPlace W P = w :=
    (pointEquivPlace (W := W.toAffine)).apply_symm_apply w
  refine ⟨P, ?_⟩
  have h := hseam P
  rw [hP] at h
  have h' : ModelGeneric6.pointPlace V (g P) = ModelGeneric6.pointPlace V P' := h.symm.trans hw
  letI := ModelGeneric6.gate V
  exact (pointEquivPlace (W := V.toAffine)).injective h'

/-! ### (b) Separable seams and σ_Q -/

/-- **A separable seam** to the vendored Vélu composite `E.cyclicQuotientCurve H n`: a seam `g`
(`ModelGeneric6.IsSeam`) with kernel `H`, along a finite map `ι` of function fields of degree
`n`. -/
structure SepSeam (E : WeierstrassCurve K) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point)
    (n : ℕ) where
  elliptic : (E.cyclicQuotientCurve H n).IsElliptic
  ι : (E.cyclicQuotientCurve H n).toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField
  isIntegral : ι.toRingHom.IsIntegral
  finite : FiniteAlong K ι
  finrank : finrankAlong K ι = n
  g : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point
  ker : g.ker = H
  seam : letI := elliptic; ModelGeneric6.IsSeam ι isIntegral g

/-- A chosen separable seam, from `ModelGeneric6.exists_quotientSeam`. -/
def SepSeam.choose (n : ℕ) (hn : n ≠ 0) (hchar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → (ℓ : K) ≠ 0)
    (E : WeierstrassCurve K) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point)
    (hH : IsAddCyclic H ∧ Nat.card H = n) : SepSeam E H n :=
  Classical.choice (by
    obtain ⟨hE', ι, hι, hfin, hdeg, g, hg, hs⟩ :=
      ModelGeneric6.exists_quotientSeam n hn hchar E H hH
    exact ⟨⟨hE', ι, hι, hfin, hdeg, g, hg, hs⟩⟩)

/-- A separable seam is surjective on points in characteristic `ell` prime to its degree. -/
theorem SepSeam.surjective (ell : ℕ) [Fact ell.Prime] [CharP K ell]
    {E : WeierstrassCurve K} [E.IsElliptic] {H : AddSubgroup E.toAffine.Point} {n : ℕ}
    (S : SepSeam E H n) (hcop : n.Coprime ell) : Function.Surjective S.g := by
  letI := S.elliptic
  exact surjective_of_isSeam S.ι S.isIntegral S.g S.finite
    (separableAlong_of_coprime ell S.ι S.finite (by rw [S.finrank]; exact hcop)) S.seam

variable {N : ℕ} [NeZero N]

omit [DecidableEq K] [IsAlgClosed K] [NeZero N] in
/-- Every prime divisor of a divisor `Q` of `N` is nonzero in `K` when `N` is. -/
theorem prime_cast_ne_zero {Q : ℕ} (hQ : Q ∣ N) (hNk : (N : K) ≠ 0) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Q → (ℓ : K) ≠ 0 := by
  intro ℓ _ hℓ h0
  obtain ⟨m, hm⟩ := hℓ.trans hQ
  exact hNk (by rw [hm, Nat.cast_mul, h0, zero_mul])

/-- The chosen separable seam of the class representative, at `C_Q = (N/Q) • C`. -/
def atkinSeam {Q : ℕ} (hQ : Q ∥ N) (hNk : (N : K) ≠ 0) (A : EnhancedCurve K N) :
    letI := A.elliptic
    SepSeam A.equation (ModelGeneric6.smulSubgroup (N / Q) A.subgroup.1) Q :=
  letI := A.elliptic
  SepSeam.choose Q hQ.ne_zero (prime_cast_ne_zero hQ.dvd hNk) A.equation _
    (smulSubgroup_cyclic (NeZero.ne N) hQ.dvd A.subgroup.1 A.subgroup.2)

/-- **The moduli Atkin–Lehner map on an enhanced curve**: `(E, C) ↦ (E.cyclicQuotientCurve C_Q Q,
g(E[Q] ⊔ C))` for the chosen separable seam `g` (class expression of the INTERFACE block). -/
def sigmaEnhanced {q e Q : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e) (hQ : Q ∥ N)
    (hNk : (N : K) ≠ 0) (h2k : (2 : K) ≠ 0) (A : EnhancedCurve K N) : PairClasses K N :=
  letI := A.elliptic
  Quot.mk _ ⟨_, (atkinSeam hQ hNk A).elliptic,
    ModelGeneric6.atkinImage A.equation hq he hQe (Nat.mul_div_cancel' hQ.dvd).symm hQ.coprime
      hNk h2k A.subgroup (atkinSeam hQ hNk A).g (atkinSeam hQ hNk A).ker⟩

/-- **σ_Q on pair classes at an exact prime-power divisor `Q = q^e ∥ N`**, through the chosen
representative `Quot.out` and the chosen separable seam. -/
def sigmaAt {q e Q : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e) (hQ : Q ∥ N)
    (hNk : (N : K) ≠ 0) (h2k : (2 : K) ≠ 0) (x : PairClasses K N) : PairClasses K N :=
  sigmaEnhanced hq he hQe hQ hNk h2k (Quot.out x)

/-- **σ_Q at `Q = q^(v_q N)`**: the moduli-side Atkin–Lehner map `X.W q` of the same-place lane. -/
def sigmaQ {q : ℕ} (hq : q.Prime) (he : 0 < N.factorization q) (hNk : (N : K) ≠ 0)
    (h2k : (2 : K) ≠ 0) : PairClasses K N → PairClasses K N :=
  sigmaAt hq he rfl (TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q)) hNk h2k

/-! ### (d) σ_Q preserves supersingularity -/

theorem sigmaEnhanced_isSupersingular (ell : ℕ) [Fact ell.Prime] [CharP K ell]
    {q e Q : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e) (hQ : Q ∥ N)
    (hNk : (N : K) ≠ 0) (h2k : (2 : K) ≠ 0) (A : EnhancedCurve K N)
    (hA : EnhancedCurve.IsSupersingular ell A) :
    PairClasses.IsSupersingular ell (sigmaEnhanced hq he hQe hQ hNk h2k A) := by
  letI := A.elliptic
  let S := atkinSeam hQ hNk A
  letI := S.elliptic
  have hcop : Q.Coprime ell := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hd => hNk ?_)
    exact (CharP.cast_eq_zero_iff K ell N).mpr (hd.trans hQ.dvd)
  have hker : Nat.card S.g.ker = Q := by
    rw [S.ker]
    exact (smulSubgroup_cyclic (NeZero.ne N) hQ.dvd A.subgroup.1 A.subgroup.2).2
  exact torsionBy_eq_bot_of_surjective S.g (S.surjective ell hcop) hker hcop hA

theorem sigmaAt_isSupersingular (ell : ℕ) [Fact ell.Prime] [CharP K ell]
    {q e Q : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e) (hQ : Q ∥ N)
    (hNk : (N : K) ≠ 0) (h2k : (2 : K) ≠ 0) (x : PairClasses K N)
    (hx : PairClasses.IsSupersingular ell x) :
    PairClasses.IsSupersingular ell (sigmaAt hq he hQe hQ hNk h2k x) := by
  apply sigmaEnhanced_isSupersingular ell hq he hQe hQ hNk h2k
  have : (Quot.mk _ (Quot.out x) : PairClasses K N) = x := Quot.out_eq x
  rw [← this] at hx
  exact hx

/-- **σ_Q on the supersingular pair classes** (the moduli-side `X.W q`). -/
def sigmaQSS (ell : ℕ) [Fact ell.Prime] [CharP K ell] {q : ℕ} (hq : q.Prime)
    (he : 0 < N.factorization q) (hNk : (N : K) ≠ 0) (h2k : (2 : K) ≠ 0)
    (x : ssPoint K ell N) : ssPoint K ell N :=
  ⟨sigmaQ hq he hNk h2k x.1,
    sigmaAt_isSupersingular ell hq he rfl _ hNk h2k x.1 x.2⟩

@[simp] theorem sigmaQSS_val (ell : ℕ) [Fact ell.Prime] [CharP K ell] {q : ℕ} (hq : q.Prime)
    (he : 0 < N.factorization q) (hNk : (N : K) ≠ 0) (h2k : (2 : K) ≠ 0)
    (x : ssPoint K ell N) : (sigmaQSS ell hq he hNk h2k x).1 = sigmaQ hq he hNk h2k x.1 :=
  rfl

end ZInQ.Manuscript.RC.SamePlace

#print axioms ZInQ.Manuscript.RC.SamePlace.smulSubgroup_cyclic
#print axioms ZInQ.Manuscript.RC.SamePlace.torsionBy_eq_bot_of_surjective
#print axioms ZInQ.Manuscript.RC.SamePlace.separableAlong_of_coprime
#print axioms ZInQ.Manuscript.RC.SamePlace.surjective_of_isSeam
#print axioms ZInQ.Manuscript.RC.SamePlace.SepSeam.choose
#print axioms ZInQ.Manuscript.RC.SamePlace.SepSeam.surjective
#print axioms ZInQ.Manuscript.RC.SamePlace.sigmaAt
#print axioms ZInQ.Manuscript.RC.SamePlace.sigmaQ
#print axioms ZInQ.Manuscript.RC.SamePlace.sigmaAt_isSupersingular
#print axioms ZInQ.Manuscript.RC.SamePlace.sigmaQSS

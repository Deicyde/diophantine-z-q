import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.Cyclotomic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Local Kronecker–Weber for `ℚ_p`, from Tau Ceti's local class field theory

Let `(AlgebraicClosure ℚ_[p]) = (AlgebraicClosure ℚ_[p])` (Mathlib's `PadicAlgCl p`). Every finite abelian extension
`L ⊆ (AlgebraicClosure ℚ_[p])` of `ℚ_p` lies in `ℚ_p(ζ_m)` for some `m ≥ 1` (`le_adjoin_rootsOfUnity`).

The proof uses the local reciprocity law and the explicit action of local Artin symbols on roots
of unity proved in Tau Ceti (vendored under `ZInQKernel/Contrib/TauCeti/`):

* **Norm groups reverse inclusion** (`le_of_normGroup_le`): for `L, M ⊆ (AlgebraicClosure ℚ_[p])` finite Galois over
  `ℚ_p` with `L` abelian, `N_M ≤ N_L` implies `L ≤ M`. This uses the density of the image of the
  absolute Artin map (`denseRange_artinMap`), its finite restrictions (`artinMap_restrict`) and
  the kernel of the finite Artin map (`localArtinMap_eq_zero_iff`).
* **Hensel** (`exists_pow_eq_of_norm_sub_one_le`): a unit `u ≡ 1 mod p^(2 v_p(n) + 1)` of `ℤ_p`
  is an `n`-th power.
* **A cyclotomic norm group** (`normGroup_cyclotomic_le_powerSubgroup`): for
  `m = p^(2 v_p(n) + 1) (pⁿ − 1)`, every norm from `ℚ_p(ζ_m)` is an `n`-th power. A norm
  `x = p^a u` has trivial Artin symbol on `ℚ_p(ζ_m)`; on the `p`-power roots of unity the symbol
  acts through `u⁻¹` (`localArtinMap_cyclotomic_padic_primePow`), so `u ≡ 1`; on the roots of
  unity of order `pⁿ − 1` it acts as the `a`-th power of Frobenius
  (`localArtinMap_cyclotomic_padic`, `localArtinMap_cyclotomic_uniformizer`), so `n ∣ a`.
* Since `(ℚ_pˣ)ⁿ ≤ N_L` for `n = [L : ℚ_p]` (`powerSubgroup_le_normGroup_of_exponent_dvd`),
  `N_{ℚ_p(ζ_m)} ≤ N_L` and `L ≤ ℚ_p(ζ_m)`.

The local existence theorem is not used.
-/

open TauCeti TauCeti.ClassFieldTheory
open scoped IsMulCommutative

noncomputable section

-- Instance search for `Nontrivial ℚ_[p]`, separability and Galois instances runs past the default
-- budget in the presence of the Tau Ceti instances.
set_option synthInstance.maxHeartbeats 100000

namespace ZInQ.Contrib.LocalKW

variable (p : ℕ) [Fact p.Prime]

/-- Instance search does not find `Nontrivial ℚ_[p]` within its budget here, so it is supplied
from the field structure (as in Tau Ceti). -/
local instance padicNontrivial : Nontrivial ℚ_[p] := DivisionRing.toNontrivial


/-! ### The inclusion of a separable intermediate field into the separable closure -/

/-- The inclusion of a separable intermediate field of `(AlgebraicClosure ℚ_[p])` into the separable
closure `SeparableClosure ℚ_[p] ⊆ (AlgebraicClosure ℚ_[p])`. -/
def sepIncl (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [Algebra.IsSeparable ℚ_[p] M] :
    M →ₐ[ℚ_[p]] SeparableClosure ℚ_[p] :=
  M.val.codRestrict (separableClosure ℚ_[p] (AlgebraicClosure ℚ_[p])).toSubalgebra
    fun z ↦ mem_separableClosure_iff.2 ((Algebra.IsSeparable.isSeparable ℚ_[p] z).map M.val
      M.val.injective)

theorem coe_sepIncl (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [Algebra.IsSeparable ℚ_[p] M] (y : M) :
    ((sepIncl p M y : SeparableClosure ℚ_[p]) : (AlgebraicClosure ℚ_[p])) = y :=
  AlgHom.coe_codRestrict _ _ _ y

/-! ### Norms have Artin symbols fixing abelian extensions -/

/-- **Converse of `mem_normGroup_of_mk_eq_artinMap_of_fixes` for abelian extensions.** If
`x ∈ ℚ_pˣ` is a norm from a finite abelian extension `L ⊆ (AlgebraicClosure ℚ_[p])`, every representative `τ` of its
absolute Artin symbol fixes `L` pointwise. -/
theorem fixes_of_mem_normGroup (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L] [IsMulCommutative Gal(L/ℚ_[p])]
    {x : ℚ_[p]ˣ} (hx : x ∈ normGroup ℚ_[p] L) (τ : Field.absoluteGaloisGroup ℚ_[p])
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = artinMap ℚ_[p] x) (z : L) :
    DFunLike.coe (F := Gal((AlgebraicClosure ℚ_[p])/ℚ_[p])) τ (z : (AlgebraicClosure ℚ_[p])) = z := by
  have : Algebra.IsSeparable ℚ_[p] L := IsGalois.to_isSeparable
  let ι := sepIncl p L
  have h := artinMap_restrict ℚ_[p] L ι x τ hτ
  rw [(localArtinMap_eq_zero_iff ℚ_[p] L ι x).2 hx] at h
  have h2 : Abelianization.of (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv ℚ_[p] τ)) =
      1 := by
    have h' := congrArg Additive.toMul h
    simpa using h'.symm
  have h1 : ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv ℚ_[p] τ) = 1 :=
    (Abelianization.equivOfComm (H := Gal(L/ℚ_[p]))).injective (by simpa using h2)
  have h3 := ι.restrictNormalHom_commutes (absoluteGaloisGroupRestrictEquiv ℚ_[p] τ) z
  rw [h1, AlgEquiv.one_apply] at h3
  have h4 := coe_absoluteGaloisGroupRestrictEquiv_apply ℚ_[p] τ (ι z)
  rw [coe_sepIncl] at h4
  rw [← h4, ← h3, coe_sepIncl]

/-! ### Norm groups reverse inclusion -/

/-- **Norm groups reverse inclusion.** Let `L, M ⊆ (AlgebraicClosure ℚ_[p])` be finite Galois over
`ℚ_p`, with `L` abelian. If every norm from `M` is a norm from `L`, then `L ≤ M`. -/
theorem le_of_normGroup_le (L M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L] [IsMulCommutative Gal(L/ℚ_[p])]
    [FiniteDimensional ℚ_[p] M] [IsGalois ℚ_[p] M]
    (h : normGroup ℚ_[p] M ≤ normGroup ℚ_[p] L) : L ≤ M := by
  have : IsGalois ℚ_[p] ((AlgebraicClosure ℚ_[p])) := IsAlgClosure.isGalois ℚ_[p] _
  rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.le_iff_le]
  intro σ hσ
  set W : Subgroup Gal((AlgebraicClosure ℚ_[p])/ℚ_[p]) := L.fixingSubgroup ⊓ M.fixingSubgroup with hWdef
  have hW : IsOpen (W : Set Gal((AlgebraicClosure ℚ_[p])/ℚ_[p])) :=
    L.fixingSubgroup_isOpen.inter M.fixingSubgroup_isOpen
  let G := Field.absoluteGaloisGroup ℚ_[p]
  let σ' : G := σ
  let W' : Set G := (W : Set Gal((AlgebraicClosure ℚ_[p])/ℚ_[p]))
  have hW' : IsOpen W' := hW
  have hS : IsOpen (((↑) : G → Field.absoluteGaloisGroupAbelianization ℚ_[p]) ''
      ((σ' * ·) '' W')) :=
    QuotientGroup.isOpenMap_coe _ (isOpenMap_mul_left σ' _ hW')
  obtain ⟨x, _, ⟨w, hw, rfl⟩, hτ⟩ := (denseRange_artinMap ℚ_[p]).exists_mem_open hS
    ⟨_, σ', ⟨1, W.one_mem, mul_one σ'⟩, rfl⟩
  let w' : Gal((AlgebraicClosure ℚ_[p])/ℚ_[p]) := w
  have hw' : w' ∈ W := hw
  have hwL : ∀ y ∈ L, w' y = y := fun y hy ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).1
    (Subgroup.mem_inf.1 hw').1 y hy
  have hwM : ∀ y ∈ M, w' y = y := fun y hy ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).1
    (Subgroup.mem_inf.1 hw').2 y hy
  have hσM : ∀ y ∈ M, σ y = y := fun y hy ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).1
    hσ y hy
  have hτM : ∀ z : M, DFunLike.coe (F := Gal((AlgebraicClosure ℚ_[p])/ℚ_[p])) (σ' * w)
      (z : AlgebraicClosure ℚ_[p]) = z := fun z ↦ by
    change σ (w' (z : AlgebraicClosure ℚ_[p])) = z
    rw [hwM z z.2, hσM z z.2]
  have hxM := mem_normGroup_of_mk_eq_artinMap_of_fixes ℚ_[p] (σ' * w) hτ M hτM
  have hτL := fixes_of_mem_normGroup p L (h hxM) (σ' * w) hτ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy ↦ ?_
  have h5 : σ (w' y) = y := hτL ⟨y, hy⟩
  rwa [hwL y hy] at h5

/-! ### Hensel -/

theorem norm_natCast_padicInt {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℤ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  rw [PadicInt.norm_def, PadicInt.coe_natCast,
    Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.2 hn), Padic.valuation_natCast]

/-- **Hensel.** A `p`-adic integer `u ≡ 1 mod p^(2 v_p(n) + 1)` is an `n`-th power. -/
theorem exists_pow_eq_of_norm_sub_one_le {n : ℕ} (hn : 0 < n) {u : ℤ_[p]}
    (hu : ‖u - 1‖ ≤ (p : ℝ) ^ (-(2 * padicValNat p n + 1 : ℤ))) : ∃ z : ℤ_[p], z ^ n = u := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  set F : Polynomial ℤ_[p] := Polynomial.X ^ n - Polynomial.C u
  have hF1 : F.aeval (1 : ℤ_[p]) = 1 - u := by simp [F]
  have hF1' : F.derivative.aeval (1 : ℤ_[p]) = n := by simp [F, Polynomial.derivative_X_pow]
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hF1, hF1', norm_natCast_padicInt p hn.ne', norm_sub_rev, ← zpow_natCast, ← zpow_mul]
    refine hu.trans_lt (zpow_lt_zpow_right₀ hp1 ?_)
    push_cast
    omega
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  simpa [F, sub_eq_zero] using hz

/-! ### The decomposition `x = p ^ a u` -/

theorem exists_eq_zpow_mul_unit (x : ℚ_[p]ˣ) :
    ∃ (a : ℤ) (u : ℤ_[p]ˣ), (x : ℚ_[p]) = (p : ℚ_[p]) ^ a * ((u : ℤ_[p]) : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set v := (x : ℚ_[p]).valuation
  have hy : ‖(x : ℚ_[p]) * (p : ℚ_[p]) ^ (-v)‖ = 1 := by
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation x.ne_zero, Padic.norm_p_zpow,
      ← zpow_add₀ hpR.ne']
    simp [v]
  refine ⟨v, PadicInt.mkUnits hy, ?_⟩
  rw [PadicInt.mkUnits_eq, zpow_neg, mul_left_comm, mul_inv_cancel₀ (zpow_ne_zero _ hp0),
    mul_one]

/-- The valuation of a unit of `ℤ_p` is zero. -/
theorem valuation_unit (u : ℤ_[p]ˣ) : ((u : ℤ_[p]) : ℚ_[p]).valuation = 0 := by
  have h1 : 0 ≤ ((u : ℤ_[p]) : ℚ_[p]).valuation :=
    (Padic.norm_le_one_iff_val_nonneg _).1 (PadicInt.norm_le_one _)
  have h2 : 0 ≤ (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]).valuation :=
    (Padic.norm_le_one_iff_val_nonneg _).1 (PadicInt.norm_le_one _)
  have h0 : ∀ w : ℤ_[p]ˣ, ((w : ℤ_[p]) : ℚ_[p]) ≠ 0 := fun w h ↦
    w.ne_zero (Subtype.ext (h.trans PadicInt.coe_zero.symm))
  have h3 := Padic.valuation_mul (h0 u) (h0 u⁻¹)
  rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, Padic.valuation_one] at h3
  omega

/-! ### The Artin map of an abelian layer, read in its Galois group -/

section ArtinGal

variable (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] M] [IsGalois ℚ_[p] M]
  [IsMulCommutative Gal(M/ℚ_[p])]

/-- The local Artin map of a finite abelian extension `M ⊆ (AlgebraicClosure ℚ_[p])` of `ℚ_p`, read in `Gal(M/ℚ_p)`. -/
def artinGal : ℚ_[p]ˣ →* Gal(M/ℚ_[p]) :=
  (Abelianization.equivOfComm (H := Gal(M/ℚ_[p]))).symm.toMonoidHom.comp
    (MonoidHom.toAdditive.symm (localArtinMap ℚ_[p] M (sepIncl p M)))

theorem localArtinMap_eq_artinGal (y : ℚ_[p]ˣ) :
    localArtinMap ℚ_[p] M (sepIncl p M) (Additive.ofMul y) =
      Additive.ofMul (Abelianization.of (artinGal p M y)) := by
  change _ = Additive.ofMul (Abelianization.equivOfComm (Abelianization.equivOfComm.symm _))
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem artinGal_eq_one_of_mem {y : ℚ_[p]ˣ} (hy : y ∈ normGroup ℚ_[p] M) :
    artinGal p M y = 1 := by
  have h := (localArtinMap_eq_zero_iff ℚ_[p] M (sepIncl p M) y).2 hy
  rw [localArtinMap_eq_artinGal] at h
  have h' : Abelianization.of (artinGal p M y) = 1 := by
    have := congrArg Additive.toMul h
    simpa using this
  exact (Abelianization.equivOfComm (H := Gal(M/ℚ_[p]))).injective (by simpa using h')

end ArtinGal

/-! ### A cyclotomic norm group consists of `n`-th powers -/

theorem coprime_self_pow_sub_one {n : ℕ} (hn : 0 < n) : p.Coprime (p ^ n - 1) := by
  have hp := (Fact.out : p.Prime)
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.pos
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ hp.one_lt.ne' (Nat.dvd_one.1 ?_)
  have := Nat.dvd_sub (dvd_pow_self p hn.ne') h
  rwa [Nat.sub_sub_self h1] at this

/-- An automorphism fixing `η` has all its integral powers fixing `η`. -/
theorem zpow_apply_eq_self {K E : Type*} [Field K] [Field E] [Algebra K E] {g : E ≃ₐ[K] E}
    {η : E} (hg : g η = η) (q : ℤ) : (g ^ q) η = η := by
  have hmem : g ∈ MulAction.stabilizer (E ≃ₐ[K] E) η := hg
  exact Subgroup.zpow_mem _ hmem q

/-- **Every norm from `ℚ_p(ζ_m)`, `m = p^(2 v_p(n) + 1) (pⁿ − 1)`, is an `n`-th power.** -/
theorem normGroup_cyclotomic_le_powerSubgroup {n : ℕ} (hn : 0 < n) {ζ : (AlgebraicClosure ℚ_[p])}
    (hζ : IsPrimitiveRoot ζ (p ^ (2 * padicValNat p n + 1) * (p ^ n - 1))) :
    normGroup ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ}) ≤ powerSubgroup ℚ_[p]ˣ n := by
  have hp := (Fact.out : p.Prime)
  set k := 2 * padicValNat p n + 1 with hk
  set m := p ^ k * (p ^ n - 1) with hm
  have hpn1 : 0 < p ^ n - 1 := by
    have : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.one_lt
    omega
  have hpk : 0 < p ^ k := Nat.pow_pos hp.pos
  have : NeZero m := ⟨(Nat.mul_pos hpk hpn1).ne'⟩
  set M := IntermediateField.adjoin ℚ_[p] {ζ}
  have : IsCyclotomicExtension {m} ℚ_[p] M := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
  have : FiniteDimensional ℚ_[p] M := IsCyclotomicExtension.finiteDimensional {m} ℚ_[p] M
  have : IsGalois ℚ_[p] M := IsCyclotomicExtension.isGalois {m} ℚ_[p] M
  have : IsMulCommutative Gal(M/ℚ_[p]) := IsCyclotomicExtension.isMulCommutative {m} ℚ_[p] M
  set ζ' : M := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ⟩
  have hζ' : IsPrimitiveRoot ζ' m := IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ
  intro x hx
  set R := artinGal p M
  have hR : R x = 1 := artinGal_eq_one_of_mem p M hx
  obtain ⟨a, u, hxu⟩ := exists_eq_zpow_mul_unit p x
  -- (i) the unit part is `≡ 1 mod p ^ k`
  set ζ1 : M := ζ' ^ (p ^ n - 1)
  have hζ1 : IsPrimitiveRoot ζ1 (p ^ k) := by
    have := hζ'.pow_of_dvd hpn1.ne' (Dvd.intro_left _ rfl)
    rwa [hm, Nat.mul_div_cancel _ hpn1] at this
  have hu1 : PadicInt.toZModPow k ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    have h := localArtinMap_cyclotomic_padic_primePow p M (sepIncl p M) hxu
      (localArtinMap_eq_artinGal p M x) hζ1.pow_eq_one
    rw [hR, AlgEquiv.one_apply] at h
    set v := (PadicInt.toZModPow k ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).val with hv
    have hk1 : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
    have hv0 : v ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at h
      exact hζ1.ne_one hk1 h
    have hζ10 : ζ1 ≠ 0 := hζ1.ne_zero (by omega)
    have h' : ζ1 ^ (v - 1) = 1 := by
      have : ζ1 ^ (v - 1) * ζ1 = 1 * ζ1 := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hv0), one_mul, ← h]
      exact mul_right_cancel₀ hζ10 this
    have hdvd : p ^ k ∣ v - 1 := hζ1.pow_eq_one_iff_dvd _ |>.1 h'
    have hcast : ((v : ℕ) : ZMod (p ^ k)) = 1 := by
      have := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hv0), sub_eq_zero, Nat.cast_one] at this
      exact this
    rwa [hv, ZMod.natCast_zmod_val] at hcast
  have hu2 : ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    have h1 : PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
      have := congrArg (PadicInt.toZModPow k) (congrArg Units.val (mul_inv_cancel u))
      rw [Units.val_mul, map_mul, hu1, mul_one, Units.val_one, map_one] at this
      exact this
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, h1, map_one, sub_self]
  obtain ⟨z, hz⟩ := exists_pow_eq_of_norm_sub_one_le p hn (u := u) (by simpa [hk] using hu2)
  have hzU : IsUnit z := (isUnit_pow_iff hn.ne').1 (hz ▸ u.isUnit)
  -- (ii) the valuation is divisible by `n`
  set η : M := ζ' ^ p ^ k
  have hη : IsPrimitiveRoot η (p ^ n - 1) := by
    have := hζ'.pow_of_dvd hpk.ne' (Dvd.intro _ rfl)
    rwa [hm, Nat.mul_div_cancel_left _ hpk] at this
  have hcop := coprime_self_pow_sub_one p hn
  set π : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 hp.ne_zero)
  set U : ℚ_[p]ˣ := Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  have hRπ : R π η = η ^ p := localArtinMap_cyclotomic_padic p M (sepIncl p M)
    (localArtinMap_eq_artinGal p M π) hcop hη.pow_eq_one
  have hπU : IsUniformizer ℚ_[p] (π * U) := by
    have h1 := Padic.isUniformizer_natCast_self p
    rw [isUniformizer_def] at h1 ⊢
    rw [map_mul, h1]
    have h2 : normalizedValuation ℚ_[p] U = 1 := by
      apply Multiplicative.toAdd.injective
      rw [_root_.Padic.toAdd_normalizedValuation_eq_valuation]
      exact valuation_unit p u
    rw [h2, mul_one]
  have hRπU : R (π * U) η = η ^ p := by
    have h := localArtinMap_cyclotomic_uniformizer ℚ_[p] M (sepIncl p M) hπU
      (localArtinMap_eq_artinGal p M (π * U)) (by rw [Padic.natCard_residueField]; exact hcop)
      hη.pow_eq_one
    rwa [Padic.natCard_residueField] at h
  have hRU : R U η = η := by
    rw [map_mul, AlgEquiv.mul_apply, ← hRπ] at hRπU
    exact (R π).injective hRπU
  have hx' : x = π ^ a * U := Units.ext <| by
    rw [hxu, Units.val_mul, Units.val_zpow_eq_zpow_val]
    rfl
  have hpow : ∀ j : ℕ, (R π ^ j) η = η ^ p ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hRπ, map_pow, ih, ← pow_mul, ← pow_succ]
  have hηn : (R π ^ n) η = η := by
    rw [hpow n]
    have : p ^ n = (p ^ n - 1) + 1 := by omega
    rw [this, pow_succ, hη.pow_eq_one, one_mul]
  have hηa : (R π ^ a) η = η := by
    have h := congrArg (fun g : Gal(M/ℚ_[p]) ↦ g η) hR
    simp only [AlgEquiv.one_apply] at h
    rw [hx', map_mul, map_zpow, AlgEquiv.mul_apply, hRU] at h
    exact h
  set q := a / n
  set r := a % n
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  have hrn : r < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
  have har : a = n * q + r := by
    have := Int.mul_ediv_add_emod a n
    linarith
  have hηr : (R π ^ r.toNat) η = η := by
    have h1 : R π ^ a = (R π ^ n) ^ q * R π ^ r.toNat := by
      rw [har, zpow_add, zpow_mul, zpow_natCast, ← zpow_natCast (R π) r.toNat,
        Int.toNat_of_nonneg hr0]
    have h2 := hηa
    rw [h1, AlgEquiv.mul_apply] at h2
    have h3 := zpow_apply_eq_self (K := ℚ_[p]) hηn (-q)
    have h4 := congrArg (DFunLike.coe ((R π ^ n) ^ (-q))) h2
    rwa [← AlgEquiv.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, AlgEquiv.one_apply,
      h3] at h4
  have hr : r = 0 := by
    rw [hpow] at hηr
    have hη0 : η ≠ 0 := hη.ne_zero hpn1.ne'
    have hpr : 1 ≤ p ^ r.toNat := Nat.one_le_pow _ _ hp.pos
    have h' : η ^ (p ^ r.toNat - 1) = 1 := by
      have : η ^ (p ^ r.toNat - 1) * η = 1 * η := by
        rw [← pow_succ, Nat.sub_add_cancel hpr, one_mul, hηr]
      exact mul_right_cancel₀ hη0 this
    have hdvd := (hη.pow_eq_one_iff_dvd _).1 h'
    have hlt : p ^ r.toNat - 1 < p ^ n - 1 := by
      have : p ^ r.toNat < p ^ n := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega
    have h0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    have h1 : p ^ r.toNat = 1 := by omega
    rcases Nat.pow_eq_one.1 h1 with h | h
    · exact absurd h hp.ne_one
    · omega
  -- conclusion
  rw [mem_powerSubgroup_iff]
  refine ⟨π ^ q * Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom hzU.unit, ?_⟩
  rw [mul_pow, ← map_pow, hx', har, hr, add_zero]
  congr 1
  · rw [← zpow_natCast, ← zpow_mul, mul_comm]
  · congr 1
    ext
    simp [hz]

/-! ### Local Kronecker–Weber -/

/-- **Local Kronecker–Weber for `ℚ_p`.** Every finite abelian extension of `ℚ_p` inside
`(AlgebraicClosure ℚ_[p])` lies in the field generated by the `m`-th roots of unity for some
`m ≥ 1`. -/
theorem le_adjoin_rootsOfUnity (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] L]
    [IsGalois ℚ_[p] L] [IsMulCommutative Gal(L/ℚ_[p])] :
    ∃ m : ℕ, 0 < m ∧ L ≤ IntermediateField.adjoin ℚ_[p] {x : (AlgebraicClosure ℚ_[p]) | x ^ m = 1} := by
  have hp := (Fact.out : p.Prime)
  set n := Module.finrank ℚ_[p] L
  have hn : 0 < n := Module.finrank_pos
  set m := p ^ (2 * padicValNat p n + 1) * (p ^ n - 1)
  have hm : 0 < m := by
    have : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.one_lt
    exact Nat.mul_pos (Nat.pow_pos hp.pos) (by omega)
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ_[p]) m
  have : IsCyclotomicExtension {m} ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ}) :=
    IsCyclotomicExtension.finiteDimensional {m} ℚ_[p] _
  have : IsGalois ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ}) :=
    IsCyclotomicExtension.isGalois {m} ℚ_[p] _
  have hexp : Monoid.exponent Gal(L/ℚ_[p]) ∣ n := by
    rw [show n = Nat.card Gal(L/ℚ_[p]) from
      (IsGalois.card_aut_eq_finrank (F := ℚ_[p]) (E := L)).symm]
    exact Group.exponent_dvd_nat_card
  have hle : L ≤ IntermediateField.adjoin ℚ_[p] {ζ} :=
    le_of_normGroup_le p L _ ((normGroup_cyclotomic_le_powerSubgroup p hn hζ).trans
      (powerSubgroup_le_normGroup_of_exponent_dvd ℚ_[p] L hexp))
  refine ⟨m, hm, hle.trans ?_⟩
  rw [IntermediateField.adjoin_simple_le_iff]
  exact IntermediateField.subset_adjoin _ _ hζ.pow_eq_one

end ZInQ.Contrib.LocalKW

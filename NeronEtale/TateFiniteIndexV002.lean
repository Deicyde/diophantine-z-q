import ZInQKernel.HDecomp.Objects

/-!
# Finite-index subgroups have the same `ℓ`-adic Tate module, for every prime `ℓ`

`PkgI3.Tate.T ℓ M` is the group of sequences `(xₙ)` with `x₀ = 0`, `ℓ • xₙ₊₁ = xₙ`.

* `tate_iter`: `xₙ = ℓ^k • xₙ₊ₖ`.
* `tate_eq_zero_of_finite`: `T_ℓ(Q) = 0` for a finite group `Q`. The coordinate `y = x_{n+c}`,
  `c = #Q`, has order dividing both `ℓ^{n+c}` and `c`, hence a power `ℓ^a` with `ℓ^a ≤ c`, so
  `a < c` and `ℓ^c • y = 0`; then `xₙ = ℓ^c • y = 0`. No coprimality of `ℓ` with `#Q` is used.
* `tate_bijective_of_exact`: for `0 → M →ⁱ N →^q Q` exact at `N` with `i` injective and `Q`
  finite, `T_ℓ(i)` is bijective. Every coordinate `tₙ` of `t ∈ T_ℓ(N)` maps to a coordinate of
  `T_ℓ(q) t ∈ T_ℓ(Q) = 0`, so `tₙ = i(sₙ)`; the relations `s₀ = 0`, `ℓ • sₙ₊₁ = sₙ` follow from
  injectivity of `i`.
* `tateEquivOfExact`, `tate_coord_eq`, `range_coord_eq_image`: the `ℤ_ℓ`-linear equivalence, and
  the coordinate identity: the level-`n` coordinates of `T_ℓ(N)` are exactly `i` applied to the
  level-`n` coordinates of `T_ℓ(M)`.
* Instances: an additive subgroup quotient (`tate_bijective_of_finite_quotient`) and the
  multiplicative form for commutative groups of points with `i.range.FiniteIndex`
  (`tate_bijective_of_finiteIndex_mul`, `tateMulEquivOfFiniteIndex`, `tate_coord_eq_mul`).

Neither surjectivity of `i` on finite-level torsion nor coprimality of `ℓ` with the index is
assumed (both fail in general: `ℓ`-primary components change `N[ℓⁿ]`, not `T_ℓ`).
-/

noncomputable section
set_option autoImplicit false

namespace FiniteIndexTate

theorem lt_pow_of_two_le {ℓ : ℕ} (h : 2 ≤ ℓ) : ∀ a : ℕ, a < ℓ ^ a
  | 0 => by simp
  | a + 1 => by
    have ih := lt_pow_of_two_le h a
    rw [pow_succ]
    nlinarith

section General

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- `xₙ = ℓ^k • xₙ₊ₖ` on `T_ℓ`. -/
theorem tate_iter {Q : Type*} [AddCommGroup Q] (t : PkgI3.Tate.T ℓ Q) (n k : ℕ) :
    t.1 n = (ℓ ^ k) • t.1 (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, pow_succ, mul_smul, ← Nat.add_assoc, t.2.2 (n + k)]

/-- **`T_ℓ` of a finite group vanishes** (every prime `ℓ`). -/
theorem tate_eq_zero_of_finite {Q : Type*} [AddCommGroup Q] [Finite Q] (t : PkgI3.Tate.T ℓ Q) :
    t = 0 := by
  apply Subtype.ext
  funext n
  set c := Nat.card Q with hc
  have hc0 : 0 < c := Nat.card_pos
  set y := t.1 (n + c) with hy
  have h1 : addOrderOf y ∣ ℓ ^ (n + c) :=
    addOrderOf_dvd_of_nsmul_eq_zero (PkgI3.Tate.pow_smul_eq_zero t.2 (n + c))
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hℓ.out).1 h1
  have h2 : ℓ ^ a ∣ c := by
    rw [← ha]
    exact addOrderOf_dvd_natCard y
  have h3 : ℓ ^ a ≤ c := Nat.le_of_dvd hc0 h2
  have h4 : a < ℓ ^ a := lt_pow_of_two_le hℓ.out.two_le a
  have h5 : addOrderOf y ∣ ℓ ^ c := by
    rw [ha]
    exact pow_dvd_pow ℓ (by omega)
  have h6 : (ℓ ^ c) • y = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.1 h5
  show t.1 n = (0 : PkgI3.Tate.T ℓ Q).1 n
  rw [tate_iter ℓ t n c, ← hy, h6]
  rfl

variable {M N Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]

/-- Every coordinate of `T_ℓ(N)` lies in the kernel of a map to a finite group. -/
theorem tate_coord_mem_ker (q : N →+ Q) [Finite Q] (t : PkgI3.Tate.T ℓ N) (n : ℕ) :
    q (t.1 n) = 0 := by
  have h := tate_eq_zero_of_finite ℓ (PkgI3.Tate.map q t)
  have h' : (PkgI3.Tate.map q t).1 n = (0 : PkgI3.Tate.T ℓ Q).1 n := by rw [h]
  exact h'

/-- **`T_ℓ(i)` is bijective** for `0 → M →ⁱ N →^q Q` exact at `N`, `i` injective, `Q` finite. -/
theorem tate_bijective_of_exact (i : M →+ N) (hi : Function.Injective i) (q : N →+ Q) [Finite Q]
    (hex : ∀ y : N, q y = 0 → ∃ x : M, i x = y) :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) i) := by
  constructor
  · intro s₁ s₂ h
    apply Subtype.ext
    funext n
    apply hi
    have h' := congrArg (fun s : PkgI3.Tate.T ℓ N => s.1 n) h
    simpa only [PkgI3.Tate.map_apply] using h'
  · intro t
    have hl : ∀ n, ∃ x : M, i x = t.1 n := fun n => hex _ (tate_coord_mem_ker ℓ q t n)
    choose s hs using hl
    have hs0 : s 0 = 0 := hi (by rw [hs, map_zero, t.2.1])
    have hss : ∀ n, ℓ • s (n + 1) = s n := fun n =>
      hi (by rw [map_nsmul, hs, hs, t.2.2 n])
    refine ⟨⟨s, hs0, hss⟩, ?_⟩
    apply Subtype.ext
    funext n
    exact hs n

/-- The `ℤ_ℓ`-linear equivalence `T_ℓ(M) ≃ T_ℓ(N)`. -/
def tateEquivOfExact (i : M →+ N) (hi : Function.Injective i) (q : N →+ Q) [Finite Q]
    (hex : ∀ y : N, q y = 0 → ∃ x : M, i x = y) :
    PkgI3.Tate.T ℓ M ≃ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ N :=
  LinearEquiv.ofBijective (PkgI3.Tate.map (ℓ := ℓ) i) (tate_bijective_of_exact ℓ i hi q hex)

/-- **Coordinate identity**: every level-`n` coordinate of `t ∈ T_ℓ(N)` is `i` of the level-`n`
coordinate of the corresponding element of `T_ℓ(M)`. -/
theorem tate_coord_eq (i : M →+ N) (hi : Function.Injective i) (q : N →+ Q) [Finite Q]
    (hex : ∀ y : N, q y = 0 → ∃ x : M, i x = y) (t : PkgI3.Tate.T ℓ N) (n : ℕ) :
    t.1 n = i (((tateEquivOfExact ℓ i hi q hex).symm t).1 n) := by
  have h := (tateEquivOfExact ℓ i hi q hex).apply_symm_apply t
  conv_lhs => rw [← h]
  rfl

/-- **The level-`n` coordinates of `T_ℓ(N)` are `i` of the level-`n` coordinates of `T_ℓ(M)`.** -/
theorem range_coord_eq_image (i : M →+ N) (hi : Function.Injective i) (q : N →+ Q) [Finite Q]
    (hex : ∀ y : N, q y = 0 → ∃ x : M, i x = y) (n : ℕ) :
    Set.range (fun t : PkgI3.Tate.T ℓ N => t.1 n) =
      i '' Set.range (fun s : PkgI3.Tate.T ℓ M => s.1 n) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨(tateEquivOfExact ℓ i hi q hex).symm t, rfl⟩,
      (tate_coord_eq ℓ i hi q hex t n).symm⟩
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨PkgI3.Tate.map i s, rfl⟩

/-- The additive form with the quotient by the image. -/
theorem tate_bijective_of_finite_quotient (i : M →+ N) (hi : Function.Injective i)
    [Finite (N ⧸ i.range)] : Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) i) :=
  tate_bijective_of_exact ℓ i hi (QuotientAddGroup.mk' i.range) (fun y hy => by
    have : y ∈ i.range := (QuotientAddGroup.eq_zero_iff y).1 hy
    exact this)

end General

section Mul

variable (ℓ : ℕ) [Fact ℓ.Prime] {M N : Type*} [CommGroup M] [CommGroup N]

/-- The quotient detector for a multiplicative finite-index image. -/
def quotDetector (i : M →* N) : Additive N →+ Additive (N ⧸ i.range) :=
  MonoidHom.toAdditive (QuotientGroup.mk' i.range)

theorem quotDetector_exact (i : M →* N) (y : Additive N) (hy : quotDetector i y = 0) :
    ∃ x : Additive M, MonoidHom.toAdditive i x = y := by
  have h1 : (QuotientGroup.mk' i.range) (Additive.toMul y) = 1 := hy
  have h2 : Additive.toMul y ∈ i.range := (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨x, hx⟩ := h2
  exact ⟨Additive.ofMul x, hx⟩

/-- **All-`ℓ` finite-index Tate bijection for commutative groups.** -/
theorem tate_bijective_of_finiteIndex_mul (i : M →* N) (hi : Function.Injective i)
    [i.range.FiniteIndex] :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) (MonoidHom.toAdditive i)) := by
  haveI : Finite (N ⧸ i.range) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (Additive (N ⧸ i.range)) := inferInstanceAs (Finite (N ⧸ i.range))
  exact tate_bijective_of_exact ℓ (MonoidHom.toAdditive i) hi (quotDetector i)
    (quotDetector_exact i)

/-- The `ℤ_ℓ`-linear equivalence `T_ℓ(M) ≃ T_ℓ(N)` for a finite-index injective homomorphism. -/
def tateMulEquivOfFiniteIndex (i : M →* N) (hi : Function.Injective i) [i.range.FiniteIndex] :
    PkgI3.Tate.T ℓ (Additive M) ≃ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ (Additive N) :=
  LinearEquiv.ofBijective _ (tate_bijective_of_finiteIndex_mul ℓ i hi)

/-- **Coordinate identity, multiplicative form**: `tₙ = i(sₙ)` with `s` the preimage of `t`. -/
theorem tate_coord_eq_mul (i : M →* N) (hi : Function.Injective i) [i.range.FiniteIndex]
    (t : PkgI3.Tate.T ℓ (Additive N)) (n : ℕ) :
    Additive.toMul (t.1 n) =
      i (Additive.toMul (((tateMulEquivOfFiniteIndex ℓ i hi).symm t).1 n)) := by
  have h := (tateMulEquivOfFiniteIndex ℓ i hi).apply_symm_apply t
  conv_lhs => rw [← h]
  rfl

/-- **Coordinate image identity, multiplicative form.** -/
theorem range_coord_eq_image_mul (i : M →* N) (hi : Function.Injective i) [i.range.FiniteIndex]
    (n : ℕ) :
    Set.range (fun t : PkgI3.Tate.T ℓ (Additive N) => Additive.toMul (t.1 n)) =
      i '' Set.range (fun s : PkgI3.Tate.T ℓ (Additive M) => Additive.toMul (s.1 n)) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨(tateMulEquivOfFiniteIndex ℓ i hi).symm t, rfl⟩,
      (tate_coord_eq_mul ℓ i hi t n).symm⟩
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨PkgI3.Tate.map (MonoidHom.toAdditive i) s, rfl⟩

end Mul

end FiniteIndexTate

#check @FiniteIndexTate.tate_eq_zero_of_finite
#check @FiniteIndexTate.tate_bijective_of_exact
#check @FiniteIndexTate.range_coord_eq_image
#check @FiniteIndexTate.tate_bijective_of_finiteIndex_mul
#check @FiniteIndexTate.tate_coord_eq_mul
#check @FiniteIndexTate.range_coord_eq_image_mul
#print axioms FiniteIndexTate.tate_eq_zero_of_finite
#print axioms FiniteIndexTate.tate_bijective_of_exact
#print axioms FiniteIndexTate.range_coord_eq_image
#print axioms FiniteIndexTate.tate_bijective_of_finite_quotient
#print axioms FiniteIndexTate.tate_bijective_of_finiteIndex_mul
#print axioms FiniteIndexTate.tate_coord_eq_mul
#print axioms FiniteIndexTate.range_coord_eq_image_mul

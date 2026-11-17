import Mathlib

/-!
# Lane RC16-uniform: height-one regularity, the quadratic case at `(t)` and `(t+2)`

Formalizes the algebra of the paragraph "Height-one regularity, including quadratic
specializations" of Elliot Glazer's proof of Theorem 5.3 (manuscript lines 4976-5136), in the
manuscript's order:

1. quadraticity, lines 5004-5009: `quadratic_iff`, `prime_of_quadratic`;
2. `W_+` and `W_-` are not isomorphic, lines 5019-5026: `sign_intertwiner_zero`;
3. the sign planes, lines 5035-5054 and 5083-5085: `weil_J_symm`, `exists_J_eigenbasis`,
   `sign_planes_hyperbolic`, `isotropic_axis`, `selfAnnihilating_eq_axis`;
4. the bookkeeping with (5.5a), lines 5072-5086 and 5116-5136: `bookkeeping_mixed`,
   `bookkeeping_single_sign`;
5. (5.5b) and the polarization, lines 5087-5115: `eval_tau_h_sq`, `polarization_exists`,
   `exists_both_coords_ne_zero`.

Every theorem here is PROVED. The base field `k` is an arbitrary field. Where the manuscript
uses "`k` has characteristic zero", the only consequence used is `(2 : k) ≠ 0`, taken as a
hypothesis exactly where it is needed. Characteristic zero gives it (see the `example` after
`quadratic_iff`). Quadraticity (item 1) and (5.5b) need no hypothesis on `2`.

Conventions. The Tate plane is `T = Fin 2 → k` with `e₂ x y = det [x; y]`. The local
cohomology at a new inert derivative prime is `F ⊕ S = T × T` (first factor finite, second
singular). `J : T →ₗ[k] T` is `ρ_T(τ)`. For `f s : T`, `signPlane f s = F(f) ⊕ S(s)`, with
axes `finAxis f = F(f)` and `singAxis s = S(s)`. So `H_+ = signPlane e₊ e₋` and
`H_- = signPlane e₋ e₊`.
-/

namespace ZInQ.Manuscript.RC.Uniform
namespace QuadraticCase

open Module

section Quadraticity

/-- Lines 5004-5006, PROVED. In any commutative ring, `(1+t)^2 = 1 ↔ t(t+2) = 0`
("quadraticity implies `t(t+2)=0`"): `(1+t)^2 - 1 = t(t+2)`. -/
theorem quadratic_iff_mul {A : Type*} [CommRing A] (t : A) :
    (1 + t) ^ 2 = 1 ↔ t * (t + 2) = 0 := by
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- Lines 5004-5006, PROVED. **Quadraticity.** In a domain, `(1+t)^2 = 1` iff `t = 0` or
`t = -2`. Here `1+t` is the value of the specialized character on the moving inertia
generator, so quadraticity means `(1+t)^2 = 1` in `k`. No hypothesis on `2` is needed. -/
theorem quadratic_iff {A : Type*} [CommRing A] [IsDomain A] (t : A) :
    (1 + t) ^ 2 = 1 ↔ t = 0 ∨ t = -2 := by
  rw [quadratic_iff_mul, mul_eq_zero, add_eq_zero_iff_eq_neg]

/-- Lines 5005-5007, PROVED. **The only possible primes are `(t)` and `(t+2)`.** For a
prime ideal `𝔭` of a commutative ring with `(1+t)^2 - 1 ∈ 𝔭`, `t ∈ 𝔭` or `t + 2 ∈ 𝔭`.
DEPARTURE: the conclusion is stated as membership, `𝔭 ⊇ (t)` or `𝔭 ⊇ (t+2)`. The equality
`𝔭 = (t)` or `𝔭 = (t+2)` for a height-one `𝔭` also needs `(t)` and `(t+2)` to be height-one
primes of `Λ`. That is not formalized here. -/
theorem prime_of_quadratic {R : Type*} [CommRing R] (𝔭 : Ideal R) [h𝔭 : 𝔭.IsPrime] (t : R)
    (h : (1 + t) ^ 2 - 1 ∈ 𝔭) : t ∈ 𝔭 ∨ t + 2 ∈ 𝔭 := by
  have e : (1 + t) ^ 2 - 1 = t * (t + 2) := by ring
  rw [e] at h
  exact h𝔭.mem_or_mem h

/-- Lines 5005-5007, PROVED. The same statement read in
`k = Frac(Λ/𝔭)`: if the image of `1+t` in `k` squares to `1`, then `t ∈ 𝔭` or `t + 2 ∈ 𝔭`. -/
theorem prime_of_quadratic_residueField {R : Type*} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (t : R)
    (h : (1 + algebraMap (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭)) (Ideal.Quotient.mk 𝔭 t)) ^ 2 = 1) :
    t ∈ 𝔭 ∨ t + 2 ∈ 𝔭 := by
  have hinj : Function.Injective (algebraMap (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭))) :=
    IsFractionRing.injective _ _
  rcases (quadratic_iff _).1 h with h0 | h2
  · left
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj
    simpa using h0
  · right
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj
    rw [map_add, map_add, h2, map_zero, map_ofNat, map_ofNat]
    ring

/-- Lines 5005-5007, PROVED. `prime_of_quadratic` for
`Λ = ℤ_2[[t]]` (`PowerSeries ℤ_[2]`) and `t = PowerSeries.X`. -/
theorem prime_of_quadratic_Lambda (𝔭 : Ideal (PowerSeries ℤ_[2])) [𝔭.IsPrime]
    (h : (1 + PowerSeries.X) ^ 2 - 1 ∈ 𝔭) :
    PowerSeries.X ∈ 𝔭 ∨ PowerSeries.X + 2 ∈ 𝔭 :=
  prime_of_quadratic 𝔭 _ h

-- The hypothesis of `prime_of_quadratic_Lambda` holds for `𝔭 = (t)`.
example : ∃ 𝔭 : Ideal (PowerSeries ℤ_[2]), 𝔭.IsPrime ∧
    (1 + PowerSeries.X) ^ 2 - 1 ∈ 𝔭 := by
  refine ⟨Ideal.span {PowerSeries.X}, PowerSeries.span_X_isPrime, ?_⟩
  have e : ((1 : PowerSeries ℤ_[2]) + PowerSeries.X) ^ 2 - 1
      = PowerSeries.X * (PowerSeries.X + 2) := by ring
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- Characteristic zero gives the only consequence used below, `(2 : k) ≠ 0`. -/
example {k : Type*} [Field k] [CharZero k] : (2 : k) ≠ 0 := two_ne_zero

end Quadraticity

section Intertwiner

/-- Lines 5021-5023, PROVED. "A scalar intertwining these two actions is zero since `2` is
invertible", as maps. Let `φ = c • id` intertwine `(W, J)` and `(W, -J)`, i.e.
`φ ∘ J = (-J) ∘ φ`, with `J` surjective and `2` a unit. Then `φ = 0`. Proof: `cJ = -cJ`, so
`2cJ = 0`. -/
theorem sign_intertwiner_zero_map {k W : Type*} [CommRing k] [AddCommGroup W] [Module k W]
    (h2 : IsUnit (2 : k)) (J : W →ₗ[k] W) (hJ : Function.Surjective J)
    (φ : W →ₗ[k] W) (hφ : φ ∘ₗ J = (-J) ∘ₗ φ) (hscalar : ∃ c : k, φ = c • LinearMap.id) :
    φ = 0 := by
  obtain ⟨c, rfl⟩ := hscalar
  ext w
  obtain ⟨v, rfl⟩ := hJ w
  have h := LinearMap.congr_fun hφ v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.neg_apply, map_smul] at h
  have h' : (2 : k) • (c • J v) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    rw [smul_neg]
    exact neg_add_cancel (c • J v)
  obtain ⟨u, hu⟩ := h2
  have h'' : (↑u⁻¹ : k) • ((2 : k) • (c • J v)) = 0 := by rw [h', smul_zero]
  rw [← hu, smul_smul, Units.inv_mul, one_smul] at h''
  simpa using h''

/-- Lines 5021-5023, PROVED. **Nonisomorphism of `W_±`, scalar form.** Let `W ≠ 0`,
`(2 : k) ≠ 0`, `J` invertible (surjective is enough) and `c • J = -(J ∘ c)`. Then `c = 0`. -/
theorem sign_intertwiner_zero {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Nontrivial W] (h2 : (2 : k) ≠ 0) (J : W →ₗ[k] W) (hJ : Function.Surjective J) (c : k)
    (hc : c • J = -(J ∘ₗ (c • LinearMap.id))) : c = 0 := by
  have hφ : (c • LinearMap.id : W →ₗ[k] W) ∘ₗ J = (-J) ∘ₗ (c • LinearMap.id) := by
    rw [LinearMap.smul_comp, LinearMap.id_comp, LinearMap.neg_comp, hc]
  have h0 := sign_intertwiner_zero_map (IsUnit.mk0 _ h2) J hJ _ hφ ⟨c, rfl⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have := LinearMap.congr_fun h0 w
  simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply,
    smul_eq_zero] at this
  exact this.resolve_right hw

/-- Lines 5019-5023, PROVED relative to Schur's lemma. **The summands are not isomorphic.**
`W_+` and `W_-` restrict to the same representation `ρ` of the index-two group, and `τ` acts by
`J` and `-J`. "An intertwiner restricts to a scalar": the hypothesis `hSchur` says every
`ρ`-endomorphism is a scalar. It is GLUE: it follows from the absolute irreducibility of lines
5017-5021, which is not formalized here. An isomorphism intertwining `J` with `-J` is then
zero, which is impossible on `W ≠ 0`. -/
theorem W_plus_not_iso_W_minus {k W G : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Nontrivial W] [Monoid G] (ρ : G →* (W →ₗ[k] W)) (h2 : (2 : k) ≠ 0) (J : W →ₗ[k] W)
    (hJ : Function.Surjective J)
    (hSchur : ∀ φ : W →ₗ[k] W, (∀ g, φ ∘ₗ ρ g = ρ g ∘ₗ φ) → ∃ c : k, φ = c • LinearMap.id)
    (e : W ≃ₗ[k] W) (he : ∀ g, (e : W →ₗ[k] W) ∘ₗ ρ g = ρ g ∘ₗ (e : W →ₗ[k] W))
    (heJ : (e : W →ₗ[k] W) ∘ₗ J = (-J) ∘ₗ (e : W →ₗ[k] W)) : False := by
  have h0 := sign_intertwiner_zero_map (IsUnit.mk0 _ h2) J hJ _ heJ (hSchur _ he)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have := LinearMap.congr_fun h0 w
  simp only [LinearEquiv.coe_coe, LinearMap.zero_apply] at this
  exact hw (e.injective (by rw [this, map_zero]))

end Intertwiner

section Exact

/-- How the dimension hypotheses of the bookkeeping theorems arise. A short exact
sequence `0 → A → B → C → 0` of finite-dimensional spaces gives
`dim B = dim A + dim C`. Applied to each sign part of (5.5a), this gives the hypotheses
`hVp`, `hVm`, `hVp'` and `hVm'` of `bookkeeping_mixed` and `bookkeeping_single_sign`. -/
theorem finrank_eq_of_shortExact {k A B C : Type*} [Field k] [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C] [FiniteDimensional k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    finrank k B = finrank k A + finrank k C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.2 hg, finrank_top, hfg.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj hf] at h1
  omega

end Exact

section SignPlanes

variable {k : Type*} [Field k]

/-- The determinant pairing `e₂(x,y) = det [x; y]` on `T = Fin 2 → k`. -/
def e₂ (x y : Fin 2 → k) : k := Matrix.det (Matrix.of ![x, y])

@[simp] lemma e₂_apply (x y : Fin 2 → k) : e₂ x y = x 0 * y 1 - x 1 * y 0 := by
  simp [e₂, Matrix.det_fin_two]

/-- Coordinates of `J y` through the matrix of `J`. -/
lemma J_apply (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (y : Fin 2 → k) (i : Fin 2) :
    J y i = LinearMap.toMatrix' J i 0 * y 0 + LinearMap.toMatrix' J i 1 * y 1 := by
  have hy : y = y 0 • (Pi.single 0 1 : Fin 2 → k) + y 1 • Pi.single 1 1 := by
    ext j; fin_cases j <;> simp
  conv_lhs => rw [hy]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.toMatrix'_apply]
  ring

/-- The entry identities given by `J^2 = 1`. -/
lemma J_entries (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hJ2 : J ∘ₗ J = LinearMap.id) :
    let M := LinearMap.toMatrix' J
    M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 ∧ M 1 0 * M 0 1 + M 1 1 * M 1 1 = 1 ∧
      M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 ∧ M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
  intro M
  have hM : M * M = 1 := by
    simp only [M]
    rw [← LinearMap.toMatrix'_comp, hJ2, LinearMap.toMatrix'_id]
  have e := fun i j => congrFun (congrFun hM i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using e 0 0
  · simpa using e 1 1
  · simpa using e 0 1
  · simpa using e 1 0

/-- `J^2 = 1` and `det J = -1` force `tr J = 0`. -/
lemma J_trace_zero (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hJ2 : J ∘ₗ J = LinearMap.id)
    (hdet : LinearMap.det J = -1) :
    LinearMap.toMatrix' J 0 0 + LinearMap.toMatrix' J 1 1 = 0 := by
  obtain ⟨e00, e11, -, -⟩ := J_entries J hJ2
  have hd : LinearMap.toMatrix' J 0 0 * LinearMap.toMatrix' J 1 1
      - LinearMap.toMatrix' J 0 1 * LinearMap.toMatrix' J 1 0 = -1 := by
    rw [← Matrix.det_fin_two, LinearMap.det_toMatrix', hdet]
  have hsq : (LinearMap.toMatrix' J 0 0 + LinearMap.toMatrix' J 1 1) ^ 2 = 0 := by
    linear_combination e00 + e11 + 2 * hd
  exact pow_eq_zero_iff (two_ne_zero) |>.1 hsq

/-- Lines 5042-5043, PROVED. **Symmetry.** "Since `det J = -1` and `J^2 = 1`,
`e₂(x,Jy) = e₂(y,Jx)`." The proof shows `tr J = 0` and uses
`e₂(x,Jy) - e₂(y,Jx) = tr J · e₂(x,y)`. It needs no hypothesis on `2`. -/
theorem weil_J_symm (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hJ2 : J ∘ₗ J = LinearMap.id)
    (hdet : LinearMap.det J = -1) (x y : Fin 2 → k) :
    e₂ x (J y) = e₂ y (J x) := by
  have htr := J_trace_zero J hJ2 hdet
  simp only [e₂_apply, J_apply J]
  linear_combination (x 0 * y 1 - x 1 * y 0) * htr


lemma e₂_self (x : Fin 2 → k) : e₂ x x = 0 := by rw [e₂_apply]; ring

lemma e₂_neg_right (x y : Fin 2 → k) : e₂ x (-y) = -e₂ x y := by
  simp only [e₂_apply, Pi.neg_apply]; ring

/-- Cramer's identity `e₂(u,v) x = e₂(x,v) u + e₂(u,x) v` in the plane. -/
lemma e₂_cramer (x u v : Fin 2 → k) : e₂ u v • x = e₂ x v • u + e₂ u x • v := by
  ext j; fin_cases j <;> simp [e₂_apply] <;> ring

/-- If `e₂(u,v) = 0` and `u ≠ 0`, then `v` is a multiple of `u`. -/
lemma eq_smul_of_e₂_eq_zero {u v : Fin 2 → k} (hu : u ≠ 0) (h : e₂ u v = 0) :
    ∃ l : k, v = l • u := by
  rw [e₂_apply] at h
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1; apply hu; ext j; fin_cases j
      · simpa using h0
      · simpa using h1
    have hv0 : v 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at h
      exact h.resolve_left h1
    refine ⟨v 1 / u 1, ?_⟩
    ext j; fin_cases j
    · simp [hv0, h0]
    · simp [div_mul_cancel₀ _ h1]
  · refine ⟨v 0 / u 0, ?_⟩
    ext j; fin_cases j
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination h

/-- Nonzero `J`-eigenvectors for `1` and `-1` have `e₂ ≠ 0` (uses `2 ≠ 0`). -/
lemma e₂_ne_zero_of_eigen (h2 : (2 : k) ≠ 0) {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)}
    {u v : Fin 2 → k} (hu : u ≠ 0) (hv : v ≠ 0) (hpu : J u = u) (hmv : J v = -v) :
    e₂ u v ≠ 0 := by
  intro h0
  obtain ⟨l, rfl⟩ := eq_smul_of_e₂_eq_zero hu h0
  rw [map_smul, hpu] at hmv
  have h' : (2 : k) • (l • u) = 0 := by
    rw [two_smul]; nth_rewrite 1 [hmv]; exact neg_add_cancel _
  rcases smul_eq_zero.1 h' with h | h
  · exact h2 h
  · exact hv h

/-- `e₂(u,v) ≠ 0` gives linear independence. -/
lemma linIndep_of_e₂_ne_zero {u v : Fin 2 → k} (he : e₂ u v ≠ 0) :
    LinearIndependent k ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun z => e₂ z v) hst
  have h2 := congrArg (fun z => e₂ u z) hst
  simp only [e₂_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2
  rw [e₂_apply] at he
  constructor
  · have : s * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_right he
  · have : t * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination h2
    exact (mul_eq_zero.1 this).resolve_right he

/-- `J ≠ -1`, because `det(-1) = 1 ≠ -1` (uses `2 ≠ 0`). -/
lemma exists_add_J_ne_zero (h2 : (2 : k) ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hdet : LinearMap.det J = -1) : ∃ x : Fin 2 → k, x + J x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have a0 := congrFun (hcon (Pi.single 0 1)) 0
  have a1 := congrFun (hcon (Pi.single 0 1)) 1
  have b0 := congrFun (hcon (Pi.single 1 1)) 0
  have b1 := congrFun (hcon (Pi.single 1 1)) 1
  simp only [Pi.add_apply, J_apply J, Pi.zero_apply] at a0 a1 b0 b1
  simp at a0 a1 b0 b1
  have hd : LinearMap.toMatrix' J 0 0 * LinearMap.toMatrix' J 1 1
      - LinearMap.toMatrix' J 0 1 * LinearMap.toMatrix' J 1 0 = -1 := by
    rw [← Matrix.det_fin_two, LinearMap.det_toMatrix', hdet]
  simp only [LinearMap.toMatrix'_apply] at hd
  apply h2
  linear_combination hd - (1 + J (Pi.single 1 1) 1) * a0 + a0 + b1 + J (Pi.single 0 1) 1 * b0

/-- `J ≠ 1`, because `det 1 = 1 ≠ -1` (uses `2 ≠ 0`). -/
lemma exists_sub_J_ne_zero (h2 : (2 : k) ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hdet : LinearMap.det J = -1) : ∃ x : Fin 2 → k, x - J x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have a0 := congrFun (hcon (Pi.single 0 1)) 0
  have a1 := congrFun (hcon (Pi.single 0 1)) 1
  have b0 := congrFun (hcon (Pi.single 1 1)) 0
  have b1 := congrFun (hcon (Pi.single 1 1)) 1
  simp only [Pi.sub_apply, J_apply J, Pi.zero_apply] at a0 a1 b0 b1
  simp at a0 a1 b0 b1
  have hd : LinearMap.toMatrix' J 0 0 * LinearMap.toMatrix' J 1 1
      - LinearMap.toMatrix' J 0 1 * LinearMap.toMatrix' J 1 0 = -1 := by
    rw [← Matrix.det_fin_two, LinearMap.det_toMatrix', hdet]
  simp only [LinearMap.toMatrix'_apply] at hd
  apply h2
  linear_combination hd - (1 - J (Pi.single 1 1) 1) * a0 + a0 + b1 + J (Pi.single 0 1) 1 * b0

/-- Lines 5043-5044, PROVED. **Eigenbasis.** "Choose nonzero `J`-eigenvectors `e_+, e_-`.
They form a basis and `e₂(e_+,e_-) ≠ 0`." Let `J^2 = 1`, `det J = -1` and `(2 : k) ≠ 0`. Then
there are `e₊ ≠ 0` with `J e₊ = e₊` and `e₋ ≠ 0` with `J e₋ = -e₋`, linearly independent and
spanning `T`, with `e₂(e₊,e₋) ≠ 0`. The witnesses are `e₊ = x + Jx` and `e₋ = y - Jy`. -/
theorem exists_J_eigenbasis (h2 : (2 : k) ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJ2 : J ∘ₗ J = LinearMap.id) (hdet : LinearMap.det J = -1) :
    ∃ ep em : Fin 2 → k, ep ≠ 0 ∧ em ≠ 0 ∧ J ep = ep ∧ J em = -em ∧ e₂ ep em ≠ 0 ∧
      LinearIndependent k ![ep, em] ∧ Submodule.span k {ep, em} = ⊤ := by
  obtain ⟨x, hx⟩ := exists_add_J_ne_zero h2 J hdet
  obtain ⟨y, hy⟩ := exists_sub_J_ne_zero h2 J hdet
  have hJJ : ∀ z, J (J z) = z := fun z => LinearMap.congr_fun hJ2 z
  have hp : J (x + J x) = x + J x := by rw [map_add, hJJ, add_comm]
  have hm : J (y - J y) = -(y - J y) := by rw [map_sub, hJJ, neg_sub]
  have he := e₂_ne_zero_of_eigen h2 hx hy hp hm
  have hli := linIndep_of_e₂_ne_zero he
  refine ⟨x + J x, y - J y, hx, hy, hp, hm, he, hli, ?_⟩
  have := hli.span_eq_top_of_card_eq_finrank (by simp)
  rwa [Matrix.range_cons_cons_empty] at this


/-- Line 5037: the transported cross pairing `β(x,y) = ε e₂(x,Jy)`, for `x ∈ F` and `y ∈ S`. -/
def crossPair (ε : k) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (x y : Fin 2 → k) : k :=
  ε * e₂ x (J y)

/-- The symmetric local pairing on `F ⊕ S` with isotropic `F` and `S` and cross
pairing `β`: `⟨(x,y),(x',y')⟩ = β(x,y') + β(x',y)`. -/
def localPair (ε : k) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (u w : (Fin 2 → k) × (Fin 2 → k)) : k :=
  crossPair ε J u.1 w.2 + crossPair ε J w.1 u.2

/-- `signPlane f s = F(f) ⊕ S(s) ⊆ F ⊕ S`. Here `H_+ = signPlane e₊ e₋` and
`H_- = signPlane e₋ e₊` (line 5047). -/
def signPlane (f s : Fin 2 → k) : Submodule k ((Fin 2 → k) × (Fin 2 → k)) :=
  (k ∙ f).prod (k ∙ s)

/-- The finite axis `F(f) = k·(f,0)` of a sign plane. -/
def finAxis (f : Fin 2 → k) : Submodule k ((Fin 2 → k) × (Fin 2 → k)) :=
  (k ∙ f).prod ⊥

/-- The singular axis `S(s) = k·(0,s)` of a sign plane. -/
def singAxis (s : Fin 2 → k) : Submodule k ((Fin 2 → k) × (Fin 2 → k)) :=
  (⊥ : Submodule k (Fin 2 → k)).prod (k ∙ s)

variable {ε : k} {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)}

lemma crossPair_smul (a b : k) (x y : Fin 2 → k) :
    crossPair ε J (a • x) (b • y) = a * b * crossPair ε J x y := by
  simp only [crossPair, map_smul, e₂_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma crossPair_add_left (x x' y : Fin 2 → k) :
    crossPair ε J (x + x') y = crossPair ε J x y + crossPair ε J x' y := by
  simp only [crossPair, e₂_apply, Pi.add_apply]; ring

lemma crossPair_add_right (x y y' : Fin 2 → k) :
    crossPair ε J x (y + y') = crossPair ε J x y + crossPair ε J x y' := by
  simp only [crossPair, map_add, e₂_apply, Pi.add_apply]; ring

lemma crossPair_smul_left (a : k) (x y : Fin 2 → k) :
    crossPair ε J (a • x) y = a * crossPair ε J x y := by
  simpa using crossPair_smul (ε := ε) (J := J) a 1 x y

lemma crossPair_smul_right (a : k) (x y : Fin 2 → k) :
    crossPair ε J x (a • y) = a * crossPair ε J x y := by
  simpa using crossPair_smul (ε := ε) (J := J) 1 a x y

lemma localPair_symm (u w : (Fin 2 → k) × (Fin 2 → k)) :
    localPair ε J u w = localPair ε J w u := by
  unfold localPair; ring

lemma localPair_add_right (u w w' : (Fin 2 → k) × (Fin 2 → k)) :
    localPair ε J u (w + w') = localPair ε J u w + localPair ε J u w' := by
  simp only [localPair, Prod.fst_add, Prod.snd_add, crossPair_add_left, crossPair_add_right]
  ring

lemma localPair_smul_right (a : k) (u w : (Fin 2 → k) × (Fin 2 → k)) :
    localPair ε J u (a • w) = a * localPair ε J u w := by
  simp only [localPair, Prod.smul_fst, Prod.smul_snd, crossPair_smul_left, crossPair_smul_right]
  ring

lemma mem_signPlane {f s : Fin 2 → k} {u : (Fin 2 → k) × (Fin 2 → k)} :
    u ∈ signPlane f s ↔ ∃ a b : k, u = (a • f, b • s) := by
  simp only [signPlane, Submodule.mem_prod, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; exact ⟨a, b, Prod.ext ha.symm hb.symm⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩

lemma mem_finAxis {f : Fin 2 → k} {u : (Fin 2 → k) × (Fin 2 → k)} :
    u ∈ finAxis f ↔ ∃ a : k, u = (a • f, 0) := by
  simp only [finAxis, Submodule.mem_prod, Submodule.mem_span_singleton, Submodule.mem_bot]
  constructor
  · rintro ⟨⟨a, ha⟩, hb⟩; exact ⟨a, Prod.ext ha.symm hb⟩
  · rintro ⟨a, rfl⟩; exact ⟨⟨a, rfl⟩, rfl⟩

lemma mem_singAxis {s : Fin 2 → k} {u : (Fin 2 → k) × (Fin 2 → k)} :
    u ∈ singAxis s ↔ ∃ b : k, u = (0, b • s) := by
  simp only [singAxis, Submodule.mem_prod, Submodule.mem_span_singleton, Submodule.mem_bot]
  constructor
  · rintro ⟨ha, ⟨b, hb⟩⟩; exact ⟨b, Prod.ext ha hb.symm⟩
  · rintro ⟨b, rfl⟩; exact ⟨rfl, ⟨b, rfl⟩⟩

lemma finAxis_le_signPlane (f s : Fin 2 → k) : finAxis f ≤ signPlane f s := by
  intro u hu
  obtain ⟨a, rfl⟩ := mem_finAxis.1 hu
  exact mem_signPlane.2 ⟨a, 0, by simp⟩

lemma singAxis_le_signPlane (f s : Fin 2 → k) : singAxis s ≤ signPlane f s := by
  intro u hu
  obtain ⟨b, rfl⟩ := mem_singAxis.1 hu
  exact mem_signPlane.2 ⟨0, b, by simp⟩

lemma finAxis_eq_span (f : Fin 2 → k) :
    finAxis f = k ∙ ((f, 0) : (Fin 2 → k) × (Fin 2 → k)) := by
  ext u
  rw [mem_finAxis, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩

lemma singAxis_eq_span (s : Fin 2 → k) :
    singAxis s = k ∙ ((0, s) : (Fin 2 → k) × (Fin 2 → k)) := by
  ext u
  rw [mem_singAxis, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩

lemma finrank_finAxis {f : Fin 2 → k} (hf : f ≠ 0) : finrank k (finAxis f) = 1 := by
  rw [finAxis_eq_span]
  exact finrank_span_singleton (by simpa using hf)

lemma finrank_singAxis {s : Fin 2 → k} (hs : s ≠ 0) : finrank k (singAxis s) = 1 := by
  rw [singAxis_eq_span]
  exact finrank_span_singleton (by simpa using hs)

lemma finAxis_inf_singAxis (f s : Fin 2 → k) : finAxis f ⊓ singAxis s = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨a, rfl⟩ := mem_finAxis.1 (Submodule.mem_inf.1 hu).1
  obtain ⟨b, hb⟩ := mem_singAxis.1 (Submodule.mem_inf.1 hu).2
  rw [Submodule.mem_bot]
  simp only [Prod.mk.injEq] at hb
  rw [hb.1]; rfl

/-- On `F(f) ⊕ S(s)`: `⟨(af,bs),(a'f,b's)⟩ = (ab' + a'b) β(f,s)`. -/
lemma localPair_plane (a b a' b' : k) (f s : Fin 2 → k) :
    localPair ε J (a • f, b • s) (a' • f, b' • s) = (a * b' + a' * b) * crossPair ε J f s := by
  simp only [localPair, crossPair_smul]; ring

/-- Line 5051: the self-pairing of `aF(f) + bS(s)` is `2ab · β(f,s)`. -/
lemma localPair_self (a b : k) (f s : Fin 2 → k) :
    localPair ε J (a • f, b • s) (a • f, b • s) = 2 * a * b * crossPair ε J f s := by
  rw [localPair_plane]; ring

lemma ne_zero_of_crossPair_ne_zero {f s : Fin 2 → k} (hκ : crossPair ε J f s ≠ 0) :
    f ≠ 0 ∧ s ≠ 0 := by
  constructor
  · rintro rfl; apply hκ; simp [crossPair, e₂_apply]
  · rintro rfl; apply hκ; simp [crossPair, e₂_apply]

/-- A sign plane with `β(f,s) ≠ 0` is nondegenerate. -/
lemma signPlane_nondegenerate {f s : Fin 2 → k} (hκ : crossPair ε J f s ≠ 0)
    (u : (Fin 2 → k) × (Fin 2 → k)) (hu : u ∈ signPlane f s)
    (H : ∀ w ∈ signPlane f s, localPair ε J u w = 0) : u = 0 := by
  obtain ⟨a, b, rfl⟩ := mem_signPlane.1 hu
  have h1 := H ((1 : k) • f, (0 : k) • s) (mem_signPlane.2 ⟨1, 0, rfl⟩)
  have h2 := H ((0 : k) • f, (1 : k) • s) (mem_signPlane.2 ⟨0, 1, rfl⟩)
  rw [localPair_plane] at h1 h2
  have hb : b = 0 := by
    have : b * crossPair ε J f s = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_right hκ
  have ha : a = 0 := by
    have : a * crossPair ε J f s = 0 := by linear_combination h2
    exact (mul_eq_zero.1 this).resolve_right hκ
  simp [ha, hb]

lemma crossPair_plus_minus (ep em : Fin 2 → k) (hm : J em = -em) :
    crossPair ε J ep em = -(ε * e₂ ep em) := by
  rw [crossPair, hm, e₂_neg_right]; ring

lemma crossPair_minus_plus (ep em : Fin 2 → k) (hp : J ep = ep) :
    crossPair ε J em ep = -(ε * e₂ ep em) := by
  rw [crossPair, hp]; simp only [e₂_apply]; ring

/-- Lines 5045-5052, PROVED. **The two local cohomology signs.** Let `J e₊ = e₊`,
`J e₋ = -e₋`, `e₂(e₊,e₋) ≠ 0` and `ε ≠ 0`. With `H_+ = F(e_+) ⊕ S(e_-)` and
`H_- = F(e_-) ⊕ S(e_+)`, the following hold. The pairing is symmetric. `H_+ ⊥ H_-`. Each
`H_±` is nondegenerate. "In either plane the self-pairing of `aF(e_±)+bS(e_∓)` is `2ab` times
a nonzero constant." The constant is the same for both planes:
`κ = β(e₊,e₋) = β(e₋,e₊) = -ε e₂(e₊,e₋)`, matching `weil_J_symm`.
DEPARTURE: the eigenvectors are hypotheses (`exists_J_eigenbasis` supplies them), so
`J^2 = 1` and `det J = -1` are not needed again. The isotropy of `F` and `S` is built into
`localPair`. In the manuscript it comes from the retained local cup-product identities. -/
theorem sign_planes_hyperbolic (ε : k) (hε : ε ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0) :
    (∀ u w, localPair ε J u w = localPair ε J w u) ∧
    (∀ u ∈ signPlane ep em, ∀ w ∈ signPlane em ep, localPair ε J u w = 0) ∧
    (∀ u ∈ signPlane ep em, (∀ w ∈ signPlane ep em, localPair ε J u w = 0) → u = 0) ∧
    (∀ u ∈ signPlane em ep, (∀ w ∈ signPlane em ep, localPair ε J u w = 0) → u = 0) ∧
    (∃ κ : k, κ ≠ 0 ∧ crossPair ε J ep em = κ ∧ crossPair ε J em ep = κ ∧ ∀ a b : k,
      localPair ε J (a • ep, b • em) (a • ep, b • em) = 2 * a * b * κ ∧
      localPair ε J (a • em, b • ep) (a • em, b • ep) = 2 * a * b * κ) := by
  have hκ : -(ε * e₂ ep em) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hε he)
  have hpm := crossPair_plus_minus (ε := ε) ep em hm
  have hmp := crossPair_minus_plus (ε := ε) ep em hp
  refine ⟨localPair_symm, ?_, ?_, ?_, ⟨_, hκ, hpm, hmp, fun a b => ?_⟩⟩
  · intro u hu w hw
    obtain ⟨a, b, rfl⟩ := mem_signPlane.1 hu
    obtain ⟨c, d, rfl⟩ := mem_signPlane.1 hw
    have hpp : crossPair ε J ep ep = 0 := by rw [crossPair, hp, e₂_self, mul_zero]
    have hmm : crossPair ε J em em = 0 := by
      rw [crossPair, hm, e₂_neg_right, e₂_self, neg_zero, mul_zero]
    simp only [localPair, crossPair_smul, hpp, hmm, mul_zero, add_zero]
  · exact signPlane_nondegenerate (hpm ▸ hκ)
  · exact signPlane_nondegenerate (hmp ▸ hκ)
  · rw [localPair_self, localPair_self, hpm, hmp]; exact ⟨rfl, rfl⟩

/-- Lines 5051-5053, PROVED. In a sign plane with `β(f,s) ≠ 0` and
`(2 : k) ≠ 0`, an isotropic vector lies on the finite or the singular axis. -/
theorem isotropic_axis_of_ne (h2 : (2 : k) ≠ 0) {f s : Fin 2 → k}
    (hκ : crossPair ε J f s ≠ 0) (u : (Fin 2 → k) × (Fin 2 → k)) (hu : u ∈ signPlane f s)
    (hiso : localPair ε J u u = 0) : u ∈ finAxis f ∨ u ∈ singAxis s := by
  obtain ⟨a, b, rfl⟩ := mem_signPlane.1 hu
  rw [localPair_self] at hiso
  rcases mul_eq_zero.1 hiso with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h h2
      · right; exact mem_singAxis.2 ⟨b, by simp [h]⟩
    · left; exact mem_finAxis.2 ⟨a, by simp [h]⟩
  · exact absurd h hκ

/-- A nonzero vector of `F(f)` spans `F(f)`. -/
lemma span_eq_finAxis {f : Fin 2 → k} {u : (Fin 2 → k) × (Fin 2 → k)} (hu0 : u ≠ 0)
    (hu : u ∈ finAxis f) : k ∙ u = finAxis f := by
  obtain ⟨a, rfl⟩ := mem_finAxis.1 hu
  have ha : a ≠ 0 := by rintro rfl; simp at hu0
  rw [finAxis_eq_span]
  have : ((a • f, 0) : (Fin 2 → k) × (Fin 2 → k)) = a • (f, 0) := by simp
  rw [this, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ ha)]

/-- A nonzero vector of `S(s)` spans `S(s)`. -/
lemma span_eq_singAxis {s : Fin 2 → k} {u : (Fin 2 → k) × (Fin 2 → k)} (hu0 : u ≠ 0)
    (hu : u ∈ singAxis s) : k ∙ u = singAxis s := by
  obtain ⟨a, rfl⟩ := mem_singAxis.1 hu
  have ha : a ≠ 0 := by rintro rfl; simp at hu0
  rw [singAxis_eq_span]
  have : ((0, a • s) : (Fin 2 → k) × (Fin 2 → k)) = a • (0, s) := by simp
  rw [this, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ ha)]

/-- `U` is its own annihilator inside `H`: `U = {u ∈ H | ⟨u,U⟩ = 0}`. -/
def IsSelfAnnihilatingIn (ε : k) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (H U : Submodule k ((Fin 2 → k) × (Fin 2 → k))) : Prop :=
  ∀ u, u ∈ U ↔ u ∈ H ∧ ∀ w ∈ U, localPair ε J u w = 0

/-- Lines 5083-5085, PROVED. In a sign plane with
`β(f,s) ≠ 0` and `(2 : k) ≠ 0`, a subspace that is its own annihilator in the plane is one of
the two axes. -/
theorem selfAnnihilating_eq_axis_of_ne (h2 : (2 : k) ≠ 0) {f s : Fin 2 → k}
    (hκ : crossPair ε J f s ≠ 0) (U : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hU : IsSelfAnnihilatingIn ε J (signPlane f s) U) : U = finAxis f ∨ U = singAxis s := by
  have hf0 := (ne_zero_of_crossPair_ne_zero hκ).1
  -- U ≠ 0
  obtain ⟨u₀, hu₀U, hu₀⟩ : ∃ u₀ ∈ U, u₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hmem : ((f, 0) : (Fin 2 → k) × (Fin 2 → k)) ∈ U := by
      refine (hU _).2 ⟨finAxis_le_signPlane f s (mem_finAxis.2 ⟨1, by simp⟩), ?_⟩
      intro w hw
      rw [hcon w hw]
      simp [localPair, crossPair, e₂_apply]
    have := hcon _ hmem
    simp only [Prod.mk_eq_zero, and_true] at this
    exact hf0 this
  have hu₀H := ((hU u₀).1 hu₀U).1
  have hiso := ((hU u₀).1 hu₀U).2 u₀ hu₀U
  obtain ⟨a, b, rfl⟩ := mem_signPlane.1 hu₀H
  rw [localPair_self] at hiso
  have hab : a = 0 ∨ b = 0 := by
    rcases mul_eq_zero.1 hiso with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h h2
        · exact Or.inl h
      · exact Or.inr h
    · exact absurd h hκ
  rcases hab with ha | hb
  · subst ha
    have hb0 : b ≠ 0 := by rintro rfl; apply hu₀; simp
    right
    have hle : U ≤ singAxis s := by
      intro v hv
      obtain ⟨c, d, rfl⟩ := mem_signPlane.1 ((hU v).1 hv).1
      have h := ((hU _).1 hv).2 _ hu₀U
      rw [localPair_plane] at h
      have hc : c = 0 := by
        have h' : c * b * crossPair ε J f s = 0 := by linear_combination h
        rcases mul_eq_zero.1 h' with h' | h'
        · exact (mul_eq_zero.1 h').resolve_right hb0
        · exact absurd h' hκ
      exact mem_singAxis.2 ⟨d, by simp [hc]⟩
    refine le_antisymm hle ?_
    intro v hv
    refine (hU v).2 ⟨singAxis_le_signPlane f s hv, fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := mem_singAxis.1 hv
    obtain ⟨c', rfl⟩ := mem_singAxis.1 (hle hw)
    simp [localPair, crossPair, e₂_apply]
  · subst hb
    have ha0 : a ≠ 0 := by rintro rfl; apply hu₀; simp
    left
    have hle : U ≤ finAxis f := by
      intro v hv
      obtain ⟨c, d, rfl⟩ := mem_signPlane.1 ((hU v).1 hv).1
      have h := ((hU _).1 hv).2 _ hu₀U
      rw [localPair_plane] at h
      have hd : d = 0 := by
        have h' : a * d * crossPair ε J f s = 0 := by linear_combination h
        rcases mul_eq_zero.1 h' with h' | h'
        · exact (mul_eq_zero.1 h').resolve_left ha0
        · exact absurd h' hκ
      exact mem_finAxis.2 ⟨c, by simp [hd]⟩
    refine le_antisymm hle ?_
    intro v hv
    refine (hU v).2 ⟨finAxis_le_signPlane f s hv, fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := mem_finAxis.1 hv
    obtain ⟨c', rfl⟩ := mem_finAxis.1 (hle hw)
    simp [localPair, crossPair, e₂_apply]

/-- Converse: `F(f)` is its own annihilator in `F(f) ⊕ S(s)` when `β(f,s) ≠ 0`. -/
lemma finAxis_selfAnnihilating {f s : Fin 2 → k} (hκ : crossPair ε J f s ≠ 0) :
    IsSelfAnnihilatingIn ε J (signPlane f s) (finAxis f) := by
  intro u
  constructor
  · intro hu
    refine ⟨finAxis_le_signPlane f s hu, fun w hw => ?_⟩
    obtain ⟨a, rfl⟩ := mem_finAxis.1 hu
    obtain ⟨c, rfl⟩ := mem_finAxis.1 hw
    simp [localPair, crossPair, e₂_apply]
  · rintro ⟨hu, H⟩
    obtain ⟨a, b, rfl⟩ := mem_signPlane.1 hu
    have h := H ((1 : k) • f, (0 : k) • s) (mem_finAxis.2 ⟨1, by simp⟩)
    rw [localPair_plane] at h
    have hb : b = 0 := by
      have : b * crossPair ε J f s = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_right hκ
    exact mem_finAxis.2 ⟨a, by simp [hb]⟩

/-- Converse: `S(s)` is its own annihilator in `F(f) ⊕ S(s)` when `β(f,s) ≠ 0`. -/
lemma singAxis_selfAnnihilating {f s : Fin 2 → k} (hκ : crossPair ε J f s ≠ 0) :
    IsSelfAnnihilatingIn ε J (signPlane f s) (singAxis s) := by
  intro u
  constructor
  · intro hu
    refine ⟨singAxis_le_signPlane f s hu, fun w hw => ?_⟩
    obtain ⟨a, rfl⟩ := mem_singAxis.1 hu
    obtain ⟨c, rfl⟩ := mem_singAxis.1 hw
    simp [localPair, crossPair, e₂_apply]
  · rintro ⟨hu, H⟩
    obtain ⟨a, b, rfl⟩ := mem_signPlane.1 hu
    have h := H ((0 : k) • f, (1 : k) • s) (mem_singAxis.2 ⟨1, by simp⟩)
    rw [localPair_plane] at h
    have ha : a = 0 := by
      have : a * crossPair ε J f s = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_right hκ
    exact mem_singAxis.2 ⟨b, by simp [ha]⟩


/-- Line 5050: `H_+ ⊥ H_-`. -/
lemma signPlane_orthogonal (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em) :
    ∀ u ∈ signPlane ep em, ∀ w ∈ signPlane em ep, localPair ε J u w = 0 := by
  intro u hu w hw
  obtain ⟨a, b, rfl⟩ := mem_signPlane.1 hu
  obtain ⟨c, d, rfl⟩ := mem_signPlane.1 hw
  have hpp : crossPair ε J ep ep = 0 := by rw [crossPair, hp, e₂_self, mul_zero]
  have hmm : crossPair ε J em em = 0 := by
    rw [crossPair, hm, e₂_neg_right, e₂_self, neg_zero, mul_zero]
  simp only [localPair, crossPair_smul, hpp, hmm, mul_zero, add_zero]

lemma crossPair_plus_ne_zero (hε : ε ≠ 0) {ep em : Fin 2 → k} (hm : J em = -em)
    (he : e₂ ep em ≠ 0) : crossPair ε J ep em ≠ 0 := by
  rw [crossPair_plus_minus ep em hm]; exact neg_ne_zero.2 (mul_ne_zero hε he)

lemma crossPair_minus_ne_zero (hε : ε ≠ 0) {ep em : Fin 2 → k} (hp : J ep = ep)
    (he : e₂ ep em ≠ 0) : crossPair ε J em ep ≠ 0 := by
  rw [crossPair_minus_plus ep em hp]; exact neg_ne_zero.2 (mul_ne_zero hε he)

/-- Lines 5051-5053, PROVED. **Isotropic lines.** With `(2 : k) ≠ 0`, `ε ≠ 0` and the eigenbasis
data, "its only isotropic lines are thus its finite and singular axes": a nonzero isotropic
`u ∈ H_+` spans `F(e_+)` or `S(e_-)`, and a nonzero isotropic `u ∈ H_-` spans `F(e_-)` or
`S(e_+)`. Without `2 ≠ 0` this fails: in characteristic `2` every vector is isotropic. -/
theorem isotropic_axis (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0)
    (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) :
    (∀ u ∈ signPlane ep em, u ≠ 0 → localPair ε J u u = 0 →
        k ∙ u = finAxis ep ∨ k ∙ u = singAxis em) ∧
    (∀ u ∈ signPlane em ep, u ≠ 0 → localPair ε J u u = 0 →
        k ∙ u = finAxis em ∨ k ∙ u = singAxis ep) := by
  constructor
  · intro u hu hu0 hiso
    rcases isotropic_axis_of_ne h2 (crossPair_plus_ne_zero hε hm he) u hu hiso with h | h
    · exact Or.inl (span_eq_finAxis hu0 h)
    · exact Or.inr (span_eq_singAxis hu0 h)
  · intro u hu hu0 hiso
    rcases isotropic_axis_of_ne h2 (crossPair_minus_ne_zero hε hp he) u hu hiso with h | h
    · exact Or.inl (span_eq_finAxis hu0 h)
    · exact Or.inr (span_eq_singAxis hu0 h)

/-- Lines 5083-5085, PROVED. **Axis lemma.** "Each `U_± ⊂ H_±` is its own annihilator in
`H_±`, hence is one of that plane's two isotropic axes." A subspace is its own annihilator in
`H_+` iff it is `F(e_+)` or `S(e_-)`, and in `H_-` iff it is `F(e_-)` or `S(e_+)`. Uses
`(2 : k) ≠ 0`. In characteristic `2` the diagonal of `H_+` is a counterexample. -/
theorem selfAnnihilating_eq_axis (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0)
    (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) (U : Submodule k ((Fin 2 → k) × (Fin 2 → k))) :
    (IsSelfAnnihilatingIn ε J (signPlane ep em) U ↔ U = finAxis ep ∨ U = singAxis em) ∧
    (IsSelfAnnihilatingIn ε J (signPlane em ep) U ↔ U = finAxis em ∨ U = singAxis ep) := by
  have hκp := crossPair_plus_ne_zero hε hm he
  have hκm := crossPair_minus_ne_zero hε hp he
  constructor
  · refine ⟨selfAnnihilating_eq_axis_of_ne h2 hκp U, ?_⟩
    rintro (rfl | rfl)
    · exact finAxis_selfAnnihilating hκp
    · exact singAxis_selfAnnihilating hκp
  · refine ⟨selfAnnihilating_eq_axis_of_ne h2 hκm U, ?_⟩
    rintro (rfl | rfl)
    · exact finAxis_selfAnnihilating hκm
    · exact singAxis_selfAnnihilating hκm

lemma ne_zero_of_e₂_ne_zero {u v : Fin 2 → k} (he : e₂ u v ≠ 0) : u ≠ 0 ∧ v ≠ 0 := by
  constructor
  · rintro rfl; apply he; simp
  · rintro rfl; apply he; simp

/-- The `+1`-eigenspace of `J` is `k e₊`. -/
lemma mem_span_plus_iff (h2 : (2 : k) ≠ 0) {ep em : Fin 2 → k} (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0) (x : Fin 2 → k) : x ∈ k ∙ ep ↔ J x = x := by
  obtain ⟨hp0, hm0⟩ := ne_zero_of_e₂_ne_zero he
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, hp]
  · intro hx
    have h1 := e₂_cramer x ep em
    have h2' := congrArg J h1
    rw [map_smul, map_add, map_smul, map_smul, hx, hp, hm] at h2'
    have key : (2 * e₂ ep x) • em = 0 := by linear_combination (norm := module) h2' - h1
    have hx0 : e₂ ep x = 0 := by
      rcases smul_eq_zero.1 key with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2
      · exact absurd h hm0
    obtain ⟨l, rfl⟩ := eq_smul_of_e₂_eq_zero hp0 hx0
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The `-1`-eigenspace of `J` is `k e₋`. -/
lemma mem_span_minus_iff (h2 : (2 : k) ≠ 0) {ep em : Fin 2 → k} (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0) (x : Fin 2 → k) : x ∈ k ∙ em ↔ J x = -x := by
  obtain ⟨hp0, hm0⟩ := ne_zero_of_e₂_ne_zero he
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, hm, smul_neg]
  · intro hx
    have h1 := e₂_cramer x ep em
    have h2' := congrArg J h1
    rw [map_smul, map_add, map_smul, map_smul, hx, hp, hm] at h2'
    have key : (2 * e₂ x em) • ep = 0 := by linear_combination (norm := module) -h1 - h2'
    have hx0 : e₂ em x = 0 := by
      rcases smul_eq_zero.1 key with h | h
      · have := (mul_eq_zero.1 h).resolve_left h2
        rw [e₂_apply] at this ⊢; linear_combination -this
      · exact absurd h hp0
    obtain ⟨l, rfl⟩ := eq_smul_of_e₂_eq_zero hm0 hx0
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- `H_+` is the `+1`-eigenspace of the involution `(x,y) ↦ (Jx, -Jy)`: `τ` acts by `J` on
`F` and by `-J` on `S` (lines 5026-5027). -/
lemma mem_signPlane_plus_iff (h2 : (2 : k) ≠ 0) {ep em : Fin 2 → k} (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0) (u : (Fin 2 → k) × (Fin 2 → k)) :
    u ∈ signPlane ep em ↔ J u.1 = u.1 ∧ J u.2 = -u.2 := by
  rw [signPlane, Submodule.mem_prod, mem_span_plus_iff h2 hp hm he,
    mem_span_minus_iff h2 hp hm he]

/-- `H_-` is the `-1`-eigenspace of `(x,y) ↦ (Jx, -Jy)`. -/
lemma mem_signPlane_minus_iff (h2 : (2 : k) ≠ 0) {ep em : Fin 2 → k} (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0) (u : (Fin 2 → k) × (Fin 2 → k)) :
    u ∈ signPlane em ep ↔ J u.1 = -u.1 ∧ J u.2 = u.2 := by
  rw [signPlane, Submodule.mem_prod, mem_span_plus_iff h2 hp hm he,
    mem_span_minus_iff h2 hp hm he]

/-- `H_+ ∩ H_- = 0` (uses `2 ≠ 0`). -/
lemma signPlane_inf_eq_bot (h2 : (2 : k) ≠ 0) {ep em : Fin 2 → k} (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0) : signPlane ep em ⊓ signPlane em ep = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨h1, h2'⟩ := (mem_signPlane_plus_iff h2 hp hm he u).1 (Submodule.mem_inf.1 hu).1
  obtain ⟨h3, h4⟩ := (mem_signPlane_minus_iff h2 hp hm he u).1 (Submodule.mem_inf.1 hu).2
  have e1 : (2 : k) • u.1 = 0 := by rw [two_smul]; nth_rewrite 2 [← h1]; rw [h3, add_neg_cancel]
  have e2 : (2 : k) • u.2 = 0 := by rw [two_smul]; nth_rewrite 1 [← h4]; rw [h2', neg_add_cancel]
  rw [smul_eq_zero] at e1 e2
  rw [Submodule.mem_bot]
  exact Prod.ext (e1.resolve_left h2) (e2.resolve_left h2)

/-- Lines 5120-5121, PROVED. "The localization of `v̄` is nonzero: its two sign
components lie on different finite axes, so cannot cancel." Let `x_+ ∈ H_+` and
`x_- ∈ H_-`, not both zero. Then `x_+ + x_- ≠ 0`. -/
theorem sign_components_no_cancel (h2 : (2 : k) ≠ 0) {ep em : Fin 2 → k} (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0) (xp xm : (Fin 2 → k) × (Fin 2 → k))
    (hxp : xp ∈ signPlane ep em) (hxm : xm ∈ signPlane em ep) (h0 : xp ≠ 0 ∨ xm ≠ 0) :
    xp + xm ≠ 0 := by
  intro hsum
  have hxm' : xm = -xp := eq_neg_of_add_eq_zero_right hsum
  have hmem : xp ∈ signPlane ep em ⊓ signPlane em ep := by
    refine Submodule.mem_inf.2 ⟨hxp, ?_⟩
    have := Submodule.neg_mem _ hxm
    rwa [hxm', neg_neg] at this
  rw [signPlane_inf_eq_bot h2 hp hm he, Submodule.mem_bot] at hmem
  rcases h0 with h | h
  · exact h hmem
  · exact h (by rw [hxm', hmem, neg_zero])

/-- Lines 5083-5085, PROVED. "The space `U` is stable under signs. Each `U_± ⊂ H_±` is
its own annihilator in `H_±`." Let `U ⊆ F ⊕ S` satisfy `U = U^⊥` (line 5067; a hypothesis
here, from the localization duality) and be stable under `τ : (x,y) ↦ (Jx, -Jy)`, with
`J^2 = 1` and `(2 : k) ≠ 0`. Then `U_± = U ∩ H_±` is its own annihilator in `H_±`. Proof:
split `w ∈ U` as `w_+ + w_-` with `w_± = (w ± τw)/2`, and use `H_+ ⊥ H_-`. -/
theorem selfAnnihilating_sign_parts (h2 : (2 : k) ≠ 0) (ε : k)
    (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k)
    (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0)
    (U : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hσ : ∀ u ∈ U, ((J u.1, -J u.2) : (Fin 2 → k) × (Fin 2 → k)) ∈ U)
    (hU : ∀ u, u ∈ U ↔ ∀ w ∈ U, localPair ε J u w = 0) :
    IsSelfAnnihilatingIn ε J (signPlane ep em) (U ⊓ signPlane ep em) ∧
    IsSelfAnnihilatingIn ε J (signPlane em ep) (U ⊓ signPlane em ep) := by
  have hJJ : ∀ z, J (J z) = z := fun z => LinearMap.congr_fun hJ2 z
  -- the sign decomposition of an element of `U`
  have hdec : ∀ w ∈ U, ∃ wp ∈ U ⊓ signPlane ep em, ∃ wm ∈ U ⊓ signPlane em ep, w = wp + wm := by
    intro w hw
    set σw : (Fin 2 → k) × (Fin 2 → k) := (J w.1, -J w.2)
    refine ⟨(2⁻¹ : k) • (w + σw), Submodule.mem_inf.2 ⟨?_, ?_⟩,
      (2⁻¹ : k) • (w - σw), Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact U.smul_mem _ (U.add_mem hw (hσ w hw))
    · rw [mem_signPlane_plus_iff h2 hp hm he]
      simp only [σw, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, map_smul,
        map_add, map_neg, hJJ]
      constructor
      · rw [add_comm]
      · rw [← smul_neg, neg_add, neg_neg, add_comm]
    · exact U.smul_mem _ (U.sub_mem hw (hσ w hw))
    · rw [mem_signPlane_minus_iff h2 hp hm he]
      simp only [σw, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, map_smul,
        map_sub, hJJ, sub_neg_eq_add, map_add]
      constructor
      · rw [← smul_neg, neg_sub]
      · rw [add_comm]
    · rw [← smul_add, add_add_sub_cancel, ← two_smul k w, smul_smul, inv_mul_cancel₀ h2,
        one_smul]
  have horth := signPlane_orthogonal (ε := ε) ep em hp hm
  constructor
  · intro u
    constructor
    · intro hu
      exact ⟨(Submodule.mem_inf.1 hu).2, fun w hw =>
        (hU u).1 (Submodule.mem_inf.1 hu).1 w (Submodule.mem_inf.1 hw).1⟩
    · rintro ⟨huH, H⟩
      refine Submodule.mem_inf.2 ⟨(hU u).2 fun w hw => ?_, huH⟩
      obtain ⟨wp, hwp, wm, hwm, rfl⟩ := hdec w hw
      rw [localPair_add_right, H wp hwp, horth u huH wm (Submodule.mem_inf.1 hwm).2, add_zero]
  · intro u
    constructor
    · intro hu
      exact ⟨(Submodule.mem_inf.1 hu).2, fun w hw =>
        (hU u).1 (Submodule.mem_inf.1 hu).1 w (Submodule.mem_inf.1 hw).1⟩
    · rintro ⟨huH, H⟩
      refine Submodule.mem_inf.2 ⟨(hU u).2 fun w hw => ?_, huH⟩
      obtain ⟨wp, hwp, wm, hwm, rfl⟩ := hdec w hw
      rw [localPair_add_right, H wm hwm, localPair_symm,
        horth wp (Submodule.mem_inf.1 hwp).2 u huH, zero_add]


/-- Detection plus the axis lemma: an axis containing a nonzero finite vector is the finite axis. -/
lemma axis_eq_finAxis_of_detect (h2 : (2 : k) ≠ 0) {f s : Fin 2 → k}
    (hκ : crossPair ε J f s ≠ 0) (U : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hU : IsSelfAnnihilatingIn ε J (signPlane f s) U)
    (hdet : ∃ x ∈ U, x ∈ finAxis f ∧ x ≠ 0) : U = finAxis f := by
  rcases selfAnnihilating_eq_axis_of_ne h2 hκ U hU with h | h
  · exact h
  · exfalso
    obtain ⟨x, hxU, hxF, hx0⟩ := hdet
    rw [h] at hxU
    have : x ∈ finAxis f ⊓ singAxis s := Submodule.mem_inf.2 ⟨hxF, hxU⟩
    rw [finAxis_inf_singAxis, Submodule.mem_bot] at this
    exact hx0 this

/-- Lines 5116-5120, PROVED. **Both signs present.** "Detection as above puts both finite axes
in `U`, so `U = F` and `U ∩ S = 0`. Equation (5.5a) gives `dim V' = s - 2`."
Hypotheses. `U_±` is its own annihilator in `H_±` (from `selfAnnihilating_sign_parts`).
Detection: `U_±` contains a nonzero vector of its finite axis `F(e_±)`. The sign parts of
(5.5a), `0 → K_0 → V → U∩F → 0` and `0 → K_0 → V' → U∩S → 0`, are given as dimension
equations, using `(U∩F)_+ = U_+ ∩ F(e_+)`, `(U∩F)_- = U_- ∩ F(e_-)`,
`(U∩S)_+ = U_+ ∩ S(e_-)` and `(U∩S)_- = U_- ∩ S(e_+)`.
Conclusion: `U_± = F(e_±)` (so `U = F`), `U ∩ S = 0`, and `dim V' = s - 2` with
`s = dim V_+ + dim V_-`.
DEPARTURE: (5.5a) enters as dimension equations (see `finrank_eq_of_shortExact`), and the
detection step is a hypothesis. "Both signs present" is what makes detection possible (lines
5087-5114). It is not a separate hypothesis. -/
theorem bookkeeping_mixed (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0)
    (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) (Up Um : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hUp : IsSelfAnnihilatingIn ε J (signPlane ep em) Up)
    (hUm : IsSelfAnnihilatingIn ε J (signPlane em ep) Um)
    (hdetp : ∃ x ∈ Up, x ∈ finAxis ep ∧ x ≠ 0) (hdetm : ∃ x ∈ Um, x ∈ finAxis em ∧ x ≠ 0)
    {K0p K0m Vp Vm Vp' Vm' : Type*}
    [AddCommGroup K0p] [Module k K0p] [FiniteDimensional k K0p]
    [AddCommGroup K0m] [Module k K0m] [FiniteDimensional k K0m]
    [AddCommGroup Vp] [Module k Vp] [FiniteDimensional k Vp]
    [AddCommGroup Vm] [Module k Vm] [FiniteDimensional k Vm]
    [AddCommGroup Vp'] [Module k Vp'] [FiniteDimensional k Vp']
    [AddCommGroup Vm'] [Module k Vm'] [FiniteDimensional k Vm']
    (hVp : finrank k Vp = finrank k K0p + finrank k ↥(Up ⊓ finAxis ep))
    (hVm : finrank k Vm = finrank k K0m + finrank k ↥(Um ⊓ finAxis em))
    (hVp' : finrank k Vp' = finrank k K0p + finrank k ↥(Up ⊓ singAxis em))
    (hVm' : finrank k Vm' = finrank k K0m + finrank k ↥(Um ⊓ singAxis ep)) :
    Up = finAxis ep ∧ Um = finAxis em ∧ Up ⊓ singAxis em = ⊥ ∧ Um ⊓ singAxis ep = ⊥ ∧
      finrank k Vp' + finrank k Vm' + 2 = finrank k Vp + finrank k Vm ∧
      finrank k Vp' + finrank k Vm' = finrank k Vp + finrank k Vm - 2 := by
  obtain ⟨hp0, hm0⟩ := ne_zero_of_e₂_ne_zero he
  have hUp' := axis_eq_finAxis_of_detect h2 (crossPair_plus_ne_zero hε hm he) Up hUp hdetp
  have hUm' := axis_eq_finAxis_of_detect h2 (crossPair_minus_ne_zero hε hp he) Um hUm hdetm
  subst hUp' hUm'
  have hSp := finAxis_inf_singAxis (k := k) ep em
  have hSm := finAxis_inf_singAxis (k := k) em ep
  refine ⟨rfl, rfl, hSp, hSm, ?_, ?_⟩ <;>
  · rw [inf_idem, finrank_finAxis hp0] at hVp
    rw [inf_idem, finrank_finAxis hm0] at hVm
    rw [hSp, finrank_bot] at hVp'
    rw [hSm, finrank_bot] at hVm'
    omega

/-- Lines 5123-5131, PROVED. **One sign only.** Let `V = V_+` (`dim V_- = 0`) with
`s = dim V_+ > 1`, and detect `v̄` in its finite axis. Then `U_+ = F(e_+)`. Since `V_- = 0`,
(5.5a) gives `U_- ∩ F(e_-) = 0`. "The isotropic-axis calculation forces `U_- = S(e_+)`." So
`K_0` has sign dimensions `(s-1, 0)` and `V'` has sign dimensions `(s-1, 1)`. The total is
`s`, the other sign appears, and both signs of `V'` are nonzero, so the next switch is the
mixed case.
DEPARTURE: as in `bookkeeping_mixed`. Here `U_- ∩ F(e_-) = 0` is derived from `V_- = 0`
rather than assumed. `selfAnnihilating_eq_axis_of_ne` supplies the axis lemma. -/
theorem bookkeeping_single_sign (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0)
    (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) (Up Um : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hUp : IsSelfAnnihilatingIn ε J (signPlane ep em) Up)
    (hUm : IsSelfAnnihilatingIn ε J (signPlane em ep) Um)
    (hdetp : ∃ x ∈ Up, x ∈ finAxis ep ∧ x ≠ 0)
    {K0p K0m Vp Vm Vp' Vm' : Type*}
    [AddCommGroup K0p] [Module k K0p] [FiniteDimensional k K0p]
    [AddCommGroup K0m] [Module k K0m] [FiniteDimensional k K0m]
    [AddCommGroup Vp] [Module k Vp] [FiniteDimensional k Vp]
    [AddCommGroup Vm] [Module k Vm] [FiniteDimensional k Vm]
    [AddCommGroup Vp'] [Module k Vp'] [FiniteDimensional k Vp']
    [AddCommGroup Vm'] [Module k Vm'] [FiniteDimensional k Vm']
    (s : ℕ) (hs : 1 < s) (hVps : finrank k Vp = s) (hVm0 : finrank k Vm = 0)
    (hVp : finrank k Vp = finrank k K0p + finrank k ↥(Up ⊓ finAxis ep))
    (hVm : finrank k Vm = finrank k K0m + finrank k ↥(Um ⊓ finAxis em))
    (hVp' : finrank k Vp' = finrank k K0p + finrank k ↥(Up ⊓ singAxis em))
    (hVm' : finrank k Vm' = finrank k K0m + finrank k ↥(Um ⊓ singAxis ep)) :
    Up = finAxis ep ∧ Um ⊓ finAxis em = ⊥ ∧ Um = singAxis ep ∧
      (finrank k K0p, finrank k K0m) = (s - 1, 0) ∧
      (finrank k Vp', finrank k Vm') = (s - 1, 1) ∧
      finrank k Vp' + finrank k Vm' = s ∧ 0 < finrank k Vp' ∧ 0 < finrank k Vm' := by
  obtain ⟨hp0, hm0⟩ := ne_zero_of_e₂_ne_zero he
  have hUp' := axis_eq_finAxis_of_detect h2 (crossPair_plus_ne_zero hε hm he) Up hUp hdetp
  subst hUp'
  -- `V_- = 0` and (5.5a) give `U_- ∩ F(e_-) = 0` and `K_0^- = 0`
  have hK0m : finrank k K0m = 0 := by omega
  have hUmF : Um ⊓ finAxis em = ⊥ := by
    have : finrank k ↥(Um ⊓ finAxis em) = 0 := by omega
    exact Submodule.finrank_eq_zero.1 this
  -- the isotropic-axis calculation forces `U_- = S(e_+)`
  have hUm' : Um = singAxis ep := by
    rcases selfAnnihilating_eq_axis_of_ne h2 (crossPair_minus_ne_zero hε hp he) Um hUm with h | h
    · exfalso
      rw [h, inf_idem] at hUmF
      have hmem : ((em, 0) : (Fin 2 → k) × (Fin 2 → k)) ∈ finAxis em :=
        mem_finAxis.2 ⟨1, by simp⟩
      rw [hUmF, Submodule.mem_bot] at hmem
      simp only [Prod.mk_eq_zero, and_true] at hmem
      exact hm0 hmem
    · exact h
  subst hUm'
  have hSp := finAxis_inf_singAxis (k := k) ep em
  rw [inf_idem, finrank_finAxis hp0] at hVp
  rw [hSp, finrank_bot] at hVp'
  rw [inf_idem, finrank_singAxis hp0] at hVm'
  refine ⟨rfl, hUmF, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp <;> omega
  · ext <;> simp <;> omega
  · omega
  · omega
  · omega


end SignPlanes

section Evaluation

/-- Lines 5010-5013, PROVED. `c^τ(g) = J c(τ⁻¹gτ)` with `J = ρ_T(τ)` is again a cocycle on
the index-two subgroup `N` (normal in `G`). -/
theorem tauAction_cocycle {k T G : Type*} [CommRing k] [AddCommGroup T] [Module k T] [Group G]
    (ρ : G →* (T →ₗ[k] T)) (N : Subgroup G) (hN : N.Normal) (τ : G) (c : G → T)
    (hc : ∀ g ∈ N, ∀ g' ∈ N, c (g * g') = c g + ρ g (c g')) (g g' : G) (hg : g ∈ N)
    (hg' : g' ∈ N) :
    ρ τ (c (τ⁻¹ * (g * g') * τ)) = ρ τ (c (τ⁻¹ * g * τ)) + ρ g (ρ τ (c (τ⁻¹ * g' * τ))) := by
  have e : τ⁻¹ * (g * g') * τ = (τ⁻¹ * g * τ) * (τ⁻¹ * g' * τ) := by group
  rw [e, hc _ (hN.conj_mem' g hg τ) _ (hN.conj_mem' g' hg' τ), map_add]
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

/-- Lines 5010-5013, PROVED. `c ↦ c^τ` sends the coboundary of `m` to the coboundary of `Jm`,
so it acts on cohomology. -/
theorem tauAction_coboundary {k T G : Type*} [CommRing k] [AddCommGroup T] [Module k T]
    [Group G] (ρ : G →* (T →ₗ[k] T)) (τ : G) (m : T) (g : G) :
    ρ τ (ρ (τ⁻¹ * g * τ) m - m) = ρ g (ρ τ m) - ρ τ m := by
  rw [map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 3
  group

/-- Lines 5010-5013, PROVED. When `τ^2 = 1`, `(c^τ)^τ = c`: the action is an involution. -/
theorem tauAction_involutive {k T G : Type*} [CommRing k] [AddCommGroup T] [Module k T]
    [Group G] (ρ : G →* (T →ₗ[k] T)) (τ : G) (hτ : τ ^ 2 = 1) (c : G → T) (g : G) :
    ρ τ (ρ τ (c (τ⁻¹ * (τ⁻¹ * g * τ) * τ))) = c g := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hτ)
  have e : τ⁻¹ * (τ⁻¹ * g * τ) * τ = g := by
    rw [hτinv]
    calc τ * (τ * g * τ) * τ = (τ * τ) * g * (τ * τ) := by group
      _ = g := by rw [← pow_two, hτ, one_mul, mul_one]
  rw [e, ← Module.End.mul_apply, ← map_mul, ← pow_two, hτ, map_one, Module.End.one_apply]

/-- Lines 5093-5099, PROVED. **(5.5b).** `c_δ((τh)^2) = (1 + δJ) c_δ(h)` for `h ∈ H`.
Hypotheses. `τ^2 = 1` (`τ` is the actual conjugation). `H ≤ N` is the exact kernel, and `ρ`
is trivial on `H`. The kernel is normal in `G`, but only its stability under conjugation by
`τ` is used, so that is the hypothesis. `c` is a cocycle on the index-two subgroup `N`. `c` has
sign `δ = ±1` in cohomology: `c^τ - δc` is a coboundary on `N`, where
`c^τ(g) = J c(τ⁻¹gτ)`.
The proof follows the manuscript: "additivity on `H` and the sign relation; a coboundary is
zero on `H`". Write `(τh)^2 = (τhτ⁻¹)h`. Additivity on `H` gives
`c((τh)^2) = c(τhτ⁻¹) + c(h)`. The sign relation at `τhτ⁻¹ ∈ H`, where the coboundary
vanishes, gives `c(τhτ⁻¹) = δJ c(h)`.
DEPARTURE: `c` is a function on `G`, but only its values on `N` are constrained, which is the
same as a cocycle `N → T`. No normalization `c(τ) = 0` is needed. `ρ(τ) = J` is not used here.
It is what makes `c^τ` a cocycle (`tauAction_cocycle`). -/
theorem eval_tau_h_sq {k T G : Type*} [CommRing k] [AddCommGroup T] [Module k T] [Group G]
    (ρ : G →* (T →ₗ[k] T)) (J : T →ₗ[k] T) (τ : G) (hτ : τ ^ 2 = 1)
    (N H : Subgroup G) (hHN : H ≤ N) (hHτ : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H)
    (hH : ∀ h ∈ H, ρ h = 1) (c : G → T) (hc : ∀ g ∈ N, ∀ g' ∈ N, c (g * g') = c g + ρ g (c g'))
    (δ : k) (hδ : δ = 1 ∨ δ = -1)
    (hsign : ∃ m : T, ∀ g ∈ N, J (c (τ⁻¹ * g * τ)) - δ • c g = ρ g m - m)
    (h : G) (hh : h ∈ H) :
    c ((τ * h) ^ 2) = (1 + δ • J) (c h) := by
  obtain ⟨m, hm⟩ := hsign
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  -- additivity on `H`
  have hadd : ∀ h₁ ∈ H, ∀ h₂ ∈ H, c (h₁ * h₂) = c h₁ + c h₂ := by
    intro h₁ h₁H h₂ h₂H
    rw [hc h₁ (hHN h₁H) h₂ (hHN h₂H), hH h₁ h₁H, Module.End.one_apply]
  -- the sign relation on `H`: a coboundary is zero on `H`
  have hsH : ∀ g ∈ H, J (c (τ⁻¹ * g * τ)) = δ • c g := by
    intro g hg
    have := hm g (hHN hg)
    rwa [hH g hg, Module.End.one_apply, sub_self, sub_eq_zero] at this
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hτ)
  have hh' : τ * h * τ⁻¹ ∈ H := hHτ h hh
  have e1 := hsH _ hh'
  have hconj : τ⁻¹ * (τ * h * τ⁻¹) * τ = h := by group
  rw [hconj] at e1
  have e2 : c (τ * h * τ⁻¹) = δ • J (c h) := by rw [e1, smul_smul, hδ2, one_smul]
  have hsq : (τ * h) ^ 2 = (τ * h * τ⁻¹) * h := by
    rw [hτinv, pow_two]; simp only [mul_assoc]
  rw [hsq, hadd _ hh' h hh, e2, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.smul_apply, add_comm]

-- The hypotheses of `eval_tau_h_sq` hold in an honest model with `ρ(τ) = J`, `τ ∉ N`,
-- sign `δ = -1` and a cocycle that is nonzero on `H`.
example : ∃ (G : Type) (_ : Group G) (ρ : G →* (ℚ →ₗ[ℚ] ℚ)) (J : ℚ →ₗ[ℚ] ℚ) (τ : G)
    (N H : Subgroup G) (c : G → ℚ) (δ : ℚ), ρ τ = J ∧ τ ∉ N ∧ τ ^ 2 = 1 ∧ H ≤ N ∧
      (∀ h ∈ H, τ * h * τ⁻¹ ∈ H) ∧ (∀ h ∈ H, ρ h = 1) ∧
      (∀ g ∈ N, ∀ g' ∈ N, c (g * g') = c g + ρ g (c g')) ∧
      δ = -1 ∧ (∃ m : ℚ, ∀ g ∈ N, J (c (τ⁻¹ * g * τ)) - δ • c g = ρ g m - m) ∧
      ∃ h ∈ H, c h ≠ 0 := by
  refine ⟨(ℚ →ₗ[ℚ] ℚ)ˣ × Multiplicative ℤ, inferInstance,
    (Units.coeHom _).comp (MonoidHom.fst _ _), -1, (-1, 1),
    (⊥ : Subgroup (ℚ →ₗ[ℚ] ℚ)ˣ).prod ⊤, (⊥ : Subgroup (ℚ →ₗ[ℚ] ℚ)ˣ).prod ⊤,
    fun g => ((Multiplicative.toAdd g.2 : ℤ) : ℚ), -1,
    ?_, ?_, ?_, le_rfl, fun h hh => Subgroup.Normal.conj_mem inferInstance h hh _, ?_, ?_,
    rfl, ⟨0, ?_⟩,
    ⟨(1, Multiplicative.ofAdd 1), ?_, ?_⟩⟩
  · simp
  · intro h
    have h1 := (Subgroup.mem_prod.1 h).1
    rw [Subgroup.mem_bot] at h1
    have := congrArg (fun u : (ℚ →ₗ[ℚ] ℚ)ˣ => (u : ℚ →ₗ[ℚ] ℚ) 1) h1
    norm_num at this
  · ext <;> simp [pow_two]
  · intro h hh
    have h1 := (Subgroup.mem_prod.1 hh).1
    rw [Subgroup.mem_bot] at h1
    simp [h1]
  · intro g hg g' _
    have h1 := (Subgroup.mem_prod.1 hg).1
    rw [Subgroup.mem_bot] at h1
    simp [h1]
  · intro g _
    simp
  · exact Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩
  · simp

/-- Lines 5103-5107, PROVED. **Polarization.** Let `x : H → M` be additive,
`x(h₁h₂) = x h₁ + x h₂`, and `Q` a quadratic map with `Q(x h) = 0` for every `h`. Then the polar
form `Q(a+b) - Q(a) - Q(b)` vanishes on all pairs of actual evaluations, hence on their linear
span. So `Q` vanishes on the span: `2Q(v)` is the polar form at `(v, v)`, and
`(2 : k) ≠ 0`. -/
theorem polarization_vanish {k M H : Type*} [Field k] [AddCommGroup M] [Module k M] [Mul H]
    (h2 : (2 : k) ≠ 0) (x : H → M) (hx : ∀ h₁ h₂, x (h₁ * h₂) = x h₁ + x h₂)
    (Q : QuadraticMap k M k) (hQ : ∀ h, Q (x h) = 0) :
    ∀ v ∈ Submodule.span k (Set.range x), Q v = 0 := by
  have hpol : ∀ h₁ h₂, QuadraticMap.polar Q (x h₁) (x h₂) = 0 := by
    intro h₁ h₂
    rw [QuadraticMap.polar, ← hx, hQ, hQ, hQ, sub_zero, sub_zero]
  have hspan : ∀ v ∈ Submodule.span k (Set.range x), ∀ w ∈ Submodule.span k (Set.range x),
      QuadraticMap.polar Q v w = 0 := by
    intro v hv w hw
    induction hv using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨h₁, rfl⟩ := ha
      induction hw using Submodule.span_induction with
      | mem b hb => obtain ⟨h₂, rfl⟩ := hb; exact hpol h₁ h₂
      | zero => exact QuadraticMap.polar_zero_right Q _
      | add b b' _ _ ih ih' => rw [QuadraticMap.polar_add_right, ih, ih', add_zero]
      | smul r b _ ih => rw [QuadraticMap.polar_smul_right, ih, smul_zero]
    | zero => exact QuadraticMap.polar_zero_left Q _
    | add a a' _ _ ih ih' => rw [QuadraticMap.polar_add_left, ih, ih', add_zero]
    | smul r a _ ih => rw [QuadraticMap.polar_smul_left, ih, smul_zero]
  intro v hv
  have h := hspan v hv v hv
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul] at h
  exact (mul_eq_zero.1 h).resolve_left h2

/-- Lines 5102-5107, PROVED. **Contrapositive of the polarization.** If the `k`-span of the
values `x h` contains a vector `v` with `Q v ≠ 0`, then there is an actual `h` with
`Q (x h) ≠ 0`. -/
theorem polarization_exists {k M H : Type*} [Field k] [AddCommGroup M] [Module k M] [Mul H]
    (h2 : (2 : k) ≠ 0) (x : H → M) (hx : ∀ h₁ h₂, x (h₁ * h₂) = x h₁ + x h₂)
    (Q : QuadraticMap k M k) (v : M) (hv : v ∈ Submodule.span k (Set.range x))
    (hQv : Q v ≠ 0) : ∃ h, Q (x h) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hQv (polarization_vanish h2 x hx Q hcon v hv)

/-- Lines 5100-5107, PROVED. **Both coordinates at once.** Let `p_+, p_-` be the two
finite-coordinate maps, with values the coordinates along `k e_+` and `k e_-`. Suppose each
maps the joint evaluation span onto `k`. Then "there is an actual `h` for which both
coordinates are nonzero". Proof: some `v` in the span has both coordinates nonzero (take a
witness for each, or their sum). Apply `polarization_exists` to `Q(w) = p_+(w) p_-(w)`
(`QuadraticMap.linMulLin`). -/
theorem exists_both_coords_ne_zero {k M H : Type*} [Field k] [AddCommGroup M] [Module k M]
    [Mul H] (h2 : (2 : k) ≠ 0) (x : H → M) (hx : ∀ h₁ h₂, x (h₁ * h₂) = x h₁ + x h₂)
    (pp pm : M →ₗ[k] k)
    (hpp : ∀ a : k, ∃ w ∈ Submodule.span k (Set.range x), pp w = a)
    (hpm : ∀ a : k, ∃ w ∈ Submodule.span k (Set.range x), pm w = a) :
    ∃ h, pp (x h) ≠ 0 ∧ pm (x h) ≠ 0 := by
  obtain ⟨w₁, hw₁, h1⟩ := hpp 1
  obtain ⟨w₂, hw₂, h2'⟩ := hpm 1
  obtain ⟨v, hv, hvp, hvm⟩ :
      ∃ v ∈ Submodule.span k (Set.range x), pp v ≠ 0 ∧ pm v ≠ 0 := by
    by_cases hA : pm w₁ = 0
    · by_cases hB : pp w₂ = 0
      · refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_, ?_⟩
        · rw [map_add, h1, hB, add_zero]; exact one_ne_zero
        · rw [map_add, hA, h2', zero_add]; exact one_ne_zero
      · exact ⟨w₂, hw₂, hB, by rw [h2']; exact one_ne_zero⟩
    · exact ⟨w₁, hw₁, by rw [h1]; exact one_ne_zero, hA⟩
  obtain ⟨h, hh⟩ := polarization_exists h2 x hx (QuadraticMap.linMulLin pp pm) v hv
    (by rw [QuadraticMap.linMulLin_apply]; exact mul_ne_zero hvp hvm)
  rw [QuadraticMap.linMulLin_apply] at hh
  exact ⟨h, left_ne_zero_of_mul hh, right_ne_zero_of_mul hh⟩

end Evaluation


section Detection

variable {k : Type*} [Field k]

/-- `y ↦ e₂(y,u)` as a linear functional. -/
def e₂LeftL (u : Fin 2 → k) : (Fin 2 → k) →ₗ[k] k where
  toFun y := e₂ y u
  map_add' y y' := by simp only [e₂_apply, Pi.add_apply]; ring
  map_smul' a y := by simp only [e₂_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- `y ↦ e₂(u,y)` as a linear functional. -/
def e₂RightL (u : Fin 2 → k) : (Fin 2 → k) →ₗ[k] k where
  toFun y := e₂ u y
  map_add' y y' := by simp only [e₂_apply, Pi.add_apply]; ring
  map_smul' a y := by simp only [e₂_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Lines 5096-5101, PROVED. `1 + J` maps `T` onto the `+` axis `k e₊`, and `1 - J` maps `T`
onto the `-` axis `k e₋`. Combined with (5.5b), "the two finite-coordinate maps on the joint
span surject respectively onto `k e_+` and `k e_-`". -/
theorem finite_coord_range (h2 : (2 : k) ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) :
    LinearMap.range (1 + J) = k ∙ ep ∧ LinearMap.range (1 - J) = k ∙ em := by
  have hJJ : ∀ z, J (J z) = z := fun z => LinearMap.congr_fun hJ2 z
  constructor
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_span_plus_iff h2 hp hm he]
      simp only [LinearMap.add_apply, Module.End.one_apply, map_add, hJJ, add_comm]
    · intro hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨(2⁻¹ * a) • ep, ?_⟩
      simp only [LinearMap.add_apply, Module.End.one_apply, map_smul, hp]
      rw [← two_smul k ep, smul_smul, mul_comm (2⁻¹ * a), ← mul_assoc,
        mul_inv_cancel₀ h2, one_mul]
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_span_minus_iff h2 hp hm he]
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hJJ, neg_sub]
    · intro hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨(2⁻¹ * a) • em, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_smul, hm, sub_neg_eq_add]
      rw [← two_smul k em, smul_smul, mul_comm (2⁻¹ * a), ← mul_assoc,
        mul_inv_cancel₀ h2, one_mul]

/-- Lines 5087-5107, PROVED. **Detection of prescribed classes of opposite signs.** Take
`c_+` of sign `+1` and `c_-` of sign `-1`, and suppose their joint evaluation span on `H`
surjects to each summand. Then some actual `h ∈ H` has both finite coordinates nonzero:
`c_+((τh)^2)` is a nonzero element of `k e_+`, and `c_-((τh)^2)` is a nonzero element of
`k e_-`.
DEPARTURE: only the manuscript's "surjects to each summand" is used. Its stronger statement
"this span [is] the full direct sum" (simplicity and nonisomorphism) is not needed for this
conclusion. `W_±` are modelled on `T`, with `H` acting trivially. The Chebotarev realization
by a new inert prime (lines 5108-5112) is not formalized. -/
theorem exists_h_finite_coords_ne_zero {G : Type*} [Group G] (h2 : (2 : k) ≠ 0)
    (ρ : G →* ((Fin 2 → k) →ₗ[k] (Fin 2 → k))) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) (τ : G) (hτ : τ ^ 2 = 1) (N H : Subgroup G) (hHN : H ≤ N)
    (hHτ : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) (hH : ∀ h ∈ H, ρ h = 1) (cp cm : G → (Fin 2 → k))
    (hcp : ∀ g ∈ N, ∀ g' ∈ N, cp (g * g') = cp g + ρ g (cp g'))
    (hcm : ∀ g ∈ N, ∀ g' ∈ N, cm (g * g') = cm g + ρ g (cm g'))
    (hsp : ∃ m : Fin 2 → k, ∀ g ∈ N, J (cp (τ⁻¹ * g * τ)) - (1 : k) • cp g = ρ g m - m)
    (hsm : ∃ m : Fin 2 → k, ∀ g ∈ N, J (cm (τ⁻¹ * g * τ)) - (-1 : k) • cm g = ρ g m - m)
    (hsurjp : ∀ y : Fin 2 → k,
      ∃ w ∈ Submodule.span k (Set.range fun h : H => (cp h, cm h)), w.1 = y)
    (hsurjm : ∀ y : Fin 2 → k,
      ∃ w ∈ Submodule.span k (Set.range fun h : H => (cp h, cm h)), w.2 = y) :
    ∃ h ∈ H, cp ((τ * h) ^ 2) ∈ k ∙ ep ∧ cp ((τ * h) ^ 2) ≠ 0 ∧
      cm ((τ * h) ^ 2) ∈ k ∙ em ∧ cm ((τ * h) ^ 2) ≠ 0 := by
  obtain ⟨hrp, hrm⟩ := finite_coord_range h2 J hJ2 ep em hp hm he
  set x : H → (Fin 2 → k) × (Fin 2 → k) := fun h => (cp h, cm h) with hxdef
  have hx : ∀ h₁ h₂ : H, x (h₁ * h₂) = x h₁ + x h₂ := by
    intro h₁ h₂
    simp only [hxdef, Subgroup.coe_mul]
    rw [hcp _ (hHN h₁.2) _ (hHN h₂.2), hcm _ (hHN h₁.2) _ (hHN h₂.2), hH _ h₁.2,
      Module.End.one_apply, Module.End.one_apply, Prod.mk_add_mk]
  set D := e₂ ep em
  let pp : (Fin 2 → k) × (Fin 2 → k) →ₗ[k] k :=
    (D⁻¹ • e₂LeftL em) ∘ₗ (1 + J) ∘ₗ LinearMap.fst k (Fin 2 → k) (Fin 2 → k)
  let pm : (Fin 2 → k) × (Fin 2 → k) →ₗ[k] k :=
    (D⁻¹ • e₂RightL ep) ∘ₗ (1 - J) ∘ₗ LinearMap.snd k (Fin 2 → k) (Fin 2 → k)
  have hpp : ∀ a : k, ∃ w ∈ Submodule.span k (Set.range x), pp w = a := by
    intro a
    obtain ⟨w, hw, hw1⟩ := hsurjp ((2⁻¹ * a) • ep)
    refine ⟨w, hw, ?_⟩
    simp only [pp, LinearMap.comp_apply, LinearMap.fst_apply, hw1, LinearMap.add_apply,
      Module.End.one_apply, map_smul, hp, LinearMap.smul_apply, e₂LeftL, LinearMap.coe_mk,
      AddHom.coe_mk, smul_eq_mul]
    have h2D : e₂ (ep + ep) em = 2 * D := by
      simp only [D, e₂_apply, Pi.add_apply]; ring
    rw [h2D]
    field_simp
  have hpm : ∀ a : k, ∃ w ∈ Submodule.span k (Set.range x), pm w = a := by
    intro a
    obtain ⟨w, hw, hw2⟩ := hsurjm ((2⁻¹ * a) • em)
    refine ⟨w, hw, ?_⟩
    simp only [pm, LinearMap.comp_apply, LinearMap.snd_apply, hw2, LinearMap.sub_apply,
      Module.End.one_apply, map_smul, hm, sub_neg_eq_add, LinearMap.smul_apply,
      e₂RightL, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    have h2D : e₂ ep (em + em) = 2 * D := by
      simp only [D, e₂_apply, Pi.add_apply]; ring
    rw [h2D]
    field_simp
  obtain ⟨h, hhp, hhm⟩ := exists_both_coords_ne_zero h2 x hx pp pm hpp hpm
  have e1 := eval_tau_h_sq ρ J τ hτ N H hHN hHτ hH cp hcp 1 (Or.inl rfl) hsp h h.2
  have e2 := eval_tau_h_sq ρ J τ hτ N H hHN hHτ hH cm hcm (-1) (Or.inr rfl) hsm h h.2
  rw [one_smul] at e1
  replace e2 : cm ((τ * h) ^ 2) = (1 - J) (cm h) := by
    rw [e2]; simp [sub_eq_add_neg]
  refine ⟨h, h.2, ?_, ?_, ?_, ?_⟩
  · rw [e1, ← hrp]; exact LinearMap.mem_range_self _ _
  · rw [e1]; intro h0
    apply hhp
    simp only [pp, x, LinearMap.comp_apply, LinearMap.fst_apply, h0, map_zero]
  · rw [e2, ← hrm]; exact LinearMap.mem_range_self _ _
  · rw [e2]; intro h0
    apply hhm
    simp only [pm, x, LinearMap.comp_apply, LinearMap.snd_apply, h0, map_zero]

end Detection

section Examples

-- The examples below show the hypotheses are satisfiable: `J = diag(1, -1)` over `ℚ`,
-- `e₊ = (1, 0)`, `e₋ = (0, 1)`, `ε = 1`. Both bookkeeping theorems apply to explicit data.

private def Jdiag : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' !![1, 0; 0, -1]

private lemma Jdiag_apply (y : Fin 2 → ℚ) : Jdiag y = ![y 0, -y 1] := by
  ext i; fin_cases i <;> simp [Jdiag, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

private lemma Jdiag_sq : Jdiag ∘ₗ Jdiag = LinearMap.id := by
  ext y i; fin_cases i <;> simp [Jdiag_apply]

private lemma Jdiag_det : LinearMap.det Jdiag = -1 := by
  rw [Jdiag, LinearMap.det_toLin', Matrix.det_fin_two_of]; norm_num

private lemma Jdiag_ep : Jdiag ![1, 0] = ![1, 0] := by
  rw [Jdiag_apply]; ext i; fin_cases i <;> simp

private lemma Jdiag_em : Jdiag ![0, 1] = -![0, 1] := by
  rw [Jdiag_apply]; ext i; fin_cases i <;> simp

private lemma e₂_std : e₂ (![1, 0] : Fin 2 → ℚ) ![0, 1] ≠ 0 := by simp

example : (2 : ℚ) ≠ 0 ∧ Jdiag ∘ₗ Jdiag = LinearMap.id ∧ LinearMap.det Jdiag = -1 :=
  ⟨two_ne_zero, Jdiag_sq, Jdiag_det⟩

example : Module.finrank ℚ (Fin 1 → ℚ) + Module.finrank ℚ (Fin 0 → ℚ) + 2
    = Module.finrank ℚ (Fin 2 → ℚ) + Module.finrank ℚ (Fin 1 → ℚ) := by
  have hne : (![1, 0] : Fin 2 → ℚ) ≠ 0 := fun h => by simpa using congrFun h 0
  have hne' : (![0, 1] : Fin 2 → ℚ) ≠ 0 := fun h => by simpa using congrFun h 1
  refine (bookkeeping_mixed (k := ℚ) two_ne_zero 1 one_ne_zero Jdiag ![1, 0] ![0, 1] Jdiag_ep
    Jdiag_em e₂_std (finAxis ![1, 0]) (finAxis ![0, 1])
    (finAxis_selfAnnihilating (crossPair_plus_ne_zero one_ne_zero Jdiag_em e₂_std))
    (finAxis_selfAnnihilating (crossPair_minus_ne_zero one_ne_zero Jdiag_ep e₂_std))
    ⟨(![1, 0], 0), mem_finAxis.2 ⟨1, by simp⟩, mem_finAxis.2 ⟨1, by simp⟩, by simp [hne]⟩
    ⟨(![0, 1], 0), mem_finAxis.2 ⟨1, by simp⟩, mem_finAxis.2 ⟨1, by simp⟩, by simp [hne']⟩
    (K0p := Fin 1 → ℚ) (K0m := Fin 0 → ℚ) (Vp := Fin 2 → ℚ) (Vm := Fin 1 → ℚ)
    (Vp' := Fin 1 → ℚ) (Vm' := Fin 0 → ℚ) ?_ ?_ ?_ ?_).2.2.2.2.1
  · rw [inf_idem, finrank_finAxis hne]; simp
  · rw [inf_idem, finrank_finAxis hne']; simp
  · rw [finAxis_inf_singAxis, finrank_bot]; simp
  · rw [finAxis_inf_singAxis, finrank_bot]; simp

example : Module.finrank ℚ (Fin 1 → ℚ) + Module.finrank ℚ (Fin 1 → ℚ) = 2 := by
  have hne : (![1, 0] : Fin 2 → ℚ) ≠ 0 := fun h => by simpa using congrFun h 0
  refine (bookkeeping_single_sign (k := ℚ) two_ne_zero 1 one_ne_zero Jdiag ![1, 0] ![0, 1]
    Jdiag_ep Jdiag_em e₂_std (finAxis ![1, 0]) (singAxis ![1, 0])
    (finAxis_selfAnnihilating (crossPair_plus_ne_zero one_ne_zero Jdiag_em e₂_std))
    (singAxis_selfAnnihilating (crossPair_minus_ne_zero one_ne_zero Jdiag_ep e₂_std))
    ⟨(![1, 0], 0), mem_finAxis.2 ⟨1, by simp⟩, mem_finAxis.2 ⟨1, by simp⟩, by simp [hne]⟩
    (K0p := Fin 1 → ℚ) (K0m := Fin 0 → ℚ) (Vp := Fin 2 → ℚ) (Vm := Fin 0 → ℚ)
    (Vp' := Fin 1 → ℚ) (Vm' := Fin 1 → ℚ) 2 one_lt_two (by simp) (by simp) ?_ ?_ ?_ ?_).2.2.2.2.2.1
  · rw [inf_idem, finrank_finAxis hne]; simp
  · rw [inf_comm, finAxis_inf_singAxis, finrank_bot]; simp
  · rw [finAxis_inf_singAxis, finrank_bot]; simp
  · rw [inf_idem, finrank_singAxis hne]; simp

-- Translations of `ℚ²`, as a subgroup of the permutation group of `ℚ²`.
private def transl : Subgroup (Equiv.Perm (Fin 2 → ℚ)) where
  carrier := {g | ∀ x, g x = x + g 0}
  mul_mem' {a b} ha hb x := by
    show a (b x) = x + a (b 0)
    rw [hb x, ha (x + b 0), ha (b 0), add_assoc]
  one_mem' x := by simp
  inv_mem' {a} ha x := by
    have h1 : ∀ y, a⁻¹ y = y - a 0 := fun y => by
      have := ha (a⁻¹ y)
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
      exact eq_sub_of_add_eq this.symm
    rw [h1 x, h1 0, zero_sub, sub_eq_add_neg]

-- The coordinate swap of `ℚ²`, an involution normalizing the translations.
private def swap2 : Equiv.Perm (Fin 2 → ℚ) where
  toFun x := ![x 1, x 0]
  invFun x := ![x 1, x 0]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl

private lemma swap2_apply (x : Fin 2 → ℚ) : swap2 x = ![x 1, x 0] := rfl

private lemma swap2_inv_apply (x : Fin 2 → ℚ) : swap2⁻¹ x = ![x 1, x 0] := rfl

private lemma swap2_zero : swap2 0 = 0 := by ext i; fin_cases i <;> rfl

-- The hypotheses of `exists_h_finite_coords_ne_zero` are satisfiable, with joint span all of
-- `T × T`: `G` = permutations of `ℚ²`, `H = N` = translations, `τ` = the coordinate swap,
-- `ρ` trivial, `J = diag(1, -1)`, `c_+(g) = (v₀ + v₁, v₀ - v₁)` and
-- `c_-(g) = (v₀ - v₁, v₀ + v₁)`, where `v = g 0`. (When `τ` acts trivially on `H`, these
-- hypotheses force the span into an eigenline. So `τ` must act nontrivially.)
example : True := by
  have hτ : swap2 ^ 2 = 1 := by
    ext x i; fin_cases i <;> simp [pow_two, swap2_apply]
  have hHτ : ∀ h ∈ transl, swap2 * h * swap2⁻¹ ∈ transl := by
    intro h hh x
    have hx := hh (swap2⁻¹ x)
    have h0 := hh (swap2⁻¹ 0)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hx h0 ⊢
    rw [hx, h0]
    ext i; fin_cases i <;> simp [swap2_apply, swap2_inv_apply]
  have hcoc : ∀ (f : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)), ∀ g ∈ transl, ∀ g' ∈ transl,
      f ((g * g') 0) = f (g 0) +
        (1 : Equiv.Perm (Fin 2 → ℚ) →* ((Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ))) g (f (g' 0)) := by
    intro f g hg g' _
    rw [MonoidHom.one_apply, Module.End.one_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      hg (g' 0), map_add, add_comm]
  let fp : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' !![1, 1; 1, -1]
  let fm : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' !![1, -1; 1, 1]
  have hfp : ∀ v, fp v = ![v 0 + v 1, v 0 - v 1] := fun v => by
    ext i; fin_cases i <;> simp [fp, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, sub_eq_add_neg]
  have hfm : ∀ v, fm v = ![v 0 - v 1, v 0 + v 1] := fun v => by
    ext i; fin_cases i <;> simp [fm, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, sub_eq_add_neg]
  have hmem : ∀ v : Fin 2 → ℚ, Equiv.addRight v ∈ transl := fun v x => by simp
  have := exists_h_finite_coords_ne_zero (k := ℚ) two_ne_zero 1 Jdiag Jdiag_sq ![1, 0] ![0, 1]
    Jdiag_ep Jdiag_em e₂_std swap2 hτ transl transl le_rfl hHτ (fun _ _ => rfl)
    (fun g => fp (g 0)) (fun g => fm (g 0)) (hcoc fp) (hcoc fm) ⟨0, fun g _ => ?_⟩
    ⟨0, fun g _ => ?_⟩ (fun y => ?_) (fun y => ?_)
  · trivial
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, swap2_zero, swap2_inv_apply, map_zero,
      sub_zero, one_smul, hfp, Jdiag_apply]
    ext i; fin_cases i
    · simp
      ring
    · simp
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, swap2_zero, swap2_inv_apply, map_zero,
      sub_zero, neg_smul, one_smul, sub_neg_eq_add, hfm, Jdiag_apply]
    ext i; fin_cases i
    · simp
    · simp
      ring
  · refine ⟨_, Submodule.subset_span ⟨⟨Equiv.addRight ![(y 0 + y 1) / 2, (y 0 - y 1) / 2],
      hmem _⟩, rfl⟩, ?_⟩
    simp only [hfp, Equiv.coe_addRight, zero_add]
    ext i; fin_cases i <;> simp <;> ring
  · refine ⟨_, Submodule.subset_span ⟨⟨Equiv.addRight ![(y 0 + y 1) / 2, (y 1 - y 0) / 2],
      hmem _⟩, rfl⟩, ?_⟩
    simp only [hfm, Equiv.coe_addRight, zero_add]
    ext i; fin_cases i <;> simp <;> ring

end Examples


end QuadraticCase
end ZInQ.Manuscript.RC.Uniform

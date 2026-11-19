import ZInQKernel.Contrib.OneProof.ConradB3Verbatim
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Homomorphisms `G_m → R_{K/ℚ_p} G_m` of `ℚ_p`-tori

Step C8, sec:height, diophantine_zq.tex L760–764. Conrad's Definition B.1 (author preprint
Dec. 11, 2011, App. B, p. 32) asks for a `ℚ_p`-homomorphism of the Weil-restricted tori
`L^× = R_{L/ℚ_p}(G_m) → K^× = R_{K/ℚ_p}(G_m)`. For `L = ℚ_p` the source is `G_m`.

* `WeilTorusHom p K`: a homomorphism `G_m → R_{K/ℚ_p} G_m` of group functors on commutative
  `ℚ_p`-algebras. It is a group homomorphism `A^× → (K ⊗_{ℚ_p} A)^×` for every `A`, natural in
  `A`. Here `R_{K/ℚ_p} G_m (A) = (K ⊗_{ℚ_p} A)^×` (Weil restriction) and `G_m(A) = A^×`. By
  Yoneda, these are exactly the homomorphisms of the affine group schemes.
* `powTorusHom p K m`: the homomorphism `x ↦ (1 ⊗ x)^m` (non-vacuity of `WeilTorusHom`).
* `weilTorusHom_pow`: on `ℚ_p`-points every `WeilTorusHom` is `x ↦ x^m` for one integer `m`.
  Evaluate at the universal unit `T` of `K[T, T⁻¹]`, whose units are `c T^m`
  (`laurent_isUnit_eq`). Naturality then gives `χ(x) = c x^m`, and `χ(1) = 1` gives `c = 1`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.WeilTori

open Module LaurentPolynomial
open scoped TensorProduct LaurentPolynomial

/-! ### Units of Laurent polynomials over a field -/

/-- Every unit of `F[T, T⁻¹]` over a field is a monomial `c T^m`. Kind: PROVED. -/
theorem laurent_isUnit_eq {F : Type*} [Field F] {g : F[T;T⁻¹]} (hg : IsUnit g) :
    ∃ (c : F) (m : ℤ), g = C c * T m := by
  obtain ⟨u, rfl⟩ := hg
  set a : F[T;T⁻¹] := (u : F[T;T⁻¹]) with ha
  set b : F[T;T⁻¹] := ((u⁻¹ : F[T;T⁻¹]ˣ) : F[T;T⁻¹]) with hb
  have hab : a * b = 1 := Units.mul_inv u
  obtain ⟨n, G, hG⟩ := exists_T_pow a
  obtain ⟨n', H, hH⟩ := exists_T_pow b
  have hGH : G * H = Polynomial.X ^ (n + n') := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hG, hH, Polynomial.toLaurent_X_pow]
    calc a * T n * (b * T n') = (a * b) * (T n * T n') := by ring
      _ = T ((n + n' : ℕ) : ℤ) := by rw [hab, one_mul, ← T_add]; push_cast; rfl
  have hdvd : G ∣ Polynomial.X ^ (n + n') := ⟨H, hGH.symm⟩
  obtain ⟨i, -, v, hv⟩ := (dvd_prime_pow Polynomial.prime_X _).mp hdvd
  obtain ⟨r, -, hrv⟩ := Polynomial.isUnit_iff.mp (v⁻¹).isUnit
  have hG' : G = Polynomial.C r * Polynomial.X ^ i := by
    rw [hrv, ← hv, mul_comm G, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨r, (i : ℤ) - n, ?_⟩
  have h2 : a * T n = C r * T i := by
    rw [← hG, hG', map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
  calc a = a * T n * T (-n) := by
        rw [mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]
    _ = C r * T i * T (-n) := by rw [h2]
    _ = C r * T ((i : ℤ) - n) := by rw [mul_assoc, ← T_add, sub_eq_add_neg]

variable (p : ℕ) [Fact p.Prime]

/-! ### Homomorphisms of tori -/

/-- **A `ℚ_p`-homomorphism of tori `G_m → R_{K/ℚ_p} G_m`**, the case `L = ℚ_p` of the
homomorphisms `L^× → K^×` in Conrad's Definition B.1 (App. B, p. 32). It is a homomorphism of
group functors on commutative `ℚ_p`-algebras: for every `A`, a group homomorphism
`A^× → (K ⊗_{ℚ_p} A)^×`, natural in `A`. Kind: definition. -/
structure WeilTorusHom (K : IntermediateField ℚ_[p] (PadicAlgCl p)) where
  /-- The map on `A`-points. -/
  app : ∀ (A : Type) [CommRing A] [Algebra ℚ_[p] A], Aˣ →* (K ⊗[ℚ_[p]] A)ˣ
  /-- Naturality in the `ℚ_p`-algebra. -/
  naturality : ∀ (A B : Type) [CommRing A] [Algebra ℚ_[p] A] [CommRing B] [Algebra ℚ_[p] B]
    (f : A →ₐ[ℚ_[p]] B) (x : Aˣ),
    Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) f).toMonoidHom (app A x) =
      app B (Units.map f.toMonoidHom x)

variable {p} in
/-- The value on `ℚ_p`-points, read in `K` through `K ⊗_{ℚ_p} ℚ_p = K`. Kind: definition. -/
def WeilTorusHom.onPoints {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (χ : WeilTorusHom p K)
    (x : ℚ_[p]ˣ) : K :=
  Algebra.TensorProduct.rid ℚ_[p] ℚ_[p] K ((χ.app ℚ_[p] x : (K ⊗[ℚ_[p]] ℚ_[p])ˣ) :
    K ⊗[ℚ_[p]] ℚ_[p])

/-- **The power homomorphism** `x ↦ (1 ⊗ x)^m` (non-vacuity of `WeilTorusHom`).
Kind: definition. -/
def powTorusHom (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (m : ℤ) : WeilTorusHom p K where
  app A _ _ := (Units.map (Algebra.TensorProduct.includeRight :
    A →ₐ[ℚ_[p]] K ⊗[ℚ_[p]] A).toMonoidHom).comp (zpowGroupHom m)
  naturality A B _ _ _ _ f x := by
    simp only [MonoidHom.comp_apply, zpowGroupHom_apply, map_zpow]
    congr 1

/-- The power homomorphism on `ℚ_p`-points is `x ↦ x^m`. Kind: PROVED. -/
theorem powTorusHom_onPoints (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (m : ℤ)
    (x : ℚ_[p]ˣ) : (powTorusHom p K m).onPoints x = algebraMap ℚ_[p] K (x : ℚ_[p]) ^ m := by
  change Algebra.TensorProduct.rid ℚ_[p] ℚ_[p] K
    ((1 : K) ⊗ₜ[ℚ_[p]] ((x ^ m : ℚ_[p]ˣ) : ℚ_[p])) = _
  rw [Algebra.TensorProduct.rid_tmul, Units.val_zpow_eq_zpow_val, Algebra.smul_def, mul_one,
    map_zpow₀]

/-- **Every homomorphism `G_m → R_{K/ℚ_p} G_m` is a power on `ℚ_p`-points**: there is
`m ∈ ℤ` with `χ(x) = x^m` for all `x ∈ ℚ_p^×`. Kind: PROVED. -/
theorem weilTorusHom_pow {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (χ : WeilTorusHom p K) :
    ∃ m : ℤ, ∀ x : ℚ_[p]ˣ, χ.onPoints x = algebraMap ℚ_[p] K (x : ℚ_[p]) ^ m := by
  classical
  let cK : K →ₐ[ℚ_[p]] K[T;T⁻¹] := { (C : K →+* K[T;T⁻¹]) with commutes' := fun _ => rfl }
  let μ : K ⊗[ℚ_[p]] K[T;T⁻¹] →ₐ[ℚ_[p]] K[T;T⁻¹] :=
    Algebra.TensorProduct.productMap cK (AlgHom.id ℚ_[p] K[T;T⁻¹])
  let tA : K[T;T⁻¹]ˣ := (isUnit_T (R := K) 1).unit
  obtain ⟨c, m, hcm⟩ := laurent_isUnit_eq (Units.map μ.toMonoidHom (χ.app K[T;T⁻¹] tA)).isUnit
  let μK : K ⊗[ℚ_[p]] K →ₐ[ℚ_[p]] K :=
    Algebra.TensorProduct.productMap (AlgHom.id ℚ_[p] K) (AlgHom.id ℚ_[p] K)
  let ι : ℚ_[p] →ₐ[ℚ_[p]] K := Algebra.ofId ℚ_[p] K
  have hrid : ∀ y : K ⊗[ℚ_[p]] ℚ_[p],
      μK (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) ι y) =
        Algebra.TensorProduct.rid ℚ_[p] ℚ_[p] K y := by
    intro y
    have h : μK.comp (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) ι) =
        (Algebra.TensorProduct.rid ℚ_[p] ℚ_[p] K).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [μK, ι, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def, mul_comm]
    exact congrArg (fun F : K ⊗[ℚ_[p]] ℚ_[p] →ₐ[ℚ_[p]] K => F y) h
  have key : ∀ x : ℚ_[p]ˣ, χ.onPoints x = c * algebraMap ℚ_[p] K (x : ℚ_[p]) ^ m := by
    intro x
    let xK : Kˣ := Units.map (algebraMap ℚ_[p] K).toMonoidHom x
    let ev : K[T;T⁻¹] →ₐ[ℚ_[p]] K :=
      { eval₂ (RingHom.id K) xK with
        commutes' := fun r => by
          change eval₂ (RingHom.id K) xK (C (algebraMap ℚ_[p] K r)) = _
          rw [eval₂_C]
          rfl }
    have hev : ∀ k : K, ∀ f : K[T;T⁻¹], μK (k ⊗ₜ[ℚ_[p]] ev f) = ev (μ (k ⊗ₜ[ℚ_[p]] f)) := by
      intro k f
      simp only [μK, μ, cK, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply,
        map_mul]
      change k * ev f = eval₂ (RingHom.id K) xK (C k) * ev f
      rw [eval₂_C]
      rfl
    have hnat_ev : ∀ y : K ⊗[ℚ_[p]] K[T;T⁻¹],
        μK (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) ev y) = ev (μ y) := by
      intro y
      have h : μK.comp (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) ev) = ev.comp μ := by
        apply Algebra.TensorProduct.ext'
        intro a b
        simpa [Algebra.TensorProduct.map_tmul] using hev a b
      exact congrArg (fun F : K ⊗[ℚ_[p]] K[T;T⁻¹] →ₐ[ℚ_[p]] K => F y) h
    have hunits : Units.map ev.toMonoidHom tA = Units.map ι.toMonoidHom x := by
      apply Units.ext
      change ev (T 1) = ι (x : ℚ_[p])
      change eval₂ (RingHom.id K) xK (T 1) = _
      rw [eval₂_T, zpow_one]
      rfl
    have h1 := χ.naturality K[T;T⁻¹] K ev tA
    have h2 := χ.naturality ℚ_[p] K ι x
    rw [hunits, ← h2] at h1
    have h3 := congrArg (fun z : (K ⊗[ℚ_[p]] K)ˣ => μK (z : K ⊗[ℚ_[p]] K)) h1
    simp only [Units.coe_map] at h3
    change μK (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) ev
      (χ.app K[T;T⁻¹] tA : K ⊗[ℚ_[p]] K[T;T⁻¹])) =
      μK (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) ι
      (χ.app ℚ_[p] x : K ⊗[ℚ_[p]] ℚ_[p])) at h3
    rw [hnat_ev, hrid] at h3
    have hμ : μ (χ.app K[T;T⁻¹] tA : K ⊗[ℚ_[p]] K[T;T⁻¹]) = C c * T m := hcm
    rw [hμ, map_mul] at h3
    change χ.onPoints x = _
    unfold WeilTorusHom.onPoints
    rw [← h3]
    change eval₂ (RingHom.id K) xK (C c) * eval₂ (RingHom.id K) xK (T m) = _
    rw [eval₂_C, eval₂_T, Units.val_zpow_eq_zpow_val]
    rfl
  have hc : c = 1 := by
    have h := key 1
    rw [WeilTorusHom.onPoints, map_one, Units.val_one, map_one, Units.val_one, map_one,
      one_zpow, mul_one] at h
    exact h.symm
  exact ⟨m, fun x => by rw [key x, hc, one_mul]⟩

end HDec.G0Galois.C8Conrad.WeilTori

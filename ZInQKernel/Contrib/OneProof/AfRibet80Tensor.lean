import ZInQKernel.Contrib.OneProof.AfRibet80

/-!
# `afCharpolyDS965` is Ribet's statement in its printed `E ⊗ ℚ_ℓ` form

Ribet, *Twists of modular forms and endomorphisms of abelian varieties*, Math. Ann. 253 (1980), 43–62, §4,
pp. 50–51, states that `V = V_l(A_f)` is a free `E ⊗ ℚ_l`-module of rank 2 and that the image of a Frobenius
element at `p ∤ lN` has trace `a_p` and determinant `ε(p) p`, calculated relative to `E ⊗ ℚ_l`.
`AfRibet80TraceDetLam` reads this statement on each factor `V_λ` of the printed decomposition `V = ∏ V_λ`; this
file states it over `E ⊗ ℚ_l` itself and proves that it is equivalent to the row `AfCharpolyDS965`.

* `AfRibet80Tensor`: Ribet's statement over `R = ℚ_ℓ ⊗_ℚ E` (`E = K_f`) acting on `V_ℓ(A_f)` through `θ`
  (`R16Used.tensorModule`): `V_ℓ(A_f)` is free of rank 2 over `R`, and for `p ∤ Nℓ` the `R`-trace and the
  `R`-determinant of a Frobenius at `p` (`galR`) are `1 ⊗ a_p` and `1 ⊗ χ(p) p`.
* `charpoly_frobLam_of_tensor`, `afCharpolyDS965_of_tensor`: the row from the tensor form, by base change to
  each `E_λ` (`LinearMap.trace_baseChange`, `LinearMap.det_baseChange`).
* `semilocalQl`: `ℚ_ℓ ⊗_ℚ E ≃ ∏_{λ ∣ ℓ} E_λ`, whose `λ`-component is `rhoLam ℓ λ` (`semilocalQl_apply`): Tau Ceti's
  semi-local decomposition `TauCeti.semilocalEquiv` after Mathlib's `ℚ_ℓ ≅ ℚ_{v_ℓ}`.
* `nonempty_basis_fin`: if `r ↦ (r)_i` is an isomorphism `R ≃ ∏_i E_i` onto finitely many fields, then an
  `R`-module `V` whose base changes `E_i ⊗_R V` all have dimension `n` has an `R`-basis indexed by `Fin n`
  (`V ≅ R ⊗_R V ≅ (∏ E_i) ⊗_R V ≅ ∏ (E_i ⊗_R V) ≅ ∏ E_iⁿ ≅ Rⁿ`).
* `free_finrank_of_factors`, `trace_det_of_factors`, `afRibet80Tensor_of_traceDetLam`: the tensor form from
  Ribet's statement on the factors: `V_ℓ(A_f)` is free of rank 2 over `R` because every `V_λ` has dimension 2
  (read at one Frobenius element at a prime `p ∤ Nℓ`, which exists by Chebotarev's density theorem, proved:
  `exists_frob`), and an element of `R` is determined by its images in the `E_λ` (`eq_of_forall_rhoLam`), so the
  trace and the determinant over `R` are determined by those on the `V_λ`. No finiteness input is needed here:
  the bases of the `V_λ` give a basis of `V_ℓ(A_f)`.
* `afRibet80Tensor_of_afCharpolyDS965`, `afCharpolyDS965_iff_tensor`, `afRibet80Tensor_iff_traceDetLam`: the
  equivalences (finiteness of `V_ℓ(A)` from Mumford's torsion theorem, proved:
  `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`, through `afRibet80_of_afCharpolyDS965`).

No `sorry`, no `axiom`.
-/

set_option autoImplicit false

noncomputable section

namespace AfTateLam

open scoped TensorProduct
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open IsDedekindDomain NumberField

namespace Ribet80

/-- **Ribet, *Twists of modular forms and endomorphisms of abelian varieties*, Math. Ann. 253 (1980), 43–62, §4,
pp. 50–51, in the print's own `E ⊗ ℚ_l` form.**

* p. 50: "Let f be a newform on Γ₁(N) and let ε : (ℤ/Nℤ)* → ℂ* be its (Nebentypus) character. As in [12], we
  regard ε as a character on G = Gal(ℚ̄/ℚ), and we may view it as taking values in the coefficient field E of f.
  Let A = A_f be the factor of J₁(N) attached to f (Sect. 2). Let l be a prime (fixed in what follows), and let
  V = V_l(A) be the usual ℚ_l-adic Tate module attached to A. Then V is simultaneously, and compatibly, a
  ℚ_l[G]-module and a free E ⊗ ℚ_l-module of rank 2. The action of G on V is thus described by a map
  ρ : G → Aut_{E⊗ℚ} V ≃ GL(2, E ⊗ ℚ_l),"
* p. 51: "which is known to be the l-adic representation attached to f, because of the Eichler-Shimura relation
  (see [15, Sect. 1] and [18, Chap. 7]). This means that ρ is unramified at each prime p not dividing lN and that
  the image under ρ of a Frobenius element φ_p ∈ G for such a prime p has trace (resp. determinant) equal to a_p
  [resp. ε(p)p]. Here we calculate trace and determinant relative to E ⊗ ℚ_l, i.e., by viewing V as a free
  E ⊗ ℚ_l-module rather than a ℚ_l-vector space."
* p. 51, proof of Proposition (4.1): "We introduce the decomposition V = ∏ V_λ induced by the decomposition of
  E ⊗ ℚ_l as a product of l-adic fields E_λ."

Lean form, over the row's objects (`A_f` as in `AfShimura`, for any model of `X₁(N)`): this is the print's own
`E ⊗ ℚ_l` form, not read on the factors `V_λ` (compare `AfRibet80TraceDetLam`). `E ⊗ ℚ_l` is
`ℚ_[ℓ] ⊗[ℚ] coeffField f` (the factors in the other order), acting on `V = V_ℓ(A_f)` through `θ`
(`R16Used.tensorModule`); `V` is free of rank 2 over `E ⊗ ℚ_l` (`Module.Free`, `Module.finrank = 2`); and for
`p ∤ Nℓ` and a Frobenius `σ` at `p`, the trace and the determinant of `σ` (`galR`), calculated "relative to
E ⊗ ℚ_l" (`LinearMap.trace` and `LinearMap.det` over `ℚ_[ℓ] ⊗[ℚ] coeffField f`), are `1 ⊗ a_p` and `1 ⊗ ε(p) p`.
Reading steps: `ε(p)` is an element `c` of `E` with `c = χ(p)` in `ℂ`; unramifiedness is dropped. -/
def AfRibet80Tensor : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
    ∀ (A : AbVar ℚ) (π : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
      IsAfQuotient χ f tp δ A π → IsAfAction χ f tp δ π θ →
    ∀ [NumberField (coeffField f)] (ℓ : ℕ) [Fact ℓ.Prime],
      letI := R16Used.tensorModule ℓ A θ
      Module.Free (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ) ∧
      Module.finrank (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ) = 2 ∧
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
          LinearMap.trace (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ) (galR ℓ A θ σ) =
            (1 : ℚ_[ℓ]) ⊗ₜ ⟨coeff f p, coeff_mem_coeffField f p⟩ ∧
          LinearMap.det (galR ℓ A θ σ) = (1 : ℚ_[ℓ]) ⊗ₜ (c * (p : coeffField f))

/-! ## Modules over a finite product of fields -/

section Pi

variable {R : Type*} [CommRing R] {I : Type*} {E : I → Type*} [∀ i, Field (E i)]
  [∀ i, Algebra R (E i)]

/-- `r ↦ (r)_i`, `R → ∏_i E_i`, as an `R`-linear map. -/
def diagₗ : R →ₗ[R] (∀ i, E i) where
  toFun r i := algebraMap R (E i) r
  map_add' r s := by funext i; simp
  map_smul' r s := by funext i; simp [Algebra.smul_def]

theorem diagₗ_apply (r : R) (i : I) : diagₗ (E := E) r i = algebraMap R (E i) r := rfl

variable [Finite I]

/-- **A module over `R ≅ ∏_i E_i` (finitely many fields) whose base changes `E_i ⊗_R V` all have dimension `n` has
an `R`-basis indexed by `Fin n`:** `V ≅ R ⊗_R V ≅ (∏ E_i) ⊗_R V ≅ ∏ (E_i ⊗_R V) ≅ ∏ E_iⁿ ≅ (∏ E_i)ⁿ ≅ Rⁿ`. -/
theorem nonempty_basis_fin (hΦ : Function.Bijective (diagₗ (R := R) (E := E)))
    (V : Type*) [AddCommGroup V] [Module R V] (n : ℕ)
    (hfin : ∀ i, Module.Finite (E i) (E i ⊗[R] V))
    (hV : ∀ i, Module.finrank (E i) (E i ⊗[R] V) = n) :
    Nonempty (Module.Basis (Fin n) R V) := by
  classical
  have := Fintype.ofFinite I
  let Φₗ : R ≃ₗ[R] (∀ i, E i) := LinearEquiv.ofBijective diagₗ hΦ
  let e1 : V ≃ₗ[R] ∀ i, E i ⊗[R] V :=
    (TensorProduct.lid R V).symm ≪≫ₗ TensorProduct.congr Φₗ (LinearEquiv.refl R V) ≪≫ₗ
      TensorProduct.piLeft R V E
  let e2 : (∀ i, E i ⊗[R] V) ≃ₗ[R] ∀ i, (Fin n → E i) :=
    LinearEquiv.piCongrRight fun i =>
      haveI := hfin i
      ((Module.finBasisOfFinrankEq (E i) (E i ⊗[R] V) (hV i)).equivFun).restrictScalars R
  let e3 : (∀ i, Fin n → E i) ≃ₗ[R] (Fin n → R) :=
    { toFun := fun g j => Φₗ.symm fun i => g i j
      invFun := fun x i j => Φₗ (x j) i
      map_add' := fun g h => by
        funext j
        rw [Pi.add_apply, ← map_add]
        rfl
      map_smul' := fun r g => by
        funext j
        rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]
        rfl
      left_inv := fun g => by
        funext i j
        simp
      right_inv := fun x => by
        funext j
        simp }
  exact ⟨Module.Basis.ofEquivFun (e1 ≪≫ₗ e2 ≪≫ₗ e3)⟩

end Pi

/-! ## The semi-local decomposition `ℚ_ℓ ⊗_ℚ K ≃ ∏_{λ ∣ ℓ} K_λ` -/

section Semilocal

open scoped AdicCompletionExtension

variable (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [NumberField K]

/-- The places `λ ∣ ℓ` of `K`. -/
abbrev PlacesAbove : Type := {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver (vQ ℓ).asIdeal}

/-- **`ℚ_ℓ ⊗_ℚ K ≃ ∏_{λ ∣ ℓ} K_λ`**: Mathlib's `ℚ_ℓ ≅ ℚ_{v_ℓ}` (`Padic.adicCompletionEquiv`), then Tau Ceti's
semi-local decomposition (`TauCeti.semilocalEquiv`). -/
def semilocalQl : ℚ_[ℓ] ⊗[ℚ] K ≃+* ∀ w : PlacesAbove ℓ K, w.1.adicCompletion K :=
  letI : Algebra ℚ ((vQ ℓ).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ (vQ ℓ)
  let e : ℚ_[ℓ] ≃ₐ[ℚ] (vQ ℓ).adicCompletion ℚ :=
    ContinuousAlgEquiv.toAlgEquiv (B := (vQ ℓ).adicCompletion ℚ)
      (Padic.adicCompletionEquiv (𝓞 ℚ) (primeL ℓ))
  (Algebra.TensorProduct.congr e (AlgEquiv.refl (R := ℚ) (A₁ := K))).toRingEquiv.trans
    (TauCeti.semilocalEquiv K (vQ ℓ)).toRingEquiv

/-- The `λ`-component of `semilocalQl` is `rhoLam ℓ λ`. -/
theorem semilocalQl_apply (r : ℚ_[ℓ] ⊗[ℚ] K) (w : PlacesAbove ℓ K) :
    haveI := w.2; semilocalQl ℓ K r w = rhoLam ℓ w.1 r := by
  have := w.2
  induction r using TensorProduct.inductionOn with
  | tmul x a =>
    rw [rhoLam_tmul]
    simp only [semilocalQl, RingEquiv.coe_trans, RingEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, Function.comp_apply, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgHom.coe_id, id_eq,
      TauCeti.semilocalEquiv_tmul, HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra, algQl,
      RingHom.coe_comp]
    rfl
  | add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, map_add]

/-- **An element of `ℚ_ℓ ⊗_ℚ K` is determined by its images in the `K_λ`, `λ ∣ ℓ`.** -/
theorem eq_of_forall_rhoLam {x y : ℚ_[ℓ] ⊗[ℚ] K}
    (h : ∀ w : PlacesAbove ℓ K, haveI := w.2; rhoLam ℓ w.1 x = rhoLam ℓ w.1 y) : x = y :=
  (semilocalQl ℓ K).injective (funext fun w => by
    rw [semilocalQl_apply, semilocalQl_apply]
    exact h w)

/-- There is a place of `K` above `ℓ`. -/
theorem nonempty_placesAbove : Nonempty (PlacesAbove ℓ K) := by
  have := (vQ ℓ).isPrime
  obtain ⟨P⟩ := Ideal.nonempty_primesOver (S := 𝓞 K) (vQ ℓ).asIdeal
  exact ⟨(HeightOneSpectrum.liesOverEquivPrimesOver (𝓞 K) (vQ ℓ)).symm P⟩

/-- `ℚ_ℓ ⊗_ℚ K` acting on each `K_λ`, `λ ∣ ℓ`, through `rhoLam`. -/
abbrev algPlaces : ∀ w : PlacesAbove ℓ K, Algebra (ℚ_[ℓ] ⊗[ℚ] K) (w.1.adicCompletion K) :=
  fun w => haveI := w.2; (rhoLam ℓ w.1).toAlgebra

/-- `r ↦ (rhoLam ℓ λ r)_λ` is bijective. -/
theorem bijective_diagₗ :
    letI := algPlaces ℓ K
    Function.Bijective
      (diagₗ (R := ℚ_[ℓ] ⊗[ℚ] K) (E := fun w : PlacesAbove ℓ K => w.1.adicCompletion K)) := by
  let := algPlaces ℓ K
  have : ⇑(diagₗ (R := ℚ_[ℓ] ⊗[ℚ] K) (E := fun w : PlacesAbove ℓ K => w.1.adicCompletion K)) =
      ⇑(semilocalQl ℓ K) := by
    funext r w
    rw [diagₗ_apply, semilocalQl_apply]
    rfl
  rw [this]
  exact (semilocalQl ℓ K).bijective

end Semilocal

/-! ## `V_ℓ(A)` over `ℚ_ℓ ⊗ K` and its factors `V_λ` -/

section Factors

variable {K : Type} [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) (θ : K →+* A.End0)

/-- **The tensor form at one Frobenius gives the characteristic polynomial on each factor** (base change of the
trace and the determinant). -/
theorem charpoly_frobLam_of_tensor (lam : HeightOneSpectrum (𝓞 K)) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal]
    (hfree : letI := R16Used.tensorModule ℓ A θ; Module.Free (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ))
    (hrk : letI := R16Used.tensorModule ℓ A θ; Module.finrank (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) = 2)
    (σ : GQ) (a d : K)
    (htr : letI := R16Used.tensorModule ℓ A θ
      LinearMap.trace (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) (galR ℓ A θ σ) = (1 : ℚ_[ℓ]) ⊗ₜ a)
    (hdet : letI := R16Used.tensorModule ℓ A θ
      LinearMap.det (galR ℓ A θ σ) = (1 : ℚ_[ℓ]) ⊗ₜ d) :
    letI := R16Used.tensorModule ℓ A θ
    letI := (rhoLam ℓ lam).toAlgebra
    letI : Module.Free (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) :=
      Module.Free.of_divisionRing (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ)
    ∀ [Module.Finite (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ)],
    LinearMap.charpoly (frobLam ℓ A θ lam σ) =
      ((Polynomial.X : Polynomial (lam.adicCompletion K)) ^ 2 -
        Polynomial.C (algebraMap K (lam.adicCompletion K) a) * Polynomial.X +
        Polynomial.C (algebraMap K (lam.adicCompletion K) d)) := by
  let := R16Used.tensorModule ℓ A θ
  let := (rhoLam ℓ lam).toAlgebra
  intro _
  have := hfree
  have : Nontrivial (ℚ_[ℓ] ⊗[ℚ] K) := RingHom.domain_nontrivial (rhoLam ℓ lam)
  have : Module.Finite (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) :=
    Module.finite_of_finrank_pos (by rw [hrk]; norm_num)
  refine (charpoly_eq_iff_trace_det _ _ _).2 ⟨?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange, hrk]
  · change LinearMap.trace _ _ ((galR ℓ A θ σ).baseChange (lam.adicCompletion K)) = _
    rw [LinearMap.trace_baseChange, htr, RingHom.algebraMap_toAlgebra, rhoLam_one_tmul]
  · change LinearMap.det ((galR ℓ A θ σ).baseChange (lam.adicCompletion K)) = _
    rw [LinearMap.det_baseChange, hdet, RingHom.algebraMap_toAlgebra, rhoLam_one_tmul]

/-- **`V_ℓ(A)` is free of rank 2 over `ℚ_ℓ ⊗ K` if every factor `V_λ`, `λ ∣ ℓ`, has dimension 2.** -/
theorem free_finrank_of_factors
    (hdim : ∀ (lam : HeightOneSpectrum (𝓞 K)) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal],
      letI := R16Used.tensorModule ℓ A θ
      letI := (rhoLam ℓ lam).toAlgebra
      Module.finrank (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) = 2) :
    letI := R16Used.tensorModule ℓ A θ
    Module.Free (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) ∧ Module.finrank (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) = 2 := by
  let := R16Used.tensorModule ℓ A θ
  obtain ⟨w₀⟩ := nonempty_placesAbove ℓ K
  have : Nontrivial (ℚ_[ℓ] ⊗[ℚ] K) := by
    have := w₀.2
    exact RingHom.domain_nontrivial (rhoLam ℓ w₀.1)
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ)) := by
    let := algPlaces ℓ K
    have hdim' : ∀ w : PlacesAbove ℓ K, Module.finrank (w.1.adicCompletion K)
        (w.1.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) = 2 := fun w => by
      have := w.2
      exact hdim w.1
    exact nonempty_basis_fin (bijective_diagₗ ℓ K) (A.V ℓ) 2
      (fun w => Module.finite_of_finrank_pos (by rw [hdim' w]; norm_num)) hdim'
  exact ⟨Module.Free.of_basis b, (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)⟩

/-- **Trace and determinant over `ℚ_ℓ ⊗ K` from those on the factors `V_λ`, `λ ∣ ℓ`.** -/
theorem trace_det_of_factors
    (hfree : letI := R16Used.tensorModule ℓ A θ; Module.Free (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ))
    (hrk : letI := R16Used.tensorModule ℓ A θ; Module.finrank (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) = 2)
    (σ : GQ) (a d : K)
    (h : ∀ (lam : HeightOneSpectrum (𝓞 K)) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal],
      letI := R16Used.tensorModule ℓ A θ
      letI := (rhoLam ℓ lam).toAlgebra
      LinearMap.trace (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ)
          (frobLam ℓ A θ lam σ) = algebraMap K (lam.adicCompletion K) a ∧
        LinearMap.det (frobLam ℓ A θ lam σ) = algebraMap K (lam.adicCompletion K) d) :
    letI := R16Used.tensorModule ℓ A θ
    LinearMap.trace (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) (galR ℓ A θ σ) = (1 : ℚ_[ℓ]) ⊗ₜ a ∧
      LinearMap.det (galR ℓ A θ σ) = (1 : ℚ_[ℓ]) ⊗ₜ d := by
  let := R16Used.tensorModule ℓ A θ
  obtain ⟨w₀⟩ := nonempty_placesAbove ℓ K
  have : Nontrivial (ℚ_[ℓ] ⊗[ℚ] K) := by
    have := w₀.2
    exact RingHom.domain_nontrivial (rhoLam ℓ w₀.1)
  have := hfree
  have : Module.Finite (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) :=
    Module.finite_of_finrank_pos (by rw [hrk]; norm_num)
  constructor
  · refine eq_of_forall_rhoLam ℓ K fun w => ?_
    have := w.2
    let := (rhoLam ℓ w.1).toAlgebra
    rw [rhoLam_one_tmul, ← (h w.1).1]
    exact (LinearMap.trace_baseChange (galR ℓ A θ σ) (w.1.adicCompletion K)).symm
  · refine eq_of_forall_rhoLam ℓ K fun w => ?_
    have := w.2
    let := (rhoLam ℓ w.1).toAlgebra
    rw [rhoLam_one_tmul, ← (h w.1).2]
    exact (LinearMap.det_baseChange (A := w.1.adicCompletion K) (galR ℓ A θ σ)).symm

end Factors

/-! ## The equivalences -/

/-- **The tensor form gives the row** (base change to each `λ`-factor). -/
theorem afCharpolyDS965_of_tensor (h : AfRibet80Tensor) : AfCharpolyDS965 := by
  intro N χ f hN hf X _ jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct _ ℓ _ lam _ _ p hp hpN σ hσ
  obtain ⟨hfree, hrk, hfrob⟩ := h N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ
  obtain ⟨c, hc, htr, hdet⟩ := hfrob p hp hpN σ hσ
  exact ⟨c, hc, charpoly_frobLam_of_tensor ℓ A θ lam hfree hrk σ _ _ htr hdet⟩

/-- **Ribet's statement on the `λ`-factors gives the tensor form** (no finiteness input; the dimension of each
`V_λ` is read at a Frobenius element at some prime `p ∤ Nℓ`, which exists by Chebotarev, `exists_frob`). -/
theorem afRibet80Tensor_of_traceDetLam (h : AfRibet80TraceDetLam) : AfRibet80Tensor := by
  intro N χ f hN hf X _ jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct _ ℓ _
  obtain ⟨p₀, σ₀, hp₀, hp₀N, hσ₀⟩ :=
    exists_frob (N * ℓ) (Nat.mul_ne_zero (by omega) (Fact.out : ℓ.Prime).ne_zero)
  obtain ⟨hfree, hrk⟩ := free_finrank_of_factors ℓ A θ fun lam _ =>
    (h N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ lam p₀ hp₀ hp₀N σ₀ hσ₀).1
  refine ⟨hfree, hrk, fun p hp hpN σ hσ => ?_⟩
  obtain ⟨w₀⟩ := nonempty_placesAbove ℓ (coeffField f)
  have := w₀.2
  obtain ⟨-, c, hc, -, -⟩ :=
    h N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ w₀.1 p hp hpN σ hσ
  refine ⟨c, hc, trace_det_of_factors ℓ A θ hfree hrk σ _ _ fun lam _ => ?_⟩
  obtain ⟨-, c', hc', htr, hdet⟩ :=
    h N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ lam p hp hpN σ hσ
  have hcc : c' = c := Subtype.ext (hc'.trans hc.symm)
  rw [hcc] at hdet
  exact ⟨htr, hdet⟩

/-- **The row gives the tensor form** (finiteness of `V_ℓ(A)` from Mumford's torsion theorem, proved). -/
theorem afRibet80Tensor_of_afCharpolyDS965 (h : AfCharpolyDS965) : AfRibet80Tensor :=
  afRibet80Tensor_of_traceDetLam
    (afRibet80_of_afCharpolyDS965 ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof h)

/-- **The row `afCharpolyDS965` is equivalent to Ribet's statement in its printed `E ⊗ ℚ_ℓ` form.** -/
theorem afCharpolyDS965_iff_tensor : AfCharpolyDS965 ↔ AfRibet80Tensor :=
  ⟨afRibet80Tensor_of_afCharpolyDS965, afCharpolyDS965_of_tensor⟩

/-- Ribet's statement in the `E ⊗ ℚ_ℓ` form is equivalent to its reading on the `λ`-factors. -/
theorem afRibet80Tensor_iff_traceDetLam : AfRibet80Tensor ↔ AfRibet80TraceDetLam :=
  afCharpolyDS965_iff_tensor.symm.trans afCharpolyDS965_iff_ribet80

end Ribet80

end AfTateLam

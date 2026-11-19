import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ConjKummer
import ZInQKernel.Contrib.OneProof.RC.Uniform.Switch
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SignSplitting
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.LocalJ

/-!
# Lane RC29, round 2, item (3b): the transported pairing at a derivative prime

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`, tex 2816–2820:

> At a derivative prime the finite and singular planes are checked with this transported
> pairing. In the chosen coordinates this is the pairing `β(x,y) = ε⟨x,Jy⟩`. The `J` is therefore
> part of the duality convention, not an extra identification of an arbitrary twist with its dual.

and Lemma `ex:limits-derivative-switch` (tex 4834–4904), in particular tex 4859–4863 (the split
local model `L_v = D⁰ ⊕ (F_v ⊕ S_v)[−1] ⊕ D²[−2]` "with the transported pairing") and tex
4888–4890 ("At a new inert prime the finite and singular planes are free of rank two, with cross
pairing `β(x,y) = ε⟨x,Jy⟩`").

What is formalized (PROVED):

* **(i) The transported coefficient pairing in coordinates.** Lane RC28's `conjPairing`
  `M_i × τ^*M_i → A_i(1)`, `(v, w) ↦ e(v, ρ_T(τ) w)` (tex 2798–2804) is, read in `A_i`
  (`conjDerPairing_eq`), the pairing `weilA v (conjBC w)` with `conjBC = id ⊗ ρ_T(τ)`. In the
  coordinates `x, y ∈ A²` of any pair `u₀, u₁` of `A ⊗ E[2^i]` on which `ρ_T(τ)` has matrix `J`
  (`hJ`), it is `β(x,y) = ε · e₂(x, J y)` with `ε = e(u₀, u₁)` (`conjDerPairing_coord`): the
  manuscript's `β(x,y) = ε⟨x,Jy⟩`, with `⟨·,·⟩ = e₂` the determinant pairing; over a field this is
  lane RC's `crossPairing ε J` (`conjDer_coord_eq_crossPairing`). The ingredients are the
  alternation of the Weil pairing (`conjDerWeilA_self`, from the vendored `weilPairing_self`) and
  bilinearity. The matrix `J` exists for every basis (`conjDer_matrix_spec`); lane RC29's
  `tateTorsQuotEquiv_conjTors` (`TateLevel.lean`) identifies `conjTors` with `ρ_T(τ)` modulo `2^i`.
  So `J` is the matrix of the actual `ρ_T(τ)`: it is part of the pairing `M_i ⊗ τ^*M_i → R_i(1)`,
  not an identification of `M_i` with its dual.
* **(ii) The transported pairing on the finite and singular planes at an inert derivative prime.**
  If the local pairing of `F_v ⊕ S_v` (coordinates `T × T`, `T = A²`, finite coordinate first) is
  `planePairing (ε₀ e₂) σ` and the transport acts by `(x, y) ↦ (J x, −J y)` (the other group's
  `localInv J`), with `J² = 1` and `det J = −1`, then the transported pairing
  `(a, b) ↦ ⟨a, (J, −J) b⟩` is exactly lane RC's switch pairing `switchPairing (−ε₀) σ J`, i.e.
  the finite and singular planes stay isotropic and the cross pairing is
  `β(x,y) = ε⟨x,Jy⟩` with `ε = −ε₀` (`conjDer_transportedPairing`, `conjDer_cross`,
  `conjDer_finite_isotropic`, `conjDer_singular_isotropic`, `conjDer_cross_isPerfPair`). The key
  identity is `e₂(Jx, y) = −e₂(x, Jy)` (`conjDer_weil_J_left`).
* Non-vacuity of `J² = 1`, `det J = −1`: `conjDer_nonvacuous` (`J = diag(1, −1)`).

What is NOT formalized here (flagged):

* GLUE (local Tate duality at a tame prime, Nekovář, *Selmer complexes*, Astérisque 310 (2006),
  Sections 5.2 and 6.3 — UNVERIFIED locators): the cup product
  `H¹(K_v, M_i) × H¹(K_v, M_i^*(1)) → A_i` at an inert derivative prime, in the finite/singular
  coordinates `(c(Frob), c(σ_tame))`, has the shape `planePairing (ε₀ e₂) σ` (the hypothesis
  `hP` of `conjDer_transportedPairing_of`). The other group states the same input as
  `ResiduePairing` (`Hsw/Coordinates.lean`).
* ELLIOT (tex 5027–5037; PROVED by the other group in cocycle coordinates as `LocalJAction`,
  `SwitchInputs/LocalJ.lean`, with their GLUE that the genuine transport is the cocycle action):
  at the derivative prime the transport acts on `F_v ⊕ S_v` by `(J, −J)`. Lane RC29's
  `conjTransportFixed_rep` (`ConjTransport.lean`) shows that the transport at a fixed place is the
  transport by the local representative of conjugation, the cocycle action of `LocalJ.lean`.
* ELLIOT/GLUE (tex 2802–2803: "`e₂` transforms by the cyclotomic character"): `det ρ_T(τ) = −1`
  (complex conjugation inverts the roots of unity). Kept as the hypothesis `hdet`.
* ELLIOT (tex 4893–4898, cited to Nekovář 6.3.3–6.3.4): the relaxed localization image is its own
  annihilator for the transported pairing; formalized as a hypothesis by lane RC's
  `relaxed_image_eq_span` (`Uniform/Switch.lean`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain WeierstrassCurve TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.Uniform (weil weil_apply planePairing planePairing_apply crossPairing
  crossPairing_apply switchPairing crossPairing_isPerfPair)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (localInv localInv_apply)

/-! ### (i) The Weil pairing is alternating -/

section Alternating

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)
  (A : Type) [CommRing A] [Algebra (ZMod N) A]

/-- PROVED (vendored `weilPairing_self`, Silverman III.8.1). `e_N(P, P) = 0` on `E(K_S)[N]`. -/
theorem conjDerWeilS_self (P : TorsS K S W N) : weilS W hμ P P = 0 := by
  have h := TauCeti.Isogeny.weilPairing_self (W.baseChange (AlgebraicClosure K)) N
    (natCast_ne_zero_bar N) (inclTors W N P)
  change weilBar W N (inclTors W N P) (inclTors W N P) = 0 at h
  rw [weilS_apply, h, map_zero]

/-- PROVED (lane RC28's `weilBar_skew`). `e_N(Q, P) = −e_N(P, Q)` on `E(K_S)[N]`. -/
theorem conjDerWeilS_swap (P Q : TorsS K S W N) : weilS W hμ Q P = -weilS W hμ P Q := by
  rw [weilS_apply, weilS_apply, weilBar_skew, map_neg]

/-- PROVED. The `A`-bilinear Weil pairing is skew: `e(y, x) = −e(x, y)`. -/
theorem conjDerWeilA_swap (x y : A ⊗[ℤ] TorsS K S W N) :
    weilA W hμ A y x = -weilA W hμ A x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a P =>
    induction y using TensorProduct.inductionOn with
    | tmul b Q =>
      rw [weilA_tmul, weilA_tmul, conjDerWeilS_swap, map_neg]
      ring
    | add y y' hy hy' =>
      simp only [map_add, LinearMap.add_apply]
      rw [hy, hy', neg_add]
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hx', neg_add]

/-- PROVED. The `A`-bilinear Weil pairing is alternating: `e(x, x) = 0`. -/
theorem conjDerWeilA_self (x : A ⊗[ℤ] TorsS K S W N) : weilA W hμ A x x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a P => rw [weilA_tmul, conjDerWeilS_self, map_zero, mul_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy, conjDerWeilA_swap W hμ A x y]
    ring

/-- PROVED. **The Weil pairing in the coordinates of a pair** `u₀, u₁`:
`e(x₀u₀ + x₁u₁, y₀u₀ + y₁u₁) = (x₀y₁ − x₁y₀) · e(u₀, u₁)`. -/
theorem conjDerWeilA_coord (u : Fin 2 → A ⊗[ℤ] TorsS K S W N) (x y : Fin 2 → A) :
    weilA W hμ A (∑ i, x i • u i) (∑ j, y j • u j) =
      (x 0 * y 1 - x 1 * y 0) * weilA W hμ A (u 0) (u 1) := by
  simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, conjDerWeilA_self, conjDerWeilA_swap W hμ A (u 0) (u 1)]
  ring

end Alternating

/-! ### (i) The transported coefficient pairing `β(x,y) = ε⟨x,Jy⟩` -/

section CoefPairing

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) [W.IsElliptic]
  (hW : W.map (C.κ : K →+* K) = W) {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)
  (A : Type) [CommRing A] [Algebra (ZMod N) A] (α : GKS K S →* Aˣ)

/-- PROVED (definitional). **The transported coefficient pairing** (lane RC28's `conjPairing`,
`(v, w) ↦ e(v, ρ_T(τ) w)`, tex 2798–2804), read in `A` through `A(1) ≃ A`: it is
`weilA v (conjBC w)`, `conjBC = id ⊗ ρ_T(τ)`. -/
theorem conjDerPairing_eq (v : CoefMod A α (TorsS K S W N))
    (w : PullMod C.conj (CoefMod A α (TorsS K S W N))) :
    (CharMod.equiv A (cycA A hμ)) (conjPairing C W hW hμ A α v w) =
      weilA W hμ A (show A ⊗[ℤ] TorsS K S W N from v)
        (conjBC C W hW A (show A ⊗[ℤ] TorsS K S W N from w)) :=
  rfl

omit [W.IsElliptic] [NeZero N] [Algebra (ZMod N) A] in
/-- PROVED. **The matrix of `ρ_T(τ)` in a basis**: for an `A`-basis `b` of `A ⊗ E(K_S)[N]`, the
matrix `J = toMatrix b b (id ⊗ ρ_T(τ))` satisfies the hypothesis `hJ` of
`conjDerPairing_coord` (non-vacuity of `hJ`). -/
theorem conjDer_matrix_spec (b : Module.Basis (Fin 2) A (A ⊗[ℤ] TorsS K S W N)) (j : Fin 2) :
    conjBC C W hW A (b j) = ∑ i, LinearMap.toMatrix b b (conjBC C W hW A) i j • b i := by
  simp only [LinearMap.toMatrix_apply]
  exact (b.sum_repr _).symm

/-- PROVED (tex 2816–2818: "In the chosen coordinates this is the pairing `β(x,y)=ε⟨x,Jy⟩`").
**The transported pairing in coordinates**: for a pair `u₀, u₁` on which `ρ_T(τ)` has the matrix
`J` (hypothesis `hJ`; it holds for every basis, `conjDer_matrix_spec`),
`e(x₀u₀ + x₁u₁, ρ_T(τ)(y₀u₀ + y₁u₁)) = ε · e₂(x, J y)` with `ε = e(u₀, u₁)` and `e₂` the
determinant pairing. -/
theorem conjDerPairing_coord (u : Fin 2 → A ⊗[ℤ] TorsS K S W N)
    (J : Matrix (Fin 2) (Fin 2) A)
    (hJ : ∀ j, conjBC C W hW A (u j) = ∑ i, J i j • u i) (x y : Fin 2 → A) :
    weilA W hμ A (∑ i, x i • u i) (conjBC C W hW A (∑ j, y j • u j)) =
      weilA W hμ A (u 0) (u 1) * (x 0 * (J.mulVec y) 1 - x 1 * (J.mulVec y) 0) := by
  have hc : conjBC C W hW A (∑ j, y j • u j) = ∑ i, (J.mulVec y) i • u i := by
    rw [Fin.sum_univ_two, map_add, map_smul, map_smul, hJ, hJ]
    simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    module
  rw [hc, conjDerWeilA_coord, mul_comm]

/-- PROVED. Over a field, the coordinate expression of `conjDerPairing_coord` is lane RC's cross
pairing `crossPairing ε J` (`Uniform/Switch.lean`, tex 4888–4890). -/
theorem conjDer_coord_eq_crossPairing {k : Type} [Field k] (ε : k) (J : Matrix (Fin 2) (Fin 2) k)
    (x y : Fin 2 → k) :
    ε * (x 0 * (J.mulVec y) 1 - x 1 * (J.mulVec y) 0) = crossPairing ε J x y := by
  rw [crossPairing_apply, weil_apply]

end CoefPairing

/-! ### (ii) The transported pairing on the finite and singular planes -/

section Planes

variable {k : Type} [Field k]

/-- PROVED. `e₂(Jx, Jz) = det J · e₂(x, z)`. -/
theorem conjDer_weil_mulVec (J : Matrix (Fin 2) (Fin 2) k) (x z : Fin 2 → k) :
    weil (J.mulVec x) (J.mulVec z) = J.det * weil x z := by
  simp only [weil_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- PROVED. **For `J² = 1` and `det J = −1`: `e₂(Jx, y) = −e₂(x, Jy)`.** -/
theorem conjDer_weil_J_left {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1) (hdet : J.det = -1)
    (x y : Fin 2 → k) : weil (J.mulVec x) y = -weil x (J.mulVec y) := by
  have h := conjDer_weil_mulVec J x (J.mulVec y)
  rw [Matrix.mulVec_mulVec, hJ2, Matrix.one_mulVec, hdet] at h
  rw [h, neg_one_mul]

/-- PROVED (tex 2816–2820, 4859–4863, 4888–4890). **The transported pairing on `F_v ⊕ S_v`**:
for the local pairing `planePairing (ε₀ e₂) σ` of the finite and singular planes (coordinates
`T × T`) and the transport `localInv J : (x, y) ↦ (J x, −J y)` with `J² = 1`, `det J = −1`, the
transported pairing `(a, b) ↦ ⟨a, (J, −J) b⟩` is lane RC's switch pairing with cross pairing
`β(x,y) = ε⟨x,Jy⟩`, `ε = −ε₀`. Hypotheses `hJ2` (tex 2802: `ρ_T(τ)² = 1`), `hdet`
(ELLIOT/GLUE, tex 2802–2803). -/
theorem conjDer_transportedPairing (ε₀ σ : k) {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (hdet : J.det = -1) (a b : (Fin 2 → k) × (Fin 2 → k)) :
    planePairing (ε₀ • weil) σ a (localInv J.mulVecLin b) = switchPairing (-ε₀) σ J a b := by
  rw [planePairing_apply, planePairing_apply, localInv_apply, crossPairing_apply,
    crossPairing_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply, map_neg,
    conjDer_weil_J_left hJ2 hdet]
  ring

/-- PROVED. **The cross pairing of the transported pairing** (tex 4888–4890):
`⟨(x, 0), (J, −J)(0, y)⟩ = β(x, y) = ε⟨x, Jy⟩`, `ε = −ε₀`. -/
theorem conjDer_cross (ε₀ σ : k) {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (hdet : J.det = -1) (x y : Fin 2 → k) :
    planePairing (ε₀ • weil) σ (x, 0) (localInv J.mulVecLin (0, y)) = crossPairing (-ε₀) J x y := by
  rw [conjDer_transportedPairing ε₀ σ hJ2 hdet]
  simp [planePairing_apply]

/-- PROVED. **The finite plane is isotropic for the transported pairing** ("the finite and singular
planes are checked with this transported pairing", tex 2816–2817). -/
theorem conjDer_finite_isotropic (ε₀ σ : k) {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (hdet : J.det = -1) (x x' : Fin 2 → k) :
    planePairing (ε₀ • weil) σ (x, 0) (localInv J.mulVecLin (x', 0)) = 0 := by
  rw [conjDer_transportedPairing ε₀ σ hJ2 hdet]
  simp [planePairing_apply]

/-- PROVED. **The singular plane is isotropic for the transported pairing.** -/
theorem conjDer_singular_isotropic (ε₀ σ : k) {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (hdet : J.det = -1) (y y' : Fin 2 → k) :
    planePairing (ε₀ • weil) σ (0, y) (localInv J.mulVecLin (0, y')) = 0 := by
  rw [conjDer_transportedPairing ε₀ σ hJ2 hdet]
  simp [planePairing_apply]

/-- PROVED (lane RC's `crossPairing_isPerfPair`). **The transported cross pairing is perfect**
for `ε₀ ≠ 0`. -/
theorem conjDer_cross_isPerfPair {ε₀ : k} (hε₀ : ε₀ ≠ 0) {J : Matrix (Fin 2) (Fin 2) k}
    (hJ2 : J * J = 1) : (crossPairing (-ε₀) J).IsPerfPair :=
  crossPairing_isPerfPair (neg_ne_zero.2 hε₀) hJ2

/-- PROVED. **The transported pairing at a derivative prime, from its two inputs**: if the local
pairing `P` of `F_v ⊕ S_v` is `planePairing (ε₀ e₂) σ` (hypothesis `hP`: GLUE, local Tate duality
at a tame prime in the finite/singular coordinates, tex 4859–4863) and the transport `Θ` acts by
`(J, −J)` (hypothesis `hΘ`: ELLIOT tex 5027–5037, the other group's `LocalJAction` in cocycle
coordinates), then the transported pairing `⟨a, Θ b⟩` is `switchPairing (−ε₀) σ J`. -/
theorem conjDer_transportedPairing_of (ε₀ σ : k) {J : Matrix (Fin 2) (Fin 2) k}
    (hJ2 : J * J = 1) (hdet : J.det = -1)
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)))
    (hP : P = planePairing (ε₀ • weil) σ)
    (Θ : (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (hΘ : Θ = localInv J.mulVecLin) (a b : (Fin 2 → k) × (Fin 2 → k)) :
    P a (Θ b) = switchPairing (-ε₀) σ J a b := by
  subst hP hΘ
  exact conjDer_transportedPairing ε₀ σ hJ2 hdet a b

/-- PROVED. **Non-vacuity** of `J² = 1`, `det J = −1` (and of `ε₀ ≠ 0`): `J = diag(1, −1)` over
`ℚ`, and then the transported cross pairing is `β(x,y) = −⟨x, Jy⟩`. -/
theorem conjDer_nonvacuous :
    ∃ J : Matrix (Fin 2) (Fin 2) ℚ, J * J = 1 ∧ J.det = -1 ∧
      ∀ x y, planePairing ((1 : ℚ) • weil) 1 (x, 0) (localInv J.mulVecLin (0, y)) =
        crossPairing (-1) J x y := by
  refine ⟨!![1, 0; 0, -1], ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [Matrix.det_fin_two]
  · intro x y
    refine conjDer_cross 1 1 ?_ ?_ x y
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · simp [Matrix.det_fin_two]

end Planes

end ZInQ.Manuscript.RC.KummerMaps

import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitTransport
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Pairing

/-!
# Lane RC31, round 2: the fibre pairing is the transported cross pairing in coordinates

Manuscript `diophantine_zq.tex`: the Weil pairing `M_i ⊗ τ^*M_i → R_i(1)`,
`(v, w) ↦ e₂(v, ρ_T(τ) w)` (tex 2798–2805), with `J = ρ_T(τ)` ((H12), tex 3093), and "the
transported cross pairing is exactly `β(x, y) = ε e₂(x, J y)`, `ε ∈ k^×`" (tex 5037).

* `betaVP_conjVPv_eq`: in the coordinates of lane RC28's basis `vpBasis`, the determinant form
  `β_𝔭(v, J w)` is `crossPairing 1 J` with `J = conjMatrix` (the matrix of `ρ_T(τ)`).
* **`betaConj_vpBasis`**: lane RC31's transported fibre pairing `betaConj` (values in the twist
  `k(𝔭)(1)`, read in `k(𝔭)` through `Tate1P.equiv`) is `crossPairing 1 J` in the coordinates of
  `vpBasis`, i.e. `(x, y) ↦ e₂(x, J y)` with `e₂` the determinant form, `ε = 1` (tex 5037).

Kind: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain TensorProduct Matrix
open Module (Basis)
open ZInQ.Manuscript.RC.Uniform (Lambda crossPairing crossPairing_apply weil weil_apply)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (ActualConj PullMod)
open ZInQ.Manuscript.RC.LambdaCoef

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (C.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W] (P : Ideal Lambda) [P.IsPrime]
  (α : GKS K S →* Lambdaˣ)

/-- **The transported determinant form on basis vectors** (tex 2798–2805, 3093):
`β_𝔭(1 ⊗ b i, J (1 ⊗ b j))` is the image in `k(𝔭)` of `detT (b i) (J b j)`, whose coordinates are
the entries of the matrix of `J`. Kind: PROVED. -/
theorem betaVP_conjVPv_basis (i j : Fin 2) :
    betaVP W P α (vpBasis P i) (conjVPv C W hW P α (vpBasis P j)) =
      crossPairing 1 (conjMatrix C W hW P) (Pi.single i 1) (Pi.single j 1) := by
  have h1 : conjVPv C W hW P α (vpBasis P j) =
      show VP K S W P α⁻¹ from (1 : ResAt P) ⊗ₜ conjTate C W hW (tateBasis j) := by
    rw [vpBasis_apply']
    rfl
  rw [h1, vpBasis_apply', betaVP_tmul, one_mul, one_mul, detT_apply, crossPairing_apply,
    one_mul, weil_apply, Matrix.mulVec_single_one]
  simp only [Basis.repr_self, conjMatrix, Matrix.col_apply, Matrix.map_apply,
    LinearMap.toMatrix_apply, map_sub, map_mul]
  fin_cases i <;> simp

/-- **The transported determinant form in coordinates** (tex 2798–2805, 3093, 5037): for
`v, w ∈ V_𝔭(α)`, `β_𝔭(v, J w) = e₂(x, J y)` with `x, y` the `vpBasis`-coordinates of `v, w` and
`J = conjMatrix`. Kind: PROVED. -/
theorem betaVP_conjVPv_eq (v w : VP K S W P α) :
    betaVP W P α v (conjVPv C W hW P α w) =
      crossPairing 1 (conjMatrix C W hW P) ((vpBasis P).repr v) ((vpBasis P).repr w) := by
  have key : (betaVP W P α).compl₂ (conjVPv C W hW P α) =
      (crossPairing 1 (conjMatrix C W hW P)).compl₁₂
        (Finsupp.lcoeFun ∘ₗ (vpBasis (α := α) P).repr.toLinearMap)
        (Finsupp.lcoeFun ∘ₗ (vpBasis (α := α) P).repr.toLinearMap) := by
    refine (vpBasis P).ext fun i => (vpBasis P).ext fun j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.compl₁₂_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, Basis.repr_self, Finsupp.lcoeFun_apply,
      Finsupp.single_eq_pi_single]
    exact betaVP_conjVPv_basis C W hW P α i j
  exact LinearMap.congr_fun₂ key v w

/-- **Bridge: lane RC31's transported fibre pairing is the transported cross pairing**
(tex 2798–2805, 3093, 5037). For `v ∈ V_𝔭(α)` and `w ∈ τ^*V_𝔭(α)`, the pairing
`β(v, J w) ∈ k(𝔭)(1)` (`betaConj`), read in `k(𝔭)`, equals `crossPairing 1 J x y = e₂(x, J y)`,
where `x, y` are the coordinates of `v, w` in lane RC28's basis `vpBasis` and `J = conjMatrix` is
the matrix of `ρ_T(τ)`. Kind: PROVED. -/
theorem betaConj_vpBasis (v : VP K S W P α) (w : PullMod C.conj (VP K S W P α)) :
    Tate1P.equiv K S P (betaConj W P α C hW v w) =
      crossPairing 1 (conjMatrix C W hW P) ((vpBasis P).repr v)
        ((vpBasis (α := α) P).repr (show VP K S W P α from w)) :=
  betaVP_conjVPv_eq C W hW P α v w

end ZInQ.Manuscript.RC.FibreDuality

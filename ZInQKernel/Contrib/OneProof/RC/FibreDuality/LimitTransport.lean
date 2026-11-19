import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitLocal
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitMatrices
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.ConjDual

/-!
# Lane RC31, round 2, part 4: the transported local pairing at a derivative label

Manuscript `diophantine_zq.tex`: "The transported cross pairing is exactly
`β(x, y) = ε e₂(x, J y)`, `ε ∈ k^×`" (tex 5037), with `J = ρ_T(τ)`, `J² = I` ((H12), tex 3093),
and the Weil pairing `M_i ⊗ τ^*M_i → R_i(1)`, `(v, w) ↦ e₂(v, ρ_T(τ) w)` (tex 2798–2805); "Here `D⁰`
and `D²` are dual, and `F_v, S_v` are the finite and singular isotropic planes" (tex 4860–4868).

* `transportedPairing ε₀ ε₂ ε σ J`: the local pairing of the split model built from the
  transported cross pairing `crossPairing ε J` (`(x, y) ↦ ε e₂(x, J y)`): `D⁰ × D²` and `D² × D⁰`
  by `crossPairing ε₀ J`, `crossPairing ε₂ J`, and `(F ⊕ S) × (F ⊕ S)` by the negative transposed
  switch pairing (the convention of the residue formula). Both perfectness inputs of the local
  duality are PROVED from `ε₂, ε, σ ≠ 0` and `J² = 1`.
* `conjMatrix C W hW P`: **the matrix of `J = ρ_T(τ)`** at the fibre `V_𝔭 = k(𝔭) ⊗ T₂E`, in lane
  RC28's basis (`tateBasis`, `vpBasis`), from lane RC31's `conjTate` (round one);
  `conjMatrix_mul_self`: `J² = 1`, PROVED. With it, `crossPairing 1 J` is lane RC31's transported
  fibre pairing `betaConj` in coordinates (`betaConj_vpBasis`, `LimitBridge.lean`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain TensorProduct Matrix
open ZInQ.Manuscript.RC.Uniform (Lambda switchPairing crossPairing crossPairing_apply weil
  planePairing_apply crossPairing_isPerfPair)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (ActualConj PullMod)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.InnerLimit (Vec2 Coords)

section Transported

variable {k : Type} [Field k]

/-- **The transported local pairing of the split model** (tex 4860–4868 and 5037): `D⁰ × D²` and
`D² × D⁰` by the transported cross pairings `ε₀ e₂(x, J y)`, `ε₂ e₂(x, J y)`, and `F ⊕ S` by
`b₁₁(x, y) = −switchPairing ε σ J y x`. Kind: definition. -/
def transportedPairing (ε₀ ε₂ ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) : SplitLocalPairing k where
  b02 := crossPairing ε₀ J
  b11 := -(switchPairing ε σ J).flip
  b20 := crossPairing ε₂ J

/-- The `F ⊕ S` component of the transported pairing. Kind: PROVED (definitional). -/
theorem transportedPairing_b11 (ε₀ ε₂ ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (x y : Coords k) :
    (transportedPairing ε₀ ε₂ ε σ J).b11 x y = -(switchPairing ε σ J y x) :=
  rfl

/-- `D² × D⁰ → k` is perfect. Kind: PROVED. -/
theorem transportedPairing_b20_bijective {ε₂ : k} (hε₂ : ε₂ ≠ 0) (ε₀ ε σ : k)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ : J * J = 1) :
    Function.Bijective (transportedPairing ε₀ ε₂ ε σ J).b20 :=
  (crossPairing_isPerfPair hε₂ hJ).bijective_left

end Transported

/-! ### The matrix of `J = ρ_T(τ)` at the fibre -/

section Conj

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (C.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W] (P : Ideal Lambda) [P.IsPrime]

/-- **The matrix of `J = ρ_T(τ)`** on `T₂E` in lane RC28's basis, read in `k(𝔭)` (tex 3093). Kind:
definition. -/
def conjMatrix : Matrix (Fin 2) (Fin 2) (ResAt P) :=
  (LinearMap.toMatrix (tateBasis (K := K) (S := S) (W := W)) tateBasis
    (conjTate C W hW)).map (algebraMap ℤ_[2] (ResAt P))

/-- **`J² = 1`** (`conjTate_conjTate`, tex 3093). Kind: PROVED. -/
theorem conjMatrix_mul_self : conjMatrix C W hW P * conjMatrix C W hW P = 1 := by
  have h : conjTate C W hW * conjTate C W hW = 1 :=
    LinearMap.ext fun x => conjTate_conjTate C W hW x
  unfold conjMatrix
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_mul, h, LinearMap.toMatrix_one, Matrix.map_one _
    (map_zero _) (map_one _)]

end Conj

end ZInQ.Manuscript.RC.FibreDuality

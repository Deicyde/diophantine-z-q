import ZInQKernel.Contrib.OneProof.RC.FibreDuality.DetPairing
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Tate1
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Comparison
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.ConjDual
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.FibreSwitch

/-!
# Lane RC31, part 10: the coefficient pairings `V_𝔭 × V_𝔭^*(1) → k(𝔭)(1)` and the fibre duality

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830): "The Weil
pairing gives the following `R_i`-linear perfect pairing: `M_i ⊗_{R_i} τ^*M_i → R_i(1)`,
`(v, w) ↦ e_2(v, ρ_T(τ) w)` … Thus `τ^*M_i ≃ M_i^*(1)`" (tex 2798–2805), at the
characteristic-zero fibres (tex 4976–5200); the transported cross pairing
"`β(x, y) = ε e_2(x, J y)`, `ε ∈ k^×`" (tex 5037).

* `betaT W P α : V_𝔭(α) × V_𝔭(α⁻¹) → k(𝔭)(1)` (values in the genuine twist `Tate1P`): the
  determinant form of an RC28 basis of `T_2E` (`betaVP`), which is the Weil pairing up to the unit
  `ε_n = e_{2^n}(b_0, b_1)` at every level `2^n` (`detT_mod_eq_weil`, `isUnit_weilS_basis`).
  PROVED: equivariant (`betaT_smul`, through `det ρ_T = χ_cyc`, `det_actLin`), perfect
  (`betaT_bijective`, `betaT_flip_bijective`), jointly continuous (`continuous_betaT`).
* `kummerDualEquiv`: the explicit dual identification `V_𝔭(α⁻¹) ≃ Hom_{k(𝔭)}(V_𝔭(α), k(𝔭)(1))`,
  equivariant for the contragredient action (`kummerDualEquiv_smul`).
* `betaConj C W hW P α : V_𝔭(α) × τ^*V_𝔭(α) → k(𝔭)(1)`, `(v, w) ↦ β(v, J w)` with `J = ρ_T(τ)`
  (tex 2798–2805, (H12) tex 3093): equivariant when `α ∘ c = α⁻¹` (tex 2786–2795), perfect and
  continuous.
* **`fibreSelmerDuality_VP`, `fibreSelmerDuality_conj`**: the fibre Selmer duality
  (`fibreSelmerDualityT`) instantiated with these genuine coefficient data — the only remaining
  inputs are the PRINT, the standing hypotheses, the trace, and the local orthogonality of the
  chosen conditions.

Kinds: definitions and PROVED. The rank `2` of `T_2E` uses lane RC28's GLUE `HasFullTwoTorsion`
(Néron–Ogg–Shafarevich).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain CategoryTheory Filter Topology TensorProduct
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules (PullMod ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] [HasFullTwoTorsion K S W]
  (P : Ideal Lambda) [P.IsPrime] (α : GKS K S →* Lambdaˣ)

/-! ### The Kummer-dual pairing with values in `k(𝔭)(1)` -/

/-- **The coefficient pairing `V_𝔭(α) × V_𝔭(α⁻¹) → k(𝔭)(1)`** (tex 2798–2805 at the fibres):
`betaVP` (the determinant form in an RC28 basis of `T_2E`, the Weil pairing up to a unit at each
finite level) read in the twist `Tate1P`. Kind: definition. -/
def betaT : VP K S W P α →ₗ[ResAt P] VP K S W P α⁻¹ →ₗ[ResAt P] Tate1P K S P :=
  (betaVP W P α).compr₂ (Tate1P.equiv K S P).symm.toLinearMap

/-- `betaT` is `betaVP` read in `k(𝔭)(1)`. Kind: PROVED (definitional). -/
theorem betaT_apply (a : VP K S W P α) (b : VP K S W P α⁻¹) :
    Tate1P.equiv K S P (betaT W P α a b) = betaVP W P α a b :=
  rfl

/-- **`betaT` is Galois-equivariant**: `β(σa, σb) = χ_cyc(σ) β(a, b)` (`det ρ_T = χ_cyc`, PROVED
level by level from the Weil pairing in `DetPairing.lean`). Kind: PROVED. -/
theorem betaT_smul (σ : GKS K S) (a : VP K S W P α) (b : VP K S W P α⁻¹) :
    betaT W P α (σ • a) (σ • b) = σ • betaT W P α a b := by
  apply (Tate1P.equiv K S P).injective
  rw [betaT_apply, betaVP_smul, Tate1P.smul_def]
  rfl

/-- Post-composition with the identification `k(𝔭)(1) ≃ k(𝔭)` is bijective on `Hom`. -/
theorem bijective_compr_equiv {X : Type} [AddCommGroup X] [Module (ResAt P) X] :
    Function.Bijective fun f : X →ₗ[ResAt P] ResAt P =>
      (Tate1P.equiv K S P).symm.toLinearMap ∘ₗ f :=
  ((LinearEquiv.congrRight (Tate1P.equiv K S P).symm :
    (X →ₗ[ResAt P] ResAt P) ≃ₗ[ResAt P] (X →ₗ[ResAt P] Tate1P K S P))).bijective

/-- **`betaT` is perfect on the left**: `V_𝔭(α) ≃ Hom(V_𝔭(α⁻¹), k(𝔭)(1))`. Kind: PROVED. -/
theorem betaT_bijective : Function.Bijective (betaT W P α) :=
  (bijective_compr_equiv P).comp (betaVP_bijective (W := W) P α)

/-- **`betaT` is perfect on the right**: `V_𝔭(α⁻¹) ≃ Hom(V_𝔭(α), k(𝔭)(1))`. Kind: PROVED. -/
theorem betaT_flip_bijective : Function.Bijective (betaT W P α).flip :=
  (bijective_compr_equiv P).comp (betaVP_flip_bijective (W := W) P α)

/-- **`betaT` is jointly continuous** for the lattice topologies of `V_𝔭(α)`, `V_𝔭(α⁻¹)` and
`k(𝔭)(1)`: it maps `latt × latt` into the lattice of `k(𝔭)(1)` (`betaVP_latt`), hence is
continuous (`continuous_of_lattice_bound`). Kind: PROVED. -/
theorem continuous_betaT [IsHeightOneOdd P] :
    Continuous fun x : VP K S W P α × VP K S W P α⁻¹ => betaT W P α x.1 x.2 :=
  continuous_of_lattice_bound (betaT W P α) (latt K S W P α) (latt K S W P α⁻¹) (tLatt K S P)
    (fib_hasBasis_nhds_zero P) (fib_hasBasis_nhds_zero P) tate1P_hasBasis_nhds_zero
    (exists_two_pow_smul_mem_latt P) (exists_two_pow_smul_mem_latt P) (fun a ha b hb => by
      obtain ⟨l, hl⟩ := betaVP_latt (W := W) P α ha hb
      exact (mem_tLatt_iff _).mpr ⟨l, hl⟩)

/-- **The explicit dual identification `V_𝔭(α⁻¹) ≃ V_𝔭(α)^*(1) = Hom_{k(𝔭)}(V_𝔭(α), k(𝔭)(1))`**
(tex 2805 "Thus `τ^*M_i ≃ M_i^*(1)`", at the fibres), the adjoint of `betaT`. Kind: definition. -/
def kummerDualEquiv : VP K S W P α⁻¹ ≃ₗ[ResAt P] (VP K S W P α →ₗ[ResAt P] Tate1P K S P) :=
  LinearEquiv.ofBijective (betaT W P α).flip (betaT_flip_bijective W P α)

/-- **The dual identification is equivariant** for the contragredient action
`(σ f)(x) = σ • f(σ⁻¹ • x)`. Kind: PROVED. -/
theorem kummerDualEquiv_smul (σ : GKS K S) (y : VP K S W P α⁻¹) (x : VP K S W P α) :
    kummerDualEquiv W P α (σ • y) x = σ • kummerDualEquiv W P α y (σ⁻¹ • x) := by
  change betaT W P α x (σ • y) = σ • betaT W P α (σ⁻¹ • x) y
  rw [← betaT_smul W P α σ (σ⁻¹ • x) y, smul_inv_smul]

/-! ### The conjugate-transported pairing (the text's form) -/

variable (C : ActualConj K S) (hW : W.map (C.κ : K →+* K) = W)

/-- **The transported coefficient pairing `V_𝔭(α) × τ^*V_𝔭(α) → k(𝔭)(1)`,
`(v, w) ↦ β(v, J w)`** with `J = ρ_T(τ)` (tex 2798–2805: `(v, w) ↦ e_2(v, ρ_T(τ) w)`; (H12),
tex 3093). Kind: definition. -/
def betaConj : VP K S W P α →ₗ[ResAt P] PullMod C.conj (VP K S W P α) →ₗ[ResAt P] Tate1P K S P :=
  (betaT W P α).compl₂ (conjVP C W hW P α)

/-- `betaConj v w = β(v, J w)`. Kind: PROVED (definitional). -/
theorem betaConj_apply (v : VP K S W P α) (w : PullMod C.conj (VP K S W P α)) :
    betaConj W P α C hW v w = betaT W P α v (conjVP C W hW P α w) :=
  rfl

/-- **The transported pairing is equivariant** when `α ∘ c = α⁻¹` (tex 2786–2795:
`α_i^τ = α_i^{-1}`): `β(σv, J(c(σ) w)) = β(σv, σ J w) = χ(σ) β(v, J w)`. Kind: PROVED. -/
theorem betaConj_smul (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (σ : GKS K S) (v : VP K S W P α)
    (w : PullMod C.conj (VP K S W P α)) :
    betaConj W P α C hW (σ • v) (σ • w) = σ • betaConj W P α C hW v w := by
  rw [betaConj_apply, betaConj_apply, conjVP_smul C W hW P α hα, betaT_smul]

/-- **The transported pairing is perfect on the left.** Kind: PROVED. -/
theorem betaConj_bijective : Function.Bijective (betaConj W P α C hW) := by
  have e : (betaConj W P α C hW : VP K S W P α → _) =
      (LinearEquiv.arrowCongr (conjVPEquiv C W hW P α).symm (LinearEquiv.refl (ResAt P)
        (Tate1P K S P))) ∘ (betaT W P α) := by
    funext v
    refine LinearMap.ext fun w => ?_
    simp only [Function.comp_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm,
      LinearEquiv.refl_apply]
    rfl
  rw [e]
  exact (LinearEquiv.bijective _).comp (betaT_bijective W P α)

/-- **The transported pairing is perfect on the right.** Kind: PROVED. -/
theorem betaConj_flip_bijective : Function.Bijective (betaConj W P α C hW).flip := by
  have e : ((betaConj W P α C hW).flip : PullMod C.conj (VP K S W P α) → _) =
      (betaT W P α).flip ∘ (conjVP C W hW P α) := by
    funext w
    rfl
  rw [e]
  exact (betaT_flip_bijective W P α).comp (conjVP_bijective C W hW P α)

/-- **The transported pairing is jointly continuous.** Kind: PROVED. -/
theorem continuous_betaConj [IsHeightOneOdd P] :
    Continuous fun x : VP K S W P α × PullMod C.conj (VP K S W P α) =>
      betaConj W P α C hW x.1 x.2 := by
  have h : (fun x : VP K S W P α × PullMod C.conj (VP K S W P α) =>
      betaConj W P α C hW x.1 x.2) =
      (fun x : VP K S W P α × VP K S W P α⁻¹ => betaT W P α x.1 x.2) ∘
        (fun x : VP K S W P α × PullMod C.conj (VP K S W P α) =>
          (x.1, conjVP C W hW P α x.2)) := by
    funext x
    exact betaConj_apply W P α C hW x.1 x.2
  rw [h]
  exact (continuous_betaT W P α).comp (continuous_fst.prodMk
    ((continuous_conjVP C W hW P α).comp continuous_snd))

/-! ### The fibre Selmer duality with the genuine coefficient data -/

section Duality

variable [IsHeightOneOdd P] [IsContChar α]

/-- **Fibre Selmer duality for `V_𝔭(α)` against its Kummer dual `V_𝔭(α⁻¹)`** (Nekovář 6.8.1;
manuscript tex 4878–4897, 5065–5070): `fibreSelmerDualityT` with the genuine coefficient data —
`V_𝔭(α)`, `V_𝔭(α⁻¹)` with RC28's topology (`isLatticeTop_vp'`), `T = k(𝔭)(1)` (`Tate1P`), and the
Weil/determinant pairing `betaT`. For any local conditions with truncated isotropy data, a trace
inducing `H³_c ≅ k(𝔭)` and the orthogonality of the local conditions, the genuine fibre Selmer
duality map is a quasi-isomorphism.
This is the duality of the Galois cochains of the fibre (DEPARTURE 5 of `Print.lean`); the
text's complexes are `C ⊗_R k` (tex 4977–4990), and `horth` for the text's derivative-prime
conditions `D⁰`, `D⁰ ⊕ (F ⊕ S)[−1]` (tex 4860–4875, 5059–5061) is not discharged here.
Kind: PROVED from the PRINT `NekovarFibreGlobalDuality`. -/
theorem fibreSelmerDuality_VP (h : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (ΔA : GaloisLocalConditions K S (ResAt P) (VP K S W P α))
    (ΔB : GaloisLocalConditions K S (ResAt P) (VP K S W P α⁻¹))
    (I : GalTruncIsotropyData S (ResAt P) (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α)
      ΔA ΔB)
    (tr : (galCompactTT S (ResAt P) (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α) ΔA
      ΔB I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) (betaT W P α) (betaT_smul W P α)
      (continuous_betaT W P α) ΔA ΔB I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr)
    (horth : FibreOrthogonalComplementsT (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α)
      ΔA ΔB I tr htr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galPairDataT S (ResAt P) (betaT W P α)
      (betaT_smul W P α) (continuous_betaT W P α) ΔA ΔB I) tr htr)) :=
  fibreSelmerDualityT (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α) h hset
    (isLatticeTop_vp' P) (isLatticeTop_vp' P) (isLatticeTop_tate1P K S P)
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion K S W; isTateTwistFibre_tate1P K S P)
    (betaT_bijective W P α) (betaT_flip_bijective W P α) ΔA ΔB I tr htr htr3 horth

/-- **Fibre Selmer duality, the text's transported form**: `V_𝔭(α)` against `τ^*V_𝔭(α)` with
`(v, w) ↦ β(v, J w)` (tex 2798–2805), for `α ∘ c = α⁻¹`.
This is the duality of the Galois cochains of the fibre (DEPARTURE 5 of `Print.lean`); the
text's complexes are `C ⊗_R k` (tex 4977–4990), and `horth` for the text's derivative-prime
conditions `D⁰`, `D⁰ ⊕ (F ⊕ S)[−1]` (tex 4860–4875, 5059–5061) is not discharged here.
Kind: PROVED from the PRINT. -/
theorem fibreSelmerDuality_conj (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹)
    (h : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (ΔA : GaloisLocalConditions K S (ResAt P) (VP K S W P α))
    (ΔB : GaloisLocalConditions K S (ResAt P) (PullMod C.conj (VP K S W P α)))
    (I : GalTruncIsotropyData S (ResAt P) (betaConj W P α C hW)
      (betaConj_smul W P α C hW hα) (continuous_betaConj W P α C hW) ΔA ΔB)
    (tr : (galCompactTT S (ResAt P) (betaConj W P α C hW) (betaConj_smul W P α C hW hα)
      (continuous_betaConj W P α C hW) ΔA ΔB I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) (betaConj W P α C hW)
      (betaConj_smul W P α C hW hα) (continuous_betaConj W P α C hW) ΔA ΔB I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr)
    (horth : FibreOrthogonalComplementsT (betaConj W P α C hW) (betaConj_smul W P α C hW hα)
      (continuous_betaConj W P α C hW) ΔA ΔB I tr htr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galPairDataT S (ResAt P) (betaConj W P α C hW)
      (betaConj_smul W P α C hW hα) (continuous_betaConj W P α C hW) ΔA ΔB I) tr htr)) :=
  fibreSelmerDualityT (betaConj W P α C hW) (betaConj_smul W P α C hW hα)
    (continuous_betaConj W P α C hW) h hset (isLatticeTop_vp' P)
    (isLatticeTop_pullVP C W P α (isLatticeTop_vp' P)) (isLatticeTop_tate1P K S P)
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion K S W; isTateTwistFibre_tate1P K S P)
    (betaConj_bijective W P α C hW) (betaConj_flip_bijective W P α C hW) ΔA ΔB I tr htr htr3
    horth

/-- **The pairing data of `betaT` between lane RC28's relaxed fibre data of `V_𝔭(α)` and its
strict fibre data of `V_𝔭(α⁻¹)`** (`fibreRelaxed`, `fibreStrict`; the zero homotopies). Kind:
definition. -/
abbrev fibrePairRelStr :
    SelPairData (fibreRelaxed (S := S) W P α) (fibreStrict (S := S) W P α⁻¹) :=
  galPairDataT S (ResAt P) (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α) _ _
    (relaxedStrictTruncIsotropy (S := S) (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α))

/-- **The pairing data of `betaT` between lane RC28's strict fibre data of `V_𝔭(α)` and its
relaxed fibre data of `V_𝔭(α⁻¹)`**. Kind: definition. -/
abbrev fibrePairStrRel :
    SelPairData (fibreStrict (S := S) W P α) (fibreRelaxed (S := S) W P α⁻¹) :=
  galPairDataT S (ResAt P) (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α) _ _
    (strictRelaxedTruncIsotropy (S := S) (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α))

/-- **Consumer form (relaxed/strict) on lane RC28's fibre Selmer data**: for `E` at `𝔭`,
`C_rel(V_𝔭(α)) ≃ Hom_{k(𝔭)}(C_str(V_𝔭(α⁻¹)), k(𝔭))[−3]` through the Weil/determinant pairing,
for any trace inducing `H³_c ≅ k(𝔭)`. Kind: PROVED from the PRINT `NekovarFibreGlobalDuality`. -/
theorem fibreSelmerDuality_relaxed_strict_VP (h : NekovarFibreGlobalDuality K)
    (hset : NekovarFibreSetting K S)
    (tr : (coneCx (fibrePairRelStr W P α).resE).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((coneCx (fibrePairRelStr W P α).resE).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (fibrePairRelStr W P α) tr htr)) :=
  fibreSelmerDuality_relaxed_strict (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α) h
    hset (isLatticeTop_vp' P) (isLatticeTop_vp' P) (isLatticeTop_tate1P K S P)
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion K S W; isTateTwistFibre_tate1P K S P)
    (betaT_bijective W P α) (betaT_flip_bijective W P α) _ tr htr htr3

/-- **Consumer form (strict/relaxed) on lane RC28's fibre Selmer data**:
`C_str(V_𝔭(α)) ≃ Hom_{k(𝔭)}(C_rel(V_𝔭(α⁻¹)), k(𝔭))[−3]`, for a global trace normalized by ONE
packet of local traces. Kind: PROVED from the PRINTs `NekovarFibreGlobalDuality` and
`NekovarFibreLocalDuality`. -/
theorem fibreSelmerDuality_strict_relaxed_VP (hG : NekovarFibreGlobalDuality K)
    (hL : NekovarFibreLocalDuality K) (hset : NekovarFibreSetting K S) [Fintype (Places K S)]
    (L : FibreLocalTraces S (ResAt P) (Tate1P K S P))
    (tr : (coneCx (fibrePairStrRel W P α).resE).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((coneCx (fibrePairStrRel W P α).resE).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) (hsum : L.Normalizes tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (fibrePairStrRel W P α) tr htr)) :=
  fibreSelmerDuality_strict_relaxed (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α) hG
    hL hset (isLatticeTop_vp' P) (isLatticeTop_vp' P) (isLatticeTop_tate1P K S P)
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion K S W; isTateTwistFibre_tate1P K S P)
    (betaT_bijective W P α) (betaT_flip_bijective W P α) L _ tr htr htr3 hsum

end Duality

end ZInQ.Manuscript.RC.FibreDuality

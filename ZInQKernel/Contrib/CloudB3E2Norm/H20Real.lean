import ZInQKernel.Contrib.CloudB3E2Norm.H20Untwisted

/-!
# The realization `hreal`: twisted local norms of points are points of the local twist

Manuscript `diophantine_zq.tex`, tex 3251–3262: "Localizing (H21) separates the cosets into
decomposition-group orbits: this is the local Mackey formula ... At `2N`, the deformation character
`Ψ` is trivial locally; the fixed quadratic character need not be trivial. Under the fixed
quadratic-twist identification, the local map is the ordinary integral norm on Kummer classes. One
can see this without a projector: the sum `∑_δ χ(δ) δ Q` is a point of the quadratic twist over the
lower field".

`H20Untwisted.oldPlaceInputU` reduces the old-place input of the Shapiro-level norm identity to the
realization `hreal`: the localization at `v ∈ P` of the weighted sum `∑_δ θ(r_δ) ρ(r_δ) y` is an
`ℤ[Δ]`-combination of images of points of the local twist `B = E^{(h)}` over `K_v`. This file
**proves** it for the points of the ambient module `y = 1 ⊗ P` with `P ∈ E(K_{S₀})` fixed by the
transfer subgroup `H` (the Heegner point over the fixed field of `H`):

For the ambient points over a larger support `S₁` (needed for the relaxed points, see
`H20Untwisted`), the same statements are `H20AmbientS.hreal_actualS` and
`H20AmbientS.oldPlaceInput_of_pointS`.

* `alphaShap_eq_one` (PROVED): `χ_h(g) [π g] = 1` in `ℤ[Δ]` forces `χ_h(g) = 1` and `π g = 1`.
* `realX d` (definition): `X_d = ∑_{δ : π(r_δ) = d} χ_h(r_δ) · j(r_δ P) ∈ E(K̄_v)`, the part of the
  localized weighted sum on the coset fibre over `d ∈ Δ`.
* `smul_realX` (PROVED; the local Mackey step): for `σ ∈ G_{K_v}`, `v ∈ P`, `σ X_d = χ_h(σ) X_d`
  (`σ` permutes the fibre since `π` is trivial on the decomposition group, `PsiTrivialAt2N`).
* `exists_twist_point` (PROVED): hence `X_d = j_B(Q_d)` for a point `Q_d ∈ B(K_v)` (the twist
  identification `twistPt` turns the `χ_h`-twisted invariance into invariance; Galois descent is the
  tree's `CoefModules.exists_basePt_of_fixed`).
* `psi_wsum` (PROVED): `ψ(∑_δ θ(r_δ) ρ(r_δ)(1 ⊗ P)) = ∑_d [d] ⊗ X_d`.
* **`hreal_actual`** (PROVED): the realization, with `J = Δ`, `a_d = [d]`, `P_d = Q_d`.
* **`oldPlaceInput_of_point`** (PROVED): the old-place input of `h1_shapiro` at `v ∈ Pl` (the old
  places where `Ψ` is trivial) for
  `y = 1 ⊗ P`, from `P` fixed by `H` alone.

Kinds: PROVED (from the ELLIOT input `PsiTrivialAt2N`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve

attribute [local instance] groupRingTop ptSAction

set_option linter.unusedSectionVars false

/-! ### The units `±[d]` of `ℤ[Δ]` -/

section Units

variable {Δ : Type} [CommGroup Δ]

/-- `ε [d] = 1` in `ℤ[Δ]` (`ε = ±1`) forces `ε = 1` and `d = 1`. Kind: PROVED. -/
theorem signed_of_eq_one {ε : ℤˣ} {d : Δ}
    (h : (((ε : ℤ) : MonoidAlgebra ℤ Δ) * MonoidAlgebra.of ℤ Δ d) = 1) : ε = 1 ∧ d = 1 := by
  have h1 : ((ε : ℤ) : MonoidAlgebra ℤ Δ) * MonoidAlgebra.of ℤ Δ d =
      MonoidAlgebra.single d (ε : ℤ) := by
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.intCast_def, MonoidAlgebra.single_mul_single]
  rw [h1, MonoidAlgebra.one_def, MonoidAlgebra.single_inj] at h
  rcases h with ⟨hd, he⟩ | ⟨he, -⟩
  · exact ⟨Units.ext he, hd⟩
  · exact absurd he (Units.ne_zero ε)

end Units

/-! ### The local Mackey step -/

section Real

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Fintype Δ] (π : GKS K S₀ →* Δ)
  (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)
  [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
  (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
  (P : PtS K S₀ W) (v : HeightOneSpectrum (𝓞 K))

/-- The coset representatives, in `G_{K,S₀}`. Kind: definition. -/
abbrev gR (δ : GKS K S ⧸ H) : GKS K S₀ := inflMap K hS (r δ)

/-- The summand `χ_h(r_δ) · j(r_δ P) ∈ E(K̄_v)`. Kind: definition. -/
def realF (δ : GKS K S ⧸ H) : PtV W v :=
  ((quadChar s hs hs0 (gR hS H r δ) : ℤˣ) : ℤ) • compPt (S := S₀) W v (gR hS H r δ • P)

/-- **`X_d = ∑_{δ : π(r_δ) = d} χ_h(r_δ) · j(r_δ P)`**. Kind: definition. -/
def realX (d : Δ) : PtV W v :=
  ∑ δ with π (gR hS H r δ) = d, realF hS W s hs hs0 H r P v δ

/-- `α = χ_h [π]` on `G_{K,S₀}` in coordinates. Kind: PROVED. -/
theorem alphaShap_val (g : GKS K S₀) :
    ((alphaShap s hs hs0 π g : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      (((quadChar s hs hs0 g : ℤˣ) : ℤ) : MonoidAlgebra ℤ Δ) * MonoidAlgebra.of ℤ Δ (π g) := by
  simp [alphaShap, charMul_apply, univChar, intUnitsTo]

include hH in
/-- On the transfer subgroup, `χ_h` and `π` are trivial. Kind: PROVED. -/
theorem chi_pi_of_mem {x : GKS K S} (hx : x ∈ H) :
    quadChar s hs hs0 (inflMap K hS x) = 1 ∧ π (inflMap K hS x) = 1 := by
  have h1 := hH hx
  rw [MonoidHom.mem_ker] at h1
  have h2 : ((alphaShap s hs hs0 π (inflMap K hS x) : (MonoidAlgebra ℤ Δ)ˣ) :
      MonoidAlgebra ℤ Δ) = 1 := by
    change ((alphaInfl hS s hs hs0 π x : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) = 1
    rw [h1, Units.val_one]
  rw [alphaShap_val] at h2
  exact signed_of_eq_one h2

include hr in
/-- `τ r_δ = r_{τδ} x` with `x ∈ H`. Kind: PROVED. -/
theorem coset_rel (τ : GKS K S) (δ : GKS K S ⧸ H) :
    ∃ x ∈ H, τ * r δ = r ((τ : GKS K S ⧸ H) * δ) * x := by
  refine ⟨(r ((τ : GKS K S ⧸ H) * δ))⁻¹ * (τ * r δ), ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [← QuotientGroup.eq, hr, QuotientGroup.mk_mul, hr]

include hH hr in
/-- **The local Mackey step on one summand** (PROVED): for `σ ∈ G_{K_v}` with `π` trivial on
`p_v(σ)`, `σ · (χ_h(r_δ) j(r_δ P)) = χ_h(σ) · χ_h(r_{σδ}) j(r_{σδ} P)` and `σ` preserves the fibre
of `δ ↦ π(r_δ)`, when `P` is fixed by `H`. -/
theorem smul_realF (hP : ∀ x ∈ H, inflMap K hS x • P = P) (σ : Gloc K v)
    (hv : π (locMap K S₀ v σ) = 1) (δ : GKS K S ⧸ H) :
    σ • realF hS W s hs hs0 H r P v δ =
        ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) •
          realF hS W s hs hs0 H r P v ((locMap K S v σ : GKS K S ⧸ H) * δ) ∧
      π (gR hS H r ((locMap K S v σ : GKS K S ⧸ H) * δ)) = π (gR hS H r δ) := by
  obtain ⟨x, hx, hxe⟩ := coset_rel H r hr (locMap K S v σ) δ
  obtain ⟨hχx, hπx⟩ := chi_pi_of_mem hS s hs hs0 π H hH hx
  have hinfl : locMap K S₀ v σ * gR hS H r δ =
      gR hS H r ((locMap K S v σ : GKS K S ⧸ H) * δ) * inflMap K hS x := by
    rw [← locMap_compat K hS v σ]
    simp only [gR, ← map_mul, hxe]
  set δ' := (locMap K S v σ : GKS K S ⧸ H) * δ
  have hpt : locMap K S₀ v σ • (gR hS H r δ • P) = gR hS H r δ' • P := by
    rw [← mul_smul, hinfl, mul_smul, hP x hx]
  have hchi : quadChar s hs hs0 (gR hS H r δ) =
      quadChar s hs hs0 (locMap K S₀ v σ) * quadChar s hs hs0 (gR hS H r δ') := by
    have := congrArg (quadChar s hs hs0) hinfl
    rw [map_mul, map_mul, hχx, mul_one] at this
    rw [← this, ← mul_assoc, Int.units_mul_self, one_mul]
  refine ⟨?_, ?_⟩
  · rw [realF, smul_comm, ← compPt_smul, ← ptS_smul_def, hpt, hchi, Units.val_mul, mul_smul]
    rfl
  · have := congrArg π hinfl
    rw [map_mul, map_mul, hv, one_mul, hπx, mul_one] at this
    exact this.symm

include hH hr in
/-- **`σ X_d = χ_h(σ) X_d`** for `σ ∈ G_{K_v}` with `π` trivial on `p_v(σ)` (PROVED; tex 3251–3262,
the local Mackey formula on points). -/
theorem smul_realX (hP : ∀ x ∈ H, inflMap K hS x • P = P) (σ : Gloc K v)
    (hv : π (locMap K S₀ v σ) = 1) (d : Δ) :
    σ • realX hS W s hs hs0 π H r P v d =
      ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) • realX hS W s hs hs0 π H r P v d := by
  have key := smul_realF hS W s hs hs0 π H hH r hr P v hP σ hv
  rw [realX, Finset.sum_filter, Finset.smul_sum, Finset.smul_sum]
  simp_rw [smul_ite, smul_zero]
  have hstep : ∀ δ : GKS K S ⧸ H,
      (if π (gR hS H r δ) = d then σ • realF hS W s hs hs0 H r P v δ else 0) =
        (fun δ' => if π (gR hS H r δ') = d then
          ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) • realF hS W s hs hs0 H r P v δ'
          else 0) ((Equiv.mulLeft ((locMap K S v σ : GKS K S) : GKS K S ⧸ H)) δ) := by
    intro δ
    simp only [Equiv.coe_mulLeft]
    rw [(key δ).1]
    simp only [(key δ).2]
  rw [Finset.sum_congr rfl fun δ _ => hstep δ]
  exact Equiv.sum_comp (Equiv.mulLeft ((locMap K S v σ : GKS K S) : GKS K S ⧸ H))
    (fun δ' => if π (gR hS H r δ') = d then
      ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) • realF hS W s hs hs0 H r P v δ' else 0)

include hH hr in
/-- **`X_d` is the image of a point of the local twist over `K_v`** (PROVED; tex 3251–3262: "the sum
`∑_δ χ(δ) δ Q` is a point of the quadratic twist over the lower field"): when `π` is trivial on the
decomposition group at `v`, `X_d = j_B(Q_d)` for some `Q_d ∈ B(K_v)`. -/
theorem exists_twist_point (hP : ∀ x ∈ H, inflMap K hS x • P = P)
    (hloc : ∀ σ : Gloc K v, π (locMap K S₀ v σ) = 1) (d : Δ) :
    ∃ Q : (localTwist W h v).toAffine.Point,
      twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
          two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
          (basePt (v.adicCompletion K) (localTwist W h v) Q) =
        realX hS W s hs hs0 π H r P v d := by
  set tw := twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
    two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
  have hfix : ∀ σ : Field.absoluteGaloisGroup (v.adicCompletion K),
      σ • tw.symm (realX hS W s hs hs0 π H r P v d) =
        tw.symm (realX hS W s hs hs0 π H r P v d) := by
    intro σ
    apply tw.injective
    rw [twistPt_smul, tw.apply_symm_apply,
      smul_realX hS W s hs hs0 π H hH r hr P v hP σ (hloc σ) d,
      twistSign_localSqrt (S := S₀) s hs hs0 v σ, smul_smul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, one_smul]
  obtain ⟨Q, hQ⟩ := ZInQ.Manuscript.RC.CoefModules.exists_basePt_of_fixed hfix
  exact ⟨Q, by rw [hQ, tw.apply_symm_apply]⟩

/-- `ρ₀(g)(1 ⊗ P) = 1 ⊗ g P` on the untwisted ambient module. Kind: PROVED. -/
theorem ambRhoU_oneTmul' (g : GKS K S) :
    ambRhoU hS W Δ g ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W) =
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ (inflMap K hS g • P) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W) := by
  have h1 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S₀ →* (MonoidAlgebra ℤ Δ)ˣ)
    (PtS K S₀ W) (inflMap K hS g) 1 P
  change (inflMap K hS g • CoefMod.equiv _ _ _ ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P) :
    ambU₀ S₀ W Δ) = CoefMod.equiv _ _ _ (_ ⊗ₜ _)
  rw [h1]
  congr 2
  simp

/-- `a ⊗ x` in the local module. Kind: definition. -/
abbrev tL (a : MonoidAlgebra ℤ Δ) (x : PtV W v) : locL W s hs hs0 v Δ :=
  (a ⊗ₜ x : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v)

/-- `a ⊗ ∑ f = ∑ a ⊗ f`. Kind: PROVED. -/
theorem tL_sum (a : MonoidAlgebra ℤ Δ) {ι : Type} (t : Finset ι) (f : ι → PtV W v) :
    tL W s hs hs0 v a (∑ i ∈ t, f i) = ∑ i ∈ t, tL W s hs hs0 v a (f i) :=
  TensorProduct.tmul_sum _ _ _

include hr in
/-- **The localized weighted sum, grouped by the fibres of `δ ↦ π(r_δ)`** (PROVED):
`ψ(∑_δ θ(r_δ) ρ₀(r_δ)(1 ⊗ P)) = ∑_d [d] ⊗ X_d`. -/
theorem psi_wsum :
    locPsiU hS W s hs hs0 v (wsum (ambRhoU hS W Δ) H r (thetaH hS s hs hs0 π H hH)
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W)) =
      ∑ d : Δ, tL W s hs hs0 v (MonoidAlgebra.of ℤ Δ d) (realX hS W s hs hs0 π H r P v d) := by
  have hterm : ∀ δ : GKS K S ⧸ H,
      locPsiU hS W s hs hs0 v (R H (ambRhoU hS W Δ) (thetaH hS s hs hs0 π H hH) (r δ)
        ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W)) =
      tL W s hs hs0 v (MonoidAlgebra.of ℤ Δ (π (gR hS H r δ))) (realF hS W s hs hs0 H r P v δ) := by
    intro δ
    change locPsiU hS W s hs hs0 v
      (((thetaH hS s hs hs0 π H hH ((r δ : GKS K S) : GKS K S ⧸ H) : (MonoidAlgebra ℤ Δ)ˣ) :
        MonoidAlgebra ℤ Δ) • ambRhoU hS W Δ (r δ)
          ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W)) = _
    rw [LinearMap.map_smul, ambRhoU_oneTmul', thetaH_mk, alphaShap_val]
    change ((((quadChar s hs hs0 (gR hS H r δ) : ℤˣ) : ℤ) : MonoidAlgebra ℤ Δ) *
        MonoidAlgebra.of ℤ Δ (π (gR hS H r δ))) •
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ compPt (S := S₀) W v (gR hS H r δ • P) :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, realF]
    change _ = (MonoidAlgebra.of ℤ Δ (π (gR hS H r δ)) ⊗ₜ
      (((quadChar s hs hs0 (gR hS H r δ) : ℤˣ) : ℤ) • compPt (S := S₀) W v (gR hS H r δ • P)) :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul]
  change locPsiU hS W s hs hs0 v (∑ δ : GKS K S ⧸ H, R H (ambRhoU hS W Δ)
    (thetaH hS s hs hs0 π H hH) (r δ)
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W)) = _
  rw [map_sum, Finset.sum_congr rfl fun δ _ => hterm δ]
  rw [← Finset.sum_fiberwise Finset.univ (fun δ => π (gR hS H r δ))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [realX, tL_sum]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  rw [(Finset.mem_filter.1 hδ).2]

end Real

/-! ### The realization and the old-place input -/

section Hreal

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Fintype Δ] (π : GKS K S₀ →* Δ)
  (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)
  [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
  (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
  (P : PtS K S₀ W)

include hH hr in
/-- **The realization `hreal`** (PROVED; tex 3251–3262): for `P ∈ E(K_{S₀})` fixed by the transfer
subgroup `H ≤ ker(χ_h [π] ∘ infl)` and a place `v` at which `π` is trivial on the decomposition
group, the localization of `∑_δ θ_H(r_δ) ρ₀(r_δ)(1 ⊗ P)` is `∑_d [d] · j_B(Q_d)` for points
`Q_d ∈ B(K_v)` of the local twist. -/
theorem hreal_actual (hP : ∀ x ∈ H, inflMap K hS x • P = P) (v : HeightOneSpectrum (𝓞 K))
    (hloc : ∀ σ : Gloc K v, π (locMap K S₀ v σ) = 1) :
    ∃ Q : Δ → (localTwist W h v).toAffine.Point,
      locPsiU hS W s hs hs0 v (wsum (ambRhoU hS W Δ) H r (thetaH hS s hs hs0 π H hH)
        ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W)) =
        ∑ d ∈ Finset.univ, MonoidAlgebra.of ℤ Δ d • locJB W s hs hs0 v (Δ := Δ)
          (basePt (v.adicCompletion K) (localTwist W h v) (Q d)) := by
  choose Q hQ using exists_twist_point hS W s hs hs0 π H hH r hr P v hP hloc
  refine ⟨Q, ?_⟩
  rw [psi_wsum hS W s hs hs0 π H hH r hr P v]
  refine Finset.sum_congr rfl fun d _ => ?_
  change _ = MonoidAlgebra.of ℤ Δ d • ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ
    twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
      two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
      (basePt (v.adicCompletion K) (localTwist W h v) (Q d)) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v)
  rw [hQ d, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include hH hr in
/-- **The old-place input of `h1_shapiro` for a point fixed by the transfer subgroup** (PROVED;
tex 3251–3270): at `v ∈ P`, for `y = 1 ⊗ P` with `P ∈ E(K_{S₀})` fixed by `H`, `OldPlaceInput` holds
for the untwisted ambient module, `θ = θ_H` and `ι = ambIotaU` — with no further input beyond the
ELLIOT `PsiTrivialAt2N`. -/
theorem oldPlaceInput_of_point {Pl : Set (HeightOneSpectrum (𝓞 K))} (ψ : Δ →* (Acoef i)ˣ)
    (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ Pl)
    (hP : ∀ x ∈ H, inflMap K hS x • P = P) (v : Places K S) (hv : v.1 ∈ Pl)
    [(localTwist W h v.1).IsElliptic] :
    OldPlaceInput (ambRhoU hS W Δ) H r (thetaH hS s hs hs0 π H hH) v.1 (localTwist W h v.1)
      (2 ^ i) (shapIota hS W i s hs hs0 hFull π v) (ambIotaU hS W i s hs hs0 π)
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W) := by
  obtain ⟨Q, hQ⟩ := hreal_actual hS W s hs hs0 π H hH r hr P hP v.1
    (fun σ => pi_trivial_of_psi i π ψ hψ hΨ hv σ)
  exact oldPlaceInputU hS W i s hs hs0 hFull π v H r (thetaH hS s hs hs0 π H hH)
    (fun σ => thetaH_local hS i s hs hs0 π H hH ψ hψ hΨ hv σ) _ Finset.univ
    (fun d => MonoidAlgebra.of ℤ Δ d) Q hQ

end Hreal

end ZInQ.Contrib.CloudB3E2.NormCochain

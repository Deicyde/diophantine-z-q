import ZInQKernel.Contrib.CloudB3E2Norm.H20AmbTors
import ZInQKernel.Contrib.CloudB3E2Norm.H20Frob
import ZInQKernel.Contrib.CloudB3E2Norm.H20Assembly
import ZInQKernel.Contrib.CloudB3E2Norm.H20FrobArtin
import ZInQKernel.Contrib.CloudB3E2Norm.RingClassMono

/-!
# The Kummer classes of the actual points as presentation classes, and their norm identity

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194, 4157–4170):
"Let `z_T` be the class of the actual point `y_T` … the actual norm identity is
`z_R = e_q i(z_P)` with its retained boundary", on the one presentation at a coefficient stage
(tex 4385–4451).

Lane RC32's chain (`CommonCoordinate16Norm.exists_bw_hnorm`, `exists_stepHyps_of_E2_RC30`) takes
classes `presClass (g_T) (u_T)` of the support complexes `C_T` (`suppCxS`) with `ι(u_T) = res(g_T)`
and the global identities `g_{T ∪ {p}} = e · g_T + d b`. This file **defines** these classes as the
Kummer classes of actual points and **proves** the identities from the point relation (4.1):

* `ActualPoint T` (structure): the actual point of the support `T` on the ambient module
  `ℤ[Δ] ⊗ E(K_{S₁})` (`H20AmbientS`): a transfer subgroup `H` (normal, of finite index, with
  `χ_h [π]` trivial on it), coset representatives, the point `y` fixed by `H`, a division point
  `Q` (`2^i Q = y`) fixed by an open normal subgroup of `H`, the old-place inputs at `v ∈ P`
  (`hin_of_point`: from `PsiTrivialAt2N` for `y = 1 ⊗ P`), and the inertia hypotheses at the
  places off `T` (`hunr`, and `hQin` from `H20AmbientS.inertiaFixes_of_support`).
* **`shapClass A`** (definition; `exists_shapClass`, PROVED): a genuine continuous Shapiro-level
  `1`-cochain carried by `ι` to the twisted transfer `𝒯_θ(κ(Q))` of the Kummer cocycle of `Q`
  (`GlobalCochain.exists_gval_eq_transfer`, `htors_ambientS`).
* **`gx A`** (definition): its push to the stage ring `k` (`gPushK`), the global component of the
  class of `y_T` in the presentation; **`ux A`** (definition; `exists_ux`, `ux_spec`, PROVED): a
  local component with `ι(u) = res(g)` (old lifts `stage_oldLiftK`, unramified lifts
  `hPw_actualS`, `stage_urLiftK`); **`gxClass A = (g, u, 0)`** (definition): the class in `C_T¹`,
  lane RC32's `presClass`.
* **`gx_step`** (PROVED): for the actual points of `T` and `T ∪ {p}` with `H_{T∪p} ≤ H_T`, a
  transversal of `H_T / (H_T ∩ H_{T∪p})` and the point relation
  `∑_τ ρ(t_τ) y_{T∪p} = a y_T − σ y_T − σ⁻¹ y_T`: `g_{T ∪ {p}} = φ(e_q) · g_T + d b`,
  `e_q = a − θ(σ) − θ(σ)⁻¹`.
* **`gx_step_frob`** (PROVED): for `σ = p_w(φ)`, `φ` an arithmetic Frobenius lift at a place
  `w ∉ S₀` (`H20Frob`), the factor is `pointFactor a z z⁻¹` with `z = α(Frob_w)` (for lane RC32's
  stage `StageRing i`, the value of `stageRingChar i α` at `Frob_w`, i.e. `CharValueAt`; for the
  leaf's value see `H20QuadFrob.charValueAt_leaf_genuine`).
* **`gxClass_step`** (PROVED): the norm identity of the classes,
  `[y_{T ∪ {p}}] = e · i([y_T]) + d b` in `C_{T ∪ {p}}¹` (the input `hnorm` of `CMStepHyps`).
* **`gx_step_anchored`** gives the step identity at the place over the anchor's prime `𝔮 ∣ q`
  for the realized Heegner points `1 ⊗ P_d`, `1 ⊗ P_{dq}` with transfer subgroups `G_{H_d}`,
  `G_{H_{dq}}`, using
  `a = a_q` and `σ = p_w(φ)` from `H20FrobArtin.exists_sigma_field_iv` (the Artin restriction is
  lane E1's Frobenius lift), and `H_{d} ⊆ H_{dq}` from `RingClassMono` (no hypothesis);
  `pointFactor_anticyclotomic`: the same factor at the conjugate place under lane RC32's
  `AnticyclotomicAt`.

The point relation and the description of the transfer subgroups are those of the anchored
Heegner datum: `H20DictFields.hnorm_of_full_anchor` (with point support `S₁`) gives the relation
for `y_T = 1 ⊗ P_{d_T}`, `H_T = G_{H_{d_T}}`, and `H20FrobArtin.exists_sigma_field_iv` gives one
`σ = p_w(φ)` serving both the relation and `gx_step_frob`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.PairedFunctional
open NumberField IsDedekindDomain TensorProduct

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop ptSAction

set_option linter.unusedSectionVars false

section Point

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) [IsOpenKer (alphaShap s hs hs0 π)]
  (P : Set (HeightOneSpectrum (𝓞 K))) {ι : Type} (place : ι × Bool → Places K S)

/-- **The actual point of a support `T`** on the ambient module `ℤ[Δ] ⊗ E(K_{S₁})` (tex 3203–3215,
3251–3290, 3471–3487, 4157–4170): the transfer subgroup, the point and its division point, and the
local inputs. Kind: definition (data with its hypotheses). -/
structure ActualPoint (Tp : Finset ι) : Type where
  /-- the transfer subgroup (for the text `G_{H_{d_T}}`) -/
  H : Subgroup (GKS K S)
  [normal : H.Normal]
  /-- `χ_h [π]` is trivial on it -/
  hH : H ≤ (alphaInfl hS s hs hs0 π).ker
  [fin : Fintype (GKS K S ⧸ H)]
  /-- coset representatives -/
  r : GKS K S ⧸ H → GKS K S
  hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ
  /-- the point (for the text `1 ⊗ y_T`) -/
  y : ambU h1 W Δ
  /-- a division point -/
  Q : ambU h1 W Δ
  hQ : ((2 ^ i : ℕ) : ℤ) • Q = y
  /-- `y` is fixed by the transfer subgroup -/
  hfix : ∀ x ∈ H, ambRhoU h1 W Δ x y = y
  /-- an open normal subgroup of `H` fixing `Q` -/
  V : Subgroup (GKS K S)
  [Vnormal : V.Normal]
  hVopen : IsOpen (V : Set (GKS K S))
  hVH : V ≤ H
  hVQ : ∀ x ∈ V, ambRhoU h1 W Δ x Q = Q
  /-- the old-place inputs at `v ∈ P` (`oldPlaceInput_of_pointS`) -/
  hin : ∀ v : Places K S₀, v.1 ∈ P →
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    OldPlaceInput (ambRhoU h1 W Δ) H r (thetaH hS s hs hs0 π H hH) v.1 (localTwist W h v.1)
      (2 ^ i) (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩)
      (ambIotaS hS h01 h1 W i s hs hs0 π) y
  /-- the transfer subgroup contains the inertia at the places off `T` -/
  hunr : ∀ j, j.1 ∉ Tp → inertiaImage (place j) ⊆ (H : Set (GKS K S))
  /-- the division point is fixed by the conjugates of that inertia -/
  hQin : ∀ j, j.1 ∉ Tp → InertiaFixesDivisionPoint (ambRhoU h1 W Δ) (inertiaImage (place j)) Q

attribute [instance] ActualPoint.normal ActualPoint.fin ActualPoint.Vnormal

variable {hS h01 h1 W i s hs hs0 hFull π P place}

/-- The weighted sum `∑_δ R(r_δ) Q`. Kind: definition. -/
abbrev ActualPoint.wsumQ {Tp : Finset ι}
    (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) : ambU h1 W Δ :=
  wsum (ambRhoU h1 W Δ) A.H A.r (thetaH hS s hs hs0 π A.H A.hH) A.Q

/-- **A genuine Shapiro-level class carried to the twisted transfer of the Kummer cocycle of `Q`**
(PROVED; continuity, `htors_ambientS`). -/
theorem ActualPoint.exists_shapClass {Tp : Finset ι}
    (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) :
    ∃ a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1,
      ∀ g : Fin 1 → GKS K S,
        ambIotaS hS h01 h1 W i s hs hs0 π
            (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
          T A.H A.r A.hr (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π A.H A.hH) 1
            (kummerCochain (ambRhoU h1 W Δ) A.H A.Q) g := by
  set θ := thetaH hS s hs hs0 π A.H A.hH
  set ρ := ambRhoU h1 W Δ
  have hk := kummer_weighted_sum A.H A.r A.hr ρ θ ((2 ^ i : ℕ) : ℤ) A.y A.Q A.hQ
  have hact : ∀ g g' : GKS K S, (fun x => R A.H ρ θ (g * g') x) =
      (fun x => R A.H ρ θ g x) ∘ (fun x => R A.H ρ θ g' x) := by
    intro g g'
    funext x
    rw [CloudB3RC53.HeegnerCohomology.TwistedTransfer.R_mul]
    rfl
  have hVP : ∀ v ∈ A.V, R A.H ρ θ v A.wsumQ = A.wsumQ := by
    intro v hv
    simp only [ActualPoint.wsumQ, wsum, map_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    have hv' : (A.r δ)⁻¹ * v * A.r δ ∈ A.V := by
      have := A.Vnormal.conj_mem v hv (A.r δ)⁻¹
      simpa using this
    have hmul : v * A.r δ = A.r δ * ((A.r δ)⁻¹ * v * A.r δ) := by group
    rw [← Module.End.mul_apply, ← CloudB3RC53.HeegnerCohomology.TwistedTransfer.R_mul, hmul,
      CloudB3RC53.HeegnerCohomology.TwistedTransfer.R_mul, Module.End.mul_apply, R_of_mem A.H ρ θ
        (A.hVH hv'), A.hVQ _ hv']
  have himg : ∀ g : GKS K S, ∃ m : shapMod hS W i s hs hs0 π,
      ambIotaS hS h01 h1 W i s hs hs0 π m = R A.H ρ θ g A.wsumQ - A.wsumQ := by
    intro g
    refine htors_ambientS hS h01 h1 W i s hs hs0 hFull π (Classical.arbitrary _) _ ?_
    have h2 : ((2 ^ i : ℕ) : ℤ) • A.wsumQ = wsum ρ A.H A.r θ A.y := hk.1
    have h3 : R A.H ρ θ g (wsum ρ A.H A.r θ A.y) = wsum ρ A.H A.r θ A.y :=
      R_wsum ρ A.H A.r A.hr θ g A.hfix
    rw [smul_sub]
    rw [← map_zsmul]
    rw [h2]
    rw [h3]
    exact sub_self _
  obtain ⟨a, ha⟩ := exists_gval_eq_transfer (ambIotaS hS h01 h1 W i s hs hs0 π)
    (ambIotaS_injective hS h01 h1 W i s hs hs0 π) (fun g x => R A.H ρ θ g x) hact A.wsumQ A.V
    A.hVopen hVP himg
  refine ⟨a, fun g => (ha g).trans ?_⟩
  exact (hk.2 g).symm

/-- **The Shapiro-level Kummer class of the actual point** (tex 3203–3215). Kind: definition. -/
def ActualPoint.shapClass {Tp : Finset ι}
    (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) :
    (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1 :=
  Classical.choose A.exists_shapClass

theorem ActualPoint.shapClass_spec {Tp : Finset ι}
    (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) (g : Fin 1 → GKS K S) :
    ambIotaS hS h01 h1 W i s hs hs0 π
        (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) A.shapClass g) =
      T A.H A.r A.hr (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π A.H A.hH) 1
        (kummerCochain (ambRhoU h1 W Δ) A.H A.Q) g :=
  Classical.choose_spec A.exists_shapClass g

/-- **The old-place inputs of an actual point `1 ⊗ P`** (PROVED; `oldPlaceInput_of_pointS`): for
`P ∈ E(K_{S₁})` fixed by the transfer subgroup, the field `hin` of `ActualPoint` holds, with no
input beyond the ELLIOT `PsiTrivialAt2N` at the places of `P`. -/
theorem hin_of_point (ψ : Δ →* (Acoef i)ˣ) (hψ : Function.Injective ψ)
    (hΨ : PsiTrivialAt2N i π ψ P) (H : Subgroup (GKS K S)) [H.Normal]
    (hH : H ≤ (alphaInfl hS s hs hs0 π).ker) [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
    (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ) (P₀ : PtS K S₁ W)
    (hP : ∀ x ∈ H, inflMap K h1 x • P₀ = P₀) :
    ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput (ambRhoU h1 W Δ) H r (thetaH hS s hs hs0 π H hH) v.1 (localTwist W h v.1)
        (2 ^ i) (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩)
        (ambIotaS hS h01 h1 W i s hs hs0 π)
        ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P₀ : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) := by
  intro v hv
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  let := Fintype.ofFinite Δ
  exact oldPlaceInput_of_pointS hS h01 h1 W i s hs hs0 hFull π H hH r hr P₀ ψ hψ hΨ hP
    ⟨v.1, hS v.2⟩ hv

end Point

/-! ### The classes at a stage -/

section Stage

attribute [local instance] mcoefModuleK

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
  [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))).V]
  (EU : ∀ j, SplitInclusion
    (genuineUq K S k (place j)
      (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))))
    (genuineLq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)))
  (hE : ∀ j, (EU j).i = genuineιq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId_compat hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (place j) (hw j)))

/-- **The global component of the class of the actual point** (tex 4157–4170): the push of its
Shapiro-level Kummer class to the stage ring `k`. Kind: definition. -/
def gx {Tp : Finset ι} (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) :
    (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 1 :=
  gPushK hS W i s hs hs0 π ψ k 1 A.shapClass

open scoped Classical in
include hψ hE in
/-- **A local component of the class of the actual point** (PROVED): old lifts at `S₀`
(`exists_oldLift_shap`, `stage_oldLiftK`) and unramified lifts at the places off `Tp`
(`hPw_actualS`, `stage_urLiftK`). -/
theorem exists_ux {Tp : Finset ι} (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) :
    ∃ u, (piMap (presCondS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
        EU Tp).i).f 1 1 rfl u =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place)
        (MinS hS W i (alphaStage i s hs hs0 π ψ))).f 1 1 rfl
        (gx hS h01 h1 W i s hs hs0 hFull π ψ P k place A) := by
  have hιeq : ∀ (g : GKS K S) (m : shapMod hS W i s hs hs0 π),
      ambIotaS hS h01 h1 W i s hs hs0 π (g • m) =
        R A.H (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π A.H A.hH) g
          (ambIotaS hS h01 h1 W i s hs hs0 π m) :=
    ambIotaS_equivariantH hS h01 h1 W i s hs hs0 π A.H A.hH
  obtain ⟨uO, huO⟩ := exists_oldLift_shap hS W i s hs hs0 hFull π ψ P hψ hΨ (ambRhoU h1 W Δ) A.H
    A.r A.hr (thetaH hS s hs hs0 π A.H A.hH) (ambIotaS hS h01 h1 W i s hs hs0 π) hιeq A.hQ A.hin
    A.shapClass A.shapClass_spec
  refine exists_presLift₁ K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
    (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
    (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    EU Tp _
    (fun v₀ => stage_oldLiftK hS W i s hs hs0 hFull π ψ P hψ hΨ k v₀ A.shapClass
      ⟨uO v₀, congrFun huO v₀⟩)
    (fun j hj => by
      rw [hE j]
      exact stage_urLiftK hS W i s hs hs0 π ψ k (place j) (hw j) A.shapClass
        (hPw_actualS hS h01 h1 W i s hs hs0 π A.H A.hH (place j) (hw j) A.r A.hr
          ((2 ^ i : ℕ) : ℤ) A.hQ A.shapClass A.shapClass_spec (A.hunr j hj) (A.hQin j hj)))

/-- **The local component of the class of the actual point**. Kind: definition. -/
def ux {Tp : Finset ι} (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) :
    (piCx (presCondS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
        EU Tp).U).X 1 :=
  Classical.choose (exists_ux hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE A)

theorem ux_spec {Tp : Finset ι} (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) :
    (piMap (presCondS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
        EU Tp).i).f 1 1 rfl (ux hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE A) =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place)
        (MinS hS W i (alphaStage i s hs hs0 π ψ))).f 1 1 rfl
        (gx hS h01 h1 W i s hs hs0 hFull π ψ P k place A) :=
  Classical.choose_spec (exists_ux hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE A)

/-- **The class of the actual point in the presentation** `(g, u, 0) ∈ C_{Tp}¹` (lane RC32's
`presClass`; tex 4157–4170). Kind: definition. -/
def gxClass {Tp : Finset ι} (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) :
    (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU Tp).X 1 :=
  ((gx hS h01 h1 W i s hs hs0 hFull π ψ P k place A,
    ux hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE A, 0) :
    selT (suppDataS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU Tp) 1)

end Stage

/-! ### The norm identity of the classes at a switch -/

section Step

attribute [local instance] mcoefModuleK

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
  [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))).V]
  (EU : ∀ j, SplitInclusion
    (genuineUq K S k (place j)
      (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))))
    (genuineLq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)))
  (hE : ∀ j, (EU j).i = genuineιq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId_compat hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (place j) (hw j)))
  {Tp : Finset ι} {p : ι}
  (AT : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp)
  (AR : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place (insert p Tp))
  (hle : AR.H ≤ AT.H) (U : Subgroup AT.H) (hU : ∀ x : AT.H, x ∈ U ↔ (x : GKS K S) ∈ AR.H)
  [Fintype (AT.H ⧸ U)] (t : AT.H ⧸ U → AT.H)
  (ht : ∀ τ : AT.H ⧸ U, (QuotientGroup.mk (t τ) : AT.H ⧸ U) = τ)

include hle hU ht in
/-- **The global identity of the classes of the actual points at a switch** (PROVED; tex
4157–4170): from the point relation (4.1) `∑_τ ρ(t_τ) y_{T∪p} = a y_T − σ y_T − σ⁻¹ y_T`,
`g_{T ∪ {p}} = φ(e_q) · g_T + d b` with `e_q = a − θ(σ) − θ(σ)⁻¹`, `θ = χ_h [π]`. -/
theorem gx_step (a : ℤ) (σ : GKS K S)
    (hnorm : ∑ τ : AT.H ⧸ U, ambRhoU h1 W Δ (t τ : GKS K S) AR.y =
      a • AT.y - ambRhoU h1 W Δ σ AT.y - ambRhoU h1 W Δ σ⁻¹ AT.y) :
    ∃ bG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0,
      gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR =
        phiK i ψ k (eq_ AT.H (thetaH hS s hs hs0 π AT.H AT.hH) a σ) •
          gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AT +
        (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG := by
  obtain ⟨bG, hG⟩ := hG_of_transfer (ambRhoU h1 W Δ) AT.H AR.H AT.r AT.hr AR.r AR.hr
    (thetaH hS s hs hs0 π AT.H AT.hH) (thetaH hS s hs hs0 π AR.H AR.hH) U hU t ht hle
    (fun _ => rfl) ((2 ^ i : ℕ) : ℤ) a σ AR.hQ AT.hQ AR.hfix AT.hfix hnorm
    (ambIotaS hS h01 h1 W i s hs hs0 π) (ambIotaS_injective hS h01 h1 W i s hs hs0 π)
    (ambIotaS_equivariantH hS h01 h1 W i s hs hs0 π AR.H AR.hH)
    (fun x hx => htors_ambientS hS h01 h1 W i s hs hs0 hFull π (Classical.arbitrary _) x hx)
    AR.shapClass AT.shapClass AR.shapClass_spec AT.shapClass_spec
  exact ⟨_, stage_globalK hS W i s hs hs0 π ψ k _ _ _ bG hG⟩

include hle hU ht in
/-- **The global identity at a Frobenius `σ`** (PROVED; tex 3915, 4144–4145, 4158–4172): for
`σ = p_w(φ)` with `φ` an arithmetic Frobenius lift at a place `w ∉ S₀` (`H20Frob`), the factor is
`pointFactor a z z⁻¹` with `z = α(Frob_w)` read in `k` (for lane RC32's `StageRing i`: the value of
`stageRingChar i α` at `Frob_w`, `H20Frob.eq_frobLift_stage`, `CharValueAt`). -/
theorem gx_step_frob (a : ℤ) (w : NewPlaces K S₀ S) (φ : Gloc K w.1)
    (hφ : TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ)
    (hnorm : ∑ τ : AT.H ⧸ U, ambRhoU h1 W Δ (t τ : GKS K S) AR.y =
      a • AT.y - ambRhoU h1 W Δ (locMap K S w.1 φ) AT.y -
        ambRhoU h1 W Δ (locMap K S w.1 φ)⁻¹ AT.y) :
    ∃ bG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0,
      gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR =
        pointFactor (a : k)
            ((eK k i).symm (alphaStage i s hs hs0 π ψ (urFrobElt K w) : Acoef i))
            ((eK k i).symm (((alphaStage i s hs hs0 π ψ (urFrobElt K w))⁻¹ : (Acoef i)ˣ) :
              Acoef i)) •
          gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AT +
        (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG := by
  obtain ⟨bG, hG⟩ := gx_step hS h01 h1 W i s hs hs0 hFull π ψ P k place AT AR hle U hU t ht a
    (locMap K S w.1 φ) hnorm
  refine ⟨bG, ?_⟩
  rw [hG, eq_frobLift hS i s hs hs0 π ψ k AT.H AT.hH a w φ hφ]

include hψ hE hle hU ht in
/-- **The norm identity of the classes of the actual points at a switch** (PROVED; tex
4157–4170, 4385–4451): `[y_{T ∪ {p}}] = e · i([y_T]) + d b` in `C_{T ∪ {p}}¹`, `e = φ(e_q)` (the
input `hnorm` of lane RC32's `CMStepHyps`, for the classes `gxClass`). -/
theorem gxClass_step (a : ℤ) (σ : GKS K S)
    (hnorm : ∑ τ : AT.H ⧸ U, ambRhoU h1 W Δ (t τ : GKS K S) AR.y =
      a • AT.y - ambRhoU h1 W Δ σ AT.y - ambRhoU h1 W Δ σ⁻¹ AT.y) :
    ∃ b : (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
        EU (insert p Tp)).X 0,
      gxClass hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AR =
        phiK i ψ k (eq_ AT.H (thetaH hS s hs hs0 π AT.H AT.hH) a σ) •
          (suppSwitchS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
            (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
            (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
              (newPlace (place j) (hw j))) EU Tp p).i.f 1 1 rfl
            (gxClass hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AT) +
        (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
          (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
            (newPlace (place j) (hw j))) EU (insert p Tp)).d 0 1 rfl b := by
  obtain ⟨bG, hG⟩ := gx_step hS h01 h1 W i s hs hs0 hFull π ψ P k place AT AR hle U hU t ht a σ
    hnorm
  have hsEU : ∀ j, Function.Surjective ((EU j).i.f 0 0 rfl) := fun j => by
    rw [hE j]
    exact genuineιq_surjective₀ (place j) _ _ _ Function.surjective_id
  obtain ⟨bU, hbU⟩ := exists_presLift₀ K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
    (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
    (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    EU (insert p Tp) (stageCondK_surjective₀ hS W i s hs hs0 hFull π ψ P hΨ k) hsEU
    ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place)
      (MinS hS W i (alphaStage i s hs hs0 π ψ))).f 0 0 rfl bG)
  exact ⟨((bG, bU, 0) : selT (suppDataS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU (insert p Tp)) 0),
    hnorm_changeIncl (presCondInclS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU Tp p) _ _ _ _ _ bG bU
      (presι_injective K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
          (newPlace (place j) (hw j))) EU (insert p Tp)
        (stageCondK_injective hS W i s hs hs0 hFull π ψ P hΨ k))
      (ux_spec hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AR)
      (ux_spec hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AT) hG hbU⟩

end Step

/-! ### The anchored Heegner points -/

section Anchored

attribute [local instance] mcoefModuleK

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST WeierstrassCurve
open scoped WeierstrassCurve

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) [(E.baseChange K).IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ (E.baseChange K) (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
  [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)

/-- **The step identity for the anchored Heegner points** (PROVED from the anchored
norm relations, tex 2914–2936, 3915, 4157–4172). For an anchored datum `D` and an admissible
`(d, q)` with `q` split, take actual points `A_T`, `A_{T∪p}` of consecutive supports with
transfer subgroups `G_{H_d}`, `G_{H_{dq}}` (fixing `κ(D.H d)`, `κ(D.H (dq))` in `K_{S₁}`)
and realized points `1 ⊗ P_d`, `1 ⊗ P_{dq}`. The inclusion `G_{H_{dq}} ⊆ G_{H_d}` holds (`RingClassMono.heegnerField_le_mul`) and there
is a prime `𝔮 ∣ q` such that at every new place `w` with `w = 𝔮`,
`g_{T ∪ {p}} = pointFactor a_q z z⁻¹ · g_T + d b` with `z = α(Frob_w)`: the classes of the
actual points satisfy lane RC32's step identity at `w` (`σ = p_w(φ)` a Frobenius lift,
`H20FrobArtin.exists_sigma_field_iv`). At the conjugate place the factor is the same under
lane RC32's `AnticyclotomicAt` (`pointFactor_anticyclotomic`). -/
theorem gx_step_anchored {cp : CSTParam E} {emb : Qbar →ₐ[ℚ] ℂ}
    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K}
    (hnorm : ∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D) :
    ∃ D : HeegnerPointData E, FullAnchor E K cp emb κ D ∧ D.NormRelations ∧
      ∀ {d q : ℕ} [NeZero d] (_ : D.Admissible d q) (_ : jacobiSym D.DK q = 1)
        (_ : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S₁)
        (hκP : ∀ x ∈ D.H d, κ x ∈ unramifiedOutside K S₁)
        (hκR : ∀ x ∈ D.H (d * q), κ x ∈ unramifiedOutside K S₁)
        {Tp : Finset ι} {p : ι}
        (AT : ActualPoint hS h01 h1 (E.baseChange K) i s hs hs0 hFull π P place Tp)
        (AR : ActualPoint hS h01 h1 (E.baseChange K) i s hs hs0 hFull π P place (insert p Tp))
        (_ : ∀ g : GKS K S, g ∈ AT.H ↔ ∀ x (hx : x ∈ D.H d),
          ((galS K S₁ (inflMap K h1 g) ⟨κ x, hκP x hx⟩ : unramifiedOutside K S₁) :
            AlgebraicClosure K) = κ x)
        (_ : ∀ g : GKS K S, g ∈ AR.H ↔ ∀ x (hx : x ∈ D.H (d * q)),
          ((galS K S₁ (inflMap K h1 g) ⟨κ x, hκR x hx⟩ : unramifiedOutside K S₁) :
            AlgebraicClosure K) = κ x)
        (U : Subgroup AT.H) (_ : ∀ x : AT.H, x ∈ U ↔ (x : GKS K S) ∈ AR.H) [Fintype (AT.H ⧸ U)]
        (t : AT.H ⧸ U → AT.H) (_ : ∀ τ : AT.H ⧸ U, (QuotientGroup.mk (t τ) : AT.H ⧸ U) = τ)
        (hyP : ∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
          Affine.Point.map (W' := E) (D.H d).val Y' = D.y d)
        (hyR : ∃ Y' : (E.baseChange (D.H (d * q))).toAffine.Point,
          Affine.Point.map (W' := E) (D.H (d * q)).val Y' = D.y (d * q))
        (_ : AT.y = yPt E h1 (Δ := Δ) (realize E S₁ κ.toAlgHom (D.H d) hκP (D.y d) hyP))
        (_ : AR.y = yPt E h1 (Δ := Δ)
          (realize E S₁ κ.toAlgHom (D.H (d * q)) hκR (D.y (d * q)) hyR)),
        ∃ 𝔮 : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∈ 𝔮.asIdeal ∧
          ∀ (w : NewPlaces K S₀ S) (_ : w.1 = 𝔮) (_ : (d : 𝓞 K) ∉ w.1.asIdeal)
            (_ : w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
              (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K d).conductorModulus)
            (_ : w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
              (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := K) d
                (NeZero.ne d)).conductorModulus),
            ∃ bG : (globalCx k (GKS K S) (MinS hS (E.baseChange K) i
                (alphaStage i s hs hs0 π ψ))).X 0,
              gx hS h01 h1 (E.baseChange K) i s hs hs0 hFull π ψ P k place AR =
                pointFactor ((E.LFunction q : ℤ) : k)
                    ((eK k i).symm (alphaStage i s hs hs0 π ψ (urFrobElt K w) : Acoef i))
                    ((eK k i).symm (((alphaStage i s hs hs0 π ψ (urFrobElt K w))⁻¹ :
                      (Acoef i)ˣ) : Acoef i)) •
                  gx hS h01 h1 (E.baseChange K) i s hs hs0 hFull π ψ P k place AT +
                (globalCx k (GKS K S) (MinS hS (E.baseChange K) i
                  (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG := by
  obtain ⟨D, hA, hD, hrel⟩ := hnorm_of_full_anchor E h1 (Δ := Δ) hnorm
  refine ⟨D, hA, hD, fun {d q} _ hadm hsplit hSd hκP hκR Tp p AT AR hHP hHR U hU _ t ht hyP
    hyR hyT hyR' => ?_⟩
  have hle : AR.H ≤ AT.H := fun g hg => (hHP g).2 fun x hx =>
    (hHR g).1 hg x (heegnerField_le_mul hA hadm x hx)
  obtain ⟨𝔮, hq, h𝔮, hall⟩ := hrel hadm hsplit hSd hκP hκR AT.H AR.H hHP hHR U hU t ht
  refine ⟨𝔮, hq, fun w hw𝔮 hwd hpr hJ => ?_⟩
  obtain ⟨φ, hφ, -, hσ⟩ := exists_sigma_field_iv hS h1 d hSd w hwd hpr hJ
  have hσ' : ∀ z : TauCeti.ClassFieldTheory.ringClassField
      (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K d),
      ((galS K S₁ (inflMap K h1 (locMap K S w.1 φ)) ⟨sepIncl K z, sepIncl_mem d hSd z⟩ :
          unramifiedOutside K S₁) : AlgebraicClosure K) =
        sepIncl K (TauCeti.ClassFieldTheory.ringClassArtinEquiv
          (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K d)
          ((ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K d).picClass ⟨𝔮.asIdeal, h𝔮⟩) z) := by
    subst hw𝔮
    exact hσ
  obtain ⟨hyR₀, hyP₀, hsum⟩ := hall (locMap K S w.1 φ) hσ'
  have e1 : hyR₀ = hyR := Subsingleton.elim _ _
  have e2 : hyP₀ = hyP := Subsingleton.elim _ _
  subst e1 e2
  rw [← hyT, ← hyR'] at hsum
  exact gx_step_frob hS h01 h1 (E.baseChange K) i s hs hs0 hFull π ψ P k place AT AR hle U hU t
    ht (E.LFunction q) w φ hφ hsum

/-- **The point factor is the same at the conjugate place** under lane RC32's
`AnticyclotomicAt` (PROVED): `a − z − z⁻¹` is symmetric under `z ↦ z⁻¹`. -/
theorem pointFactor_anticyclotomic {R : Type} [CommRing R] (a : R) (u v : Rˣ) (huv : v = u⁻¹) :
    pointFactor a (v : R) ((v⁻¹ : Rˣ) : R) = pointFactor a (u : R) ((u⁻¹ : Rˣ) : R) := by
  subst huv
  simp only [pointFactor, inv_inv]
  ring

end Anchored

end ZInQ.Contrib.CloudB3E2.NormCochain

import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointKummerClass
import ZInQKernel.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel

/-!
# The classes of the actual points at the center

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-central-specialization` (tex 3895–3975), (4.5)
(tex 3911–3915).

**(C4) at cochain level.** At the center (`Ψ = 1`, i.e. `t = 0`), the push `ℤ[Δ] → A_s` composed
with the specialization is the augmentation `ε : ℤ[Δ] → ℤ`. On the ambient module
`ℤ[Δ] ⊗ E(K_{S₁})` write `aug = ε ⊗ id : ℤ[Δ] ⊗ E(K_{S₁}) → E(K_{S₁})`:

* `augAmb_rho`, `augAmb_smul`, `augAmb_R` (PROVED): `aug ∘ ρ(g) = g ∘ aug`, `aug(u x) = ε(u) aug x`,
  and `aug ∘ R(g) = χ_h(g) · g ∘ aug` for the transfer action `R(g) = θ(g) ρ(g)`, `θ = χ_h [π]`.
* **`aug_shapClass`** (PROVED): the augmented Shapiro class of an actual point is the
  `χ_h`-twisted Kummer cocycle `g ↦ χ_h(g) g(Q̄) − Q̄` of `Q̄ = aug(∑_δ R(r_δ) Q)`;
  **`aug_wsumQ`** (PROVED): `2^i Q̄ = ∑_δ χ_h(r_δ) r_δ(aug y)` — `Q̄` is a `2^i`-division point of
  the `χ_h`-weighted trace of the point (for `y = 1 ⊗ P_f`, the trace whose descent is lane E1's
  `P^{rc}`).

**The factor and (4.5) at a stage.**

* `sp_pointFactor_center` (PROVED): under the specialization `t ↦ 0` (`Ψ = 1`) the point factor
  of the step identity at the moving prime is `m = a_r − 2χ_h(r)`.
* **`CentralStageComparison`** (definition; GLUE, the named input): the comparison of the
  presentation at a stage with the compact central complex — (C1) the coefficients at the center
  and the twist identification, (C2) the support/reduction comparison, with faithfulness of the
  read-out; the local conditions (C3), needed for the lift to the Selmer cones, stay named.
* **`central45_global`** (PROVED from the named comparison, `gx_step_heegner_at` and (C4)): the
  specialization of the class of `A_R` is `m · red(κ(P)) + dZ(…)` — the retained boundary
  `z̄ = i(m · P)` of (4.5), global component, at a stage. The multiplier `L` of (H11) is not
  carried by these classes.

Kinds: definitions, GLUE and PROVED.
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

/-! ### The augmentation on the ambient module -/

section Aug

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- **The augmentation `ε : ℤ[Δ] → ℤ`**. Kind: definition. -/
def augε (Δ : Type) [CommGroup Δ] : MonoidAlgebra ℤ Δ →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ Δ (1 : Δ →* ℤ)).toRingHom

theorem augε_of (d : Δ) : augε Δ (MonoidAlgebra.of ℤ Δ d) = 1 := by
  change MonoidAlgebra.lift ℤ ℤ Δ (1 : Δ →* ℤ) (MonoidAlgebra.of ℤ Δ d) = 1
  rw [MonoidAlgebra.lift_of]
  rfl

/-- **`aug = ε ⊗ id : ℤ[Δ] ⊗ E(K_{S₁}) → E(K_{S₁})`**. Kind: definition. -/
def augAmb : ambU h1 W Δ →+ PtS K S₁ W :=
  ((TensorProduct.lid ℤ (PtS K S₁ W)).toLinearMap ∘ₗ
    TensorProduct.map (augε Δ).toIntAlgHom.toLinearMap LinearMap.id).toAddMonoidHom

theorem augAmb_tmul (u : MonoidAlgebra ℤ Δ) (P : PtS K S₁ W) :
    augAmb h1 W (Δ := Δ) ((u ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) : ambU h1 W Δ) =
      augε Δ u • P := by
  change TensorProduct.lid ℤ (PtS K S₁ W) (TensorProduct.map (augε Δ).toIntAlgHom.toLinearMap
    LinearMap.id (u ⊗ₜ P)) = _
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
  rfl

theorem augAmb_oneTmul (P : PtS K S₁ W) :
    augAmb h1 W (Δ := Δ) (((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) :
      ambU h1 W Δ) = P := by
  rw [augAmb_tmul, map_one, one_smul]

/-- `ρ(g)(u ⊗ P) = u ⊗ g P`. Kind: PROVED. -/
theorem ambRhoU_tmul (g : GKS K S) (u : MonoidAlgebra ℤ Δ) (P : PtS K S₁ W) :
    ambRhoU h1 W Δ g ((u ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) : ambU h1 W Δ) =
      ((u ⊗ₜ (inflMap K h1 g • P) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) : ambU h1 W Δ) := by
  have e := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S₁ →* (MonoidAlgebra ℤ Δ)ˣ)
    (PtS K S₁ W) (inflMap K h1 g) u P
  change (inflMap K h1 g • CoefMod.equiv _ _ _ (u ⊗ₜ P) : ambU₀ S₁ W Δ) =
    CoefMod.equiv _ _ _ (_ ⊗ₜ _)
  rw [e]
  congr 2
  simp

/-- `aug ∘ ρ(g) = g ∘ aug`. Kind: PROVED. -/
theorem augAmb_rho (g : GKS K S) (x : ambU h1 W Δ) :
    augAmb h1 W (ambRhoU h1 W Δ g x) = inflMap K h1 g • augAmb h1 W x := by
  have key : ∀ y : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W,
      augAmb h1 W (ambRhoU h1 W Δ g (y : ambU h1 W Δ)) =
        inflMap K h1 g • augAmb h1 W (y : ambU h1 W Δ) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul u P =>
      rw [ambRhoU_tmul, augAmb_tmul, augAmb_tmul, smul_comm]
    | add y z hy hz =>
      show augAmb h1 W (ambRhoU h1 W Δ g ((show ambU h1 W Δ from y) + (show ambU h1 W Δ from z)))
        = inflMap K h1 g • augAmb h1 W ((show ambU h1 W Δ from y) + (show ambU h1 W Δ from z))
      rw [map_add, map_add, hy, hz, map_add, smul_add]
  exact key x

/-- `aug(u x) = ε(u) aug x`. Kind: PROVED. -/
theorem augAmb_smul (u : MonoidAlgebra ℤ Δ) (x : ambU h1 W Δ) :
    augAmb h1 W (u • x) = augε Δ u • augAmb h1 W x := by
  have key : ∀ y : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W,
      augAmb h1 W (u • (y : ambU h1 W Δ)) = augε Δ u • augAmb h1 W (y : ambU h1 W Δ) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul v P =>
      change augAmb h1 W (((u * v) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) : ambU h1 W Δ) = _
      rw [augAmb_tmul, augAmb_tmul, map_mul, mul_smul]
    | add y z hy hz =>
      show augAmb h1 W (u • ((show ambU h1 W Δ from y) + (show ambU h1 W Δ from z))) =
        augε Δ u • augAmb h1 W ((show ambU h1 W Δ from y) + (show ambU h1 W Δ from z))
      rw [smul_add, map_add, map_add, smul_add]
      exact congrArg₂ (· + ·) hy hz
  exact key x

/-- `ε(χ_h [π](g)) = χ_h(g)`. Kind: PROVED. -/
theorem augε_alphaShap [Fintype Δ] (g : GKS K S₀) :
    augε Δ ((alphaShap s hs hs0 π g : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      ((quadChar s hs hs0 g : ℤˣ) : ℤ) := by
  rw [alphaShap_val, map_mul, augε_of, mul_one, map_intCast]
  rfl

/-- **`aug ∘ R(g) = χ_h(g) · g ∘ aug`** for the transfer action of `θ = χ_h [π]` (PROVED). -/
theorem augAmb_R (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)
    (g : GKS K S) (x : ambU h1 W Δ) :
    augAmb h1 W (R H (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π H hH) g x) =
      ((quadChar s hs hs0 (inflMap K hS g) : ℤˣ) : ℤ) • (inflMap K h1 g • augAmb h1 W x) := by
  let := Fintype.ofFinite Δ
  rw [R, LinearMap.smul_apply, augAmb_smul, augAmb_rho, thetaH_mk, augε_alphaShap]

end Aug

/-! ### (C4): the augmented classes of the actual points -/

section C4

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  {hS : S₀ ⊆ S} {h01 : S₀ ⊆ S₁} {h1 : S₁ ⊆ S} {W : WeierstrassCurve K} [W.IsElliptic] {i : ℕ}
  [NeZero i] {s : KS K S₀} {h : K} {hs : s ^ 2 = algebraMap K (KS K S₀) h} {hs0 : s ≠ 0}
  {hFull : FullTorsion K S₀ W (2 ^ i)}
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] {π : GKS K S₀ →* Δ} [IsOpenKer (alphaShap s hs hs0 π)]
  {P : Set (HeightOneSpectrum (𝓞 K))} {ι : Type} {place : ι × Bool → Places K S}

/-- **(C4) The augmented Shapiro class of an actual point** (PROVED; tex 3911–3915): it is the
`χ_h`-twisted Kummer cocycle `g ↦ χ_h(g) g(Q̄) − Q̄` of `Q̄ = aug(∑_δ R(r_δ) Q)`. -/
theorem aug_shapClass {Tp : Finset ι} (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp)
    (g : Fin 1 → GKS K S) :
    augAmb h1 W (ambIotaS hS h01 h1 W i s hs hs0 π
        (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) A.shapClass g)) =
      ((quadChar s hs hs0 (inflMap K hS (g 0)) : ℤˣ) : ℤ) •
          (inflMap K h1 (g 0) • augAmb h1 W A.wsumQ) - augAmb h1 W A.wsumQ := by
  rw [ActualPoint.shapClass_spec]
  have hk := (kummer_weighted_sum A.H A.r A.hr (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π A.H A.hH)
    ((2 ^ i : ℕ) : ℤ) A.y A.Q A.hQ).2 g
  rw [show kummerCochain (ambRhoU h1 W Δ) A.H A.Q = fun x => ambRhoU h1 W Δ (x 0 : GKS K S) A.Q -
    A.Q from rfl, hk, map_sub, augAmb_R]
  rfl

/-- **The augmented weighted sum is a `2^i`-division point of the `χ_h`-weighted trace**
(PROVED): `2^i Q̄ = ∑_δ χ_h(r_δ) r_δ (aug y)`. -/
theorem aug_wsumQ {Tp : Finset ι} (A : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp) :
    ((2 ^ i : ℕ) : ℤ) • augAmb h1 W A.wsumQ =
      ∑ δ, ((quadChar s hs hs0 (inflMap K hS (A.r δ)) : ℤˣ) : ℤ) •
        (inflMap K h1 (A.r δ) • augAmb h1 W A.y) := by
  have hk := (kummer_weighted_sum A.H A.r A.hr (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π A.H A.hH)
    ((2 ^ i : ℕ) : ℤ) A.y A.Q A.hQ).1
  rw [← map_zsmul, show A.wsumQ = ∑ δ, R A.H (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π A.H A.hH)
    (A.r δ) A.Q from rfl, hk, map_sum]
  exact Finset.sum_congr rfl fun δ _ => augAmb_R hS h1 W s hs hs0 π A.H A.hH (A.r δ) A.y

end C4

/-! ### The factor at the center -/

section Factor

open ZInQ.Manuscript.RC.Central (pointFactor)

variable {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))} (i : ℕ)
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)

/-- **The point factor at the center** (PROVED; tex 3913): under a ring map `sp` with
`sp(Ψ) = 1` (the specialization `t ↦ 0`), `sp(pointFactor a z z⁻¹) = sp a − 2 χ_h(σ)`,
`z = α(σ) = χ_h(σ) Ψ(σ)` — the factor `m = a_r − 2χ_h(r)` of (4.5). -/
theorem sp_pointFactor_center (k : Type) [CommRing k] [StageIsoA k i] {R0 : Type} [CommRing R0]
    (sp : k →+* R0) (hsp : ∀ d : Δ, sp ((eK k i).symm (ψ d : Acoef i)) = 1) (a : k)
    (σ : GKS K S₀) :
    sp (pointFactor a ((eK k i).symm (alphaStage i s hs hs0 π ψ σ : Acoef i))
        ((eK k i).symm (((alphaStage i s hs hs0 π ψ σ)⁻¹ : (Acoef i)ˣ) : Acoef i))) =
      sp a - 2 * (((quadChar s hs hs0 σ : ℤˣ) : ℤ) : R0) := by
  have hψinv : sp ((eK k i).symm (((ψ (π σ))⁻¹ : (Acoef i)ˣ) : Acoef i)) = 1 := by
    have h1 := hsp (π σ)
    have h2 : sp ((eK k i).symm (ψ (π σ) : Acoef i)) *
        sp ((eK k i).symm (((ψ (π σ))⁻¹ : (Acoef i)ˣ) : Acoef i)) = 1 := by
      rw [← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, map_one]
    rwa [h1, one_mul] at h2
  have hχ : ∀ u : ℤˣ, sp ((eK k i).symm ((intUnitsTo (Acoef i) u : (Acoef i)ˣ) : Acoef i)) =
      ((u : ℤ) : R0) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp [intUnitsTo]
  have hχinv : ∀ u : ℤˣ, ((u⁻¹ : ℤˣ) : ℤ) = (u : ℤ) := fun u => by
    rw [Int.units_inv_eq_self]
  have hz : alphaStage i s hs hs0 π ψ σ =
      intUnitsTo (Acoef i) (quadChar s hs hs0 σ) * ψ (π σ) := by
    simp [alphaStage, charMul_apply]
  have hzi : (alphaStage i s hs hs0 π ψ σ)⁻¹ =
      intUnitsTo (Acoef i) (quadChar s hs hs0 σ)⁻¹ * (ψ (π σ))⁻¹ := by
    rw [hz, mul_inv (intUnitsTo (Acoef i) (quadChar s hs hs0 σ)) (ψ (π σ)), map_inv]
  rw [hzi, hz]
  simp only [pointFactor, map_sub, Units.val_mul, map_mul, hχ, hsp, hψinv, hχinv, mul_one]
  ring

end Factor

/-! ### The comparison with the compact central complex, and (4.5) at a stage -/

section Comparison

open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Manuscript.RC.CalPoint (IsGlobalDivTower globalKummerCochain)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve)

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : GenuineKummerData K E₀ hZ)

attribute [local instance] mcoefModuleK

/-- **The comparison of the presentation at a stage with the compact central complex**
(tex 3911–3975, `i : K_0 → R_0` read at a coefficient stage), the named input of (4.5):

* (C1) the coefficients at the center (tex 2781–2791, 3924–3933): the specialization
  `sp : A_s → R0` (`t ↦ 0`, so `sp(Ψ) = 1`, `hspψ`), a common degree-one target `Z1` (an
  `R0`-module) with degree-zero term `Z0` and differential `dZ`, the specialization of the
  presentation's global cochains `specG`/`specG0` (`sp`-semilinear, commuting with `d`), the
  read-out `Φ` of `χ_h`-twisted torsion cochains of `E(K_{S₁})`, and the identity of the
  specialization of a pushed Shapiro cochain with the read-out of its augmentation (`hpush`; the
  push `ℤ[Δ] → A_s` followed by `t ↦ 0` is the augmentation); the twist identification
  `twistPt : E^{(h)}(K_{S_C}) → E(K_{S₁})` (tex 3904: `E^{(h)}[2^s] ≅ E[2^s](χ_h)`);
* (C2) the support comparison (tex 3911–3915): the reduction `red` of the central global
  `2`-adic cochains of `G_{K,S_C}` to `Z1` (reduction mod `2^s` followed by inflation to
  `G_{K,S}`), with the reduction of a global Kummer cochain the read-out of the `χ_h`-twisted
  Kummer cocycle of the twisted division point (`hred`);
* faithfulness: `Φ` is injective on `2^i`-torsion-valued cochains and `twistPt` is injective
  (the genuine read-out and twist identification are), so the target is not degenerate.

The local conditions (C3: the central Kummer conditions map into the presentation's conditions,
tex 3913–3915) are needed only for the lift of (4.5) to the Selmer cones and are not part of this
global-component comparison; they remain a separately named input.

Kind: definition (GLUE; the comparison of complexes is not in the tree). -/
structure CentralStageComparison where
  /-- the residue ring at the center -/
  R0 : Type
  [ringR0 : CommRing R0]
  /-- (C1) the specialization `t ↦ 0` -/
  sp : k →+* R0
  /-- (C1) `Ψ = 1` at the center -/
  hspψ : ∀ d : Δ, sp ((eK k i).symm (ψ d : Acoef i)) = 1
  /-- the degree-one cochains of the central stage complex -/
  Z1 : Type
  [acgZ1 : AddCommGroup Z1]
  [modZ1 : Module R0 Z1]
  /-- its degree-zero cochains -/
  Z0 : Type
  [acgZ0 : AddCommGroup Z0]
  /-- its differential -/
  dZ : Z0 →+ Z1
  /-- (C1) the specialization of the presentation's global cochains, degree one -/
  specG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 1 →+ Z1
  /-- (C1) degree zero -/
  specG0 : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0 →+ Z0
  /-- it commutes with the differential -/
  hd : ∀ x, specG ((globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl x) =
    dZ (specG0 x)
  /-- it is `sp`-semilinear -/
  hsmul : ∀ (c : k) x, specG (c • x) = sp c • specG x
  /-- (C1) the read-out of `χ_h`-twisted torsion cochains of `E(K_{S₁})` -/
  Φ : ((Fin 1 → GKS K S) → PtS K S₁ W) →+ Z1
  /-- (C1) the specialization of a pushed Shapiro cochain is the read-out of its augmentation -/
  hpush : ∀ c : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1,
    specG (gPushK hS W i s hs hs0 π ψ k 1 c) =
      Φ (fun g => augAmb h1 W (ambIotaS hS h01 h1 W i s hs hs0 π
        (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) c g)))
  /-- (C1) the twist identification of the central points with `E(K_{S₁})` -/
  twistPt : ((centralCurve G).baseChange (KS K G.S)).toAffine.Point →+ PtS K S₁ W
  /-- (C2) the reduction of the central global cochains -/
  red : contCochain ℤ_[2] (GKS K G.S)
    (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (centralCurve G)) 1 →+ Z1
  /-- (C2) the reduction of a global Kummer cochain -/
  hred : ∀ {P : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) P Rt),
    red (globalKummerCochain hR) = Φ (fun g =>
      ((quadChar s hs hs0 (inflMap K hS (g 0)) : ℤˣ) : ℤ) •
        (inflMap K h1 (g 0) • twistPt (Rt i)) - twistPt (Rt i))
  /-- faithfulness: `Φ` is injective on `2^i`-torsion-valued cochains -/
  hΦinj : ∀ f : (Fin 1 → GKS K S) → PtS K S₁ W, (∀ g, (2 ^ i : ℕ) • f g = 0) → Φ f = 0 → f = 0
  /-- faithfulness: the twist identification is injective -/
  twistPt_injective : Function.Injective twistPt

attribute [instance] CentralStageComparison.ringR0 CentralStageComparison.acgZ1
  CentralStageComparison.modZ1 CentralStageComparison.acgZ0

/-- **The comparison's target is not degenerate** (PROVED): if `E(K_{S₁})` has a nonzero
`2^i`-torsion point (e.g. under full `2^i`-torsion), the degree-one target `Z1` is nontrivial. -/
theorem CentralStageComparison.nontrivial_Z1
    (C : CentralStageComparison hS h01 h1 W i s hs hs0 π ψ k G)
    {t : PtS K S₁ W} (ht : t ≠ 0) (ht2 : (2 ^ i : ℕ) • t = 0) : Nontrivial C.Z1 := by
  refine ⟨⟨C.Φ (fun _ => t), 0, fun h0 => ht ?_⟩⟩
  have := C.hΦinj (fun _ => t) (fun _ => ht2) h0
  exact congrFun this (fun _ => 1)

variable {hS h01 h1 W i s hs hs0 π ψ k G}

/-- **(4.5) at a stage, global component** (PROVED from the named comparison; tex 3911–3915):
for the actual points `A_T`, `A_R` of a switch at the moving prime with the global identity
`g_R = pointFactor a z z⁻¹ · g_T + d b_G` (`gx_step_heegner_at`, `z = α(σ)`), and a global tower
`R` of a central point `P` whose twisted `2^i`-division point is the augmented weighted sum of
`A_T` (`htower`; for the text `P = P^{rc}`, the descent of the `χ_h`-weighted trace,
`aug_wsumQ`), the specialization of the class of `A_R` is
`specG g_R = (sp a − 2χ_h(σ)) · red(κ(P)) + dZ(…)`: the retained boundary `z̄ = i(m · P)` with
`m = a_r − 2χ_h(r)`. The fixed multiplier `L` of (H11) is not carried by these classes (it
multiplies both sides of the text's (4.5)). -/
theorem central45_global (hFull : FullTorsion K S₀ W (2 ^ i)) {P : Set (HeightOneSpectrum (𝓞 K))}
    {ι : Type} {place : ι × Bool → Places K S}
    (C : CentralStageComparison hS h01 h1 W i s hs hs0 π ψ k G) {Tp Tq : Finset ι}
    (AT : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp)
    (AR : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tq)
    (a : k) (σ : GKS K S₀)
    (bG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0)
    (hG : gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR =
      pointFactor a ((eK k i).symm (alphaStage i s hs hs0 π ψ σ : Acoef i))
          ((eK k i).symm (((alphaStage i s hs hs0 π ψ σ)⁻¹ : (Acoef i)ˣ) : Acoef i)) •
        gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AT +
      (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG)
    {Pc : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) Pc Rt)
    (htower : C.twistPt (Rt i) = augAmb h1 W AT.wsumQ) :
    C.specG (gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR) =
      (C.sp a - 2 * (((quadChar s hs hs0 σ : ℤˣ) : ℤ) : C.R0)) •
          C.red (globalKummerCochain hR) + C.dZ (C.specG0 bG) := by
  rw [hG, map_add, C.hsmul, C.hd, sp_pointFactor_center i s hs hs0 π ψ k C.sp C.hspψ a σ,
    C.hred hR, htower]
  congr 2
  rw [gx, C.hpush]
  congr 1
  funext g
  exact aug_shapClass AT g

end Comparison

end ZInQ.Contrib.CloudB3E2.NormCochain

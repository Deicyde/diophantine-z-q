import ZInQKernel.Contrib.CloudB3E2Norm.H20HeegnerNorm
import ZInQKernel.Contrib.CloudB3E2Norm.H20Twist

/-!
# The transport of the Heegner point data: reduction to an explicit `ℚ̄ → K̄` dictionary

Manuscript `diophantine_zq.tex`, tex 2914–2936 (the Heegner points `y_d = π(x_d) ∈ E(H_d)` and the
norm relations (4.1)) and tex 4157–4170 (the norm identity in the twisted-transfer form).

`H20HeegnerNorm.lean` takes the norm relation `hnorm` from the print `CCLThm2_15Applied` through the
GLUE `HeegnerTransportAt`: an additive comparison `j : E(ℚ̄) → D` into the ambient module of points,
compatible with the Galois data of `HeegnerPointData` (which is abstract: `H`, `y`, `relGal`, `frob`
are fields with no stated relations). For the ambient module of points of `H20Twist.lean`,
`D = (ℤ[Δ] ⊗ E(K_{S₀}))(χ_h)`, no comparison is defined on all of `E(ℚ̄)`; this file replaces it by one
defined on the points that are realized in `E(K_{S₀})`, and constructs it from an explicit
dictionary.

* **`HeegnerTransportOn`** (Prop; GLUE form): as `HeegnerTransportAt`, with `j` defined on an
  additive subgroup `Λ ⊆ E(ℚ̄)` containing the points used.
* **`hnorm_of_normRelations_on`**, **`hnorm_of_print_on`** (PROVED): the norm relation from
  `D.NormRelations` (resp. the print) and `HeegnerTransportOn`, as in `H20HeegnerNorm.lean`.
* `nonVacuity_transportOn` (the zero comparison into the zero system).
* `bc_eq`, `compQ κ` (definitions/PROVED): for an embedding `κ : ℚ̄ → K̄` over `ℚ`, the comparison
  `E(ℚ̄) → E(K̄)` (with `E ×_ℚ K̄ = (E ×_ℚ K) ×_K K̄`); `incS`: `E(K_{S₀}) → E(K̄)`; `dictΛ`, `preS`,
  `dictJ` (definitions): the points of `E(ℚ̄)` realized in `E(K_{S₀})`, their realization, and
  `x ↦ 1 ⊗ x` into the ambient module of points.
* **`heegnerTransportOn_of_dictionary`** (PROVED): for `W = E ×_ℚ K`, the ambient module of points
  `ambD` and `ρ = ambRho`, `HeegnerTransportOn` holds with `y_R = 1 ⊗ P_R`, `y_P = 1 ⊗ P_P` from the
  dictionary:
  1. `κ(y_{dq}) = P_R` and `κ(y_d) = P_P` for points `P_R, P_P ∈ E(K_{S₀})` (the Heegner points are
     realized in `E(K_{S₀})`; by `DivisionPointsF.le_unramifiedOutside_of_field` with the ring class
     fields in `K_{S₀}`, `RingClassKS.ringClassField_le_KS`, once `κ(H_n) = H_n` inside `K̄`);
  2. a bijection `e : H_P/U ≃ relGal d q` with `κ(τ_e y_{dq}) = t_τ · P_R` (the transversal of
     `Gal(H_{dq}/H_d)` matches the lifts of `HeegnerPointData`);
  3. `κ(frob y_d) = σ · P_P`, `κ(frob⁻¹ y_d) = σ⁻¹ · P_P` (the Frobenius matches `σ`);
  4. `χ_h(t_τ) = χ_h(σ) = 1` (the character of the twist is trivial on these elements, e.g. when
     `√h ∈ H_d`).

Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied`; the dictionary is the GLUE.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve
open scoped WeierstrassCurve

set_option linter.unusedSectionVars false

/-! ### Transport on a subgroup -/

section On

variable {E : WeierstrassCurve ℚ} {G : Type*} [Group G] {A : Type*} [CommRing A] {Dm : Type*}
  [AddCommGroup Dm] [Module A Dm] (ρ : G →* Module.End A Dm)
  (HP : Subgroup G) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP)

/-- **The transport of the Heegner point data on a subgroup** at `(d, q)` (Prop; GLUE): an
additive comparison `j : Λ → D` on a subgroup `Λ ⊆ E(ℚ̄)` containing `y_{dq}`, its conjugates by
`relGal d q`, `y_d` and its Frobenius conjugates, with the compatibilities of
`HeegnerTransportAt`. Kind: definition (Prop). -/
def HeegnerTransportOn (D : HeegnerPointData E) (d q : ℕ) (σ : G) (yR yP : Dm) : Prop :=
  ∃ (Λ : AddSubgroup (E⁄Qbar).toAffine.Point) (j : Λ →+ Dm) (e : HP ⧸ U ≃ D.relGal d q)
    (hR : D.y (d * q) ∈ Λ) (hP : D.y d ∈ Λ)
    (hτ : ∀ τ : HP ⧸ U, Affine.Point.map (e τ).1.toAlgHom (D.y (d * q)) ∈ Λ)
    (hf : Affine.Point.map (D.frob d q).toAlgHom (D.y d) ∈ Λ)
    (hfi : Affine.Point.map (D.frob d q)⁻¹.toAlgHom (D.y d) ∈ Λ),
    j ⟨_, hR⟩ = yR ∧ j ⟨_, hP⟩ = yP ∧
    (∀ τ : HP ⧸ U, ρ (t τ : G) yR = j ⟨_, hτ τ⟩) ∧
    j ⟨_, hf⟩ = ρ σ yP ∧ j ⟨_, hfi⟩ = ρ σ⁻¹ yP

/-- **`hnorm` from the norm relations (4.1) and the transport on a subgroup** (PROVED; tex
2924–2929, 4157–4170). -/
theorem hnorm_of_normRelations_on (D : HeegnerPointData E) (hD : D.NormRelations) {d q : ℕ}
    (hadm : D.Admissible d q) (hsplit : jacobiSym D.DK q = 1) {σ : G} {yR yP : Dm}
    (htr : HeegnerTransportOn ρ HP U t D d q σ yR yP) :
    ∑ τ : HP ⧸ U, ρ (t τ : G) yR =
      (E.LFunction q : ℤ) • yP - ρ σ yP - ρ σ⁻¹ yP := by
  obtain ⟨Λ, j, e, hR, hP, hτ, hf, hfi, hjR, hjP, hjτ, hjf, hjfi⟩ := htr
  have hrel := hD.2 d q hadm hsplit
  have hmem : ∀ x ∈ D.relGal d q, Affine.Point.map x.toAlgHom (D.y (d * q)) ∈ Λ := by
    intro x hx
    have := hτ (e.symm ⟨x, hx⟩)
    rwa [Equiv.apply_symm_apply] at this
  have hsum : ∑ τ : HP ⧸ U, ρ (t τ : G) yR =
      j ⟨∑ x ∈ D.relGal d q, Affine.Point.map x.toAlgHom (D.y (d * q)),
        AddSubgroup.sum_mem Λ hmem⟩ := by
    have h1 : (⟨∑ x ∈ D.relGal d q, Affine.Point.map x.toAlgHom (D.y (d * q)),
        AddSubgroup.sum_mem Λ hmem⟩ : Λ) = ∑ τ : HP ⧸ U, ⟨_, hτ τ⟩ := by
      apply Subtype.ext
      change ∑ x ∈ D.relGal d q, Affine.Point.map x.toAlgHom (D.y (d * q)) = _
      rw [AddSubgroup.val_finsetSum, ← Finset.sum_coe_sort (D.relGal d q)]
      exact (Fintype.sum_equiv e _ _ (fun τ => rfl)).symm
    rw [h1, map_sum]
    exact Finset.sum_congr rfl fun τ _ => hjτ τ
  have h2 : (⟨∑ x ∈ D.relGal d q, Affine.Point.map x.toAlgHom (D.y (d * q)),
      AddSubgroup.sum_mem Λ hmem⟩ : Λ) =
      (E.LFunction q : ℤ) • ⟨_, hP⟩ - ⟨_, hf⟩ - ⟨_, hfi⟩ := Subtype.ext hrel
  rw [hsum, h2, map_sub, map_sub, map_zsmul, hjP, hjf, hjfi]

/-- **`hnorm` from the print and the transport on a subgroup** (PROVED from the PRINT
`CCLThm2_15Applied`). -/
theorem hnorm_of_print_on {Anchor : HeegnerPointData E → Prop}
    (hprint : CCLThm2_15Applied E Anchor) {d q : ℕ} (σ : G) (yR yP : HeegnerPointData E → Dm)
    (hadm : ∀ D, Anchor D → D.Admissible d q) (hsplit : ∀ D : HeegnerPointData E, Anchor D →
      jacobiSym D.DK q = 1)
    (htr : ∀ D, Anchor D → HeegnerTransportOn ρ HP U t D d q σ (yR D) (yP D)) :
    ∃ D : HeegnerPointData E, Anchor D ∧
      ∑ τ : HP ⧸ U, ρ (t τ : G) (yR D) =
        (E.LFunction q : ℤ) • yP D - ρ σ (yP D) - ρ σ⁻¹ (yP D) := by
  obtain ⟨D, hD, hA⟩ := hprint
  exact ⟨D, hA, hnorm_of_normRelations_on ρ HP U t D hD (hadm D hA) (hsplit D hA) (htr D hA)⟩

/-- **Non-vacuity of `HeegnerTransportOn`** (logical consistency only): the zero comparison on the
whole group into the zero system. -/
theorem nonVacuity_transportOn {E : WeierstrassCurve ℚ} {G : Type*} [Group G] {A : Type*}
    [CommRing A] {Dm : Type*} [AddCommGroup Dm] [Module A Dm] (ρ : G →* Module.End A Dm)
    (HP : Subgroup G) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP) (DK : ℤ) (N d q : ℕ)
    (H : ℕ → IntermediateField ℚ Qbar) (frob : ℕ → ℕ → GalQ) (σ : G)
    (rg : Finset GalQ) (e : HP ⧸ U ≃ rg) :
    HeegnerTransportOn ρ HP U t (HeegnerPointData.mk (E := E) DK N H (fun _ => 0) (fun _ _ => rg)
      frob) d q σ 0 0 :=
  ⟨⊤, 0, e, trivial, trivial, fun _ => trivial, trivial, trivial, rfl, rfl, fun _ => by simp,
    by simp, by simp⟩

end On

/-! ### The dictionary -/

section Dictionary

attribute [local instance] groupRingTop ptSAction

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)

/-- `E ×_ℚ K̄ = (E ×_ℚ K) ×_K K̄`. Kind: PROVED. -/
theorem bc_eq : (E.baseChange K).baseChange (AlgebraicClosure K) =
    E.baseChange (AlgebraicClosure K) := by
  rw [baseChange, baseChange, baseChange, WeierstrassCurve.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- **The comparison `E(ℚ̄) → E(K̄)` along `κ : ℚ̄ → K̄`**. Kind: definition. -/
def compQ (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) :
    (E⁄Qbar).toAffine.Point →+ ((E.baseChange K).baseChange (AlgebraicClosure K)).toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure K) => V.toAffine.Point)
    (bc_eq E).symm).toAddMonoidHom.comp (Affine.Point.map (W' := E) κ)

/-- `E(K_{S₀}) → E(K̄)`. Kind: definition. -/
abbrev incS (S₀ : Set (HeightOneSpectrum (𝓞 K))) (W : WeierstrassCurve K) :
    PtS K S₀ W →+ (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  Affine.Point.map (W' := W) (unramifiedOutside K S₀).val

/-- `incS` is injective. Kind: PROVED. -/
theorem incS_injective (S₀ : Set (HeightOneSpectrum (𝓞 K))) (W : WeierstrassCurve K) :
    Function.Injective (incS S₀ W) :=
  Affine.Point.map_injective (W' := W) (unramifiedOutside K S₀).val

variable {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) [(E.baseChange K).IsElliptic]
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Finite Δ]

/-- The points of `E(ℚ̄)` realized in `E(K_{S₀})` along `κ`. Kind: definition. -/
abbrev dictΛ (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) : AddSubgroup (E⁄Qbar).toAffine.Point :=
  (AddMonoidHom.range (incS S₀ (E.baseChange K))).comap (compQ E κ)

/-- The realization `Λ → E(K_{S₀})`. Kind: definition. -/
def preS (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) :
    dictΛ (S₀ := S₀) E κ →+ PtS K S₀ (E.baseChange K) where
  toFun x := Classical.choose (AddMonoidHom.mem_range.1 x.2)
  map_zero' := by
    apply incS_injective S₀ (E.baseChange K)
    rw [Classical.choose_spec (AddMonoidHom.mem_range.1 (0 : dictΛ (S₀ := S₀) E κ).2)]
    change compQ E κ 0 = incS S₀ (E.baseChange K) 0
    rw [map_zero, map_zero]
  map_add' x y := by
    apply incS_injective S₀ (E.baseChange K)
    rw [map_add, Classical.choose_spec (AddMonoidHom.mem_range.1 (x + y).2),
      Classical.choose_spec (AddMonoidHom.mem_range.1 x.2),
      Classical.choose_spec (AddMonoidHom.mem_range.1 y.2)]
    exact map_add _ _ _

/-- The realization of a realized point is the given point. Kind: PROVED. -/
theorem preS_eq (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) (x : (E⁄Qbar).toAffine.Point)
    (P : PtS K S₀ (E.baseChange K)) (hx : compQ E κ x = incS S₀ (E.baseChange K) P) :
    preS (S₀ := S₀) E κ ⟨x, ⟨P, hx.symm⟩⟩ = P := by
  apply incS_injective S₀ (E.baseChange K)
  exact (Classical.choose_spec (AddMonoidHom.mem_range.1
    (⟨x, ⟨P, hx.symm⟩⟩ : dictΛ (S₀ := S₀) E κ).2)).trans hx

/-- The comparison `E(ℚ̄) ⊇ Λ → ℤ[Δ] ⊗ E(K_{S₀})`, `x ↦ 1 ⊗ x` on the points realized in
`E(K_{S₀})`. Kind: definition. -/
def dictJ (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) :
    dictΛ (S₀ := S₀) E κ →+ ambD hS (E.baseChange K) s hs hs0 (Δ := Δ) :=
  (TensorProduct.mk ℤ (MonoidAlgebra ℤ Δ) (PtS K S₀ (E.baseChange K)) 1).toAddMonoidHom.comp
    (preS E κ)

/-- The value of `dictJ` at a realized point. Kind: PROVED. -/
theorem dictJ_apply (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) (x : (E⁄Qbar).toAffine.Point)
    (P : PtS K S₀ (E.baseChange K)) (hx : compQ E κ x = incS S₀ (E.baseChange K) P) :
    dictJ E hS s hs hs0 (Δ := Δ) κ ⟨x, ⟨P, hx.symm⟩⟩ =
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) := by
  change (1 : MonoidAlgebra ℤ Δ) ⊗ₜ[ℤ] preS (S₀ := S₀) E κ ⟨x, ⟨P, hx.symm⟩⟩ = _
  rw [preS_eq E κ x P hx]

/-- `ρ(g)(1 ⊗ P) = 1 ⊗ g P` when `χ_h(g) = 1`. Kind: PROVED. -/
theorem ambRho_oneTmul (g : GKS K S) (hg : quadChar s hs hs0 (inflMap K hS g) = 1)
    (P : PtS K S₀ (E.baseChange K)) :
    ambRho hS (E.baseChange K) s hs hs0 (Δ := Δ) g
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) =
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ (inflMap K hS g • P) :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) := by
  have h1 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (chiZ s hs hs0 (Δ := Δ))
    (PtS K S₀ (E.baseChange K)) (inflMap K hS g) 1 P
  change (inflMap K hS g • CoefMod.equiv _ _ _ ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P) :
    ambD₀ (E.baseChange K) s hs hs0 (Δ := Δ)) = CoefMod.equiv _ _ _ (_ ⊗ₜ _)
  rw [h1]
  congr 2
  simp [chiZ, hg]

variable {G : Type} (HP : Subgroup (GKS K S)) (U : Subgroup HP) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP)

/-- **`HeegnerTransportOn` from the explicit `ℚ̄ → K̄` dictionary** (PROVED; tex 2914–2936): for
`W = E ×_ℚ K`, the ambient module of points and `ρ = ambRho`, the realization of `y_{dq}`, `y_d` in
`E(K_{S₀})` along `κ`, the matching of `relGal d q` with the transversal `t` and of `frob` with `σ`,
and the triviality of `χ_h` on `t_τ` and `σ` give the transport with `y_R = 1 ⊗ P_R`,
`y_P = 1 ⊗ P_P`.
**Superseded for the wiring** (see `H20Untwisted.lean`): the statement is valid, but with the
`χ_h`-twisted ambient module the norm relation needed by `h1_shapiro` holds only when `χ_h(σ_q) =
1`, and the point factor loses the text's sign `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172); wire the
untwisted instance instead (`heegnerTransportOn_of_dictionaryU`). -/
theorem heegnerTransportOn_of_dictionary (D : HeegnerPointData E) (d q : ℕ) (σ : GKS K S)
    (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) (PR PP : PtS K S₀ (E.baseChange K))
    (hR : compQ E κ (D.y (d * q)) = incS S₀ (E.baseChange K) PR)
    (hP : compQ E κ (D.y d) = incS S₀ (E.baseChange K) PP)
    (e : HP ⧸ U ≃ D.relGal d q)
    (hτ : ∀ τ, compQ E κ (Affine.Point.map (e τ).1.toAlgHom (D.y (d * q))) =
      incS S₀ (E.baseChange K) (inflMap K hS (t τ : GKS K S) • PR))
    (hf : compQ E κ (Affine.Point.map (D.frob d q).toAlgHom (D.y d)) =
      incS S₀ (E.baseChange K) (inflMap K hS σ • PP))
    (hfi : compQ E κ (Affine.Point.map (D.frob d q)⁻¹.toAlgHom (D.y d)) =
      incS S₀ (E.baseChange K) (inflMap K hS σ⁻¹ • PP))
    (hχτ : ∀ τ, quadChar s hs hs0 (inflMap K hS (t τ : GKS K S)) = 1)
    (hχσ : quadChar s hs hs0 (inflMap K hS σ) = 1) :
    HeegnerTransportOn (ambRho hS (E.baseChange K) s hs hs0 (Δ := Δ)) HP U t D d q σ
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ PR : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K))
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ PP : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) := by
  have hχσi : quadChar s hs hs0 (inflMap K hS σ⁻¹) = 1 := by
    rw [map_inv, map_inv, hχσ, inv_one]
  refine ⟨_, dictJ E hS s hs hs0 (Δ := Δ) κ, e, ⟨PR, hR.symm⟩, ⟨PP, hP.symm⟩,
    fun τ => ⟨_, (hτ τ).symm⟩, ⟨_, hf.symm⟩, ⟨_, hfi.symm⟩,
    dictJ_apply E hS s hs hs0 κ _ PR hR, dictJ_apply E hS s hs hs0 κ _ PP hP,
    fun τ => ?_, ?_, ?_⟩
  · rw [dictJ_apply E hS s hs hs0 κ _ _ (hτ τ)]
    exact ambRho_oneTmul E hS s hs hs0 _ (hχτ τ) PR
  · rw [dictJ_apply E hS s hs hs0 κ _ _ hf]
    exact (ambRho_oneTmul E hS s hs hs0 _ hχσ PP).symm
  · rw [dictJ_apply E hS s hs hs0 κ _ _ hfi]
    exact (ambRho_oneTmul E hS s hs hs0 _ hχσi PP).symm

end Dictionary

end ZInQ.Contrib.CloudB3E2.NormCochain

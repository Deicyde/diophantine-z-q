/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MulSemiringAction_exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_MulSemiringAction_exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem MulSemiringAction.exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle
    {C : Type*} [inst_t1 : Field C] [inst_t2 : TopologicalSpace C] [inst_t3 : IsTopologicalRing C]
    {G : Type*} [inst_t4 : Monoid G] [inst_t5 : TopologicalSpace G] [inst_t6 : MulSemiringAction G C] (χ : G →* Cˣ)
    (hχ : ∀ k : ℤ, k ≠ 0 → ∀ c : C, (∀ σ : G, σ • c = (χ σ : C) ^ k * c) → c = 0)
    (hχG : ∀ σ τ : G, σ • (χ τ : C) = χ τ)
    (hχc : ∀ k : ℤ, Continuous fun σ : G => (χ σ : C) ^ k)
    (m : ℤ) (hm : m ≠ 0)
    (hH1 : ∀ c : G → C, Continuous c →
      (∀ σ τ : G, c (σ * τ) = c σ + (χ σ : C) ^ (-m) * σ • c τ) →
        ∃ b : C, ∀ σ : G, c σ = (χ σ : C) ^ (-m) * σ • b - b)
    {W : Type*} [inst_t7 : AddCommGroup W] [inst_t8 : Module C W] [inst_t9 : FiniteDimensional C W] (ρ : G → W →+ W)
    (hρ : ∀ (σ : G) (c : C) (w : W), ρ σ (c • w) = (σ • c) • ρ σ w)
    (hρmul : ∀ (σ τ : G) (w : W), ρ (σ * τ) w = ρ σ (ρ τ w))
    (hρc : ∀ (f : W →ₗ[C] C) (w : W), Continuous fun σ : G => f (ρ σ w))
    {W' : Type*} [inst_t10 : AddCommGroup W'] [inst_t11 : Module C W'] (ρ' : G → W' →+ W')
    (hρ' : ∀ (σ : G) (c : C) (w' : W'), ρ' σ (c • w') = (σ • c) • ρ' σ w')
    (B : W →ₗ[C] W' →ₗ[C] C)
    (hB : ∀ (σ : G) (w : W) (w' : W'), B (ρ σ w) (ρ' σ w') = (χ σ : C) ^ m * σ • B w w')
    (hBr : ∀ w' : W', (∀ w : W, B w w' = 0) → w' = 0)
    {ι ι' : Type*} [inst_t12 : Fintype ι] [inst_t13 : Fintype ι']
    (v : ι → W) (hv : ∀ (σ : G) (i : ι), ρ σ (v i) = v i) (hvi : LinearIndependent C v)
    (v' : ι' → W') (hv' : ∀ (σ : G) (j : ι'), ρ' σ (v' j) = v' j)
    (hvi' : LinearIndependent C v')
    (hcard : Fintype.card ι + Fintype.card ι' = Module.finrank C W) :
    ∃ b : Module.Basis (ι ⊕ ι') C W,
      (∀ i, b (Sum.inl i) = v i) ∧
      (∀ (σ : G) (j : ι'), ρ σ (b (Sum.inr j)) = ((χ σ : C) ^ m) • b (Sum.inr j)) ∧
      (∀ j, B (b (Sum.inr j)) (v' j) = 1 ∧ ∀ j', j' ≠ j → B (b (Sum.inr j)) (v' j') = 0) ∧
      (∀ w : W, (∀ σ : G, ρ σ w = w) ↔
        w ∈ Submodule.span (FixedPoints.subfield G C) (Set.range v)) ∧
      (∀ w : W, (∀ σ : G, ρ σ w = ((χ σ : C) ^ m) • w) ↔
        w ∈ Submodule.span (FixedPoints.subfield G C) (Set.range fun j => b (Sum.inr j))) ∧
      (∀ w' : W', (∀ σ : G, ρ' σ w' = w') ↔
        w' ∈ Submodule.span (FixedPoints.subfield G C) (Set.range v')) ∧
      (∀ (k : ℤ) (w : W), k ≠ 0 → k ≠ m → (∀ σ : G, ρ σ w = ((χ σ : C) ^ k) • w) → w = 0) :=
  @_root_.P2MW.S_MulSemiringAction_exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle.solution C inst_t1 inst_t2 inst_t3 G inst_t4 inst_t5 inst_t6 χ hχ hχG hχc m hm hH1 W inst_t7 inst_t8 inst_t9 ρ hρ hρmul hρc W' inst_t10 inst_t11 ρ' hρ' B hB hBr ι ι' inst_t12 inst_t13 v hv hvi v' hv' hvi' hcard

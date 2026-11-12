import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-descent/Cochain.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-descent: the group theory of B2-B3 (N5 L693-716)

`G` stands for `G_ℚ` (or the finite quotient `Gal(L'/ℚ)` through which everything factors),
`H` for `G_L` (normal, of index `d = [L:ℚ]`), `ε` for the sign cocycle inflated from
`Gal(L/ℚ) = G/H` and normalized, `U` for the coefficient group (`E^×` for a field `E`), and
`β : G → U` for the cochain with `β σ β τ = ε(σ,τ) β(στ)`.

Proved here, over arbitrary groups (genuine Mathlib definitions):

* `β|_H` is a homomorphism and is invariant under conjugation by `G` (N5 L701);
* `K' = ker β|_H` is normal in `G`, and `β` is constant on its cosets, so `β` factors
  through `G/K' = Gal(L'/ℚ)` (implicit in N5);
* if `β^{2m} = 1` on `H` with values in a field, `[H : K'] ≤ 2m`, hence
  `[G : K'] ≤ 2m [G : H]` (N5 L711-714: `[L':ℚ] ≤ 2md`);
* twisting by a character `η` with `η² = 1` changes neither `β² = χ` nor `dβ = ε`
  (N5 L707-709);
* the cohomological core of B2: if `ε · (dβ₀)⁻¹ = dγ` with `β₀² = χ` and `γ` valued in `±1`,
  then `β = β₀ γ⁻¹` has `β² = χ` and `dβ = ε` (N5 L694-700).
-/

namespace GlueDescent

section Basic

variable {G : Type*} [Group G] {U : Type*} [CommGroup U]

/-- The coboundary relation `β σ β τ = ε(σ,τ) β(στ)` (N5 L698). -/
def IsCochainFor (ε : G → G → U) (β : G → U) : Prop :=
  ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ)

/-- `ε` is inflated from `G/H` and normalized: it is `1` as soon as one argument lies in `H`.
(This is what "inflated from `Gal(L/ℚ)`" with `μ₁ = 1` gives: `ε(σ,τ)` depends only on the
classes of `σ, τ` mod `H` and vanishes when one class is trivial.) -/
def InflatedNormalized (H : Subgroup G) (ε : G → G → U) : Prop :=
  ∀ σ τ, (σ ∈ H ∨ τ ∈ H) → ε σ τ = 1

variable {H : Subgroup G} {ε : G → G → U} {β : G → U}

theorem cochain_one (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) : β 1 = 1 := by
  have h := hβ 1 1
  rw [hε 1 1 (Or.inl H.one_mem), one_mul, mul_one] at h
  exact mul_eq_left.mp h

theorem cochain_mul_right (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (σ : G)
    {s : G} (hs : s ∈ H) : β (σ * s) = β σ * β s := by
  rw [hβ, hε σ s (Or.inr hs), one_mul]

theorem cochain_mul_left (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (σ : G)
    {s : G} (hs : s ∈ H) : β (s * σ) = β s * β σ := by
  rw [hβ, hε s σ (Or.inl hs), one_mul]

/-- **B3, `β|_H` is a homomorphism** (N5 L701: "Its restriction to `G_L` is a character"). -/
def restrictHom (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) : H →* U where
  toFun s := β s
  map_one' := cochain_one hβ hε
  map_mul' s t := cochain_mul_right hβ hε s t.2

/-- **B3, invariance under `G`** (N5 L701: "invariant under `G_ℚ`"): for `s ∈ H` normal,
`β(σ s σ⁻¹) = β(s)`. -/
theorem cochain_conj [H.Normal] (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (σ : G)
    {s : G} (hs : s ∈ H) : β (σ * s * σ⁻¹) = β s := by
  have hc : σ * s * σ⁻¹ ∈ H := Subgroup.Normal.conj_mem inferInstance s hs σ
  have h1 : β (σ * s) = β σ * β s := cochain_mul_right hβ hε σ hs
  have h2 : β (σ * s) = β (σ * s * σ⁻¹) * β σ := by
    rw [← cochain_mul_left hβ hε σ hc]; group
  rw [h1, mul_comm (β (σ * s * σ⁻¹))] at h2
  exact (mul_left_cancel h2).symm

/-- `K' = ker(β|_H)`, as a subgroup of `G`. -/
def kernelSubgroup (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) : Subgroup G :=
  (restrictHom hβ hε).ker.map H.subtype

theorem mem_kernelSubgroup (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) {g : G} :
    g ∈ kernelSubgroup hβ hε ↔ g ∈ H ∧ β g = 1 := by
  constructor
  · rintro ⟨⟨s, hs⟩, hk, rfl⟩
    exact ⟨hs, hk⟩
  · rintro ⟨hs, hk⟩
    exact ⟨⟨g, hs⟩, hk, rfl⟩

/-- **B3, `L'/ℚ` is Galois** (N5 L712: "Conjugacy invariance shows that `L'/ℚ` is Galois"):
`K'` is normal in `G`. -/
theorem kernelSubgroup_normal [H.Normal] (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) :
    (kernelSubgroup hβ hε).Normal where
  conj_mem g hg σ := by
    rw [mem_kernelSubgroup] at hg ⊢
    exact ⟨Subgroup.Normal.conj_mem inferInstance g hg.1 σ, by rw [cochain_conj hβ hε σ hg.1, hg.2]⟩

/-- `β` is constant on the cosets of `K'`, so it factors through `G/K' = Gal(L'/ℚ)`. -/
theorem cochain_mul_kernel (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (σ : G)
    {k : G} (hk : k ∈ kernelSubgroup hβ hε) : β (σ * k) = β σ := by
  rw [mem_kernelSubgroup] at hk
  rw [cochain_mul_right hβ hε σ hk.1, hk.2, mul_one]

/-- `K' ≤ H`. -/
theorem kernelSubgroup_le (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) :
    kernelSubgroup hβ hε ≤ H := fun _ hg => ((mem_kernelSubgroup hβ hε).mp hg).1

/-- **B3, twisting.** If `η : G →* U` and `β` is a cochain for `ε` with `β² = χ`, and
`η² = 1`, then `β η` is a cochain for `ε` with `(β η)² = χ` (N5 L707-709: "changes neither
displayed identity"). -/
theorem twist (hβ : IsCochainFor ε β) (η : G →* U) :
    IsCochainFor ε (fun σ => β σ * η σ) := by
  intro σ τ
  show β σ * η σ * (β τ * η τ) = ε σ τ * (β (σ * τ) * η (σ * τ))
  calc β σ * η σ * (β τ * η τ) = (β σ * β τ) * (η σ * η τ) := by ac_rfl
    _ = _ := by rw [hβ, ← map_mul]; ac_rfl

theorem twist_sq (χ : G → U) (hχ : ∀ σ, β σ ^ 2 = χ σ) (η : G →* U) (hη : ∀ σ, η σ ^ 2 = 1)
    (σ : G) : (β σ * η σ) ^ 2 = χ σ := by
  rw [mul_pow, hχ, hη, mul_one]

/-- **B2, the cohomological core** (N5 L694-700). `β₀` is a pointwise square root of the
character `χ`; its coboundary `ε₀(σ,τ) = β₀ σ β₀ τ / β₀(στ)` differs from `ε` by the
coboundary of a sign cochain `γ` (this is the global equality `δχ = [ε]` in
`H²(G_ℚ, ±1)`). Then `β = β₀ γ⁻¹` satisfies `β² = χ` and `dβ = ε`. -/
theorem cochain_of_boundary_eq (χ : G → U) (β₀ γ : G → U) (hβ₀ : ∀ σ, β₀ σ ^ 2 = χ σ)
    (hγ : ∀ σ, γ σ ^ 2 = 1)
    (hdiff : ∀ σ τ, β₀ σ * β₀ τ * (β₀ (σ * τ))⁻¹ =
      ε σ τ * (γ σ * γ τ * (γ (σ * τ))⁻¹)) :
    IsCochainFor ε (fun σ => β₀ σ * (γ σ)⁻¹) ∧ ∀ σ, (β₀ σ * (γ σ)⁻¹) ^ 2 = χ σ := by
  refine ⟨fun σ τ => ?_, fun σ => ?_⟩
  · have h := hdiff σ τ
    have h' : β₀ σ * β₀ τ = ε σ τ * (γ σ * γ τ * (γ (σ * τ))⁻¹) * β₀ (σ * τ) := by
      rw [← h]; group
    calc β₀ σ * (γ σ)⁻¹ * (β₀ τ * (γ τ)⁻¹) = (β₀ σ * β₀ τ) * (γ σ * γ τ)⁻¹ := by
          rw [mul_inv]; ac_rfl
      _ = ε σ τ * (β₀ (σ * τ) * (γ (σ * τ))⁻¹) * ((γ σ * γ τ) * (γ σ * γ τ)⁻¹) := by
          rw [h']; ac_rfl
      _ = ε σ τ * (β₀ (σ * τ) * (γ (σ * τ))⁻¹) := by rw [mul_inv_cancel, mul_one]
  · rw [mul_pow, hβ₀, inv_pow, hγ, inv_one, mul_one]

/-- The coboundary of a square root of a character is a sign: if `β₀² = χ` with `χ`
multiplicative, then `(β₀ σ β₀ τ / β₀(στ))² = 1`. -/
theorem boundary_sq (χ : G →* U) (β₀ : G → U) (hβ₀ : ∀ σ, β₀ σ ^ 2 = χ σ) (σ τ : G) :
    (β₀ σ * β₀ τ * (β₀ (σ * τ))⁻¹) ^ 2 = 1 := by
  rw [mul_pow, mul_pow, inv_pow, hβ₀, hβ₀, hβ₀, map_mul, mul_inv_cancel]

end Basic

section Index

variable {G : Type*} [Group G] {E : Type*} [Field E]
variable {H : Subgroup G} {ε : G → G → Eˣ} {β : G → Eˣ}

/-- **B3, the degree bound** (N5 L711-714). If `β^n = 1` on `H` (`n = 2m`: `β² = χ` and
`χ^m = 1`), then `[H : K'] ≤ n`, because the image of `β|_H` lies in the `n`-th roots of unity
of a field. -/
theorem relindex_kernel_le (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (n : ℕ)
    (hn : 0 < n) (hpow : ∀ s ∈ H, β s ^ n = 1) : (restrictHom hβ hε).ker.index ≤ n := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have hrange : (restrictHom hβ hε).range ≤ rootsOfUnity n E := by
    rintro _ ⟨s, rfl⟩
    rw [mem_rootsOfUnity]
    exact hpow s s.2
  rw [Subgroup.index_ker]
  calc Nat.card (restrictHom hβ hε).range ≤ Nat.card (rootsOfUnity n E) :=
        Subgroup.card_le_of_le hrange
    _ ≤ n := card_rootsOfUnity E n

/-- **B3, `[L':ℚ] ≤ 2m d`** in group form: `[G : K'] ≤ n [G : H]`. -/
theorem index_kernel_le (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (n : ℕ)
    (hn : 0 < n) (hpow : ∀ s ∈ H, β s ^ n = 1) :
    (kernelSubgroup hβ hε).index ≤ n * H.index := by
  have h := relindex_kernel_le hβ hε n hn hpow
  have hrel : (kernelSubgroup hβ hε).relIndex H = (restrictHom hβ hε).ker.index := by
    rw [kernelSubgroup, Subgroup.relIndex]
    congr 1
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [← Subgroup.relIndex_mul_index (kernelSubgroup_le hβ hε), hrel]
  exact Nat.mul_le_mul_right _ h

end Index

section Inertia

variable {G : Type*} [Group G] {U : Type*} [CommGroup U]

/-- **B3, the twist kills inertia outside `T`** (N5 L702-709). `I v ≤ H` are the inertia groups
at the primes `v ∉ T` (contained in `G_L` since `L` is unramified there). On each, `β` is a
quadratic character (`β² = χ` and `χ` is unramified at `v`). `unique` is leaf L-B3a (at an
odd prime there is a unique nontrivial quadratic character of inertia), and `hηI` says that the
quadratic character `η` is ramified exactly where `β` is (leaf L-B3b for the Dirichlet
character of conductor `P`). Then `βη` is trivial on every `I v`. -/
theorem twist_kills_inertia {ι : Type*} (I : ι → Subgroup G) (β : G → U) (η : G →* U)
    (hmul : ∀ v, ∀ s ∈ I v, ∀ t ∈ I v, β (s * t) = β s * β t)
    (hquad : ∀ v, ∀ s ∈ I v, β s ^ 2 = 1) (hη2 : ∀ s, η s ^ 2 = 1)
    (unique : ∀ v, ∀ φ ψ : I v →* U, (∀ s, φ s ^ 2 = 1) → (∀ s, ψ s ^ 2 = 1) →
      φ ≠ 1 → ψ ≠ 1 → φ = ψ)
    (hηI : ∀ v, (∃ s ∈ I v, η s ≠ 1) ↔ (∃ s ∈ I v, β s ≠ 1)) :
    ∀ v, ∀ s ∈ I v, β s * η s = 1 := by
  intro v s hs
  by_cases hb : ∃ s ∈ I v, β s ≠ 1
  · let βv : I v →* U :=
      { toFun := fun t => β t
        map_one' := by
          have h := hmul v 1 (I v).one_mem 1 (I v).one_mem
          rw [one_mul] at h
          exact (mul_eq_left.mp h.symm)
        map_mul' := fun t u => hmul v t t.2 u u.2 }
    let ηv : I v →* U := η.comp (I v).subtype
    have hβne : βv ≠ 1 := by
      obtain ⟨t, ht, hne⟩ := hb
      intro h; apply hne; exact congrArg (fun f : I v →* U => f ⟨t, ht⟩) h
    have hηne : ηv ≠ 1 := by
      obtain ⟨t, ht, hne⟩ := (hηI v).mpr hb
      intro h; apply hne; exact congrArg (fun f : I v →* U => f ⟨t, ht⟩) h
    have heq := unique v βv ηv (fun t => hquad v t t.2) (fun t => hη2 t) hβne hηne
    have : β s = η s := congrArg (fun f : I v →* U => f ⟨s, hs⟩) heq
    rw [this, ← sq, hη2]
  · push_neg at hb
    have hη : ∀ s ∈ I v, η s = 1 := by
      by_contra h; push_neg at h
      obtain ⟨t, ht, hne⟩ := (hηI v).mp h
      exact hne (hb t ht)
    rw [hb s hs, hη s hs, one_mul]

/-- With `βη` trivial on `I v ≤ H`, the inertia group lies in `K' = ker(βη|_H)`:
`L'` is unramified at `v`. -/
theorem inertia_le_kernel {H : Subgroup G} {ε : G → G → U} {β : G → U}
    (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (Iv : Subgroup G) (hI : Iv ≤ H)
    (htriv : ∀ s ∈ Iv, β s = 1) : Iv ≤ kernelSubgroup hβ hε := fun s hs =>
  (mem_kernelSubgroup hβ hε).mpr ⟨hI hs, htriv s hs⟩

end Inertia

end GlueDescent

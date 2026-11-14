import ZInQKernel.HDecomp.QM.Leaves

/-!
# shimura-split, Part 2: the orbit computation for `Y3Connected` (row H-59)

The row `TSHecke.Y3Connected` (`∃ (Y, Φ), R1fpProps Y Φ ∧ ConnectedSpace Y.left`) is a composite: Deligne's
description of the geometric components of a Shimura variety with the Galois action on them (Deligne,
*Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§2-3; *Variétés de Shimura*, PSPM 33 (1979), 2.1, 2.6.3),
specialized to `K₃`, **plus** an orbit computation (the Galois group acts transitively on the components,
hence `Y₃` is connected over `ℚ`). This file states the first as a leaf over genuine definitions (the
connected components of the base change `Y ×_ℚ Spec ℚ̄`, the action of `Aut(ℚ̄/ℚ)` on it, and the mod-3
cyclotomic character) and proves the row from it in Lean.
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- `Spec ℚ̄ → Spec ℚ`. -/
abbrev sQbar : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))

/-- The base change `Y_ℚ̄ = Y ×_{Spec ℚ} Spec ℚ̄` of a `ℚ`-scheme. -/
abbrev baseQbar (Y : Over (Spec (CommRingCat.of ℚ))) : Scheme := pullback Y.hom sQbar

theorem specMap_sigma_comp (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ sQbar = sQbar := by
  rw [sQbar, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (σ : Qbar →ₐ[ℚ] Qbar).comp_algebraMap

/-- **The action of `σ ∈ Aut(ℚ̄/ℚ)` on `Y_ℚ̄`**: `id_Y × Spec σ`. -/
def galAct (Y : Over (Spec (CommRingCat.of ℚ))) (σ : Qbar ≃ₐ[ℚ] Qbar) : baseQbar Y ⟶ baseQbar Y :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar))) (𝟙 _)
    (by simp) (by rw [Category.comp_id, specMap_sigma_comp])

theorem galAct_fst (Y : Over (Spec (CommRingCat.of ℚ))) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    galAct Y σ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [galAct]

/-- The induced map on the connected components of `Y_ℚ̄`. -/
def galActπ₀ (Y : Over (Spec (CommRingCat.of ℚ))) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    _root_.ConnectedComponents (baseQbar Y) → _root_.ConnectedComponents (baseQbar Y) :=
  (galAct Y σ).continuous.connectedComponentsMap

/-- **The mod-3 cyclotomic character** `χ₃ : Aut(ℚ̄/ℚ) → (ℤ/3)^×`: `σ(ζ) = ζ^{χ₃(σ)}` for the primitive cube
roots of unity `ζ`; since `(ℤ/3)^× = {±1}`, `χ₃(σ) = 1` iff `σ` fixes them. -/
def chi3 (σ : Qbar ≃ₐ[ℚ] Qbar) : (ZMod 3)ˣ :=
  open Classical in if ∀ w : Qbar, IsPrimitiveRoot w 3 → σ w = w then 1 else -1

/-- **LEAF (Deligne's components of `Sh_{K₃}` with the Galois action; specialization).**

*Published statement* (Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§2-3; *Variétés de
Shimura*, PSPM 33 (1979), 2.1 and Thm 2.6.3; Milne, *Introduction to Shimura varieties* (2005), Thm 5.17
and §13; locators UNVERIFIED, no network): for `G = B^×` the set of connected components of
`Sh_K(G, X)_ℚ̄` is `π₀ = ℚ^×_{>0} \ 𝔸_f^× / nrd(K)`, and `σ ∈ Gal(ℚ̄/ℚ)` acts on it by multiplication by
`art⁻¹(σ|ℚ^ab) ∈ ℤ̂^×` (up to the sign convention of the reciprocity map).

*Lean form*: some fine witness `(Y, Φ)` (the canonical model `Y₃ = Sh_{K₃}`, as in `CanonicalModelY3`) has
a bijection `c : π₀(Y_ℚ̄) ≃ (ℤ/3)^×` under which `σ` acts by multiplication by `χ₃(σ)`.

*Why a specialization of the display (with one computation)*: for `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`,
`nrd(K₃) = ∏_{ℓ≠3} ℤ_ℓ^× × (1 + 3ℤ_3)` (`nrd(𝒪_ℓ^×) = ℤ_ℓ^×` for every `ℓ`, and `nrd(1 + 3𝒪_3) = 1 + 3ℤ_3`),
and `𝔸_f^× = ℚ^×_{>0} · ℤ̂^×` with `ℚ^×_{>0} ∩ ℤ̂^× = 1`, so `π₀ = ℤ̂^×/nrd(K₃) = (ℤ/3)^×`; the image of
`art⁻¹(σ)` there is `χ₃(σ)^{±1} = χ₃(σ)` (`χ₃` has order 2, so the sign convention does not matter).
The computation of `nrd(K₃)` is not formalized (no local quaternion algebras in Mathlib); ts-hecke's
`pi0_check.py` checks the two orbits in Shimura's uniformization `𝒪^× \ (ℍ^± × (𝒪/3𝒪)^×)`.
So this leaf is a **consequence of one theorem** (Deligne's `π₀`), not its printed form. -/
def DeligneComponentsY3 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∃ c : _root_.ConnectedComponents (baseQbar Y) ≃ (ZMod 3)ˣ,
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (z : _root_.ConnectedComponents (baseQbar Y)),
        c (galActπ₀ Y σ z) = chi3 σ * c z

/-! ## The orbit computation -/

/-- Some `σ ∈ Aut(ℚ̄/ℚ)` has `χ₃(σ) = −1` (moves a primitive cube root of unity). -/
theorem exists_chi3_neg : ∃ σ : Qbar ≃ₐ[ℚ] Qbar, chi3 σ = -1 := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 3 Qbar)
    (by rw [Polynomial.degree_cyclotomic]; norm_num)
  have hprim : IsPrimitiveRoot ω 3 := (Polynomial.isRoot_cyclotomic_iff).1 hω
  have hprim2 : IsPrimitiveRoot (ω ^ 2) 3 := hprim.pow_of_coprime 2 (by norm_num)
  have hmin : minpoly ℚ (ω ^ 2) = minpoly ℚ ω := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim2 (by norm_num),
      ← Polynomial.cyclotomic_eq_minpoly_rat hprim (by norm_num)]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Qbar)).1 hmin
  refine ⟨σ, ?_⟩
  have hne : σ ω ≠ ω := by
    change σ • ω = ω ^ 2 at hσ
    rw [AlgEquiv.smul_def] at hσ
    rw [hσ]
    intro h
    have h1 : ω = 1 := by
      have : ω * (ω - 1) = 0 := by rw [mul_sub, ← sq, h, mul_one, sub_self]
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 (hprim.ne_zero (by norm_num))
      · exact sub_eq_zero.1 h0
    exact absurd h1 (hprim.ne_one (by norm_num))
  unfold chi3
  rw [if_neg]
  intro h
  exact hne (h ω hprim)

theorem units_zmod3 (t u : (ZMod 3)ˣ) : u = t ∨ u = -1 * t := by
  revert t u; decide

instance : AlgebraicGeometry.Surjective sQbar := by
  constructor
  intro x
  obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of Qbar)))
  exact ⟨y, Subsingleton.elim _ _⟩

/-- **The orbit computation (row H-59 from the leaf)**: if `Aut(ℚ̄/ℚ)` acts on `π₀(Y_ℚ̄) ≃ (ℤ/3)^×` by
`χ₃`, then `Y` is connected (a clopen `U ⊆ Y` pulls back to a Galois-stable clopen of `Y_ℚ̄`, a union of
components whose labels form a `χ₃`-stable subset of `(ℤ/3)^×`, hence `∅` or everything). -/
theorem y3Connected_of_deligne (h : DeligneComponentsY3) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ConnectedSpace Y.left := by
  obtain ⟨Y, Φ, h1, c, hc⟩ := h
  refine ⟨Y, Φ, h1, ?_⟩
  obtain ⟨-, -, ⟨y₀⟩, -, -, -⟩ := h1
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨y₀.left (IsLocalRing.closedPoint _)⟩, fun U hU => ?_⟩
  let p : baseQbar Y ⟶ Y.left := pullback.fst _ _
  have hpsurj : Function.Surjective p := p.surjective
  let V : Set (baseQbar Y) := p ⁻¹' U
  have hV : IsClopen V := hU.preimage p.continuous
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne0, hne1⟩ := hne
  obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 hne0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra hall
    exact hne1 (Set.eq_univ_of_forall fun a => by by_contra ha; exact hall ⟨a, ha⟩)
  obtain ⟨z, hz⟩ := hpsurj u
  obtain ⟨z', hz'⟩ := hpsurj u'
  have hzV : z ∈ V := by show p z ∈ U; rw [hz]; exact hu
  have hz'V : z' ∉ V := by show p z' ∉ U; rw [hz']; exact hu'
  -- labels of components inside `V`
  let T : Set (ZMod 3)ˣ := {t | ∃ w ∈ V, c (ConnectedComponents.mk w) = t}
  have hT : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ t ∈ T, chi3 σ * t ∈ T := by
    rintro σ t ⟨w, hw, rfl⟩
    refine ⟨galAct Y σ w, ?_, ?_⟩
    · show p (galAct Y σ w) ∈ U
      change (pullback.fst Y.hom sQbar) (galAct Y σ w) ∈ U
      rw [← Scheme.Hom.comp_apply, galAct_fst]; exact hw
    · rw [← hc σ]; rfl
  obtain ⟨σ, hσ⟩ := exists_chi3_neg
  have hzT : c (ConnectedComponents.mk z) ∈ T := ⟨z, hzV, rfl⟩
  rcases units_zmod3 (c (ConnectedComponents.mk z)) (c (ConnectedComponents.mk z')) with e | e
  · -- same component as `z`
    have hmk : ConnectedComponents.mk z' = ConnectedComponents.mk z := c.injective e
    rw [ConnectedComponents.coe_eq_coe'] at hmk
    exact hz'V (hV.connectedComponent_subset hzV hmk)
  · obtain ⟨w, hw, hwe⟩ := hT σ _ hzT
    rw [hσ, ← e] at hwe
    have hmk : ConnectedComponents.mk z' = ConnectedComponents.mk w := c.injective hwe.symm
    rw [ConnectedComponents.coe_eq_coe'] at hmk
    exact hz'V (hV.connectedComponent_subset hw hmk)

end ShimuraSplit

#print axioms ShimuraSplit.y3Connected_of_deligne

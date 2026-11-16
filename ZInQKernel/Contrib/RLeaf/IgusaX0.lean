import ZInQKernel.Contrib.RLeaf.IgusaSL2

/-!
# t40-igusa: Igusa transitivity = transitivity on cyclic subgroups + the cusp `μ_N`

`ZInQ.RLeaf.IgusaTransitive` (the `x`-coordinates of the points of exact order `N` on `E_j` form
one `Gal(\overline{ℚ(j)}/ℚ(j))`-orbit; the curve `X₁(N)` is irreducible over `ℚ`) splits into two
strictly weaker statements, each a published theorem:

* `X0Transitive` (`X₀(N)`): the Galois group permutes the cyclic subgroups of order `N` of
  `E_j` transitively (equivalently, the modular equation `Φ_N(X, j)` is irreducible over `ℚ(j)`).
* `TateMuN` (the Tate curve at `j = ∞`): for each `N` some cyclic subgroup `⟨Q₀⟩` of order `N`
  (the subgroup `μ_N` of the Tate curve) has its generators permuted transitively, on
  `x`-coordinates, by the Galois group (`Gal(ℚ((1/j))(ζ_N)/ℚ((1/j))) ≅ (ℤ/N)^×`).

Proved here: `igusaTransitive_of_x0_tateMuN : X0Transitive → TateMuN → IgusaTransitive`, and
conversely `x0Transitive_of_igusaTransitive`, `tateMuN_of_igusaTransitive`, so
`igusaTransitive_iff : IgusaTransitive ↔ X0Transitive ∧ TateMuN`.
-/

namespace ZInQ.RLeaf

open LeafModCurves WeierstrassCurve X1Belyi

/-! ## Points with the same `x`-coordinate -/

/-- `x(-P) = x(P)`. -/
theorem xCoord_neg {F : Type*} [Field F] {W : WeierstrassCurve F} (P : W.toAffine.Point) :
    xCoord (-P) = xCoord P := by
  cases P with
  | zero => rfl
  | some h => rfl

/-- Two nonzero points with the same `x`-coordinate are equal up to sign. -/
theorem eq_or_eq_neg_of_xCoord_eq {F : Type*} [Field F] {W : WeierstrassCurve F}
    {A B : W.toAffine.Point} (hA : A ≠ 0) (hB : B ≠ 0) (h : xCoord A = xCoord B) :
    A = B ∨ A = -B := by
  rcases A with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hA
  rcases B with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hB
  simp only [xCoord] at h
  subst h
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 rfl with hy | hy
  · left; subst hy; rfl
  · right; subst hy; rfl

/-- `x(σ P) = σ(x(P))` for the Galois action `galPt`. -/
theorem xCoord_galPt (σ : Kbar ≃ₐ[Qj] Kbar) (P : EjBar.toAffine.Point) :
    xCoord (galPt σ P) = σ (xCoord P) :=
  xCoord_map σ P

/-- The Galois action preserves orders of points. -/
theorem addOrderOf_galPt (σ : Kbar ≃ₐ[Qj] Kbar) (P : EjBar.toAffine.Point) :
    addOrderOf (galPt σ P) = addOrderOf P :=
  addOrderOf_injective (galPt σ) (WeierstrassCurve.Affine.Point.map_injective (W' := Ej) _) P

/-! ## The two leaves -/

/-- **`X₀(N)` is irreducible: Galois is transitive on the cyclic subgroups of order `N`**
(published). For points `P, P'` of exact order `N` on `E_j` over `\overline{ℚ(j)}` there is
`σ ∈ Aut(\overline{ℚ(j)}/ℚ(j))` with `σ P ∈ ⟨P'⟩` (so `σ⟨P⟩ = ⟨P'⟩`).

Source: the irreducibility over `ℂ(j)` of the modular equation `Φ_N(X, j)`, whose roots are the
`j(E_j/C)` for the cyclic subgroups `C` of order `N` (`C ↦ j(E_j/C)` is a Galois-equivariant
bijection because `End(E_j) = ℤ`): Lang, *Elliptic functions*, Ch. 5, §2, Thm 3; Cox, *Primes of
the form x² + ny²*, Thm 11.18; Shimura 1971, §6.1 (numbers UNVERIFIED). Also a consequence of
Igusa's theorem (`x0Transitive_of_igusaTransitive`). -/
def X0Transitive : Prop :=
  ∀ (N : ℕ) (P P' : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → addOrderOf P' = N →
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, galPt σ P ∈ AddSubgroup.zmultiples P'

/-- **The cusp `μ_N` of the Tate curve** (published). For each `N > 0` there is a point `Q₀` of
exact order `N` on `E_j` over `\overline{ℚ(j)}` such that for every generator `R` of `⟨Q₀⟩` some
`τ ∈ Aut(\overline{ℚ(j)}/ℚ(j))` sends `x(Q₀)` to `x(R)`.

Source: Tate's `p`-adic (here `1/j`-adic) uniformization: over the completion `ℚ((1/j))` of
`ℚ(j)` at `j = ∞`, `E_j` is a quadratic twist of the Tate curve `E_q`, and
`E_q(Ω) ≅ Ω^×/q^ℤ` Galois-equivariantly (Silverman, *Advanced topics in the arithmetic of
elliptic curves*, V, Thm 3.1 and Thm 5.3; Tate, *A review of non-archimedean elliptic functions*,
1995; numbers UNVERIFIED); take `Q₀` the image of a primitive `N`-th root of unity `ζ_N`. Its
generators are the images of `ζ_N^c`, `c ∈ (ℤ/N)^×`, permuted transitively by
`Gal(ℚ((1/j))(ζ_N)/ℚ((1/j))) ≅ (ℤ/N)^×` (the cyclotomic polynomial stays irreducible over
`ℚ((1/j))`); the twist changes the action by `±1`, invisible on `x`; and automorphisms of
`\overline{ℚ((1/j))}` restrict to `\overline{ℚ(j)}`. Also a consequence of Igusa's theorem
(`tateMuN_of_igusaTransitive`). -/
def TateMuN : Prop :=
  ∀ N : ℕ, 0 < N → ∃ Q₀ : EjBar.toAffine.Point, addOrderOf Q₀ = N ∧
    ∀ R ∈ AddSubgroup.zmultiples Q₀, addOrderOf R = N →
      ∃ τ : Kbar ≃ₐ[Qj] Kbar, τ (xCoord Q₀) = xCoord R

/-! ## The glue -/

/-- **Igusa transitivity from `X₀(N)`-transitivity and the cusp `μ_N`.** -/
theorem igusaTransitive_of_x0_tateMuN (h0 : X0Transitive) (hT : TateMuN) : IgusaTransitive := by
  intro N P P' hN hP hP'
  obtain ⟨Q₀, hQ₀, hτ⟩ := hT N hN
  obtain ⟨σ₁, hσ₁⟩ := h0 N P Q₀ hN hP hQ₀
  obtain ⟨σ₂, hσ₂⟩ := h0 N P' Q₀ hN hP' hQ₀
  obtain ⟨τ₁, hτ₁⟩ := hτ _ hσ₁ ((addOrderOf_galPt σ₁ P).trans hP)
  obtain ⟨τ₂, hτ₂⟩ := hτ _ hσ₂ ((addOrderOf_galPt σ₂ P').trans hP')
  rw [xCoord_galPt] at hτ₁ hτ₂
  -- `P ↦σ₁ A`, `Q₀ ↦τ₁ A`, `Q₀ ↦τ₂ B`, `P' ↦σ₂ B` on `x`-coordinates
  refine ⟨σ₁.trans (τ₁.symm.trans (τ₂.trans σ₂.symm)), ?_⟩
  simp only [AlgEquiv.trans_apply]
  rw [← hτ₁, AlgEquiv.symm_apply_apply, hτ₂, AlgEquiv.symm_apply_apply]

/-- **`X₀(N)`-transitivity is a consequence of Igusa transitivity.** -/
theorem x0Transitive_of_igusaTransitive (h : IgusaTransitive) : X0Transitive := by
  intro N P P' hN hP hP'
  obtain ⟨σ, hσ⟩ := h N P P' hN hP hP'
  refine ⟨σ, ?_⟩
  have hA : addOrderOf (galPt σ P) = N := (addOrderOf_galPt σ P).trans hP
  by_cases h1 : N = 1
  · subst h1
    rw [AddMonoid.addOrderOf_eq_one_iff] at hA
    rw [hA]; exact zero_mem _
  · have hne : ∀ R : EjBar.toAffine.Point, addOrderOf R = N → R ≠ 0 := by
      intro R hR h0
      rw [h0, addOrderOf_zero] at hR
      exact h1 hR.symm
    have hx : xCoord (galPt σ P) = xCoord P' := by rw [xCoord_galPt]; exact hσ
    rcases eq_or_eq_neg_of_xCoord_eq (hne _ hA) (hne _ hP') hx with he | he
    · rw [he]; exact AddSubgroup.mem_zmultiples P'
    · rw [he]; exact neg_mem (AddSubgroup.mem_zmultiples P')

/-- **The cusp statement is a consequence of Igusa transitivity** (any `Q₀` of order `N`). -/
theorem tateMuN_of_igusaTransitive (h : IgusaTransitive) : TateMuN := by
  intro N hN
  obtain ⟨e⟩ := t36_torsionStructure Kbar EjBar N hN
  obtain ⟨Q₀, hQ₀⟩ := exists_addOrderOf Kbar EjBar N e
  exact ⟨Q₀, hQ₀, fun R _ hR => h N Q₀ R hN hQ₀ hR⟩

/-- **Igusa transitivity splits into `X₀(N)`-transitivity and the cusp `μ_N`.** -/
theorem igusaTransitive_iff : IgusaTransitive ↔ X0Transitive ∧ TateMuN :=
  ⟨fun h => ⟨x0Transitive_of_igusaTransitive h, tateMuN_of_igusaTransitive h⟩,
    fun h => igusaTransitive_of_x0_tateMuN h.1 h.2⟩

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.igusaTransitive_of_x0_tateMuN
#print axioms ZInQ.RLeaf.x0Transitive_of_igusaTransitive
#print axioms ZInQ.RLeaf.tateMuN_of_igusaTransitive
#print axioms ZInQ.RLeaf.igusaTransitive_iff

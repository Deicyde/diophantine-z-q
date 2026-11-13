import ZInQKernel.Contrib.RLeaf.X1ConstantField

/-!
# rleaf-elliptic: the leaf T40 reduced to Igusa's theorem and one Tate-curve cusp

`X1Belyi.X1RationalCusp` (leaf T40: for every point `P` of exact order `N` on `E_j` over
`\overline{ℚ(j)}`, `K_N = ℚ(j)(x(P))` has a place of degree 1 over `ℚ`) follows from two named
statements:

* `IgusaTransitive`: the `x`-coordinates of the points of exact order `N` form one orbit under
  `Gal(\overline{ℚ(j)}/ℚ(j))`. This is a consequence of Igusa's theorem (Igusa, *Fibre systems of
  Jacobian varieties III*, Amer. J. Math. 81 (1959): the Galois group of `ℚ(j)(E_j[N])` over
  `ℚ(j)` is `GL₂(ℤ/N)` up to `±1`, whose subgroup `SL₂(ℤ/N)` acts transitively on the vectors of
  exact order `N`; also Lang, *Elliptic functions*, Ch. 6, Shimura 1971 §6.1; numbers UNVERIFIED).
* `TateCuspLaurent`: for each `N` some point `P₀` of exact order `N` has a `ℚ`-embedding
  `K_N(P₀) → ℚ((t))` under which `j` is not a power series. This is the Tate curve at `j = ∞`
  (Silverman, *Advanced topics*, V.3-V.5, UNVERIFIED numbers): over `ℚ((q))`, `E_j ≅ E_q` because
  `E₄/E₆ ∈ 1 + qℚ[[q]]` is a square, `j = 1/q + 744 + ⋯`, and the point `u = q^{1/N}` of
  `E_q(ℚ((q^{1/N})))` has exact order `N` and `x(u) ∈ ℚ((t))`, `t = q^{1/N}`.

Proved here: `hasRationalPlace_of_laurent` (a `ℚ`-embedding into `ℚ((t))` that sends some element
outside `ℚ[[t]]` gives a degree-one place: the pullback of `ℚ[[t]]`),
`hasRationalPlace_of_algEquiv` (transport along `ℚ(j)`-isomorphisms),
`x1RationalCusp_of_igusa_tateCusp : IgusaTransitive → TateCusp → X1RationalCusp`, and the same
with `TateCuspLaurent`. Combined with `X1ConstantField.lean`, T39 and T40 both follow from
`IgusaTransitive` and `TateCuspLaurent`.
-/

namespace ZInQ.RLeaf

open Polynomial LeafModCurves

/-! ## Transport of degree-one places -/

/-- Membership in the nonunits of a pulled-back valuation subring. -/
theorem mem_nonunits_comap_iff {F F' : Type*} [Field F] [Field F'] (f : F →+* F')
    (w : ValuationSubring F') (x : F) : x ∈ (w.comap f).nonunits ↔ f x ∈ w.nonunits := by
  have key : ∀ (A : ValuationSubring F) (a : F), a ∈ A.nonunits ↔ a = 0 ∨ a⁻¹ ∉ A := by
    intro A a
    have := A.inv_mem_nonunits_iff (x := a⁻¹)
    rwa [inv_inv, inv_eq_zero] at this
  have key' : ∀ (A : ValuationSubring F') (a : F'), a ∈ A.nonunits ↔ a = 0 ∨ a⁻¹ ∉ A := by
    intro A a
    have := A.inv_mem_nonunits_iff (x := a⁻¹)
    rwa [inv_inv, inv_eq_zero] at this
  rw [key, key', ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

/-- **Degree-one places transport along `ℚ(j)`-isomorphisms.** -/
theorem hasRationalPlace_of_algEquiv {F F' : Type} [Field F] [Field F'] [Algebra Qj F]
    [Algebra Qj F'] (e : F ≃ₐ[Qj] F') (h : X1Belyi.HasRationalPlace F) :
    X1Belyi.HasRationalPlace F' := by
  obtain ⟨w, hne, hQ, hres⟩ := h
  have hrat : ∀ c : ℚ, (e.symm : F' →+* F) (X1Belyi.ratHom F' c) = X1Belyi.ratHom F c := by
    intro c
    simp only [X1Belyi.ratHom, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
      AlgEquiv.commutes]
  refine ⟨w.comap (e.symm : F' →+* F), ?_, fun c => ?_, fun x hx => ?_⟩
  · intro htop
    apply hne
    rw [eq_top_iff]
    intro y _
    have hy : e y ∈ w.comap (e.symm : F' →+* F) := by rw [htop]; trivial
    rw [ValuationSubring.mem_comap] at hy
    simpa using hy
  · rw [ValuationSubring.mem_comap, hrat]; exact hQ c
  · obtain ⟨c, hc⟩ := hres _ hx
    refine ⟨c, ?_⟩
    rw [mem_nonunits_comap_iff, map_sub, hrat]
    exact hc

/-! ## A `ℚ`-embedding into `ℚ((t))` gives a degree-one place -/

/-- `ℚ[[t]]` as a valuation subring of `ℚ((t))`. -/
noncomputable def powerSeriesVS : ValuationSubring (LaurentSeries ℚ) :=
  ValuationSubring.ofSubring (HahnSeries.ofPowerSeries ℤ ℚ).range fun x => by
    rcases ValuationRing.isInteger_or_isInteger (PowerSeries ℚ) x with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r, hr⟩
    · exact Or.inr ⟨r, hr⟩

theorem mem_powerSeriesVS {x : LaurentSeries ℚ} :
    x ∈ powerSeriesVS ↔ x ∈ Set.range (HahnSeries.ofPowerSeries ℤ ℚ) := Iff.rfl

/-- A power series with zero constant term has no power-series inverse. -/
theorem inv_not_mem_powerSeriesVS {p : PowerSeries ℚ} (hp0 : PowerSeries.constantCoeff p = 0)
    (hp : p ≠ 0) : (HahnSeries.ofPowerSeries ℤ ℚ p)⁻¹ ∉ powerSeriesVS := by
  rintro ⟨r, hr⟩
  have hne : HahnSeries.ofPowerSeries ℤ ℚ p ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective]
  have h1 : HahnSeries.ofPowerSeries ℤ ℚ (p * r) = 1 := by
    rw [map_mul, hr, mul_inv_cancel₀ hne]
  have h2 : p * r = 1 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ) (by rw [h1, map_one])
  have h3 := congrArg PowerSeries.constantCoeff h2
  rw [map_mul, hp0, zero_mul, map_one] at h3
  exact zero_ne_one h3

/-- **A `ℚ`-embedding `F → ℚ((t))` hitting a non-power-series gives a degree-one place.** -/
theorem hasRationalPlace_of_laurent (F : Type) [Field F] [Algebra Qj F]
    (ψ : F →+* LaurentSeries ℚ) (hψ : ∀ c : ℚ, ψ (X1Belyi.ratHom F c) = HahnSeries.C c)
    (z : F) (hz : ψ z ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)) :
    X1Belyi.HasRationalPlace F := by
  refine ⟨powerSeriesVS.comap ψ, fun htop => hz ?_, fun c => ?_, fun x hx => ?_⟩
  · have : z ∈ powerSeriesVS.comap ψ := by rw [htop]; trivial
    exact this
  · rw [ValuationSubring.mem_comap, hψ, mem_powerSeriesVS]
    exact ⟨PowerSeries.C c, HahnSeries.ofPowerSeries_C c⟩
  · obtain ⟨p, hp⟩ := (mem_powerSeriesVS).mp (ValuationSubring.mem_comap.mp hx)
    refine ⟨PowerSeries.constantCoeff p, ?_⟩
    rw [mem_nonunits_comap_iff, map_sub, hψ, ← hp, ← HahnSeries.ofPowerSeries_C, ← map_sub]
    set q := p - PowerSeries.C (PowerSeries.constantCoeff p)
    have hq0 : PowerSeries.constantCoeff q = 0 := by simp [q]
    have key := powerSeriesVS.inv_mem_nonunits_iff (x := (HahnSeries.ofPowerSeries ℤ ℚ q)⁻¹)
    rw [inv_inv, inv_eq_zero] at key
    rw [key]
    by_cases hq : q = 0
    · left; rw [hq, map_zero]
    · right; exact inv_not_mem_powerSeriesVS hq0 hq

/-! ## The reduction of T40 -/

/-- **Igusa transitivity** (consequence of Igusa 1959): the `x`-coordinates of the points of
exact order `N` on `E_j` form a single `Gal(\overline{ℚ(j)}/ℚ(j))`-orbit. -/
def IgusaTransitive : Prop :=
  ∀ (N : ℕ) (P P' : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → addOrderOf P' = N →
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, σ (xCoord P) = xCoord P'

/-- **One rational cusp for each level**: some point of exact order `N` has `K_N` with a place of
degree one. -/
def TateCusp : Prop :=
  ∀ N : ℕ, 0 < N → ∃ P : EjBar.toAffine.Point, addOrderOf P = N ∧
    X1Belyi.HasRationalPlace (fieldX1 P)

/-- **The Tate curve at `j = ∞`, embedding form**: for each `N`, some point `P₀` of exact order
`N` admits a `ℚ`-embedding `K_N(P₀) → ℚ((t))` under which `j` is not a power series
(`t = q^{1/N}`, `P₀ = q^{1/N}` on the Tate curve). -/
def TateCuspLaurent : Prop :=
  ∀ N : ℕ, 0 < N → ∃ (P : EjBar.toAffine.Point) (ψ : fieldX1 P →+* LaurentSeries ℚ),
    addOrderOf P = N ∧ (∀ c : ℚ, ψ (X1Belyi.ratHom (fieldX1 P) c) = HahnSeries.C c) ∧
    ψ (algebraMap Qj (fieldX1 P) RatFunc.X) ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)

theorem tateCusp_of_laurent (h : TateCuspLaurent) : TateCusp := fun N hN => by
  obtain ⟨P, ψ, hP, hψ, hj⟩ := h N hN
  exact ⟨P, hP, hasRationalPlace_of_laurent _ ψ hψ _ hj⟩

/-- `K_N` depends only on the Galois orbit of `x(P)`. -/
noncomputable def fieldX1Equiv {P P' : EjBar.toAffine.Point} (σ : Kbar ≃ₐ[Qj] Kbar)
    (hσ : σ (xCoord P) = xCoord P') : fieldX1 P ≃ₐ[Qj] fieldX1 P' :=
  (IntermediateField.equivMap (fieldX1 P) (σ : Kbar →ₐ[Qj] Kbar)).trans
    (IntermediateField.equivOfEq (by
      rw [fieldX1, IntermediateField.adjoin_map, Set.image_singleton]
      simp only [AlgEquiv.coe_toAlgHom]
      rw [hσ]; rfl))

/-- **T40 from Igusa transitivity and one rational cusp.** -/
theorem x1RationalCusp_of_igusa_tateCusp (hI : IgusaTransitive) (hT : TateCusp) :
    X1Belyi.X1RationalCusp := by
  intro N P hN hP
  obtain ⟨P₀, hP₀, hplace⟩ := hT N hN
  obtain ⟨σ, hσ⟩ := hI N P₀ P hN hP₀ hP
  exact hasRationalPlace_of_algEquiv (fieldX1Equiv σ hσ) hplace

/-- **T40 from Igusa transitivity and the Tate curve.** -/
theorem x1RationalCusp_of_igusa_tate (hI : IgusaTransitive) (hT : TateCuspLaurent) :
    X1Belyi.X1RationalCusp :=
  x1RationalCusp_of_igusa_tateCusp hI (tateCusp_of_laurent hT)

/-- **T39 from Igusa transitivity and the Tate curve.** -/
theorem x1ConstantField_of_igusa_tate (hI : IgusaTransitive) (hT : TateCuspLaurent) :
    X1Belyi.X1ConstantField :=
  x1ConstantField_of_x1RationalCusp (x1RationalCusp_of_igusa_tate hI hT)

/-- `X1ModelExists` from T38, Igusa transitivity and the Tate curve. -/
theorem x1ModelExists_of_t38_igusa_tate (hC : X1Belyi.CurveOfFunctionFieldQ)
    (hI : IgusaTransitive) (hT : TateCuspLaurent) : LeafModCurves.X1ModelExists :=
  x1ModelExists_of_t38_t40 hC (x1RationalCusp_of_igusa_tate hI hT)

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.hasRationalPlace_of_algEquiv
#print axioms ZInQ.RLeaf.hasRationalPlace_of_laurent
#print axioms ZInQ.RLeaf.x1RationalCusp_of_igusa_tateCusp
#print axioms ZInQ.RLeaf.x1RationalCusp_of_igusa_tate
#print axioms ZInQ.RLeaf.x1ConstantField_of_igusa_tate
#print axioms ZInQ.RLeaf.x1ModelExists_of_t38_igusa_tate

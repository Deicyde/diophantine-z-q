import ZInQKernel.Contrib.RLeaf.IgusaX0
import Mathlib.RingTheory.LaurentSeries

/-!
# t40-igusa: the cusp `μ_N` from any algebraically closed extension of `ℚ(j)`

`ZInQ.RLeaf.TateMuN` asks, over `\overline{ℚ(j)}`, for a point `Q₀` of exact order `N` on `E_j`
whose generators are Galois-conjugate on `x`-coordinates. Its source is local: the Tate curve over
the completion `ℚ((1/j))` of `ℚ(j)` at `j = ∞`. This file shows that the statement may be checked
over any algebraically closed field `Ω` containing `ℚ(j)` (`tateMuN_of_over`): the `N`-torsion of
`E_j(Ω)` is the image of that of `E_j(\overline{ℚ(j)})` (both have `N²` points, leaf T36), and
automorphisms of `Ω` over `ℚ(j)` restrict to the normal subextension `\overline{ℚ(j)}`.

The named leaf `TateMuNLocal` is the statement over `Ω = \overline{ℚ((t))}`, with `ℚ(j)`
embedded by `j ↦ t⁻¹` (`jInvLaurent`), i.e. over the algebraic closure of the completion at
`j = ∞`, where the Tate curve lives.

Proved: `jInv_X`, `jInvLaurent_X`, `tateMuNAt_kbar`, `tateMuN_of_over`, `tateMuN_of_at`, `tateMuN_of_local : TateMuNLocal → TateMuN`,
`igusaTransitive_of_x0_tateMuNLocal : X0Transitive → TateMuNLocal → IgusaTransitive`.
-/

namespace ZInQ.RLeaf

open LeafModCurves WeierstrassCurve X1Belyi

/-! ## Transport from an algebraically closed extension -/

section Over

variable (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra Qj Ω] [DecidableEq Ω]

/-- The cusp statement `TateMuN` over an algebraically closed extension `Ω` of `ℚ(j)`: for each
`N > 0` some point `Q₀ ∈ E_j(Ω)` of exact order `N` has all generators of `⟨Q₀⟩` conjugate to
`Q₀` on `x`-coordinates under `Aut(Ω/ℚ(j))`. -/
def TateMuNOver : Prop :=
  ∀ N : ℕ, 0 < N → ∃ Q₀ : (Ej.baseChange Ω).toAffine.Point, addOrderOf Q₀ = N ∧
    ∀ R ∈ AddSubgroup.zmultiples Q₀, addOrderOf R = N →
      ∃ τ : Ω ≃ₐ[Qj] Ω, τ (xCoord Q₀) = xCoord R

/-- The cusp statement at one level `N`, over an extension `Ω` of `ℚ(j)`. -/
def TateMuNAt (N : ℕ) (Ω : Type) [Field Ω] [Algebra Qj Ω] [DecidableEq Ω] : Prop :=
  ∃ Q₀ : (Ej.baseChange Ω).toAffine.Point, addOrderOf Q₀ = N ∧
    ∀ R ∈ AddSubgroup.zmultiples Q₀, addOrderOf R = N →
      ∃ τ : Ω ≃ₐ[Qj] Ω, τ (xCoord Q₀) = xCoord R

omit [IsAlgClosed Ω] in
theorem tateMuNOver_iff : TateMuNOver Ω ↔ ∀ N : ℕ, 0 < N → TateMuNAt N Ω := Iff.rfl

omit [IsAlgClosed Ω] in
/-- `x(f P) = f(x(P))` for the point map along `f : Kbar →ₐ[ℚ(j)] Ω`. -/
theorem xCoord_map_alg (f : Kbar →ₐ[Qj] Ω) (P : EjBar.toAffine.Point) :
    xCoord (WeierstrassCurve.Affine.Point.map (W' := Ej) f P) = f (xCoord P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some h => rfl

/-- **The `N`-torsion of `E_j(Ω)` comes from `E_j(\overline{ℚ(j)})`.** -/
theorem exists_map_eq_of_nsmul_eq_zero (f : Kbar →ₐ[Qj] Ω) {N : ℕ} (hN : 0 < N)
    (P : (Ej.baseChange Ω).toAffine.Point) (hP : N • P = 0) :
    ∃ P' : EjBar.toAffine.Point, WeierstrassCurve.Affine.Point.map (W' := Ej) f P' = P := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Qj Ω).injective
  have : NeZero N := ⟨hN.ne'⟩
  let m := WeierstrassCurve.Affine.Point.map (W' := Ej) f
  have hm : Function.Injective m := WeierstrassCurve.Affine.Point.map_injective (W' := Ej) f
  obtain ⟨e₁⟩ := t36_torsionStructure Kbar EjBar N hN
  obtain ⟨e₂⟩ := t36_torsionStructure Ω (Ej.baseChange Ω) N hN
  have : Finite (nTors (Ej.baseChange Ω) N) := Finite.of_equiv _ e₂.symm.toEquiv
  let g : nTors EjBar N → nTors (Ej.baseChange Ω) N := fun Q =>
    ⟨m Q.1, by
      show N • m Q.1 = 0
      have hq : N • Q.1 = 0 := Q.2
      exact (map_nsmul m N Q.1).symm.trans ((congrArg m hq).trans (map_zero m))⟩
  have hg : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (hm (congrArg Subtype.val hab))
  have hcard : Nat.card (nTors (Ej.baseChange Ω) N) ≤ Nat.card (nTors EjBar N) := by
    rw [nTors_card _ _ N hN e₁, nTors_card _ _ N hN e₂]
  obtain ⟨Q, hQ⟩ := (hg.bijective_of_nat_card_le hcard).2 ⟨P, hP⟩
  exact ⟨Q.1, congrArg Subtype.val hQ⟩

omit [IsAlgClosed Ω] [DecidableEq Ω] in
/-- **Automorphisms of `Ω` over `ℚ(j)` restrict to `\overline{ℚ(j)}`** (a normal extension). -/
theorem exists_restrict (f : Kbar →ₐ[Qj] Ω) (τ : Ω ≃ₐ[Qj] Ω) :
    ∃ τ' : Kbar ≃ₐ[Qj] Kbar, ∀ a, f (τ' a) = τ (f a) := by
  let : Algebra Kbar Ω := f.toRingHom.toAlgebra
  have : IsScalarTower Qj Kbar Ω := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  exact ⟨τ.restrictNormal Kbar, fun a => τ.restrictNormal_commutes Kbar a⟩

/-- **The cusp statement at level `N` transfers from `Ω` to `\overline{ℚ(j)}`.** -/
theorem tateMuNAt_kbar {N : ℕ} (hN : 0 < N) (h : TateMuNAt N Ω) : TateMuNAt N Kbar := by
  obtain ⟨Q, hQ, hτ⟩ := h
  let f : Kbar →ₐ[Qj] Ω := IsAlgClosed.lift
  let m := WeierstrassCurve.Affine.Point.map (W' := Ej) f
  have hm : Function.Injective m := WeierstrassCurve.Affine.Point.map_injective (W' := Ej) f
  have hQN : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  obtain ⟨Q', rfl⟩ := exists_map_eq_of_nsmul_eq_zero Ω f hN Q hQN
  have hQ' : addOrderOf Q' = N := (addOrderOf_injective m hm Q').symm.trans hQ
  refine ⟨Q', hQ', fun R hR hRN => ?_⟩
  have hmR : m R ∈ AddSubgroup.zmultiples (m Q') := by
    obtain ⟨k, rfl⟩ := hR
    exact ⟨k, (map_zsmul m k Q').symm⟩
  obtain ⟨τ, hτR⟩ := hτ (m R) hmR ((addOrderOf_injective m hm R).trans hRN)
  obtain ⟨τ', hτ'⟩ := exists_restrict Ω f τ
  refine ⟨τ', f.injective ?_⟩
  show f (τ' (xCoord Q')) = f (xCoord R)
  rw [hτ', ← xCoord_map_alg, hτR]
  exact xCoord_map_alg Ω f R

/-- **`TateMuN` may be checked over any algebraically closed extension of `ℚ(j)`.** -/
theorem tateMuN_of_over (h : TateMuNOver Ω) : TateMuN := fun N hN =>
  tateMuNAt_kbar Ω hN (h N hN)

end Over

/-- **`TateMuN` may be checked level by level, over an algebraically closed extension of `ℚ(j)`
depending on the level.** -/
theorem tateMuN_of_at (h : ∀ N : ℕ, 0 < N → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
    (_ : Algebra Qj Ω) (_ : DecidableEq Ω), TateMuNAt N Ω) : TateMuN := by
  intro N hN
  obtain ⟨Ω, _, _, _, _, hΩ⟩ := h N hN
  exact tateMuNAt_kbar Ω hN hΩ

/-! ## The completion at `j = ∞` -/

open scoped RatFunc

/-- `j` is transcendental over `ℚ` in `ℚ(j)`. -/
theorem transcendental_X : Transcendental ℚ (RatFunc.X : Qj) := by
  have hne : ¬∃ c : ℚ, (RatFunc.X : Qj) = RatFunc.C c := by
    rintro ⟨c, hc⟩
    have := congrArg RatFunc.intDegree hc
    rw [RatFunc.intDegree_X (K := ℚ), RatFunc.intDegree_C] at this
    exact one_ne_zero this
  have h := RatFunc.transcendental_of_ne_C (K := ℚ) (f := RatFunc.X) hne
  convert h
  exact Subsingleton.elim _ _

/-- `1/j` is transcendental over `ℚ`. -/
theorem transcendental_X_inv : Transcendental ℚ (RatFunc.X⁻¹ : Qj) := fun h =>
  transcendental_X (IsAlgebraic.inv_iff.mp h)

/-- Nonzero polynomials stay nonzero at `1/j`. -/
theorem aeval_X_inv_nonZeroDivisors :
    nonZeroDivisors (Polynomial ℚ) ≤
      (nonZeroDivisors Qj).comap (Polynomial.aeval (RatFunc.X⁻¹ : Qj)).toRingHom := fun p hp => by
  rw [Submonoid.mem_comap]
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => transcendental_X_inv ⟨p, ?_, h0⟩
  exact nonZeroDivisors.ne_zero hp

/-- The ring endomorphism `j ↦ 1/j` of `ℚ(j)`. -/
noncomputable def jInv : Qj →+* Qj :=
  RatFunc.liftRingHom (Polynomial.aeval (RatFunc.X⁻¹ : Qj)).toRingHom aeval_X_inv_nonZeroDivisors

theorem jInv_X : jInv RatFunc.X = RatFunc.X⁻¹ := by
  have h := RatFunc.liftRingHom_apply_div (Polynomial.aeval (RatFunc.X⁻¹ : Qj)).toRingHom
    aeval_X_inv_nonZeroDivisors Polynomial.X 1
  simp only [map_one, div_one, RatFunc.algebraMap_X, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Polynomial.aeval_X] at h
  exact h

/-- **`ℚ(j)` inside its completion at `j = ∞`**: `ℚ(j) → ℚ((t))`, `j ↦ t⁻¹`. -/
noncomputable def jInvLaurent : Qj →+* LaurentSeries ℚ :=
  (algebraMap Qj (LaurentSeries ℚ)).comp jInv

theorem jInvLaurent_X : jInvLaurent RatFunc.X = (HahnSeries.single 1 1 : LaurentSeries ℚ)⁻¹ := by
  rw [jInvLaurent, RingHom.comp_apply, jInv_X, map_inv₀]
  exact congrArg _ RatFunc.coe_X

/-- `\overline{ℚ((t))}`, as an extension of `ℚ(j)` through `j ↦ t⁻¹` (a type synonym, so that
Mathlib's `ℚ(j) → ℚ((t))`, `j ↦ t`, is not used). -/
def TateOmega : Type := AlgebraicClosure (LaurentSeries ℚ)

noncomputable instance : Field TateOmega := inferInstanceAs (Field (AlgebraicClosure _))

instance : IsAlgClosed TateOmega := inferInstanceAs (IsAlgClosed (AlgebraicClosure _))

noncomputable instance : DecidableEq TateOmega := Classical.decEq _

noncomputable instance : Algebra Qj TateOmega :=
  ((algebraMap (LaurentSeries ℚ) (AlgebraicClosure (LaurentSeries ℚ))).comp jInvLaurent).toAlgebra

/-- **The cusp `μ_N` of the Tate curve, local form** (published). Over `Ω = \overline{ℚ((t))}`,
with `ℚ(j) ⊆ ℚ((t))` by `j ↦ t⁻¹` (the completion at `j = ∞`): for each `N > 0` there is a point
`Q₀ ∈ E_j(Ω)` of exact order `N` such that for every generator `R` of `⟨Q₀⟩` some
`τ ∈ Aut(Ω/ℚ(j))` sends `x(Q₀)` to `x(R)`.

Source: Tate's uniformization (Silverman, *Advanced topics in the arithmetic of elliptic curves*,
Ch. V, Thm 3.1 (`E_q(L) ≅ L^×/q^ℤ`, Galois-equivariant) and Thm 5.3 (`E` with `|j| > 1` is a
quadratic twist of `E_q`); Tate, *A review of non-archimedean elliptic functions*, 1995; numbers
UNVERIFIED). Here `ℚ((t)) = ℚ((q))` with `t = 1/j = q - 744 q² + ⋯`; take `Q₀` the image of a
primitive `N`-th root of unity `ζ_N`; the generators of `⟨Q₀⟩` are the images of `ζ_N^c`,
`c ∈ (ℤ/N)^×`, and `τ` extends `ζ_N ↦ ζ_N^c` from `Gal(ℚ((t))(ζ_N)/ℚ((t))) ≅ (ℤ/N)^×` (the
quadratic twist changes the action by `±1`, invisible on `x`). The `τ` provided are even
`ℚ((t))`-linear. -/
def TateMuNLocal : Prop := TateMuNOver TateOmega

/-- **The global cusp statement from the local one.** -/
theorem tateMuN_of_local (h : TateMuNLocal) : TateMuN := tateMuN_of_over TateOmega h

/-- **Igusa transitivity from `X₀(N)`-transitivity and the Tate curve at `j = ∞`.** -/
theorem igusaTransitive_of_x0_tateMuNLocal (h0 : X0Transitive) (hT : TateMuNLocal) :
    IgusaTransitive :=
  igusaTransitive_of_x0_tateMuN h0 (tateMuN_of_local hT)

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.tateMuN_of_over
#print axioms ZInQ.RLeaf.tateMuN_of_at
#print axioms ZInQ.RLeaf.jInvLaurent_X
#print axioms ZInQ.RLeaf.tateMuN_of_local
#print axioms ZInQ.RLeaf.igusaTransitive_of_x0_tateMuNLocal

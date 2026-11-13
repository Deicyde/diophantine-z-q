import Mathlib

/-!
# bp-modcurves, nodes MC1, MC3a, MC4 (definitions and open statements)

These definitions compile against Mathlib v4.35. The `Prop`s at the end are **open
statements**: targets for the crowd, or leaves where marked. Nothing here is assumed by
another file.

* `Ej` : the elliptic curve over `ℚ(j) = RatFunc ℚ` with `j`-invariant `j`: Mathlib's
  `WeierstrassCurve.ofJNe0Or1728 X` (`y² + xy = x³ − 36/(j−1728)·x − 1/(j−1728)`).
* `fieldX1 P = ℚ(j)(x(P)) ⊆ \overline{ℚ(j)}` for a point `P` of `Ej` over the algebraic closure.
  For `P` of exact order `N ≥ 3` this is the function field of `X₁(N)` over `ℚ` (STANDARD; §4 of
  `docs/research/bp-modcurves.md`).
* `Y1j P` : Mathlib's relative normalization of the `j`-line `Spec ℚ[j]` in `fieldX1 P`, i.e.
  `X₁(N)` minus its cusps. The proper `X₁(N)` is obtained the same way over `ℙ¹`. Mathlib has no
  `ℙ¹` scheme by name, so one uses the two charts `Spec ℚ[j]`, `Spec ℚ[1/j]` or `Proj`.
-/

namespace BPModCurves

open WeierstrassCurve AlgebraicGeometry

/-- The function field `ℚ(j)` of the `j`-line. -/
abbrev Qj := RatFunc ℚ

/-- The elliptic curve over `ℚ(j)` with `j`-invariant `j`. -/
noncomputable def Ej : WeierstrassCurve Qj := ofJNe0Or1728 (RatFunc.X : Qj)

theorem X_sub_1728_ne_zero : (RatFunc.X : Qj) - 1728 ≠ 0 := by
  intro h
  have h' : (algebraMap (Polynomial ℚ) Qj) (Polynomial.X - Polynomial.C 1728) = 0 := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    simpa using h
  rw [map_eq_zero_iff _ (IsFractionRing.injective (Polynomial ℚ) Qj)] at h'
  exact Polynomial.X_sub_C_ne_zero 1728 h'

instance : Fact (IsUnit (RatFunc.X : Qj)) := ⟨isUnit_iff_ne_zero.2 RatFunc.X_ne_zero⟩
instance : Fact (IsUnit ((RatFunc.X : Qj) - 1728)) := ⟨isUnit_iff_ne_zero.2 X_sub_1728_ne_zero⟩

instance : Ej.IsElliptic := by unfold Ej; infer_instance

/-- `j(E_j) = j`. -/
theorem Ej_j : Ej.j = RatFunc.X := by unfold Ej; exact ofJNe0Or1728_j _

/-- An algebraic closure of `ℚ(j)`. -/
abbrev Kbar := AlgebraicClosure Qj

noncomputable instance : DecidableEq Kbar := Classical.decEq _

/-- `E_j` over `\overline{ℚ(j)}`. -/
noncomputable def EjBar : WeierstrassCurve Kbar := Ej.baseChange Kbar

/-- The `x`-coordinate of an affine point (junk value `0` at the origin). -/
def xCoord {F : Type*} [Field F] {W : WeierstrassCurve F} : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x

/-- **`ℚ(X₁(N)) = ℚ(j)(x(P))`** for `P` of exact order `N`. -/
noncomputable def fieldX1 (P : EjBar.toAffine.Point) : IntermediateField Qj Kbar :=
  IntermediateField.adjoin Qj {xCoord P}

/-- The structure map `ℚ[j] → ℚ(j)(x(P))`. -/
noncomputable def jLineToField (P : EjBar.toAffine.Point) : Polynomial ℚ →+* fieldX1 P :=
  (algebraMap Qj (fieldX1 P)).comp (algebraMap (Polynomial ℚ) Qj)

/-- **`X₁(N)` minus the cusps**: the relative normalization of `Spec ℚ[j]` in `ℚ(j)(x(P))`. -/
noncomputable def Y1j (P : EjBar.toAffine.Point) : Scheme :=
  (Spec.map (CommRingCat.ofHom (jLineToField P))).normalization

/-- The `j`-map `Y₁(N) → 𝔸¹_j` (integral, by Mathlib's relative normalization). -/
noncomputable def jMap (P : EjBar.toAffine.Point) : Y1j P ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  (Spec.map (CommRingCat.ofHom (jLineToField P))).fromNormalization

/-! ### Open statements (targets; not proved) -/

/-- MC3a: `#E[N] ≤ N²` over an algebraically closed field of characteristic 0
(Silverman III.6.4, UNVERIFIED number). -/
def TorsionCardLe : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [DecidableEq F] (W : WeierstrassCurve F)
    [W.IsElliptic] (N : ℕ), 0 < N → Nat.card {P : W.toAffine.Point // N • P = 0} ≤ N ^ 2

/-- MC1: the degree bound used for the Belyi degree. -/
def FieldX1DegreeLe : Prop :=
  ∀ (N : ℕ), 3 ≤ N → ∀ P : EjBar.toAffine.Point, addOrderOf P = N →
    Module.finrank Qj (fieldX1 P) ≤ N ^ 2 / 2

/-- MC1' (leaf: Igusa; Shimura 1971 Thm 6.6, UNVERIFIED): the exact degree `J₂(N)/2`, i.e. the
`x`-coordinates of the points of exact order `N` form one Galois orbit over `ℚ(j)`. -/
def FieldX1Degree : Prop :=
  ∀ (N : ℕ), 3 ≤ N → ∀ P : EjBar.toAffine.Point, addOrderOf P = N →
    2 * Module.finrank Qj (fieldX1 P) =
      Nat.card {v : ZMod N × ZMod N // ∃ x y : ZMod N, x * v.1 + y * v.2 = 1}

end BPModCurves

#print axioms BPModCurves.Ej_j
#check @BPModCurves.Y1j
#check @BPModCurves.jMap

/-! rv-blueprints axiom audit (appended): every declaration added in this file. -/
open Lean Elab Command in
elab "#rv_audit_axioms" : command => do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (c, _) in env.constants.map₂.toList do
    if c.isInternal then continue
    n := n + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    let extra := axs.filter (fun a => !std.contains a)
    if extra.size > 0 then bad := bad.push (c, extra)
  logInfo m!"rv_audit: {n} declarations; non-standard axioms in {bad.size}: {bad.toList.take 20}"
#rv_audit_axioms

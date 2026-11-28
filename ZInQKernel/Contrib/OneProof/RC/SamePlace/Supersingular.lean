import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.PairIsomorphisms

/-! # The supersingular locus of the coarse special fibre (rc-same-place1, item 2)

For a field `K` (in use: algebraically closed of characteristic `ell`) a Weierstrass curve `E`
over `K` is **supersingular** when its `ell`-torsion is trivial, `E[ell](K) = {0}`, i.e.
`Submodule.torsionBy ℤ E(K) ell = ⊥` (the standard definition; Silverman, *The Arithmetic of
Elliptic Curves*, 1986, Thm. V.3.1(a), UNVERIFIED). The predicate is invariant under variable
changes (`isSupersingular_variableChange`, through the tree's point isomorphism
`Point.addEquivVariableChange`), so it descends to the pair classes `PairClasses K N` of the
pinned level model (`PairClasses.IsSupersingular`), and `ssPoint ell K N` is the subtype of
supersingular classes: the `Point` type of the moduli-side coarse fibre `X` of the same-place
lane (lead's ruling R2: `frobenius_sq` fails on ordinary points, and the Jetchev–Kane class
bijection reaches only the supersingular locus).

Provenance: the definition is the textbook one; its invariance and descent are on the spot (c). -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Manuscript.RC.SamePlace

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.ModelLevels

/-- Trivial `n`-torsion passes along an additive equivalence (one direction). -/
theorem torsionBy_eq_bot_of_addEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    (n : ℤ) (hG : Submodule.torsionBy ℤ G n = ⊥) : Submodule.torsionBy ℤ H n = ⊥ := by
  rw [Submodule.eq_bot_iff] at hG ⊢
  intro y hy
  rw [Submodule.mem_torsionBy_iff] at hy
  have hx : e.symm y ∈ Submodule.torsionBy ℤ G n := by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hy, map_zero]
  have := hG _ hx
  simpa using congrArg e this

/-- Trivial `n`-torsion transports along an additive equivalence. -/
theorem torsionBy_eq_bot_congr {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    (n : ℤ) : Submodule.torsionBy ℤ G n = ⊥ ↔ Submodule.torsionBy ℤ H n = ⊥ :=
  ⟨torsionBy_eq_bot_of_addEquiv e n, torsionBy_eq_bot_of_addEquiv e.symm n⟩

variable {K : Type} [Field K] [DecidableEq K]

/-- **Supersingularity** (standard definition): the `ell`-torsion of `E(K)` is trivial,
`E[ell](K) = {0}`. Intended for `K` algebraically closed of characteristic `ell`. -/
def IsSupersingular (ell : ℕ) (E : WeierstrassCurve K) [E.IsElliptic] : Prop :=
  Submodule.torsionBy ℤ E.toAffine.Point (ell : ℤ) = ⊥

theorem isSupersingular_iff (ell : ℕ) (E : WeierstrassCurve K) [E.IsElliptic] :
    IsSupersingular ell E ↔ ∀ P : E.toAffine.Point, (ell : ℤ) • P = 0 → P = 0 := by
  rw [IsSupersingular, Submodule.eq_bot_iff]
  simp only [Submodule.mem_torsionBy_iff]

/-- Supersingularity does not see the elliptic instance, and transports along equal curves. -/
theorem isSupersingular_congr (ell : ℕ) {E E' : WeierstrassCurve K} (h : E = E')
    [E.IsElliptic] [E'.IsElliptic] : IsSupersingular ell E ↔ IsSupersingular ell E' := by
  subst h
  exact Iff.rfl

/-- **Invariance under variable changes.** -/
theorem isSupersingular_variableChange (ell : ℕ) (E : WeierstrassCurve K) [E.IsElliptic]
    (v : VariableChange K) : IsSupersingular ell (v • E) ↔ IsSupersingular ell E :=
  torsionBy_eq_bot_congr (Point.addEquivVariableChange E v) _

/-- Supersingularity of the source curve of an enhanced curve. -/
def EnhancedCurve.IsSupersingular {N : ℕ} (ell : ℕ) (A : EnhancedCurve K N) : Prop :=
  letI := A.elliptic
  SamePlace.IsSupersingular ell A.equation

/-- **The supersingularity predicate on pair classes**, well defined by
`isSupersingular_variableChange`. -/
def PairClasses.IsSupersingular {N : ℕ} (ell : ℕ) : PairClasses K N → Prop :=
  Quot.lift (EnhancedCurve.IsSupersingular ell) (by
    intro A B hAB
    obtain ⟨v, h, -⟩ := hAB
    letI := A.elliptic
    letI := B.elliptic
    exact propext (((isSupersingular_variableChange ell A.equation v).symm).trans
      (isSupersingular_congr ell h)))

@[simp] theorem PairClasses.isSupersingular_mk {N : ℕ} (ell : ℕ) (A : EnhancedCurve K N) :
    PairClasses.IsSupersingular ell (Quot.mk _ A : PairClasses K N) ↔
      (letI := A.elliptic; SamePlace.IsSupersingular ell A.equation) :=
  Iff.rfl

variable (K) in
/-- **The supersingular pair classes**: the `Point` type of the moduli-side coarse fibre `X`
(with `X.ss = univ`). Built from the pinned model's actual pair classes `PairClasses K N`
(classes of elliptic curves with a cyclic subgroup of order `N` up to variable changes). -/
def ssPoint (ell N : ℕ) : Type :=
  {x : PairClasses K N // PairClasses.IsSupersingular ell x}

end ZInQ.Manuscript.RC.SamePlace

#print axioms ZInQ.Manuscript.RC.SamePlace.torsionBy_eq_bot_congr
#print axioms ZInQ.Manuscript.RC.SamePlace.isSupersingular_variableChange
#print axioms ZInQ.Manuscript.RC.SamePlace.PairClasses.IsSupersingular
#print axioms ZInQ.Manuscript.RC.SamePlace.ssPoint

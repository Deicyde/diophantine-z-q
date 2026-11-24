import ZInQKernel.Contrib.CloudR2CM.SerreTate.SerreRigidity

/-!
# P3: from inertia trivial on `T_ℓ` to good reduction, through the Néron–Ogg–Shafarevich converse

Statements only; they supply no proofs.

The converse direction of the criterion of Néron–Ogg–Shafarevich (Serre–Tate, Ann. of Math. 88
(1968), Thm 1, (c) ⇒ (a); in the project `NOSProof.NOSConverseSep`) takes, over a field `K` with a
discrete valuation ring `O`, a separable closure `K_s` and a valuation ring `w` of `K_s` over `O`, an
abelian variety `A : Grp (Over (Spec K))` with `[IsAbelianVariety A]` and the hypothesis that
`{m | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}` is infinite, and concludes
`PkgI2.HasGoodReduction A O`.

* `P3ConverseInput` (the type adapter), over a NUMBER FIELD `K`: for `A : PkgI3.AbVar K` (the type of
  the base change of a `ZInQ.DefFaltings.AbVar`, which is `PkgI3.AbVar` by definition), viewed as
  `ObjBridge.toGrp A : Grp (Over (Spec K))`, and `Ω = K_s = AlgebraicClosure K`: if inertia at `w`
  acts trivially on `T_ℓ(A)` for one prime `ℓ` invertible in `O` (`InertiaTrivialOnTate`), the
  converse's hypothesis set is infinite (it contains every `ℓⁿ`, `n ≥ 1`).
  The step "every point of `A(Ω)[ℓⁿ]` is the `n`-th coordinate of an element of `T_ℓ(A)`" is a
  property of the actual abelian-variety points, not of Tate modules of arbitrary groups (for
  `M = ℤ/ℓ` the projection `T_ℓ(M) = 0 → M[ℓ]` is not onto). Its supplier is the
  `ℓ`-divisibility of `A(Ω)`: multiplication by `ℓ` is finite and surjective,
  `ZInQ.Contrib.AbVarBC.mulIsogeny : ZInQ.Contrib.AbVarBC.G0FibreSimple.MulIsogeny`, whose statement
  is `∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
  PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)`, with points lifted along it over the
  algebraically closed `Ω` (`ZInQ.Contrib.AbVarBC.exists_lift_of_isFinite`). Because that supplier
  is stated in characteristic `0`, the field is restricted to number fields, the scope of the route
  (`L₁` a number field, `O` a discrete valuation ring of `L₁`), and the torsion lifting is used
  only there.
* `P3GoodReduction`: the same hypothesis gives `PkgI2.HasGoodReduction (ObjBridge.toGrp A) O`.
  Its proof is `P3ConverseInput` followed by the converse at `K_s = AlgebraicClosure K` (a
  separable closure: a number field is perfect). `NOSProof.NOSConverseSep` is a statement, not a
  proof: P3GoodReduction additionally needs a proof of the converse, supplied by the banked proof
  closure of the converse; that closure is a separate gate which this file does not establish.
* `GoodAtFinitePlaces`: `HasGoodReduction` at every discrete valuation ring of `K` with finite
  residue field (for a number field, every localization of `𝓞_K` at a maximal ideal). This is the
  output of P3 over all places and the input of P4.
-/

set_option autoImplicit false

noncomputable section

namespace HDec.CMSerreTate

/-- **P3, the adapter to the converse's input.** Over a number field `K`: if inertia at `w` acts
trivially on `T_ℓ(A)` for a prime `ℓ` invertible in `O`, then inertia fixes `A(K̄)[m]` for
infinitely many `m > 0` invertible in `O`, in the converse's own predicate
`PkgI2.InertiaTrivialOn`. -/
def P3ConverseInput : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      InertiaTrivialOnTate A w ℓ →
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧
        _root_.PkgI2.InertiaTrivialOn (_root_.ObjBridge.toGrp A) w m}.Infinite

/-- **P3, good reduction at one place.** Over a number field `K`, if inertia at `w` (over the
discrete valuation ring `O`) acts trivially on `T_ℓ(A)` for a prime `ℓ` invertible in `O`, then `A`
has good reduction at `O`. A proof needs `P3ConverseInput` and a proof of
`NOSProof.NOSConverseSep` (a separate gate). -/
def P3GoodReduction : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      InertiaTrivialOnTate A w ℓ →
      _root_.PkgI2.HasGoodReduction (_root_.ObjBridge.toGrp A) O

/-- Good reduction at every finite place: at every discrete valuation ring of `K` with finite
residue field. -/
def GoodAtFinitePlaces {K : Type} [Field K] (A : _root_.PkgI3.AbVar K) : Prop :=
  ∀ (O : ValuationSubring K) [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)],
    _root_.PkgI2.HasGoodReduction (_root_.ObjBridge.toGrp A) O

end HDec.CMSerreTate

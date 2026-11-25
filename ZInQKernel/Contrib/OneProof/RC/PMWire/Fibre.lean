import ZInQKernel.Contrib.OneProof.RC.PMWire.Cusps
import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Geometry

/-! A compatibility adapter for the old divisor interface (c).
Its formal symbols let that interface subtract zero and name the elliptic
translation. They are outside the supersingular locus and stand for no
points of the modular special fibre. Tex 8476–8492, 9336–9355. -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
open FreeAbelianGroup (of lift)
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open scoped WeierstrassCurve

set_option autoImplicit false
set_option maxHeartbeats 1350000
set_option synthInstance.maxHeartbeats 350000

namespace ZInQ.Manuscript.RC.PMWire

open PMGeometry (DivZero center)
open PMAdelic Stages

/-- Insert the actual coarse divisors without changing any multiplicities. -/
def embedDivisor (X : CoarseFibre) : FreeAbelianGroup X.Point →+
    FreeAbelianGroup (X.Point ⊕ Option ℕ) :=
  lift (of ∘ Sum.inl)

/-- Add formal symbols for zero and for the elliptic translations.
Only the old API reads their operator values, and only at the zero symbol. -/
abbrev adapter (X : CoarseFibre) : CoarseFibre where
  Point := X.Point ⊕ Option ℕ
  ss := fun x => match x with
    | .inl p => p ∈ X.ss
    | .inr _ => False
  T q := Sum.elim (fun x => embedDivisor X (X.T q x)) (fun a => (q + 1) • of (.inr a))
  W q := Sum.elim (Sum.inl ∘ X.W q) (fun _ => .inr (.some q))
  frobenius := Sum.map X.frobenius id

/-- The adapter has exactly the original supersingular locus. -/
def ssEquiv (X : CoarseFibre) : X.ss ≃ (adapter X).ss where
  toFun x := ⟨.inl x.val, x.property⟩
  invFun x := match x with
    | ⟨.inl p, hp⟩ => ⟨p, hp⟩
    | ⟨.inr _, hp⟩ => False.elim hp
  left_inv _ := rfl
  right_inv := by
    rintro ⟨p | a, hp⟩
    · rfl
    · exact False.elim hp

/-- Transport the existing class-set comparison along the inclusion of
actual points. -/
def adaptComparison {ell N : ℕ} [Fact ell.Prime] {h : ell % 4 = 3} {hN : 0 < N}
    {hcop : N.Coprime ell} {X : CoarseFibre} (J : JetchevKane ell h N hN hcop X) :
    JetchevKane ell h N hN hcop (adapter X) where
  classes := J.classes.trans (ssEquiv X)

/-- Transport the existing operator comparison along the inclusion of
actual points. All operators on the supersingular locus keep their values. -/
theorem adaptOperators {ell N : ℕ} [Fact ell.Prime] {h : ell % 4 = 3} {hN : 0 < N}
    {hcop : N.Coprime ell} {X : CoarseFibre} {J : JetchevKane ell h N hN hcop X}
    (O : OperatorComparison ell h N hN hcop X J) :
    OperatorComparison ell h N hN hcop (adapter X) (adaptComparison J) where
  hecke p hp hg z := by
    change embedDivisor X (X.T p (J.classes z).val) = _
    rw [O.hecke p hp hg z, map_multiset_sum, Multiset.map_map]
    congr 1
  atkin p hp he z := congrArg Sum.inl (O.atkin p hp he z)
  frobenius z := congrArg Sum.inl (O.frobenius z)

namespace GoodRow

variable {R : Type} [CommRing R] [Algebra R ℚ]
  {ell N : ℕ} [Fact ell.Prime] [NeZero N] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
  {Ebar : WeierstrassCurve (ZMod ell)} {X : CoarseFibre}
  {E₀ : WeierstrassCurve ℚ} [E₀.IsElliptic] {π : rationalSource N ⟶ ellipticTarget E₀}
  (G : GoodRow R ell N K Ebar X π)

abbrev extendedValue : (adapter X).Point → PM.ReducedPoints (K := K) Ebar :=
  Sum.elim G.value (Option.elim' 0 G.translation)

/-- The divisor quotient remains the linear extension of the point
reading of the Néron extension, restricted to degree zero. The only
extra summands are the reductions of the rational constants on the target. -/
def quotient : DivZero (adapter X).Point →+ PM.ReducedPoints (K := K) Ebar :=
  (lift G.extendedValue).comp (DivZero (adapter X).Point).subtype

theorem quotient_center :
    G.quotient.comp (center (Sum.inr none : (adapter X).Point)) = lift G.extendedValue := by
  apply FreeAbelianGroup.lift_ext
  intro x
  change lift G.extendedValue (of x -
    lift (fun _ : (adapter X).Point => (1 : ℤ)) (of x) • of (.inr none)) = _
  have hzero : lift G.extendedValue (of (Sum.inr none)) = 0 :=
    (FreeAbelianGroup.lift_apply_of _ _).trans rfl
  rw [map_sub, map_zsmul, hzero, smul_zero, sub_zero]

theorem quotient_center_apply (D : FreeAbelianGroup (adapter X).Point) :
    G.quotient (center (.inr none) D) = lift G.extendedValue D :=
  DFunLike.congr_fun G.quotient_center D

private theorem extend_embed :
    (lift G.extendedValue).comp (embedDivisor X) = lift G.value := by
  apply FreeAbelianGroup.lift_ext
  intro x
  rw [AddMonoidHom.comp_apply]
  change lift G.extendedValue (lift (of ∘ Sum.inl) (of x)) = lift G.value (of x)
  rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
  exact FreeAbelianGroup.lift_apply_of _ _

private theorem eval_hecke {q : ℕ} {x : X.Point} (T : G.HeckePacket q x) {c : ℤ}
    (hc : G.HeckeIdentity T c) :
    lift G.extendedValue (embedDivisor X (X.T q x) - (q + 1) • of (Sum.inr none)) =
      c • lift G.extendedValue (of (Sum.inl x)) := by
  have hzero : lift G.extendedValue (of (Sum.inr none)) = 0 :=
    (FreeAbelianGroup.lift_apply_of _ _).trans rfl
  rw [map_sub, map_nsmul, hzero, smul_zero, sub_zero, FreeAbelianGroup.lift_apply_of]
  have he := DFunLike.congr_fun G.extend_embed (X.T q x)
  change lift G.extendedValue (embedDivisor X (X.T q x)) = lift G.value (X.T q x) at he
  rw [he, T.divisor_eq, map_sum]
  simp only [FreeAbelianGroup.lift_apply_of]
  change (∑ j, G.value (T.neighbour j)) = c • G.value x
  exact G.hecke_values T hc

/-- The signed old interface is filled from the actual modular model.
The formal zero symbol is never evaluated on that model. -/
def specialFibre {f : HeckeRing.GL2.Newform N 2} {χ : f.χ = 1}
    {Lat : PeriodPair} {κ : ℂ}
    (P : FixedAtScale π f χ Lat κ) {w : ℕ → ℤˣ} (hw : AtkinPin.wNew f χ = w)
    {ap : ℕ → ℤ} (H : G.Relations ap) :
    AtkinSign.SpecialFibreAtSigns ell N K Ebar ap (adapter X) w where
  infinity := .inr none
  frobenius_sq := by
    rintro (x | a)
    · exact congrArg Sum.inl (G.frobenius_sq x)
    · rfl
  T_infinity _ _ _ := rfl
  frobenius_infinity := rfl
  J := DivZero (adapter X).Point
  jacobianGroup := inferInstanceAs (AddCommGroup (DivZero (adapter X).Point))
  divisorClass := AddMonoidHom.id _
  quotient := G.quotient
  hecke_quotient q hq hg x hx := by
    simp only [AddMonoidHom.id_apply]
    rcases x with x | a
    · change x ∈ X.ss at hx
      let T := H.hecke q hq hg x hx
      rw [G.quotient_center_apply, G.quotient_center_apply]
      exact G.eval_hecke T (H.eigen q hq hg x hx)
    · exact False.elim hx
  atkin_quotient q hq he x hx := by
    simp only [AddMonoidHom.id_apply]
    rcases x with x | a
    · rw [G.quotient_center_apply, G.quotient_center_apply, map_sub]
      simp only [FreeAbelianGroup.lift_apply_of]
      rw [← hw]
      exact (sub_eq_iff_eq_add).2 (G.atkin_value P q hq he x)
    · exact False.elim hx
  frobenius_quotient x hx := by
    simp only [AddMonoidHom.id_apply]
    rcases x with x | a
    · rw [G.quotient_center_apply, G.quotient_center_apply, map_sub]
      simp only [FreeAbelianGroup.lift_apply_of]
      exact (sub_zero _).trans (G.value_frob x)
    · exact False.elim hx

variable {hell : ell % 4 = 3} {hN : 0 < N} {hcop : N.Coprime ell}
  (J : JetchevKane ell hell N hN hcop X)
  (O : OperatorComparison ell hell N hN hcop X J)
  {f : HeckeRing.GL2.Newform N 2} {χ : f.χ = 1}
  {Lat : PeriodPair} {κ : ℂ}
  (P : FixedAtScale π f χ Lat κ) {w : ℕ → ℤˣ} (hw : AtkinPin.wNew f χ = w)
    {ap : ℕ → ℤ} (H : G.Relations ap)

theorem specialize_eq_value (x : X.Point) :
    (geometricInput (adaptComparison J) (adaptOperators O) (G.specialFibre P hw H).toSpecialFibre).specialize (.inl x)
      = G.value x := by
  change G.quotient (center (.inr none) (of (.inl x))) = G.value x
  rw [G.quotient_center_apply, FreeAbelianGroup.lift_apply_of]
  rfl

theorem cusp_eq_translation (q : ℕ) :
    (geometry (adaptComparison J) (adaptOperators O) (G.specialFibre P hw H).toSpecialFibre).cusp q = G.translation q := by
  change G.quotient (center (.inr none) (of (.inr (.some q)))) = G.translation q
  rw [G.quotient_center_apply, FreeAbelianGroup.lift_apply_of]
  rfl

end GoodRow


end ZInQ.Manuscript.RC.PMWire

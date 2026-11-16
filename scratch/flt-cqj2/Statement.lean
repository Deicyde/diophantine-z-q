import ZInQKernel.Contrib.OneProof.ModularEquationGeneric

/-! flt-cqj2: the statements, copied verbatim, checked against the constants by `Iff.rfl`. -/

open LeafModCurves WeierstrassCurve Polynomial

/-- Verbatim copy of `ZInQ.Contrib.CloudB2X0Transitive.CyclicQuotientJBijOn` (Bridge.lean:61). -/
def CyclicQuotientJBijOnCopy : Prop :=
  ∀ (K : Type) [Field K] (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (L : Type) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra K L]
    (_ : (N : L) ≠ 0) (E : WeierstrassCurve L) [E.IsElliptic] (_ : Transcendental K E.j),
    Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H N)
      {H | IsAddCyclic H ∧ Nat.card H = N}
      {y | (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j)).IsRoot y}

example : ZInQ.Contrib.CloudB2X0Transitive.CyclicQuotientJBijOn ↔ CyclicQuotientJBijOnCopy := Iff.rfl

/-- Verbatim copy of `ZInQ.RLeaf.X0Transitive` (ZInQKernel/Contrib/RLeaf/IgusaX0.lean:69). -/
def X0TransitiveCopy : Prop :=
  ∀ (N : ℕ) (P P' : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → addOrderOf P' = N →
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, ZInQ.RLeaf.galPt σ P ∈ AddSubgroup.zmultiples P'

example : ZInQ.RLeaf.X0Transitive ↔ X0TransitiveCopy := Iff.rfl

/-- The chain proved in this task: FLT bijection ⇒ modular equation ⇒ `X₀(N)`-transitivity. -/
example : ZInQ.Contrib.CloudB2X0Transitive.CyclicQuotientJBijOn → ZInQ.RLeaf.X0Transitive :=
  fun h => FltCqj.x0Transitive_of_modularEquationGeneric (FltCqj.modularEquationGeneric_of_bijOn h)

/-- Verbatim copy of `FltCqj.ModularEquationGeneric` (ZInQKernel/Contrib/CloudB2X0Transitive/ModularEquation.lean:254). -/
def ModularEquationGenericCopy : Prop :=
  ∀ (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (H : AddSubgroup EjBar.toAffine.Point), IsAddCyclic H → Nat.card H = N →
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar)
        (algebraMap Qj Kbar RatFunc.X))).IsRoot (EjBar.cyclicQuotientJ H N)

example : FltCqj.ModularEquationGeneric ↔ ModularEquationGenericCopy := Iff.rfl

/-- flt-cqj2: the copies, proved. -/
theorem cyclicQuotientJBijOnCopy_proof : CyclicQuotientJBijOnCopy := FltCqj2.cyclicQuotientJBijOn_proof
theorem modularEquationGenericCopy_proof : ModularEquationGenericCopy := FltCqj2.modularEquationGeneric_proof
theorem x0TransitiveCopy_proof : X0TransitiveCopy := FltCqj2.x0Transitive_proof

#print axioms cyclicQuotientJBijOnCopy_proof
#print axioms modularEquationGenericCopy_proof
#print axioms x0TransitiveCopy_proof

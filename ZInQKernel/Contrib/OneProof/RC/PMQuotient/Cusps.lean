import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Operators

/-! Tex 2937–2942, 8282–8297, 8487–8489. Specialization of the
rational torsion translation uses the same extended map (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 350000

namespace ZInQ.Manuscript.RC.PMQuotient.GoodRow

open GoodReduction (generic)

variable {R : Type} [CommRing R] [Algebra R ℚ]
    {ell N : ℕ} [Fact ell.Prime] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} {X : PMAdelic.CoarseFibre}
    {XQ EQ : Over (Spec (.of ℚ))} {π : XQ ⟶ EQ}
    (G : GoodRow R ell N K Ebar X π)

/-- The rational point group of the generic elliptic model, as sections.
The base changed terminal object is isomorphic to `Spec ℚ` over `Spec ℚ`. -/
abbrev RationalPoints :=
  Additive ((generic R ℚ).obj (𝟙_ (Over (Spec (.of R)))) ⟶ (generic R ℚ).obj G.E)

/-- The image of the moved rational cusp in the generic target.
An involution at an exact divisor of the level is defined over ℚ, so its
image of infinity is rational (Deligne–Rapoport VI.6, UNVERIFIED). -/
def rationalCusp {q : ℕ} (hq : q.Prime) (he : 0 < N.factorization q) : G.RationalPoints :=
  Additive.ofMul ((generic R ℚ).map (G.movedCusp hq he))

/-- Cuspidal torsion and the chosen multiplier, for just the rational
cusps used by this row. The class identification is the Abel–Jacobi
statement for the actual `J₀(N)`, kept as a separate input. -/
structure CuspInput (L : ℕ) where
  /-- The rational points of `J₀(N)`, needed only at the rational cusp classes. -/
  Jac : Type
  /-- The Jacobian group law. -/
  [groupJac : AddCommGroup Jac]
  /-- The class `[W_{q^e}∞] - [∞]` of the actual rational cusps. -/
  classOf : ∀ q : ℕ, q.Prime → 0 < N.factorization q → Jac
  /-- The elliptic quotient inducing the fixed parametrization (tex 1785–1787). -/
  phi : Jac →+ G.RationalPoints
  /-- The Abel–Jacobi factorization at these classes (tex 1786). -/
  image : ∀ q hq he, phi (classOf q hq he) = G.rationalCusp hq he
  /-- The actual cuspidal degree-zero classes are torsion: Elkik,
  Astérisque 183 (1990), Théorème, p. 59, applied to Γ₀(N). -/
  torsion : ∀ q hq he, IsOfFinAddOrder (classOf q hq he)
  /-- The needed part of `B_cusp ∣ L` (tex 8282–8297): the chosen `L`
  kills the image of each indicated rational torsion point. -/
  kills : ∀ q hq he, IsOfFinAddOrder (G.rationalCusp (q := q) hq he) →
    L • G.rationalCusp hq he = 0

attribute [instance] CuspInput.groupJac

/-- For the very same quotient used by the Heegner comparison, `L`
kills the residue of the moving cusp. The reduction of the generic
annihilation is additive since it is the reading of a group section. -/
theorem hCusp {L : ℕ} (C : G.CuspInput L) {ap : ℕ → ℤ} {w : ℕ → ℤˣ}
    (H : G.Relations ap w) {hell : ell % 4 = 3} {hN : 0 < N} {hcop : N.Coprime ell}
    (J : PMAdelic.JetchevKane ell hell N hN hcop X)
    (O : PMAdelic.OperatorComparison ell hell N hN hcop X J)
    (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) :
    L • (PMAdelic.geometry J O (G.specialFibre H).toSpecialFibre).cusp q = 0 := by
  have ht : IsOfFinAddOrder (G.rationalCusp hq he) := by
    rw [← C.image q hq he]
    obtain ⟨n, hn, h⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (C.torsion q hq he)
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨n, hn, by rw [← map_nsmul, h, map_zero]⟩
  have hg := C.kills q hq he ht
  let : Smooth (𝟙_ (Over (Spec (.of R)))).hom := by
    change Smooth (𝟙 (Spec (.of R)))
    infer_instance
  have hi : (G.movedCusp hq he) ^ L = 1 := by
    apply (G.neron.2.2.2.2 _).injective
    let f := (generic R ℚ).homMonoidHom (X := 𝟙_ (Over (Spec (.of R)))) (M := G.E)
    change f ((G.movedCusp hq he) ^ L) = f 1
    rw [map_pow, map_one]
    exact hg
  change L • (PMAdelic.geometricInput J O (G.specialFibre H).toSpecialFibre).specialize
    (X.W q G.infinity) = 0
  rw [G.specialize_eq_value H J O]
  apply Subtype.ext
  change L • G.evaluate (G.point (X.W q G.infinity)) = 0
  rw [G.point_W q hq he, G.point_infinity, evaluate]
  simp only [Category.assoc, ← Functor.map_comp]
  let red := G.readAt (residueUnit G.closed)
  change L • (red (G.movedCusp hq he)).toAdd = 0
  change ((red (G.movedCusp hq he)) ^ L).toAdd = (1 : Multiplicative _).toAdd
  rw [← map_pow, hi, map_one]


end ZInQ.Manuscript.RC.PMQuotient.GoodRow

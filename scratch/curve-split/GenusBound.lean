import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.RLeaf.BelyiX1
import ZInQKernel.Contrib.RLeaf.T40

/-! # curve-split: row H-79 `ZInQ.Contrib.CurvesG.GenusX1Field`

`GenusX1Field` (imported from `ZInQKernel/Contrib/CurvesG/GenusSplit.lean`, unchanged) says that the
genus of `K_N = ℚ(j)(x(P))` *equals* the genus of `Γ₁(N)`. Its published sources (Shimura 1971,
§6.7 canonical model of `X₁(N)`, and Prop. 1.40, the genus of `Γ\ℍ*`) are statements about the
compact Riemann surface `Γ₁(N)\ℍ*`, which has no Lean definition today (Mathlib v4.35 has the upper
half plane and the action of `SL₂(ℤ)`, not the compactified quotient as a Riemann surface nor its
genus). So `GenusX1Field` cannot be split into published-form leaves over genuine definitions now.

Finding (VERIFIED by reading the consumers): the proof only uses `GenusX1Field` through
`LeafModCurves.dim_J1_le` (`dim J₁(N) ≤ N²`; consumers `javanpeykarJ1` and the E2 step of
`scratch/g0-assemble2/olean/TailD.lean`). The bound needs much less than the equality:

* `GenusX1Le` (new, weaker than the row): `g(K_N) ≤ N²`; `genusX1Le_of_genusX1Field` (proved).
* `dimJ1Le_of` (proved): `DimJacobianEqGenus → GenusX1Le → DimJ1Le`, where `DimJ1Le` is exactly the
  conclusion of `LeafModCurves.dim_J1_le`.
* `genusX1Le_of_belyi` (proved): `BelyiGenusBound → X0Transitive → GenusX1Le`, from the kernel
  theorems `ZInQ.RLeaf.belyiX1` (`j/1728` is a Belyi function on `K_N`, `[K_N : ℚ(j)] ≤ N²`) and
  `ZInQ.RLeaf.x1ConstantField_of_x0Transitive` (`ℚ` is algebraically closed in `K_N`).
* `BelyiGenusBound` (named GLUE, a two-line consequence of Riemann–Hurwitz): a function field
  `F/ℚ` with constant field `ℚ` and a Belyi function `t` of degree `d` has `2g(F) + 1 ≤ d`.

No `sorry`, no `axiom`. -/

noncomputable section

namespace CurveSplit

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

/-- **GLUE (lit-composite): the Riemann–Hurwitz bound for Belyi functions.** Let `F` be a finite
extension of `ℚ(j)` (`Qj = RatFunc ℚ`) in which `ℚ` is algebraically closed, and suppose
`t = j/1728` is a Belyi function on `F` over `ℚ` (`IsBelyiFunction`: unramified over every finite
place of `ℚ(t)` other than `t = 0, 1`). Then `2 g(F) + 1 ≤ [F : ℚ(j)]`, `g = fieldGenus`.

Why true (STANDARD): Riemann–Hurwitz (Stichtenoth, *Algebraic function fields and codes*, Thm
3.4.13, with Dedekind's different theorem Thm 3.5.1 in characteristic 0; Hartshorne IV.2.4
geometrically; numbers UNVERIFIED) gives `2g − 2 = −2d + Σ_P (e_P − 1) deg P`, the sum over the
places above `t = 0, 1, ∞` only; at each of these three degree-one places the fundamental
identity `Σ_{P|Q} e_P f_P = d` (Stichtenoth Thm 3.1.11) gives `Σ_{P|Q} (e_P − 1) f_P ≤ d − 1`; so
`2g − 2 ≤ d − 3`. Also needed: the places of `F/ℚ` are discrete valuation rings (Stichtenoth Thm
1.1.6) to read `IsBelyiFunction` as `e_P = 1`, and `fieldGenus` (holomorphic differentials) is the
Riemann–Roch genus (Stichtenoth Thm 1.5.15 / Chevalley; UNVERIFIED). A Lean proof needs Lean
statements of these four textbook results over Mathlib's `ValuationSubring` (places, `e_P` as the
index of `Uₚ·ℚ(t)ˣ` in `Fˣ`, `deg P` as the `ℚ`-dimension of the residue field) and about 400
lines of valuation-theoretic glue. -/
def BelyiGenusBound : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → IsBelyiFunction ℚ F (algebraMap Qj F (RatFunc.X / 1728)) →
      2 * fieldGenus F + 1 ≤ Module.finrank Qj F

/-- **The genus bound that the proof uses** (weaker than `GenusX1Field`): `g(K_N) ≤ N²`. -/
def GenusX1Le : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N →
    fieldGenus (fieldX1 P) ≤ N ^ 2

/-- **The conclusion of `LeafModCurves.dim_J1_le`** (`dim J₁(N) ≤ N²`), the only use of T34. -/
def DimJ1Le : Prop :=
  ∀ (N : ℕ) (J : PkgI3.AbVar ℚ), 0 < N → IsJ1 N J →
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2

/-- `GenusX1Field → GenusX1Le` (proved, from `genus_Gamma1_le`). -/
theorem genusX1Le_of_genusX1Field (h : GenusX1Field) : GenusX1Le := by
  intro N P hN hP
  have : NeZero N := ⟨hN.ne'⟩
  have h1 := h N P hN hP
  have h2 := genus_Gamma1_le N
  rw [← h1] at h2
  exact_mod_cast h2

/-- **`DimJ1Le` from the first half of T34 and the genus bound** (proved). -/
theorem dimJ1Le_of (h1 : DimJacobianEqGenus) (h2 : GenusX1Le) : DimJ1Le := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, h2 N P hN hP⟩

/-- `K_N` is finite over `ℚ(j)`. -/
instance fieldX1_finiteDimensional (P : EjBar.toAffine.Point) :
    FiniteDimensional Qj (fieldX1 P) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (xCoord P))

/-- **`GenusX1Le` from the Riemann–Hurwitz bound for Belyi functions and `X₀(N)`-transitivity**
(proved; `BelyiX1` and the constant field are kernel theorems). -/
theorem genusX1Le_of_belyi (hB : BelyiGenusBound) (h0 : ZInQ.RLeaf.X0Transitive) :
    GenusX1Le := by
  intro N P hN hP
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hK := ZInQ.RLeaf.x1ConstantField_of_x0Transitive h0 N P hN hP
  have := hB (fieldX1 P) hK hBel
  omega

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, `BelyiGenusBound` and
`X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_belyi (h1 : DimJacobianEqGenus) (hB : BelyiGenusBound)
    (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of h1 (genusX1Le_of_belyi hB h0)

end CurveSplit

#print axioms CurveSplit.genusX1Le_of_genusX1Field
#print axioms CurveSplit.dimJ1Le_of
#print axioms CurveSplit.genusX1Le_of_belyi
#print axioms CurveSplit.dimJ1Le_of_belyi

import PGBase
/-! # period-glue: `PiTwistC` from R2fp and two smaller named Props

Task period-glue, 2026-11-13. `PiTwistC Y Φ π` (period-map, `PGBase`, unchanged) is proved from
* `R1fpProps Y Φ` (only: `Y` proper and smooth over `ℚ`) and `R2fpProps Y Φ π` (the leaves R1, R2;
  both already hypotheses at the own triple),
* `TwistOrbitFinite Y Φ` (**GLUE**, moduli: the twist relation on `ℚ̄`- and `ℂ`-points is the
  orbit relation of a finite set of automorphisms of `Y`), and
* `FibreTransferC Y π` (**GLUE**, algebraic geometry: a fibre statement for `π` that holds on
  `ℚ̄`-points holds on `ℂ`-points),
by `piTwistC_of`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

/-- **GLUE (moduli: the `Aut(𝒪)`-twist relation is a finite orbit relation).** There is a finite
set `G` of automorphisms of `Y` over `ℚ` such that, on `ℚ̄`-points and on `ℂ`-points, two points
have twist-equivalent QM pairs iff one is the image of the other under some `g ∈ G`.

Why true for the genuine `Y₃` (model argument): `G` = the automorphisms inducing `twist α`
(`α ∈ Aut 𝒪`) and `rightMul u` (`u ∈ 𝒪^×`) on points (`R1heckeProps`, a clause of R1), composed.
It is finite: `rightMul u` depends only on `u mod 3𝒪` (`Level3.rightMul_eq_self`), inner twists
are `rightMul`s up to isomorphism, and `Aut(𝒪)/Inn` is finite (mobius-glue `AutOInnerFinite`,
from the kernel's Skolem–Noether); an automorphism of the reduced `Y` is determined by its action
on field points. (⇐) is `Φ` of `y ≫ g`. (⇒) a QM isomorphism `Q.q.twist α ≅ Q'.q` transports
`Q'`'s level structure to one on `(A, ι∘α)`; over an algebraically closed field two level
structures on the same QM pair differ by right multiplication by a unit of `𝒪/3𝒪` (both are
`𝒪`-linear isomorphisms `𝒪/3𝒪 ≅ A[3]`, `|A[3]| = 81`), and `𝒪^× → (𝒪/3𝒪)^×` is onto (strong
approximation for `𝒪¹`, plus `1 + i` of reduced norm `−1`; a finite check on the 72 units of
`𝒪/3𝒪`); then `Φ` injective gives `y' = y ≫ g`. Size: medium. -/
def TwistOrbitFinite (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ G : Set (Y ≅ Y), G.Finite ∧
    (∀ (y y' : fieldPt Qbar ⟶ Y) (Q Q' : QML3 Qbar), Φ Qbar y = M3.mk Q → Φ Qbar y' = M3.mk Q' →
      ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
        ∃ g ∈ G, y' = y ≫ g.hom)) ∧
    (∀ (y y' : fieldPt ℂ ⟶ Y) (Q Q' : QML3 ℂ), Φ ℂ y = M3.mk Q → Φ ℂ y' = M3.mk Q' →
      ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
        ∃ g ∈ G, y' = y ≫ g.hom))

/-- **GLUE (algebraic geometry: transfer of a fibre statement from `ℚ̄`- to `ℂ`-points).** For a
proper smooth curve `Y` over `ℚ` (the hypotheses make the statement true for every `Y`; without
them it fails, e.g. for `Y = Spec ℂ`, which has no `ℚ̄`-points) and a finite set `G` of
automorphisms of `Y` over `ℚ`, if the fibres of `π` on `ℚ̄`-points are exactly
the `G`-orbits (in the sense below), the same holds on `ℂ`-points.

Why true (model argument), for `Y` of finite type and separated over `ℚ` (R1fp: proper):
`E = {(p, q) ∈ Y ×_ℚ Y : π(p) = π(q)}` (the equalizer of `π∘pr₁`, `π∘pr₂`, closed since `P¹` is
separated) and `Γ = ⋃_{g ∈ G} graph(g)` (finite union of closed graphs, `Y` separated) are closed
subsets of the finite-type `ℚ`-scheme `Y ×_ℚ Y`, hence Jacobson: each is the closure of its closed
points. Closed points are the images of `ℚ̄`-points (Nullstellensatz), and on those `E` and `Γ`
agree by hypothesis, so `E = Γ`. A `ℂ`-point `(y, y')` lies in `E` iff `π(y) = π(y')`, and in
`Γ` iff `y' = y ≫ g` for some `g ∈ G` (it factors through the reduced closed subscheme
`graph(g) ≅ Y`, `Y` smooth hence reduced). Mathlib has Jacobson schemes
(`AlgebraicGeometry.JacobsonSpace`) and equalizers/graphs of morphisms; the charts of `ToP1` must
be turned into a morphism to `P¹`. Size: medium. -/
def FibreTransferC (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ G : Set (Y ≅ Y), G.Finite →
    (∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)) →
    ∀ y y' : fieldPt ℂ ⟶ Y,
      (π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)

/-- **`PiTwistC` from R2fp, `TwistOrbitFinite` and `FibreTransferC` (proved).** -/
theorem piTwistC_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (hT : TwistOrbitFinite Y Φ)
    (hF : FibreTransferC Y π) :
    PiTwistC Y Φ π := by
  obtain ⟨G, hG, hQbar, hC⟩ := hT
  have hfibQ : ∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom) := by
    intro y y'
    have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
    have hQ : Φ Qbar y' = M3.mk (Quotient.out (Φ Qbar y')) := (Quotient.out_eq _).symm
    exact ((h2 y y' _ _ hP hQ).1).trans (hQbar y y' _ _ hP hQ)
  intro y y' Q Q' hQ hQ'
  exact (hF h1.1 h1.2.1 G hG hfibQ y y').trans (hC y y' Q Q' hQ hQ').symm

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.piTwistC_of

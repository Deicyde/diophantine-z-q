import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.HDecomp.QM.Structures

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/leaf-push2/LeafPush2.lean`, R3.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

namespace ZInQ.LeafPush2

open NumberField MeasureTheory

/-! Part I of the draft (def-faltings §§1-18 and H5, a verbatim copy) is imported from
`ZInQKernel.HDecomp.Faltings.Height`, namespace `ZInQ.DefFaltings`; the copies of
leaf-modcurves' curve definitions are `LeafModCurves`'s, from
`ZInQKernel.HDecomp.ModCurves.Leaves`. -/
open ZInQ.DefFaltings
open LeafModCurves (IsCurve IsJacobian JacobianExists IsBelyiFunction)
/-! The order `𝒪` and `QMStr` (copied in the draft from leaf-qm-fp) are `LeafQM`'s, from
`ZInQKernel.HDecomp.QM.Structures`. -/
open LeafQM (B ofInt InO mulCoord ofInt_mul ofInt_add ofInt_neg ofInt_zero ofInt_one O)
open LeafQM.AV (QMStr)

section R3Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ### The order `𝒪` and QM structures (copied from `scratch/leaf-qm-fp/QMLeaves.lean` §0-§1) -/

/-! ### Igusa–Clebsch and Igusa invariants of a sextic (copied from
`scratch/hdec-elementary/Leaves.lean` §1; Igusa's `J`'s new here) -/

variable {k : Type*} [Field k]

/-- (copied) `(rᵢ - rⱼ)²`. -/
def dsq (r : Fin 6 → k) (i j : Fin 6) : k := (r i - r j) ^ 2

/-- (copied) Igusa–Clebsch `I₂` of `a ∏ (X - rᵢ)`. -/
def IC2 (a : k) (r : Fin 6 → k) : k :=
  a ^ 2 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 2) (σ 3) * dsq r (σ 4) (σ 5)) / 48

/-- (copied) Igusa–Clebsch `I₄`. -/
def IC4 (a : k) (r : Fin 6 → k) : k :=
  a ^ 4 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 1) (σ 2) * dsq r (σ 2) (σ 0) *
    dsq r (σ 3) (σ 4) * dsq r (σ 4) (σ 5) * dsq r (σ 5) (σ 3)) / 72

/-- (copied) Igusa–Clebsch `I₆`. -/
def IC6 (a : k) (r : Fin 6 → k) : k :=
  a ^ 6 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 1) (σ 2) * dsq r (σ 2) (σ 0) *
    dsq r (σ 3) (σ 4) * dsq r (σ 4) (σ 5) * dsq r (σ 5) (σ 3) *
    dsq r (σ 0) (σ 3) * dsq r (σ 1) (σ 4) * dsq r (σ 2) (σ 5)) / 12

/-- (copied) Igusa–Clebsch `I₁₀`: the discriminant `a¹⁰ ∏_{i<j} (rᵢ - rⱼ)²`. -/
def IC10 (a : k) (r : Fin 6 → k) : k :=
  a ^ 10 * ∏ i : Fin 6, ∏ j : Fin 6, if i < j then dsq r i j else 1

/-- (copied) `y² = a ∏ (X - rᵢ)` is a genus-2 curve: `a ≠ 0` and distinct roots. -/
def IsGenus2 (a : k) (r : Fin 6 → k) : Prop := a ≠ 0 ∧ Function.Injective r

/-- (copied) The QM locus in Igusa–Clebsch coordinates (hdec-elementary). -/
def OnQMLocus (a : k) (r : Fin 6 → k) (j : k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ IC2 a r = c ^ 2 * (96 * (j + 1)) ∧ IC4 a r = c ^ 4 * (576 * j) ∧
    IC6 a r = c ^ 6 * (4608 * j * (5 * j + 4)) ∧ IC10 a r = c ^ 10 * (4096 * j ^ 3)

/-- Igusa's `J₂ = I₂/8`. -/
def IgJ2 (a : k) (r : Fin 6 → k) : k := IC2 a r / 8
/-- Igusa's `J₄ = (4J₂² − I₄)/96`. -/
def IgJ4 (a : k) (r : Fin 6 → k) : k := (4 * IgJ2 a r ^ 2 - IC4 a r) / 96
/-- Igusa's `J₆ = (8J₂³ − 160J₂J₄ − I₆)/576`. -/
def IgJ6 (a : k) (r : Fin 6 → k) : k :=
  (8 * IgJ2 a r ^ 3 - 160 * IgJ2 a r * IgJ4 a r - IC6 a r) / 576
/-- Igusa's `J₁₀ = I₁₀/4096`. -/
def IgJ10 (a : k) (r : Fin 6 → k) : k := IC10 a r / 4096

/-- **Lin–Yang's tuple** (arXiv:1807.00466v1 Example 29, eqs. (13)-(14)): the weighted-projective
point `[J₂ : J₄ : J₆ : J₁₀]` (weights `1, 2, 3, 5`) of `a ∏ (X - rᵢ)` is
`[12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`. The `J`/Igusa–Clebsch convention is Igusa's
(`I₂ = 8J₂`, `I₄ = 4J₂² − 96J₄`, `I₆ = 8J₂³ − 160J₂J₄ − 576J₆`, `I₁₀ = 4096J₁₀`; the convention of
hdec-elementary's `igusa_thomae_check.py`); locators.md asks to fix it before use: the check
`linYangTuple_onQMLocus` below ties it to hdec-elementary's `OnQMLocus`. -/
def LinYangTuple (a : k) (r : Fin 6 → k) (j : k) : Prop :=
  ∃ t : k, t ≠ 0 ∧ IgJ2 a r = t * (12 * (j + 1)) ∧ IgJ4 a r = t ^ 2 * (6 * (j ^ 2 + j + 1)) ∧
    IgJ6 a r = t ^ 3 * (4 * (j ^ 3 - 2 * j ^ 2 + 1)) ∧ IgJ10 a r = t ^ 5 * j ^ 3

/-- **Convention check (proved).** Lin–Yang's `J`-tuple with scaling `t = c²` is
hdec-elementary's Igusa–Clebsch locus `OnQMLocus` (the input of the proved F1 glue
`HDec.j_eq_of_onQMLocus`). Over an algebraically closed field every `t` is a square. -/
theorem linYangTuple_onQMLocus [CharZero k] {a : k} {r : Fin 6 → k} {j c : k} (hc : c ≠ 0)
    (h2 : IgJ2 a r = c ^ 2 * (12 * (j + 1)))
    (h4 : IgJ4 a r = (c ^ 2) ^ 2 * (6 * (j ^ 2 + j + 1)))
    (h6 : IgJ6 a r = (c ^ 2) ^ 3 * (4 * (j ^ 3 - 2 * j ^ 2 + 1)))
    (h10 : IgJ10 a r = (c ^ 2) ^ 5 * j ^ 3) : OnQMLocus a r j := by
  have e2 : IC2 a r = 8 * IgJ2 a r := by unfold IgJ2; field_simp
  have e4 : IC4 a r = 4 * IgJ2 a r ^ 2 - 96 * IgJ4 a r := by
    rw [show IgJ4 a r = (4 * IgJ2 a r ^ 2 - IC4 a r) / 96 from rfl]; field_simp; ring
  have e6 : IC6 a r = 8 * IgJ2 a r ^ 3 - 160 * IgJ2 a r * IgJ4 a r - 576 * IgJ6 a r := by
    rw [show IgJ6 a r = (8 * IgJ2 a r ^ 3 - 160 * IgJ2 a r * IgJ4 a r - IC6 a r) / 576 from rfl]
    field_simp; ring
  have e10 : IC10 a r = 4096 * IgJ10 a r := by unfold IgJ10; field_simp
  refine ⟨c, hc, ?_, ?_, ?_, ?_⟩
  · rw [e2, h2]; ring
  · rw [e4, h2, h4]; ring
  · rw [e6, h2, h4, h6]; ring
  · rw [e10, h10]; ring

/-- `LinYangTuple` gives `OnQMLocus` when the scaling is a square (e.g. `k` algebraically
closed), hence, by hdec-elementary's proved glue, `j = 3779136 · I₁₀² / I₄⁵`. -/
theorem onQMLocus_of_linYangTuple [CharZero k] [IsAlgClosed k] {a : k} {r : Fin 6 → k} {j : k}
    (h : LinYangTuple a r j) : OnQMLocus a r j := by
  obtain ⟨t, ht, h2, h4, h6, h10⟩ := h
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq t (by norm_num : 0 < 2)
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact ht hc.symm
  rw [← hc] at h2 h4 h6 h10
  exact linYangTuple_onQMLocus hc0 h2 h4 h6 h10

/-! ### The curve `y² = a ∏ (X − rᵢ)` as a scheme -/

/-- The sextic `a ∏ (X − rᵢ)`. -/
noncomputable def sextic (a : k) (r : Fin 6 → k) : Polynomial k :=
  Polynomial.C a * ∏ i, (Polynomial.X - Polynomial.C (r i))

/-- **`C` has the affine model `y² = a ∏ (X − rᵢ)`**: its function field is generated over `k`
by `x` transcendental and `y` with `y² = a ∏ (x − rᵢ)` (so it is `k(x)[y]/(y² − f(x))`, `f`
squarefree of degree 6 under `IsGenus2`). For a smooth proper geometrically connected curve this
determines `C` up to `k`-isomorphism (Hartshorne I.6.12 with II.6.7, UNVERIFIED numbers). -/
def HasSexticModel {K : Type} [Field K] (C : Over (Spec (CommRingCat.of K))) [IsIntegral C.left]
    (a : K) (r : Fin 6 → K) : Prop :=
  letI := ffAlgebra C
  ∃ x y : C.left.functionField, Transcendental K x ∧ y ^ 2 = Polynomial.aeval x (sextic a r) ∧
    IntermediateField.adjoin K {x, y} = ⊤

/-- **R3. Lin–Yang** (Math. Z. 295 (2020), 775-819; arXiv:1807.00466v1 **Example 29**, pp. 20-21,
discriminant 6, eqs. (13)-(14); read in arXiv v1 by the locator audit, journal numbering
UNVERIFIED; alternative supplier of the tuple and of the finite-nonzero-`j` Jacobian assertion:
Baba–Granath, Canad. J. Math. 60 (2008), Prop. 3.6, p. 742, read by the audit). Printed: on the
finite nonzero `j`-locus, the principally polarized QM surface of discriminant 6 over `j` is the
Jacobian of a genus-2 curve with `[J₂:J₄:J₆:J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`.

**Stated form (a consequence; polarization-free and coordinate-free).** Every abelian surface `A`
over `ℂ` with an embedding `𝒪 ↪ End(A)` is either `≅ Jac(C)` (as group schemes) for a curve `C`
with an affine model `y² = a ∏ (x − rᵢ)` (six distinct roots) on the Lin–Yang family at some
`j ≠ 0`, or `≅ E₁ × E₂` for elliptic curves `E₁, E₂`.

Why it is a consequence (citation chain, not Lean leaves):
* `(A, ι)` carries a principal polarization of the fixed type, so it is a point of `X₆` with a
  value `j ∈ ℙ¹` of the Hauptmodul of `X₆/W` (existence of the polarization: Lemma P
  (rv-qm-polar §0), for a fixed `μ` the type-`μ` principal polarization of `(A, ι)` exists and
  is unique in characteristic 0; VERIFIED as an argument, lattice cores compiled in
  `QM/Polar.lean`, published locators UNVERIFIED; Baba–Granath Thm 2.1 for `X₆/W`).
* `j ≠ 0, ∞`: Lin–Yang's assertion, forgetting the polarization (`≅` of group schemes).
* `j ∈ {0, ∞}`: the tuple has `J₁₀ = 0` there (in weighted-projective coordinates), so the
  principally polarized surface is not the Jacobian of a smooth curve, hence a product of elliptic
  curves (Weil's dichotomy for principally polarized abelian surfaces; Weil 1957, UNVERIFIED).
  The second disjunct is weaker than "product with its product polarization".

**Polarization (rv-qm-polar).** The statement is existential in `C` and does not mention a
polarization, so it stays a consequence if a QM surface carries several principal polarizations
(each gives a curve; Lin–Yang's is one of them). What would change: a form "for **every** genus-2
`C` with `Jac C ≅ A`, `C` lies on the family" (not stated here; false in general if `A` carries a
principal polarization whose Rosati involution is not of the fixed type), and the
coordinate-linked form "`j` = the value `π₆(x)` of the moduli point" (needs leaf-qm-fp's `X₆`
package and the polarization type; not stated here).

**Over `ℂ`** (Lin–Yang's setting). The `ℚ̄`-form used at A7/F1 follows by the Lefschetz principle
(the Shimura curve, the family and the Igusa invariants are defined over `ℚ`): glue target
`R03_LinYang_algClosed` below, not a leaf. -/
def R03_LinYang : Prop :=
  ∀ (A : AbVar ℂ) (_ : QMStr A), A.dim = (2 : WithBot ℕ∞) →
    (∃ (j a : ℂ) (r : Fin 6 → ℂ), j ≠ 0 ∧ IsGenus2 a r ∧ LinYangTuple a r j ∧
      ∃ (C : Over (Spec (CommRingCat.of ℂ))) (_ : IsCurve C) (_ : IsIntegral C.left),
        HasSexticModel C a r ∧
        ∃ (P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ C) (J : AbVar ℂ) (aj : C ⟶ J.X),
          IsJacobian C P₀ J aj ∧ ∃ e : J.X ≅ A.X, IsMonHom e.hom) ∨
    (∃ E₁ E₂ : AbVar ℂ, E₁.dim = (1 : WithBot ℕ∞) ∧ E₂.dim = (1 : WithBot ℕ∞) ∧
      Nonempty (A.X ≅ E₁.X ⊗ E₂.X))

/-- **Glue target (Lefschetz principle), not a leaf**: `R03_LinYang` over every algebraically
closed field of characteristic 0 (the case `k = ℚ̄` is the one A7/F1 use). -/
def R03_LinYang_algClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k) (_ : QMStr A),
    A.dim = (2 : WithBot ℕ∞) →
    (∃ (j a : k) (r : Fin 6 → k), j ≠ 0 ∧ IsGenus2 a r ∧ LinYangTuple a r j ∧
      ∃ (C : Over (Spec (CommRingCat.of k))) (_ : IsCurve C) (_ : IsIntegral C.left),
        HasSexticModel C a r ∧
        ∃ (P₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (J : AbVar k) (aj : C ⟶ J.X),
          IsJacobian C P₀ J aj ∧ ∃ e : J.X ≅ A.X, IsMonHom e.hom) ∨
    (∃ E₁ E₂ : AbVar k, E₁.dim = (1 : WithBot ℕ∞) ∧ E₂.dim = (1 : WithBot ℕ∞) ∧
      Nonempty (A.X ≅ E₁.X ⊗ E₂.X))

/-- The algebraically closed form contains the leaf (`k = ℂ`). -/
theorem R03_of_algClosed (h : R03_LinYang_algClosed) : R03_LinYang :=
  fun A q hA => h ℂ A q hA

/-- Consumer form (F1): on the first branch, Lin–Yang's `j` is the weight-0 Igusa invariant
`3779136 · I₁₀² / I₄⁵` of the curve (from `onQMLocus_of_linYangTuple` and hdec-elementary's
`j_eq_of_onQMLocus`, whose two-line proof is repeated here). -/
theorem linYang_j_eq [CharZero k] [IsAlgClosed k] {a : k} {r : Fin 6 → k} {j : k} (hj : j ≠ 0)
    (h : LinYangTuple a r j) : j = 3779136 * IC10 a r ^ 2 / IC4 a r ^ 5 := by
  obtain ⟨c, hc, -, h4, -, h10⟩ := onQMLocus_of_linYangTuple h
  rw [h4, h10]
  field_simp
  ring

end R3Sec

/-! ## T10-T12: what a concrete statement needs (only the parts statable over the definitions
above; no étale cohomology is built). See docs/research/leaf-push2.md §5. -/

end ZInQ.LeafPush2

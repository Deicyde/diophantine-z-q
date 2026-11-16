import ZInQKernel.OneProof.H.TailS
import ZInQKernel.HDecomp.Objects

/-! dict-galois: the four chain statements, copied verbatim (`TailS.lean` l. 69, 347, 1992; `HDecomp/Objects.lean`
l. 861, universe fixed to `Type` as in the field `PkgI2.NeronOggShafarevich.{0}`), each checked `Iff.rfl` against
the original. -/

namespace DictGaloisOld

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open CategoryTheory AlgebraicGeometry
open PkgI2 (IsAbelianVariety HasGoodReduction InertiaTrivialOn)
open scoped TensorProduct

/-- **LEAF (Tate 1967, §3.3, Theorem 2; locator UNVERIFIED).** Tate, *p-divisible groups*, Proc.
Conf. Local Fields (Driebergen 1966), Springer 1967, pp. 158-183, §3.3: for a complete discretely
valued field `K` of characteristic `0` with perfect residue field of characteristic `p`, and
`i ≠ 0`, `H⁰(G_K, ℂ(i)) = 0`, where `ℂ` is the completion of `K̄` and `ℂ(i)` its twist by the
`i`-th power of the cyclotomic character. Specialization: `K` finite over `ℚ_p` (inside `ℚ̄_p`, so
that `ℂ = ℂ_p` and `G_K = Gal(ℚ̄_p/K)`). -/
def TateTwistInvariants : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (i : ℤ), i ≠ 0 → ∀ x : ℂ_[p],
      (∀ σ ∈ K.fixingSubgroup, cycPow p σ i • cpAct p σ x = x) → x = 0

/-- **LEAF (Hodge–Tate decomposition of the Tate module of an abelian variety).** Fontaine,
*Formes différentielles et modules de Tate des variétés abéliennes sur les corps locaux*, Invent.
Math. 65 (1982), 379-409, Théorème principal (with Tate 1967 §4, Cor. 2 of Thm 3 for good
reduction, and Faltings, JAMS 1 (1988), for `H¹_ét`; all locators UNVERIFIED): for an abelian
variety `A` of dimension `g` over a finite extension `F` of `ℚ_p` there is a `G_F`-equivariant
`ℂ_p`-linear isomorphism `ℂ_p ⊗_{ℚ_p} V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t_{A'}^*)` with
`dim_F t_A = dim_F t_{A'}^* = g` (`t` = tangent space at the origin, `A'` the dual). Lean form:
after choosing `F`-bases of the two `g`-dimensional spaces, `ℂ_p(1)^g ⊕ ℂ_p^g`; `G_F` acts on
`ℂ_p ⊗ V` by `σ ⊗ ρ(σ)` and on `ℂ_p(1)` by `c ↦ χ(σ) σ(c)`, through pkg-I4's `gfToGqp`
(the embedding `ℚ̄_p ≅ F̄` behind Mathlib's `Field.absoluteGaloisGroup.map`, which identifies
`ℂ_F` with `ℂ_p`). Specialization of the printed statement (bases chosen). -/
def HodgeTateDecompAbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

/-- **LEAF (the de Rham comparison for `H¹` of an abelian variety, printed `D_dR`).** As
`DeRhamH1AbVar`, with `H¹_ét(A_{F̄}, ℚ_p)` replaced by `Hom_{ℚ_p}(V_p(A), ℚ_p)` with the
contragredient action (the standard identification; Milne, *Abelian varieties*, Thm 15.1(a),
UNVERIFIED) and `D_dR` in its printed form `(B_dR ⊗ W)^{G_F}`. Faltings 1989; Tsuji 1999; Scholze,
Forum Math. Pi 1 (2013), Cor. 1.8; Fontaine 1982 for abelian varieties. -/
def DeRhamH1AbVarT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), IsDeRhamTensorOver p (A.galRep p).dual

/-- **Leaf I2-NOS (Serre–Tate 1968, Thm 1; criterion of Néron–Ogg–Shafarevich).**
`K` a field with a discrete valuation ring `O`, `w` a valuation ring of `K̄` over `O`, `A/K` an
abelian variety. Then (a) ⟺ (b) ⟺ (c), where (a) good reduction at `O`, (b) for every `m ≥ 1`
invertible in `O`, inertia at `w` fixes `A(K̄)[m]`, (c) the same for infinitely many such `m`. -/
def NeronOggShafarevich : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)

theorem tate_iff : TateTwistInvariants ↔ ZInQ.Contrib.HodgeSplit.TateTwistInvariants := Iff.rfl
theorem ht_iff : HodgeTateDecompAbVar ↔ ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar := Iff.rfl
theorem dr_iff : DeRhamH1AbVarT ↔ ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT := Iff.rfl
theorem nos_iff : NeronOggShafarevich ↔ PkgI2.NeronOggShafarevich.{0} := Iff.rfl

end DictGaloisOld

import ZInQKernel.HDecomp.Textbook.T10Etale
import ZInQKernel.Contrib.OneProof.EllAdic.EtaleHOneKernelRebaseV1

/-!
# Milne's Tate duality for an abelian variety, on the étale site

The printed statement behind `t10TateDuality`, read on classical étale cohomology:
`H¹(A_K̄, ℤ_ℓ)` is the group of compatible families of classes in `H¹_et(A_K̄, ℤ/ℓⁿ)` on the small
étale site of `A_K̄ = A ×_K Spec K̄` (`EtaleHOneZl`), with the `ℤ_ℓ`-module structure through
residues (`RC53.EllAdic.etaleHOneKernelModule`). `Gal(K̄/K)` acts by the same transport as in
`T10Etale.galH`: `σ` acts by pullback along `(T10Etale.galIso A σ⁻¹).symm`, i.e. by `(1 × Spec σ)^*`
(`etaleGalH`).

The statement uses no vendored source and no pro-étale cohomology.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory RC53.EllAdic
open scoped RC53.EllAdic.FiniteAbDictionary
open PkgI3 MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.OneProof.MilneTateDuality

/-- `H¹(A_K̄, ℤ_ℓ)` as compatible families of classes in `H¹_et(A_K̄, ℤ/ℓⁿ)`. -/
abbrev EtaleHOneZl {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) : Type 1 :=
  ↥(etaleResidueHOneSubShift (A.baseChange (AlgebraicClosure K)).X.left ℓ).ker

/-- The Galois action on `H¹(A_K̄, ℤ_ℓ)`: `σ` acts by pullback along `1 × Spec σ`, written exactly
as `T10Etale.galH` writes it, as transport along `galIso A σ⁻¹`. -/
noncomputable def etaleGalH {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    (σ : Field.absoluteGaloisGroup K) : EtaleHOneZl A ℓ →+ EtaleHOneZl A ℓ :=
  etaleResidueHOneKernel_rebase (T10Etale.galIso A (σ⁻¹ : Field.absoluteGaloisGroup K)).symm ℓ

/-- **Milne, *Abelian varieties* (1986), Theorem 15.1(a) with Remark 15.5, degree one.**
J. S. Milne, *Abelian varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic Geometry*
(Springer, 1986), pp. 103–150:

* Theorem 15.1, p. 129: "Let A be an abelian variety of dimension g over an algebraically closed
  field k, and let l be a prime different from char(k). (a) There is a canonical isomorphism
  H¹(A_et, ℤ_l) → Hom_{ℤ_l}(T_l A, ℤ_l)."
* Remark 15.5, p. 131: "Theorem 15.1 is still true if k is only separably closed (see [13, II,
  3.17]). If A is defined over a field k, then the isomorphism Λ* Hom(T_l, ℤ_l) → H*(A_{k_s}, ℤ_l)
  is compatible with the natural actions of Gal(k_s/k)."

Read here at `k = K̄`, the algebraic closure, with `Gal(K̄/K)` acting as in `etaleGalH` and on
`Hom(T_ℓ A, ℤ_ℓ)` by the contragredient action of `T10Etale.T10_TateDuality`. Reading steps:
`H¹(A_et, ℤ_l)` is the inverse limit of `H¹(A_et, ℤ/lⁿ)` (Milne's proof identifies it with
`Hom_conts(π₁^et(A, 0), ℤ_l)`); `K̄` in place of `k_s` (equal in characteristic zero); the
canonical isomorphism is weakened to an existing one. -/
def MilneAV86Thm151aRem155 : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    letI := etaleHOneKernelModule (A.baseChange (AlgebraicClosure K)).X.left ℓ
    ∃ φ : EtaleHOneZl A ℓ ≃ₗ[ℤ_[ℓ]] Module.Dual ℤ_[ℓ] (A.T ℓ),
      ∀ (σ : Field.absoluteGaloisGroup K) (y : EtaleHOneZl A ℓ),
        φ (etaleGalH A ℓ σ y) = (A.galT (ℓ := ℓ) σ⁻¹).dualMap (φ y)

end ZInQ.OneProof.MilneTateDuality

import ZInQKernel.Contrib.CloudR2CM.SerreTate.FiniteInertiaStatements
import ZInQKernel.Contrib.AVB1.BaseChange

/-!
# P0: the field of definition of complex multiplication

Statement only; it supplies no proof. Let `E/L` be an elliptic curve (an abelian variety of
dimension `1`) over a number field whose geometric endomorphism ring is the order `R` of the
imaginary quadratic field `k` (`HDec.CMBranch.IsCMBy`, endomorphisms over `L̄`). Then every
geometric endomorphism is defined over a finite extension `L'` of `L` that receives `k`. Over every
extension `M ⊇ L'` of `L`:

* `AllGeometricEndDefined`: the base change `End_M(E_M) → End_{M̄}(E_{M̄})` (`ZInQ.Contrib.AVB1.bcHom`,
  injective by `bcHom_injective`) is bijective, i.e. every endomorphism over `M̄` is defined over
  `M`; in particular the Galois group of `M̄/M` acts trivially on `End_{M̄}(E_{M̄})`, the image of
  the base change;
* `BaseDefinedCM`: `End_M(E_M) ≅ R`, so all of `R` acts through `M`-endomorphisms and the Galois
  image `ρ_ℓ(G_M)` commutes with `R ⊗ ℤ_ℓ` on `T_ℓ` (the input of P1).

The extensions `M` are FINITE over `L` (a forced feasibility narrowing; the route uses only
`M = L₁`, finite over `L`). KNOWN LIMITATION, not an assumption: the same conclusion for every
extension `M ⊇ L'` is true but would need rigidity of endomorphisms under extension of
algebraically closed fields to transcendental ones (Chow; or the discreteness of Hom schemes), for
which no supplier is used here. For finite `M`, `M̄` is an algebraic closure of `L`, isomorphic to
`L̄` over `L`. The extension is stated by base change from `L` itself (no iterated base change).

Classical: the endomorphisms of a CM elliptic curve are defined over `Lk` (Silverman, *Advanced
Topics in the Arithmetic of Elliptic Curves*, Thm II.2.2; Serre–Tate, Ann. of Math. 88 (1968), §4;
numbers UNVERIFIED).
-/

set_option autoImplicit false

noncomputable section

namespace HDec.CMSerreTate

/-- Every endomorphism of `A` over an algebraic closure of `K` is defined over `K`: the base change
`End_K(A) → End_{K̄}(A_{K̄})` is bijective. -/
def AllGeometricEndDefined {K : Type} [Field K] (A : _root_.PkgI3.AbVar K) : Prop :=
  Function.Bijective (_root_.ZInQ.Contrib.AVB1.bcHom (AlgebraicClosure K) A A)

/-- **P0 (the CM field of definition).** For `E/L` of dimension `1` with `IsCMBy E k R`, there is a
finite extension `L'/L` with a field embedding `k → L'` such that over every FINITE extension `M`
of `L` that receives `L'` over `L`, every geometric endomorphism of `E_M` is defined over `M` and
`End(E_M) ≅ R`. -/
def CMFieldOfDefinition : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : _root_.ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k),
      HDec.CMBranch.IsImagQuadOrder k R → HDec.CMBranch.IsCMBy E k R →
      ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L')
        (_ : FiniteDimensional L L'),
        Nonempty (k →+* L') ∧
        ∀ (M : Type) [Field M] [Algebra L M] [FiniteDimensional L M], Nonempty (L' →ₐ[L] M) →
          AllGeometricEndDefined ((HDec.LeafAdopt.abVarEquiv L E).baseChange M) ∧
            BaseDefinedCM ((HDec.LeafAdopt.abVarEquiv L E).baseChange M) R

end HDec.CMSerreTate

import ZInQKernel.Contrib.LocalSquareRoot.Cyclotomic
import ZInQKernel.Contrib.LocalSquareRoot.Necessity

/-!
# T30: the exact baseline leaf, conditional only on actual local KW

`localKroneckerWeber_implies_leafSqrtCrit` is a closed implication from the actual
T16(a) proposition to `GlueDescent.B2Q.LeafSqrtCrit`. It is not an unconditional
provider, does not prove local KW, and does not register or close an H target.

The forward construction is unconditional. Local KW enters only when an arbitrary
locally constant square-root character must be descended to a cyclotomic level.
The two CRT casts and the consumed global character are exactly the baseline's.
-/

namespace ZInQ.Contrib.LocalSquareRoot

open GlueSqrtDisj GlueDescent.B2Q

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The actual Dirichlet character has a locally constant local square root whenever
its prescribed CRT-unit value is one. This direction does not use local KW. -/
theorem dirichlet_squareRoot_at_level (p : Nat.Primes)
    (k m : ℕ) [NeZero m] (hcop : (p : ℕ).Coprime m)
    (χ : DirichletCharacter ℂ ((p : ℕ) ^ k * m))
    (u : (ZMod ((p : ℕ) ^ k * m))ˣ)
    (hu₁ : ((u : ZMod ((p : ℕ) ^ k * m)).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu₂ : ((u : ZMod ((p : ℕ) ^ k * m)).cast : ZMod m) = 1)
    (hχ : χ.toUnitHom u = 1) :
    ∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
      ∀ g, φ g ^ 2 = galChar χ (resp p g) := by
  obtain ⟨τ, hτ⟩ := exists_tau (p := (p : ℕ))
    (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m hcop
  have hτχ : finiteGalChar (p : ℕ) χ τ = 1 :=
    (finiteGalChar_tau_eq (p : ℕ) k m hcop χ τ hτ u hu₁ hu₂).trans hχ
  obtain ⟨φ, hφ, hsq⟩ := exists_inflated_squareRoot (p : ℕ) k m hcop τ hτ
    (finiteGalChar (p : ℕ) χ) hτχ
  exact ⟨φ, hφ, fun g => (hsq g).trans (finiteGalChar_restrict_eq_galChar p χ g)⟩

/-- The finite-level normalization is a proved equality, not a replacement definition.
This theorem retains exactly the local-KW premise and both original residue hypotheses. -/
theorem local_squareRoot_criterion_normalized (p : Nat.Primes)
    (hKW : PkgI6.LocalKroneckerWeber (p : ℕ))
    (N k m : ℕ) [NeZero N] [NeZero m]
    (hN : N = (p : ℕ) ^ k * m) (hcop : (p : ℕ).Coprime m)
    (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ)
    (hu₁ : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu₂ : ((u : ZMod N).cast : ZMod m) = 1) :
    (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
      ∀ g, φ g ^ 2 = galChar χ (resp p g)) ↔ χ.toUnitHom u = 1 := by
  subst N
  constructor
  · rintro ⟨φ, hφ, hsq⟩
    obtain ⟨τ, hτ⟩ := exists_tau (p := (p : ℕ))
      (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m hcop
    have hsq' : ∀ g, φ g ^ 2 = finiteGalChar (p : ℕ) χ
        (g.restrictNormal (muField (p : ℕ) ((p : ℕ) ^ k * m))) := by
      intro g
      exact (hsq g).trans (finiteGalChar_restrict_eq_galChar p χ g).symm
    have hval := finite_obstruction_of_squareRoot (p : ℕ) hKW k m hcop τ hτ
      (finiteGalChar (p : ℕ) χ) φ hφ hsq'
    rwa [finiteGalChar_tau_eq (p : ℕ) k m hcop χ τ hτ u hu₁ hu₂] at hval
  · exact dirichlet_squareRoot_at_level p k m hcop χ u hu₁ hu₂

/-- **Closed conditional T30 glue.** The sole remaining mathematical premise is the
actual universal local-Kronecker-Weber proposition, i.e. frozen T16(a). The conclusion
is definitionally the exact PR36 baseline leaf and frozen draft T30. No H provider or
acceptance is asserted. -/
theorem localKroneckerWeber_implies_leafSqrtCrit :
    (∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p) →
      GlueDescent.B2Q.LeafSqrtCrit := by
  intro hKW p N _ χ u hu₁ hu₂
  obtain ⟨hm, hcop, hN⟩ := canonical_cyclotomic_level (p : ℕ) N
  haveI : NeZero (N / (p : ℕ) ^ N.factorization p) := ⟨hm.ne'⟩
  exact local_squareRoot_criterion_normalized p (hKW (p : ℕ)) N
    (N.factorization p) (N / (p : ℕ) ^ N.factorization p) hN hcop χ u hu₁ hu₂

end ZInQ.Contrib.LocalSquareRoot

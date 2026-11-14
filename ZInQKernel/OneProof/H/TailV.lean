import ZInQKernel.OneProof.H.TailO
import ZInQKernel.OneProof.H.TailT

/-! # OneProof H, leaf-fold7 part V: hodge-split's rows transported to the chain's copies

hodge-split (`TailS`, `TailT`) proves its five rows over the kernel's pkg-I4 layer `ZInQ.Contrib.G9.PkgI4`
(`ZInQKernel/Contrib/G9/I4Layer.lean`). The chain states the same rows over its own copies: the structures
`_root_.PkgI4.GaloisRep`, `_root_.PkgI4.GaloisChar` (`HDecomp/Conductor/LadicCond.lean`, aliased in `HDec.PkgI4`) and
`HDec.PkgI4.I3.AbVar`, and the definitions of `HDec.PkgI4` (`htMult`, `HasHTWeightsAtSelf`, `IsDeRham`,
`IsDeRhamOver`, `htMultOver`, ...), all verbatim copies of pkg-I4. The transports below send a chain object to the
G9 object with the same fields; the predicates then agree by unfolding (the copies have the same text over Mathlib). -/

namespace HDec

set_option maxHeartbeats 1000000

namespace HSyn

namespace HodgeLF7

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- A chain Galois representation as a G9 one (same fields). -/
def toG9Rep {p n : ℕ} [Fact p.Prime] (ρ : _root_.PkgI4.GaloisRep p n) : ZInQ.Contrib.G9.PkgI4.GaloisRep p n :=
  ⟨ρ.toHom, ρ.continuous_toHom⟩

/-- A G9 Galois representation as a chain one (same fields). -/
def ofG9Rep {p n : ℕ} [Fact p.Prime] (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep p n) : _root_.PkgI4.GaloisRep p n :=
  ⟨ρ.toHom, ρ.continuous_toHom⟩

/-- A chain Galois character as a G9 one (same fields). -/
def toG9Char {p : ℕ} [Fact p.Prime] (ψ : _root_.PkgI4.GaloisChar p) : ZInQ.Contrib.G9.PkgI4.GaloisChar p :=
  ⟨ψ.toHom, ψ.continuous_toHom⟩

/-- A chain abelian variety (pkg-I4's I3 layer) as a G9 one (same fields). -/
def toG9AbVar {F : Type} [Field F] (A : PkgI4.I3.AbVar F) : ZInQ.Contrib.G9.PkgI4.I3.AbVar F :=
  { X := A.X, grp := A.grp, proper := A.proper, smooth := A.smooth, geomInt := A.geomInt }

/-- **H-52** on the chain's copy. -/
theorem finiteImageHT (h : _root_.ZInQ.Contrib.HodgeSplit.G0Galois.FiniteImageHT) : G0Galois.FiniteImageHT := by
  intro p _ n ρ hfin
  exact h p n (toG9Rep ρ) hfin

/-- **H-51** on the chain's copy. -/
theorem senTwist (h : _root_.ZInQ.Contrib.HodgeSplit.G0Galois.SenTwist) : G0Galois.SenTwist := by
  intro p _ n ρ ρ' ψ S S' htw hS hS' h1 h2
  exact h p n (toG9Rep ρ) (toG9Rep ρ') (toG9Char ψ) S S' htw hS hS' h1 h2

/-- **H-22** on the chain's copy. -/
theorem r14Det (h : _root_.ZInQ.Contrib.HodgeSplit.G0Galois.R14Det) : G0Galois.R14Det := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, h1, h2, ε, h3, h4⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨ofG9Rep ρ, h1, h2, ε, h3, h4⟩

/-- **H-32** on the chain's copy. -/
theorem t23 (h : ∀ (p : ℕ) [Fact p.Prime], ZInQ.Contrib.G9.PkgI4.T23_FontaineClosure p) :
    ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p :=
  fun p _ => h p

end HodgeLF7

end HSyn

end HDec

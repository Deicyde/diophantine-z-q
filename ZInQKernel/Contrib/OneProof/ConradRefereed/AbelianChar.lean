import ZInQKernel.Contrib.OneProof.ConradRefereed.Bridges
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-! Pass from a continuous character on `G_{ℚ_p}` to its evaluation at
the arithmetic Artin map. Provenance (c): quotient and neighbourhood translations. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Bridges

open Module
open scoped TensorProduct Topology Filter

set_option linter.style.longLine false

variable (p : ℕ) [Fact p.Prime]
variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- The continuous character on the topological abelianization appearing in
Conrad, Appendix B pp. 32 (UNVERIFIED)–33 (C8, L760–762). -/
def conradAbelianChar (ψ : PkgI4.GQp p →* Kˣ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))) :
    Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* Kˣ :=
  TopologicalAbelianization.lift
    { toMonoidHom := ψ
      continuous_toFun := Units.isEmbedding_val₀.isInducing.continuous_iff.mpr
        (Topology.IsInducing.subtypeVal.continuous_iff.mpr hc) }

/-- C8, Conrad p. 33 (UNVERIFIED): the displayed near-one equality on the arithmetic Artin
map itself, for local base `ℚ_p` (one factor in the product). -/
def ArtinNearOneOnAbelianization (ψ : PkgI4.GQp p →* Kˣ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))) (n : ℤ) : Prop :=
  ∀ᶠ x : ℚ_[p]ˣ in 𝓝 1,
    (conradAbelianChar p ψ hc (TauCeti.ClassFieldTheory.artinMap ℚ_[p] x) : K) =
      algebraMap ℚ_[p] K (x : ℚ_[p]) ^ (-n)

/-- Evaluating the descended character on the arithmetic Artin symbol agrees
with evaluating the original character on any lift of that symbol. -/
theorem conradAbelianChar_artinLift (ψ : PkgI4.GQp p →* Kˣ) (hc)
    (x : ℚ_[p]ˣ) (σ : PkgI4.GQp p) (hσ : IsArtinLift p σ x) :
    conradAbelianChar p ψ hc (TauCeti.ClassFieldTheory.artinMap ℚ_[p] x) = ψ σ := by
  rw [← hσ]
  exact TopologicalAbelianization.lift_mk _ _

/-- The old lift formulation is equivalent to Conrad's equality on the
abelianization. Surjectivity is used pointwise, with no choice of section. -/
theorem artinNearOneOnAbelianization_iff (ψ : PkgI4.GQp p →* Kˣ) (hc) (n : ℤ) :
    ArtinNearOneOnAbelianization p ψ hc n ↔ ArtinNearOne p ψ n := by
  constructor
  · intro h
    filter_upwards [h] with x hx σ hσ
    rwa [← conradAbelianChar_artinLift p ψ hc x σ hσ]
  · intro h
    filter_upwards [h] with x hx
    obtain ⟨σ, hσ⟩ := exists_artinLift p x
    rw [conradAbelianChar_artinLift p ψ hc x σ hσ]
    exact hx σ hσ


#print axioms conradAbelianChar_artinLift
#print axioms artinNearOneOnAbelianization_iff

end HDec.G0Galois.C8Conrad.Bridges

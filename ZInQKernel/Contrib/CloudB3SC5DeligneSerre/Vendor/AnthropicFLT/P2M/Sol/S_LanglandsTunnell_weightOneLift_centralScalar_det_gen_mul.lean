/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul (git blob e01dc8a10a3befaa82a16195531d5ac79205ab00, sha256 5302c029673b536e8ed1ffe9cfc122338a726e2fbee39452f2cf6fb54a9ef12b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_DirichletCharacter_DirichletIdeleChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LanglandsTunnell_weightOneLift_centralScalar_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul

set_option autoImplicit false

namespace P2GProbe
namespace C2

open NumberField IsDedekindDomain AutomorphicForm UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups

noncomputable section

private theorem det_gen_mem_Z (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v) ∈ (productionPinsCompact ℚ).Z := by
  rw [productionPinsCompact_Z]
  exact Subgroup.mem_top _

private theorem det_gen_law_of_central_law {n : ℕ} [NeZero n] (f : ℍ → ℂ)
    (χ : DirichletCharacter ℂ n)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ))
    (hlaw : ∀ (z : (productionPinsCompact ℚ).Z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g)
        = ((((DirichletCharacter.dirichletIdeleChar χ *
            (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
              (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          (productionPinsCompact ℚ).Z.subtype) z : ℂˣ) : ℂ) * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
          (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)) * g)
        = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  intro v hv g
  rw [hb v hv]
  exact hlaw ⟨Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v), det_gen_mem_Z v⟩ g

end

end P2GProbe.C2

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne in
open IsDedekindDomain in
open scoped ModularForm MatrixGroups in
theorem solution
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
          (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)) * g)
        = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  exact P2GProbe.C2.det_gen_law_of_central_law f χ Φ S hb
    (LanglandsTunnell.weightOneLift_centralScalar_mul hn f hf χ hχ)

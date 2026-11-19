/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_HeckeEigensystemMap (git blob 0a7e18963273d60c5a2e655a85a997ba8e91f4d7, sha256 19830ae0a25093afd219203d28453d8259abde237de1ee60eb6affd09987bdcb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_HeckeEigensystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open IsDedekindDomain NumberField

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]
  {S : Type*} [CommRing S]

def map (ι : R →+* S) (Φ : HeckeEigensystem F R) : HeckeEigensystem F S where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => ι (Φ.a v)
  b := fun v => ι (Φ.b v)

@[simp] theorem map_level (ι : R →+* S) (Φ : HeckeEigensystem F R) :
    (Φ.map ι).level = Φ.level := rfl

@[simp] theorem map_a (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).a v = ι (Φ.a v) := rfl

@[simp] theorem map_b (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).b v = ι (Φ.b v) := rfl

theorem map_id (Φ : HeckeEigensystem F R) : Φ.map (RingHom.id R) = Φ := rfl

theorem map_map {T : Type*} [CommRing T] (ι : R →+* S) (κ : S →+* T)
    (Φ : HeckeEigensystem F R) : (Φ.map ι).map κ = Φ.map (κ.comp ι) := rfl

theorem map_twist (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) :
    (Φ.twist χ).map ι = (Φ.map ι).twist fun v => ι (χ v) := by
  simp only [map, twist]
  congr 1 <;> funext v
  · exact map_mul ι (χ v) (Φ.a v)
  · rw [map_mul, map_pow]

theorem AgreesAwayFromFinite.map {Φ Φ' : HeckeEigensystem F R}
    (h : AgreesAwayFromFinite Φ Φ') (ι : R →+* S) :
    AgreesAwayFromFinite (Φ.map ι) (Φ'.map ι) := by
  obtain ⟨S₀, hS₀⟩ := h
  exact ⟨S₀, fun v hv => ⟨congrArg ι (hS₀ v hv).1, congrArg ι (hS₀ v hv).2⟩⟩

end HeckeEigensystem

end AutomorphicForm

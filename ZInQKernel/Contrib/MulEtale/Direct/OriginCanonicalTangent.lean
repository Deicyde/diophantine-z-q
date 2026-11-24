/-
Multiplication-etale construction: OriginCanonicalTangent.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.OriginTangent

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

noncomputable section

namespace H101DirectFieldRoute

universe u

/-- The canonical tangent map of multiplication at the actual identity is
bijective. Its target is the actual tangent space at f(e); only the proved
unit equation canonically identifies that point with e. -/
theorem canonical_unit_tangentMap_bijective
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) (n : ℕ)
    (hn : IsUnit ((n + 1 : ℕ) : G.left.residueField ((η[G]).left s))) :
    letI := AlgebraicGeometry.isIso_residueFieldMap_zpow_id_left
      G s ((n + 1 : ℕ) : ℤ)
    Function.Bijective
      (AlgebraicGeometry.tangentMap
        ((𝟙 G) ^ ((n + 1 : ℕ) : ℤ)).left G.hom G.hom (Over.w _)
        ((η[G]).left s)) := by
  haveI := AlgebraicGeometry.isIso_residueFieldMap_zpow_id_left
    G s ((n + 1 : ℕ) : ℤ)
  let φ := ((𝟙 G) ^ ((n + 1 : ℕ) : ℤ)).left
  let e := (η[G]).left s
  have hbase : φ ≫ G.hom = G.hom := Over.w _
  have hfix : φ e = e := by
    simpa only [Scheme.Hom.comp_apply] using congrArg
      (fun a : S ⟶ G.left => a s)
      (AlgebraicGeometry.unit_left_comp_zpow_id_left
        G ((n + 1 : ℕ) : ℤ))
  haveI : IsIso (G.hom.residueFieldMap e) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section
      G.hom (η[G]).left (Over.Hom.w (η[G])) s
  let E : DottedTangentArrow G.hom (φ e) ≃ DottedTangentArrow G.hom e :=
    Equiv.cast (congrArg (fun x => DottedTangentArrow G.hom x) hfix)
  have hformula (θ : DottedTangentArrow G.hom e) :
      E (AlgebraicGeometry.tangentMap φ G.hom G.hom hbase e θ) =
        unitTangentPower G s n θ := by
    have hcast : ∀ {x y : G.left} (h : x = y)
        (v : DottedTangentArrow G.hom x),
        Equiv.cast (congrArg (fun z => DottedTangentArrow G.hom z) h) v = (h ▸ v) := by
      intro x y h v
      cases h
      rfl
    apply Subtype.ext
    calc
      (E (AlgebraicGeometry.tangentMap φ G.hom G.hom hbase e θ)).val =
          (hfix ▸ AlgebraicGeometry.tangentMap φ G.hom G.hom hbase e θ).val :=
        congrArg Subtype.val
          (hcast hfix (AlgebraicGeometry.tangentMap φ G.hom G.hom hbase e θ))
      _ = θ.val ≫ φ :=
        AlgebraicGeometry.tangentMap_fixed_apply G.hom φ hbase e hfix θ
      _ = (unitTangentPower G s n θ).val := by
        simp only [unitTangentPower, φ, zpow_natCast]
  have hunit := unitTangentPower_bijective G s n hn
  change Function.Bijective (AlgebraicGeometry.tangentMap φ G.hom G.hom hbase e)
  constructor
  · intro θ ψ h
    apply hunit.1
    rw [← hformula, ← hformula, h]
  · intro θ
    obtain ⟨ψ, hψ⟩ := hunit.2 (E θ)
    refine ⟨ψ, E.injective ?_⟩
    rw [hformula, hψ]

end H101DirectFieldRoute

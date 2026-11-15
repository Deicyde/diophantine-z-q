import ZInQKernel.OneProof.Main

/-! # rigid-prune: the two consumers that need rigidity, and the comparisons that do not (scratch, not on the chain)

Compile from the repository root after `lake build +ZInQKernel.OneProof.Main`:

    lake env lean scratch/rigid-prune/Sites.lean

* §1 `phi_part_ab`: qm-pin's `phi_part` with the universal clause of one witness and the family clause of the other
  both in abelian-scheme form: the comparison of two witnesses needs no rigidity.
* §2 the site `ModelGlue.exists_genFib_to_Y` (TailL): its one use of `R1univProps` is on `famBC 𝒜 j`, the generic
  fibre of the Shimura model's family. `ShimuraModelGenericAb` (that family is an abelian scheme with `𝒪`-action and
  level 3) is exactly what the abelian-scheme clause needs there (`exists_genFib_to_Y_ab`), and it is an instance of
  `QMFamilyGroupLaw` (`shimuraModelGenericAb_of_gl`).
* §3 the site `MCRGlue.modelCoordinateResidue_of_quotient` (TailW): the field `quotientP1Coordinate` takes
  `R1fpProps Y Φ`; on a witness of the abelian-scheme leaves this is `R1univProps Y Φ`, which follows from
  `QMFamilyGroupLaw` (`r1fpProps_of_ab_gl`). -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits LeafQM.AV

namespace RigidPrune

open LeafQM.AV.R1UnivRigid

/-! ## §1 Comparisons of abelian-scheme witnesses need no rigidity -/

/-- **`phi_part` on abelian schemes** (the proof of `LeafQM.AV.Pin.phi_part` with `R1univAbProps` and
`R1fpPropsAb`): the universal object of `(Y', Φ')` is a `QMAbScheme`, so `R1univAbProps Y Φ` classifies it. -/
theorem phi_part_ab {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univAbProps Y Φ) (h1' : R1fpPropsAb Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, -, ⟨𝒜', h𝒜'⟩, -⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜'.toQMFamily s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

end RigidPrune

namespace HDec.ModelGlue

open Polynomial VertWitness HeckeRestNV _root_.HDec.LeafQM.AV.Pin _root_.HDec.G0ModField PropTSRed PropTSGlue
open LeafQM.AV.R1UnivRigid

/-! ## §2 The site `exists_genFib_to_Y` -/

/-- **The fact the vertical witness needs** (precise form): for every Shimura model `(𝒴, 𝒜)` over `ℤ_(p)`, the
pulled-back family `famBC 𝒜 j` over the generic fibre `𝒴_ℚ` underlies an abelian scheme with `𝒪`-action and
level 3. The field `shimuraGoodReductionNoGuard` gives `𝒜` as a `QMFamily` only. -/
def ShimuraModelGenericAb : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left),
    IsShimuraModel p 𝒴 𝒜 →
    ∃ 𝒜' : QMAbScheme (genFib 𝒴).left,
      𝒜'.toQMFamily = famBC 𝒜 (pullback.fst 𝒴.hom (specRatToZloc p))

/-- **`exists_genFib_to_Y` from the abelian-scheme clause and `ShimuraModelGenericAb`** (the proof of
`exists_genFib_to_Y`, TailL, with `R1univAbProps` applied to the abelian scheme on `famBC 𝒜 j`). -/
theorem exists_genFib_to_Y_ab (hA : ShimuraModelGenericAb) {p : ℕ} [Fact p.Prime]
    {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h1 : R1univAbProps Y Φ) :
    ∃ g : genFib 𝒴 ⟶ Y,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ genFib 𝒴) (P : QML3 K),
        IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P →
          Φ K (s ≫ g) = M3.mk P) ∧
      Function.Bijective (fun s : fieldPt Qbar ⟶ genFib 𝒴 => s ≫ g) := by
  obtain ⟨𝒜', h𝒜'⟩ := hA p 𝒴 𝒜 hM
  obtain ⟨hP, hS, hfib, hinj, hsurj, -, -, -⟩ := hM
  set j := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ genFib 𝒴),
      ∃ P : QML3 K, IsFibreOf 𝒜'.toQMFamily s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := hfib K (s.left ≫ j)
    exact ⟨P, h𝒜' ▸ isFibreOf_baseChange 𝒜 j s.left P hP⟩
  obtain ⟨g, hg⟩ := h1 (genFib 𝒴) (genFib_isProper 𝒴 hP) (genFib_smooth 𝒴 hS) 𝒜' hall
  have hg' : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ genFib 𝒴) (P : QML3 K),
      IsFibreOf 𝒜 (s.left ≫ j) P → Φ K (s ≫ g) = M3.mk P :=
    fun K _ _ s P hP => hg K s P (h𝒜' ▸ isFibreOf_baseChange 𝒜 j s.left P hP)
  refine ⟨g, hg', ?_, ?_⟩
  · intro s s' hss
    obtain ⟨P, hPs⟩ := hfib Qbar (s.left ≫ j)
    obtain ⟨P', hPs'⟩ := hfib Qbar (s'.left ≫ j)
    have e : M3.mk P = M3.mk P' := by
      rw [← hg' _ s P hPs, ← hg' _ s' P' hPs']
      exact congrArg (Φ Qbar) hss
    exact genFib_pt_inj 𝒴 s s' (hinj _ _ P P' hPs hPs' e)
  · intro y
    set P := Quotient.out (Φ Qbar y)
    have hPy : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
    obtain ⟨y𝒴, hy⟩ := hsurj P
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y𝒴
    refine ⟨s, (Φ Qbar).injective ?_⟩
    rw [hPy]
    exact hg' Qbar s P (hs ▸ hy)

/-- **`ShimuraModelGenericAb` is an instance of `QMFamilyGroupLaw`**: `𝒴_ℚ` is a proper smooth curve over `ℚ`
and every field fibre of `famBC 𝒜 j` is an object (the fibre clause of `IsShimuraModel` at `s ≫ j`). -/
theorem shimuraModelGenericAb_of_gl (hG : QMFamilyGroupLaw) : ShimuraModelGenericAb := by
  intro p _ 𝒴 𝒜 hM
  obtain ⟨hP, hS, hfib, -⟩ := hM
  exact hG (genFib 𝒴) (genFib_isProper 𝒴 hP) (genFib_smooth 𝒴 hS) _ (fun K _ _ s => by
    obtain ⟨P, hP⟩ := hfib K (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p))
    exact ⟨P, isFibreOf_baseChange 𝒜 _ s.left P hP⟩)

end HDec.ModelGlue

namespace RigidPrune

open LeafQM.AV.R1UnivRigid

/-! ## §3 The site of the field `quotientP1Coordinate` -/

/-- **What the field `OpenGlue7.quotientP1Coordinate` needs of a witness**: `R1fpProps Y Φ`, i.e. on a witness of the
abelian-scheme leaves its universal clause on every `QMFamily`; from `QMFamilyGroupLaw`. -/
theorem r1fpProps_of_ab_gl (hG : QMFamilyGroupLaw) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsAb Y Φ) : R1fpProps Y Φ :=
  (r1fpProps_iff_ab_gl hG Y Φ).mpr h

/-- The field's statement, unfolded: its hypothesis list contains `R1fpProps Y Φ` (and its conclusion does not
mention `Y`), so using it needs some witness with `R1fpProps`. -/
example : HDec.MCRGlue.QuotientP1Coordinate =
    ∀ (p : ℕ) [Fact p.Prime], 324 < p →
      ∀ (𝒴 : Over (Spec (CommRingCat.of (HDec.VertWitness.Zloc p)))) (𝒜 : QMFamily 𝒴.left),
        HDec.VertWitness.IsShimuraModel p 𝒴 𝒜 → HDec.VertWitness.CMObjectsExist →
        ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
          R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
          ∃ (𝒵 : Over (Spec (CommRingCat.of (HDec.VertWitness.Zloc p)))) (q : 𝒴 ⟶ 𝒵) (ρ' : ToP1 𝒵.left),
            IsFinite q.left ∧ HDec.MCRGlue.IsP1Coordinate 𝒵 ρ' ∧
              HDec.VertWitness.CoordFibres 𝒴 𝒜 (ρ'.comp q.left) := rfl

end RigidPrune

#print axioms RigidPrune.phi_part_ab
#print axioms HDec.ModelGlue.exists_genFib_to_Y_ab
#print axioms HDec.ModelGlue.shimuraModelGenericAb_of_gl
#print axioms RigidPrune.r1fpProps_of_ab_gl

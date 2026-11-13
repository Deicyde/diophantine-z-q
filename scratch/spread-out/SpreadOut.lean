import ZInQKernel.HDecomp.Faltings.H5BaseChange
import ZInQKernel.Contrib.SpreadOut.NumberField

/-! # spread-out: neron-lg's glue N1-g1 `AbVarSpreadsOut` from three EGA IV leaves

`HasAbelianSchemeAway` and `AbVarSpreadsOut` below are verbatim copies (docstring and `def`) of the
declarations of the same names in `scratch/neron-lg/NeronLG.lean` (namespace `ZInQ.NeronLG`), under
the same `open`s (checked by `scratch/spread-out/py/verbatim_check.py`).  The proof is
`ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega` (`ZInQKernel/Contrib/SpreadOut/NumberField.lean`),
whose statement is the body of `AbVarSpreadsOut` with `HasAbelianSchemeAway` unfolded; the leaves
are `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii`, `EGAIV_8_10_5_xii`, `EGAIV_17_7_8_ii`
(`ZInQKernel/Contrib/SpreadOut/Spread.lean`). -/

namespace ZInQ.SpreadOutN1

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open ZInQ.H5Neron (jL NeronProp)
open scoped Obj

/-- `B` extends to an abelian scheme over `𝓞_L[1/f]`: a smooth proper group scheme whose generic
fibre is identified with `B` as a group scheme (over every presentation of `𝓞_L[1/f]`). -/
def HasAbelianSchemeAway (L : Type) [Field L] [NumberField L] (B : AbVar L) (f : 𝓞 L) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L],
    ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
      letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
        Functor.grpObjObj
      IsMonHom gen.hom

/-- **Glue N1-g1 (spreading out an abelian variety).** An abelian variety `B` over a number field
`L` extends to an abelian scheme over `𝓞_L[1/f]` for some nonzero `f ∈ 𝓞_L`. Textbook (a
candidate for a textbook leaf): `L = colim 𝓞_L[1/f]`, so `B`, its group law, unit and inverse
and the group axioms (equalities of morphisms) descend to some `𝓞_L[1/f]` (EGA IV₃ 8.8.2), as do
properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8 (ii)); all locators UNVERIFIED.
Mathlib v4.35 has the descent of morphisms for affine transition maps
(`AlgebraicGeometry/.../AffineTransitionLimit.lean`, EGA IV 8.8.2) but not the descent of schemes
or of properness and smoothness. -/
def AbVarSpreadsOut : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L), ∃ f : 𝓞 L, f ≠ 0 ∧ HasAbelianSchemeAway L B f

open ZInQ.Contrib.SpreadOut in
/-- **N1-g1 `AbVarSpreadsOut` from the EGA IV leaves 8.8.2 (ii), 8.10.5 (xii), 17.7.8 (ii)
(proved).** -/
theorem abVarSpreadsOut_of_ega (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii)
    (hsm : EGAIV_17_7_8_ii) : AbVarSpreadsOut :=
  fun L _ _ B => ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega h882 hpr hsm L B

end ZInQ.SpreadOutN1

#print axioms ZInQ.SpreadOutN1.abVarSpreadsOut_of_ega
#print axioms ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega
#print axioms ZInQ.Contrib.SpreadOut.exists_grpObj_descend
#print axioms ZInQ.Contrib.SpreadOut.exists_lift
#print axioms ZInQ.Contrib.SpreadOut.exists_map_eq
#print axioms ZInQ.Contrib.SpreadOut.NF.specConeIsLimit
#print axioms ZInQ.Contrib.SpreadOut.isMonHom_descend


/-! # shimura-split additions over the chain: rows r1rec, r5 from r1r2; H-1 from four inputs -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Row `r1rec` (`R1rec`) from row `r1r2` (`R1R2fpRep`)**: the bundle's `R1R2fpRep` carries the point
form `R1recProps` on its fine witness; field of moduli = residue field (`ShimuraSplit.fieldOfModuli3_eq_residueImage`,
from the kernel's rigidity) gives the object form. -/
theorem r1rec_of_r1r2 (h : LeafAdopt.R1R2fpRep) : LeafQM.AV.R1rec := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, h6, -, hr, -, h5, -⟩ := h
  exact ShimuraSplit.r1rec_of_point ⟨Y, Φ, h1, hr⟩

/-- **Row `r5` (`R5fp`) from row `r1r2` (`R1R2fpRep`)**: the point form `R5ptProps` on the coarse witness
and field of moduli = residue field (`ShimuraSplit.fieldOfModuliPair_eq_residueImage`). -/
theorem r5fp_of_r1r2 (h : LeafAdopt.R1R2fpRep) : LeafQM.AV.R5fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, h6, -, hr, -, h5, -⟩ := h
  exact ShimuraSplit.r5fp_of_point ⟨Y, Φ, X, Ψ, fY, h6, h5⟩

/-- `ReciprocityOfFine` (qm-split's universal glue) from the object form `R1rec`. -/
theorem reciprocityOfFine_of_r1rec (h : LeafQM.AV.R1rec) : ReciprocityOfFine :=
  fun _ _ h1 => ShimuraSplit.point_of_r1rec h h1

/-- `ResidueOfX6` (qm-split's universal glue) from the object form `R5fp`. -/
theorem residueOfX6_of_r5fp (h : LeafQM.AV.R5fp) : ResidueOfX6 :=
  fun _ _ _ _ _ _ h6 => ShimuraSplit.point_of_r5fp h h6

/-- `CanonicalModelY3` is implied by `CanonicalCoarseX6` (so it is not a separate input). -/
theorem canonicalModelY3_of_coarse (hC : CanonicalCoarseX6) : CanonicalModelY3 := by
  obtain ⟨Y, Φ, -, -, -, h1, -⟩ := hC
  exact ⟨Y, Φ, h1⟩

/-- `ReciprocityOfFine` from the existential point form on one fine witness (the form of Shimura
reciprocity closest to print: a statement about points of the canonical model). -/
def ReciprocityCanonical : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ R1recProps Y Φ

theorem r1rec_of_reciprocityCanonical (h : ReciprocityCanonical) : LeafQM.AV.R1rec :=
  ShimuraSplit.r1rec_of_point h

/-- **Row H-1 (`r1r2`) from two existential moduli statements and the two object forms**:
`CanonicalCoarseX6` (Shimura/Deligne canonical model with its coarse quotient), `BabaGranathX6`
(Baba–Granath's Hauptmodul on it), `R1rec` (Shimura reciprocity, field-of-moduli form) and `R5fp`
(González–Rotger Thm 5.12, field-of-moduli form). `HeckeOfFine`, `CoarseFactor`, `CurveBijIso` are
theorems (qm-split, coarse-factor, curve-split); `ReciprocityOfFine`, `ResidueOfX6` follow from the object
forms by the bridge. -/
theorem r1r2fpRep_of_split (hC : CanonicalCoarseX6) (hB : BabaGranathX6) (hR : LeafQM.AV.R1rec)
    (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRep :=
  r1r2fpRep_of' (canonicalModelY3_of_coarse hC) (coarseX6OfFine_of hC)
    (hauptmodulOfX6_of hB (coarseCompare_of_canonical hC)) (reciprocityOfFine_of_r1rec hR)
    (residueOfX6_of_r5fp h5)

/-- The same with `GonzalezRotgerX6` (the point form on the canonical `X₆`) for `R5fp`, and the
reciprocity point form `ReciprocityCanonical` for `R1rec`. -/
theorem r1r2fpRep_of_split' (hC : CanonicalCoarseX6) (hB : BabaGranathX6) (hR : ReciprocityCanonical)
    (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRep := by
  refine r1r2fpRep_of_split hC hB (r1rec_of_reciprocityCanonical hR) ?_
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, h5⟩ := hG
  exact ShimuraSplit.r5fp_of_point ⟨Y, Φ, X, Ψ, fY, h6, h5⟩

/-- **Finding (VERIFIED by `Iff.rfl`)**: qm-glue's LEAF-form `ConicCanonical` is the row
`X6Kummer.X6ConicModel` itself, so `x6ConicModel_of_canonical'(')` does not reduce H-43. -/
theorem conicCanonical_iff : ConicCanonical ↔ X6Kummer.X6ConicModel := Iff.rfl

/-- **Finding (VERIFIED by `Iff.rfl`)**: qm-glue's LEAF-form `ConnectedCanonical` is the row
`TSHecke.Y3Connected` itself (qm-glue says so). -/
theorem connectedCanonical_iff : ConnectedCanonical ↔ TSHecke.Y3Connected := Iff.rfl

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.r1rec_of_r1r2
#print axioms HDec.QMSplit.Moduli.r5fp_of_r1r2
#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of_split
#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of_split'

/-! ## `CanonicalCoarseX6` split; rows H-59 and r5count at the chain's constants -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF-form (canonical models `Y₃`, `X₆` with `X₆` geometrically connected).** Some fine witness carries
a coarse witness `X` (`X6Props`: the coarse moduli interpretation of `X₆(ℚ̄)`, the Atkin–Lehner action over
`ℚ`, the forgetful map) with `X ×_ℚ ℚ̄` connected in every geometric fibre (`GeometricallyConnected`).
Published: Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21
and §2 (`π₀(Sh_{𝒪̂^×} ⊗ ℚ̄) = ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×) = 1`, as `nrd(𝒪̂^×) = ℤ̂^×`); locators UNVERIFIED.
This is `CanonicalCoarseX6` without the clause "the forgetful map is onto `X(ℚ̄)`". -/
def GeomConnX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ LeafAdopt.R1pi0Props X

/-- `CanonicalCoarseX6` from `GeomConnX6` and coarse-factor's `PairsLift` (every QM pair over `ℚ̄` carries a
level-3 structure): the forgetful map is onto `X(ℚ̄)`. -/
theorem canonicalCoarseX6_of (hG : GeomConnX6) (hL : PairsLift) : CanonicalCoarseX6 := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, hpi⟩ := hG
  refine ⟨Y, Φ, X, Ψ, fY, h1, h6, fun x => ?_, hpi⟩
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Ψ x)
  obtain ⟨P, hP⟩ := hL Q
  obtain ⟨y, hy⟩ := (Φ Qbar).surjective (M3.mk P)
  refine ⟨y, Ψ.injective ?_⟩
  rw [h6.2.2.2.2.2 y P hy, hP, hQ]

/-- And conversely (so the split is an equivalence). -/
theorem geomConnX6_pairsLift_of (hC : CanonicalCoarseX6) : GeomConnX6 ∧ PairsLift := by
  refine ⟨?_, pairsLift_of_canonical hC⟩
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -, hpi⟩ := hC
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, hpi⟩

/-- **Row H-1 (`r1r2`) from five inputs**: `GeomConnX6` (canonical models, `X₆` geometrically connected),
`PairsLift` (level-3 structures exist over `ℚ̄`), `BabaGranathX6` (the Hauptmodul of `X₆/W`), `R1rec`
(Shimura reciprocity, field-of-moduli form) and `R5fp` (González–Rotger Thm 5.12, field-of-moduli form). -/
theorem r1r2fpRep_of_split5 (hG : GeomConnX6) (hL : PairsLift) (hB : BabaGranathX6)
    (hR : LeafQM.AV.R1rec) (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRep :=
  r1r2fpRep_of_split (canonicalCoarseX6_of hG hL) hB hR h5

/-- **Row H-59 (`y3Connected`) from Deligne's components leaf** (`ShimuraSplit.DeligneComponentsY3`) by the
orbit computation `ShimuraSplit.y3Connected_of_deligne`. -/
theorem y3Connected_of_deligne (h : ShimuraSplit.DeligneComponentsY3) : TSHecke.Y3Connected :=
  ShimuraSplit.y3Connected_of_deligne h

/-- **Row r5count (`R5fpCount`) from González–Rotger's count on the points of the canonical `X₆`.** -/
theorem r5fpCount_of_points (h : ShimuraSplit.GonzalezRotgerCountX6) : LeafQM.AV.R5fpCount :=
  ShimuraSplit.r5fpCount_of_points h

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.canonicalCoarseX6_of
#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of_split5
#print axioms HDec.QMSplit.Moduli.y3Connected_of_deligne
#print axioms HDec.QMSplit.Moduli.r5fpCount_of_points

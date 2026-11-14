
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

/-- **LEAF-form (Shimura reciprocity at the three elliptic CM points, on the points of the canonical
`Y₃`).** Some fine witness `(Y, Φ)` satisfies `R1recProps`: a `ℚ̄`-point whose object has CM by `ℤ[i]`,
`ℤ[ζ₃]` or `ℤ[√−6]` has residue field unramified at every `p ≥ 5`.
*Published statement*: Shimura reciprocity for CM points on the canonical model (Shimura, Ann. of Math. 85
(1967), Main Thm II; Deligne, Sém. Bourbaki 389 (1971), §§3.7-3.13, Thm 4.19, read by the audit as
"consequence with qualifications"; locators otherwise UNVERIFIED): for `y` with CM by the maximal order of
`k`, `k(y)` lies in the ray class field of `k` of conductor 3, which is unramified outside `3·disc(k) | 72`.
*Form*: a **consequence** of one theorem (the unramifiedness conclusion, not the printed reciprocity law);
it is the point form of leaf-qm-fp's `R1recProps`, and equivalent to `R1rec` given a fine witness
(`ShimuraSplit.r1rec_of_point`, `point_of_r1rec`). Lemma QP as for `R1fp`. -/
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

/-! ## `BabaGranathX6` without its surjectivity clause -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF-form (Baba–Granath on the canonical `X₆`), without the surjectivity clause.** Some coarse
witness carries `π₆ : X₆ → P¹` with the fibre clause (two `ℚ̄`-points have the same value iff their QM pairs
are `Aut(𝒪)`-twists, i.e. `W`-conjugate) and the CM clauses (`π₆ = 0, ∞, −16/27` exactly at CM by `ℤ[i]`,
`ℤ[ζ₃]`, `ℤ[√−6]`) of `R2X6PropsIff`. Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 (`X₆/W ≅ P¹_ℚ`,
the polarized moduli space is `X₆/W`), Lemma 3.1 and the §3.1 table (each of `CM(−4)`, `CM(−3)`, `CM(−24)`
is one `W`-orbit); read by the audit (YES); the coordinate is Baba–Granath's `j` (values `0, ∞, −16/27`). -/
def BabaGranathX6' : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ ∃ π₆ : ToP1 X.left, LeafAdopt.R2X6PropsIff X Ψ π₆

/-- `BabaGranathX6` from `BabaGranathX6'`: the surjectivity of `π₆` on `ℚ̄`-points is proved
(`ShimuraSplit.surj_of_fibre`: finite twist classes and the kernel's `CurveSurj`). -/
theorem babaGranathX6_of (h : BabaGranathX6') : BabaGranathX6 := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, π₆, h2⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, π₆, h2,
    ShimuraSplit.surj_of_fibre h6 π₆ fun x x' P Q hP hQ => (h2 x x' P Q hP hQ).1⟩

theorem babaGranathX6'_of (h : BabaGranathX6) : BabaGranathX6' := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, π₆, h2, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, π₆, h2⟩

/-- **Row H-1 (`r1r2`) from five inputs, `BabaGranathX6'` without the surjectivity clause.** -/
theorem r1r2fpRep_of_split6 (hG : GeomConnX6) (hL : PairsLift) (hB : BabaGranathX6')
    (hR : LeafQM.AV.R1rec) (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRep :=
  r1r2fpRep_of_split5 hG hL (babaGranathX6_of hB) hR h5

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.babaGranathX6_of
#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of_split6

/-! ## `GeomConnX6` split: Deligne's `π₀` at level one and the textbook step to geometric connectedness -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF (textbook: connectedness over an algebraic closure gives geometric connectedness).** For a proper
morphism `f : X → Spec k`, if `X ×_k k̄` is connected (`k̄` an algebraic closure) then `f` is geometrically
connected. EGA IV_2 (4.5.1)-(4.5.2); Stacks, Varieties, Lemma 33.7.6 (tag 0389): `X` is geometrically
connected over `k` iff `X_{k^sep}` is connected (locators UNVERIFIED, no network; the printed statement
needs no properness, which is added here, so the leaf is weaker than the print). Stacks uses a separable
closure; `X_{k̄} → X_{k^sep}` is a universal homeomorphism, and here `k` has characteristic 0 (hypothesis
`[CharZero k]`, also weakening), where the two closures agree. Mathlib 4.35 has the
definition `GeometricallyConnected` but not this criterion. -/
def GeomConnOfAlgClosure : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), IsProper f →
    ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) →
      GeometricallyConnected f

/-- **LEAF-form (Deligne's components at level one; specialization).** Some witness of the moduli clause
lists has `X₆ ×_ℚ ℚ̄` connected. Deligne, Sém. Bourbaki 389 (1971), §§2-3 and PSPM 33 (1979), 2.1, 2.6.3:
`π₀(Sh_K ⊗ ℚ̄) = ℚ^×_{>0}\𝔸_f^×/nrd(K)`; for `K = 𝒪̂^×`, `nrd(𝒪̂^×) = ℤ̂^×` and
`𝔸_f^× = ℚ^×_{>0}·ℤ̂^×`, so `π₀` is one point (locators UNVERIFIED). A consequence of one theorem (the
computation `nrd(𝒪̂^×) = ℤ̂^×` is not formalized). -/
def DeligneComponentsX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ ConnectedSpace (ShimuraSplit.baseQbar X)

theorem geomConnX6_of (hD : DeligneComponentsX6) (hE : GeomConnOfAlgClosure) : GeomConnX6 := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, hc⟩ := hD
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, hE ℚ X.left X.hom h6.1 hc⟩

/-- **Row H-1 (`r1r2`) from its printed parts on the canonical models**: Deligne's `π₀` at level one
(`DeligneComponentsX6`) with the textbook criterion `GeomConnOfAlgClosure`, the existence of level-3
structures (`PairsLift`), Baba–Granath (`BabaGranathX6'`), Shimura reciprocity on points
(`ReciprocityCanonical`) and González–Rotger Thm 5.12 on points (`GonzalezRotgerX6`). -/
theorem r1r2fpRep_of_printed (hD : DeligneComponentsX6) (hE : GeomConnOfAlgClosure) (hL : PairsLift)
    (hB : BabaGranathX6') (hR : ReciprocityCanonical) (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRep := by
  refine r1r2fpRep_of_split6 (geomConnX6_of hD hE) hL hB (r1rec_of_reciprocityCanonical hR) ?_
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, h5⟩ := hG
  exact ShimuraSplit.r5fp_of_point ⟨Y, Φ, X, Ψ, fY, h6, h5⟩

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.geomConnX6_of
#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of_printed

/-! ## H-43 `x6ConicModel`: Elkies' model of the canonical `X₆` as the only new input -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF-form (Kurihara, Elkies: the conic model of the canonical `X₆` with its Hauptmodul).** Some witness
`(Y, Φ, X, Ψ, fY)` of the moduli clause lists `R1fpProps`, `X6Props` carries `π₆ : X₆ → P¹` with the fibre and
CM clauses `R2X6Props` and the conic model `X6Kummer.ConicModel X π₆` (`X₆(ℚ̄) ≃ C(ℚ̄)` for
`C : Y² + 3X² + 3Z² = 0`, `Aut(ℚ̄/ℚ)`-equivariantly, with `π₆ = −16(X² + Z²)/(27Z²)`). Published: Kurihara,
J. Fac. Sci. Univ. Tokyo 25 (1979) (`X₀(6,1) : x² + y² + 3 = 0`); Elkies, ANTS-III, LNCS 1423 (1998), §3
(`X*(6) = X₆/W` with coordinate `t`, `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`, and
`X₆ = X*(6)(√−t, √(3(t − 1)))`; `j = 16(t − 1)/27`); locators UNVERIFIED. Unlike qm-glue's `ConicCanonical`
(which is the row `X6ConicModel` itself), it does not contain the clauses `R1heckeProps`, `CMExists`,
`R1recProps`, `X6Surj`, `R5ptProps` of the row's witness: those come from `r1r2`. -/
def ElkiesConicX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧ X6Kummer.ConicModel X π₆

/-- `ConicOfWitness` from `ElkiesConicX6` (qm-glue's `conicOfWitness_of'` with the smaller leaf). -/
theorem conicOfWitness_of_elkies (hC : ElkiesConicX6) (hK : CoarseCompare) (hU : HauptmodulUniqueX6S) :
    ConicOfWitness := by
  intro Y Φ X Ψ fY π₆ hfull
  obtain ⟨h1f, -, h6, h2, hcm, -, ⟨-, hs⟩, -⟩ := hfull
  have h1 : R1fpProps Y Φ := h1f
  obtain ⟨Y₀, Φ₀, X₀, Ψ₀, fY₀, π₀, h1₀, h6₀, h2₀, e₀, he₀g, he₀p, he₀i⟩ := hC
  obtain ⟨g, hg⟩ := compare_iso h1₀ h1
  obtain ⟨k, hk⟩ := hK Y Φ X X₀ Ψ Ψ₀ fY (g.hom ≫ fY₀) h1 h6 (x6Props_transport g hg h6₀)
  have hval : ∀ x : fieldPt Qbar ⟶ X,
      (π₀.comp k.hom.left).val (K := Qbar) x.left = π₀.val (K := Qbar) (x ≫ k.hom).left := by
    intro x; exact ToP1.val_comp_right (K := Qbar) π₀ k.hom.left x.left
  have h2' : R2X6Props X Ψ (π₀.comp k.hom.left) := by
    intro x x' P Q hP hQ
    have := h2₀ (x ≫ k.hom) (x' ≫ k.hom) P Q ((hk x).trans hP) ((hk x').trans hQ)
    simpa only [hval] using this
  have hagree : ∀ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = π₀.val (K := Qbar) (x ≫ k.hom).left :=
    fun x => (hU Y Φ X Ψ fY π₆ _ h1 h6 hs h2 h2' hcm x).trans (hval x)
  let post : (fieldPt Qbar ⟶ X) ≃ (fieldPt Qbar ⟶ X₀) :=
    ⟨fun x => x ≫ k.hom, fun x => x ≫ k.inv, fun x => by simp, fun x => by simp⟩
  refine ⟨post.trans e₀, fun σ x => ?_, fun x p hp => ?_, fun x b hb => ?_⟩
  · show e₀ ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) ≫ k.hom) = X6Kummer.conicGal σ (e₀ (x ≫ k.hom))
    rw [Category.assoc]; exact he₀g σ (x ≫ k.hom)
  · rw [hagree]; exact he₀p (x ≫ k.hom) p hp
  · rw [hagree]; exact he₀i (x ≫ k.hom) b hb

/-- **Row H-43 (`x6ConicModel`) from `r1r2`, Elkies' model `ElkiesConicX6` and `MobiusGlue`** (the kernel
proves `MobiusGlue` from T5: `LeafQM.AV.CurveGlue.mobiusGlue_of_T5`). -/
theorem x6ConicModel_of_elkies (hR : LeafAdopt.R1R2fpRep) (hC : ElkiesConicX6) (hM : Pin.MobiusGlue) :
    X6Kummer.X6ConicModel :=
  x6ConicModel_of hR (conicOfWitness_of_elkies hC
    (coarseCompare_of (coarseFactor_of_rep' hR) CurveSplit.curveBijIso) (hauptmodulUniqueX6S_of hM))

/-- Conversely the row gives the leaf-form (so `ElkiesConicX6` is not stronger than the row). -/
theorem elkiesConicX6_of (h : X6Kummer.X6ConicModel) : ElkiesConicX6 := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, ⟨h1f, -, h6, h2, -⟩, hc⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1f, h6, h2, hc⟩

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.x6ConicModel_of_elkies
#print axioms HDec.QMSplit.Moduli.elkiesConicX6_of

namespace HDec.QMSplit.Moduli

/-- **Row H-43 with `MobiusGlue` discharged from T5** (`PkgI2.TorsionStructure`, the bundle's T5 form; the
kernel's `LeafQM.AV.CurveGlue.mobiusGlue_of_t5`, image-plane). -/
theorem x6ConicModel_of_elkies_t5 (hR : LeafAdopt.R1R2fpRep) (hC : ElkiesConicX6)
    (hT : PkgI2.TorsionStructure.{0}) : X6Kummer.X6ConicModel :=
  x6ConicModel_of_elkies hR hC (LeafQM.AV.CurveGlue.mobiusGlue_of_t5 hT)

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.x6ConicModel_of_elkies_t5

/-! ## `PairsLift` from T5; row H-1 with `PairsLift` discharged -/

namespace HDec.QMSplit.Moduli

/-- **coarse-factor's `PairsLift` is a theorem from T5** (`ShimuraSplit.pairsLift_of_T5`). -/
theorem pairsLift_of_t5 (hT : PkgI2.TorsionStructure.{0}) : PairsLift :=
  ShimuraSplit.pairsLift_of_T5 (ObjBridge.torsionStructure_iff.2 hT)

/-- **Row H-1 (`r1r2`) from its printed parts and T5**: `PairsLift` discharged. -/
theorem r1r2fpRep_of_printed_t5 (hD : DeligneComponentsX6) (hE : GeomConnOfAlgClosure)
    (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathX6') (hR : ReciprocityCanonical)
    (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRep :=
  r1r2fpRep_of_printed hD hE (pairsLift_of_t5 hT) hB hR hG

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.pairsLift_of_t5
#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of_printed_t5

/-! ## All rows of this task (except `shimuraFamily`, in `ShimuraFam.lean`, and `r3`) from one bundle -/

namespace HDec.QMSplit.Moduli

/-- **The new leaves of shimura-split** (besides `ShimuraHolFamily`, stated over TailU in
`ShimuraFam.lean`), with T5 as in the bundle. -/
structure ShimuraSplitLeaves : Prop where
  deligneX6 : DeligneComponentsX6
  geomConn : GeomConnOfAlgClosure
  t5 : PkgI2.TorsionStructure.{0}
  babaGranath : BabaGranathX6'
  reciprocity : ReciprocityCanonical
  gonzalezRotger : GonzalezRotgerX6
  gonzalezRotgerCount : ShimuraSplit.GonzalezRotgerCountX6
  deligneY3 : ShimuraSplit.DeligneComponentsY3
  elkies : ElkiesConicX6

/-- **Rows `r1r2`, `r1rec`, `r5`, `r5count`, `y3Connected`, `x6ConicModel` from the bundle.** -/
theorem rows_of_shimuraSplitLeaves (L : ShimuraSplitLeaves) :
    LeafAdopt.R1R2fpRep ∧ LeafQM.AV.R1rec ∧ LeafQM.AV.R5fp ∧ LeafQM.AV.R5fpCount ∧
      TSHecke.Y3Connected ∧ X6Kummer.X6ConicModel := by
  have hR := r1r2fpRep_of_printed_t5 L.deligneX6 L.geomConn L.t5 L.babaGranath L.reciprocity
    L.gonzalezRotger
  exact ⟨hR, r1rec_of_r1r2 hR, r5fp_of_r1r2 hR, r5fpCount_of_points L.gonzalezRotgerCount,
    y3Connected_of_deligne L.deligneY3, x6ConicModel_of_elkies_t5 hR L.elkies L.t5⟩

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.rows_of_shimuraSplitLeaves

/-! ## The row statements, fully qualified (the bundle fields' types; leaf-fold8 §2) -/

example : HDec.LeafAdopt.R1R2fpRep → _root_.LeafQM.AV.R1rec := HDec.QMSplit.Moduli.r1rec_of_r1r2
example : HDec.LeafAdopt.R1R2fpRep → _root_.LeafQM.AV.R5fp := HDec.QMSplit.Moduli.r5fp_of_r1r2
example : ShimuraSplit.GonzalezRotgerCountX6 → _root_.LeafQM.AV.R5fpCount :=
  HDec.QMSplit.Moduli.r5fpCount_of_points
example : ShimuraSplit.DeligneComponentsY3 → HDec.TSHecke.Y3Connected :=
  HDec.QMSplit.Moduli.y3Connected_of_deligne
example : HDec.LeafAdopt.R1R2fpRep → HDec.QMSplit.Moduli.ElkiesConicX6 → PkgI2.TorsionStructure.{0} →
    HDec.X6Kummer.X6ConicModel := HDec.QMSplit.Moduli.x6ConicModel_of_elkies_t5
example : HDec.QMSplit.Moduli.DeligneComponentsX6 → HDec.QMSplit.Moduli.GeomConnOfAlgClosure →
    HDec.QMSplit.Moduli.PairsLift → HDec.QMSplit.Moduli.BabaGranathX6' →
    HDec.QMSplit.Moduli.ReciprocityCanonical → HDec.QMSplit.Moduli.GonzalezRotgerX6 →
    HDec.LeafAdopt.R1R2fpRep := HDec.QMSplit.Moduli.r1r2fpRep_of_printed
example : HDec.QMSplit.Moduli.DeligneComponentsX6 → HDec.QMSplit.Moduli.GeomConnOfAlgClosure →
    PkgI2.TorsionStructure.{0} → HDec.QMSplit.Moduli.BabaGranathX6' →
    HDec.QMSplit.Moduli.ReciprocityCanonical → HDec.QMSplit.Moduli.GonzalezRotgerX6 →
    HDec.LeafAdopt.R1R2fpRep := HDec.QMSplit.Moduli.r1r2fpRep_of_printed_t5

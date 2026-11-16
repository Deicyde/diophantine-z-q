/-! ### The producers of the weak row (pi0-fold, from pi0-prune's `tools/base_producers.lean`)

The chain's `r1r2fpRep_of` (TailU), `coarseX6OfFine_of`, `canonicalCoarseX6_of`, `r1r2fpRep_of_split{,5,6}`,
`r1r2fpRep_of_printed{,_t5}` (TailZ20), `r1r2_of_published` and `x6Rows_of_leaves` (above) with the clause `R1pi0Props`
removed from the intermediate statements `CoarseX6OfFine`, `CanonicalCoarseX6`, `GeomConnX6` (each weak form with its
implication from the original); the base witness `(Y, Φ, X, Ψ, fY)` with `R1fpProps ∧ X6Props` comes from
`GonzalezRotgerX6` (González–Rotger 2006 Thm 5.12 on the canonical `X₆`, already an input of `r1r2fpRep_of_printed`)
instead of `geomConnX6_of hD hE`. No new hypothesis: every leaf here is one of `r1r2_of_published`'s. -/

/-- `CoarseX6OfFine` (TailU) without the clause `R1pi0Props X`. -/
def CoarseX6OfFineW : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → R1heckeProps Y Φ →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
      (fY : Y ⟶ X), X6Props Y Φ X Ψ fY ∧ (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x)

theorem coarseX6OfFineW_of (h : CoarseX6OfFine) : CoarseX6OfFineW := by
  intro Y Φ h1 hh
  obtain ⟨X, Ψ, fY, h6, hs, -⟩ := h Y Φ h1 hh
  exact ⟨X, Ψ, fY, h6, hs⟩

/-- `r1r2fpRep_of` (TailU 1914-1921) for the weak row; the proof without the clause `R1pi0Props`. -/
theorem r1r2fpRep_ofW (hE : CanonicalModelY3) (hH : HeckeOfFine) (hX : CoarseX6OfFineW)
    (hP : HauptmodulOfX6) (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : LeafAdopt.R1R2fpRepW := by
  obtain ⟨Y, Φ, h1⟩ := hE
  have hh := hH Y Φ h1
  obtain ⟨X, Ψ, fY, h6, hsurj⟩ := hX Y Φ h1 hh
  obtain ⟨π₆, h2, ht⟩ := hP Y Φ X Ψ fY h1 h6
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hR Y Φ h1, ⟨ht, hsurj⟩, h5 Y Φ X Ψ fY h1 h6⟩

/-- `r1r2fpRep_of'` (TailU 2267-2270) for the weak row. -/
theorem r1r2fpRep_of'W (hE : CanonicalModelY3) (hX : CoarseX6OfFineW) (hP : HauptmodulOfX6)
    (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_ofW hE heckeOfFine_proof hX hP hR h5

/-- `CanonicalCoarseX6` (TailZ20 185) without the clause `R1pi0Props X`. -/
def CanonicalCoarseX6W : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x)

theorem canonicalCoarseX6W_of (h : CanonicalCoarseX6) : CanonicalCoarseX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, hs, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, hs⟩

/-- `coarseX6OfFine_of` (TailZ20 212-219) for the weak forms. -/
theorem coarseX6OfFine_ofW (hC : CanonicalCoarseX6W) : CoarseX6OfFineW := by
  intro Y Φ h1 _
  obtain ⟨Y₀, Φ₀, X, Ψ, fY₀, h1₀, h6₀, hsurj⟩ := hC
  obtain ⟨g, hg⟩ := compare_iso h1₀ h1
  refine ⟨X, Ψ, g.hom ≫ fY₀, x6Props_transport g hg h6₀, fun x => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hsurj x
  exact ⟨y₀ ≫ g.inv, by rw [Category.assoc, Iso.inv_hom_id_assoc, hy₀]⟩

/-- `canonicalModelY3_of_coarse` (TailZ20 1723-1726) for the weak form. -/
theorem canonicalModelY3_of_coarseW (hC : CanonicalCoarseX6W) : CanonicalModelY3 := by
  obtain ⟨Y, Φ, -, -, -, h1, -⟩ := hC
  exact ⟨Y, Φ, h1⟩

/-- `pairsLift_of_canonical` (TailZ20 1026-1028) for the weak form. -/
theorem pairsLift_of_canonicalW (h : CanonicalCoarseX6W) : PairsLift := by
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, hs⟩ := h
  exact pairsLift_of_witness h6 hs

/-- `coarseCompare_of_canonical` (TailZ20 1089-1090, through `coarseFactor_of_canonical'`) for the weak form. -/
theorem coarseCompare_of_canonicalW (hC : CanonicalCoarseX6W) : CoarseCompare :=
  coarseCompare_of (coarseFactor_of (pairsLift_of_canonicalW hC) factorThroughSurj_proof) CurveSplit.curveBijIso

/-- `r1r2fpRep_of_split` (TailZ20 1749-1753) for the weak forms. -/
theorem r1r2fpRep_of_splitW (hC : CanonicalCoarseX6W) (hB : BabaGranathX6) (hR : LeafQM.AV.R1rec)
    (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of'W (canonicalModelY3_of_coarseW hC) (coarseX6OfFine_ofW hC)
    (hauptmodulOfX6_of hB (coarseCompare_of_canonicalW hC)) (reciprocityOfFine_of_r1rec hR)
    (residueOfX6_of_r5fp h5)

/-- `GeomConnX6` (TailZ20 1770) without the clause `R1pi0Props X`: the base witness of the moduli clause lists. -/
def GeomConnX6W : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY

theorem geomConnX6W_of (h : GeomConnX6) : GeomConnX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

/-- **The base witness from González–Rotger's leaf** (no Deligne, no `GeomConnOfAlgClosure`). -/
theorem geomConnX6W_of_gr (hG : GonzalezRotgerX6) : GeomConnX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := hG
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

/-- `canonicalCoarseX6_of` (TailZ20 1776-1784) for the weak forms. -/
theorem canonicalCoarseX6_ofW (hG : GeomConnX6W) (hL : PairsLift) : CanonicalCoarseX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6⟩ := hG
  refine ⟨Y, Φ, X, Ψ, fY, h1, h6, fun x => ?_⟩
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Ψ x)
  obtain ⟨P, hP⟩ := hL Q
  obtain ⟨y, hy⟩ := (Φ Qbar).surjective (M3.mk P)
  refine ⟨y, Ψ.injective ?_⟩
  rw [h6.2.2.2.2.2 y P hy, hP, hQ]

/-- `r1r2fpRep_of_split5` (TailZ20 1789-1791) for the weak forms. -/
theorem r1r2fpRep_of_split5W (hG : GeomConnX6W) (hL : PairsLift) (hB : BabaGranathX6)
    (hR : LeafQM.AV.R1rec) (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_splitW (canonicalCoarseX6_ofW hG hL) hB hR h5

/-- `r1r2fpRep_of_split6` (TailZ20 1820-1823) for the weak forms. -/
theorem r1r2fpRep_of_split6W (hG : GeomConnX6W) (hL : PairsLift) (hB : BabaGranathX6')
    (hR : LeafQM.AV.R1rec) (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_split5W hG hL (babaGranathX6_of hB) hR h5

/-- **`r1r2fpRep_of_printed` (TailZ20 1855-1859) without `hD` and `hE`**: the base witness from `hG`. -/
theorem r1r2fpRep_of_printedW (hL : PairsLift) (hB : BabaGranathX6') (hR : ReciprocityCanonical)
    (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRepW := by
  refine r1r2fpRep_of_split6W (geomConnX6W_of_gr hG) hL hB (r1rec_of_reciprocityCanonical hR) ?_
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, h5⟩ := hG
  exact ShimuraSplit.r5fp_of_point ⟨Y, Φ, X, Ψ, fY, h6, h5⟩

/-- `r1r2fpRep_of_printed_t5` (TailZ20 1937-1941) without `hD` and `hE`. -/
theorem r1r2fpRep_of_printed_t5W (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathX6')
    (hR : ReciprocityCanonical) (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_printedW (pairsLift_of_t5 hT) hB hR hG

/-- **The row `r1r2` (weak form) from published-form leaves**: `r1r2_of_published` (TailZ21 1420-1433) without
`hD : ShimuraGlue.DeligneComponentsX6Printed` and `hE : GeomConnOfAlgClosure`. Every hypothesis is a hypothesis of
`r1r2_of_published`: T5 (`PkgI2.TorsionStructure`), Baba–Granath (`BabaGranathRational`), the ray-class consequence
`RayClassCM` and González–Rotger Thm 5.12 (`GonzalezRotgerX6`). -/
theorem r1r2_of_publishedW (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
    (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_printed_t5W hT (babaGranathX6'_of_rational' hB) (ShimuraGlue.Ray.reciprocityCanonical_of_rayClass hR) hG

/-- `x6ConicModel_of_published` (TailZ21 1435-1441) without `hD` and `hE`. -/
theorem x6ConicModel_of_publishedW (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
    (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) (hC : ElkiesEquationsX6) :
    X6Kummer.X6ConicModel :=
  x6ConicModel_of_elkies_t5 (r1r2_of_publishedW hT hB hR hG) (elkiesConicX6_of_equations hC) hT

/-- `X6Leaves` (TailZ21 1444-1451) without `deligneX6P` and `geomConn`. -/
structure X6LeavesW : Prop where
  t5 : PkgI2.TorsionStructure.{0}
  babaGranathR : BabaGranathRational
  rayClass : ShimuraGlue.Ray.RayClassCM
  gonzalezRotger : GonzalezRotgerX6
  elkiesEq : ElkiesEquationsX6

/-- `x6Rows_of_leaves` (TailZ21 1453-1456) for the weak row, without the two leaves. -/
theorem x6Rows_of_leavesW (L : X6LeavesW) : LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel :=
  ⟨r1r2_of_publishedW L.t5 L.babaGranathR L.rayClass L.gonzalezRotger,
    x6ConicModel_of_publishedW L.t5 L.babaGranathR L.rayClass L.gonzalezRotger L.elkiesEq⟩

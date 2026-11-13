
/-! ## The piece from leaves -/

namespace G0X1Belyi

/-- **`X1BelyiOnModel` from the two x1-belyi leaves** (glue, proved): `BelyiX1` from
`X1Belyi.TorsionStructure` (T1, Silverman AEC Cor. III.6.4(b), UNVERIFIED number) and
`X1Belyi.GoodReductionUnramified` (T2, Serre–Tate 1968 Thm 1 / Néron–Ogg–Shafarevich,
UNVERIFIED number) by `X1Belyi.belyiX1_of_leaves`, then transport along `ℚ(X) ≅ K_N`
(`x1BelyiOnModel_of_belyiX1`). -/
theorem x1BelyiOnModel_of_leaves (hT : X1Belyi.TorsionStructure)
    (hG : X1Belyi.GoodReductionUnramified) : HSyn.G0Split.X1BelyiOnModel :=
  x1BelyiOnModel_of_belyiX1 (X1Belyi.belyiX1_of_leaves hT hG)

/-- The same from the bundle `X1Belyi.X1Leaves` of x1-belyi. -/
theorem x1BelyiOnModel_of_x1Leaves (L : X1Belyi.X1Leaves) : HSyn.G0Split.X1BelyiOnModel :=
  x1BelyiOnModel_of_leaves L.torsion L.goodRed

end G0X1Belyi

end

#print axioms G0X1Belyi.x1BelyiOnModel_of_belyiX1
#print axioms G0X1Belyi.x1BelyiOnModel_of_leaves
#print axioms G0X1Belyi.x1BelyiOnModel_of_x1Leaves

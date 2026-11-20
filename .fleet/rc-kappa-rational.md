# Fixed parametrization scale

**Scoped stop.** Lean proves that a rational morphism on `X0Branch.model (newformLevel (Ecurve ℓ))` whose complex values equal the fixed `phiAn` on a width-one cusp tail forces `∃ c : ℚ, (c : ℂ) = κ`. The coefficients at degrees `-2` and `-3` of the rational affine coordinates are `κ⁻²` and `-κ⁻³`, so the witness is their negative ratio. The base already gives the reverse implication for the whole interior chart.

`ZInQKernel/Contrib/OneProof/RC/KappaRational/FixedScale.lean` passed serial `lake env lean -j1 -DautoImplicit=false`. All six axiom checks report only `propext`, `Classical.choice` and `Quot.sound`. The report `docs/research/rc-kappa-rational.md` gives the exact local hypothesis, the scout, and the unchanged consumer inputs. No new print or named assumption.

The remaining step at tex 1785–1787 and 1825–1828 is to supply the independently chosen rational map and identify its values on that tail, or give its rational Laurent pullback differential at the already fixed scale. The typed BCDT and Milne declarations supply no such map. The existing audit notes that Milne's cited pair at tex 1784 covers the map to the elliptic curve and its Jacobian quotient, but does not supply the specific newform statement or the Hecke equality at tex 1788. Nothing here requires a numerical value or integrality of a Manin constant. Once the local match is supplied, the scalar input of the prepared values, Stage Kummer and rough (3.4) is discharged; CM field of definition remains separate.

Final proof and report SHA: `ee0e48f6226b8a4f519ea64c9618bafe5487af04`.

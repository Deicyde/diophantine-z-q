/-
Cloud batch 3 W16 H99: exact rational-point leaf.
Recovered from sources/owned/RationalPoint.lean in the H99-H150 V3a packet.
The supporting theorem is the rational-section consequence of Stacks Tag 04KV,
ported from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
See CloudB3W16Connected/NOTICE.md and LICENSE for source attribution.
-/

import ZInQKernel.Contrib.OneProof.H.TailP
import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint

open CategoryTheory AlgebraicGeometry

/-- A connected scheme with a rational section is geometrically connected.
This proves the exact `AVGlue.GeomConnOfRationalPoint` statement without
additional hypotheses; its finite-type and quasi-compact assumptions are unused. -/
theorem geomConnOfRationalPoint_proof : AVGlue.GeomConnOfRationalPoint := by
  intro k _ X f s hs _hft _hqc hc
  have : ConnectedSpace X := hc
  exact AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section f s hs

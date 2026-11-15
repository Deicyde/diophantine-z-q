# p1-quot results log

Target: `HDec.MCRGlue.QuotientP1Coordinate` (ZInQKernel/OneProof/H/TailW.lean L202), bundle field
`HDec.HSyn.OpenGlue7.quotientP1Coordinate`. Base 24f97774 (wip/w72).

## Setup
- Build tree: copied (cp --reflink) from ~/dzq-wt/yu-prune-base (c2ad4181); diff to base in ZInQKernel/ is
  docstring-only in LPrefix/TailA/C/F/H plus TailZ33/Main/two contributions (VERIFIED by git diff).

## Port0/Port1 (mcr-quot over the chain)
- Port0.lean = header (import TailW + CloudW07 ProjectiveLine.Geometry/RelativeCoordinates, namespace HDec,
  TailW's attribute line) + MCRQuot.lean L4406-end (mcr-glue parts 5-6, mcr-quot parts 1-24) minus #print.
  34 errors: name resolution only (ImagePlane.*, curveFacts, smoothStalkDimOne under namespace HDec;
  transportLevel ambiguous Pin vs HDec.G0ModField), plus a stray `end HDec`.
- Port1.lean = Port0 with `_root_.LeafQM.AV.Pin.` qualification of those names: VERIFIED compiles, exit 0, no
  errors (port1_out.txt). So all of mcr-quot holds verbatim over the chain's constants (HDec.MCRGlue.*).

## P1SchemeQ (P1Test.lean)

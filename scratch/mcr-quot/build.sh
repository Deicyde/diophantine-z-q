#!/bin/bash
# MCRQuot.lean = MCRGlue.lean (verbatim) + parts, in this order
cd "$(dirname "$0")"
cat ../mcr-glue/MCRGlue.lean MCRQuot1.lean.part MCRQuot2.lean.part MCRQuot3.lean.part \
  MCRQuot4.lean.part MCRQuot5.lean.part MCRQuot6.lean.part MCRQuot6b.lean.part MCRQuot7.lean.part \
  MCRQuot8.lean.part MCRQuot8b.lean.part MCRQuot10.lean.part MCRQuot11.lean.part MCRQuot12.lean.part MCRQuot13.lean.part MCRQuot9.lean.part > MCRQuot.lean

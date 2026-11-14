#!/bin/bash
# MCRQuot.lean = MCRGlue.lean (verbatim) + parts
cd "$(dirname "$0")"
cat ../mcr-glue/MCRGlue.lean MCRQuot*.lean.part > MCRQuot.lean

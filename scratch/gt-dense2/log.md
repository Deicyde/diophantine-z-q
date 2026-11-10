# gt-dense2 log
- 04:27 merged origin/wip/gt-import (90d1e0c, report: GreenTaoVendor builds, no sorry).
- moved drafts SetWeight, PrimeModulusTransference, Assembly to ZInQKernel/External/GreenTaoDense/ unchanged; bridge appended to root; draft/Bridge.lean deleted.
- added ZInQKernel/MainGreenTao.lean (two variants), import line in ZInQKernel.lean.
- lake build ZInQKernel: success (9847 jobs, 5m22s wall incl. vendored library). No edits to the drafts were needed.
- #print axioms greenTaoDense and both variants: [propext, Classical.choice, Quot.sound]. check_target.py: OK.

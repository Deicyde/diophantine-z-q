# Construction sources

The selected Brox source files under `inputs/jose/` are copied unchanged from
[José Brox's repository](https://github.com/JoseBrox/diophantine-z-q_improvements)
at commit `cd474ee67104586c9d71885a7c95e8a21f12ca0c`. Their exact original bytes
are identified in `INPUTS.json`.
Brox's repository distributes this material under the Creative Commons
Attribution 4.0 International license; the pinned license is retained at
`inputs/jose/LICENSE`. The original paper authorship and notices remain in the
source files.

The data under `inputs/carbon/` and the explicit decimal table were supplied by
Gemini Carbon for this project. The explicit construction uses Brox's additive
framework and is credited to Carbon and Brox in the manuscript. The 195-variable
construction is Brox's reduction of the retained Conant-based parent.

The verification scripts in this directory were written independently for this
project. They read the selected source data as inert JSON and TeX; they do not
import or execute the upstream construction programs. Moving them from the
scratch audit into the repository changes their paths and output handling, not
the underlying identities they check.

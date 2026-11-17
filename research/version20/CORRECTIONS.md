# Version 19 backlog in Version 20

This inventory records the Version 19 entries in [issue 129](https://github.com/elliotglazer/diophantine-z-q/issues/129)
and Elliot's additional wording instructions. “Corrected” means the stated
edit is present in this candidate, not that independent review has accepted it.
No listed item is deferred. Earlier released files remain unchanged.

The seven reviewer notes are preserved in [the original PR147 backlog comment](https://github.com/elliotglazer/diophantine-z-q/issues/129#issuecomment-6937654226),
against head `86b83260525aadc6cfa616fe78e4fa0746d2e9b6`. They were nonblocking
notes, not findings that invalidate the accepted polynomial.

| Entry | Class/scope | Disposition and location |
| --- | --- | --- |
| `44011213563-1-astra-V19-N1` | C, navigation | Corrected in the Version 20 dependency map: effective sums are consumed by `v19:250-soundness`. The released Version 19 map is preserved. |
| `44011213563-1-fable-n1-secant-wording` | C, omitted explanatory calculation | Corrected in `v19:195-reduction`: the two secant relations are combined explicitly without dividing by the slope; the constants are `kappa` and `lambda`, not the slope. |
| `44011213563-1-fable-n2-scalar-divisibility-citation` | C, overstrong unused citation | Corrected in `v19:250-soundness`: the text uses the actual `c >= 149^L_N` lower bound and the retained height bound. The later inequality needs no stronger divisibility assertion. |
| `44011213563-1-fable-n3-deleted-rows-meaning` | C, explanation | Corrected in the retained parent construction: the two coordinates and their defining rows are printed, and the four replaced rows containing them are identified. |
| `44011213563-1-fable-n4-verify250-input-weight` | Verification coverage | Corrected in `construction/verify250_retained.py`: input 1 is checked absent from the nontrivial weights and powers, and the printed exponent table is parsed and compared. |
| `44011213563-1-fable-n5-verify250-mapping-fallback` | Verification coverage | Corrected in the same new checker: mappings use strict lookup, with regressions rejecting each of deleted coordinates 119 and 120 in an unchanged row. |
| `44011213563-1-fable-n6-formal-log-homomorphism` | C, explanatory proof | Corrected in `v19:sum-height`: integrating the invariant differential gives the formal identity; convergence on positive-valuation parameters justifies it at every finite place, including above 2. |
| [Carbon omission from AI usage](https://github.com/elliotglazer/diophantine-z-q/issues/129#issuecomment-6941309459) | B, attribution | Corrected in the AI usage paragraph: Gemini 4 Carbon is included, with the approved first sentence and “the polynomials.” |
| [Two edition-relative phrases](https://github.com/elliotglazer/diophantine-z-q/issues/129#issuecomment-6941309857) | C, wording | Corrected: the 196/198 heading names Version 18; the 214 attribution says “This retained section.” Historical contributors remain credited. |
| [OpenAI agent-name order](https://github.com/elliotglazer/diophantine-z-q/issues/129#issuecomment-6941808127) | C, naming | Corrected to “6 Astra and 6.1 Sol” in the approved AI usage statement. |
| Elliot's “Gemini 4 Carbon” instruction | B/C, attribution naming | Corrected throughout the new manuscript and current release documentation. Frozen historical records retain their bytes. |
| Elliot's 195 wording instruction | C, quantifier clarity | Corrected where the fixed result was called a family. The result is one quartic with Busy Beaver coefficients; genuine parameterized intermediate constructions remain described as such. |

Gate, kernel and contributor-guide notes in issue 129 concern other repository
components. They are not Version 19 manuscript corrections and remain in their
own backlog. This candidate does not silently mark those notes resolved.

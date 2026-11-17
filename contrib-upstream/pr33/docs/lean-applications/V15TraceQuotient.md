# V15 retained contact and the actual trace quotient

This native root-package application formalizes the existing V15 contact-domain argument
and its proposed trace quotient. The external-open-problem KPI is zero.
Independent source review and protocol acceptance remain pending. No manuscript,
accepted helper, frozen target, existing application contract or earlier review
disposition is changed.

`ZInQKernel/Contrib/V15RetainedContact.lean` proves, for every rational `t,q`, that
`(1+q) P5((t-1)^2) = ((t-1)^2)^5` implies `q != 0`. Both the expanded
polynomial and its five literal contact factors are checked. It then proves
`x102 != 0` for every rational raw224 tuple satisfying the ten specified rows
and every rational `A != 0`. The parameter-family endpoint allows every integer
`N`, using nonvanishing of `149^(2*N+1)`; it introduces no effective threshold.

`ZInQKernel/Contrib/V15RawRows.lean` contains every literal summand of the 197 parent residuals
and 196 target residuals. Small row definitions and lookup blocks are only
their representation. `ZInQKernel/Contrib/V15TraceQuotient.lean` applies the ten-row result to
the actual parent coordinates, derives `Q != 0` from row 47, proves the
substitution identity for every parent row, and constructs an equivalence
between the full rational solution sets of these two explicit row families.
The points have types `Fin 223 -> Q` and `Fin 222 -> Q`; `coord` exposes the
source's one-based indices without adding a free coordinate. Both maps fix
all 221 retained coordinates, including physical input coordinate 1.

## Mathematical sources and exact bindings

All source paths below are under
`research/version15/quartics/quartic-222/provenance/` at
`elliotglazer/diophantine-z-q@511529bbe9d635194f0c9d925709e77a5d3afa64`.

| Source | SHA-256 |
| --- | --- |
| `detector-q-nonzero-107/PROOF.md` | `d1d33a5a937fe00df6b008835c058759ccb6c575ee547e297dffc55064da16e5` |
| `detector-q-nonzero-107/REQUIRED-ROWS.json` | `6d04f2f063e3d903abdcf5c769180389a716fa360a0ced6467287aed9451977f` |
| `shared-T-redundancy224-006/candidate224-ir.json` | `6b961988414509ff6619fb674b696c745b098d00ad2af326df43e4db5aa5d39f` |
| `joint-root-factor-110/candidate223-ir.json` | `0839eb623c76ba462eec8842dc5b8c85fef85cc924c9daa98f35a83ae61948e0` |
| `trace-quotient222-116/raw222-ir.json` | `34974cb8e9c274fa7612d93603224fa02fd0fc13ceb37f55eb0be8dce91b7bce` |

The consumer is `trace-quotient222-116/PROOF.md`, which explicitly describes
an author proposal pending independent acceptance. Formal verification of
this local chart does not supply that protocol acceptance.

| Application obligation | Constructed inputs and derivation |
| --- | --- |
| Source hypotheses | `Raw224Ten` is exactly rows 9,43,44,45,46,56,57,68,71,73, with the sole parameter hypothesis `A != 0`. No root or trace row is used for contact nonvanishing. |
| Constructed objects | `P5`, `obstruction`, `Retained`, the two literal residual families, `coord`, and the two coordinate maps are explicit definitions in the three modules. |
| Domain and index coverage | The contact variables and every source coordinate range over all rationals. The solution predicates quantify over all 197 and 196 row IDs, respectively. `row_substitution` covers every parent ID 1 through 197. |
| Transition maps | Raw224 slots 98,99,100,101,102,113,114,125,126,128 bind to parent slots 92,93,94,95,96,107,108,119,120,122; slots 1 and 55 are fixed. The parent-to-target map sets new slot 222 to `Z/Q`; the reverse sets old slots 222 and 223 to `R2*U` and `Q*U`. |
| Consumed-object identity | Parent `q=x96`, `Q=x98`, `R2=x119`, `G=x222`, `Z=x223`. Row 47 is `q^2-Q=0`. Row 186 is `Q*G-R2*Z=0`. Rows 196 and 197 are the literal special-trace and other-trace definitions, not arbitrary predicates. |
| Coefficients and normalization | The obstruction is `3813373161796*(P5(S^2)-S^10)`. Rows 56 and 57 yield the scalar quartic with five positive coefficients. Row 71 forces `R != 0` before row 68 supplies `T=R^2 != 0` and division by `T` is used. Mathlib's `den_dvd_of_is_root` and `num_isRoot_scaleRoots_of_aeval_eq_zero` are applied directly, with `IsFractionRing.den`; no identification with `Rat.den` is asserted. |
| Local conditions | All 1,061 parent and 1,059 target coefficient terms are represented. The checked substitution makes precisely parent row 186 the zero polynomial, and shifts subsequent row IDs down by one. |
| Exceptional cases | No trace or `U` is inverted. There is no positivity hypothesis on `q`, no `q+1 != 0` hypothesis and no added inverse guard. The audit includes the valid normalized local contact `t=1,q=-1`; it is not a full-system existence witness. |
| Downstream consumption | `raw223_retained`, `raw223_q_nonzero` and `raw223_Q_nonzero` discharge the denominator used by `to222`. `row_substitution`, `reverse_solution`, both inverse identities and `forward_solution` are consumed by `solutionEquiv`. |

## Contributor-declared coverage and application index

This is an author/contributor declaration of the existing argument, not a
reviewer reconstruction or acceptance record. Every entry marked `awaiting`
awaits eligible independent non-author review, as do all source-use matches,
application links, exclusions and the complete composition. Source-first initial
reconstruction, its provenance and reconciliation, and separate coverage,
application and assembled-proof decisions remain pending under Protocol_D.
The nine-obligation table above is the shared application contract for U1–U18;
the records below locate its actual suppliers, derivations and consumers. No
new mathematical claim, proof route or independent approval is supplied here.

### Frozen inputs and excerpt convention

The current mathematical-module packet is pinned at
`30a68253217ff0b7d6ae9dcd00f75ef563c683ab`, after merging upstream main
`a5937595cde3e3db00975b81e5171cdef92c801a`. `C`, `R`, `Q` denote the
following native root-package application files. Their declaration bodies,
starting at `namespace V15RetainedContact`, are byte-identical to the historical
proof packet `2ed35f8e55f57b49578ab01325ec262387ce28af`; only license locators
and the two local module imports changed. The audit also prints the expanded
contact and actual-denominator closures. All local application declaration
names below remain in namespace `V15RetainedContact`.
The [historical author index](https://github.com/loning/diophantine-z-q/blob/f2298824f5244c61a09a20bcc20fd267fe05e660/lean/Examples/V15TraceQuotient.md)
and its original bindings remain historical evidence, not acceptance of this
native packaging. This table and the coverage/excerpt bindings below describe
the current files; no independent decision has been carried forward.
The source table above keeps
its base pin `511529bbe9d635194f0c9d925709e77a5d3afa64`; its five SHA-256
bindings are reused, not replaced. These are mathematical data/argument sources,
not independent review evidence.

| Input at current mathematical-module packet | Whole-file SHA-256 |
| --- | --- |
| `C` = [V15RetainedContact.lean](../../ZInQKernel/Contrib/V15RetainedContact.lean) | `aa8d07c624946c576c8c2f743db1300e6b9b7074c38fb23ad3b38d612753b816` |
| `R` = [V15RawRows.lean](../../ZInQKernel/Contrib/V15RawRows.lean) | `a96af3462692a97f3022038030adb53ea8c0ede51effb12922d037e03eb4543e` |
| `Q` = [V15TraceQuotient.lean](../../ZInQKernel/Contrib/V15TraceQuotient.lean) | `5b4c71fedff1979aa70f892329a04143afb5296036485f35c055127df3cad3ef` |
| `ZInQKernel/Contrib/V15TraceQuotientAxioms.lean` | `288c48d67a689fad9ad5edffb74e31ca6ed88c56f447a5a0ce17a48095555ad6` |
| `docs/lean-applications/V15Application.LICENSE` | `45404ee75576b053a86e89e545fd6987a607107cf4d846fa78dcb6a233d53447` |

Hashes bind raw Git blob bytes, decoded as UTF-8 only for reading; no whitespace,
JSON, Unicode or newline normalization is performed. Ranges are inclusive,
one-based physical lines delimited by byte `0a`, retaining each selected line's
terminator (and any preceding `0d`). An excerpt is exactly the concatenation of
those selected byte lines. All C/R/Q blobs use LF and end with LF. Thus, for
example, the digest of `git show <pin>:<path>` bytes split with
`splitlines(keepends=True)`, sliced `[lo-1:hi]` and rejoined with `b""` reproduces
each table entry. Whole-file excerpts use every byte, including the last newline;
source JSON is never parsed for hashing. This document has no self-hash and is
not itself a frozen mathematical supplier.

The downstream source is the base-pinned
`trace-quotient222-116/PROOF.md` (same provenance directory as above), whole-file
SHA-256 `9cd304aee28f53efb9fc963b801a947b6e66851db99067c0a3ca2521c345fdab`; its paragraphs beginning “Forward map”, “Reverse map”
and “Keep one coordinate” are the chart assertions addressed by U12–U18.
Its additional weighted-polynomial, height and arithmetic assertions are outside
this application and are not supplied by `solutionEquiv`.

Mathlib is the existing pin `56a005855ea17e0b0958f73ec801ae140b0a1679`.
`M` denotes `Mathlib/RingTheory/Polynomial/RationalRoot.lean`, whole-file SHA-256
`a25773fa3c0a63c87f3a19988512d27b1ee01b54ce58fb39d8b7191dc5d42c6c`.
The two substantive imported suppliers used directly by U1 are bound with their
local contexts and complete proofs:

| Source excerpt at Mathlib pin | SHA-256 |
| --- | --- |
| `M:34–55`, `num_isRoot_scaleRoots_of_aeval_eq_zero`, including ring/localization context | `5ffc4770f670a9dba9c7a7055c95afc1f4e61b2121364236cce7a4613c9c1bec` |
| `M:60–109`, `den_dvd_of_is_root`, including fraction-ring/UFD context | `0d20b10bf98b9d2e54ddfe03c4a4a0140f3cdf44a178caf3ecf6e23b805e3e84` |

These are pinned library results, not a claim to have checked a separate
publication or the complete Mathlib proof closure. The governing local
Protocol_D v1.4 is unchanged, SHA-256
`3d16c4d58d030ff745460386b081eb21c8c0d3f375cbfb06c4f9777c235a12f9`.

### Complete declared passage partition

Each C/R/Q line belongs to exactly one range below, including all statement,
proof, construction and mathematical-prose passages. `outside` means outside
the mathematical argument for the reason in that row; assessment of each
exclusion also awaits eligible independent review. `awaiting` always means
awaiting eligible independent review, never reviewed or accepted. Grouped
literal definitions and unnamed proof blocks remain within their listed range.

| ID | Frozen passage | Declared role and source-use/application links | Excerpt SHA-256 |
| --- | --- | --- | --- |
| C01 | `C:1–5` | outside: module and license notice | `62327ec805d84243f6bd9efd2605101840263e8335f86f2d4b82038700b0aa81` |
| C02 | `C:6–27` | awaiting: source/claim and normalization prose; U1–U4 | `d7ab5d0b5230a5ee8f784a46dd8dca92d0e1d1d878e40936a37a8b453f73efef` |
| C03 | `C:28–44` | outside: imports, options, sections and namespace syntax; dependencies identified below | `df31f9fcdff40021b70cfac3aaf3507fc263b7f4ce837a93b0abf139406c2316` |
| C04 | `C:45–55` | awaiting: `P5`, `obstruction` definitions; U1–U2 | `caff7a407f92f8e67e2fb99a9fe949e5838bb3b33021e2ebd28b63fd9ad27afe` |
| C05 | `C:56–87` | awaiting: `obstruction_no_rational_root`, entire proof including `hmod`; U1 | `abde9f82f2da42cb2a0053b10bf2465efb9080162a16fd2ef500f80e09f86d1c` |
| C06 | `C:88–108` | awaiting: `contact_nonzero`, `contact_product_nonzero`, including inline `hp`; U2 | `9f33dc5f4f5e609d222162809b20f95267aa251355234d62244f46140b57ae1c` |
| C07 | `C:109–123` | awaiting: `Retained` and all ten conjuncts; U3 | `bb7147d13f92c792d843b187dce4f5b63431dfc91e4f6ed0ce800c70629e59e4` |
| C08 | `C:124–172` | awaiting: `retained_nonzero`, entire proof and unnamed intermediate algebra; U3 | `eca094c34c2c85978b394ec84c5ac7ebb6952ad4f791e2bee317387e876732a0` |
| C09 | `C:173–180` | awaiting: `Raw224Ten`, `raw224_q_nonzero`; U4 | `2c08f2602b6e04e893888b9f980f9ba70375bcded188df73872668fb2c677e02` |
| C10 | `C:181–184` | awaiting: `raw224_family_q_nonzero`; U4 | `a834168bc4b0efbb1d4c18d2e2881d94ecbfa97824b57f0fa3f57a9484c2c668` |
| C11 | `C:185–185` | outside: namespace close | `5bc00a450bc879e5ec1c97d5bc62409de76c9778f3151aa120bc0bc4ce81ec45` |
| R01 | `R:1–7` | outside: module, license and rational-type import syntax | `858e522bbf0dd6bda19abaa8993bb4287845795f992ff65a36b3ffa002441708` |
| R02 | `R:8–24` | awaiting: literal-family and deletion claim prose; U5–U7, U13 | `a2ad5d14ceee66224a7eaa602121ec456067c90919e136d27620162c82c477d4` |
| R03 | `R:25–29` | outside: exposure/section and namespace syntax | `8d037f4e7e2308ea7e19a79df62dbb3a669d60eccc1745243130f114bbe7acbe` |
| R04 | `R:30–620` | awaiting: all `raw223Row_1` through `raw223Row_197` literal definitions; U5 | `bc71bf50999f43d38b1318a29c5506e7e5003c8cd56560f0dcd8c9076005ce55` |
| R05 | `R:621–875` | awaiting: all `raw223RowBlock0` through `raw223RowBlock12`, `raw223Row`; U7 | `a4d5a055182844beb48832d827f3996b3d67427a57495562ea68c8ba06cdd6e6` |
| R06 | `R:876–1463` | awaiting: all `raw222Row_1` through `raw222Row_196` literal definitions; U6 | `0c9b9682a4affa584974b193e63a3a8bebf6d596c263ed8b105d8e27830bbe16` |
| R07 | `R:1464–1716` | awaiting: all `raw222RowBlock0` through `raw222RowBlock12`, `raw222Row`; U7 | `8e0dfc12a93d93e1caecdae77837e714c3e4f1d5b8317385a4f9b337307c7125` |
| R08 | `R:1717–1718` | outside: blank line and namespace close | `f1a86215ddb17a66d66ed2cc0df20bc9c35e3e98dc55827ed5e2869bd7f4f9c3` |
| Q01 | `Q:1–8` | outside: module, license and local import syntax | `7424ae5a356cedb074bdf300cc6e9e1789e6aa6679ec3a3fa2f66d0a1184aa0c` |
| Q02 | `Q:9–23` | awaiting: chart statement, source and exceptional-case prose; U8–U18 | `d272b9fe65d0d87ea90e99ea6870082ee8d7d0ea25554bf0c10d66e965b30cd7` |
| Q03 | `Q:24–32` | outside: options, section and namespace syntax | `f07133c4d555f4f878e2bfef6a2297da51b540267f59e5c8dfd0ffca1b2d5acf` |
| Q04 | `Q:33–42` | awaiting: `coord`, `Raw223Solution`, `Raw222Solution`; U8 | `ac95c6fb9600dc104d581607071219a47769f197784e21f7df398b0e8b9c47ae` |
| Q05 | `Q:43–69` | awaiting: `raw223_retained`, including all ten row-extraction proof blocks; U9 | `ed390af55df931b6fb8fe0e68bf7a15f5f201248ced7de691b885bab0ccfdd85` |
| Q06 | `Q:70–73` | awaiting: `raw223_q_nonzero`; U10 | `0123ce196fb2781177092d3a0be060ddaa6c835f069d0097584abb49900dda1a` |
| Q07 | `Q:74–82` | awaiting: `raw223_Q_nonzero` and row-47 proof; U11 | `faacadab3a603454150e9b2f485fdb466570a7f9a9d2ef2509c1caeca678215c` |
| Q08 | `Q:83–93` | awaiting: `to222`, `to223`; U12 | `e2e64a0d6653aef0e98fcb642de590411080c019e28329233a44114424537ebf` |
| Q09 | `Q:94–106` | awaiting: `forward_coordinates`, `reverse_coordinates`, entire proofs; U12 | `288f50bccccb2f64ca88e0be750edb8a6671213d1c7cf126f3a93ac0b365efac` |
| Q10 | `Q:107–113` | awaiting: `row_substitution`, including all interval cases; U13 | `8fc52fe9d8497f6272da71b20add119b0d2e5de21702c9e5bbe0054511c50a97` |
| Q11 | `Q:114–122` | awaiting: `reverse_solution`, all branches; U14 | `454a50e8fc3e81bcb09f0ae37c4b8e0b7c0d06af1fbadac65bab0be86eff0503` |
| Q12 | `Q:123–142` | awaiting: `reverse_forward`, all coordinate branches; U15 | `d667b4fbce301e7e670313e399370ed7e5d2f521e8d7154a30eb66d484eddbfa` |
| Q13 | `Q:143–155` | awaiting: `forward_reverse`, all coordinate branches; U16 | `a64551c492fdeb217f62ba7b5ee444f9de8bf82fa32daf50d194c9739d7034f7` |
| Q14 | `Q:156–173` | awaiting: `forward_solution`, both row-index branches; U17 | `5a020fb5cf23e93307c03892c86d19796ef89bb6459796eb456a531a6d07d434` |
| Q15 | `Q:174–181` | awaiting: `solutionEquiv`, including all four structure-field proof/application blocks; U18 | `1eb4a7d4994c6ff5c7142f6216d18eee029c0d64db02d16dd46fa231ff99d686` |
| Q16 | `Q:182–182` | outside: namespace close | `5bc00a450bc879e5ec1c97d5bc62409de76c9778f3151aa120bc0bc4ce81ec45` |

There are 35 disjoint ranges: 26 awaiting review and 9 outside the mathematical
argument. The audit file (all 42 lines, whole-file hash above) is outside the
three-module argument: lines 1–39 implement/print a scoped axiom check, and
lines 40–42 give only the local `t=1,q=-1` example. That example is no supplier
to the chart and no full-system existence witness. The license (all 201 lines,
whole-file hash above) supplies redistribution terms, not a mathematical premise.
This document's reproduction code is operational guidance, not a proof passage.

### Declared direct source uses and existing derivations

Every row below is `awaiting eligible independent review`. A supplier in the
DIRECT column is actually used by the stated consumer; an ancestor is not
substituted for an immediate supplier. Definition unfolding, normalization and
elementary algebra stay in the existing named proof or indicated inline block;
they are not new fact nodes. The C/R/Q coverage ranges bind the complete
construction, application and consuming passages by excerpt hash above.
The available result, needed assertion and derivation are summaries pointing
to those existing proofs, not duplicated proofs or a fresh mathematical review.

| Use | Available result and needed assertion | DIRECT supplier(s) → consuming declaration(s) | Existing derivation / application location |
| --- | --- | --- | --- |
| U1 | A root of `p : ℤ[X]` in `ℚ` has `IsFractionRing.den ℤ s` dividing the leading coefficient; its numerator is a root of the denominator-scaled polynomial. Needed: no rational root of the actual `obstruction`. The required commutative domain/UFD, field, algebra and fraction-ring instances are `ℤ`, `ℚ` with the standard embeddings; `p=obstruction`, `s` is arbitrary rational and `hs` is the assumed root equation. | `M:60–109 den_dvd_of_is_root`, `M:34–55 num_isRoot_scaleRoots_of_aeval_eq_zero`, `obstruction` → `obstruction_no_rational_root`. | C04–C05: degree 8 and leading coefficient `-35893742479489` are computed before the applications at C:65,73. The leading coefficient is nonzero mod 5, so the actual denominator is nonzero mod 5; the scaled-root equality is cast to `ZMod 5` and contradicted by inline exhaustive `hmod` at C:80–86. No conversion to `Rat.den` is used. |
| U2 | U1 excludes the root equation obtained when `q=0`. Needed: nonzero `q` from either the expanded or five-factor contact equation, for every rational `t,q`. | `obstruction_no_rational_root`, `P5`, `obstruction` → `contact_nonzero`; `contact_nonzero`, `P5` and inline `hp` → `contact_product_nonzero`. | C06: C:93–96 applies U1 at `s=t-1` and uses scalar `3813373161796`; C:103–108 uses the exact five-factor equality `hp`, proved by `ring`, then invokes `contact_nonzero`. Neither result assumes a sign or inverse guard. |
| U3 | The source `detector-q-nonzero-107/PROOF.md`, sections “R and T cannot vanish” / “Normalize the retained detector”, and `REQUIRED-ROWS.json` specify ten equations. Needed: `R≠0 ∧ T≠0 ∧ q≠0` for all rational inputs and `A≠0`. | `Retained`, `P5`, `contact_nonzero` → `retained_nonzero`; the ten source rows supply the explicit `Retained` definition. | C07–C08: the actual conjunction is destructured; row 9 gives `inputSq≥0`, rows 56/57 give the five-positive-coefficient quartic, row 71 and `A≠0` give `R≠0`, then row 68 gives `T≠0`. The inline `t=a/T`, `r=b/T` calculations at C:144–170 normalize rows 43/44/73/45/46 and feed `contact_nonzero` directly at C:171. |
| U4 | U3 returns all three nonvanishings. Needed: raw224 slot 102 nonzero for all rational `A≠0`, and for every integer `N` in `A=149^(2*N+1)`. | `Retained` → `Raw224Ten`; `retained_nonzero`, `Raw224Ten` → `raw224_q_nonzero`; `raw224_q_nonzero`, Mathlib `zpow_ne_zero` → `raw224_family_q_nonzero`. | C09–C10: use exactly raw224 rows 9,43,44,45,46,56,57,68,71,73 with slots 1,55,98,99,100,101,102,113,114,125,126,128; project `.2.2` of U3. C:183 supplies base nonzero by `norm_num` to `zpow_ne_zero`; all integer `N` remain allowed, with no threshold. This is a separate endpoint, not the direct supplier of U10. |
| U5 | Base-pinned `joint-root-factor-110/candidate223-ir.json`, entire row family, supplies the explicit parent residuals. Needed: all 197 literal polynomials in rational `A` and one-based `x : ℕ → ℚ`. | That JSON, rows 1–197 → `raw223Row_1` through `raw223Row_197`. | R04 is the complete literal coefficient/parameter-power/coordinate specification, without a new proof. Used directly by `raw223RowBlock0` through `raw223RowBlock12` (U7); the full family reaches U9/U11/U13/U15 through `raw223Row`. |
| U6 | Base-pinned `trace-quotient222-116/raw222-ir.json`, entire row family, supplies the explicit target residuals. Needed: all 196 literal polynomials over the same rational domain. | That JSON, rows 1–196 → `raw222Row_1` through `raw222Row_196`. | R06 is the complete literal specification; direct consumers are `raw222RowBlock0` through `raw222RowBlock12` (U7), then `raw222Row` reaches U13. No weighted sum-of-squares identification is asserted. |
| U7 | U5/U6 give all row definitions. Needed: row dispatch on the complete intervals 1–197 and 1–196. | Each `raw223Row_i` / `raw222Row_i` → its respective `raw223RowBlockk` / `raw222RowBlockk`; those 13 blocks per family → `raw223Row` / `raw222Row`. | R05/R07 use `(i-1)/16` and `(i-1)%16`, with zero outside the guarded interval. These are the actual supplier definitions unfolded in U9/U11/U13/U15 and the predicates in U8; no sampled-row claim substitutes for the complete families. |
| U8 | Rational tuples have types `Fin 223 → ℚ` and `Fin 222 → ℚ`. Needed: one-based source coordinates and solution predicates covering every row. | Inline bounded-index construction → `coord`; `coord`, `raw223Row` → `Raw223Solution`; `coord`, `raw222Row` → `Raw222Solution`. | Q04 uses `i-1` with the explicit bounds (zero outside), and quantifies over every row ID 1–197 / 1–196. This supplies the same objects used in U9–U18, without a spare coordinate or any existence premise. |
| U9 | A `Raw223Solution A x` supplies every parent equation. Needed: the exact ten-conjunct `Retained` on parent coordinates. | `Raw223Solution`, `coord`, `raw223Row` with its blocks/literals, `Retained` → `raw223_retained`. | Q05 extracts rows 9,43,44,45,46,56,57,68,71,73 and normalizes each literal polynomial. Raw224 slots 98,99,100,101,102,113,114,125,126,128 become parent 92,93,94,95,96,107,108,119,120,122; 1 and 55 stay fixed. No raw224-to-raw223 whole-system equivalence is used. |
| U10 | U9 supplies the exact `Retained` tuple; U3 gives its nonvanishings when `A≠0`. Needed: actual parent `q=coord x 96≠0`. | `raw223_retained`, `retained_nonzero` → `raw223_q_nonzero`. | Q06 passes precisely U9's tuple and the same rational `A≠0` to U3, then projects `.2.2`. It does not invoke the raw224 endpoint U4. |
| U11 | U10 gives `q≠0`; parent row 47 is `q²-Q=0`. Needed: actual `Q=coord x 98≠0`. | `raw223_q_nonzero`, `Raw223Solution` row 47, `raw223Row` with blocks/literals → `raw223_Q_nonzero`. | Q07 normalizes row 47 and uses `sq_nonneg` / `nlinarith` to contradict U10 if Q vanishes. This supplies the nonzero denominator required by U15/U16 for the map defined in U12. |
| U12 | The base trace proof's “Keep one coordinate” / map paragraphs specify `U=Z/Q`, `G=R2*U`, `Z=Q*U`. Needed: concrete maps fixing coordinates 1..221. | `coord` and inline `Fin` constructions → `to222`, `to223`; `to222` → `forward_coordinates`; `to223` → `reverse_coordinates`. | Q08–Q09 define the maps on all rational tuples and prove the retained-coordinate identities by `omega`, `simp`, `congr`. Parent `Z=x223`, `Q=x98`, `R2=x119`, `G=x222`; target `U=y222`. Division is total as a definition; using it as an inverse on solutions requires U11 via U15/U16, not an extra definition hypothesis. |
| U13 | U5–U8/U12 supply literal rows, coordinates and reverse substitution. Needed: equality for every parent row and every rational `A,y`, with row 186 identically zero. | `raw223Row`, `raw222Row`, all their lookup blocks/literals, `coord`, `to223` → `row_substitution`. | Q10: `interval_cases i` covers all 1≤i≤197; `norm_num` unfolds the whole families and `ring` proves each identity. The exact target index is `i` for i<186 and `i-1` for i>186. No solution hypothesis or nonzero parameter is required here. |
| U14 | U13 is a whole-family identity; `hy` vanishes on every target row. Needed: a parent solution from each target solution for every rational `A`. | `row_substitution`, `Raw222Solution` → `reverse_solution`. | Q11 splits i=186, i<186 and i>186; the deleted row is zero, and `omega` supplies the target bounds for i or i-1. Every parent row is restored. |
| U15 | U11 gives `Q≠0` for a parent solution with `A≠0`; parent row 186 is `Q*G-R2*Z=0`. Needed: `to223 (to222 x)=x` on that same tuple. | `raw223_Q_nonzero`, `Raw223Solution` row 186, `raw223Row` with blocks/literals, `coord`, `to222`, `to223` → `reverse_forward`. | Q12 performs function extensionality, treats slots 222/223 explicitly, and uses `field_simp [hQ]`; `linear_combination -ht` supplies G's identity. All retained coordinates reduce by `simp`. It does not invert any trace or U. |
| U16 | U14 makes `to223 y` a parent solution; U11 gives its Q nonzero when `A≠0`. Needed: `to222 (to223 y)=y` on the original target solution. | `reverse_solution`, `raw223_Q_nonzero`, `coord`, `to223`, `to222` → `forward_reverse`. | Q13 obtains Q nonzero on that very reconstructed parent, simplifies to the unchanged target slot 98, and cancels only Q in slot 222; other coordinates reduce by `simp`. No target-solvability assumption beyond `hy` is introduced. |
| U17 | U13 supplies row identities; U15 identifies the reconstructed parent with the original parent solution. Needed: all 196 target equations for `to222 x`. | `row_substitution`, `reverse_forward`, `Raw223Solution` → `forward_solution`. | Q14 uses parent index j for target j<186 and j+1 otherwise, rewrites by U15, and applies the original parent solution. Thus no target row is missed or consumed on a different tuple. |
| U18 | U17/U14 supply the two solution-preserving maps; U15/U16 supply both inverse identities. Needed: the equivalence of these exact full rational solution subtypes for each rational `A≠0`. | `to222`, `forward_solution`, `to223`, `reverse_solution`, `reverse_forward`, `forward_reverse` → `solutionEquiv`. | Q15 binds the two maps and their proofs in `toFun`/`invFun`; `Subtype.ext` uses the corresponding inverse identities in `left_inv`/`right_inv`. This is the local 197-to-196 row chart, with coordinates 1..221 fixed, including `q=-1` and zero-trace strata, and no trace/U inversion or whole-system existence conclusion. |

The only external theorem applications isolated as substantive suppliers here
are the two rational-root results in U1. Elementary field, order, polynomial,
finite-arithmetic and nonzero-power steps remain at their exact inline Lean
locations (including `zpow_ne_zero` in U4); this grouping is itself awaiting
independent coverage review. Imported modules and tactic implementation are
part of the pinned Lean/Mathlib trust base, not newly accepted project lemmas.
No claim is made that this declaration is a source-first reconstruction, that
all sources are independently complete, or that application, composition, CI,
release or external-open-problem acceptance has been obtained. This index
declares source bindings; the scoped compilation and replay
evidence is described below. Those checks do not supply independent coverage
or application acceptance.

## Scope and proof shape

These are independently authored applications of the cited mathematical
equations and pinned Mathlib results, not transplants of external Lean code.
Coefficient expansion, positivity, row normalization, rational-root
applications, finite arithmetic and the quotient identities follow the reuse
route. No new local escape witness, local freezing eligibility or mathematical
novelty is claimed. No implementation from the unlicensed third-party search
hits is imported or copied. The new source files have the accompanying Apache
2.0 license; source mathematics retains its original attribution. The pinned
trace-quotient proof credits `arithmetic_author` for the substitution packet,
H6 for normalization 109 and GI for trace organization 005. These mathematical
credits are distinct from the independently authored Lean implementation,
which was assisted by Codex CLI. The license bytes are unchanged from the
historical application.

This does not prove the complete Z-in-Q defining theorem, a final polynomial
identity, a coefficient-height bound, SixContactMin or CertifiedRank. It does
not identify the weighted sum-of-squares zero set, formalize the earlier
raw224-to-raw223 construction as a whole, or establish full-system existence.
The accepted helper snapshot is outside this application's import closure.
The current root imports are the three contribution modules and their pinned
Mathlib dependencies; no historical Examples provider or replacement fixture
is used.

## Scoped reproduction

Use the repository root package `z_in_q_kernel`, the committed root
`lean-toolchain` and `lake-manifest.json`: Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and all nine pinned Git
packages. The root and helper manifests agree on those Git revisions. Existing
compatible package caches were reused; no pin or dependency source was changed.
The default `ZInQKernel` target is unchanged. Current CI separately discovers
and builds every tracked `ZInQKernel/Contrib/*.lean` module.

From the repository root, build the real modules with ordinary Lake targets:

```sh
lake build --wfail +ZInQKernel.Contrib.V15RetainedContact \
  +ZInQKernel.Contrib.V15RawRows +ZInQKernel.Contrib.V15TraceQuotient \
  +ZInQKernel.Contrib.V15TraceQuotientAxioms
```

For a fresh scoped re-elaboration, use the same source files and native package
search paths, with a fresh output directory in front of them. The explicit
compiler options enable kernel checking and treat warnings as errors:

```python
import json, os, subprocess, tempfile
from pathlib import Path

root = Path.cwd()
manifest = json.loads((root / "lake-manifest.json").read_bytes())
for package in manifest["packages"]:
    if package["type"] != "git":
        continue
    folder = root / manifest["packagesDir"] / package["name"]
    assert subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=folder, text=True).strip() == package["rev"]
    assert not subprocess.check_output(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=folder)
(root / "build").mkdir(exist_ok=True)
out = Path(tempfile.mkdtemp(prefix="v15-native-", dir=root / "build"))
env = os.environ.copy()
env.pop("LEAN_SRC_PATH", None)
native_path = subprocess.check_output(
    ["lake", "env", "printenv", "LEAN_PATH"], cwd=root, text=True).strip()
env["LEAN_PATH"] = str(out) + os.pathsep + native_path
for name in ["V15RetainedContact", "V15RawRows", "V15TraceQuotient",
             "V15TraceQuotientAxioms"]:
    module = "ZInQKernel/Contrib/" + name
    target = out / (module + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["lean", "-j1", "-Ddebug.skipKernelTC=false",
                    "-DwarningAsError=true", "-o", str(target), module + ".lean"],
                   cwd=root, env=env, check=True)
```

The scoped audit checks every declaration originating in the three application
modules, including generated declarations, against exactly `propext`,
`Quot.sound` and `Classical.choice`. It prints eight endpoint closures,
including both contact forms and the actual `Q` denominator.

The native migration also receives an ordinary-import check of the exact public
statements, both coordinate-preservation lemmas and inverse identities. The
unmodified root `scripts/audit_kernel.lean` is used for a scoped replay of the
three real modules and a temporary exact-type specification: seven closed Prop
types cover the two contacts, two raw224 endpoints, parent q/Q nonvanishing
and all-row substitution; the full equivalence type is compared separately.
Those specifications are transient checks, not new mathematical library results.
Whole-project validation and required CI remain separate from this scoped audit.

On this native packet, the four-module Lake build with `--wfail`, fresh scoped
compilation with both explicit options above, and ordinary-import check all
exited 0 without warnings. The three-module declaration audit checked 1,355
declarations and all eight printed closures used exactly the three allowed
axioms. Native kernel replay checked 1,370 declarations (the three application
modules plus the temporary exact-type specification), with no runtime bodies
excluded, all seven Prop providers marked `proved_exact_type`, and the full
equivalence telescope checked. Its report explicitly says
`protocol_acceptance=false`.

Raw literal comparison matched every term in 197 parent / 196 target rows
(1,061 / 1,059 terms), and a separate polynomial comparison matched the ten
`Retained` conjuncts to the raw224 source rows. All 50 declared whole-file and
excerpt SHA-256 bindings and the 35 gapless passage ranges were checked.
These finite comparisons establish representation fidelity, not the arithmetic
theorem. The earlier preliminary CLI reviews at
`2ed35f8e55f57b49578ab01325ec262387ce28af` and
`4a08e757d20c481bb1fac51fa3194f2b87c821ee` keep their original scopes.
The earlier auxiliary-parser advisory remains limited historical evidence;
this contributor check does not independently close it or supply acceptance.

This non-release application does not update the current manuscript/PDF,
release profile, cumulative handoff, archive manifest or publication mirrors.
No record promotion or assembled-proof/research-release acceptance is requested.
Independent non-author source-first reconstruction and reconciliation, separate
coverage/application/composition decisions and final scoped closure are pending.
The authenticated designated `gpt-6-astra` controller's exact-revision
`Protocol / independent agent audit` and ordinary required checks, including
maintainer workflow approval where needed, remain external gates.

# h21-gchar: step (b) of the `h21C` verdict is closed in Lean. TYZ's `χ_{d₁,d₂}` is the Legendre-symbol character

**Main result.** The queue10 verdict rated `h21C` (`ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC`, TYZ Theorem 2.1 for
pairs) a composite GLUE statement with three steps. Step (b) was "the Legendre-symbol Hecke character (`gchar`) used in
Lean versus TYZ's class-field-theoretic `χ_{d₁,d₂}`". That step is now a Lean proof:

* **TYZ's `χ_{d₁,d₂}`** is defined over genuine objects (`IsTYZChi`, `tyzChi`, `tyzChiCl`). It is the character of
  `Cl_n = Gal(H_n/K_n)` attached to the quadratic extension `K_n(√d₂*)`, `d* = (−1)^{(d−1)/2} d`, where `H_n` is Tau
  Ceti's Hilbert class field. It is read on ideal classes through Tau Ceti's Artin map `Cl(K_n) ≃ Gal(H_n/K_n)`.
* **The equality** `tyzChiCl_eq_gchar` says that for odd squarefree `n` and `d₂ ∣ n` this character equals the
  statement's `gchar n (divSet n d₂) = Π_{q ∣ d₂} (N𝔞/q)` on every class.
* **The norm form**, the standard formula on ideals, is also proved:
  * `χ([𝔞]) = (d₂*/N𝔞)` (Jacobi symbol) whenever `N𝔞` is prime to `2d₂`;
  * on ideals with `N𝔞` prime to `2n`, also the `d₁`-side formula `(D₁/N𝔞)`, with `D₁ = d₁*` for `n ≡ 3 (mod 4)` and
    `D₁ = −4d₁*` for `n ≡ 1 (mod 4)`;
  * these values determine a function on `Cl(K_n)`.
* **The restatements.** `h21S` (h21c-steps) and `h21C` are restated with TYZ's character as `h21G = TYZThm21SpanG` and
  `h21PG = TYZThm21PairsG`. Each is proved equivalent to the statement it restates. The restated hypothesis does not
  depend on which factor carries the character (`tyzThm21SpanG_iff_swap`).
* **The fold check** of `Main.lean` compiles. Every new theorem depends only on `[propext, Classical.choice,
  Quot.sound]`.

**What remains of the verdict.**
* Step (a), `lcalSq = 𝓛²`, is task h21-lcal. My files are separate, so the two results can be combined.
* Step (c) was reduced by h21c-steps to the definition-level reading `π^U = ⊕ ℂ f_δ`.

**One caveat.** The TYZ source `~/tyz-src/Period7.tex` is **not on this host**. TYZ's own definition of `χ_{d₁,d₂}`
(near L510, per the notes) was therefore not re-read. Every TYZ line number below comes from the project notes and is
UNVERIFIED here. Two facts make this harmless:
* the two natural conventions, the character attached to `d₂` and the character attached to `d₁`, give the same
  hypothesis (proved in Lean);
* the two forms of the definition, class field theory and the norm formula, are proved equal.

Statuses: VERIFIED means compiled or read in the tree; STANDARD means published; UNVERIFIED means a line number recalled
from the notes.

## 1. TYZ's character: what is formalized

TYZ define the quadratic periods `P(d₁, d₂) = Σ_{t ∈ Cl_n} χ_{d₁,d₂}(t) f_n(t)` (L551–552, UNVERIFIED), where
`χ_{d₁,d₂}` is the genus character attached to `n = d₁d₂`. What the notes record about it (UNVERIFIED here):

* `χ_{n,1} = 1` (L510; h29-proof.md, h29-ne3.md).
* `χ_{d₁,d₂} = χ_{d₂,d₁}` for `n ≡ 3 (mod 8)` (L994–995).
* The proof of Theorem 2.1 states that `χ_{d₁,d₂}` is trivial on `K_{n,2}^×` iff `d₂* ≡ 1 (mod 8)` (rv-tyz-inputs §1.2,
  item 4).
* §3 uses the wording "the unique Hecke character over `K_n` associated to the extension `K_n(√d₁*)`" (L1304–1305,
  read by h33-sign).

All of these fit **`χ_{d₁,d₂}` = the character of `K_n(√d₂*)/K_n`**. This is the reading formalized here. §4 below shows
that the attachment to `d₁` gives the same hypothesis.

Lean (`scratch/h21-gchar/GChar.lean`, namespace `ZInQ.Contrib.H21GChar`):

| name | content |
| --- | --- |
| `dstar d` | `d* = d` if `d ≡ 1 (mod 4)`, else `−d`; `dstar_eq_neg_one_pow`: `= (−1)^{(d−1)/2} d` for odd `d` |
| `IsTYZChi n d₂ χ` | `IsExtChar n (dstar d₂) χ`: for `χ : Gal(H_n/K_n) →* ℤˣ`, every lift `ρ ∈ Gal(ℚ̄/ℚ)` of `t` multiplies every square root of `d₂*` by `χ(t)` (the tree's `TYZSplit.IsExtChar`) |
| `tyzChi n d₂` | the character with `IsTYZChi` (by choice; `1` if none exists) |
| `tyzChiCl n d₂ t` | `tyzChi n d₂ (art n t)`, where `art n = ringClassArtinEquiv (OK n) : Pic(𝒪_K) ≃* Gal(H_n/K_n)` is Tau Ceti's Artin map (built from the ray-class Artin map, `ringClassArtinEquiv_picClass`) |
| `IsTYZChiNorm n d₂ χ` | norm form: `χ([𝔞]) = jacobiSym (d₂*) (N𝔞)` for every integral `𝔞` with `N𝔞` prime to `2n` |

The definitions use only Mathlib, Tau Ceti and the tree's genus-theory files. No structure was invented for the
purpose.

## 2. The equality (step (b)); all VERIFIED, compiled

| theorem | statement |
| --- | --- |
| `isTYZChi_chiT` | `χ_{T(d₂)}` (`chiT n (divSet n d₂)`) is the character of `K_n(√d₂*)`; from `TYZSplit.isExtChar_chiT` and `prod_pstar_divSet` (`Π_{q ∣ d₂} q* = d₂*`) |
| `isTYZChi_unique` | the character of `K_n(√d₂*)` is unique (`isExtChar_unique`) |
| `tyzChi_eq_chiT` | `tyzChi n d₂ = chiT n (divSet n d₂)` |
| **`tyzChiCl_eq_gchar`** | `Odd n → Squarefree n → d₂ ∣ n → tyzChiCl n d₂ t = gchar n (divSet n d₂) t` |
| `jacobiSym_dstar` | `(d*/m) = (m/d)` for odd `d`, `m` (Mathlib's Jacobi reciprocity) |
| `exists_mk0_coprime'` | every ideal class contains an integral ideal of norm prime to `M` (`M > 1`) |
| `gchar_mk0_eq_jacobiSym` | `N𝔞` prime to `2d₂` ⇒ `gchar n (divSet n d₂) [𝔞] = Π_{q ∣ d₂} (N𝔞/q) = (N𝔞/d₂) = (d₂*/N𝔞)` |
| `isTYZChiNorm_unique`, `isTYZChiNorm_gchar`, `isTYZChiNorm_tyzChiCl` | the norm form determines the character, and both `gchar` and the class-field-theoretic `tyzChiCl` satisfy it |
| `jacobiSym_d₁_side` | for `N𝔞` prime to `2n`: `(D₁/N𝔞) = (d₂*/N𝔞)`, with `D₁ = d_K/d₂*` (`d₁*` or `−4d₁*`). The proof uses `(−n/N𝔞) = 1` (`TYZGenusFold.jacobiSym_neg_absNorm`) |

The pairs the consumer uses are all decompositions `n = d₁d₂` of squarefree `1 < n ≡ 1, 3 (mod 8)`. They are covered,
since the equality holds for every `d₂ ∣ n` with `n` odd and squarefree, and for every class.

## 3. The restated hypotheses

* `quadPeriodTYZ n τ f d₂ = Σ_{t ∈ Cl(K_n)} tyzChiCl n d₂ t · f(τ̂(clLift t))`, TYZ's `P(d₁, d₂)` with TYZ's
  character. `quadPeriodTYZ_eq` shows it equals the tree's `quadPeriod` for `d₂ ∣ n`.
* **`TYZThm21SpanG`** (`h21G`): `H21CSteps.TYZThm21Span` word for word, with `quadPeriod` replaced by `quadPeriodTYZ`.
  * Proved: `tyzThm21Span_of_G : TYZThm21SpanG → TYZThm21Span` and its converse `tyzThm21SpanG_of_span`.
* **`TYZThm21PairsG`** (`h21PG`): `TYZGenusFold.TYZThm21PairsC` with `quadPeriodTYZ`. This is for integration without
  h21c-steps.
  * Proved: `tyzThm21PairsC_of_G` and `tyzThm21PairsG_of_pairsC`; also `tyzThm21PairsG_of_spanG`.
* `TYZThm21SpanG₁` is the same with the character of `K_n(√d₁*)`, the other convention.
  * Proved: `tyzThm21SpanG_iff_swap : TYZThm21SpanG ↔ TYZThm21SpanG₁`.
  * For `n ≡ 3 (mod 8)` the two characters agree (`quadPeriod_div`).
  * For `n ≡ 1 (mod 8)` both clauses are symmetric under `d₁ ↔ d₂`, since `d₂ ≡ 1 ⇔ d₁ ≡ 1 (mod 8)`.
* Non-vacuity: test vectors exist for every admissible `τ` (h21c-steps' `exists_testVectorSpan`). The hypotheses of
  `h21G` are therefore satisfiable, as they are for `h21S`.

## 4. Fold and checks (all VERIFIED, compiled against `ZInQKernel.OneProof.Main` at base 6b97a5c7 + h21c-steps)

* `scratch/h21-gchar/GChar.lean`: 0 errors, no `sorry`. `#print axioms` for the eight main theorems gives
  `[propext, Classical.choice, Quot.sound]`. Output: `GChar-output.txt`.
* `scratch/h21-gchar/FoldCheck.lean` is generated by `mk_foldcheck.py`: the body of `GChar.lean` plus the hand fold.
  * `frozenTarget_h21G`: the body of `frozenTarget` with the binder `(h21C : …TYZThm21PairsC)` replaced by
    `(h21G : ZInQ.Contrib.H21GChar.TYZThm21SpanG)`, and both uses replaced by
    `(ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span (ZInQ.Contrib.H21GChar.tyzThm21Span_of_G h21G))`.
  * `frozenTarget_h21G'`: the same through the current `frozenTarget`.
  * `frozenTarget_h21PG`, `frozenTarget_h21PG'`: the alternative, with uses replaced by
    `(ZInQ.Contrib.H21GChar.tyzThm21PairsC_of_G h21PG)`.
  * All four depend only on `[propext, Classical.choice, Quot.sound]`. Output: `FoldCheck-output.txt`.
* `scratch/h21-gchar/Discharges.lean` (`#discharges`; output `Discharges-output.txt`):
  `DISCHARGES [h21C] by ZInQ.Contrib.H21GChar.tyzThm21PairsC_of_G, still assumes [ZInQ.Contrib.H21GChar.TYZThm21PairsG]`,
  axioms standard.
* Integration (`scratch/h21-gchar/autofold.json`):
  * move the content of `GChar.lean` into a new module, e.g. `ZInQKernel/Contrib/OneProof/TYZThm21GChar.lean`. Its
    imports are `OneProof.TYZSplit`, `Contrib.OneProof.TYZThm21Span` and `Contrib.OneProof.TYZGenusFold.Jacobi`, and it
    must not import `OneProof.Main`;
  * add the import to `Main.lean`;
  * apply the binder/argument replacement above.
* Kinds rows: `scratch/h21-gchar/kinds-rows.tsv`.
  * Row `h21G`: kind **consequence**, flag **pending review**, strict/strictest GLUE/GLUE. Step (a) is still open, so it
    is not yet a LEAF candidate. When h21-lcal closes step (a), the combined statement is Theorem 2.1 with the reading
    `π^U` of h21c-steps.
  * Row `h21PG` is the alternative.
  * Remove the `frozenTarget h21C` row, or the `h21S` row if h21c-steps is integrated first.
* Combining with h21-lcal: their restatement presumably changes `IsLcalSignC`/`lcalSq` in the same `∀ ℓ` clause. Mine
  changes only `quadPeriod` to `quadPeriodTYZ`. The two edits touch different subterms, and both directions of each
  dictionary are proved, so the combined statement follows by composing the two dictionaries.

## 5. What remains

* A reviewer's rating of `h21G`, and a check of TYZ's printed definition of `χ_{d₁,d₂}` (near L510) against
  `IsTYZChi`. If TYZ attach the character to `d₁`, `tyzThm21SpanG_iff_swap` covers it. If they define it on ideals by
  `(D/N𝔭)`, `isTYZChiNorm_tyzChiCl` and `jacobiSym_d₁_side` cover it.
* Locator row for `docs/research/locators.md` (for the integrator): TYZ arXiv:1411.4728v1, definition of
  `χ_{d₁,d₂}` near L510 and quadratic periods L551–552 (line numbers UNVERIFIED on this host; per h29-proof and
  h29-ne3).
* Not done: the Kronecker symbol at `2`. Mathlib has no Kronecker symbol, so the norm form is stated on odd norms.
  That is enough, because every class contains an ideal of odd norm prime to `n`.

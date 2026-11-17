# h21-combine: `h21S` replaced by `h21GP`, TYZ Theorem 2.1 with TYZ's genus character and TYZ's printed `𝓛²`

**Main result.** h21-gchar (step (b) of the queue10 verdict on `h21C`) and h21-lcal (step (a)) are combined into one
restatement of the `frozenTarget` hypothesis `h21S` (`ZInQ.Contrib.H21CSteps.TYZThm21Span`, h21c-steps):

* `h21GP = ZInQ.Contrib.H21Combine.TYZThm21SpanGP` (`ZInQKernel/Contrib/OneProof/TYZThm21GP.lean`): `h21S` word for
  word, with two changes.
  * The quadratic period is formed with TYZ's `χ_{d₁,d₂}`. This is the character of `Cl_n = Gal(H_n/K_n)` attached
    to `K_n(√d₂*)` through Tau Ceti's Artin map: `H21GChar.quadPeriodTYZ`.
  * The sign choices `ℓ(m)² = 𝓛(m)²` are taken against TYZ's printed `𝓛²`. That definition splits on
    `ord_{s=1} L(E_m, s)`, with the `L′/(Ω R)` branch, for every regulator function `R`: `H21Lcal.IsLcalSignPrinted R`.
* The equivalences, all proved in Lean:
  * `tyzThm21Span_of_GP : TYZThm21SpanGP → TYZThm21Span` and the converse `tyzThm21SpanGP_of_span`;
  * `tyzThm21SpanGP_iff_printed` (equivalence with h21-lcal's `TYZThm21SpanPrinted`);
  * `tyzThm21PairsC_of_GP`, the form `Main` reads.

  They compose h21-gchar's `tyzChiCl_eq_gchar` (TYZ's character = the Legendre-symbol `gchar`) with h21-lcal's
  `lcalSqPrinted_eq` (printed `𝓛²` = `lcalSq` on squarefree `m ≡ 1, 3 (mod 8)`, from root number `+1`).
* The fold into `ZInQKernel/OneProof/Main.lean` was done by hand, since `h21S` is a top-level binder: the binder
  `h21S` becomes `(h21GP : ZInQ.Contrib.H21Combine.TYZThm21SpanGP)`, and its two uses become
  `ZInQ.Contrib.H21Combine.tyzThm21PairsC_of_GP h21GP`.
* The kinds row `frozenTarget/h21S` is replaced by `frozenTarget/h21GP`, kind consequence, strict and strictest GLUE,
  flag "pending review (steps (a) and (b) of the queue10 verdict proved: h21-lcal, h21-gchar; step (c) InPiZ as
  h21c-steps left it; clause 1 rests on the corrected symmetric reading, readings/gee-tyz.md)".
* **Count neutral** (39 open; one GLUE row for another) until a reviewer rates `h21GP`. The integrator asked for the
  fold regardless.

Check results: §3 (filled in from `scratch/h21-combine/log.md`).

## 1. Files

| file | content |
| --- | --- |
| `ZInQKernel/Contrib/OneProof/TYZThm21GChar.lean` | h21-gchar's `scratch/h21-gchar/GChar.lean`, moved unchanged (namespace `ZInQ.Contrib.H21GChar`) |
| `ZInQKernel/Contrib/OneProof/H21Lcal.lean` | h21-lcal's `scratch/h21-lcal/H21Lcal.lean`, moved unchanged (namespace `ZInQ.Contrib.H21Lcal`) |
| `ZInQKernel/Contrib/OneProof/TYZThm21GP.lean` | new: `TYZThm21SpanGP`, the equivalences, `tyzThm21PairsC_of_GP`, `exists_isLcalSignPrinted` |
| `ZInQKernel/OneProof/Main.lean` | binder `h21S` → `h21GP`, its two uses, an import, and one docstring paragraph |
| `docs/one-proof/kinds.tsv` | row `h21S` → row `h21GP` (`scratch/h21-combine/kinds-row.tsv`) |
| `scratch/h21-combine/fold.py` | generator: reproduces the Main and kinds edits on any head that still has the `h21S` binder |
| `scratch/h21-combine/autofold.json` | the fold spec in the format of the earlier manual folds |

Merge hygiene:
* every scratch `.lean` of the two merged tasks is renamed `.lean.txt`, because they copy the declarations now in
  Contrib and their FoldChecks name an older `frozenTarget`;
* `scratch/h21-lcal/src/build.sh` now points at the `.lean.txt` names;
* there were no host paths and no vendored code.

## 2. The statement

`TYZThm21SpanGP` quantifies over:
* `R : ℕ → ℝ`;
* squarefree `1 < n ≡ 1, 3 (mod 8)`;
* admissible `τ`;
* `f` a `ℤ`-generator of `π_ℤ^{U_n}`, with `π^U = ⊕_δ ℂ f_δ` (`IsTestVectorSpan`);
* `ℓ` with `IsLcalSignPrinted R ℓ`;
* `d₁d₂ = n`.

It asserts:
* `quadPeriodTYZ n τ f d₂ = 0` when neither factor is `≡ 1 (mod 8)`;
* `quadPeriodTYZ n τ f d₂ = ±2^{#{p∣n}−1} (w/2) ℓ(d₁)ℓ(d₂)` when `d₂ ≡ 1 (mod 8)`.

Remarks:
* Non-vacuity of the premises:
  * test vectors exist (`H21CSteps.exists_testVectorSpan`);
  * for every `R` there is an `ℓ` with `IsLcalSignPrinted R ℓ` (`exists_isLcalSignPrinted`, a complex square root);
  * `𝓛(1)² = 1` (`H21Lcal.lcalSqPrinted_one`).
* Character on the other factor. h21-gchar proved that `TYZThm21SpanG` does not change if the character is attached to
  `d₁` instead (`tyzThm21SpanG_iff_swap`). Since `TYZThm21SpanGP ↔ TYZThm21Span ↔ TYZThm21SpanG`, the same holds for
  `h21GP`.
* What remains of the queue10 verdict:
  * step (c) (`InPiZ` against TYZ's `π_ℤ^{U_n}`) is read through Theorem 2.4(1) as h21c-steps left it;
  * clause 1 rests on the corrected symmetric reading (readings/gee-tyz.md, as in the existing `h21S` flag).
* Unread. The TYZ source (`~/tyz-src/Period7.tex`) is absent on this host too. TYZ's definition of `χ_{d₁,d₂}` (near
  L510) and of `𝓛` (L338–353) were therefore not re-read, and these line numbers are the project's transcriptions
  (UNVERIFIED).

## 3. Checks

(see `scratch/h21-combine/log.md`)

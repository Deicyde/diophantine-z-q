# tyz-decomp (2026-11-13)

**Main result.** The premise `ZInQ.Literature.TYZThm35ReadingA` (TYZ Theorem 3.5(2), `n ≡ 5 mod 8`, reading A)
now follows, by glue proved in Lean, from four leaves. Three are genuine, refereed and unambiguous statements
about TYZ's `𝓛` on the classes `1, 3 (mod 8)`. The fourth is the genus-point package of TYZ §3, kept as one
bundled leaf. And, given the three genuine leaves, **the package is equivalent to the premise**
(`genusPackage_iff_readingA`). So all the remaining content of reading A sits in the genus points. The package
cannot be split over Mathlib's definitions: Mathlib has no modular parametrization of `X₀(32)`, no CM points and
no ring class fields, so its objects are existential. Report: `docs/research/tyz-decomp.md`.

Leaves (`def … : Prop`, namespace `ZInQ.Contrib.TYZDecomp`):
- `TYZThm11Integral`: TYZ Thm 1.1 integrality.
- `TYZLcalOne`: `𝓛(1) = 1`.
- `TYZLemma29Mod2`: Lemma 2.9 with Prop 2.3, mod 2. The alternative `TYZThm11Mod2` also works.
- `TYZGenusPackage`: `∀ ℓ, IsTYZLcal ℓ → ∀ n ≡ 5 squarefree, Nonempty (PropN.GenusData ℓ n)`.
- `CurveA.TYZLemma316`: Lemma 3.16 over genuine definitions. Statable now, but not consumed by the glue.

`𝓛` is pinned by genuine definitions:
- `lcalSq m = L(C_m,1)/(2^{2k−3}Ω_m)`, with `Ω_m = (2/√m)∫₁^∞dx/√(x³−x)`.
- `IsTYZLcal` (sign choices; zero set on class 5).
- Readings A/B/C/D of Thm 3.5(2) are stated (`Thm35Reading`); `readingA_iff : Thm35ReadingA ↔ TYZThm35ReadingA`.

**What compiles.**
- New modules `ZInQKernel/Contrib/TYZDecomp/{Leaves,CurveA}.lean`: `lake build` OK.
- Drafts `scratch/tyz-decomp/{TYZDecomp,CurveA}.lean`: `lake env lean` OK.
- No `sorry`. Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

**Declarations proved** (namespace `ZInQ.Contrib.TYZDecomp`):
- `readingA_iff`, `not_reading_of`
- `omegaInt_pos`, `omegaInt_integrable`
- `lValOne_eq`, `isTYZLcal_lcalChoice`
- `lemma29Mod2_of_thm11Mod2`
- `tyzInputs_of_leaves`, `tyzThm35ReadingA_of_leaves` (and `'`)
- `genusData_nonempty_iff`, `genusPackage_iff_readingA`
- In `CurveA`: `nonsingular_iPt`, `lemma316_zero`, `slope_iPt`, `iPt_add` (`[i]` is additive), `iPt_iPt` (`[i]² = −1`)

**What remains (unproved / open).**
- No leaf is proved.
- Splitting the genus package into separate leaves needs four things (report §4.2):
  - the ℤ[i]-module `A(ℚ̄)` with pinned `τ`; only the additivity of `[i]` is done;
  - a pinned lifting `β'`;
  - ring class fields `H_{d,4}`, `ℍ'_n`;
  - CM points via the modular parametrization of `X₀(32) = A`.

**Caveats** (kept in the report and the docstrings):
- Reading A is printed only by Smith, arXiv:1603.08479, which is unrefereed.
- TYZ was read in arXiv v1 only, by AI agents. Its Theorem 1.2 (journal 1.4) is false read literally.
- Proposition N and the faithfulness arguments for `GenusData` were reviewed by AI only.
- `Period7.tex` is not on this host, so all line numbers are quoted from earlier notes. PARI is not installed, so no new numerics were run.
- An independent AI review found no blocker and 9 findings, all fixed.

# htmult-model (fleet note)

**Main result (VERIFIED, compiled, no sorry, axioms `[propext, Classical.choice, Quot.sound]`).** The Hodge–Tate
multiplicities `htMultE` do not depend on the finite coefficient model. New file
`ZInQKernel/Contrib/OneProof/HTModel.lean` (imports `PstModel`; does not import `ZInQKernel.OneProof.Main`;
nothing imports it yet), namespace `HDec.PkgI4.HTModel`:

- `tensorInvEquiv` / `finrank_tensorInv`: `(A ⊗ L^n)^H ≅ ((A ⊗ E^n)^H)^{[L:E]}` over `ℚ_p`, for any `ℚ_p`-module `A` with a `G_{ℚ_p}`-action, built on pb-dimform's `psi`/`phiE`.
- `htMultU_eq_of_basis`, `htMultE_eq_of_basis`, `htMultE_eq_of_le`: `htMultE ρ_L w = htMultE ρ_E w` for `ρ_L = ρ_E ⊗_E L` (scalars compared via `dim_{ℚ_p}`, `[L:E]`, `[E:ℚ_p]` and pb-fix3's `htMultE_eq_htMultU`).
- `htMultE_model_eq`: two finite models of one `ℚ̄_p`-valued `ρ` have equal multiplicities (via `E ⊔ E'`).
- `localDistinctHTP_iff_of_model`, `localDistinctHTP_iff_forall` (and `localDistinctHTU_iff_of_model`): Pan's `LocalDistinctHTP` on some model ⇔ on any given model ⇔ the same distinct pair on every model.

**Co-step cleared:** the Hodge–Tate model clause of `panPrintedF` (`LocalDistinctHTP` read "on some finite model").
The rating does not change on this alone; the Brinon–Conrad 9.2.10 step remains.

Proof only: no bundle field, statement or kinds row changed, no fold, no leaf added. On-the-spot (provenance (c)),
standard; the manuscript states the underlying direct-sum fact at L10976–10977 for the de Rham property.

**Manuscript issues:** no error found. Gaps filled: L719–723 / L735–739 / L756–757 (weights read on an arbitrary
finite coefficient field; now model-independent in Lean). Unverified: L756–757 Pan's other hypotheses (no network),
L10948–10950 "at every coefficient embedding" vs `htMultE` (standard, not formalized), L10996–11000 weight count.

**What remains:** nothing in scope. Not done (out of scope): wiring these lemmas into a consumer (proof only, no
fold). Report: `docs/research/htmult-model.md`; log and compile outputs: `scratch/htmult-model/`.

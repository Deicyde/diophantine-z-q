# t10-etale

**Main result.** T10 (Milne 1986, Thm 15.1; `H¹_et(A_K̄, ℤ_ℓ) ≅ Hom(T_ℓ A, ℤ_ℓ)`) is now stated in
its **Galois-equivariant form** over genuine definitions: `T10Etale.T10_TateDuality` in
`scratch/t10-etale/T10Etale.lean`. It was the last opaque leaf. The cohomology is Mathlib's
pro-étale `Scheme.EllAdicCohomology`; `AbVar`, `T_ℓ` and `galT` are the build's (Objects.lean).
Mathlib gives the cohomology only as an abelian group, so this task builds the missing structure
from Mathlib's own API (`Sheaf.H.map`, `Ext.mapExactFunctor`, `Equivalence.sheafCongr`,
`MorphismProperty.Over.map`):
- the **`ℤ_ℓ`-module structure** on `EllAdicCohomology`;
- **transport `e_*`** along scheme isomorphisms;
- the **Galois action** `galH σ`, transport along `1 × Spec(σ⁻¹)` on `A ×_K Spec K̄`.

Proved: `T10_TateDuality → T10_linIso → T10_groupIso` (leaf-push2's form).

**What compiles.** All of `T10Etale.lean` (543 lines). There is no `sorry`, and every declaration
uses only `propext`, `Classical.choice` and `Quot.sound`. Checks that it is not vacuous and is
correct, all proved in Lean:
- `H0Equiv : H⁰(X, ℤ_ℓ) ≃ₗ[ℤ_ℓ] C(X, ℤ_ℓ)` and `nontrivial_H0`: the module structure is the
  standard one, and the groups are not trivially zero;
- `T10_linIso_zero`: at the zero abelian variety the leaf says `H¹(Spec K̄, ℤ_ℓ) = 0`, which is true
  content;
- `transport_smul`: transport is `ℤ_ℓ`-linear;
- `transport_bijective`: transport is never degenerate;
- `transport_H0`: in degree 0, transport is `f ↦ f ∘ e⁻¹`, so the constant-sheaf isomorphism is the
  canonical one.

The σ against σ⁻¹ convention was argued by hand. One read-only model review (no human review)
re-derived it independently by a torsor computation and found no defect.

**What remains.**
- **Group-action laws for `galH`:** `transport_trans`, 150–250 lines; `galIso_inv_mul` is proved.
  They are optional and not needed to state the leaf.
- **The `ℚ_ℓ`/`V_ℓ` form:** about 100 lines, using the `TateModuleFree` leaf.
- **Proving the leaf (crowdsourcing):** very large. Étale cohomology of abelian varieties and the
  Bhatt–Scholze pro-étale/étale comparison are not in Mathlib.
- **Unverified citations:** the Milne sub-item number and the Bhatt–Scholze §5.6 number (no
  network).
- **Folding in:** replace `opaque T10_TateDuality` in Leaves.lean; this needs four extra Mathlib
  imports.

Report: docs/research/t10-etale.md. Log: scratch/t10-etale/log.md.

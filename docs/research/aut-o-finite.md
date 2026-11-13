# aut-o-finite: `AutOInnerFinite` is proved, and `Aut(𝒪)/Inn(𝒪^×)` has exactly four classes

Task aut-o-finite, 2026-11-13. Base 2dd83306 merged with `origin/wip/mobius-glue`. Scratch:
`scratch/aut-o-finite/` (results log `log.md`, compile outputs `run1.txt`, `run2.txt`). No file under
`ZInQKernel/`, `blueprint/` or another task's directory was edited. Model work only, no human review.

## 1. Result

**`LeafQM.AV.Pin.AutOInnerFinite` is proved in Lean.** No new hypotheses, leaves or glue Props are
needed (`scratch/aut-o-finite/AutOFinite.lean`; 0 errors; axioms
`[propext, Classical.choice, Quot.sound]`; VERIFIED, compiled):

```lean
def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)

theorem autOInnerFinite : AutOInnerFinite
```

The statement is copied verbatim, docstring included, from `scratch/mobius-glue/MobiusGlue.lean`
lines 419-428 (`diff` is empty; VERIFIED). It depends only on the kernel's maximal order
`LeafQM.O = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩ ⊆ LeafQM.B = (2, −3)_ℚ`, of discriminant 6
(`ZInQKernel/HDecomp/QM/Structures.lean`). The file imports only that module and
`ZInQKernel.HDecomp.Textbook.SkolemNoether`.

**The explicit computation (new, §9):**

```lean
theorem Exact.autO_mod_inner_exact : ∃ t : Fin 4 → (O ≃+* O),
    (∀ α : O ≃+* O, ∃ k, ∃ v : Oˣ, ∀ a : O, α a = (v : O) * t k a * ((v⁻¹ : Oˣ) : O)) ∧
    ∀ k l, (∃ v : Oˣ, ∀ a : O, t k a = (v : O) * t l a * ((v⁻¹ : Oˣ) : O)) → k = l
```

So `Aut(𝒪)` modulo conjugation by `𝒪^×` has **exactly four classes**. They are represented by
conjugation by `1, i, j, ij`, matching the Atkin–Lehner group `W ≅ (ℤ/2)²` for discriminant 6.
`Exact.autOInnerFinite'` derives `AutOInnerFinite` a second time, from this computation.

Status of the target: proved, with no leaves and no glue Props. Skolem–Noether is a kernel theorem
(`TSkolemKW.leafSkolemNoether : LeafSkolemNoether`, a `theorem` proved from Mathlib with no
hypotheses; VERIFIED by reading `ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`). The normalizer
step is elementary and proved in the file.

## 2. Proof

§7 and §8 are copied from `MobiusGlue.lean`, where task mobius-glue first proved
`autOInnerFinite`. Here they are extracted into a self-contained file and recompiled.

- **§7 (extension and Skolem–Noether).**
  - Every `α ∈ Aut(𝒪)` extends to `α̃ ∈ Aut_ℚ(B)`, by `α̃(b) = m⁻¹ α(m b)` with `m b ∈ 𝒪`
    (`extAlgEquiv`).
  - Skolem–Noether (`GlueDescent.B6_inner TSkolemKW.leafSkolemNoether`) gives `α̃ = c_u` with
    `u ∈ B^×`, and `u` normalizes `𝒪`.
- **§8 (normalizer).** Every `u ∈ B^×` normalizing `𝒪` is `q · v · t` with `q ∈ ℚ^×`, `v ∈ 𝒪^×` and
  `t ∈ {1, i, j, ij}`. The proof is a descent on `|nrd u|` after scaling `u` into `𝒪`:
  - a prime `p ∤ 6` dividing `nrd u` divides `u`, by an integer identity
    `6 x_l² = Σ λ · coord(u e_k ū)`;
  - `2 | nrd u` gives `u i⁻¹ ∈ 𝒪`, and `3 | nrd u` gives `u j⁻¹ ∈ 𝒪` (checks modulo 2 and 3 by
    `decide`).
- **§9 (exact count, new in this task).**
  - `rep_cover`: by §7 and the concrete normalizer statement, `α = c_v ∘ c_{t_k}`.
  - `rep_distinct`: if `c_{t_k} = c_v ∘ c_{t_l}`, then `w = t_l⁻¹ v⁻¹ t_k` commutes with `i` and
    `j`, so `w = r ∈ ℚ` (`comm_scalar`, a coordinate computation).
    - Hence `t_k = r · v · t_l`, and taking reduced norms, `nrd t_k = ± r² · nrd t_l`, since
      `nrd v = ±1` for `v ∈ 𝒪^×` (`nrd_unit`).
    - The reduced norms of `1, i, j, ij` are `1, −2, 3, −6`. So `(r · nrd t_l)² = ± nrd t_k · nrd t_l`,
      and for `k ≠ l` the right side is one of `±2, ±3, ±6, ±12, ±18`, never a rational square
      (`Rat.isSquare_iff`; `decide +kernel` on `ℤ`). This gives 24 cases.

## 3. Lean outcomes (VERIFIED; `scratch/aut-o-finite/log.md`)

| file | content | outcome |
|---|---|---|
| `AutOFinite.lean` §A | `AutOInnerFinite`, verbatim | text identical to source |
| §7, §8 | copied from `MobiusGlue.lean` (curve and T5 parts omitted) | compiled |
| §9 | `rep_cover`, `rep_distinct`, `autO_mod_inner_exact`, `autOInnerFinite'` | compiled |
| run2 | whole file | 0 errors, 9 linter warnings (unused `<;> norm_num` inherited from §8); 5 `#print axioms` all standard |

Notes:

- Plain `decide` on `¬IsSquare (6 : ℤ)` gets stuck on `Nat.sqrt`; `decide +kernel` works and adds no
  axiom (VERIFIED from the `#print axioms` output).
- Integration: §7-§9 need only `ZInQKernel.HDecomp.QM.Structures` and
  `ZInQKernel.HDecomp.Textbook.SkolemNoether`. They could go into `ZInQKernel/HDecomp/QM/` as one
  module, and `MobiusGlue.lean` §4 would then import it.

## 4. What remains

Nothing remains for this Prop. The consumers (`twistClassFinite`, `mobiusGlue_of_curves` in
`scratch/mobius-glue/`) still depend on `CurveRatFactor`, `CurveSurj` and the leaf
`TorsionStructure`, as `docs/research/mobius-glue.md` reports. Those are outside this task.

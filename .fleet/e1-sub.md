# e1-sub (2026-11-12): E1 glue for R16 — done in Lean

**Verdict:** the E1 glue for R16 is proved. `scratch/e1-sub/E1Sub.lean` (882 lines, imports only
kernel modules) compiles (`lake env lean`, exit 0, no `sorry`); every main theorem has axioms
`[propext, Classical.choice, Quot.sound]`. Hypotheses are only R16 (`R16_EichlerShimuraJ1'`) and the
kernel I3 leaves `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree` (+ `PoincareReducibility`
for the isogeny). Report: `docs/research/e1-sub.md`; log: `scratch/e1-sub/log.md`.

**What compiles**
- `vSurjOfSurjective : LeafModCurves.VSurjOfSurjective` (glue target of leaf-modcurves), via
  `homVK_surjective` over any number field: semisimple complement of the image + lattice clearing +
  Faltings Tate + injectivity of precomposition with a surjection (Mathlib
  `ext_of_isDominant_of_isSeparated`) + flatness of ℤ_ℓ/ℤ. No Poincaré needed.
  `g13_constituent'` = G13 with that hypothesis discharged.
- `rhoF_subrep_J`: R16's `ρ_{f,ι}` (`rhoF`) is 2-dim, semisimple, has traces `ι(a_p)`, and is
  equivariantly ≅ a subrepresentation of `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` (sub, not just quotient).
- `V_ℓ` under base change: `bcV ℓ J i : V_ℓ(J) → V_ℓ(J_L)` for `i : K̄ → L̄`, injective (also
  after `⊗E`), equivariant for `i∘σ = τ∘i`; `res i : G_L →* G_K`; `bcT_bijective` given
  `TateModuleFree` and `dim J_L = dim J` (hypothesis, not needed for E1).
- **`rhoF_subrep_JL` / `rhoFL_subrep_JL`**: `ρ_{f,ι}|_{G_L}` ≅ a subrepresentation of
  `V_ℓ(J₁(N)_L) ⊗ ℚ̄_ℓ` (the `U'` that `PkgI3.E1_exists_hom_ne_zero'` consumes).
- **`E1_R16`**: given a nonzero subrep of `V_ℓ(A') ⊗ ℚ̄_ℓ` (A'/L number field) ≅ `ρ_{f,ι}|_{G_L}`,
  a nonzero `A' → J_L`, and under `EndDivision A'` an isogeny `A' × Z → J_L` (N5 L861-867).

**What remains** (outside this task): the `A'`-side isomorphism `U ≅ ρ_{f,ι}|_{G_L}` (C9:
Brauer–Nesbitt; semisimplicity of `rhoF` is now proved, Chebotarev/continuity open);
`EndDivision A'` (G17); `2 ≤ dim J₁(N)` (needs dimension theory of `AbVar` isogenies). One model
review: no false or vacuous statement; its interface finding is applied. At integration, update the
`VSurjOfSurjective` docstring in `ModCurves/Glue.lean` (it says "by Poincaré reducibility").

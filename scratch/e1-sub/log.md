# e1-sub results log

- 22:57 built ZInQKernel.HDecomp.ModCurves.Glue, I3Linalg.C2, I3Linalg.TateBC (lake build, exit 0).
- 23:00 VERIFIED (compiled, `lake env lean scratch/e1-sub/VSurj.lean`, no errors):
  `E1Sub.homVK_surjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
   [NumberField K] (J A : AbVar K) (π : Hom J A) (hπ : Surjective π.hom.left) :
   Function.Surjective (homVK ℓ π)`; route: semisimple complement of the image, lattice
  clearing, Faltings Tate, injectivity of precomposition (`precomp_injective`, from Mathlib
  `ext_of_isDominant_of_isSeparated`, `A` reduced via `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`),
  flatness of ℤ_ℓ over ℤ. No Poincaré reducibility used.
- 23:05 VERIFIED (compiled): `E1Sub.vSurjOfSurjective (hS) (hF) (hT) : LeafModCurves.VSurjOfSurjective`;
  `exists_subrep_equiv_of_surjective` (semisimple + surjective equivariant ⇒ subrep ≅ target);
  `evalEigE_surjective`, `evalEigE_equivariant`; `rhoF_subrep_of_surj`; `rhoF_subrep_J` (from R16 +
  FaltingsSemisimple + FaltingsTate + TateModuleFree: `rhoF ℓ A θ ι` ≅ subrep of `V_ℓ(J)⊗ℚ̄_ℓ` over G_ℚ).
- 23:10 VERIFIED (compiled, scratch/e1-sub/BC.lean): `bcPt` (A(M) →* A_L(M), via `Functor.map_mul`
  for the monoidal `Over.pullback`), `bcPt_injective`, `precompPt_injective` (Spec of a field map is
  dominant; `ext_of_isDominant_of_isSeparated`), `bcPhi_galAct` (equivariance for `i∘σ = τ∘i`),
  `exists_res` (every τ ∈ G_L restricts: `AlgEquiv.restrictNormal`), `bcT_injective`, `bcT_galT`,
  `bcV_injective` (ℚ_ℓ flat over ℤ_ℓ: `IsLocalization.flat`), `bcV_galRep`, `bcVE_injective`,
  `bcVE_equivariant`. No dimension-under-base-change input is needed (injectivity suffices).
- 23:15 VERIFIED (compiled, `lake env lean scratch/e1-sub/E1Sub.lean`, exit 0, no errors, no sorry):
  combined file; `E1Sub.rhoF_subrep_JL` (E1 for R16: `rhoF ℓ A_f θ ι` ≅ subrep `U` of
  `V_ℓ(J_L) ⊗ ℚ̄_ℓ`, τ ∈ G_L acting through any σ ∈ G_ℚ with i∘σ = τ∘i). `#print axioms` for
  vSurjOfSurjective, homVK_surjective, rhoF_subrep_J, bcVE_injective, bcVE_equivariant, exists_res,
  rhoF_subrep_JL: [propext, Classical.choice, Quot.sound].
  Finding: `set Ψ := … with …` in the final proof timed out (whnf, 200000 heartbeats); `let` works.
- 23:16 VERIFIED (compiled): `rhoF_semisimple_of_surj` (rhoF semisimple: an equivariant quotient of
  the semisimple V_ℓ(J)⊗ℚ̄_ℓ, via kernel `GlueI3.isSemisimple_of_surjective`); semisimplicity added
  to the outputs of `rhoF_subrep_J`, `rhoF_subrep_JL`. Also `res` (G_L →* G_K), `res_spec`,
  `rhoFL`, `rhoFL_subrep_JL`, `bcT_bijective` (hyp. `dim J_L = dim J`), `E1_R16` (nonzero
  A' → J_L from an A'-side constituent ≅ rhoFL, plus Poincaré isogeny under EndDivision A').
  All `#print axioms`: [propext, Classical.choice, Quot.sound].
- 23:20 VERIFIED (compiled): `g13_constituent'` (g13_constituent with `VSurjOfSurjective` discharged).

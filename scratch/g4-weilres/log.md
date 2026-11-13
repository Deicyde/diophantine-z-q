# g4-weilres results log

## Setup
- Built `ZInQKernel.HDecomp.B3Unram.B3b`, `ZInQKernel.HDecomp.Repo.TorsionFree` (lake build, OK).
- Consumer of G4 (VERIFIED by reading): `GlueDescent.B3Q.b3_degree_le_QM` (ZInQKernel/HDecomp/Descent/B3Assembly.lean)
  takes `L : IntermediateField ℚ ℚ̄`, `[FiniteDimensional ℚ L] [IsGalois ℚ L]`, `finrank ℚ L ≤ heightD`,
  `∀ p : Nat.Primes, p ∉ ramSet S u → UnramifiedAt L p`, and `ε` with `InflatedFrom L ε`.
  `GlueAssembly.CMOutput` takes only a real `d` with `1 ≤ d ≤ heightD`.

## Bridge.lean — COMPILED (lake env lean, no errors, no sorry)
- `G4WeilRes.exists_liesOver`: a valuation subring of ℚ̄ over every prime p.
- `G4WeilRes.exists_inertia_restrict`: L finite Galois, σ trivial mod w on integers of L ⇒ ∃ s ∈ I_w, s = σ on L.
- `G4WeilRes.unramifiedAt_of_inertia_le`: (∀ w over p, I_w ≤ G_L) ⇒ `UnramifiedAt L p`.
- `G4WeilRes.galUnramifiedOutside_iff`: `GalUnramifiedOutside L T ↔ ∀ p ∉ T, UnramifiedAt L p` (finite Galois L).
- Bridge.lean merged into G4.lean (scratch files cannot import each other); Bridge.lean removed.

## G4.lean — core COMPILED (lake env lean, no errors, no sorry)
- `G4WeilRes.toGL`, `toGL_injective`: `(M ≃ₗ[ℤ] M) →* GL_r(ℤ)` from a basis, injective.
- `G4WeilRes.homField_core`: K ⊆ ℚ̄ finite Galois, GalUnramifiedOutside K T; ρ : G_ℚ →* (M ≃ₗ[ℤ] M), M with
  basis `Fin r`, open stabilizers, inertia over p ∉ T acting trivially ⇒ ∃ L ⊇ K finite Galois,
  G_L acts trivially on M, finrank L ≤ finrank K · 3^(r²), GalUnramifiedOutside L T, ∀ p ∉ T UnramifiedAt L p.
  Uses GlueRepo.TorsionFree.card_le_three_pow (Minkowski), InfiniteGalois.*, the bridge.
- `G4WeilRes.homField_le_heightD`: with finrank K ≤ heightF0, r ≤ 16·heightF0² ⇒ finrank L ≤ heightD
  (GlueRepo.Numerics.a8_degree, ZInQ.Compiler.Precision.heightD_eq).

## G4.lean — lattice, AbVar instantiation, feed to G7: COMPILED; axioms VERIFIED
- `pi_rank_le`: ∏_{(i,j)∈n×n} of free finite ℤ-modules of rank ≤ c has finrank ≤ c·n².
- `trivial_of_faithful`, `conj_trivial`: equivariant injective realization ⇒ trivial action transfers (N5 L559-561 algebra).
- `HomLattice A := ∀ ij : Fin n × Fin n, PkgI3.AbVar.Hom (A ij.1) (A ij.2)` (A : Fin n → AbVar ℚ̄).
- `homLattice_free (hHFF : PkgI3.HomFreeFinite)`: dim A i = 2 ⇒ HomLattice free, finite, finrank ≤ 16n².
- `homField_of_conjugates`: HomFreeFinite + K (finrank ≤ F₀, Galois-unramified outside T) + n ≤ F₀ surfaces +
  ρ : G_ℚ →* Aut_ℤ(HomLattice A) continuous, inertia-trivial outside T ⇒ Hom field L, finrank ≤ heightD, both unramified forms.
- `b3_of_homField`: G4's L fed into `GlueDescent.B3Q.b3_degree_le_QM` (with T = ramSet S u); needs `hdesc`
  (ε inflated from any field defining the lattice — G7's instantiation, hypothesis).
- `#print axioms` of all six main theorems: [propext, Classical.choice, Quot.sound].

## G4.lean — conjugation data (COMPILED)
- Lattice section generalized to any `[Fintype Idx]` (index = conjugates, e.g. embeddings K → ℚ̄); `homField_of_conjugates` takes `Fintype.card Idx ≤ F₀`.
- `ConjData Idx` (A : Idx → AbVar ℚ̄, act : G_ℚ → Perm Idx, g σ i : A(σ·i) → A i with IsPullback over Spec σ).
- `IsConjAction D ρ`: ρ σ f ∘ g_{σ,i} = g_{σ,j} ∘ f componentwise.
- `isConjAction_unique`: two conjugation actions for the same data are equal (IsPullback.hom_ext). COMPILED.
- `ConjActionExists D` (def, Prop): open glue target.

## G4.lean — conjugates of a model A/K (COMPILED; axioms VERIFIED standard)
- `bcAlong A f`: base change of `AbVar K` along any ring hom `f : K →+* L` (Over.pullback, grpObjObj).
- `embAct K σ`: G_ℚ permutes embeddings K →ₐ[ℚ] ℚ̄; `specEmb_act`: Spec(σ∘e) = Spec σ ≫ Spec e.
- `conjMap`, `conjMap_isPullback`: A_{σ∘e} → A_e over Spec σ is a pullback (IsPullback.of_right').
- `conjData K A : ConjData (K →ₐ[ℚ] ℚ̄)`: constructed, no hypotheses.
- `card_conjugates`: #embeddings = [K:ℚ] (AlgHom.card).
- `homField_of_model`: G4 for a model A/K with ρ the (unique) conjugation action; remaining hypotheses:
  hdim (dim of base change = 2), ρ itself (ConjActionExists), hcont, hinert, hK (G2 output).
- `cm_degree_of_homField`: 1 ≤ [L:ℚ] ≤ heightD as reals (the `d` of `GlueAssembly.CMOutput`). COMPILED.
- G4.lean: 760 lines, 0 `sorry`, compiles with `lake env lean scratch/g4-weilres/G4.lean` (needs oleans of
  ZInQKernel.HDecomp.{B3Unram.B3b, Repo.TorsionFree, Repo.Numerics, Descent.B3Assembly, Objects}: `lake build` them first).

## G4.lean — ℓ-adic faithfulness (COMPILED; axioms VERIFIED standard)
- `tateHom_injective (hHFF)`: Hom(A,B) → Hom_{ℤ_ℓ}(T_ℓA, T_ℓB) injective for ℓ invertible
  (HomFreeFinite's injectivity on ℤ_ℓ ⊗ Hom + flatness of the free module Hom).
- `tateLattice`, `tateLattice_injective`: componentwise realization of HomLattice, injective over ℚ̄.
- `inertia_of_tate`: equivariant τ on the realization with inertia trivial ⇒ `hinert`.
- File: 0 `sorry` (grep), all 12 printed theorems on [propext, Classical.choice, Quot.sound].

## G4.lean — the conjugation action CONSTRUCTED (COMPILED; axioms VERIFIED standard)
- Generic section `G4Conj` (any category with pullbacks; Conj.lean merged in, then removed):
  `mul_left_fst`, `one_left_fst` (Mathlib's monoidal Over.pullback: μ, η of a base change vs the projection);
  `cmp X s h : X ×_{f₂} T → X ×_{f₁} T` for f₂ = s ≫ f₁; `cmp_isPullback`; `cmp_mul`, `cmp_one` (respects μ, η);
  `conj X Y s hf hg φ` (conjugate of φ : X_{f₁} → Y_{g₁}); `conj_cmp`, `conj_unique`;
  `conj_isMonHom` (conjugate of a monoid hom is a monoid hom); `conj_mul`, `conj_one` (multiplicative);
  `conj_congr`, `conj_self`, `conj_comp` (functorial in s).
- `ConjData` re-oriented: g σ i : A i → A (σ⁻¹·i) over Spec σ; `IsConjAction` accordingly; `isConjAction_unique` re-proved.
- `conjData K A` now uses `G4Conj.cmp` (`specEmb_symm`). `specGal_mul`, `specGal_one`.
- `conjHom`, `conjAct`, `conjAct_isConjAction`, `conjAct_one`, `conjAct_mul`; `conjAction K A : G_ℚ →* Aut_ℤ(HomLattice)`.
- **`conjActionExists : ConjActionExists (conjData K A)` — PROVED.** (index defeq `(στ)⁻¹∘e ≡ τ⁻¹∘σ⁻¹∘e` checked by rfl.)
- `homField_of_model` now uses `conjAction K A` (no ρ hypothesis). Remaining hypotheses: hdim, hcont, hinert, hK.
- G4.lean: 1184 lines, 0 sorry; 13 printed theorems all on [propext, Classical.choice, Quot.sound].

## G4.lean — continuity from a descent input (COMPILED; axioms VERIFIED standard)
- `HomDescends` (def, Prop): every morphism A ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄ is fixed by `G4Conj.conj` along an open
  subgroup of G_ℚ. Consequence of EGA IV₃ 8.8.2 (UNVERIFIED locator) + descent bookkeeping (glue, not formalized).
- `embAct_symm_of_mem`: G_K fixes the embeddings of Galois K. `stabSub`: stabilizer subgroup.
- `conjAction_continuous (hD : HomDescends)`: every lattice element has an open stabilizer. PROVED.
- `homField_of_model'`: G4 for A/K from HomFreeFinite + HomDescends + hdim + hK + hinert.

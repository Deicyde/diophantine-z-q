import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.ExactSequences

/-!
# Switch inputs: the switch exact sequences (5.5a) from Selmer data

Proposition `ex:limits-uniform-lower-bound`, tex L5055–5086: at a new derivative prime the strict,
finite, singular and relaxed conditions are `D⁰ ⊂ D⁰ ⊕ F[−1], D⁰ ⊕ S[−1] ⊂ D⁰ ⊕ (F ⊕ S)[−1]`, and

> The cone triangles, with `D⁰` retained, give exact sequences
> `0 → K₀ → V → U ∩ F → 0`, `0 → K₀ → V' → U ∩ S → 0`, (5.5a)
> where `V'` is the switched fiber cohomology. There is no preceding local degree-zero term, since
> the quotient conditions are `F[−1]` and `S[−1]`.

`ExactSequences.lean` proves the dimension equations of (5.5a) from two abstract short exact sequences
of cochain complexes (`SwitchDimsOfSES`) and local cohomology hypotheses on the quotients. Here both
are discharged from Selmer data (all over a field `k`, the fiber `C ⊗_R k` at a height-one prime):

* the two short exact sequences are SelmerDuality's change-of-local-conditions sequences
  `0 → C(U_str) → C(U_F) → W_F → 0`, `0 → C(U_F) → C(U_rel) → W_S → 0` (`changeSES`,
  `relaxedQuotientNode_proof`), and the relaxed localization `λ : C(U_rel) → W_rel` is `quotMap`;
* the quotients `W_F, W_rel, W_S` are concentrated in degree one (the conditions `F[−1]`, `(F⊕S)[−1]`,
  `S[−1]`), so they have zero differential, `H⁰ = 0` and `H¹ = W¹` (`h1Iso`, natural in the
  complex), and the local hypotheses of `SwitchDimsOfSES` follow from degree-one exactness of
  `0 → F → F ⊕ S → S → 0` (`degreeOne_hypotheses`).

Nodes (PROVED):
* `SwitchSideDims`: for one side (finite or singular), `dim H¹(C(U_F)) = dim H¹(C(U_str)) + dim(U ⊓ P)`,
  with `U ⊆ k² × k²` the image of `H¹(C(U_rel))` under the relaxed localization in the coordinates
  `W_rel¹ ≃ k² × k²`, and `P` the image of the side's plane (`finPlane` or `singPlane`).
* `switchDims_of_selmerData`: both (5.5a) equations, `s = k₀ + dim(U ⊓ finPlane)` and
  `s' = k₀' + dim(U ⊓ singPlane)` (the `hs`, `hs'` shapes of `NonquadDims`), with one common `U`, and
  `k₀ = k₀'` when the two strict conditions are the same local map (`strict_eq`).

DEPARTURE (form only): the Selmer complexes are SelmerDuality's `selCx` models
`C^n = G^n ⊕ U^n ⊕ L^{n−1}`; their identification with the Galois cochains of the text is the
SelmerDuality GLUE, not repeated here.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k]

/-! ### Complexes concentrated in degree one -/

/-- A graded complex concentrated in degree one (the quotient conditions `F[−1]`, `S[−1]`,
`(F ⊕ S)[−1]` of tex L5080–5083). -/
def ConcDegOne (W : GCx k) : Prop := ∀ n : ℤ, n ≠ 1 → Subsingleton (W.X n)

theorem toCC_d_zero_in {W : GCx k} (hW : ConcDegOne W) : W.toCC.d 0 1 = 0 := by
  have : Subsingleton (W.toCC.X 0) := hW 0 (by norm_num)
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  simp

theorem toCC_d_zero_out {W : GCx k} (hW : ConcDegOne W) : W.toCC.d 1 2 = 0 := by
  have : Subsingleton (W.toCC.X 2) := hW 2 (by norm_num)
  ext x
  exact Subsingleton.elim _ _

/-- `H¹(W) ≅ W¹` for a complex concentrated in degree one. -/
def h1Iso (W : GCx k) (hW : ConcDegOne W) : W.toCC.homology 1 ≅ W.toCC.X 1 :=
  (W.toCC.isoHomologyπ 0 1 (by simp) (toCC_d_zero_in hW)).symm ≪≫
    W.toCC.iCyclesIso 1 2 (by simp) (toCC_d_zero_out hW)

theorem homologyπ_h1Iso (W : GCx k) (hW : ConcDegOne W) :
    W.toCC.homologyπ 1 ≫ (h1Iso W hW).hom = W.toCC.iCycles 1 := by
  simp only [h1Iso, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
    HomologicalComplex.iCyclesIso_hom]

/-- Naturality of `h1Iso`: under `H¹(W) ≅ W¹`, `H¹(φ)` is `φ¹`. -/
theorem h1Iso_natural {W W' : GCx k} (hW : ConcDegOne W) (hW' : ConcDegOne W') (φ : GHom W W') :
    HomologicalComplex.homologyMap (GHom.toCC φ) 1 ≫ (h1Iso W' hW').hom =
      (h1Iso W hW).hom ≫ (GHom.toCC φ).f 1 := by
  rw [← cancel_epi (W.toCC.homologyπ 1), ← Category.assoc,
    HomologicalComplex.homologyπ_naturality, Category.assoc, homologyπ_h1Iso,
    HomologicalComplex.cyclesMap_i, ← Category.assoc, homologyπ_h1Iso]

/-- The linear equivalence `H¹(W) ≃ W¹`. -/
def h1Equiv (W : GCx k) (hW : ConcDegOne W) : W.toCC.homology 1 ≃ₗ[k] W.X 1 :=
  (h1Iso W hW).toLinearEquiv

theorem h1Equiv_apply (W : GCx k) (hW : ConcDegOne W) (x : W.toCC.homology 1) :
    h1Equiv W hW x = (h1Iso W hW).hom.hom x := rfl

theorem h1Equiv_natural {W W' : GCx k} (hW : ConcDegOne W) (hW' : ConcDegOne W') (φ : GHom W W')
    (x : W.toCC.homology 1) :
    h1Equiv W' hW' ((HomologicalComplex.homologyMap (GHom.toCC φ) 1).hom x) =
      φ.f 1 1 rfl (h1Equiv W hW x) := by
  have := congrArg (fun f => f.hom x) (h1Iso_natural hW hW' φ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  rw [h1Equiv_apply, h1Equiv_apply, this]
  rfl

theorem subsingleton_h0 {W : GCx k} (hW : ConcDegOne W) : Subsingleton (W.toCC.homology 0) := by
  have : Subsingleton (W.toCC.X 0) := hW 0 (by norm_num)
  have hinj : Function.Injective (W.toCC.iCycles 0).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have : Subsingleton (W.toCC.cycles 0) := hinj.subsingleton
  exact ((ModuleCat.epi_iff_surjective _).mp inferInstance :
    Function.Surjective (W.toCC.homologyπ 0).hom).subsingleton

/-- **The local cohomology hypotheses of `SwitchDimsOfSES`** (tex L5080–5083): for complexes
`W₁, W_rel, W₂` concentrated in degree one and chain maps `i : W₁ → W_rel`, `p : W_rel → W₂` exact in
degree one with `i¹` injective, `H⁰(W₁) = 0`, `H¹(i)` is injective and `ker H¹(p) = im H¹(i)`. PROVED. -/
theorem degreeOne_hypotheses {W₁ Wr W₂ : GCx k} (h₁ : ConcDegOne W₁) (hr : ConcDegOne Wr)
    (h₂ : ConcDegOne W₂) (i : GHom W₁ Wr) (p : GHom Wr W₂) (hi : Function.Injective (i.f 1 1 rfl))
    (hex : ∀ y, p.f 1 1 rfl y = 0 ↔ ∃ x, i.f 1 1 rfl x = y) :
    Subsingleton (W₁.toCC.homology 0) ∧
    Function.Injective (HomologicalComplex.homologyMap (GHom.toCC i) 1).hom ∧
    LinearMap.ker (HomologicalComplex.homologyMap (GHom.toCC p) 1).hom =
      LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC i) 1).hom := by
  refine ⟨subsingleton_h0 h₁, fun x y hxy => ?_, ?_⟩
  · have := congrArg (h1Equiv Wr hr) hxy
    rw [h1Equiv_natural h₁ hr, h1Equiv_natural h₁ hr] at this
    exact (h1Equiv W₁ h₁).injective (hi this)
  · ext y
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      have h0 : p.f 1 1 rfl (h1Equiv Wr hr y) = 0 := by
        rw [← h1Equiv_natural hr h₂, hy, map_zero]
      obtain ⟨x, hx⟩ := (hex _).mp h0
      refine ⟨(h1Equiv W₁ h₁).symm x, (h1Equiv Wr hr).injective ?_⟩
      rw [h1Equiv_natural h₁ hr, LinearEquiv.apply_symm_apply, hx]
    · rintro ⟨x, rfl⟩
      apply (h1Equiv W₂ h₂).injective
      rw [h1Equiv_natural hr h₂, h1Equiv_natural h₁ hr, map_zero]
      exact (hex _).mpr ⟨_, rfl⟩

/-! ### Finite dimensionality of the Selmer cohomology -/

theorem finiteDimensional_h1_selCx (D : SelData k) [FiniteDimensional k (D.G.X 1)]
    [FiniteDimensional k (D.U.X 1)] [FiniteDimensional k (D.L.X 0)] :
    FiniteDimensional k ((selCx D).toCC.homology 1) := by
  have : FiniteDimensional k ((selCx D).toCC.X 1) := by
    change FiniteDimensional k (D.G.X 1 × D.U.X 1 × D.L.X (1 - 1))
    rw [sub_self]
    infer_instance
  have hinj : Function.Injective ((selCx D).toCC.iCycles 1).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have : FiniteDimensional k ((selCx D).toCC.cycles 1) :=
    Module.Finite.of_injective _ hinj
  exact Module.Finite.of_surjective _
    ((ModuleCat.epi_iff_surjective _).mp inferInstance :
      Function.Surjective ((selCx D).toCC.homologyπ 1).hom)

/-! ### The Selmer data of a switch -/

/-- **The relaxed condition and its localization** (tex L5070–5075): Selmer data `D` whose local
condition `D.U` is the relaxed one `D⁰ ⊕ (F ⊕ S)[−1]`, the relaxed quotient `W_rel = (F ⊕ S)[−1]`
(concentrated in degree one) with the projection `g_R : D.U → W_rel`, and coordinates
`W_rel¹ ≃ k² × k²`. -/
structure RelaxedLocalization (k : Type) [Field k] where
  D : SelData k
  Wrel : GCx k
  gR : GHom D.U Wrel
  eR : Wrel.X 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)
  hWrel : ConcDegOne Wrel

/-- The relaxed localization image `U = im(H¹(C_rel ⊗ k) → F ⊕ S)` (tex L5072–5074), in the
coordinates `k² × k²`. -/
def RelaxedLocalization.U (R : RelaxedLocalization k) : Submodule k ((Fin 2 → k) × (Fin 2 → k)) :=
  (LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC (quotMap R.D R.gR)) 1).hom).map
    ((h1Equiv R.Wrel R.hWrel).trans R.eR).toLinearMap

/-- **One side of the switch** (finite or singular; tex L5055–5086): the side condition
`U₁ = D⁰ ⊕ P[−1]` inside the relaxed one (`f₁`, with quotient `W₂ = Q[−1]`, `g₂`), the strict condition
`U_str = D⁰` inside `U₁` (`f_s`, with quotient `W₁ = P[−1]`, `g₁`), the inclusion `i : W₁ → W_rel`
and projection `p : W_rel → W₂` of `0 → P → F ⊕ S → Q → 0`, compatibly with the relaxed localization;
all quotients concentrated in degree one; `P` the image of `W₁¹` in the coordinates. -/
structure SwitchSide (R : RelaxedLocalization k) (P : Submodule k ((Fin 2 → k) × (Fin 2 → k))) where
  U₁ : GCx k
  Ustr : GCx k
  W₁ : GCx k
  W₂ : GCx k
  f₁ : GHom U₁ R.D.U
  g₂ : GHom R.D.U W₂
  fs : GHom Ustr U₁
  g₁ : GHom U₁ W₁
  i : GHom W₁ R.Wrel
  p : GHom R.Wrel W₂
  hfg₂ : ∀ n (u : U₁.X n), g₂.f n n rfl (f₁.f n n rfl u) = 0
  f₁_inj : ∀ n, Function.Injective (f₁.f n n rfl)
  g₂_surj : ∀ n, Function.Surjective (g₂.f n n rfl)
  ex₂ : ∀ n (u : R.D.U.X n), g₂.f n n rfl u = 0 → ∃ u', f₁.f n n rfl u' = u
  hfg₁ : ∀ n (u : Ustr.X n), g₁.f n n rfl (fs.f n n rfl u) = 0
  fs_inj : ∀ n, Function.Injective (fs.f n n rfl)
  g₁_surj : ∀ n, Function.Surjective (g₁.f n n rfl)
  ex₁ : ∀ n (u : U₁.X n), g₁.f n n rfl u = 0 → ∃ u', fs.f n n rfl u' = u
  hRF : ∀ n (u : U₁.X n), R.gR.f n n rfl (f₁.f n n rfl u) = i.f n n rfl (g₁.f n n rfl u)
  hpR : ∀ n (u : R.D.U.X n), p.f n n rfl (R.gR.f n n rfl u) = g₂.f n n rfl u
  hW₁ : ConcDegOne W₁
  hW₂ : ConcDegOne W₂
  i_inj : Function.Injective (i.f 1 1 rfl)
  ip_exact : ∀ y, p.f 1 1 rfl y = 0 ↔ ∃ x, i.f 1 1 rfl x = y
  hP : LinearMap.range (R.eR.toLinearMap ∘ₗ i.f 1 1 rfl) = P

variable {R : RelaxedLocalization k} {P : Submodule k ((Fin 2 → k) × (Fin 2 → k))}

/-- The side Selmer data `C(U₁)`. -/
def SwitchSide.Dside (S : SwitchSide R P) : SelData k := restrictData R.D S.f₁

/-- The strict Selmer data `C(U_str)`. -/
def SwitchSide.Dstr (S : SwitchSide R P) : SelData k := restrictData S.Dside S.fs

/-- **The first short exact sequence** `0 → C(U_str) → C(U₁) → W₁ → 0` (tex L5080–5083). PROVED. -/
theorem SwitchSide.ses₁ (S : SwitchSide R P) :
    (changeSES S.Dside S.fs S.g₁ S.hfg₁).ShortExact :=
  relaxedQuotientNode_proof k S.Dside S.Ustr S.W₁ S.fs S.g₁ S.hfg₁ S.fs_inj S.g₁_surj S.ex₁

/-- **The second short exact sequence** `0 → C(U₁) → C(U_rel) → W₂ → 0` (tex L5080–5083). PROVED. -/
theorem SwitchSide.ses₂ (S : SwitchSide R P) :
    (changeSES R.D S.f₁ S.g₂ S.hfg₂).ShortExact :=
  relaxedQuotientNode_proof k R.D S.U₁ S.W₂ S.f₁ S.g₂ S.hfg₂ S.f₁_inj S.g₂_surj S.ex₂

theorem SwitchSide.comm_lam (S : SwitchSide R P) :
    GHom.toCC (changeMap R.D S.f₁) ≫ GHom.toCC (quotMap R.D R.gR) =
      GHom.toCC (quotMap S.Dside S.g₁) ≫ GHom.toCC S.i := by
  rw [GHom.toCC_comp, GHom.toCC_comp]
  apply GHom.toCC_ext
  intro n c
  obtain ⟨a, u, x⟩ := c
  exact S.hRF n u

theorem SwitchSide.fac_p (S : SwitchSide R P) :
    GHom.toCC (quotMap R.D R.gR) ≫ GHom.toCC S.p = GHom.toCC (quotMap R.D S.g₂) := by
  rw [GHom.toCC_comp]
  apply GHom.toCC_ext
  intro n c
  obtain ⟨a, u, x⟩ := c
  exact S.hpR n u

/-- **(5.5a) for one side** (tex L5055–5086): from the Selmer data of a switch side,
`dim H¹(C(U₁)) = dim H¹(C(U_str)) + dim(U ⊓ P)`, with `U` the relaxed localization image and `P` the
side plane, both in the coordinates `k² × k²`. Classification: PROVED. -/
def SwitchSideDims : Prop :=
  ∀ (k : Type) [Field k] (R : RelaxedLocalization k) (P : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (S : SwitchSide R P) [FiniteDimensional k (R.D.G.X 1)] [FiniteDimensional k (S.U₁.X 1)]
    [FiniteDimensional k (R.D.L.X 0)],
    finrank k ((selCx S.Dside).toCC.homology 1) =
      finrank k ((selCx S.Dstr).toCC.homology 1) + finrank k ↥(R.U ⊓ P)

theorem switchSideDims_proof : SwitchSideDims := by
  intro k _ R P S _ _ _
  obtain ⟨h0, hi, hpi⟩ := degreeOne_hypotheses S.hW₁ R.hWrel S.hW₂ S.i S.p S.i_inj S.ip_exact
  have : FiniteDimensional k (S.Dside.U.X 1) := by
    change FiniteDimensional k (S.U₁.X 1); infer_instance
  have : FiniteDimensional k (S.Dside.G.X 1) := by
    change FiniteDimensional k (R.D.G.X 1); infer_instance
  have : FiniteDimensional k (S.Dside.L.X 0) := by
    change FiniteDimensional k (R.D.L.X 0); infer_instance
  have hfinCf := finiteDimensional_h1_selCx S.Dside
  have hfinWr : FiniteDimensional k (R.Wrel.toCC.homology 1) := by
    have : FiniteDimensional k (R.Wrel.X 1) := LinearEquiv.finiteDimensional R.eR.symm
    exact LinearEquiv.finiteDimensional (h1Equiv R.Wrel R.hWrel).symm
  have hdims := switchDimsOfSES_proof.{0} k _ _ _ _ _ _ _ _ _ _ _ _ _
    (changeSES S.Dside S.fs S.g₁ S.hfg₁).zero (changeSES R.D S.f₁ S.g₂ S.hfg₂).zero
    S.ses₁ S.ses₂ S.comm_lam S.fac_p h0 hi hpi hfinCf hfinWr
  have hdims' : finrank k ((selCx S.Dside).toCC.homology 1) =
      finrank k ((selCx S.Dstr).toCC.homology 1) +
        finrank k ↥(LinearMap.range
            (HomologicalComplex.homologyMap (GHom.toCC (quotMap R.D R.gR)) 1).hom ⊓
          LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC S.i) 1).hom) := hdims
  rw [hdims']
  congr 1
  -- transport the intersection along `εW = h1Equiv ≪≫ eR`
  set εW := (h1Equiv R.Wrel R.hWrel).trans R.eR
  have hA : (LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC S.i) 1).hom).map
      εW.toLinearMap = LinearMap.range (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨h1Equiv S.W₁ S.hW₁ x, ?_⟩
      simp only [εW, LinearEquiv.trans_apply, h1Equiv_natural S.hW₁ R.hWrel]
    · rintro ⟨x, rfl⟩
      refine ⟨_, ⟨(h1Equiv S.W₁ S.hW₁).symm x, rfl⟩, ?_⟩
      simp only [εW, LinearEquiv.trans_apply, h1Equiv_natural S.hW₁ R.hWrel,
        LinearEquiv.apply_symm_apply]
  have key : finrank k ↥(LinearMap.range
        (HomologicalComplex.homologyMap (GHom.toCC (quotMap R.D R.gR)) 1).hom ⊓
      LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC S.i) 1).hom) =
      finrank k ↥(R.U ⊓ LinearMap.range (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl)) := by
    rw [RelaxedLocalization.U, ← hA, ← Submodule.map_inf _ εW.injective]
    exact (Submodule.equivMapOfInjective _ εW.injective _).finrank_eq
  rw [S.hP] at key
  exact key

/-- Extensionality of relation-indexed chain maps. -/
theorem ghom_ext {A B : GCx k} {f g : GHom A B} (h : ∀ n x, f.f n n rfl x = g.f n n rfl x) :
    f = g := by
  cases f with
  | mk f fc =>
    cases g with
    | mk g gc =>
      have : f = g := by
        funext i j hij
        subst hij
        exact LinearMap.ext (h i)
      subst this
      rfl

/-- **One `K₀` for both sides of (5.5a)**: Selmer data with the same global complex, local condition,
full local complex and restriction, whose local condition maps agree degree by degree, have the same
`H¹`. The strict data `S.Dstr` of a side is `⟨R.D.G, S.Ustr, R.D.L, R.D.res, ι_str⟩` with
`ι_str = ι ∘ f₁ ∘ f_s`; so the two sides have the same `k₀` as soon as they are built on the same
strict condition with the same composite `U_str → L`. PROVED. -/
theorem finrank_h1_selCx_congr (G U L : GCx k) (res : GHom G L) (ι ι' : GHom U L)
    (h : ∀ n x, ι.f n n rfl x = ι'.f n n rfl x) :
    finrank k ((selCx ⟨G, U, L, res, ι⟩).toCC.homology 1) =
      finrank k ((selCx ⟨G, U, L, res, ι'⟩).toCC.homology 1) := by
  rw [ghom_ext h]

/-- **(5.5a), both equations, from the Selmer data** (tex L5055–5086): for a relaxed localization
`R` and the finite and singular sides `S_F`, `S_S` (with planes `finPlane` and `singPlane`),
`s = k₀ + dim(U ⊓ finPlane)` and `s' = k₀' + dim(U ⊓ singPlane)`, where `s = dim H¹(C(U_F))`,
`s' = dim H¹(C(U_S))`, `k₀, k₀'` the strict dimensions and `U` the common relaxed localization image:
the `hs`, `hs'` shapes of `NonquadDims`. Classification: PROVED. -/
theorem switchDims_of_selmerData (R : RelaxedLocalization k)
    (SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    [FiniteDimensional k (R.D.G.X 1)] [FiniteDimensional k (R.D.L.X 0)]
    [FiniteDimensional k (SF.U₁.X 1)] [FiniteDimensional k (SS.U₁.X 1)] :
    finrank k ((selCx SF.Dside).toCC.homology 1) = finrank k ((selCx SF.Dstr).toCC.homology 1) +
        finrank k ↥(R.U ⊓ finPlane k (Fin 2 → k) (Fin 2 → k)) ∧
    finrank k ((selCx SS.Dside).toCC.homology 1) = finrank k ((selCx SS.Dstr).toCC.homology 1) +
        finrank k ↥(R.U ⊓ singPlane k (Fin 2 → k) (Fin 2 → k)) :=
  ⟨switchSideDims_proof k R _ SF, switchSideDims_proof k R _ SS⟩

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

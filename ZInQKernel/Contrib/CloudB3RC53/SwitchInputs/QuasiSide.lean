import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuity

/-!
# Switch inputs: the switch sides up to quasi-isomorphism, and localization duality

Proposition `ex:limits-uniform-lower-bound`, tex L5055–5086 ((5.5a)) and tex L5068–5075 (the
relaxed localization image is its own annihilator).

**Item (0).** `SelmerSES.lean`'s `RelaxedLocalization` / `SwitchSide` ask the quotient local
conditions `W_F = F[−1]`, `W_rel = (F ⊕ S)[−1]`, `W_S = S[−1]` to be literally concentrated in degree
one, with `W_rel¹ ≃ k² × k²`. Cochain-level local conditions give such quotients only up to
quasi-isomorphism. The dimension count (5.5a) only uses `H⁰` and `H¹` of the quotients and the long
exact sequence, so it holds verbatim with homology-level hypotheses:

* `QuasiRelaxedLocalization`: the relaxed data with coordinates on `H¹(W_rel)` (not on `W_rel¹`);
  `U` is the image of `H¹(C(U_rel))` in those coordinates.
* `QuasiSwitchSide`: a switch side whose quotients satisfy `H⁰(W₁) = 0`, `H¹(i)` injective,
  `ker H¹(p) = im H¹(i)`, and whose side plane is the image of `H¹(W₁)`; no degree-one condition.
* `QuasiSwitchSideDims` (PROVED): `dim H¹(C(U₁)) = dim H¹(C(U_str)) + dim(U ⊓ P)`, and
  `quasiSwitchDims_of_selmerData` (PROVED): both equations of (5.5a), the `hs`, `hs'` shapes.
* `QuasiModelHypotheses` (PROVED): the homology hypotheses hold as soon as the quotients are
  quasi-isomorphic, compatibly with `i` and `p`, to degree-one complexes satisfying the literal
  conditions of `SwitchSide` — "quasi-isomorphic to a degree-one complex".
* `SwitchSide.toQuasi`, `switchDims_literal_special_case` (PROVED): the literal version is the
  special case `W = W₀`, with the same `U` and the same equations.

**Item (1).** `localization_lagrangian` (PROVED): for an exact sequence `V --λ--> W --δ--> V'` (the
cohomology sequence `H¹(C_rel) → H¹(W_rel) → H²(C_str)` of `0 → C_str → C_rel → W_rel → 0`), a
separating pairing `⟨·,·⟩ : V' × V → k` and a bilinear form `B` on `W` with `⟨δ w, v⟩ = B(λ v, w)`
("localization's connecting map is its dual under the strict/relaxed duality", tex L5068–5075),
`(im λ)^⊥ = im λ`. `SwitchDualityAdjunction` is the remaining input in the new style (GLUE): the
strict/relaxed Selmer duality at the switch (Nekovář 6.3.4; for genuine complexes the other team's
`genuineSelmerDuality`) supplies the separating pairing, and its compatibility with the cone triangle
(Nekovář 6.3.3) supplies the adjunction; `localizationDualityInput_of_adjunction` (PROVED) then gives
`LocalizationDualityInput` for the actual relaxed image.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k]

theorem H1_comp_apply {A B C : GCx k} (f : GHom A B) (g : GHom B C) (x : A.toCC.homology 1) :
    H1 g (H1 f x) = H1 (ghomComp f g) x := by
  simp only [H1, ← GHom.toCC_comp, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]

theorem H1_square {A B C D : GCx k} (f : GHom A B) (g : GHom B D) (f' : GHom A C) (g' : GHom C D)
    (h : ∀ n x, g.f n n rfl (f.f n n rfl x) = g'.f n n rfl (f'.f n n rfl x))
    (x : A.toCC.homology 1) : H1 g (H1 f x) = H1 g' (H1 f' x) := by
  rw [H1_comp_apply, H1_comp_apply,
    show ghomComp f g = ghomComp f' g' from ghom_ext (f := ghomComp f g) (g := ghomComp f' g') h]

/-! ### Item (0): the relaxed localization and the switch sides, up to quasi-isomorphism -/

/-- **The relaxed localization, homology-level** (tex L5070–5075): Selmer data `D` with the relaxed
local condition, the relaxed quotient `W_rel` with projection `g_R`, and coordinates
`H¹(W_rel) ≃ k² × k²` (only the cohomology of `W_rel` is identified with `F ⊕ S`). -/
structure QuasiRelaxedLocalization (k : Type) [Field k] where
  D : SelData k
  Wrel : GCx k
  gR : GHom D.U Wrel
  eR : Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)

/-- The relaxed localization image `U = im(H¹(C_rel) → H¹(W_rel) ≃ F ⊕ S)` (tex L5072–5074). -/
def QuasiRelaxedLocalization.U (R : QuasiRelaxedLocalization k) :
    Submodule k ((Fin 2 → k) × (Fin 2 → k)) :=
  (LinearMap.range (H1 (quotMap R.D R.gR))).map R.eR.toLinearMap

/-- **A switch side up to quasi-isomorphism** (tex L5055–5086): the data of `SwitchSide` (the side
condition `U₁` inside the relaxed one with quotient `W₂`, the strict condition inside `U₁` with
quotient `W₁`, the maps `i : W₁ → W_rel`, `p : W_rel → W₂` compatible with the relaxed
localization), with the degree-one conditions on `W₁, W₂` replaced by the homology-level facts used
by (5.5a): `H⁰(W₁) = 0`, `H¹(i)` injective, `ker H¹(p) = im H¹(i)`, and the side plane `P` the image
of `H¹(W₁)` in the coordinates. -/
structure QuasiSwitchSide (R : QuasiRelaxedLocalization k)
    (P : Submodule k ((Fin 2 → k) × (Fin 2 → k))) where
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
  h0 : Subsingleton (W₁.toCC.homology 0)
  hi : Function.Injective (H1 i)
  hpi : LinearMap.ker (H1 p) = LinearMap.range (H1 i)
  hP : (LinearMap.range (H1 i)).map R.eR.toLinearMap = P

variable {R : QuasiRelaxedLocalization k} {P : Submodule k ((Fin 2 → k) × (Fin 2 → k))}

/-- The side Selmer data `C(U₁)`. -/
def QuasiSwitchSide.Dside (S : QuasiSwitchSide R P) : SelData k := restrictData R.D S.f₁

/-- The strict Selmer data `C(U_str)`. -/
def QuasiSwitchSide.Dstr (S : QuasiSwitchSide R P) : SelData k := restrictData S.Dside S.fs

theorem QuasiSwitchSide.ses₁ (S : QuasiSwitchSide R P) :
    (changeSES S.Dside S.fs S.g₁ S.hfg₁).ShortExact :=
  relaxedQuotientNode_proof k S.Dside S.Ustr S.W₁ S.fs S.g₁ S.hfg₁ S.fs_inj S.g₁_surj S.ex₁

theorem QuasiSwitchSide.ses₂ (S : QuasiSwitchSide R P) :
    (changeSES R.D S.f₁ S.g₂ S.hfg₂).ShortExact :=
  relaxedQuotientNode_proof k R.D S.U₁ S.W₂ S.f₁ S.g₂ S.hfg₂ S.f₁_inj S.g₂_surj S.ex₂

theorem QuasiSwitchSide.comm_lam (S : QuasiSwitchSide R P) :
    GHom.toCC (changeMap R.D S.f₁) ≫ GHom.toCC (quotMap R.D R.gR) =
      GHom.toCC (quotMap S.Dside S.g₁) ≫ GHom.toCC S.i := by
  rw [GHom.toCC_comp, GHom.toCC_comp]
  apply GHom.toCC_ext
  intro n c
  obtain ⟨a, u, x⟩ := c
  exact S.hRF n u

theorem QuasiSwitchSide.fac_p (S : QuasiSwitchSide R P) :
    GHom.toCC (quotMap R.D R.gR) ≫ GHom.toCC S.p = GHom.toCC (quotMap R.D S.g₂) := by
  rw [GHom.toCC_comp]
  apply GHom.toCC_ext
  intro n c
  obtain ⟨a, u, x⟩ := c
  exact S.hpR n u

/-- **(5.5a) for one side, up to quasi-isomorphism** (tex L5055–5086): for a quasi switch side,
`dim H¹(C(U₁)) = dim H¹(C(U_str)) + dim(U ⊓ P)`. Classification: PROVED. -/
def QuasiSwitchSideDims : Prop :=
  ∀ (k : Type) [Field k] (R : QuasiRelaxedLocalization k)
    (P : Submodule k ((Fin 2 → k) × (Fin 2 → k))) (S : QuasiSwitchSide R P)
    [FiniteDimensional k (R.D.G.X 1)] [FiniteDimensional k (S.U₁.X 1)]
    [FiniteDimensional k (R.D.L.X 0)],
    finrank k ((selCx S.Dside).toCC.homology 1) =
      finrank k ((selCx S.Dstr).toCC.homology 1) + finrank k ↥(R.U ⊓ P)

theorem quasiSwitchSideDims_proof : QuasiSwitchSideDims := by
  intro k _ R P S _ _ _
  have : FiniteDimensional k (S.Dside.U.X 1) := by
    change FiniteDimensional k (S.U₁.X 1); infer_instance
  have : FiniteDimensional k (S.Dside.G.X 1) := by
    change FiniteDimensional k (R.D.G.X 1); infer_instance
  have : FiniteDimensional k (S.Dside.L.X 0) := by
    change FiniteDimensional k (R.D.L.X 0); infer_instance
  have hfinCf := finiteDimensional_h1_selCx S.Dside
  have hfinWr : FiniteDimensional k (R.Wrel.toCC.homology 1) :=
    LinearEquiv.finiteDimensional R.eR.symm
  have hdims := switchDimsOfSES_proof.{0} k _ _ _ _ _ _ _ _ _ _ _ _ _
    (changeSES S.Dside S.fs S.g₁ S.hfg₁).zero (changeSES R.D S.f₁ S.g₂ S.hfg₂).zero
    S.ses₁ S.ses₂ S.comm_lam S.fac_p S.h0 S.hi S.hpi hfinCf hfinWr
  have hdims' : finrank k ((selCx S.Dside).toCC.homology 1) =
      finrank k ((selCx S.Dstr).toCC.homology 1) +
        finrank k ↥(LinearMap.range (H1 (quotMap R.D R.gR)) ⊓ LinearMap.range (H1 S.i)) := hdims
  rw [hdims']
  congr 1
  conv_rhs => rw [QuasiRelaxedLocalization.U, ← S.hP, ← Submodule.map_inf _ R.eR.injective]
  exact ((Submodule.equivMapOfInjective _ R.eR.injective _).finrank_eq)

/-- **(5.5a), both equations, up to quasi-isomorphism** (tex L5055–5086): for a quasi relaxed
localization and the finite and singular quasi sides, `s = k₀ + dim(U ⊓ finPlane)` and
`s' = k₀' + dim(U ⊓ singPlane)` — the `hs`, `hs'` shapes of `NonquadDims`. PROVED. -/
theorem quasiSwitchDims_of_selmerData (R : QuasiRelaxedLocalization k)
    (SF : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    [FiniteDimensional k (R.D.G.X 1)] [FiniteDimensional k (R.D.L.X 0)]
    [FiniteDimensional k (SF.U₁.X 1)] [FiniteDimensional k (SS.U₁.X 1)] :
    finrank k ((selCx SF.Dside).toCC.homology 1) = finrank k ((selCx SF.Dstr).toCC.homology 1) +
        finrank k ↥(R.U ⊓ finPlane k (Fin 2 → k) (Fin 2 → k)) ∧
    finrank k ((selCx SS.Dside).toCC.homology 1) = finrank k ((selCx SS.Dstr).toCC.homology 1) +
        finrank k ↥(R.U ⊓ singPlane k (Fin 2 → k) (Fin 2 → k)) :=
  ⟨quasiSwitchSideDims_proof k R _ SF, quasiSwitchSideDims_proof k R _ SS⟩

/-! ### Quasi-isomorphic to degree-one complexes -/

theorem H1_bijective_of_quasiIso {A B : GCx k} (q : GHom A B) [QuasiIso (GHom.toCC q)] :
    Function.Bijective (H1 q) := by
  have : IsIso (HomologicalComplex.homologyMap (GHom.toCC q) 1) :=
    (quasiIsoAt_iff_isIso_homologyMap (GHom.toCC q) 1).mp inferInstance
  exact ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap (GHom.toCC q) 1)

/-- **The homology hypotheses from degree-one models** (tex L5080–5083, up to quasi-isomorphism).
Let `q₁ : W₁ → W₁m`, `q_r : W_rel → W_rel⁰`, `q₂ : W₂ → W₂m` be quasi-isomorphisms to complexes
concentrated in degree one, and `im : W₁m → W_rel⁰`, `pm : W_rel⁰ → W₂m` maps satisfying the literal
conditions of `SwitchSide` (`im¹` injective, exactness in degree one), compatible with `i, p`
(`q₁ ≫ im = i ≫ q_r`, `q_r ≫ pm = p ≫ q₂` degreewise). Then `H⁰(W₁) = 0`, `H¹(i)` is injective and
`ker H¹(p) = im H¹(i)`. Classification: PROVED. -/
def QuasiModelHypotheses : Prop :=
  ∀ (k : Type) [Field k] (W₁ Wr W₂ W₁m Wrm W₂m : GCx k) (i : GHom W₁ Wr) (p : GHom Wr W₂)
    (q₁ : GHom W₁ W₁m) (qr : GHom Wr Wrm) (q₂ : GHom W₂ W₂m) (im : GHom W₁m Wrm) (pm : GHom Wrm W₂m),
    QuasiIso (GHom.toCC q₁) → QuasiIso (GHom.toCC qr) → QuasiIso (GHom.toCC q₂) →
    ConcDegOne W₁m → ConcDegOne Wrm → ConcDegOne W₂m →
    Function.Injective (im.f 1 1 rfl) →
    (∀ y, pm.f 1 1 rfl y = 0 ↔ ∃ x, im.f 1 1 rfl x = y) →
    (∀ n x, im.f n n rfl (q₁.f n n rfl x) = qr.f n n rfl (i.f n n rfl x)) →
    (∀ n x, pm.f n n rfl (qr.f n n rfl x) = q₂.f n n rfl (p.f n n rfl x)) →
      Subsingleton (W₁.toCC.homology 0) ∧ Function.Injective (H1 i) ∧
        LinearMap.ker (H1 p) = LinearMap.range (H1 i)

theorem quasiModelHypotheses_proof : QuasiModelHypotheses := by
  intro k _ W₁ Wr W₂ W₁m Wrm W₂m i p q₁ qr q₂ im pm hq₁ hqr hq₂ h₁ hr h₂ him hexm hsq₁ hsq₂
  obtain ⟨h0m, hiHm, hpiHm⟩ := degreeOne_hypotheses h₁ hr h₂ im pm him hexm
  have b₁ := H1_bijective_of_quasiIso q₁
  have br := H1_bijective_of_quasiIso qr
  have b₂ := H1_bijective_of_quasiIso q₂
  have sq₁ : ∀ x, H1 im (H1 q₁ x) = H1 qr (H1 i x) := fun x =>
    H1_square q₁ im i qr hsq₁ x
  have sq₂ : ∀ y, H1 pm (H1 qr y) = H1 q₂ (H1 p y) := fun y =>
    H1_square qr pm p q₂ hsq₂ y
  refine ⟨?_, fun x y hxy => ?_, ?_⟩
  · -- `H⁰(W₁) ≅ H⁰(W₁m) = 0`
    have : IsIso (HomologicalComplex.homologyMap (GHom.toCC q₁) 0) :=
      (quasiIsoAt_iff_isIso_homologyMap (GHom.toCC q₁) 0).mp inferInstance
    have hb := ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap (GHom.toCC q₁) 0)
    exact ⟨fun a b => hb.1 (Subsingleton.elim _ _)⟩
  · apply b₁.1
    apply hiHm
    change H1 im (H1 q₁ x) = H1 im (H1 q₁ y)
    rw [sq₁, sq₁, hxy]
  · ext y
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      have h0 : H1 pm (H1 qr y) = 0 := by rw [sq₂, hy, map_zero]
      have hmem : H1 qr y ∈ LinearMap.ker (H1 pm) := h0
      change H1 qr y ∈ LinearMap.ker (HomologicalComplex.homologyMap (GHom.toCC pm) 1).hom at hmem
      rw [hpiHm] at hmem
      obtain ⟨xm, hxm⟩ := hmem
      obtain ⟨x, rfl⟩ := b₁.2 xm
      refine ⟨x, br.1 ?_⟩
      rw [← sq₁]; exact hxm
    · rintro ⟨x, rfl⟩
      apply b₂.1
      rw [← sq₂, ← sq₁, map_zero]
      have : H1 im (H1 q₁ x) ∈ LinearMap.range (H1 im) := ⟨_, rfl⟩
      change _ ∈ LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC im) 1).hom at this
      rw [← hpiHm] at this
      exact this

/-! ### The literal version is a special case -/

/-- The homology-level relaxed localization of a literal one: coordinates
`H¹(W_rel) ≃ W_rel¹ ≃ k² × k²`. -/
def RelaxedLocalization.toQuasi (R : RelaxedLocalization k) : QuasiRelaxedLocalization k where
  D := R.D
  Wrel := R.Wrel
  gR := R.gR
  eR := (h1Equiv R.Wrel R.hWrel).trans R.eR

theorem RelaxedLocalization.toQuasi_U (R : RelaxedLocalization k) : R.toQuasi.U = R.U := rfl

/-- A literal switch side is a quasi switch side (with the same Selmer data). PROVED. -/
def SwitchSide.toQuasi {R : RelaxedLocalization k} {P : Submodule k ((Fin 2 → k) × (Fin 2 → k))}
    (S : SwitchSide R P) : QuasiSwitchSide R.toQuasi P where
  U₁ := S.U₁
  Ustr := S.Ustr
  W₁ := S.W₁
  W₂ := S.W₂
  f₁ := S.f₁
  g₂ := S.g₂
  fs := S.fs
  g₁ := S.g₁
  i := S.i
  p := S.p
  hfg₂ := S.hfg₂
  f₁_inj := S.f₁_inj
  g₂_surj := S.g₂_surj
  ex₂ := S.ex₂
  hfg₁ := S.hfg₁
  fs_inj := S.fs_inj
  g₁_surj := S.g₁_surj
  ex₁ := S.ex₁
  hRF := S.hRF
  hpR := S.hpR
  h0 := (degreeOne_hypotheses S.hW₁ R.hWrel S.hW₂ S.i S.p S.i_inj S.ip_exact).1
  hi := (degreeOne_hypotheses S.hW₁ R.hWrel S.hW₂ S.i S.p S.i_inj S.ip_exact).2.1
  hpi := (degreeOne_hypotheses S.hW₁ R.hWrel S.hW₂ S.i S.p S.i_inj S.ip_exact).2.2
  hP := by
    conv_rhs => rw [← S.hP]
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨h1Equiv S.W₁ S.hW₁ x, ?_⟩
      change _ = R.eR (h1Equiv R.Wrel R.hWrel
        ((HomologicalComplex.homologyMap (GHom.toCC S.i) 1).hom x))
      rw [h1Equiv_natural S.hW₁ R.hWrel]
    · rintro ⟨x, rfl⟩
      refine ⟨_, ⟨(h1Equiv S.W₁ S.hW₁).symm x, rfl⟩, ?_⟩
      change R.eR (h1Equiv R.Wrel R.hWrel
        ((HomologicalComplex.homologyMap (GHom.toCC S.i) 1).hom ((h1Equiv S.W₁ S.hW₁).symm x))) = _
      rw [h1Equiv_natural S.hW₁ R.hWrel, LinearEquiv.apply_symm_apply]

/-- **The literal (5.5a) is the special case** of the quasi version: for literal sides the quasi
dimension equations are the equations of `switchDims_of_selmerData` (same Selmer data, same `U`).
PROVED. -/
theorem switchDims_literal_special_case (R : RelaxedLocalization k)
    (SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    [FiniteDimensional k (R.D.G.X 1)] [FiniteDimensional k (R.D.L.X 0)]
    [FiniteDimensional k (SF.U₁.X 1)] [FiniteDimensional k (SS.U₁.X 1)] :
    finrank k ((selCx SF.Dside).toCC.homology 1) = finrank k ((selCx SF.Dstr).toCC.homology 1) +
        finrank k ↥(R.U ⊓ finPlane k (Fin 2 → k) (Fin 2 → k)) ∧
    finrank k ((selCx SS.Dside).toCC.homology 1) = finrank k ((selCx SS.Dstr).toCC.homology 1) +
        finrank k ↥(R.U ⊓ singPlane k (Fin 2 → k) (Fin 2 → k)) := by
  have : FiniteDimensional k (R.toQuasi.D.G.X 1) := by change FiniteDimensional k (R.D.G.X 1); infer_instance
  have : FiniteDimensional k (R.toQuasi.D.L.X 0) := by change FiniteDimensional k (R.D.L.X 0); infer_instance
  have : FiniteDimensional k (SF.toQuasi.U₁.X 1) := by change FiniteDimensional k (SF.U₁.X 1); infer_instance
  have : FiniteDimensional k (SS.toQuasi.U₁.X 1) := by change FiniteDimensional k (SS.U₁.X 1); infer_instance
  exact quasiSwitchDims_of_selmerData R.toQuasi SF.toQuasi SS.toQuasi

/-! ### Item (1): the relaxed localization image is Lagrangian -/

/-- **The localization image is its own annihilator** (tex L5068–5075: "localization's connecting
map is its dual under the strict/relaxed duality, so its kernel is both `U` and `U^⊥`"). Let
`V --λ--> W --δ--> V'` be exact at `W`, `⟨·,·⟩ : V' × V → k` separating in the first variable, and `B`
a bilinear form on `W` with `⟨δ w, v⟩ = B(λ v, w)`. Then `(im λ)^⊥_B = im λ`. Classification:
PROVED. -/
def LocalizationLagrangian : Prop :=
  ∀ (k : Type) [Field k] (V W V' : Type) [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [AddCommGroup V'] [Module k V'] (lam : V →ₗ[k] W) (δ : W →ₗ[k] V')
    (pair : V' →ₗ[k] V →ₗ[k] k) (B : LinearMap.BilinForm k W),
    LinearMap.range lam = LinearMap.ker δ →
    (∀ x : V', (∀ v, pair x v = 0) → x = 0) →
    (∀ w v, pair (δ w) v = B (lam v) w) →
      B.orthogonal (LinearMap.range lam) = LinearMap.range lam

theorem localizationLagrangian_proof : LocalizationLagrangian := by
  intro k _ V W V' _ _ _ _ _ _ lam δ pair B hex hsep hadj
  ext w
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    rw [hex, LinearMap.mem_ker]
    apply hsep
    intro v
    rw [hadj]
    exact h _ ⟨v, rfl⟩
  · intro hw n hn
    rw [hex, LinearMap.mem_ker] at hw
    obtain ⟨v, rfl⟩ := hn
    change B (lam v) w = 0
    rw [← hadj, hw, map_zero, LinearMap.zero_apply]

/-- **GLUE input: the strict/relaxed duality at the switch is adjoint to localization** (Nekovář,
*Selmer complexes*, 6.3.3–6.3.4, cited at tex L5068–5075; for genuine complexes the separating
pairing is supplied by the other team's `genuineSelmerDuality` for the pair strict/relaxed, and the
adjunction is its compatibility with the cone triangle). For the relaxed localization `R` with strict
Selmer data `Dstr` and the connecting map `δ : H¹(W_rel) → H²(C_str)` of
`0 → C_str → C_rel → W_rel → 0`, exact at `H¹(W_rel)` after `H¹(λ)`: there is a pairing
`H²(C_str) × H¹(C_rel) → k`, separating in the first variable, with
`⟨δ w, v⟩ = β(λ v, w)` for the switch pairing `β = switchPairing ε σ J` transported by the coordinates
`R.eR`. The stateable hypotheses (`ε, σ ≠ 0`, `J² = 1`, exactness) are in the type.
Classification: GLUE (assumed input). -/
def SwitchDualityAdjunction (R : QuasiRelaxedLocalization k) (Dstr : SelData k) (ε σ : k)
    (J : Matrix (Fin 2) (Fin 2) k) (_hε : ε ≠ 0) (_hσ : σ ≠ 0) (_hJ2 : J * J = 1)
    (δ : R.Wrel.toCC.homology 1 →ₗ[k] (selCx Dstr).toCC.homology 2)
    (_hex : LinearMap.range (H1 (quotMap R.D R.gR)) = LinearMap.ker δ) : Prop :=
  ∃ pair : (selCx Dstr).toCC.homology 2 →ₗ[k] (selCx R.D).toCC.homology 1 →ₗ[k] k,
    (∀ x, (∀ v, pair x v = 0) → x = 0) ∧
    ∀ w v, pair (δ w) v = switchPairing ε σ J (R.eR (H1 (quotMap R.D R.gR) v)) (R.eR w)

/-- **`LocalizationDualityInput` from the duality adjunction** (tex L5068–5075): under
`SwitchDualityAdjunction`, the actual relaxed localization image `U = R.U` is its own annihilator for
the switch pairing — the GLUE input `LocalizationDualityInput` of `ExactSequences.lean`, now derived.
Classification: PROVED (from the input). -/
theorem localizationDualityInput_of_adjunction (R : QuasiRelaxedLocalization k) (Dstr : SelData k)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (δ : R.Wrel.toCC.homology 1 →ₗ[k] (selCx Dstr).toCC.homology 2)
    (hex : LinearMap.range (H1 (quotMap R.D R.gR)) = LinearMap.ker δ)
    (hadj : SwitchDualityAdjunction R Dstr ε σ J hε hσ hJ2 δ hex) :
    LocalizationDualityInput ε σ J hε hσ hJ2 R.U := by
  obtain ⟨pair, hsep, hpair⟩ := hadj
  -- transport to the coordinates: `λ' = eR ∘ H¹(λ)`, `δ' = δ ∘ eR⁻¹`
  set lam' := R.eR.toLinearMap ∘ₗ H1 (quotMap R.D R.gR)
  set δ' := δ ∘ₗ R.eR.symm.toLinearMap
  have hex' : LinearMap.range lam' = LinearMap.ker δ' := by
    ext y
    simp only [lam', δ', LinearMap.mem_range, LinearMap.mem_ker, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, rfl⟩
      rw [LinearEquiv.symm_apply_apply, ← LinearMap.mem_ker, ← hex]
      exact ⟨v, rfl⟩
    · intro h
      have : R.eR.symm y ∈ LinearMap.range (H1 (quotMap R.D R.gR)) := by
        rw [hex]; exact h
      obtain ⟨v, hv⟩ := this
      exact ⟨v, by rw [hv, LinearEquiv.apply_symm_apply]⟩
  have hadj' : ∀ w v, pair (δ' w) v = switchPairing ε σ J (lam' v) w := by
    intro w v
    simp only [δ', lam', LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [hpair, LinearEquiv.apply_symm_apply]
  have h := localizationLagrangian_proof k _ _ _ lam' δ' pair (switchPairing ε σ J) hex' hsep
    hadj'
  have hU : R.U = LinearMap.range lam' := by
    rw [QuasiRelaxedLocalization.U, LinearMap.range_comp]
  unfold LocalizationDualityInput
  rw [hU]
  exact h

/-! ### Non-vacuity (LESSON 2) -/

/-- The quasi relaxed localization of the degree-one example `exRel` over `ℚ`. -/
def exQuasiRel : QuasiRelaxedLocalization ℚ := exRel.toQuasi

/-- Quasi switch sides over `ℚ` (the literal sides `exSideF`, `exSideS` of `NonVacuity.lean`). -/
def exQuasiSideF : QuasiSwitchSide exQuasiRel (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) :=
  exSideF.toQuasi

def exQuasiSideS : QuasiSwitchSide exQuasiRel (singPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) :=
  exSideS.toQuasi

/-- **Non-vacuity**: the quasi relaxed image of the example is the finite plane, and the quasi
version of (5.5a) applies to it. PROVED. -/
theorem exQuasiRel_U : exQuasiRel.U = finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := exRel_U

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

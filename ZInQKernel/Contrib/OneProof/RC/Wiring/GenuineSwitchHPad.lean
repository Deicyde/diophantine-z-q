import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHPK
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel

/-!
**Theorem 5.3: padding a configuration family by an infinite-dimensional contractible summand**

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity, including quadratic
specializations", tex 4976–5195 (switch sequences (5.5a), tex 5055–5086).

The text's switching argument only reads cohomology: the fibre dimension `s = dim_k H¹(C ⊗ k)`
(tex 4983–4996) and the dimension counts of the switch exact sequences (tex 5055–5086). Padding a
fibre by a contractible summand changes no cohomology. This file makes that precise and draws the
consequence for the two forms of the height-one switching data.

* `hpadC k V`: the contractible complex with every term `V × V`, differential `(x, y) ↦ (0, x)` and
  contraction `(x, y) ↦ (y, 0)` (`hpadC_homotopy`: `𝟙 ≃ 0`).
* `hpadSel D V`: the Selmer data `D` with global complex `G ⊕ hpadC V` (degreewise), restriction
  reading only `G`, the same local conditions. Its global 1-cochains are `G¹ × (V × V)`.
* `hpadRetract D V`: a normalized graded deformation retract (lane RC31's `GRetract`) of
  `C(hpadSel D V)` onto `C(D)`, hence `hpadEquiv D V : C(hpadSel D V) ≃ C(D)` (homotopy equivalence,
  `hom` the projection, `inv` the inclusion, `inv ≫ hom = 𝟙` on the nose) and
  `hpadH1 D V : H¹(C(hpadSel D V)) ≃ H¹(C(D))`.
* Naturality: `hpad_quotMap`, `hpad_H1_quotMap`, `hpadRel_U` (the relaxed localization image is
  unchanged); `hpadSide`, `hpadNonquad` transport the homology-level switch sides and nonquadratic
  steps of the RC53 group to the padded data, with the sides the padded fibres.
* `hpadFamily Φ V`: the configuration family with every fibre padded; `HomologySwitchDataPK.hpad`:
  homology-level switching data over `Φ` (nonquadratic) give the same data over `hpadFamily Φ V`.

**The old data die.** The old structure `GenuineSwitchDataPK` takes its switch steps from batch 3,
whose model steps demand `fG : FiniteDimensional k (R.D.G.X 1)` with the side tied to the fibre. So
the homology-level structure `HomologySwitchDataPK` cannot distinguish a fibre from its padding,
while the old structure's `fG` does: `hpad_isEmpty_genuinePK` — if a homology-level datum over `Φ`
demands a switch at the start (`s > 1`) and `V` is infinite-dimensional, there is no old datum over
the padded family (any old datum has the same fibre dimensions, its demanded switch forces
finite-dimensional global 1-cochains `G¹ × (V × V)`). `hpad_separates` packages this: over the padded
family the homology-level data exist and the old data do not. This is evidence, in the sense of the
non-vacuity requirement, that the homology-level structure removes the `fG` obstruction.

Non-vacuity: `hpadInf` (`ℕ →₀ k` is infinite-dimensional) and `hpadExData` (the padding applied to
the existing one-configuration example of batch 3, a homology-level datum over a family whose fibres
have infinite-dimensional global 1-cochains). The family with a demanded switch to which
`hpad_separates` applies is built in a separate file of lane RC29.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Module ZInQ.Manuscript.RC.Uniform
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Uniform.QuadraticCase
open ZInQ.Manuscript.RC.Limits (GRetract homotopyOfIdentities toCC_d_hom_eq)

/-! **The contractible summand** -/

section Contractible

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]

/-- The differential `(x, y) ↦ (0, x)` of the contractible complex. Kind: definition. -/
def hpadDiff : V × V →ₗ[k] V × V := LinearMap.inr k V V ∘ₗ LinearMap.fst k V V

/-- The contraction `(x, y) ↦ (y, 0)` of the contractible complex. Kind: definition. -/
def hpadContr : V × V →ₗ[k] V × V := LinearMap.inl k V V ∘ₗ LinearMap.snd k V V

/-- The differential of the summand: `d (x, y) = (0, x)`. Kind: PROVED. -/
theorem hpadDiff_apply (c : V × V) : hpadDiff k V c = (0, c.1) := rfl

/-- The contraction of the summand: `h (x, y) = (y, 0)`. Kind: PROVED. -/
theorem hpadContr_apply (c : V × V) : hpadContr k V c = (c.2, 0) := rfl

/-- **`d h + h d = 1`** on `V × V`. Kind: PROVED. -/
theorem hpad_diff_contr (c : V × V) :
    hpadDiff k V (hpadContr k V c) + hpadContr k V (hpadDiff k V c) = c := by
  rw [hpadDiff_apply, hpadContr_apply, hpadContr_apply, hpadDiff_apply]
  exact Prod.ext (zero_add c.1) (add_zero c.2)

/-- **The contractible complex** `hpadC k V`: `V × V` in every degree, differential
`(x, y) ↦ (0, x)`. Kind: definition. -/
def hpadC : GCx k where
  X _ := ModuleCat.of k (V × V)
  d _ _ _ := hpadDiff k V
  d_d _ _ _ _ _ _ := rfl

/-- **`hpadC k V` is contractible**: the identity is homotopic to zero, through the contraction
`(x, y) ↦ (y, 0)`. Kind: PROVED. -/
def hpadC_homotopy : Homotopy (𝟙 (hpadC k V).toCC) 0 :=
  homotopyOfIdentities _ _ (fun _ _ _ => hpadContr k V) (by
    intro a
    rw [toCC_d_hom_eq (hpadC k V) a (a + 1) rfl, toCC_d_hom_eq (hpadC k V) (a - 1) a (by omega)]
    refine LinearMap.ext fun (c : V × V) => ?_
    show c = hpadContr k V (hpadDiff k V c) + hpadDiff k V (hpadContr k V c) + (0 : V × V)
    rw [add_zero, add_comm, hpad_diff_contr])

end Contractible

/-! **The padded Selmer data** -/

section Padded

variable {k : Type} [Field k]

/-- The degreewise product of two complexes. Kind: definition. -/
def hpadProd (A B : GCx k) : GCx k where
  X n := ModuleCat.of k (A.X n × B.X n)
  d i j h := (A.d i j h).prodMap (B.d i j h)
  d_d i j l hij hjl x := Prod.ext (A.d_d i j l hij hjl x.1) (B.d_d i j l hij hjl x.2)

/-- The restriction `res ∘ pr₁` of the padded global complex: it reads only the first factor.
Kind: definition. -/
def hpadRes {G L : GCx k} (res : GHom G L) (V : Type) [AddCommGroup V] [Module k V] :
    GHom (hpadProd G (hpadC k V)) L where
  f i j h := (res.f i j h).comp (LinearMap.fst k (G.X i) (V × V))
  comm i i₁ j j₁ hij h₁ h₂ hj x := res.comm i i₁ j j₁ hij h₁ h₂ hj x.1

/-- **The padded Selmer data** `hpadSel D V`: global complex `G ⊕ hpadC V` (degreewise product),
restriction `res ∘ pr₁`, the same local conditions `U`, `L`, `ι`. Kind: definition. -/
def hpadSel (D : SelData k) (V : Type) [AddCommGroup V] [Module k V] : SelData k :=
  ⟨hpadProd D.G (hpadC k V), D.U, D.L, hpadRes D.res V, D.ι⟩

variable (D : SelData k) (V : Type) [AddCommGroup V] [Module k V]

/-- The global cochains of the padded data are `Gⁿ × (V × V)`. Kind: PROVED. -/
theorem hpadSel_G_X (n : ℤ) : ((hpadSel D V).G.X n : Type) = (D.G.X n × (V × V)) := rfl

/-- **Padding commutes with changing the local condition** (definitionally). Kind: PROVED. -/
theorem hpadSel_restrict {U' : GCx k} (f : GHom U' D.U) :
    ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData (hpadSel D V) f = hpadSel (ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData D f) V := rfl

/-- The projection `((a, c), u, x) ↦ (a, u, x)` in degree `n`. Kind: definition. -/
def hpadProjMap (n : ℤ) : selT (hpadSel D V) n →ₗ[k] selT D n :=
  (LinearMap.fst k (D.G.X n) (V × V)).prodMap LinearMap.id

/-- The inclusion `(a, u, x) ↦ ((a, 0), u, x)` in degree `n`. Kind: definition. -/
def hpadInclMap (n : ℤ) : selT D n →ₗ[k] selT (hpadSel D V) n :=
  (LinearMap.inl k (D.G.X n) (V × V)).prodMap LinearMap.id

/-- The homotopy `((a, c), u, x) ↦ ((0, h c), 0, 0)` from degree `a` to degree `b`.
Kind: definition. -/
def hpadHtpyMap (a b : ℤ) : selT (hpadSel D V) a →ₗ[k] selT (hpadSel D V) b :=
  LinearMap.inl k (D.G.X b × (V × V)) (D.U.X b × D.L.X (b - 1)) ∘ₗ
    LinearMap.inr k (D.G.X b) (V × V) ∘ₗ hpadContr k V ∘ₗ
      LinearMap.snd k (D.G.X a) (V × V) ∘ₗ
        LinearMap.fst k (D.G.X a × (V × V)) (D.U.X a × D.L.X (a - 1))

/-- **The projection of the padded Selmer complex** `C(hpadSel D V) → C(D)`, dropping the
contractible summand. Kind: definition. -/
def hpadProj : GHom (selCx (hpadSel D V)) (selCx D) where
  f i j h := h ▸ hpadProjMap D V i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

/-- **The inclusion** `C(D) → C(hpadSel D V)` with zero contractible component.
Kind: definition. -/
def hpadIncl : GHom (selCx D) (selCx (hpadSel D V)) where
  f i j h := h ▸ hpadInclMap D V i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

/-- The components of the projection. Kind: PROVED. -/
theorem hpadProj_apply (n : ℤ) (x : (selCx (hpadSel D V)).X n) :
    (hpadProj D V).f n n rfl x = hpadProjMap D V n x := rfl

/-- The components of the inclusion. Kind: PROVED. -/
theorem hpadIncl_apply (n : ℤ) (x : (selCx D).X n) :
    (hpadIncl D V).f n n rfl x = hpadInclMap D V n x := rfl

/-- **The padding is a normalized graded deformation retract** (lane RC31's `GRetract`, the
interface of Lemma `ex:limits-inner-limit`, tex 4423–4437) of `C(hpadSel D V)` onto `C(D)`:
`p i = 1`, `1 − i p = d h + h d` with `h((a, c), u, x) = ((0, (c₂, 0)), 0, 0)`, `h² = 0`, `h i = 0`,
`p h = 0`. Kind: PROVED. -/
def hpadRetract : GRetract (selCx (hpadSel D V)) (selCx D) where
  i := hpadIncl D V
  p := hpadProj D V
  h a b _ := hpadHtpyMap D V a b
  p_i _ _ := rfl
  homotopy n x := by
    obtain ⟨⟨a, c⟩, u, y⟩ := x
    have hc := hpad_diff_contr k V c
    show ((((a, c), u, y) : (D.G.X n × (V × V)) × D.U.X n × D.L.X (n - 1)) -
        (((a, 0), u, y) : (D.G.X n × (V × V)) × D.U.X n × D.L.X (n - 1))) =
      (((D.G.d (n - 1) n (by omega) 0, hpadDiff k V (hpadContr k V c)), D.U.d (n - 1) n (by omega) 0,
        D.res.f (n - 1) (n - 1) (by omega) 0 - D.ι.f (n - 1) (n - 1) (by omega) 0 -
          D.L.d (n - 1 - 1) (n - 1) (by omega) 0) : (D.G.X n × (V × V)) × D.U.X n × D.L.X (n - 1)) +
      (((0, hpadContr k V (hpadDiff k V c)), 0, 0) : (D.G.X n × (V × V)) × D.U.X n × D.L.X (n - 1))
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp [hc]
    exact sub_zero _
  h_h _ _ _ _ _ _ := rfl
  h_i _ _ _ _ := rfl
  p_h _ _ _ _ := rfl

/-- **Padding is a homotopy equivalence** `C(hpadSel D V) ≃ C(D)`: `hom` the projection, `inv` the
inclusion (`inv ≫ hom = 𝟙` on the nose, `hom ≫ inv ≃ 𝟙` through the contraction of the summand).
Kind: PROVED. -/
def hpadEquiv : HomotopyEquiv (selCx (hpadSel D V)).toCC (selCx D).toCC :=
  (hpadRetract D V).homotopyEquiv.symm

/-- `hom` of `hpadEquiv` is the projection. Kind: PROVED. -/
theorem hpadEquiv_hom : (hpadEquiv D V).hom = GHom.toCC (hpadProj D V) := rfl

/-- `inv` of `hpadEquiv` is the inclusion. Kind: PROVED. -/
theorem hpadEquiv_inv : (hpadEquiv D V).inv = GHom.toCC (hpadIncl D V) := rfl

/-- The formula for `hom`: `((a, c), u, x) ↦ (a, u, x)`. Kind: PROVED. -/
theorem hpadEquiv_hom_f (n : ℤ) (a : D.G.X n) (c : V × V) (u : D.U.X n) (y : D.L.X (n - 1)) :
    ((hpadEquiv D V).hom.f n).hom (((a, c), u, y) : selT (hpadSel D V) n) =
      ((a, u, y) : selT D n) := rfl

/-- The formula for `inv`: `(a, u, x) ↦ ((a, 0), u, x)`. Kind: PROVED. -/
theorem hpadEquiv_inv_f (n : ℤ) (a : D.G.X n) (u : D.U.X n) (y : D.L.X (n - 1)) :
    ((hpadEquiv D V).inv.f n).hom ((a, u, y) : selT D n) =
      (((a, 0), u, y) : selT (hpadSel D V) n) := rfl

/-- **`inv ≫ hom = 𝟙`** on the nose. Kind: PROVED. -/
theorem hpadEquiv_inv_hom : (hpadEquiv D V).inv ≫ (hpadEquiv D V).hom = 𝟙 _ := by
  ext n x
  rfl

/-- **`H¹` is unchanged by padding**: `H¹(C(hpadSel D V)) ≃ H¹(C(D))`, the map on `H¹` of the
projection. Kind: PROVED. -/
def hpadH1 : (selCx (hpadSel D V)).toCC.homology 1 ≃ₗ[k] (selCx D).toCC.homology 1 :=
  ((hpadEquiv D V).toHomologyIso 1).toLinearEquiv

/-- `hpadH1` is `H¹` of the projection. Kind: PROVED. -/
theorem hpadH1_apply (x : (selCx (hpadSel D V)).toCC.homology 1) :
    hpadH1 D V x = H1 (hpadProj D V) x := rfl

/-- `dim H¹` is unchanged by padding. Kind: PROVED. -/
theorem hpad_finrank_h1 :
    finrank k ((selCx (hpadSel D V)).toCC.homology 1) = finrank k ((selCx D).toCC.homology 1) :=
  (hpadH1 D V).finrank_eq

/-- `H¹` of the projection after `H¹` of the inclusion is the identity. Kind: PROVED. -/
theorem hpad_H1_proj_incl (y : (selCx D).toCC.homology 1) :
    H1 (hpadProj D V) (H1 (hpadIncl D V) y) = y := by
  have h : GHom.toCC (hpadIncl D V) ≫ GHom.toCC (hpadProj D V) = 𝟙 _ := hpadEquiv_inv_hom D V
  change (HomologicalComplex.homologyMap (GHom.toCC (hpadIncl D V)) 1 ≫
    HomologicalComplex.homologyMap (GHom.toCC (hpadProj D V)) 1).hom y = y
  rw [← HomologicalComplex.homologyMap_comp, h, HomologicalComplex.homologyMap_id]
  rfl

/-- `H¹` of the projection is surjective (split by `H¹` of the inclusion). Kind: PROVED. -/
theorem hpad_H1_proj_surjective : Function.Surjective (H1 (hpadProj D V)) :=
  fun y => ⟨H1 (hpadIncl D V) y, hpad_H1_proj_incl D V y⟩

/-- **Naturality of the quotient map**: `quotMap` of the padded data is the projection followed by
`quotMap` of `D` (it reads only the local condition). Kind: PROVED. -/
theorem hpad_quotMap {W : GCx k} (g : GHom D.U W) :
    quotMap (hpadSel D V) g = ghomComp (hpadProj D V) (quotMap D g) :=
  ghom_ext fun _ _ => rfl

/-- **Naturality on `H¹`**: `H¹(quotMap (hpadSel D V) g) = H¹(quotMap D g) ∘ H¹(projection)`.
Kind: PROVED. -/
theorem hpad_H1_quotMap {W : GCx k} (g : GHom D.U W) :
    H1 (quotMap (hpadSel D V) g) = H1 (quotMap D g) ∘ₗ H1 (hpadProj D V) := by
  rw [hpad_quotMap]
  exact LinearMap.ext fun x => (H1_comp_apply _ _ x).symm

/-- The inclusion sends cycles to cycles (degree one). Kind: PROVED. -/
theorem hpadIncl_cycle (z : (selCx D).toCC.X 1) (hz : ((selCx D).toCC.d 1 2).hom z = 0) :
    ((selCx (hpadSel D V)).toCC.d 1 2).hom (((hpadEquiv D V).inv.f 1).hom z) = 0 := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f z) ((hpadEquiv D V).inv.comm 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, hz, map_zero]

/-- A functional killing coboundaries, pulled back along the projection, kills coboundaries.
Kind: PROVED. -/
theorem hpadProj_cocycle (lam : (selCx D).toCC.X 2 →ₗ[k] k)
    (hlam : ∀ y, lam (((selCx D).toCC.d 1 2).hom y) = 0) (y : (selCx (hpadSel D V)).toCC.X 1) :
    (lam ∘ₗ ((hpadEquiv D V).hom.f 2).hom) (((selCx (hpadSel D V)).toCC.d 1 2).hom y) = 0 := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f y) ((hpadEquiv D V).hom.comm 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [LinearMap.comp_apply, ← h]
  exact hlam _

end Padded

/-! **Padded relaxed localizations, switch sides and nonquadratic steps** -/

section Steps

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **The padded relaxed localization** `⟨hpadSel R.D V, W_rel, g_R, e_R⟩` (tex 5068–5075): the
relaxed Selmer data padded, the relaxed quotient and its coordinates unchanged.
Kind: definition. -/
def hpadRel (R : QuasiRelaxedLocalization k) (V : Type) [AddCommGroup V] [Module k V] :
    QuasiRelaxedLocalization k :=
  ⟨hpadSel R.D V, R.Wrel, R.gR, R.eR⟩

/-- **The relaxed localization image is unchanged by padding** (tex 5068–5075):
`H¹(quotMap)` of the padded data is `H¹(quotMap)` of `R.D` after the surjection `H¹(projection)`.
Kind: PROVED. -/
theorem hpadRel_U (R : QuasiRelaxedLocalization k) (V : Type) [AddCommGroup V] [Module k V] :
    (hpadRel R V).U = R.U := by
  show (LinearMap.range (H1 (quotMap (hpadSel R.D V) R.gR))).map R.eR.toLinearMap =
    (LinearMap.range (H1 (quotMap R.D R.gR))).map R.eR.toLinearMap
  rw [hpad_H1_quotMap, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (hpad_H1_proj_surjective R.D V))]

variable {R : QuasiRelaxedLocalization k} {P : Submodule k ((Fin 2 → k) × (Fin 2 → k))}

/-- **The padded switch side** (tex 5055–5086): the same side, strict and quotient conditions over
the padded relaxed localization (the fields only involve `R.D.U`, `W_rel`, `g_R`, `e_R`, which
padding does not change). Kind: definition. -/
def hpadSide (S : QuasiSwitchSide R P) (V : Type) [AddCommGroup V] [Module k V] :
    QuasiSwitchSide (hpadRel R V) P where
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
  h0 := S.h0
  hi := S.hi
  hpi := S.hpi
  hP := S.hP

/-- The side Selmer data of the padded side are the padded side Selmer data. Kind: PROVED. -/
theorem hpadSide_Dside (S : QuasiSwitchSide R P) (V : Type) [AddCommGroup V] [Module k V] :
    (hpadSide S V).Dside = hpadSel S.Dside V := rfl

/-- The strict Selmer data of the padded side are the padded strict Selmer data. Kind: PROVED. -/
theorem hpadSide_Dstr (S : QuasiSwitchSide R P) (V : Type) [AddCommGroup V] [Module k V] :
    (hpadSide S V).Dstr = hpadSel S.Dstr V := rfl

/-- **The padded homology-level nonquadratic step** (tex 4997–5003, 5055–5086): the padded relaxed
localization and sides; `hk0` by `dim H¹` invariance; the duality and detection through
`hpadRel_U`; the fibre isomorphisms precomposed with `hpadH1`. Kind: definition. -/
def hpadNonquad {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι} (N : QuasiNonquadStep ρ S S')
    (V : Type) [AddCommGroup V] [Module k V] : QuasiNonquadStep ρ S S' where
  R := hpadRel N.R V
  SF := hpadSide N.SF V
  SS := hpadSide N.SS V
  hk0 := (hpad_finrank_h1 N.SF.Dstr V).trans (N.hk0.trans (hpad_finrank_h1 N.SS.Dstr V).symm)
  ε := N.ε
  σ := N.σ
  J := N.J
  hε := N.hε
  hσ := N.hσ
  hJ2 := N.hJ2
  hdual := by rw [hpadRel_U]; exact N.hdual
  hdet := by rw [hpadRel_U]; exact N.hdet
  φ := (hpadH1 N.SF.Dside V).trans N.φ
  φ' := (hpadH1 N.SS.Dside V).trans N.φ'

/-- The finite side of the padded step is the padded finite side (tex 5055–5086).
Kind: PROVED. -/
theorem hpadNonquad_SF_Dside {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι}
    (N : QuasiNonquadStep ρ S S') (V : Type) [AddCommGroup V] [Module k V] :
    (hpadNonquad N V).SF.Dside = hpadSel N.SF.Dside V := rfl

/-- The singular side of the padded step is the padded singular side (tex 5055–5086).
Kind: PROVED. -/
theorem hpadNonquad_SS_Dside {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι}
    (N : QuasiNonquadStep ρ S S') (V : Type) [AddCommGroup V] [Module k V] :
    (hpadNonquad N V).SS.Dside = hpadSel N.SS.Dside V := rfl

end Steps

/-! **The padded configuration family and the padded homology-level switching data** -/

section Family

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **The padded configuration family** (tex 4976–5195): the same configurations, primes, actual
configuration, successor and moving variable `t`; every fibre padded; the actual class included
with zero contractible component, the actual functional pulled back along the projection.
Kind: definition. -/
def hpadFamily (Φ : SwitchFamily k A) (V : Type) [AddCommGroup V] [Module k V] :
    SwitchFamily k A where
  Config := Φ.Config
  Prime := Φ.Prime
  actual := Φ.actual
  next := Φ.next
  fibre c := hpadSel (Φ.fibre c) V
  t := Φ.t
  zAct := ((hpadEquiv (Φ.fibre Φ.actual) V).inv.f 1).hom Φ.zAct
  hzAct := hpadIncl_cycle (Φ.fibre Φ.actual) V Φ.zAct Φ.hzAct
  lamAct := Φ.lamAct ∘ₗ ((hpadEquiv (Φ.fibre Φ.actual) V).hom.f 2).hom
  hlamAct := hpadProj_cocycle (Φ.fibre Φ.actual) V Φ.lamAct Φ.hlamAct

/-- The fibres of the padded family are the padded fibres. Kind: PROVED. -/
theorem hpadFamily_fibre (Φ : SwitchFamily k A) (V : Type) [AddCommGroup V] [Module k V]
    (c : Φ.Config) : (hpadFamily Φ V).fibre c = hpadSel (Φ.fibre c) V := rfl

/-- The padded family is quadratic exactly when `Φ` is (same `t`). Kind: PROVED. -/
theorem hpadFamily_quadratic (Φ : SwitchFamily k A) (V : Type) [AddCommGroup V] [Module k V]
    (ρ : A →+* k) : (hpadFamily Φ V).quadratic ρ ↔ Φ.quadratic ρ := Iff.rfl

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **Homology-level switching data transfer to the padded family** (tex 4976–5195; nonquadratic
`Φ`): the same stages, signs and classes; the models `C(hpadSel (fibre c) V) ≃ C(fibre c) ≃ model`
(`hpadEquiv` then the old model); the nonquadratic switches through `hpadNonquad`, whose sides are the
padded fibres; the quadratic branches are vacuous. Kind: PROVED. -/
def HomologySwitchDataPK.hpad (G : HomologySwitchDataPK Φ ι ρ u) (hq : ¬ Φ.quadratic ρ)
    (V : Type) [AddCommGroup V] [Module k V] : HomologySwitchDataPK (hpadFamily Φ V) ι ρ u where
  stage := G.stage
  model c := (hpadEquiv (Φ.fibre c) V).trans (G.model c)
  hz0 := G.hz0
  hw0 y := G.hw0 (((hpadEquiv (Φ.fibre Φ.actual) V).hom.f 2).hom y)
  hu0 := G.hu0
  σ := G.σ
  h2 := G.h2
  hσ := G.hσ
  class_ne_zero := G.class_ne_zero
  switch_mixed c hc h1 h2 :=
    (G.switch_mixed c hc h1 h2).elim fun p hp => ⟨p, hp.1, fun q => absurd q hq, fun nq =>
      (hp.2.2 nq).elim fun N hN => ⟨hpadNonquad N V, congrArg (fun D => hpadSel D V) hN.1,
        congrArg (fun D => hpadSel D V) hN.2⟩⟩
  switch_single _ _ q := absurd q hq

/-- The padded datum has the same stages (hence the same fibre dimensions and coordinates).
Kind: PROVED. -/
theorem HomologySwitchDataPK.hpad_stage (G : HomologySwitchDataPK Φ ι ρ u) (hq : ¬ Φ.quadratic ρ)
    (V : Type) [AddCommGroup V] [Module k V] : (G.hpad hq V).stage = G.stage := rfl

/-- The stage fibre dimensions of homology-level data are the `H¹` dimensions of the fibres (tex
4976–4996). Kind: PROVED. -/
theorem hpad_fiberDim_eq_h1 (G : HomologySwitchDataPK Φ ι ρ u) (c : Φ.Config) :
    (G.stage c).fiberDim ρ = finrank k ((selCx (Φ.fibre c)).toCC.homology 1) :=
  fiberDim_eq_h1 k A F ι ρ (G.stage c) (Φ.fibre c) ⟨G.model c⟩

end Family

/-! **The old data die over the padded family** -/

section Death

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]
variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **A demanded switch of an old datum forces finite-dimensional global 1-cochains at its source**
(batch 3's model steps carry `fG`, the side tied to the fibre by `hF`). Kind: PROVED. -/
theorem hpad_switch_forces_finiteDim (G : GenuineSwitchDataPK Φ ι ρ u) {c : Φ.Config}
    (hc : Reach Φ.next Φ.actual c) (h1 : 1 < (G.stage c).fiberDim ρ) :
    FiniteDimensional k ((Φ.fibre c).G.X 1) := by
  by_cases hq : Φ.quadratic ρ
  · by_cases hmix : (0 < finrank k ↥(signPart (G.σ c) (1 : k)) ∧
        0 < finrank k ↥(signPart (G.σ c) (-1 : k)))
    · obtain ⟨p, -, hM, -⟩ := G.switch_mixed c hc (Or.inr hmix) h1
      obtain ⟨M⟩ := hM hq
      have h := M.M.Y.X.fG
      rw [← M.hF]
      exact h
    · obtain ⟨p, -, ⟨M⟩⟩ := G.switch_single c hc hq hmix h1
      have h := M.M.Y.X.fG
      rw [← M.hF]
      exact h
  · obtain ⟨p, -, -, hN⟩ := G.switch_mixed c hc (Or.inl hq) h1
    obtain ⟨N⟩ := hN hq
    have h := N.N.fG
    rw [← N.hF]
    exact h

/-- **The padded fibres have infinite-dimensional global 1-cochains** when `V` is
infinite-dimensional (`G¹ × (V × V)` surjects onto `V`). Kind: PROVED. -/
theorem hpadFamily_not_finiteDimensional (Φ : SwitchFamily k A) (V : Type) [AddCommGroup V]
    [Module k V] (hV : ¬ FiniteDimensional k V) (c : Φ.Config) :
    ¬ FiniteDimensional k (((hpadFamily Φ V).fibre c).G.X 1) := by
  intro h
  have : Module.Finite k ((Φ.fibre c).G.X 1 × (V × V)) := h
  exact hV (Module.Finite.of_surjective
    (LinearMap.fst k V V ∘ₗ LinearMap.snd k ((Φ.fibre c).G.X 1) (V × V))
    (fun v => ⟨(0, (v, 0)), rfl⟩))

/-- **No old datum over the padded family when `dim H¹` of the actual fibre exceeds one**: any old
datum has actual fibre dimension `dim H¹(fibre actual)` (padding does not change it), so its switch
at the start is demanded and forces finite-dimensional global 1-cochains `G¹ × (V × V)`.
Kind: PROVED. -/
theorem hpad_isEmpty_genuinePK_of_h1 (u' : F) (V : Type) [AddCommGroup V] [Module k V]
    (hV : ¬ FiniteDimensional k V)
    (h1 : 1 < finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1)) :
    IsEmpty (GenuineSwitchDataPK (hpadFamily Φ V) ι ρ u') := by
  refine ⟨fun G' => ?_⟩
  have hdim : (G'.stage Φ.actual).fiberDim ρ =
      finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) :=
    (G'.fiberDim_eq Φ.actual).trans (hpad_finrank_h1 (Φ.fibre Φ.actual) V)
  exact hpadFamily_not_finiteDimensional Φ V hV Φ.actual
    (hpad_switch_forces_finiteDim G' Reach.start (h1.trans_eq hdim.symm))

/-- **No free choice of fibre dimensions**: an old datum over the padded family has the fibre
dimensions of any homology-level datum over `Φ` (both are the `H¹` dimensions of the fibres).
Kind: PROVED. -/
theorem hpad_fiberDim_same (G : HomologySwitchDataPK Φ ι ρ u) (V : Type) [AddCommGroup V]
    [Module k V] {u' : F} (G' : GenuineSwitchDataPK (hpadFamily Φ V) ι ρ u') (c : Φ.Config) :
    (G'.stage c).fiberDim ρ = (G.stage c).fiberDim ρ :=
  ((G'.fiberDim_eq c).trans (hpad_finrank_h1 (Φ.fibre c) V)).trans (hpad_fiberDim_eq_h1 G c).symm

/-- **The old data die** (tex 4976–5195, the case `s(𝔭) > 1` of the switching argument): if a
homology-level datum over `Φ` has starting fibre dimension `> 1` and `V` is infinite-dimensional,
there is no old datum `GenuineSwitchDataPK` over the padded family, for any coordinate.
Kind: PROVED. -/
theorem hpad_isEmpty_genuinePK (G : HomologySwitchDataPK Φ ι ρ u)
    (h1 : 1 < (G.stage Φ.actual).fiberDim ρ) (V : Type) [AddCommGroup V] [Module k V]
    (hV : ¬ FiniteDimensional k V) (u' : F) :
    IsEmpty (GenuineSwitchDataPK (hpadFamily Φ V) ι ρ u') :=
  hpad_isEmpty_genuinePK_of_h1 u' V hV (h1.trans_eq (hpad_fiberDim_eq_h1 G Φ.actual))

/-- **Padding separates the two structures** (tex 4976–5195, 5055–5086): for a nonquadratic family
with a homology-level datum demanding a switch at the start and an infinite-dimensional `V`, over
the padded family the homology-level data exist, the old data do not, and every fibre has
infinite-dimensional global 1-cochains. Kind: PROVED. -/
theorem hpad_separates (G : HomologySwitchDataPK Φ ι ρ u) (hq : ¬ Φ.quadratic ρ)
    (h1 : 1 < (G.stage Φ.actual).fiberDim ρ) (V : Type) [AddCommGroup V] [Module k V]
    (hV : ¬ FiniteDimensional k V) :
    Nonempty (HomologySwitchDataPK (hpadFamily Φ V) ι ρ u) ∧
      IsEmpty (GenuineSwitchDataPK (hpadFamily Φ V) ι ρ u) ∧
      ∀ c, ¬ FiniteDimensional k (((hpadFamily Φ V).fibre c).G.X 1) :=
  ⟨⟨G.hpad hq V⟩, hpad_isEmpty_genuinePK G h1 V hV u, hpadFamily_not_finiteDimensional Φ V hV⟩

end Death

/-! **Non-vacuity** -/

section NonVacuity

/-- **An infinite-dimensional module**: `ℕ →₀ k` is not finite-dimensional (it has a basis indexed
by `ℕ`). Kind: PROVED. -/
theorem hpadInf (k : Type) [Field k] : ¬ FiniteDimensional k (ℕ →₀ k) := by
  intro h
  have := Module.Finite.finite_basis (Finsupp.basisSingleOne : Basis ℕ k (ℕ →₀ k))
  exact not_finite ℕ

/-- **`hpad_separates` with the concrete `V = ℕ →₀ k`.** Kind: PROVED. -/
theorem hpad_separates_finsupp {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]
    {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}
    (G : HomologySwitchDataPK Φ ι ρ u) (hq : ¬ Φ.quadratic ρ)
    (h1 : 1 < (G.stage Φ.actual).fiberDim ρ) :
    Nonempty (HomologySwitchDataPK (hpadFamily Φ (ℕ →₀ k)) ι ρ u) ∧
      IsEmpty (GenuineSwitchDataPK (hpadFamily Φ (ℕ →₀ k)) ι ρ u) ∧
      ∀ c, ¬ FiniteDimensional k (((hpadFamily Φ (ℕ →₀ k)).fibre c).G.X 1) :=
  hpad_separates G hq h1 (ℕ →₀ k) (hpadInf k)

/-- Batch 3's one-configuration example family (`t = 1`) is nonquadratic. Kind: PROVED. -/
theorem hpadEx_nonquad : ¬ exGenuineFamily.quadratic (RingHom.id ℚ) := by
  intro h
  have h' : (1 : ℚ) * (1 + 2) = 0 := h
  norm_num at h'

/-- **The padding applied to an actual datum**: batch 3's example `exGenuineSwitchData` (through
`ofGenuineSwitchData` and `toHomology`), padded by `ℕ →₀ ℚ`: a homology-level datum over a family
whose fibres have infinite-dimensional global 1-cochains (`hpadExData_inf`). Kind: PROVED. -/
def hpadExData :
    HomologySwitchDataPK (hpadFamily exGenuineFamily (ℕ →₀ ℚ)) (RingHom.id ℚ) (RingHom.id ℚ) 1 :=
  (GenuineSwitchDataPK.ofGenuineSwitchData exGenuineSwitchData).toHomology.hpad hpadEx_nonquad
    (ℕ →₀ ℚ)

/-- The fibres of the padded example family have infinite-dimensional global 1-cochains.
Kind: PROVED. -/
theorem hpadExData_inf (c : exGenuineFamily.Config) :
    ¬ FiniteDimensional ℚ (((hpadFamily exGenuineFamily (ℕ →₀ ℚ)).fibre c).G.X 1) :=
  hpadFamily_not_finiteDimensional _ _ (hpadInf ℚ) c

end NonVacuity

end ZInQ.Manuscript.RC.Wiring

import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuityQuad
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.TameComplex
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Proposition
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.NonVacuity

/-!
# RC53 SwitchInputs: one strict condition for both sides; the fiber dimension of a stage

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, tex L4976–4996 and L5055–5086:

> At the new prime let `C_str` and `C_rel` have the actual truncated conditions `D⁰` and
> `D⁰ ⊕ (F ⊕ S)[−1]`. [...] The cone triangles, with `D⁰` retained, give exact sequences
> `0 → K₀ → V → U ∩ F → 0`, `0 → K₀ → V' → U ∩ S → 0`. (5.5a)

Both sequences of (5.5a) start with the same `K₀ = H¹(C_str ⊗ k)`: the strict condition `D⁰` is
retained on both sides. In `Plug.lean` the finite and singular switch sides are separate
`SwitchSide` data, each with its own strict condition, so the shared `K₀` entered as the hypotheses
`hk0` (equal dimensions, `SelmerNonquadStep`) and `eK` (an identification of the two strict
`H¹`, `SelmerQuadSwitch`). Here they are derived.

Nodes (PROVED):
* `StrictIdentification`: the two strict conditions are identified by inverse chain maps `e`, `e'`
  commuting with the maps to the local complex (`U_str → U₁ → U_rel → L` on both sides). When both
  sides are built on the same strict condition (the text's `D⁰`), `e = e' = idGHom` and the only
  condition is the equality of the two composites to `L` (`exStrictIdentification`).
* `StrictIdentification.eK`: the induced linear equivalence of the strict cohomology groups
  `H¹(C(U_str))` (SS) `≃ H¹(C(U_str))` (SF), from the support comparison of `SelmerDuality` with
  identity global and local complexes; `StrictIdentification.hk0`: equal dimensions.
* `SelmerNonquadStep.ofStrict`, `nonquadDims_of_strict`: the nonquadratic switch step with `hk0`
  discharged.
* `twoTermFiberComplex`, `finrank_h1_twoTermFiberComplex`: the fiber `[k^{n+1} --D̄--> k^{n+1}]`
  of a stage's two-term model in degrees one and two has `dim H¹ = dim ker D̄ = fiberDim`.
* `FiberDimEqH1` / `fiberDim_eq_h1`: if the Selmer complex of a side is homotopy equivalent to the
  fiber of the stage's two-term model (the stage is a finite free model of that Selmer complex),
  then `fiberDim = dim H¹(C(U_F))`, the exact shape of the step fields of `SelmerSwitchData`.
* Non-vacuity (LESSON 2): `exStrictIdentification` for the sides of `NonVacuity.lean`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform
  ZInQ.Manuscript.RC.Uniform.QuadraticCase ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k]

/-! ### The identity chain map in the Mathlib category -/

theorem toCC_idGHom (A : GCx k) : GHom.toCC (idGHom A) = 𝟙 A.toCC := by
  ext i x
  rfl

/-! ### One strict condition for both sides -/

section Strict

variable {R : RelaxedLocalization k} {P Q : Submodule k ((Fin 2 → k) × (Fin 2 → k))}

/-- **The two sides share the strict condition** (tex L5072–5083, "with `D⁰` retained"): inverse
chain maps between the strict conditions of the two sides, commuting with the maps to the local
complex `L`. -/
structure StrictIdentification (SF : SwitchSide R P) (SS : SwitchSide R Q) where
  e : GHom SS.Ustr SF.Ustr
  e' : GHom SF.Ustr SS.Ustr
  he'e : ∀ n x, e'.f n n rfl (e.f n n rfl x) = x
  hee' : ∀ n x, e.f n n rfl (e'.f n n rfl x) = x
  hι : ∀ n x, SF.Dstr.ι.f n n rfl (e.f n n rfl x) = SS.Dstr.ι.f n n rfl x

variable {SF : SwitchSide R P} {SS : SwitchSide R Q}

theorem StrictIdentification.hι' (I : StrictIdentification SF SS) (n : ℤ) (x : SF.Ustr.X n) :
    SS.Dstr.ι.f n n rfl (I.e'.f n n rfl x) = SF.Dstr.ι.f n n rfl x := by
  rw [← I.hι n, I.hee']

/-- The comparison of strict Selmer complexes induced by `e` (identity on the global and local
complexes): a support-change datum of `SelmerDuality` with no new place. -/
def StrictIdentification.data (I : StrictIdentification SF SS) : SupportChangeData k where
  D := SS.Dstr
  Dp := SF.Dstr
  g := idGHom _
  lam := idGHom _
  mu := I.e
  r := zeroGHom _ _
  hres i j h a := by
    subst h
    change SF.Dstr.res.f i i rfl a = SF.Dstr.res.f i i rfl a + SF.Dstr.ι.f i i rfl 0
    rw [map_zero, add_zero]
  hι i j h u := by
    subst h
    exact I.hι i u

/-- The comparison in the other direction, induced by `e'`. -/
def StrictIdentification.data' (I : StrictIdentification SF SS) : SupportChangeData k where
  D := SF.Dstr
  Dp := SS.Dstr
  g := idGHom _
  lam := idGHom _
  mu := I.e'
  r := zeroGHom _ _
  hres i j h a := by
    subst h
    change SS.Dstr.res.f i i rfl a = SS.Dstr.res.f i i rfl a + SS.Dstr.ι.f i i rfl 0
    rw [map_zero, add_zero]
  hι i j h u := by
    subst h
    exact I.hι' i u

/-- The comparison `C(U_str)` (SS) `→ C(U_str)` (SF). -/
def StrictIdentification.φ (I : StrictIdentification SF SS) :
    GHom (selCx SS.Dstr) (selCx SF.Dstr) :=
  supportMap I.data

/-- The comparison `C(U_str)` (SF) `→ C(U_str)` (SS). -/
def StrictIdentification.ψ (I : StrictIdentification SF SS) :
    GHom (selCx SF.Dstr) (selCx SS.Dstr) :=
  supportMap I.data'

theorem StrictIdentification.comp_eq (I : StrictIdentification SF SS) :
    GHom.toCC I.φ ≫ GHom.toCC I.ψ = 𝟙 _ := by
  rw [GHom.toCC_comp, ← toCC_idGHom]
  apply GHom.toCC_ext
  intro n c
  obtain ⟨a, u, x⟩ := c
  change ((a, I.e'.f n n rfl (I.e.f n n rfl u + (0 : SF.Ustr.X n)) + (0 : SS.Ustr.X n), x) :
    SS.Dstr.G.X n × SS.Ustr.X n × SS.Dstr.L.X (n - 1)) = (a, u, x)
  rw [add_zero, add_zero]
  exact Prod.ext rfl (Prod.ext (I.he'e n u) rfl)

theorem StrictIdentification.comp_eq' (I : StrictIdentification SF SS) :
    GHom.toCC I.ψ ≫ GHom.toCC I.φ = 𝟙 _ := by
  rw [GHom.toCC_comp, ← toCC_idGHom]
  apply GHom.toCC_ext
  intro n c
  obtain ⟨a, u, x⟩ := c
  change ((a, I.e.f n n rfl (I.e'.f n n rfl u + (0 : SS.Ustr.X n)) + (0 : SF.Ustr.X n), x) :
    SF.Dstr.G.X n × SF.Ustr.X n × SF.Dstr.L.X (n - 1)) = (a, u, x)
  rw [add_zero, add_zero]
  exact Prod.ext rfl (Prod.ext (I.hee' n u) rfl)

/-- **The identification `eK` of the two strict cohomology groups** (tex L5072–5083). PROVED. -/
def StrictIdentification.eK (I : StrictIdentification SF SS) :
    (selCx SS.Dstr).toCC.homology 1 ≃ₗ[k] (selCx SF.Dstr).toCC.homology 1 :=
  LinearEquiv.ofLinearMap (H1 I.φ) (H1 I.ψ)
    (by
      change (HomologicalComplex.homologyMap (GHom.toCC I.ψ) 1 ≫
        HomologicalComplex.homologyMap (GHom.toCC I.φ) 1).hom = _
      rw [← HomologicalComplex.homologyMap_comp, I.comp_eq', HomologicalComplex.homologyMap_id]
      rfl)
    (by
      change (HomologicalComplex.homologyMap (GHom.toCC I.φ) 1 ≫
        HomologicalComplex.homologyMap (GHom.toCC I.ψ) 1).hom = _
      rw [← HomologicalComplex.homologyMap_comp, I.comp_eq, HomologicalComplex.homologyMap_id]
      rfl)

/-- **One `k₀` for both sides** (tex L5080–5083). PROVED. -/
theorem StrictIdentification.hk0 (I : StrictIdentification SF SS) :
    finrank k ((selCx SF.Dstr).toCC.homology 1) = finrank k ((selCx SS.Dstr).toCC.homology 1) :=
  I.eK.finrank_eq.symm

end Strict

/-! ### The nonquadratic step with `hk0` derived -/

/-- **`SelmerNonquadStep` with a shared strict condition** (tex L4997–5003, L5055–5086): the step
of `Plug.lean` with `hk0` derived from the strict identification. PROVED. -/
def SelmerNonquadStep.ofStrict (R : RelaxedLocalization k)
    (SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    (fG : FiniteDimensional k (R.D.G.X 1)) (fL : FiniteDimensional k (R.D.L.X 0))
    (fF : FiniteDimensional k (SF.U₁.X 1)) (fS : FiniteDimensional k (SS.U₁.X 1))
    (I : StrictIdentification SF SS) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0)
    (hσ : σ ≠ 0) (hJ2 : J * J = 1) (hdual : LocalizationDualityInput ε σ J hε hσ hJ2 R.U)
    (hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ R.U) : SelmerNonquadStep k where
  R := R
  SF := SF
  SS := SS
  fG := fG
  fL := fL
  fF := fF
  fS := fS
  hk0 := I.hk0
  ε := ε
  σ := σ
  J := J
  hε := hε
  hσ := hσ
  hJ2 := hJ2
  hdual := hdual
  hdet := hdet

/-- **The nonquadratic switch dimensions from a shared strict condition**: `NonquadDims` of
UniformSwitch with `hk0` derived. PROVED. -/
def nonquadDims_of_strict (R : RelaxedLocalization k)
    (SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    [FiniteDimensional k (R.D.G.X 1)] [FiniteDimensional k (R.D.L.X 0)]
    [FiniteDimensional k (SF.U₁.X 1)] [FiniteDimensional k (SS.U₁.X 1)]
    (I : StrictIdentification SF SS) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0)
    (hσ : σ ≠ 0) (hJ2 : J * J = 1) (hdual : LocalizationDualityInput ε σ J hε hσ hJ2 R.U)
    (hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ R.U) :
    NonquadDims (k := k) (finrank k ((selCx SF.Dside).toCC.homology 1))
      (finrank k ((selCx SS.Dside).toCC.homology 1)) :=
  nonquadDims_of_selmerData R SF SS I.hk0 ε σ J hε hσ hJ2 hdual hdet

/-! ### The fiber dimension of a stage is the `H¹` dimension of its Selmer complex -/

section Fiber

variable {A F : Type*} [CommRing A] [Field F]

/-- **The fiber of a stage's two-term model** (tex L4976–4992): `[k^{n+1} --D̄--> k^{n+1}]` in degrees
one and two (degree zero is `0`), `D̄ = D ⊗_ρ k`. -/
def twoTermFiberComplex {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι) :
    CochainComplex (ModuleCat.{0} k) ℤ :=
  threeTermComplex (0 : PUnit.{1} →ₗ[k] (Fin (S.n + 1) → k)) (S.D.map ρ).mulVecLin
    (LinearMap.comp_zero _)

/-- **`dim_k H¹` of the fiber is the fiber dimension** (tex L4976–4996: `s = dim_k H¹(C ⊗ k)` is
`dim_k ker D̄`). PROVED. -/
theorem finrank_h1_twoTermFiberComplex {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι) :
    finrank k ((twoTermFiberComplex ρ S).homology 1) = S.fiberDim ρ := by
  set K := twoTermFiberComplex ρ S
  have hd0 : K.d 0 1 = 0 := by
    change ModuleCat.ofHom (0 : PUnit.{1} →ₗ[k] (Fin (S.n + 1) → k)) = 0
    rfl
  have e1 := (K.isoHomologyπ 0 1 (by simp) hd0).symm
  have e2 := K.cyclesIsoSc' 0 1 2 (by simp) (by simp)
  have e3 := (K.sc' 0 1 2).moduleCatCyclesIso
  have := ((e1 ≪≫ e2 ≪≫ e3).toLinearEquiv).finrank_eq
  rw [this]
  rfl

/-- **The fiber dimension of a stage equals the `H¹` dimension of its Selmer complex** (tex
L4976–4996, L5055–5086): if the Selmer complex `C(D)` over `k` (the fiber of the Selmer complex of
the configuration, as in `SelmerSES`) is homotopy equivalent to the fiber of the stage's two-term
model (the stage is a finite free model of that Selmer complex), then
`fiberDim = dim_k H¹(C(D))`. Classification: PROVED. -/
def FiberDimEqH1 : Prop :=
  ∀ (k : Type) [Field k] (A F : Type) [CommRing A] [Field F] (ι : A →+* F) (ρ : A →+* k)
    (S : TwoTermStage ι) (D : SelData k),
    Nonempty (HomotopyEquiv (selCx D).toCC (twoTermFiberComplex ρ S)) →
      S.fiberDim ρ = finrank k ((selCx D).toCC.homology 1)

theorem fiberDim_eq_h1 : FiberDimEqH1 := by
  intro k _ A F _ _ ι ρ S D ⟨e⟩
  rw [← finrank_h1_twoTermFiberComplex ρ S]
  exact ((e.toHomologyIso 1).toLinearEquiv.finrank_eq).symm

/-- **The nonquadratic step fields of `SelmerSwitchData` from finite free models** (tex L4976–4996,
L4997–5003): for a Selmer step `X` and stages `S`, `S'` whose two-term fibers are homotopy
equivalent to the Selmer complexes of the finite and singular sides, the two identifications
required by the `switch_mixed` field of `SelmerSwitchData` hold. PROVED. -/
theorem nonquadStepFields_of_models {A F : Type} [CommRing A] [Field F] {ι : A →+* F}
    {ρ : A →+* k} (X : SelmerNonquadStep k) (S S' : TwoTermStage ι)
    (eS : Nonempty (HomotopyEquiv (selCx X.SF.Dside).toCC (twoTermFiberComplex ρ S)))
    (eS' : Nonempty (HomotopyEquiv (selCx X.SS.Dside).toCC (twoTermFiberComplex ρ S'))) :
    S.fiberDim ρ = finrank k ((selCx X.SF.Dside).toCC.homology 1) ∧
      S'.fiberDim ρ = finrank k ((selCx X.SS.Dside).toCC.homology 1) :=
  ⟨fiberDim_eq_h1 k A F ι ρ S _ eS, fiberDim_eq_h1 k A F ι ρ S' _ eS'⟩

theorem signPart_one_eq_plusPart {V : Type} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V) :
    signPart T (1 : k) = plusPart T := by
  ext v; rw [mem_signPart, mem_plusPart, one_smul]

theorem signPart_neg_one_eq_minusPart {V : Type} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V) :
    signPart T (-1 : k) = minusPart T := by
  ext v; rw [mem_signPart, mem_minusPart, neg_one_smul]

/-- **The single-sign step field of `SelmerSwitchData` from a finite free model** (tex
L5123–5136): for a single-sign Selmer step `Y` (whose `−` part vanishes, `Y.hs0`) and a stage `S`
whose two-term fiber is homotopy equivalent to the Selmer complex of the finite side,
`fiberDim S = dim V₊`, the identification required by the `switch_single` field. PROVED. -/
theorem singleStepField_of_model {A F : Type} [CommRing A] [Field F] {ι : A →+* F}
    {ρ : A →+* k} (Y : SelmerQuadSingleStep k) (S : TwoTermStage ι)
    (eS : Nonempty (HomotopyEquiv (selCx Y.X.SF.Dside).toCC (twoTermFiberComplex ρ S))) :
    S.fiberDim ρ = finrank k ↥(signPart Y.X.σV (1 : k)) := by
  have hV := Y.X.fin_V
  rw [fiberDim_eq_h1 k A F ι ρ S _ eS,
    (involutionSplitting_proof k _ Y.X.σV Y.h2 Y.X.hV).2.2 hV, signPart_one_eq_plusPart,
    ← signPart_neg_one_eq_minusPart, ← Y.hs0, add_zero]

end Fiber

/-! ### Non-vacuity (LESSON 2) -/

section NonVacuity

/-- **A strict identification of the two sides of `NonVacuity.lean`** (`exSideF`, `exSideS`): both
are built on the same strict condition, so `e = e' = id`; the two composites to `L` agree. -/
def exStrictIdentification : StrictIdentification exSideF exSideS where
  e := idGHom (zGCx Zn)
  e' := idGHom (zGCx Zn)
  he'e _ _ := rfl
  hee' _ _ := rfl
  hι n x := by
    have hx : x = 0 := funext fun i => Fin.elim0 i
    subst hx
    exact ((exSideF.Dstr.ι.f n n rfl).map_zero).trans ((exSideS.Dstr.ι.f n n rfl).map_zero).symm

/-- The strict identification discharges `hk0` for the example: both strict dimensions are `1`. -/
theorem exStrictIdentification_hk0 :
    finrank ℚ ((selCx exSideF.Dstr).toCC.homology 1) =
      finrank ℚ ((selCx exSideS.Dstr).toCC.homology 1) :=
  exStrictIdentification.hk0

/-- The nonquadratic Selmer step of `NonVacuity.lean` rebuilt with `hk0` derived from the strict
identification (`SelmerNonquadStep.ofStrict`). -/
def exSelmerNonquadStepOfStrict : SelmerNonquadStep ℚ :=
  SelmerNonquadStep.ofStrict exRel exSideF exSideS exSelmerNonquadStep.fG exSelmerNonquadStep.fL
    exSelmerNonquadStep.fF exSelmerNonquadStep.fS exStrictIdentification 1 1 J₀ one_ne_zero
    one_ne_zero J₀_sq exSelmerNonquadStep.hdual exSelmerNonquadStep.hdet

/-- A stage with the unit two-term model `[ℚ --1--> ℚ]`, zero cycle and functional, coordinate `0`. -/
def exUnitStage : TwoTermStage (RingHom.id ℚ) where
  n := 0
  D := 1
  z := 0
  w := 0
  u := 0
  hz := by simp
  hw := by simp
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    ext i j
    simp [Matrix.vecMulVec_apply]

theorem exUnitStage_contractible :
    Nonempty (Homotopy (𝟙 (twoTermFiberComplex (RingHom.id ℚ) exUnitStage)) 0) := by
  have hD : (exUnitStage.D.map (RingHom.id ℚ)).mulVecLin = LinearMap.id := by
    rw [show exUnitStage.D.map (RingHom.id ℚ) = 1 from by ext i j; exact rfl]
    exact Matrix.mulVecLin_one
  apply contractible_of_isContraction _ _ _ 0 LinearMap.id
  refine ⟨?_, ?_, ?_⟩
  · ext x
  · rw [LinearMap.zero_comp, zero_add, LinearMap.id_comp]
    exact hD
  · rw [LinearMap.comp_id]
    exact hD

theorem zeroSel_contractible :
    Nonempty (Homotopy (𝟙 (selCx (zeroSel ℚ)).toCC) 0) :=
  ⟨Homotopy.ofEq (by
    ext n x
    exact Subsingleton.elim (α := (zeroCx ℚ).X n × (zeroCx ℚ).X n × (zeroCx ℚ).X (n - 1)) _ _)⟩

/-- **The hypothesis of `fiberDim_eq_h1` is satisfiable**: the zero Selmer data and the unit stage
(both contractible) are homotopy equivalent, and `fiberDim = dim H¹ = 0`. -/
theorem exFiberDimEqH1 :
    exUnitStage.fiberDim (RingHom.id ℚ) = finrank ℚ ((selCx (zeroSel ℚ)).toCC.homology 1) := by
  obtain ⟨h1⟩ := zeroSel_contractible
  obtain ⟨h2⟩ := exUnitStage_contractible
  exact fiberDim_eq_h1 ℚ ℚ ℚ (RingHom.id ℚ) (RingHom.id ℚ) exUnitStage (zeroSel ℚ)
    ⟨homotopyEquivOfContractible h1 h2⟩

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

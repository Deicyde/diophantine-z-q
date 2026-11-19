import ZInQKernel.Contrib.OneProof.RC.Wiring.StageSupportConvention

/-!
Theorem 5.3, Lane RC0 round 16: the coefficient comparison for the stage support convention

RC0's actual stage datum `actualSelData` hard-codes the coefficient module
`MinS hS W i α = InflMod hS (Mcoef K S₀ W i α)`. When the coefficient support equals the Selmer
support (`hS = subset_refl S`) this is the module `Mcoef K S W i α` with the `G_{K,S}`-action
`g • m = inflMap g • m`, which agrees with the action on `Mcoef` only propositionally
(`minS_refl_smul`). Tex 5056–5062: the stage complex carries no condition at the new place `q`.
This file compares the two coefficient conventions and assembles RC0's literal stage datum with
the RC53 group's stage complex `F.globalCx i`.

* `resCochains_comm_id`: restriction along an abstract `φ : H →ₜ* G` commutes with a change of
  coefficients along the identities of the groups. `res_locMinSToMcoef`: its instance for the
  comparisons `minSToMcoef`, `locMinSToMcoef v` and the localization map `locMap K S v`. Proving
  the abstract statement first keeps the kernel from unfolding the localization map.
* `coefSelHom`: for genuine Selmer data over the same groups and places, a global cochain map,
  local cochain maps commuting with restriction, and maps of conditions compatible with the
  condition maps give a chain map of Selmer complexes. `coefSelHom_isIso`: with inverse cochain
  maps and bijective condition maps it is an isomorphism. `coefSelHom_projG`: on the global
  complexes it is the global cochain map.
* `oldCoefHom`, `oldCoefHom_isIso`, `oldCoefHom_projG`: the old-places datum over `MinS` with the
  transported conditions `condToMinS ∘ c` is isomorphic to the old-places datum over `Mcoef` with
  the conditions `c`.
* `actualSelData_oldEquiv`: RC0's literal `actualSelData` at `insert q S₀` with the transported
  old conditions extended by `fullAt` at `q` is homotopy equivalent to the old-places complex over
  `Mcoef`. `actualSelData_insertEquiv_hom_projG`, `actualSelData_oldEquiv_hom_projG`: the
  compatibility with the global complexes.
* `actualStageFamily_actualEquiv`: for the RC53 group's actual stage family `F`, RC0's literal
  actual datum with the old conditions `condToMinS ∘ F.old i` and `fullAt` at `q i` is homotopy
  equivalent to `F.globalCx i`. `actualStageFamily_actualEquiv_hom_projG`: on the global
  complexes the equivalence is the coefficient comparison `minSToMcoef` (the identity on
  cochains).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring.StageSupport

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex

/-! **Restriction against a change of coefficients, abstractly** -/

section ResComm

variable {k : Type} [CommRing k] {G H : Type} [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] [ContinuousMul G] [ContinuousMul H]
  {M₁ : Type} [AddCommGroup M₁] [Module k M₁] [DistribMulAction G M₁] [SMulCommClass G k M₁]
  [TopologicalSpace M₁] [ContinuousAdd M₁] [ContinuousConstSMul k M₁] [ContinuousSMul G M₁]
  {M₂ : Type} [AddCommGroup M₂] [Module k M₂] [DistribMulAction G M₂] [SMulCommClass G k M₂]
  [TopologicalSpace M₂] [ContinuousAdd M₂] [ContinuousConstSMul k M₂] [ContinuousSMul G M₂]
  (φ : H →ₜ* G)

/-- **Restriction commutes with a change of coefficients along the identity of the groups**:
for `f : M₁ → M₂` and its copy `f'` on the restricted modules, `res_φ ∘ f = f' ∘ res_φ` on
continuous cochains. The homomorphism `φ` is abstract here. Kind: PROVED. -/
theorem resCochains_comm_id (f : M₁ →ₗ[k] M₂) (hfc : Continuous f)
    (hf : ∀ (g : G) (m : M₁), f (ContinuousMonoidHom.id G g • m) = g • f m)
    (f' : ResMod φ M₁ →ₗ[k] ResMod φ M₂) (hfc' : Continuous f')
    (hf' : ∀ (h : H) (m : ResMod φ M₁), f' (ContinuousMonoidHom.id H h • m) = h • f' m)
    (hff : ∀ m : M₁, f' m = f m) :
    resCochains (k := k) (M := M₁) φ ≫ contCochainsMap (ContinuousMonoidHom.id H) f' hfc' hf' =
      contCochainsMap (ContinuousMonoidHom.id G) f hfc hf ≫
        resCochains (k := k) (M := M₂) φ := by
  ext n c
  apply Subtype.ext
  funext x
  exact hff _

end ResComm

section PiBij

variable {k : Type} [CommRing k] {ι : Type} {A B : ι → GCx k}

/-- A product of bijective maps is bijective. Kind: PROVED. -/
theorem piMap_bijective (f : ∀ v, GHom (A v) (B v)) (n : ℤ)
    (hf : ∀ v, Function.Bijective ((f v).f n n rfl)) :
    Function.Bijective ((piMap f).f n n rfl) := by
  refine ⟨fun x y h => funext fun v => (hf v).1 (congrFun h v), fun y => ?_⟩
  choose x hx using fun v => (hf v).2 (y v)
  exact ⟨x, funext hx⟩

end PiBij

/-! **A change of coefficients of genuine Selmer data** -/

section GenericCoef

variable {k : Type} [CommRing k] {GS : Type} [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {ι : Type} {Gv : ι → Type} [∀ v, Group (Gv v)]
  [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M₁ : Type} [AddCommGroup M₁] [Module k M₁] [DistribMulAction GS M₁] [SMulCommClass GS k M₁]
  [TopologicalSpace M₁] [ContinuousAdd M₁] [ContinuousConstSMul k M₁] [ContinuousSMul GS M₁]
  {M₂ : Type} [AddCommGroup M₂] [Module k M₂] [DistribMulAction GS M₂] [SMulCommClass GS k M₂]
  [TopologicalSpace M₂] [ContinuousAdd M₂] [ContinuousConstSMul k M₂] [ContinuousSMul GS M₂]
  (Δ₁ : LocalConditions k GS Gv loc M₁) (Δ₂ : LocalConditions k GS Gv loc M₂)
  (ψ : contCochains k GS M₁ ⟶ contCochains k GS M₂)
  (ψv : ∀ v, contCochains k (Gv v) (ResMod (loc v) M₁) ⟶
    contCochains k (Gv v) (ResMod (loc v) M₂))
  (φU : ∀ v, GHom (Δ₁.U v) (Δ₂.U v))

/-- The local component of a change of coefficients. -/
abbrev locCoefHom : GHom (selData k GS Gv loc M₁ Δ₁).L (selData k GS Gv loc M₂ Δ₂).L :=
  piMap fun v => natHom (ψv v)

/-- The input `hres` of `selHom` for a change of coefficients. Kind: PROVED. -/
theorem coef_hres
    (hcomm : ∀ v, resCochains (k := k) (M := M₁) (loc v) ≫ ψv v =
      ψ ≫ resCochains (k := k) (M := M₂) (loc v))
    (n : ℤ) (a : natX (contCochains k GS M₁) n) :
    (locCoefHom Δ₁ Δ₂ ψv).f n n rfl ((selData k GS Gv loc M₁ Δ₁).res.f n n rfl a) =
      (selData k GS Gv loc M₂ Δ₂).res.f n n rfl ((natHom ψ).f n n rfl a) := by
  funext v
  change natF (ψv v) n (natF (resCochains (k := k) (M := M₁) (loc v)) n a) =
    natF (resCochains (k := k) (M := M₂) (loc v)) n (natF ψ n a)
  rw [natF_natF, natF_natF, hcomm]

/-- The input `hι` of `selHom` for a change of coefficients. Kind: PROVED. -/
theorem coef_hι
    (hι : ∀ v n (u : (Δ₁.U v).X n), (natHom (ψv v)).f n n rfl ((Δ₁.i v).f n n rfl u) =
      (Δ₂.i v).f n n rfl ((φU v).f n n rfl u))
    (n : ℤ) (u : (selData k GS Gv loc M₁ Δ₁).U.X n) :
    (locCoefHom Δ₁ Δ₂ ψv).f n n rfl ((selData k GS Gv loc M₁ Δ₁).ι.f n n rfl u) =
      (selData k GS Gv loc M₂ Δ₂).ι.f n n rfl ((piMap φU).f n n rfl u) := by
  funext v
  exact hι v n (u v)

/-- **A change of coefficients of genuine Selmer data**: a global cochain map `ψ`, local cochain
maps `ψ_v` commuting with restriction and maps of conditions `φ_v` compatible with the condition
maps give the chain map `(a, u, x) ↦ (ψ a, φ u, ψ_v x)` of Selmer complexes. Kind: PROVED. -/
def coefSelHom
    (hcomm : ∀ v, resCochains (k := k) (M := M₁) (loc v) ≫ ψv v =
      ψ ≫ resCochains (k := k) (M := M₂) (loc v))
    (hι : ∀ v n (u : (Δ₁.U v).X n), (natHom (ψv v)).f n n rfl ((Δ₁.i v).f n n rfl u) =
      (Δ₂.i v).f n n rfl ((φU v).f n n rfl u)) :
    GHom (selCx (selData k GS Gv loc M₁ Δ₁)) (selCx (selData k GS Gv loc M₂ Δ₂)) :=
  selHom (natHom ψ) (piMap φU) (locCoefHom Δ₁ Δ₂ ψv) (coef_hres Δ₁ Δ₂ ψ ψv hcomm)
    (coef_hι Δ₁ Δ₂ ψv φU hι)

/-- **With inverse cochain maps and bijective condition maps the change of coefficients is an
isomorphism of Selmer complexes.** Kind: PROVED. -/
theorem coefSelHom_isIso
    (hcomm : ∀ v, resCochains (k := k) (M := M₁) (loc v) ≫ ψv v =
      ψ ≫ resCochains (k := k) (M := M₂) (loc v))
    (hι : ∀ v n (u : (Δ₁.U v).X n), (natHom (ψv v)).f n n rfl ((Δ₁.i v).f n n rfl u) =
      (Δ₂.i v).f n n rfl ((φU v).f n n rfl u))
    (ψ' : contCochains k GS M₂ ⟶ contCochains k GS M₁) (h₁ : ψ ≫ ψ' = 𝟙 _) (h₂ : ψ' ≫ ψ = 𝟙 _)
    (ψv' : ∀ v, contCochains k (Gv v) (ResMod (loc v) M₂) ⟶
      contCochains k (Gv v) (ResMod (loc v) M₁))
    (hv₁ : ∀ v, ψv v ≫ ψv' v = 𝟙 _) (hv₂ : ∀ v, ψv' v ≫ ψv v = 𝟙 _)
    (hU : ∀ v n, Function.Bijective ((φU v).f n n rfl)) :
    IsIso (GHom.toCC (coefSelHom Δ₁ Δ₂ ψ ψv φU hcomm hι)) :=
  selHom_isIso _ _ _ _ _ (fun n => natF_bijective ψ ψ' h₁ h₂ n)
    (fun n => piMap_bijective φU n fun v => hU v n)
    (fun n => piMap_bijective _ n fun v => natF_bijective (ψv v) (ψv' v) (hv₁ v) (hv₂ v) n)

/-- **On the global complexes the change of coefficients is the global cochain map.** Kind:
PROVED. -/
theorem coefSelHom_projG
    (hcomm : ∀ v, resCochains (k := k) (M := M₁) (loc v) ≫ ψv v =
      ψ ≫ resCochains (k := k) (M := M₂) (loc v))
    (hι : ∀ v n (u : (Δ₁.U v).X n), (natHom (ψv v)).f n n rfl ((Δ₁.i v).f n n rfl u) =
      (Δ₂.i v).f n n rfl ((φU v).f n n rfl u)) :
    GHom.toCC (coefSelHom Δ₁ Δ₂ ψ ψv φU hcomm hι) ≫
        GHom.toCC (projG (selData k GS Gv loc M₂ Δ₂)) =
      GHom.toCC (projG (selData k GS Gv loc M₁ Δ₁)) ≫ GHom.toCC (natHom ψ) := by
  ext n x
  rfl

end GenericCoef

/-! **Transport along an equality of Selmer data** -/

section Cast

variable {k : Type} [CommRing k]

/-- A homotopy equivalence transported along an equality of Selmer data. Kind: PROVED. -/
theorem mpr_hom_eq {D₁ D₂ : SelData k} (h : D₁ = D₂) {Z : CochainComplex (ModuleCat k) ℤ}
    (p : HomotopyEquiv (selCx D₁).toCC Z = HomotopyEquiv (selCx D₂).toCC Z)
    (e : HomotopyEquiv (selCx D₂).toCC Z) :
    (Eq.mpr p e).hom = eqToHom (congrArg (fun D => (selCx D).toCC) h) ≫ e.hom := by
  subst h
  simp

/-- An equality of Selmer data commutes with the projections to the global complexes. Kind:
PROVED. -/
theorem eqToHom_selCx_projG {D₁ D₂ : SelData k} (h : D₁ = D₂) :
    eqToHom (congrArg (fun D => (selCx D).toCC) h) ≫ GHom.toCC (projG D₂) =
      GHom.toCC (projG D₁) ≫ eqToHom (congrArg (fun D => D.G.toCC) h) := by
  subst h
  simp

end Cast

/-! **The comparisons `minSToMcoef`, `locMinSToMcoef` commute with restriction** -/

section CoefRes

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (Mcoef IsOpenKer MinS)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]

/-- **Restriction to `v` commutes with the coefficient comparison** `MinS (subset_refl S)` to
`Mcoef`: `res_v ≫ locMinSToMcoef v = minSToMcoef ≫ res_v`. Kind: PROVED. -/
theorem res_locMinSToMcoef (v : HeightOneSpectrum (𝓞 K)) :
    resCochains (k := Acoef i) (M := MinS (subset_refl S) W i α) (locMap K S v) ≫
        locMinSToMcoef W i α v =
      minSToMcoef W i α ≫ resCochains (k := Acoef i) (M := Mcoef K S W i α) (locMap K S v) := by
  unfold locMinSToMcoef minSToMcoef
  exact resCochains_comm_id _ _ _ _ _ _ _ (fun _ => rfl)

end CoefRes

/-! **The old-places data over `MinS` and over `Mcoef`** -/

section CoefInsert

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (CondAt Mcoef IsOpenKer MinS actualSelData)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] (S₀ : Set (HeightOneSpectrum (𝓞 K)))
  (q : HeightOneSpectrum (𝓞 K)) (W : WeierstrassCurve K) (i : ℕ)
  (α : GKS K (insert q S₀) →* (Acoef i)ˣ) [IsOpenKer α]
  (c : ∀ v : Places K S₀, CondAt K (insert q S₀) (Acoef i) (Mcoef K (insert q S₀) W i α)
    (oldPlace S₀ q v))

/-- The transported conditions are compatible with the comparison. Kind: PROVED. -/
theorem oldCoef_hι (v : Places K S₀) (n : ℤ) (u : ((c v).U).X n) :
    (natHom (locMinSToMcoef W i α v.1)).f n n rfl ((condToMinS W i α (c v)).i.f n n rfl u) =
      (c v).i.f n n rfl ((idGHom (c v).U).f n n rfl u) :=
  natHom_loc_inv W i α v.1 n _

/-- **The comparison of the old-places data** over `MinS (subset_refl _)` with the transported
conditions and over `Mcoef` with the conditions `c`: the identity on cochains and on
conditions. Kind: PROVED. -/
def oldCoefHom :
    GHom (selCx (oldData S₀ q (Acoef i) (MinS (subset_refl (insert q S₀)) W i α)
      (fun v => condToMinS W i α (c v))))
      (selCx (oldData S₀ q (Acoef i) (Mcoef K (insert q S₀) W i α) c)) :=
  coefSelHom _ _ (minSToMcoef W i α) (fun v => locMinSToMcoef W i α v.1)
    (fun v => idGHom (c v).U) (fun v => res_locMinSToMcoef W i α v.1) (oldCoef_hι S₀ q W i α c)

/-- **The comparison of the old-places data is an isomorphism.** Kind: PROVED. -/
theorem oldCoefHom_isIso : IsIso (GHom.toCC (oldCoefHom S₀ q W i α c)) :=
  coefSelHom_isIso _ _ _ _ _ _ _ (mcoefToMinS W i α) (minSToMcoef_comp W i α)
    (mcoefToMinS_comp W i α) (fun v => locMcoefToMinS W i α v.1)
    (fun v => locMinSToMcoef_comp W i α v.1) (fun v => locMcoefToMinS_comp W i α v.1)
    (fun _ _ => ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩)

/-- On the global complexes the comparison is `minSToMcoef`. Kind: PROVED. -/
theorem oldCoefHom_projG :
    GHom.toCC (oldCoefHom S₀ q W i α c) ≫
        GHom.toCC (projG (oldData S₀ q (Acoef i) (Mcoef K (insert q S₀) W i α) c)) =
      GHom.toCC (projG (oldData S₀ q (Acoef i) (MinS (subset_refl (insert q S₀)) W i α)
        (fun v => condToMinS W i α (c v)))) ≫ GHom.toCC (natHom (minSToMcoef W i α)) :=
  coefSelHom_projG _ _ _ _ _ _ _

/-- **`actualSelData_insertEquiv` is the identity on the global complex.** Kind: PROVED. -/
theorem actualSelData_insertEquiv_hom_projG [W.IsElliptic] (hq : q ∉ S₀)
    (c' : ∀ v : Places K S₀, CondAt K (insert q S₀) (Acoef i)
      (MinS (subset_refl (insert q S₀)) W i α) (oldPlace S₀ q v)) :
    (actualSelData_insertEquiv W i S₀ q hq α c').hom ≫
        GHom.toCC (projG (oldData S₀ q (Acoef i) (MinS (subset_refl (insert q S₀)) W i α) c')) =
      GHom.toCC (projG (actualSelData (subset_refl (insert q S₀)) W i α
        (extendFull S₀ q (insert q S₀) (Acoef i) (MinS (subset_refl (insert q S₀)) W i α)
          (ofOld S₀ q (Acoef i) _ c')))) := by
  have h3 : eqToHom (congrArg (fun D => D.G.toCC) (actualSelData_refl_eq W i α
      (extendFull S₀ q (insert q S₀) (Acoef i) (MinS (subset_refl (insert q S₀)) W i α)
        (ofOld S₀ q (Acoef i) _ c')))) = 𝟙 _ :=
    eqToHom_refl _ _
  unfold actualSelData_insertEquiv
  rw [mpr_hom_eq (actualSelData_refl_eq W i α _) _ (insertEquiv S₀ q (Acoef i) _ hq c'),
    Category.assoc]
  erw [insertEquiv_hom_projG]
  erw [eqToHom_selCx_projG (actualSelData_refl_eq W i α _)]
  rw [h3]
  exact Category.comp_id _

/-- **RC0's literal stage datum against the old-places complex over `Mcoef`**: RC0's
`actualSelData` with coefficient and Selmer support `insert q S₀`, the old conditions `c` (over
`Mcoef`) transported to `MinS` and extended by `fullAt` at `q`, is homotopy equivalent to the
old-places complex over `Mcoef`: `actualSelData_insertEquiv` followed by `oldCoefHom`. Kind:
PROVED. -/
def actualSelData_oldEquiv [W.IsElliptic] (hq : q ∉ S₀) :
    HomotopyEquiv (selCx (actualSelData (subset_refl (insert q S₀)) W i α
        (extendFull S₀ q (insert q S₀) (Acoef i) (MinS (subset_refl (insert q S₀)) W i α)
          (ofOld S₀ q (Acoef i) _ (fun v => condToMinS W i α (c v)))))).toCC
      (selCx (oldData S₀ q (Acoef i) (Mcoef K (insert q S₀) W i α) c)).toCC :=
  haveI := oldCoefHom_isIso S₀ q W i α c
  (actualSelData_insertEquiv W i S₀ q hq α (fun v => condToMinS W i α (c v))).trans
    (HomotopyEquiv.ofIso (asIso (GHom.toCC (oldCoefHom S₀ q W i α c))))

/-- **On the global complexes `actualSelData_oldEquiv` is the coefficient comparison
`minSToMcoef`** (the identity on cochains). Kind: PROVED. -/
theorem actualSelData_oldEquiv_hom_projG [W.IsElliptic] (hq : q ∉ S₀) :
    (actualSelData_oldEquiv S₀ q W i α c hq).hom ≫
        GHom.toCC (projG (oldData S₀ q (Acoef i) (Mcoef K (insert q S₀) W i α) c)) =
      GHom.toCC (projG (actualSelData (subset_refl (insert q S₀)) W i α
        (extendFull S₀ q (insert q S₀) (Acoef i) (MinS (subset_refl (insert q S₀)) W i α)
          (ofOld S₀ q (Acoef i) _ (fun v => condToMinS W i α (c v)))))) ≫
        GHom.toCC (natHom (minSToMcoef W i α)) := by
  have h1 := actualSelData_insertEquiv_hom_projG S₀ q W i α hq (fun v => condToMinS W i α (c v))
  change ((actualSelData_insertEquiv W i S₀ q hq α (fun v => condToMinS W i α (c v))).hom ≫
      GHom.toCC (oldCoefHom S₀ q W i α c)) ≫ _ = _
  rw [Category.assoc, oldCoefHom_projG]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1)

end CoefInsert

/-! **The RC53 group's actual stage family and RC0's literal actual datum** -/

section Family

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (IsOpenKer MinS actualSelData)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange (ActualStageFamily)

variable {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ}
  [∀ i, IsOpenKer (α i)]

/-- **RC0's literal actual datum for the RC53 group's family is homotopy equivalent to
`F.globalCx i`**: `actualSelData` with coefficient and Selmer support `insert (q i) S₀`, the
character `F.character i`, the old conditions `condToMinS ∘ F.old i` at `S₀` and `fullAt` at
`q i`. Kind: PROVED. -/
def actualStageFamily_actualEquiv (F : ActualStageFamily S₀ W α) (i : ℕ) :
    HomotopyEquiv (selCx (actualSelData (subset_refl (F.support i)) W i (F.character i)
        (extendFull S₀ (F.q i) (F.support i) (Acoef i)
          (MinS (subset_refl (F.support i)) W i (F.character i))
          (ofOld S₀ (F.q i) (Acoef i) _
            (fun v => condToMinS W i (F.character i) (F.old i v)))))).toCC
      (F.globalCx i).toCC :=
  actualSelData_oldEquiv S₀ (F.q i) W i (F.character i) (F.old i) (F.new i)

/-- **On the global complexes the equivalence is the coefficient comparison `minSToMcoef`**
(the identity on cochains). Kind: PROVED. -/
theorem actualStageFamily_actualEquiv_hom_projG (F : ActualStageFamily S₀ W α) (i : ℕ) :
    (actualStageFamily_actualEquiv F i).hom ≫ GHom.toCC (projG (F.datum i)) =
      GHom.toCC (projG (actualSelData (subset_refl (F.support i)) W i (F.character i)
        (extendFull S₀ (F.q i) (F.support i) (Acoef i)
          (MinS (subset_refl (F.support i)) W i (F.character i))
          (ofOld S₀ (F.q i) (Acoef i) _
            (fun v => condToMinS W i (F.character i) (F.old i v)))))) ≫
        GHom.toCC (natHom (minSToMcoef W i (F.character i))) :=
  actualSelData_oldEquiv_hom_projG S₀ (F.q i) W i (F.character i) (F.old i) (F.new i)

end Family

end ZInQ.Manuscript.RC.Wiring.StageSupport

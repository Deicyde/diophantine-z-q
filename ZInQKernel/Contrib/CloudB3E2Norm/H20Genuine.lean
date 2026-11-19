import ZInQKernel.Contrib.CloudB3E2Norm.H20Cochains
import ZInQKernel.Contrib.CloudB3E2Norm.LocalIdentity

/-!
# The coefficient push (H20) on the genuine Selmer data

Manuscript `diophantine_zq.tex`, tex 3203–3215, 3262–3270, 3281–3290. For a ring homomorphism
`φ : k₁ →+* k₂` (for the text, `h20RingHom θ : ℤ[Δ_f] → A_i`, `θ = χ_h Ψ_i`) and a `φ`-semilinear
`G_{K,S}`-equivariant coefficient map `f : M₁ → M₂` of discrete modules (for the text,
`v ⊗ [δ] ↦ θ(δ) v`):

* `CondPushAt` (definition): a push of one local condition compatible with the coefficient
  change of the local complex; `CondPushAt.cocycle` (PROVED) for cocycle conditions mapped into
  each other, `CondPushAt.kummer` (PROVED) for the extended Kummer conditions with
  `ι₂ = f ∘ ι₁` (the old Kummer conditions survive), `CondPushAt.full` (PROVED) for the full
  condition.
* `selDataPush` (definition): the semilinear push `SelPush φ (selData Δ₁) (selData Δ₂)` of the
  genuine Selmer data from per-place condition pushes.
* `SelPush.addPlace` (definition): the push of the data with one more place, from a push of the
  local complex at the place and of its condition; `relaxedPush` (definition): the push of the
  genuine relaxed data `stageRelaxed`.
* **`h20CoefficientPush_genuine`** (PROVED): `H20CoefficientPush` for the genuine relaxed data
  with the old Kummer conditions, the classes pushed by the coefficient change, and the
  primitive data at `w` given by a push of the condition at `w` compatible with `ι_q`
  (`WPush`; constructed for the genuine unramified condition in `H20Unramified.lean`,
  `wPushUr`).
* **`pushed_class_transfer`** (PROVED): the global component of the pushed class is the stage
  transferred Kummer class of the pushed point, `ι₂(f ∘ z) = 𝒯_{θ₂}(κ(c Q))`, when the source
  class is `𝒯_{θ₁}(κ(Q))` (the coefficient-push step, by the naturality `transfer_kummer_coeff`;
  the source identity is the hypothesis `hz`).
* Non-vacuity: `nonVacuity_condPush`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

/-! ### Adding a place -/

section AddPlace

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {φ : k₁ →+* k₂}

/-- The product of two semilinear maps on the terms of product complexes. Kind: definition. -/
def sprodCx {A B : GCx k₁} {A' B' : GCx k₂} (n : ℤ) (f : A.X n →ₛₗ[φ] A'.X n)
    (g : B.X n →ₛₗ[φ] B'.X n) : (prodCx A B).X n →ₛₗ[φ] (prodCx A' B').X n where
  toFun p := ((f (p : A.X n × B.X n).1, g (p : A.X n × B.X n).2) : A'.X n × B'.X n)
  map_add' _ _ := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' _ _ := Prod.ext (LinearMap.map_smulₛₗ _ _ _) (LinearMap.map_smulₛₗ _ _ _)

/-- **A push of a local complex at one place** (degrees `−1, 0, 1`) compatible with its
differential (degrees `0 → 1`). Kind: definition (data with identities). -/
structure LocPush (φ : k₁ →+* k₂) (L₁ : GCx k₁) (L₂ : GCx k₂) where
  /-- degree `−1` -/
  lm : L₁.X (0 - 1) →ₛₗ[φ] L₂.X (0 - 1)
  /-- degree `0` -/
  l0 : L₁.X 0 →ₛₗ[φ] L₂.X 0
  /-- degree `1` -/
  l1 : L₁.X 1 →ₛₗ[φ] L₂.X 1
  /-- compatibility with `d⁻¹` -/
  hdm : ∀ x, l0 (L₁.d (0 - 1) (1 - 1) (by omega) x) = L₂.d (0 - 1) (1 - 1) (by omega) (lm x)
  /-- compatibility with `d⁰` -/
  hd0 : ∀ x, l1 (L₁.d 0 1 rfl x) = L₂.d 0 1 rfl (l0 x)

/-- **The push of the data with one more place** (Kind: definition): from a push `P` of `D`, a
push `Q` of the local complex at the place compatible with the restrictions, and a push of the
condition `U_q` compatible with `ι_q` in degree `0`. -/
def SelPush.addPlace {D₁ : SelData k₁} {D₂ : SelData k₂} (P : SelPush φ D₁ D₂)
    {Lq₁ : GCx k₁} {Lq₂ : GCx k₂} (resq₁ : GHom D₁.G Lq₁) (resq₂ : GHom D₂.G Lq₂)
    (Q : LocPush φ Lq₁ Lq₂)
    (hresq : ∀ a, Q.l0 (resq₁.f 0 0 rfl a) = resq₂.f 0 0 rfl (P.g0 a))
    {Uq₁ : GCx k₁} {Uq₂ : GCx k₂} (ιq₁ : GHom Uq₁ Lq₁) (ιq₂ : GHom Uq₂ Lq₂)
    (uq0 : Uq₁.X 0 →ₛₗ[φ] Uq₂.X 0) (uq1 : Uq₁.X 1 →ₛₗ[φ] Uq₂.X 1)
    (huq : ∀ u, uq1 (Uq₁.d 0 1 rfl u) = Uq₂.d 0 1 rfl (uq0 u))
    (hιq : ∀ u, Q.l0 (ιq₁.f 0 0 rfl u) = ιq₂.f 0 0 rfl (uq0 u)) :
    SelPush φ (addPlace D₁ resq₁ ιq₁) (addPlace D₂ resq₂ ιq₂) where
  g0 := P.g0
  g1 := P.g1
  u0 := sprodCx 0 P.u0 uq0
  u1 := sprodCx 1 P.u1 uq1
  lm := sprodCx (0 - 1) P.lm Q.lm
  l0 := sprodCx (1 - 1) P.l0 Q.l0
  hg := P.hg
  hu u := Prod.ext (P.hu (u : D₁.U.X 0 × Uq₁.X 0).1) (huq (u : D₁.U.X 0 × Uq₁.X 0).2)
  hres a := Prod.ext (P.hres a) (hresq a)
  hι u := Prod.ext (P.hι (u : D₁.U.X 0 × Uq₁.X 0).1) (hιq (u : D₁.U.X 0 × Uq₁.X 0).2)
  hL x := Prod.ext (P.hL (x : D₁.L.X (0 - 1) × Lq₁.X (0 - 1)).1)
    (Q.hdm (x : D₁.L.X (0 - 1) × Lq₁.X (0 - 1)).2)

/-- **The push of the relaxed data** (full condition at the place). Kind: definition. -/
def SelPush.relaxed {D₁ : SelData k₁} {D₂ : SelData k₂} (P : SelPush φ D₁ D₂)
    {Lq₁ : GCx k₁} {Lq₂ : GCx k₂} (resq₁ : GHom D₁.G Lq₁) (resq₂ : GHom D₂.G Lq₂)
    (Q : LocPush φ Lq₁ Lq₂)
    (hresq : ∀ a, Q.l0 (resq₁.f 0 0 rfl a) = resq₂.f 0 0 rfl (P.g0 a)) :
    SelPush φ (relaxedAt D₁ resq₁) (relaxedAt D₂ resq₂) :=
  P.addPlace resq₁ resq₂ Q hresq (idGHom Lq₁) (idGHom Lq₂) Q.l0 Q.l1 Q.hd0 (fun _ => rfl)

/-- **The push of the condition at the new place for the primitive data** (data with
identities): semilinear maps on `U_q` compatible with its differential and with `ι_q` in degrees
`0`, `1`. Kind: definition. -/
structure WPush (φ : k₁ →+* k₂) {Lq₁ : GCx k₁} {Lq₂ : GCx k₂} (Q : LocPush φ Lq₁ Lq₂)
    {Uq₁ : GCx k₁} {Uq₂ : GCx k₂} (ιq₁ : GHom Uq₁ Lq₁) (ιq₂ : GHom Uq₂ Lq₂) where
  /-- degree `0` -/
  w0 : Uq₁.X 0 →ₛₗ[φ] Uq₂.X 0
  /-- degree `1` -/
  w1 : Uq₁.X 1 →ₛₗ[φ] Uq₂.X 1
  /-- compatibility with the differential -/
  hw : ∀ u, w1 (Uq₁.d 0 1 rfl u) = Uq₂.d 0 1 rfl (w0 u)
  /-- compatibility with `ι_q`, degree `0` -/
  hι0 : ∀ u, Q.l0 (ιq₁.f 0 0 rfl u) = ιq₂.f 0 0 rfl (w0 u)
  /-- compatibility with `ι_q`, degree `1` -/
  hι1 : ∀ u, Q.l1 (ιq₁.f 1 1 rfl u) = ιq₂.f 1 1 rfl (w1 u)

/-- **`H20CoefficientPush` for relaxed/primitive data at a new place** (PROVED): from a push of
the old data, of the local complex at the place, and of the condition at the place. -/
theorem h20CoefficientPush_relaxed {D₁ : SelData k₁} {D₂ : SelData k₂} (P : SelPush φ D₁ D₂)
    {Lq₁ : GCx k₁} {Lq₂ : GCx k₂} (resq₁ : GHom D₁.G Lq₁) (resq₂ : GHom D₂.G Lq₂)
    (Q : LocPush φ Lq₁ Lq₂)
    (hresq : ∀ a, Q.l0 (resq₁.f 0 0 rfl a) = resq₂.f 0 0 rfl (P.g0 a))
    {Uq₁ : GCx k₁} {Uq₂ : GCx k₂} (ιq₁ : GHom Uq₁ Lq₁) (ιq₂ : GHom Uq₂ Lq₂)
    (W : WPush φ Q ιq₁ ιq₂) (zR₁ : (selCx (relaxedAt D₁ resq₁)).X 1)
    (zP₁ : (selCx (selRestrict (relaxedAt D₁ resq₁) (primToRel D₁ resq₁ ιq₁))).X 1) (e₁ : k₁) :
    ∃ zP₂ : (selCx (selRestrict (relaxedAt D₂ resq₂) (primToRel D₂ resq₂ ιq₂))).X 1,
      H20CoefficientPush (relaxedAt D₁ resq₁) (primToRel D₁ resq₁ ιq₁) zR₁ zP₁ e₁
        (relaxedAt D₂ resq₂) (primToRel D₂ resq₂ ιq₂) ((P.relaxed resq₁ resq₂ Q hresq).push1 zR₁)
        zP₂ (φ e₁) :=
  ⟨_, h20CoefficientPush_of_selPush φ (P.relaxed resq₁ resq₂ Q hresq) (primToRel D₁ resq₁ ιq₁)
    (primToRel D₂ resq₂ ιq₂) (sprodCx 0 P.u0 W.w0) (sprodCx 1 P.u1 W.w1)
    (fun u => Prod.ext (P.hu (u : D₁.U.X 0 × Uq₁.X 0).1) (W.hw (u : D₁.U.X 0 × Uq₁.X 0).2))
    (fun u => Prod.ext rfl (W.hι0 (u : D₁.U.X 0 × Uq₁.X 0).2))
    (fun u => Prod.ext rfl (W.hι1 (u : D₁.U.X 1 × Uq₁.X 1).2)) zR₁ zP₁ e₁⟩

end AddPlace

/-! ### The genuine data -/

/-- The differential out of degree `−1` of a complex `natCx K` vanishes. Kind: PROVED. -/
theorem natCx_d_neg {k : Type} [CommRing k] (K : CochainComplex (ModuleCat.{0} k) ℕ) (j : ℤ)
    (h : (0 - 1 : ℤ) + 1 = j) (y : (natCx K).X (0 - 1)) : (natCx K).d (0 - 1) j h y = 0 :=
  rfl

section Genuine

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] (φ : k₁ →+* k₂)
  {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {M₁ : Type} [AddCommGroup M₁] [Module k₁ M₁] [DistribMulAction (GKS K S) M₁]
  [SMulCommClass (GKS K S) k₁ M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul (GKS K S) M₁]
  {M₂ : Type} [AddCommGroup M₂] [Module k₂ M₂] [DistribMulAction (GKS K S) M₂]
  [SMulCommClass (GKS K S) k₂ M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
  [ContinuousSMul (GKS K S) M₂]
  (f : M₁ →ₛₗ[φ] M₂) (hf : ∀ (g : GKS K S) (m : M₁), f (g • m) = g • f m)

/-- The coefficient map on the restricted module at a place. Kind: definition. -/
def resPush (v : HeightOneSpectrum (𝓞 K)) :
    ResMod (locMap K S v) M₁ →ₛₗ[φ] ResMod (locMap K S v) M₂ := f

include hf in
theorem resPush_equivariant (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v)
    (m : ResMod (locMap K S v) M₁) : resPush φ f v (σ • m) = σ • resPush φ f v m :=
  hf (locMap K S v σ) m

/-- **The push of the local complex at a place** (degrees `−1, 0, 1`). Kind: definition. -/
def locPush (v : HeightOneSpectrum (𝓞 K)) :
    LocPush φ (natCx (contCochains k₁ (Gloc K v) (ResMod (locMap K S v) M₁)))
      (natCx (contCochains k₂ (Gloc K v) (ResMod (locMap K S v) M₂))) where
  lm := 0
  l0 := cmapCx φ (resPush φ f v) 0
  l1 := cmapCx φ (resPush φ f v) 1
  hdm x := by rw [natCx_d_neg, natCx_d_neg, map_zero]
  hd0 x := cmap_d0 φ (resPush φ f v) (resPush_equivariant φ f hf v) x

/-- **A push of one local condition** at the place `v`, compatible with `locPush` (data with
identities). Kind: definition. -/
structure CondPushAt (v : HeightOneSpectrum (𝓞 K)) {U₁ : GCx k₁} {U₂ : GCx k₂}
    (i₁ : GHom U₁ (natCx (contCochains k₁ (Gloc K v) (ResMod (locMap K S v) M₁))))
    (i₂ : GHom U₂ (natCx (contCochains k₂ (Gloc K v) (ResMod (locMap K S v) M₂)))) where
  /-- degree `0` -/
  u0 : U₁.X 0 →ₛₗ[φ] U₂.X 0
  /-- degree `1` -/
  u1 : U₁.X 1 →ₛₗ[φ] U₂.X 1
  /-- compatibility with the differential -/
  hu : ∀ u, u1 (U₁.d 0 1 rfl u) = U₂.d 0 1 rfl (u0 u)
  /-- compatibility with the local maps -/
  hι : ∀ u, (locPush φ f hf v).l0 (i₁.f 0 0 rfl u) = i₂.f 0 0 rfl (u0 u)

/-- **The full condition is pushed to the full condition** (PROVED). -/
def CondPushAt.full (v : HeightOneSpectrum (𝓞 K)) :
    CondPushAt φ f hf v (idGHom _) (idGHom _) where
  u0 := (locPush φ f hf v).l0
  u1 := (locPush φ f hf v).l1
  hu := (locPush φ f hf v).hd0
  hι _ := rfl

/-- **A cocycle condition is pushed into a cocycle condition** (PROVED) when the coefficient
change maps `Z₁` into `Z₂`. -/
def CondPushAt.cocycle (v : HeightOneSpectrum (𝓞 K))
    (Z₁ : Submodule k₁ (contCochain k₁ (Gloc K v) (ResMod (locMap K S v) M₁) 1))
    (hZ₁ : ∀ z ∈ Z₁, contD k₁ (Gloc K v) (ResMod (locMap K S v) M₁) 1 z = 0)
    (Z₂ : Submodule k₂ (contCochain k₂ (Gloc K v) (ResMod (locMap K S v) M₂) 1))
    (hZ₂ : ∀ z ∈ Z₂, contD k₂ (Gloc K v) (ResMod (locMap K S v) M₂) 1 z = 0)
    (hZ : ∀ z ∈ Z₁, cmap φ (resPush φ f v) 1 z ∈ Z₂) :
    CondPushAt φ f hf v (cocycleConditionι Z₁ hZ₁) (cocycleConditionι Z₂ hZ₂) where
  u0 :=
    { toFun := fun u => (⟨cmap φ (resPush φ f v) 0 (u : condP Z₁ 0).1, Submodule.mem_top⟩ :
        condP Z₂ 0)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (LinearMap.map_smulₛₗ _ _ _) }
  u1 :=
    { toFun := fun u => (⟨cmap φ (resPush φ f v) 1 (u : condP Z₁ 1).1,
        cocyclePush φ (resPush φ f v) (resPush_equivariant φ f hf v) Z₁ Z₂ hZ
          (u : condP Z₁ 1).2⟩ : condP Z₂ 1)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (LinearMap.map_smulₛₗ _ _ _) }
  hu u := Subtype.ext (cmap_d0 φ (resPush φ f v) (resPush_equivariant φ f hf v)
    (u : condP Z₁ 0).1)
  hι _ := rfl

open scoped Classical in
/-- **The extended Kummer condition is pushed into the extended Kummer condition** (PROVED; tex
3262–3270) when `ι₂ = f ∘ ι₁`. -/
def CondPushAt.kummer (v : HeightOneSpectrum (𝓞 K)) {B : WeierstrassCurve (v.adicCompletion K)}
    [B.IsElliptic] {m : ℕ} [NeZero m]
    (ι₁ : TorsAlg (v.adicCompletion K) B m →+ ResMod (locMap K S v) M₁)
    (hι₁ : ∀ (σ : Gloc K v) (t : TorsAlg (v.adicCompletion K) B m), ι₁ (σ • t) = σ • ι₁ t)
    (ι₂ : TorsAlg (v.adicCompletion K) B m →+ ResMod (locMap K S v) M₂)
    (hι₂ : ∀ (σ : Gloc K v) (t : TorsAlg (v.adicCompletion K) B m), ι₂ (σ • t) = σ • ι₂ t)
    (hι : ∀ t, ι₂ t = resPush φ f v (ι₁ t)) :
    CondPushAt φ f hf v (kummerConditionInι k₁ ι₁ hι₁) (kummerConditionInι k₂ ι₂ hι₂) :=
  CondPushAt.cocycle φ f hf v _ _ _ _ fun _ hz =>
    kummer_push_mem φ (resPush φ f v) ι₁ ι₂ hι hz

/-- **The push of the genuine Selmer data** from per-place condition pushes. Kind: definition. -/
def selDataPush (Δ₁ : LocalConditions k₁ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₁)
    (Δ₂ : LocalConditions k₂ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₂)
    (C : ∀ v : Places K S₀, CondPushAt φ f hf v.1 (Δ₁.i v) (Δ₂.i v)) :
    SelPush φ (stageOld K S₀ S k₁ M₁ Δ₁) (stageOld K S₀ S k₂ M₂ Δ₂) where
  g0 := cmapCx φ f 0
  g1 := cmapCx φ f 1
  u0 :=
    { toFun := fun x v => (C v).u0 (x v)
      map_add' := fun _ _ => funext fun v => map_add _ _ _
      map_smul' := fun _ _ => funext fun v => LinearMap.map_smulₛₗ _ _ _ }
  u1 :=
    { toFun := fun x v => (C v).u1 (x v)
      map_add' := fun _ _ => funext fun v => map_add _ _ _
      map_smul' := fun _ _ => funext fun v => LinearMap.map_smulₛₗ _ _ _ }
  lm := 0
  l0 :=
    { toFun := fun x v => (locPush φ f hf v.1).l0 (x v)
      map_add' := fun _ _ => funext fun v => map_add _ _ _
      map_smul' := fun _ _ => funext fun v => LinearMap.map_smulₛₗ _ _ _ }
  hg a := cmap_d0 φ f hf a
  hu x := funext fun v => (C v).hu (x v)
  hres _ := rfl
  hι x := funext fun v => (C v).hι (x v)
  hL x := funext fun v => by
    change (locPush φ f hf v.1).l0 ((natCx _).d (0 - 1) (1 - 1) (by omega) (x v)) =
      (natCx _).d (0 - 1) (1 - 1) (by omega) (0 : (natCx (contCochains k₂ (Gloc K v.1)
        (ResMod (locMap K S v.1) M₂))).X (0 - 1))
    rw [natCx_d_neg, natCx_d_neg, map_zero]

/-- **The push of the genuine relaxed data at `w`**. Kind: definition. -/
def relaxedPush (Δ₁ : LocalConditions k₁ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₁)
    (Δ₂ : LocalConditions k₂ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₂)
    (C : ∀ v : Places K S₀, CondPushAt φ f hf v.1 (Δ₁.i v) (Δ₂.i v)) (w : Places K S) :
    SelPush φ (stageRelaxed K S₀ S k₁ M₁ Δ₁ w) (stageRelaxed K S₀ S k₂ M₂ Δ₂ w) :=
  (selDataPush φ f hf Δ₁ Δ₂ C).relaxed _ _ (locPush φ f hf w.1) (fun _ => rfl)

/-- **`H20CoefficientPush` on the genuine relaxed data** (PROVED; tex 3203–3215, 3262–3270,
3281–3290): for per-place pushes of the old conditions (e.g. `CondPushAt.kummer`), a push `W` of
the condition at `w` compatible with `ι_q`, any source classes and `e₁`, the pushed relaxed class
and a pushed primitive class satisfy `H20CoefficientPush` with `e₂ = φ(e₁)`. -/
theorem h20CoefficientPush_genuine
    (Δ₁ : LocalConditions k₁ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₁)
    (Δ₂ : LocalConditions k₂ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₂)
    (C : ∀ v : Places K S₀, CondPushAt φ f hf v.1 (Δ₁.i v) (Δ₂.i v)) (w : Places K S)
    {Uq₁ : GCx k₁} {Uq₂ : GCx k₂}
    (ιq₁ : GHom Uq₁ (natCx (contCochains k₁ (Gloc K w.1) (ResMod (locMap K S w.1) M₁))))
    (ιq₂ : GHom Uq₂ (natCx (contCochains k₂ (Gloc K w.1) (ResMod (locMap K S w.1) M₂))))
    (W : WPush φ (locPush φ f hf w.1) ιq₁ ιq₂)
    (zR₁ : (selCx (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)).X 1)
    (zP₁ : (selCx (selRestrict (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)
      (primToRel (stageOld K S₀ S k₁ M₁ Δ₁) (stageRes K S k₁ M₁ w) ιq₁))).X 1) (e₁ : k₁) :
    ∃ zP₂ : (selCx (selRestrict (stageRelaxed K S₀ S k₂ M₂ Δ₂ w)
        (primToRel (stageOld K S₀ S k₂ M₂ Δ₂) (stageRes K S k₂ M₂ w) ιq₂))).X 1,
      H20CoefficientPush (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)
        (primToRel (stageOld K S₀ S k₁ M₁ Δ₁) (stageRes K S k₁ M₁ w) ιq₁) zR₁ zP₁ e₁
        (stageRelaxed K S₀ S k₂ M₂ Δ₂ w)
        (primToRel (stageOld K S₀ S k₂ M₂ Δ₂) (stageRes K S k₂ M₂ w) ιq₂)
        ((relaxedPush φ f hf Δ₁ Δ₂ C w).push1 zR₁) zP₂ (φ e₁) :=
  h20CoefficientPush_relaxed (selDataPush φ f hf Δ₁ Δ₂ C) _ _ (locPush φ f hf w.1)
    (fun _ => rfl) ιq₁ ιq₂ W zR₁ zP₁ e₁

/-- **The pushed class is the stage transferred Kummer class of the pushed point** (PROVED; the
coefficient-push step, by naturality of the transfer, tex 3203–3250): if the global component of the source class
is carried by `ι₁` to `𝒯_{θ₁}(κ(Q))` in a `k₁`-module `D₁` of points, and `c : D₁ → D₂` is a
`φ`-semilinear equivariant coefficient map with `ι₂ ∘ f = c ∘ ι₁` and `φ ∘ θ₁ = θ₂`, then the
global component of the pushed class is carried by `ι₂` to `𝒯_{θ₂}(κ(c Q))`. -/
theorem pushed_class_transfer
    (Δ₁ : LocalConditions k₁ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₁)
    (Δ₂ : LocalConditions k₂ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₂)
    (C : ∀ v : Places K S₀, CondPushAt φ f hf v.1 (Δ₁.i v) (Δ₂.i v)) (w : Places K S)
    (H : Subgroup (GKS K S)) [H.Normal] [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
    (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
    {D₁ D₂ : Type} [AddCommGroup D₁] [Module k₁ D₁] [AddCommGroup D₂] [Module k₂ D₂]
    (ρ₁ : GKS K S →* Module.End k₁ D₁) (ρ₂ : GKS K S →* Module.End k₂ D₂)
    (θ₁ : GKS K S ⧸ H →* k₁ˣ) (θ₂ : GKS K S ⧸ H →* k₂ˣ) (c : D₁ →ₛₗ[φ] D₂)
    (hφ : ∀ x, φ (θ₁ x : k₁) = θ₂ x) (hc : ∀ g x, c (ρ₁ g x) = ρ₂ g (c x))
    (ι₁ : M₁ →ₗ[k₁] D₁) (ι₂ : M₂ →ₗ[k₂] D₂) (hιc : ∀ x, ι₂ (f x) = c (ι₁ x)) (Q : D₁)
    (zR₁ : (selCx (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S, ι₁ (gval (A := k₁) (M := M₁) (zR₁ : selT _ 1).1 g) =
      T H r hr ρ₁ θ₁ 1 (kummerCochain ρ₁ H Q) g) (g : Fin 1 → GKS K S) :
    ι₂ (gval (A := k₂) (M := M₂)
        (((relaxedPush φ f hf Δ₁ Δ₂ C w).push1 zR₁ : (selCx _).X 1) : selT _ 1).1 g) =
      T H r hr ρ₂ θ₂ 1 (kummerCochain ρ₂ H (c Q)) g := by
  change ι₂ (f (gval (A := k₁) (M := M₁) (zR₁ : selT _ 1).1 g)) = _
  rw [hιc, hz, transfer_kummer_coeff H r hr φ ρ₁ ρ₂ θ₁ θ₂ c hφ hc]

/-- **The local conditions are pushed** (Prop; the remaining input of (H20) on the Selmer
complexes, tex 3262–3270): per-place pushes of the old conditions compatible with the coefficient
change, and a push of the condition at the new place `w` compatible with `ι_q`. For the old Kummer
conditions the first part is `CondPushAt.kummer`, i.e. the compatibility `ι₂ = f ∘ ι₁` of the
coefficient maps (`h20ConditionsPush_kummer`). Kind: definition (Prop). -/
def H20ConditionsPush
    (Δ₁ : LocalConditions k₁ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₁)
    (Δ₂ : LocalConditions k₂ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₂) (w : Places K S) {Uq₁ : GCx k₁} {Uq₂ : GCx k₂}
    (ιq₁ : GHom Uq₁ (natCx (contCochains k₁ (Gloc K w.1) (ResMod (locMap K S w.1) M₁))))
    (ιq₂ : GHom Uq₂ (natCx (contCochains k₂ (Gloc K w.1) (ResMod (locMap K S w.1) M₂)))) :
    Prop :=
  Nonempty (∀ v : Places K S₀, CondPushAt φ f hf v.1 (Δ₁.i v) (Δ₂.i v)) ∧
    Nonempty (WPush φ (locPush φ f hf w.1) ιq₁ ιq₂)

/-- **`H20CoefficientPush` from `H20ConditionsPush`** (PROVED): for any source classes there are
stage classes (the pushes) with `H20CoefficientPush` and `e₂ = φ(e₁)`. -/
theorem h20CoefficientPush_of_conditionsPush
    (Δ₁ : LocalConditions k₁ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₁)
    (Δ₂ : LocalConditions k₂ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₂) (w : Places K S) {Uq₁ : GCx k₁} {Uq₂ : GCx k₂}
    (ιq₁ : GHom Uq₁ (natCx (contCochains k₁ (Gloc K w.1) (ResMod (locMap K S w.1) M₁))))
    (ιq₂ : GHom Uq₂ (natCx (contCochains k₂ (Gloc K w.1) (ResMod (locMap K S w.1) M₂))))
    (hpush : H20ConditionsPush φ f hf Δ₁ Δ₂ w ιq₁ ιq₂)
    (zR₁ : (selCx (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)).X 1)
    (zP₁ : (selCx (selRestrict (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)
      (primToRel (stageOld K S₀ S k₁ M₁ Δ₁) (stageRes K S k₁ M₁ w) ιq₁))).X 1) (e₁ : k₁) :
    ∃ (zR₂ : (selCx (stageRelaxed K S₀ S k₂ M₂ Δ₂ w)).X 1)
      (zP₂ : (selCx (selRestrict (stageRelaxed K S₀ S k₂ M₂ Δ₂ w)
        (primToRel (stageOld K S₀ S k₂ M₂ Δ₂) (stageRes K S k₂ M₂ w) ιq₂))).X 1),
      H20CoefficientPush (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)
        (primToRel (stageOld K S₀ S k₁ M₁ Δ₁) (stageRes K S k₁ M₁ w) ιq₁) zR₁ zP₁ e₁
        (stageRelaxed K S₀ S k₂ M₂ Δ₂ w)
        (primToRel (stageOld K S₀ S k₂ M₂ Δ₂) (stageRes K S k₂ M₂ w) ιq₂) zR₂ zP₂ (φ e₁) := by
  obtain ⟨⟨C⟩, ⟨W⟩⟩ := hpush
  obtain ⟨zP₂, h⟩ := h20CoefficientPush_genuine φ f hf Δ₁ Δ₂ C w ιq₁ ιq₂ W zR₁ zP₁ e₁
  exact ⟨_, zP₂, h⟩

/-- **The stage norm identity from the Shapiro-level one** (PROVED): under `H20ConditionsPush`,
the norm identity with retained boundary `z_R¹ = e₁ • i(z_P¹) + d b` for genuine relaxed and
primitive classes over `k₁` gives stage classes with `z_R² = φ(e₁) • i(z_P²) + d b'` over `k₂`. -/
theorem hzR_stage_of_shapiro
    (Δ₁ : LocalConditions k₁ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₁)
    (Δ₂ : LocalConditions k₂ (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M₂) (w : Places K S) {Uq₁ : GCx k₁} {Uq₂ : GCx k₂}
    (ιq₁ : GHom Uq₁ (natCx (contCochains k₁ (Gloc K w.1) (ResMod (locMap K S w.1) M₁))))
    (ιq₂ : GHom Uq₂ (natCx (contCochains k₂ (Gloc K w.1) (ResMod (locMap K S w.1) M₂))))
    (hpush : H20ConditionsPush φ f hf Δ₁ Δ₂ w ιq₁ ιq₂)
    (zR₁ : (selCx (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)).X 1)
    (zP₁ : (selCx (selRestrict (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)
      (primToRel (stageOld K S₀ S k₁ M₁ Δ₁) (stageRes K S k₁ M₁ w) ιq₁))).X 1) (e₁ : k₁)
    (h₁ : ∃ b, zR₁ = e₁ • (changeMap _ _).f 1 1 rfl zP₁ +
      (selCx (stageRelaxed K S₀ S k₁ M₁ Δ₁ w)).d 0 1 rfl b) :
    ∃ (zR₂ : (selCx (stageRelaxed K S₀ S k₂ M₂ Δ₂ w)).X 1)
      (zP₂ : (selCx (selRestrict (stageRelaxed K S₀ S k₂ M₂ Δ₂ w)
        (primToRel (stageOld K S₀ S k₂ M₂ Δ₂) (stageRes K S k₂ M₂ w) ιq₂))).X 1),
      ∃ b, zR₂ = φ e₁ • (changeMap _ _).f 1 1 rfl zP₂ +
        (selCx (stageRelaxed K S₀ S k₂ M₂ Δ₂ w)).d 0 1 rfl b := by
  obtain ⟨zR₂, zP₂, h⟩ :=
    h20CoefficientPush_of_conditionsPush φ f hf Δ₁ Δ₂ w ιq₁ ιq₂ hpush zR₁ zP₁ e₁
  exact ⟨zR₂, zP₂, hzR_of_H20 _ _ _ _ _ _ _ _ _ _ h₁ h⟩

open scoped Classical in
/-- **`H20ConditionsPush` for the old Kummer conditions** (PROVED; tex 3262–3270): it reduces to
the compatibility `ι₂ = f ∘ ι₁` of the Kummer coefficient maps at the old places and a push of
the condition at `w`. -/
theorem h20ConditionsPush_kummer (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (ι₁ : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M₁)
    (hι₁ : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι₁ v (σ • t) = σ • ι₁ v t)
    (ι₂ : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M₂)
    (hι₂ : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι₂ v (σ • t) = σ • ι₂ v t)
    (hι : ∀ v t, ι₂ v t = resPush φ f v.1 (ι₁ v t)) (w : Places K S) {Uq₁ : GCx k₁}
    {Uq₂ : GCx k₂}
    (ιq₁ : GHom Uq₁ (natCx (contCochains k₁ (Gloc K w.1) (ResMod (locMap K S w.1) M₁))))
    (ιq₂ : GHom Uq₂ (natCx (contCochains k₂ (Gloc K w.1) (ResMod (locMap K S w.1) M₂))))
    (W : WPush φ (locPush φ f hf w.1) ιq₁ ιq₂) :
    H20ConditionsPush φ f hf (kummerOldConditions K S₀ S k₁ M₁ m B ι₁ hι₁)
      (kummerOldConditions K S₀ S k₂ M₂ m B ι₂ hι₂) w ιq₁ ιq₂ :=
  ⟨⟨fun v => CondPushAt.kummer φ f hf v.1 (ι₁ v) (hι₁ v) (ι₂ v) (hι₂ v) (hι v)⟩, ⟨W⟩⟩

end Genuine

/-! ### Non-vacuity -/

/-- **Non-vacuity of `CondPushAt`**: the full condition is pushed along the identity.
Kind: PROVED. -/
theorem nonVacuity_condPush {k : Type} [CommRing k] {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (CondPushAt (RingHom.id k) (LinearMap.id : M →ₗ[k] M) (fun _ _ => rfl) v
      (S := S) (idGHom _) (idGHom _)) :=
  ⟨CondPushAt.full _ _ _ v⟩

end ZInQ.Contrib.CloudB3E2.NormCochain

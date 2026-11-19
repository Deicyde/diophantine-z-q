import ZInQKernel.Contrib.CloudB3E2Norm.LocalIdentity

/-!
# The genuine wrappers over a commutative coefficient ring (the stage ring `A_i`)

Lanes RC28/RC29's genuine local conditions live over the stage ring `A_i = Acoef i`
(`(ℤ/2^i)[t]/t^i`, not a field), while lane RC32's genuine Selmer data
(`RC/Wiring/CommonCoordinate11Genuine.lean`) are declared in a section with `(k : Type) [Field k]
[TopologicalSpace k]`. This file restates the genuine objects and this directory's genuine
wrappers over any commutative ring `k`:

* `stageOld`, `stageRes`, `stageRelaxed` (definitions, `[CommRing k]`; `stagePrimitive` also needs
  `[TopologicalSpace k]` for the unramified complex `genuineUq`): RC32's `genuineOld`,
  `genuineRes`, `genuineRelaxed`, `genuinePrimitive` with the same bodies;
  `stageOld_eq_genuineOld`, `stageRes_eq_genuineRes`, `stageRelaxed_eq_genuineRelaxed`,
  `stagePrimitive_eq_genuinePrimitive` (PROVED, `rfl`): over a field they ARE RC32's objects.
* **`hG_stage_of_transfer`** (from `hG_genuine_of_transfer`), **`hzR_stage_of_strictLifts`**
  (from `hzR_genuine_of_strictLifts`), **`exists_hRloc_stage`** (from `exists_hRloc_genuine`) and
  **`exists_hRloc_of_oldInputs_stage`** (from `exists_hRloc_of_oldInputs`) (all PROVED): the
  genuine wrappers at `stageRelaxed` over any commutative ring.

**Which ring.** The Selmer-complex statements (`exists_hRloc_stage`, and the generic reductions
it uses) apply at `k = Acoef i` with lanes RC28/RC29's local conditions. The transfer hypotheses
(`hzR`, `hzP`, `hz`: the genuine classes are carried to `𝒯_θ(κ(Q_T))` in a `k`-module `D` of points)
are non-degenerate only over a coefficient ring that does not kill the points' division (e.g. the
group ring `ℤ[Δ_f]` with the universal character, the Shapiro level of (H20)); over `A_i`, where
`2^i = 0`, they force `y_T = 0` (see `LocalIdentity.lean`, "Coefficient ring"). The passage from
`ℤ[Δ_f]` to `A_i` (`δ ↦ θ(δ)`, (H20)) is a coefficient change of the Selmer complexes, not
formalized here.

**Which of RC32's genuine definitions need a field, and why** (checked by compiling their
bodies over `[CommRing k]`): `genuineOld` (`selData`), `genuineRes` (restriction of continuous
cochains) and `genuineRelaxed` (`relaxedAt`) need only `[CommRing k]`; `genuinePrimitive` needs
`[CommRing k] [TopologicalSpace k]` (the unramified complex of a `TopRep k`); the section's
`[Field k]` is inherited, not used. Only `genuineSupportTriangle` needs the field: it produces a
`SupportTriangle k`, declared over `[Field F]`, whose data feed the full-condition model
(`relModel`, `relRetract`, `CommonCoordinate10Model.lean`, section `[Field F]`) and the
Knudsen–Mumford step (`KmStep`, `KmCoordBilinear.lean`, sections `[Field K]`: the step inverts
`det B` and `q`, and identifies coordinates up to the determinant of the two-place block), i.e.
the coordinates are taken over a field. (Lane RC31's `kmCoord` itself is stated over any
commutative ring; the split inclusion, the block complexes and the retracts are over any
commutative ring as well.) So a stage-ring version of the common-coordinate step must stop
before the coordinates: the cochain-level norm identity `hzR` holds over `A_i` (this file), and
the passage to `SupportTriangle` needs a base change of the stage complexes to a field.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### The genuine objects over a commutative ring -/

section Objects

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The genuine old Selmer data over a commutative ring** (RC32's `genuineOld`, same body).
Kind: definition. -/
abbrev stageOld (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M) : SelData k :=
  selData k (GKS K S) (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K S v.1) M Δ

/-- **The genuine restriction to the new place over a commutative ring** (RC32's `genuineRes`).
Kind: definition. -/
abbrev stageRes (w : Places K S) :
    GHom (globalCx k (GKS K S) M)
      (natCx (contCochains k (Gloc K w.1) (ResMod (locMap K S w.1) M))) :=
  natHom (resCochains (k := k) (M := M) (locMap K S w.1))

/-- **The genuine relaxed Selmer data over a commutative ring** (RC32's `genuineRelaxed`).
Kind: definition. -/
abbrev stageRelaxed (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M) (w : Places K S) : SelData k :=
  relaxedAt (stageOld K S₀ S k M Δ) (stageRes K S k M w)

/-- **The genuine primitive Selmer data over a commutative ring** (RC32's `genuinePrimitive`).
Kind: definition. -/
abbrev stagePrimitive [TopologicalSpace k]
    (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M) (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x) :
    SelData k :=
  addPlace (stageOld K S₀ S k M Δ) (stageRes K S k M w) (genuineιq K S k M w X f hf)

end Objects

section Compat

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M) (w : Places K S)

set_option linter.unusedSectionVars false

/-- Over a field, `stageOld` is RC32's `genuineOld`. Kind: PROVED. -/
theorem stageOld_eq_genuineOld : stageOld K S₀ S k M Δ = genuineOld K S₀ S k M Δ := rfl

/-- Over a field, `stageRes` is RC32's `genuineRes`. Kind: PROVED. -/
theorem stageRes_eq_genuineRes : stageRes K S k M w = genuineRes K S k M w := rfl

/-- Over a field, `stageRelaxed` is RC32's `genuineRelaxed`. Kind: PROVED. -/
theorem stageRelaxed_eq_genuineRelaxed :
    stageRelaxed K S₀ S k M Δ w = genuineRelaxed K S₀ S k M Δ w := rfl

/-- Over a field, `stagePrimitive` is RC32's `genuinePrimitive`. Kind: PROVED. -/
theorem stagePrimitive_eq_genuinePrimitive (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x) :
    stagePrimitive K S₀ S k M Δ w X f hf = genuinePrimitive K S₀ S k M Δ w X f hf := rfl

end Compat

/-! ### The genuine wrappers over a commutative ring -/

section Wrappers

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {D : Type} [AddCommGroup D] [Module k D] (ρ : GKS K S →* Module.End k D)
  (HP HR : Subgroup (GKS K S)) [HP.Normal] [HR.Normal] [Fintype (GKS K S ⧸ HP)]
  [Fintype (GKS K S ⧸ HR)]
  (rP : GKS K S ⧸ HP → GKS K S) (hrP : ∀ δ, ((rP δ : GKS K S) : GKS K S ⧸ HP) = δ)
  (rR : GKS K S ⧸ HR → GKS K S) (hrR : ∀ δ, ((rR δ : GKS K S) : GKS K S ⧸ HR) = δ)
  (θP : GKS K S ⧸ HP →* kˣ) (θR : GKS K S ⧸ HR →* kˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

set_option linter.unusedSectionVars false

include hrP hrR hU ht in
/-- **`hG` at the stage relaxed data** (PROVED): `hG_genuine_of_transfer` over any commutative
coefficient ring. -/
theorem hG_stage_of_transfer
    (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M) (w : Places K S) {U' : GCx k}
    (f : GHom U' (stageRelaxed K S₀ S k M Δ w).U)
    (zR : (selCx (stageRelaxed K S₀ S k M Δ w)).X 1)
    (zP : (selCx (selRestrict (stageRelaxed K S₀ S k M Δ w) f)).X 1)
    (hle : HR ≤ HP)
    (hθ : ∀ x : GKS K S, ((θR (x : GKS K S ⧸ HR) : kˣ) : k) = θP (x : GKS K S ⧸ HP))
    (kk a : ℤ) (σ : GKS K S) {yR yP QR QP : D}
    (hQR : kk • QR = yR) (hQP : kk • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : GKS K S) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP)
    (ι : M →ₗ[k] D) (hι : Function.Injective ι)
    (hιeq : ∀ (g : GKS K S) (m : M), ι (g • m) = R HR ρ θR g (ι m))
    (htors : ∀ x : D, kk • x = 0 → ∃ m : M, ι m = x)
    (hzR : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) zR.1 g) = T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g)
    (hzP : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) (primG (stageRelaxed K S₀ S k M Δ w) f 1 zP) g) =
        T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g) :
    ∃ bG : (stageRelaxed K S₀ S k M Δ w).G.X 0,
      zR.1 = eq_ HP θP a σ • primG (stageRelaxed K S₀ S k M Δ w) f 1 zP +
        (stageRelaxed K S₀ S k M Δ w).G.d 0 1 rfl bG :=
  hG_of_transfer ρ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ kk a σ hQR hQP hfixR hfixP hnorm
    ι hι hιeq htors zR.1 (primG (stageRelaxed K S₀ S k M Δ w) f 1 zP) hzR hzP

include hrP hrR hU ht in
/-- **The full `hzR` at the stage relaxed data for strict lifts** (PROVED):
`hzR_genuine_of_strictLifts` over any commutative coefficient ring. -/
theorem hzR_stage_of_strictLifts
    (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M) (w : Places K S) {U' : GCx k}
    (f : GHom U' (stageRelaxed K S₀ S k M Δ w).U)
    (aR aP : (globalCx k (GKS K S) M).X 1)
    (uR : (stageRelaxed K S₀ S k M Δ w).U.X 1) (uP : U'.X 1)
    (hιold : Function.Injective ((stageOld K S₀ S k M Δ).ι.f 1 1 rfl))
    (hsold : ∀ y : (stageOld K S₀ S k M Δ).L.X 0,
      ∃ x : (stageOld K S₀ S k M Δ).U.X 0, (stageOld K S₀ S k M Δ).ι.f 0 0 rfl x = y)
    (hRloc : (stageRelaxed K S₀ S k M Δ w).ι.f 1 1 rfl uR =
      (stageRelaxed K S₀ S k M Δ w).res.f 1 1 rfl aR)
    (hPloc : (stageRelaxed K S₀ S k M Δ w).ι.f 1 1 rfl (f.f 1 1 rfl uP) =
      (stageRelaxed K S₀ S k M Δ w).res.f 1 1 rfl aP)
    (hle : HR ≤ HP)
    (hθ : ∀ x : GKS K S, ((θR (x : GKS K S ⧸ HR) : kˣ) : k) = θP (x : GKS K S ⧸ HP))
    (kk a : ℤ) (σ : GKS K S) {yR yP QR QP : D}
    (hQR : kk • QR = yR) (hQP : kk • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : GKS K S) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP)
    (ι : M →ₗ[k] D) (hι : Function.Injective ι)
    (hιeq : ∀ (g : GKS K S) (m : M), ι (g • m) = R HR ρ θR g (ι m))
    (htors : ∀ x : D, kk • x = 0 → ∃ m : M, ι m = x)
    (hzR : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) aR g) = T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g)
    (hzP : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) aP g) = T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g) :
    ∃ b : (selCx (stageRelaxed K S₀ S k M Δ w)).X 0,
      strictLift (stageRelaxed K S₀ S k M Δ w) aR uR =
        eq_ HP θP a σ • (changeMap (stageRelaxed K S₀ S k M Δ w) f).f 1 1 rfl
          (strictLiftP (stageRelaxed K S₀ S k M Δ w) f aP uP) +
        (selCx (stageRelaxed K S₀ S k M Δ w)).d 0 1 rfl b := by
  obtain ⟨bG, hG⟩ := hG_of_transfer ρ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ kk a σ hQR hQP
    hfixR hfixP hnorm ι hι hιeq htors aR aP hzR hzP
  obtain ⟨bU, hbU⟩ := addPlace_ι_surjective (stageOld K S₀ S k M Δ) (stageRes K S k M w)
    hsold ((stageRelaxed K S₀ S k M Δ w).res.f 0 0 rfl bG)
  exact ⟨_, hzR_of_strictLifts (stageRelaxed K S₀ S k M Δ w) f aR aP uR uP _ bG bU
    (addPlace_ι_injective (stageOld K S₀ S k M Δ) (stageRes K S k M w) hιold) hRloc hPloc
    hG hbU⟩

/-- **`hRloc` at the stage relaxed data from the old places** (PROVED): `exists_hRloc_genuine`
over any commutative coefficient ring. -/
theorem exists_hRloc_stage
    (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M) (w : Places K S) (aR : (globalCx k (GKS K S) M).X 1)
    (hold : ∀ v : Places K S₀, ∃ u : (Δ.U v).X 1,
      (Δ.i v).f 1 1 rfl u = (stageOld K S₀ S k M Δ).res.f 1 1 rfl aR v) :
    ∃ uR : (stageRelaxed K S₀ S k M Δ w).U.X 1,
      (stageRelaxed K S₀ S k M Δ w).ι.f 1 1 rfl uR =
        (stageRelaxed K S₀ S k M Δ w).res.f 1 1 rfl aR :=
  exists_lift_relaxedAt (stageOld K S₀ S k M Δ) (stageRes K S k M w) aR
    (exists_lift_selData Δ aR hold)

open scoped Classical in
include hrR in
/-- **`hRloc` at the stage relaxed data from the old-place inputs** (PROVED):
`exists_hRloc_of_oldInputs` over any commutative coefficient ring, e.g. `k = Acoef i` with the
Kummer conditions of lanes RC28/RC29 at the old places. -/
theorem exists_hRloc_of_oldInputs_stage (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (ιv : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hιv : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ιv v (σ • t) = σ • ιv v t) (w : Places K S)
    (ι : M →ₗ[k] D) (hιeq : ∀ (g : GKS K S) (x : M), ι (g • x) = R HR ρ θR g (ι x))
    {Q y : D} (hQ : (m : ℤ) • Q = y)
    (hin : ∀ v : Places K S₀, OldPlaceInput ρ HR rR θR v.1 (B v) m (ιv v) ι y)
    (aT : (globalCx k (GKS K S) M).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) aT g) = T HR rR hrR ρ θR 1 (kummerCochain ρ HR Q) g) :
    ∃ uR : (stageRelaxed K S₀ S k M (kummerOldConditions K S₀ S k M m B ιv hιv) w).U.X 1,
      (stageRelaxed K S₀ S k M (kummerOldConditions K S₀ S k M m B ιv hιv) w).ι.f 1 1 rfl uR =
        (stageRelaxed K S₀ S k M (kummerOldConditions K S₀ S k M m B ιv hιv) w).res.f 1 1 rfl
          aT :=
  exists_lift_relaxedAt (stageOld K S₀ S k M (kummerOldConditions K S₀ S k M m B ιv hιv))
    (stageRes K S k M w) aT
    (exists_oldLift_of_inputs ρ HR rR hrR θR m B ιv hιv ι hιeq hQ hin aT hz)

end Wrappers

end ZInQ.Contrib.CloudB3E2.NormCochain

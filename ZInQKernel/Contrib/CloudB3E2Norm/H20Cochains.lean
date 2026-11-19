import ZInQKernel.Contrib.CloudB3E2Norm.H20SelPush

/-!
# The coefficient push (H20) on the genuine continuous cochains and local conditions

Manuscript `diophantine_zq.tex`, tex 3203–3215 (the coefficient map `v ⊗ [δ] ↦ θ(δ) v` of (H20))
and tex 3262–3270 ("the old Kummer conditions proved in paragraph 5 survive (H20)").

For a ring homomorphism `φ : k₁ →+* k₂` and a `φ`-semilinear, `G`-equivariant map `f : M₁ → M₂`
of discrete modules (for the text: the coefficient map of (H20), `h20RingHom θ`-semilinear):

* `cmap f n` (definition): the coefficient change `c ↦ f ∘ c` on continuous `n`-cochains;
  `cmap_d0` (PROVED): it commutes with `d⁰`; `cmap_B1` (PROVED): it maps coboundaries to
  coboundaries.
* `cmapCx f n`: the same on the terms of the genuine complex `natCx (contCochains k G M)`.
* `cocyclePush` (PROVED): the coefficient change maps the cocycle condition `Z₁ ⊔ B¹` into
  `Z₂ ⊔ B¹` when it maps `Z₁` into `Z₂`; **`kummer_push_mem`** (PROVED): it maps the extended
  Kummer submodule of `ι₁` into that of `ι₂` when `ι₂ = f ∘ ι₁` (the generators
  `a • ι₁ ∘ κ_P` go to `φ(a) • ι₂ ∘ κ_P`): the old Kummer conditions survive the push.
* Non-vacuity: `nonVacuity_cmap`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules

set_option linter.unusedSectionVars false

section Cochains

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] (φ : k₁ →+* k₂)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M₁ : Type} [AddCommGroup M₁] [Module k₁ M₁] [DistribMulAction G M₁] [SMulCommClass G k₁ M₁]
  [TopologicalSpace M₁] [DiscreteTopology M₁] [ContinuousSMul G M₁]
  {M₂ : Type} [AddCommGroup M₂] [Module k₂ M₂] [DistribMulAction G M₂] [SMulCommClass G k₂ M₂]
  [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousSMul G M₂]
  (f : M₁ →ₛₗ[φ] M₂)

/-- **The coefficient change on continuous `n`-cochains**: `c ↦ f ∘ c`. Kind: definition. -/
def cmap (n : ℕ) : contCochain k₁ G M₁ n →ₛₗ[φ] contCochain k₂ G M₂ n where
  toFun c := ⟨(fun x => f (cfun c x) : (Fin n → G) → M₂),
    (continuous_of_discreteTopology (f := fun m : M₁ => f m)).comp c.2⟩
  map_add' c c' := Subtype.ext (funext fun x => map_add f (cfun c x) (cfun c' x))
  map_smul' a c := Subtype.ext (funext fun x => LinearMap.map_smulₛₗ f a (cfun c x))

@[simp] theorem cfun_cmap (n : ℕ) (c : contCochain k₁ G M₁ n) (x : Fin n → G) :
    cfun (cmap φ f n c) x = f (cfun c x) := rfl

/-- **The coefficient change commutes with `d⁰`** (PROVED), for `f` equivariant. -/
theorem cmap_d0 (hf : ∀ (g : G) (m : M₁), f (g • m) = g • f m) (c : contCochain k₁ G M₁ 0) :
    cmap φ f 1 (contD k₁ G M₁ 0 c) = contD k₂ G M₂ 0 (cmap φ f 0 c) := by
  apply Subtype.ext
  funext g
  change f (cfun (contD k₁ G M₁ 0 c) g) = cfun (contD k₂ G M₂ 0 (cmap φ f 0 c)) g
  rw [contD_zero_apply, contD_zero_apply, map_sub, hf]
  rfl

/-- **The coefficient change maps coboundaries to coboundaries** (PROVED). -/
theorem cmap_B1 (hf : ∀ (g : G) (m : M₁), f (g • m) = g • f m) {c : contCochain k₁ G M₁ 1}
    (hc : c ∈ contB1 k₁ G M₁) : cmap φ f 1 c ∈ contB1 k₂ G M₂ := by
  obtain ⟨b, rfl⟩ := LinearMap.mem_range.1 hc
  exact LinearMap.mem_range.2 ⟨cmap φ f 0 b, (cmap_d0 φ f hf b).symm⟩

/-- **The coefficient change maps a cocycle condition into a cocycle condition** (PROVED): if it
maps `Z₁` into `Z₂`, it maps `Z₁ ⊔ B¹` into `Z₂ ⊔ B¹`. -/
theorem cocyclePush (hf : ∀ (g : G) (m : M₁), f (g • m) = g • f m)
    (Z₁ : Submodule k₁ (contCochain k₁ G M₁ 1)) (Z₂ : Submodule k₂ (contCochain k₂ G M₂ 1))
    (hZ : ∀ z ∈ Z₁, cmap φ f 1 z ∈ Z₂) {c : contCochain k₁ G M₁ 1}
    (hc : c ∈ Z₁ ⊔ contB1 k₁ G M₁) : cmap φ f 1 c ∈ Z₂ ⊔ contB1 k₂ G M₂ := by
  obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
  rw [map_add]
  exact Submodule.add_mem_sup (hZ z hz) (cmap_B1 φ f hf hb)

/-- The coefficient change on the terms of the genuine complex `natCx (contCochains k G M)`.
Kind: definition. -/
def cmapCx (n : ℕ) :
    (natCx (contCochains k₁ G M₁)).X n →ₛₗ[φ] (natCx (contCochains k₂ G M₂)).X n :=
  cmap φ f n

end Cochains

/-! ### The old Kummer conditions survive the push -/

section Kummer

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] (φ : k₁ →+* k₂)
  {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m]
  {M₁ : Type} [AddCommGroup M₁] [Module k₁ M₁] [DistribMulAction (Field.absoluteGaloisGroup F) M₁]
  [SMulCommClass (Field.absoluteGaloisGroup F) k₁ M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M₁]
  {M₂ : Type} [AddCommGroup M₂] [Module k₂ M₂] [DistribMulAction (Field.absoluteGaloisGroup F) M₂]
  [SMulCommClass (Field.absoluteGaloisGroup F) k₂ M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M₂]
  (f : M₁ →ₛₗ[φ] M₂) (ι₁ : TorsAlg F B m →+ M₁) (ι₂ : TorsAlg F B m →+ M₂)

/-- **A pushed extended Kummer cocycle is an extended Kummer cocycle** (PROVED):
`f ∘ (a • ι₁ ∘ κ_P) = φ(a) • ι₂ ∘ κ_P` when `ι₂ = f ∘ ι₁`. -/
theorem cmap_kummerCocycleIn (hι : ∀ t, ι₂ t = f (ι₁ t)) (a : k₁) (P : B.toAffine.Point) :
    cmap φ f 1 (kummerCocycleIn ι₁ a P) = kummerCocycleIn ι₂ (φ a) P := by
  apply Subtype.ext
  funext g
  change f (a • ι₁ (kummerFun F B m P (g 0))) = φ a • ι₂ (kummerFun F B m P (g 0))
  rw [LinearMap.map_smulₛₗ, hι]

/-- **The extended Kummer submodule is pushed into the extended Kummer submodule** (PROVED; tex
3262–3270: the old Kummer conditions survive (H20)). -/
theorem kummer_push_mem (hι : ∀ t, ι₂ t = f (ι₁ t)) {z : contCochain k₁
    (Field.absoluteGaloisGroup F) M₁ 1} (hz : z ∈ kummerZ' k₁ ι₁) :
    cmap φ f 1 z ∈ kummerZ' k₂ ι₂ := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, P⟩, rfl⟩ := hx
    rw [cmap_kummerCocycleIn φ f ι₁ ι₂ hι]
    exact kummerCocycleIn_mem ι₂ (φ a) P
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end Kummer

/-! ### Non-vacuity -/

/-- **Non-vacuity**: the identity coefficient change (`φ = id`, `f = id`) is the identity on
cochains. Kind: PROVED. -/
theorem nonVacuity_cmap {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] (n : ℕ)
    (c : contCochain k G M n) : cmap (RingHom.id k) (LinearMap.id : M →ₗ[k] M) n c = c :=
  rfl

end ZInQ.Contrib.CloudB3E2.NormCochain

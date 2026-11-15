import ZInQKernel.Contrib.OneProof.RayClassShimura

/-!
# shimura-split2: `rayClassCMAb` and `shimuraFamilyAb` without the composite leaf

Task shimura-split2 (2026-11-15). Report: `docs/research/shimura-split2.md`; log: `scratch/shimura-split2/log.md`.

gt-rayclass (`RayClassShimura.lean`) proved the two GLUE fields `rayClassCMAb` and `shimuraFamilyAb` from one
composite statement, `RayClassCFT.ShimuraMainThmIDeligneY3AbU`: a map `Ψ : ℍ × (B ⊗ 𝔸_f)^× → Y(ℂ)` on a fine
witness `(Y, Φ)` with Deligne's uniformization, holomorphy, the moduli clause at `𝒪̂^×` and Shimura's reciprocity law,
all for the same `Ψ`. A split into "for every `Ψ`" statements is false (gt-rayclass §3: twisting `Ψ` by a unit on one
geometric component keeps the moduli clauses and breaks reciprocity).

This file states Shimura's reciprocity law **on objects, not on a map `Ψ`**. For `τ ∈ ℍ` and `g ∈ (B ⊗ 𝔸_f)^×` let
`L_g = B ∩ 𝒪̂g⁻¹` and `T(τ, g) = (ℂ²/ι(L_g)(τ,1)ᵀ, ι, η_g)` with `η_g(a) = [ι(x)(τ,1)ᵀ/3]` for `x ∈ B`,
`x g ≡ a mod 3𝒪̂`: Deligne's moduli description of the point `[τ, g]` of `Sh_{K₃}(B^×, ℍ^±)`. `MIsAt P τ g` says that
`P : QML3 ℂ` is (`ι`- and level-compatibly uniformized by) `T(τ, g)`. Then

* **LEAF `QMReciprocityL3`** (the main theorem of complex multiplication for the QM surfaces `T(z, g)` at CM points
  `z`): if `MIsAt P z g` and `P'` is the base change of `P` along `σ = [s, K]`, then `MIsAt P' z (q̂(s)^ε g)`. It
  names no `Ψ` and no witness, so it carries no normalization; it is a consequence of the main theorem of CM
  (Shimura–Taniyama) for the CM algebra `F ⊗ K` acting on `H₁ = L_g`.
* **LEAF `ShimuraHolFamilyAb`** (Shimura's Main Theorem I, complex part, on a fine witness): one holomorphic family
  `τ ↦ y_τ` with the moduli clause; shimura-split's `ShimuraHolFamily` with `R1fpPropsAb` (route A).
* GLUE (Props here, proved below where marked): `DCRelTransport` (the moduli point is constant on `DCRel`
  classes), `UnifDetermines` (the object is determined by `(τ, g)`), `ComplexUnifL3` (every object is some
  `T(τ, u)`, `u ∈ 𝒪̂^×`).
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit2

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT ShimuraGlue.Ray
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)

/-! ## §1 The objects `T(τ, g)` -/

/-- **`L_g = B ∩ 𝒪̂ g⁻¹ = {x ∈ B : x g ∈ 𝒪̂}`**, a lattice in `B` (left `𝒪`-stable). -/
def latB (g : BAQˣ) : AddSubgroup LeafQM.B where
  carrier := {x | bEmb x * (g : BAQ) ∈ OhatQ}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_add, add_mul] at *
    exact OhatQ_add hx hy
  zero_mem' := by simp [OhatQ_zero]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, map_neg, neg_mul] at *
    exact OhatQ_neg hx

theorem mem_latB {g : BAQˣ} {x : LeafQM.B} : x ∈ latB g ↔ bEmb x * (g : BAQ) ∈ OhatQ := Iff.rfl

/-- `x ↦ ι(x)(τ, 1)ᵀ`, `B → ℂ²`. -/
def vecAdd (τ : ℂ) : LeafQM.B →+ (Fin 2 → ℂ) where
  toFun x := (iotaC x).mulVec ![τ, 1]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.add_mulVec]

theorem vecAdd_apply (τ : ℂ) (x : LeafQM.B) : vecAdd τ x = (iotaC x).mulVec ![τ, 1] := rfl

/-- **The period lattice `ι(L_g)(τ, 1)ᵀ ⊂ ℂ²` of `T(τ, g)`.** -/
def vecLat (τ : ℂ) (g : BAQˣ) : Submodule ℤ (Fin 2 → ℂ) :=
  ((latB g).map (vecAdd τ)).toIntSubmodule

theorem mem_vecLat {τ : ℂ} {g : BAQˣ} {v : Fin 2 → ℂ} :
    v ∈ vecLat τ g ↔ ∃ x : LeafQM.B, bEmb x * (g : BAQ) ∈ OhatQ ∧ (iotaC x).mulVec ![τ, 1] = v := by
  show v ∈ (latB g).map (vecAdd τ) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

/-- **The level structure of `T(τ, g)`**: `η(a) = Φ(ι(x)(τ, 1)ᵀ / 3)` for every `x ∈ B` with
`x g ∈ a + 3𝒪̂` (`x ≡ a g⁻¹ mod 3 L̂_g`). -/
def LevelAt (P : QML3 ℂ) (Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ)) (τ : ℂ) (g : BAQˣ) : Prop :=
  ∀ (a : LeafQM.O) (x : LeafQM.B),
    (∃ y ∈ OhatQ, bEmb x * (g : BAQ) = bEmb (a : LeafQM.B) + 3 * y) →
      Φu ((3 : ℂ)⁻¹ • (iotaC x).mulVec ![τ, 1]) = Additive.toMul (P.e.eta a)

/-- **`P` is the object `T(τ, g)`**: an analytic uniformization `Φ : ℂ² → P.A(ℂ)` with kernel
`ι(L_g)(τ, 1)ᵀ`, compatible with `ι` and carrying the level structure of `T(τ, g)` to `η_P`. -/
def MIsAt (P : QML3 ℂ) (τ : UpperHalfPlane) (g : BAQˣ) : Prop :=
  ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ) (vecLat (τ : ℂ) g) Φu ∧
    HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φu ∧ LevelAt P Φu (τ : ℂ) g

/-! ## §2 The two leaves -/

/-- **LEAF `QMReciprocityL3` (Shimura's reciprocity law at CM points, on the QM surfaces with level 3; the main
theorem of complex multiplication for `T(z, g)`).** There are signs `ε = ±1` and `δ` (the conventions) such that:
for every imaginary quadratic `K`, `κ : K → ℂ`, `q : K → B` with CM point `z ∈ ℍ` (`IsCMPoint`, reflex embedding
`κ`, or `κ̄` when `δ = false`), every idele `s` of `K` and `σ ∈ Aut(ℂ)` with `σ = [s, K]` on `K^ab` (`ArtinCondC`,
Tau Ceti's Artin map), every `g ∈ (B ⊗ 𝔸_f)^×` and all `P, P' : QML3 ℂ` with `P'` the base change of `P` along `σ`:
if `P` is `T(z, g)` then `P'` is `T(z, q̂(s_f)^ε g)`.

*Published statements* (locators recalled, UNVERIFIED; no network):
* the main theorem of complex multiplication, adelic form (Shimura–Taniyama; Shimura, *Introduction to the arithmetic
  theory of automorphic functions* (1971), Thm 5.15; Milne, *Introduction to Shimura varieties* (2005), Thm 11.2;
  Milne, *Complex multiplication* notes, Thm 9.x): for `(A, i)` of CM type `(E, Φ)`, `σ ∈ Aut(ℂ/E*)`, `s` an idele of
  `E*` with `art(s) = σ|E*^ab`, and an `E`-linear uniformization `θ : ℂ^Φ/Φ(𝔞) → A(ℂ)`, there is
  `θ' : ℂ^Φ/Φ(N_{Φ*}(s)⁻¹𝔞) → A^σ(ℂ)` with `σθ(x) = θ'(N_{Φ*}(s)⁻¹ x)` for `x ∈ E/𝔞`;
* its form for the QM family: Shimura, Ann. of Math. 85 (1967), §§2-3 (the step from which Main Theorem I's reciprocity
  law is deduced); Deligne, Sém. Bourbaki 389 (1971), §4 (the moduli interpretation is a canonical model).

*Form*: a consequence of the main theorem of CM, not stronger. `T(z, g) = ℂ²/ι(L_g)(z,1)ᵀ` has `H₁ = L_g`, and the
commutative algebra `E = F ⊗ K` (`F ⊂ B` a maximal subfield with `F ⊗ K` a field, acting on `B` by `x ↦ f x q(k)`)
acts on it with `K` acting on `ℂ²` by the scalars `κ(k)` (`IsCMPoint`); its CM type is the set of extensions of `κ`,
with reflex `(K, κ)` and reflex norm `s ↦ q̂(s)` (right multiplication). So `T(z, g)^σ` has `H₁ = L_g q̂(s)^{∓1} =
B ∩ 𝒪̂(q̂(s)^{±1}g)⁻¹ = L_{q̂(s)^{±1} g}`, and the torsion points `[ι(x)(z,1)ᵀ/3]` move by `x ↦ x q̂(s)^{∓1}`, which is
the level structure of `T(z, q̂(s)^{±1}g)`. The signs `ε`, `δ` absorb the normalization of the Artin map and `z`
versus `z̄`. No map `Ψ` and no fine witness occur, so the normalization problem of a "for every `Ψ`" reciprocity
statement does not arise. -/
def QMReciprocityL3 : Prop :=
  ∃ (ε : ℤˣ) (δ : Bool),
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
      IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
    ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
    ∀ (g : BAQˣ) (P P' : QML3 ℂ), IsBaseChangeOf (σ : ℂ →+* ℂ) P P' →
      MIsAt P z g → MIsAt P' z (qHatU q s ^ (ε : ℤ) * g)

/-- **LEAF `ShimuraHolFamilyAb` (Shimura's Main Theorem I, complex part, on a fine witness; shimura-split's
`ShimuraHolFamily` with the abelian-scheme clause list of route A).** Some fine witness `(Y, Φ)` (`R1fpPropsAb`: the
moduli scheme `Y₃` of QM abelian surfaces with level 3) has a holomorphic `τ ↦ y_τ ∈ Y(ℂ)` (`IsHolFamily`) with the
object at `y_τ` equal (by an `ι`-compatible uniformization with kernel `Λ_τ = ι(𝒪)(τ,1)ᵀ`) to `ℂ²/Λ_τ`.

*Published statements* (UNVERIFIED locators): Shimura, Ann. of Math. 85 (1967), Main Theorem I and §§2-3 (the
holomorphic `φ : ℍ → V(ℂ)` with `φ(τ)` the moduli point of `ℂ²/ι(𝒪)(τ,1)ᵀ`); Deligne, Sém. Bourbaki 389 (1971), §4
(the moduli scheme with its complex uniformization). *Form*: the clauses 2 and 3 of gt-rayclass's composite at
`g = 1`, with the representability clause (R) that every moduli leaf of the bundle carries (`gonzalezRotgerX6Ab`,
`deligneComponentsX6PrintedAb`, ...); one family, not every `π : Y → P¹`; the moduli clause describes only the QM
pair. -/
def ShimuraHolFamilyAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ

/-! ## §3 The glue -/

/-- **GLUE `DCRelTransport`**: the object `T(τ, g)` depends only on the class of `(τ, g)` in
`B^×_+ \ (ℍ × (B ⊗ 𝔸_f)^×) / K₃`: if `(τ', g') = (γτ, γ g k)` and `P` is `T(τ', g')`, then `P` is `T(τ, g)`.
True: `L_{γgk} = L_g γ⁻¹` (`k ∈ 𝒪̂^×`), `ι(γ)(τ, 1)ᵀ = j·(γτ, 1)ᵀ` with `j ≠ 0`, so `ι(L_g)(τ,1)ᵀ = j·ι(L_{g'})(τ',1)ᵀ`
and `z ↦ j⁻¹z` carries one uniformization to the other; `k ≡ 1 mod 3` keeps the level structure. -/
def DCRelTransport : Prop :=
  ∀ (P : QML3 ℂ) (τ : UpperHalfPlane) (g : BAQˣ) (τ' : UpperHalfPlane) (g' : BAQˣ),
    DCRel τ g τ' g' → MIsAt P τ' g' → MIsAt P τ g

/-- **GLUE `UnifDetermines`**: two objects that are both `T(τ, g)` are isomorphic. True: `Φ_Q ∘ Φ_P⁻¹` is induced
by the identity of `ℂ²`, hence (GAGA, the textbook leaf `HomLatticeCorr`) by an isomorphism of abelian surfaces,
which commutes with `ι` and carries `η_P` to `η_Q` because the uniformizations do. -/
def UnifDetermines : Prop :=
  ∀ (P Q : QML3 ℂ) (τ : UpperHalfPlane) (g : BAQˣ), MIsAt P τ g → MIsAt Q τ g → M3.mk P = M3.mk Q

/-- **GLUE `ComplexUnifL3`**: every object over `ℂ` is some `T(τ, u)` with `u ∈ 𝒪̂^×`. True: `QMComplexUnif` gives an
`ι`-compatible uniformization by `Λ_τ`; `η(1) = [ι(b)(τ,1)ᵀ/3]` with `b ∈ 𝒪` invertible mod `3` (the kernel of
`η` is `3𝒪`), and `u = ε⁻¹` for a unit `ε ∈ 𝒪^×` with `ε ≡ b mod 3𝒪`. -/
def ComplexUnifL3 : Prop :=
  ∀ P : QML3 ℂ, ∃ (τ : UpperHalfPlane) (u : BAQˣ), u ∈ OhatU ∧ MIsAt P τ u

/-! ## §4 Lemmas -/

/-- `ι(β)(τ, 1)ᵀ ∈ Λ_τ` for `β ∈ 𝒪`. -/
theorem mem_qmLattice_of_inO {τ : ℂ} (hτ : τ.im ≠ 0) {β : LeafQM.B} (hβ : InO β) :
    (iotaC β).mulVec ![τ, 1] ∈ BPAnalytic.QM.qmLattice hτ := by
  obtain ⟨c, rfl⟩ := hβ
  rw [BPAnalytic.QM.qmLattice_eq]
  have e : LeafQM.ofInt c = ∑ i, c i • BPAnalytic.QM.oBasis i := by
    ext <;> simp [LeafQM.ofInt, BPAnalytic.QM.oBasis, Fin.sum_univ_four] <;> ring
  rw [e, map_sum, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_zsmul, Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- `L_u = 𝒪` for `u ∈ 𝒪̂^×`, so `ι(L_u)(τ, 1)ᵀ = Λ_τ`. -/
theorem vecLat_unit {u : BAQˣ} (hu : u ∈ OhatU) (τ : UpperHalfPlane) :
    vecLat (τ : ℂ) u = BPAnalytic.QM.qmLattice τ.im_pos.ne' := by
  ext v
  rw [mem_vecLat]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxO : bEmb x ∈ OhatQ := by
      have e : bEmb x = bEmb x * (u : BAQ) * ((u⁻¹ : BAQˣ) : BAQ) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      rw [e]; exact OhatQ_mul hx hu.2
    exact mem_qmLattice_of_inO τ.im_pos.ne' (inO_of_bEmb_mem hxO)
  · intro hv
    obtain ⟨β, hβ, rfl⟩ := exists_of_mem_qmLattice τ.im_pos.ne' hv
    exact ⟨β, OhatQ_mul (bEmb_mem_of_inO hβ) hu.1, rfl⟩

/-- **The moduli clause at units** (`ModuliAtUnits`' form): `T(τ, u)` is `ℂ²/Λ_τ` as a QM pair. -/
theorem unif_of_mIsAt_unit {P : QML3 ℂ} {τ : UpperHalfPlane} {u : BAQˣ} (hu : u ∈ OhatU)
    (h : MIsAt P τ u) :
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φu := by
  obtain ⟨Φu, hU, hI, -⟩ := h
  exact ⟨Φu, vecLat_unit hu τ ▸ hU, hI⟩

/-! ## §5 The ray-class argument on objects -/

/-- **The core argument, on objects.** Let `(Y, Φ)` satisfy `R1fpPropsAb`, `y` a `ℚ̄`-point, `Q` the object at
`ιC^* y`, and suppose `Q` is `T(τ, u)` with `u ∈ 𝒪̂^×`, `τ` the CM point of `q : k → B` (`q(𝒪_k) ⊆ 𝒪`). Then `ℚ(y)`
embeds into the ray class field of `k` of conductor `3`. (rayclass-cft's `embed_core`, with the map `Ψ` replaced by
the objects `T(τ, g)`.) -/
theorem embed_core_obj {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (hR1 : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (hS : QMReciprocityL3) (hT : DCRelTransport)
    (hD : UnifDetermines)
    (k : Type) [Field k] [NumberField k] [IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (hI : QHatIntegral k) (y : fieldPt Qbar ⟶ Y) (Q : QML3 ℂ)
    (hQ : Φ ℂ (fieldMap ιC ≫ y) = M3.mk Q) (τ : UpperHalfPlane) (u : BAQˣ) (hu : u ∈ OhatU)
    (hM : MIsAt Q τ u) (q : k →ₐ[ℚ] LeafQM.B) (κ₀ : k →+* ℂ) (hqO : ∀ x : 𝓞 k, InO (q x))
    (hcmτ : IsCMPoint q κ₀ τ) :
    Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (ShimuraGlue.Ray.mod3 k)) := by
  obtain ⟨ε, δ, hrec⟩ := hS
  obtain ⟨-, -, -, hnat, -, -⟩ := hR1
  -- (c) the reflex embedding in the convention `δ`
  let κ : k →+* ℂ := if δ then κ₀ else (starRingEnd ℂ).comp κ₀
  have hκκ : (if δ then κ else (starRingEnd ℂ).comp κ) = κ₀ := by
    cases δ <;> ext a <;> simp [κ]
  -- (d) the ray class field `L` and an embedding `j : L → ℚ̄` over `κ`
  let L := rayClassField (ShimuraGlue.Ray.mod3 k)
  letI : Algebra k ℂ := κ.toAlgebra
  let j' : L →ₐ[k] ℂ := IsAlgClosed.lift
  have hj' : (j' : L →+* ℂ).comp (algebraMap k L) = κ := by
    ext a; exact j'.commutes a
  obtain ⟨j, hj⟩ := exists_lift_ringHom (L := L) (j' : L →+* ℂ)
  let jA : L →ₐ[ℚ] Qbar := j.toRatAlgHom
  let F : IntermediateField ℚ Qbar := jA.fieldRange
  -- (e) every `σ ∈ Gal(ℚ̄/F)` fixes `y`
  have hfix : ∀ σ ∈ F.fixingSubgroup,
      Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y.left = y.left := by
    intro σ hσ
    obtain ⟨σC, hσC⟩ := T5Glue.exists_ringEquiv_extend (ιC : Qbar →+* ℂ) σ.toRingEquiv
    have hσC' : ∀ a, σC (ιC a) = ιC (σ a) := fun a => hσC a
    have hσF : ∀ x : L, σ (j x) = j x := fun x =>
      (IntermediateField.mem_fixingSubgroup_iff F σ).1 hσ (j x) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    have hσL : ∀ x : L, σC (j' x) = j' x := fun x => by
      rw [show j' x = (j' : L →+* ℂ) x from rfl, ← hj, hσC', hσF]
    have hσκ : ∀ a : k, σC (κ a) = κ a := fun a => by
      have e : (j' : L →+* ℂ) (algebraMap k L a) = κ a := congrArg (fun f => f a) hj'
      have := hσL (algebraMap k L a)
      rw [show j' (algebraMap k L a) = (j' : L →+* ℂ) (algebraMap k L a) from rfl, e] at this
      exact this
    obtain ⟨s, hs⟩ := exists_artinCondC κ σC hσκ
    -- the Artin symbol of `s` is trivial on `L`
    have hart : ideleClassArtinMap k L (QuotientGroup.mk s) = 1 := by
      refine AlgEquiv.ext fun x => ?_
      apply (j' : L →+* ℂ).injective
      rw [AlgEquiv.one_apply, ← hs L (j' : L →+* ℂ) hj' x]
      exact hσL x
    have hray : ((s : IdeleGroup (𝓞 k) k) : IdeleClassGroup (𝓞 k) k) ∈
        raySubgroup (ShimuraGlue.Ray.mod3 k) := by
      have hker : (QuotientGroup.mk s : IdeleClassGroup (𝓞 k) k) ∈ (ideleClassArtinMap k L).ker := hart
      rw [ker_ideleClassArtinMap, range_ideleClassNormMap_rayClassField] at hker
      exact hker
    rw [mk_mem_raySubgroup_iff] at hray
    obtain ⟨s₀, hs₀, z, ⟨c, rfl⟩, hsz⟩ := Subgroup.mem_sup.1 hray
    -- the object at `σ(ιC^* y)`, and Shimura's reciprocity law on it
    obtain ⟨Q', hQ', hbc⟩ := hnat ℂ ℂ (σC : ℂ →+* ℂ).toRatAlgHom (fieldMap ιC ≫ y) Q hQ
    have h4 : MIsAt Q' τ (qHatU q s ^ (ε : ℤ) * u) :=
      hrec k hk κ q τ (by rw [hκκ]; exact hcmτ) σC s hs u Q Q' hbc hM
    let c' : kˣ := c ^ (ε : ℤ)
    have hsε : s ^ (ε : ℤ) = IdeleGroup.unitEmbedding (𝓞 k) k c' * s₀ ^ (ε : ℤ) := by
      rw [← hsz, mul_zpow, map_zpow, mul_comm]
    have hX : qHatU q s ^ (ε : ℤ) * u = qHatU q (IdeleGroup.unitEmbedding (𝓞 k) k c') * u *
        (u⁻¹ * qHatU q (s₀ ^ (ε : ℤ)) * u) := by
      rw [← map_zpow, hsε, map_mul]; group
    have hk3 : u⁻¹ * qHatU q (s₀ ^ (ε : ℤ)) * u ∈ K3Q :=
      conj_mem_K3Q hu (hI q hqO _ (Subgroup.zpow_mem _ hs₀ _))
    have hdc : DCRel τ u τ (qHatU q s ^ (ε : ℤ) * u) := by
      refine dcRel_fix (nrd_pos_of_cm q κ₀ τ hcmτ c') τ (hcmτ c') u _ _ hk3 ?_
      rw [hX, Units.val_mul, Units.val_mul, qHatU_unitEmbedding]
    have h5 : MIsAt Q' τ u := hT Q' τ u τ _ hdc h4
    have h6 : M3.mk Q' = M3.mk Q := hD Q' Q τ u h5 hM
    have hΨ : galPt σC (fieldMap ιC ≫ y) = fieldMap ιC ≫ y := by
      apply (Φ ℂ).injective
      show Φ ℂ (fieldMap (σC : ℂ →+* ℂ).toRatAlgHom ≫ (fieldMap ιC ≫ y)) = _
      rw [hQ', h6, hQ]
    rw [galPt_fieldMap y σ σC hσC'] at hΨ
    exact congrArg CommaMorphism.left (fieldMap_ιC_inj hΨ)
  -- (f) `ℚ(y) ⊆ F ≅ L`
  have hle : residueImage (X := Y.left) y.left ≤ F := residueImage_le y.left F hfix
  exact ⟨((AlgEquiv.ofInjectiveField jA).symm.toAlgHom.comp
    (IntermediateField.inclusion hle)).toRingHom⟩

/-- The CM data at a representative: from `MIsAt Q τ u` and the CM of the object `P` at `y`. -/
theorem cm_at {P : QML3 Qbar} {Q : QML3 ℂ} (hbc : IsBaseChangeOf (ιC : Qbar →+* ℂ) P Q)
    {τ : UpperHalfPlane} {u : BAQˣ} (hu : u ∈ OhatU) (hM : MIsAt Q τ u) :
    ∃ Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu ∧
      (HasCM4 P.q → HasCM4 Q.q) ∧ (HasCM3 P.q → HasCM3 Q.q) ∧ (HasCM24 P.q → HasCM24 Q.q) := by
  obtain ⟨Φu, hun, hio⟩ := unif_of_mIsAt_unit hu hM
  obtain ⟨b4, b3, b24⟩ := cmBaseChange (ιC : Qbar →+* ℂ) P Q hbc
  exact ⟨Φu, hun, hio, b4, b3, b24⟩

/-! ## §6 The two fields -/

/-- **`RayClassCMAb` from the two leaves and the glue** (no map `Ψ`, no class-number argument: `ComplexUnifL3`
gives a representative with `u ∈ 𝒪̂^×` directly). The witness is the one of `ShimuraHolFamilyAb` (any fine witness
would do: the proof reads only `R1fpPropsAb`'s naturality clause and `Φ`). -/
theorem rayClassCMAb_of_split (hH : ShimuraHolFamilyAb) (hS : QMReciprocityL3) (hT : DCRelTransport)
    (hD : UnifDetermines) (hC : ComplexUnifL3) (hHL : ZInQ.HomUnify.HomLinearLift) :
    ShimuraGlue.Ray.RayClassCMAb := by
  obtain ⟨Y, Φ, hAb, -⟩ := hH
  have hA : CMAnalytic := cmAnalytic_of hHL
  refine ⟨Y, Φ, hAb, fun y P hP => ?_⟩
  have hnat := hAb.2.2.2.1
  obtain ⟨Q, hQ, hbc⟩ := hnat Qbar ℂ ιC y P hP
  obtain ⟨τ, u, hu, hM⟩ := hC Q
  obtain ⟨Φu, hun, hio, c4, c3, c24⟩ := cm_at hbc hu hM
  obtain ⟨ρ, hρ⟩ := hA τ Q Φu hun hio
  refine ⟨fun h4 => ?_, fun h3 => ?_, fun h24 => ?_⟩
  · obtain ⟨φ, hφ, hφ2⟩ := c4 h4
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    obtain ⟨q, κ₀, hqO, hcm⟩ := cm_data K4 finrank_K4 (not_rat_of_disc y4_rel (by norm_num)) y4_rel
      ringOfIntegersGen_K4 τ _ hβO (by
        have := com_rel ρ hφ (P0 := 0) (Q0 := 1) (by rw [hφ2]; simp)
        simpa using this) lam heig
    exact embed_core_obj hAb hS hT hD K4 finrank_K4 (qHatIntegral K4) y Q hQ τ u hu hM q κ₀ hqO hcm
  · obtain ⟨φ, hφ, hφ2⟩ := c3 h3
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    obtain ⟨q, κ₀, hqO, hcm⟩ := cm_data K3 finrank_K3 (not_rat_of_disc y3_rel (by norm_num)) y3_rel
      ringOfIntegersGen_K3 τ _ hβO (by
        have := com_rel ρ hφ (P0 := -1) (Q0 := 1) (by rw [← hφ2]; simp; abel)
        simpa using this) lam heig
    exact embed_core_obj hAb hS hT hD K3 finrank_K3 (qHatIntegral K3) y Q hQ τ u hu hM q κ₀ hqO hcm
  · obtain ⟨φ, hφ, hφ2⟩ := c24 h24
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    obtain ⟨q, κ₀, hqO, hcm⟩ := cm_data K24 finrank_K24 (not_rat_of_disc y24_rel (by norm_num)) y24_rel
      ringOfIntegersGen_K24 τ _ hβO (by
        have := com_rel ρ hφ (P0 := 0) (Q0 := 6) (by rw [hφ2]; simp)
        simpa using this) lam heig
    exact embed_core_obj hAb hS hT hD K24 finrank_K24 (qHatIntegral K24) y Q hQ τ u hu hM q κ₀ hqO hcm

/-- **`ShimuraFamilyAb` from `ShimuraHolFamilyAb`** (shimura-split's `isR1bFamily_of_hol` for every `π`). -/
theorem shimuraFamilyAb_of_hol (hH : ShimuraHolFamilyAb) : HDec.QMSplit.Moduli.ShimuraFamilyAb := by
  obtain ⟨Y, Φ, h1, yτ, hy⟩ := hH
  exact ⟨Y, Φ, h1, fun π => ⟨yτ, HDec.HSyn.G0Split.FibreQM.isR1bFamily_of_hol hy π⟩⟩

end ShimuraSplit2

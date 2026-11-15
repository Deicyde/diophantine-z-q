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
`P : QML3 ℂ` is (`ι`- and level-compatibly uniformized by) `T(τ, g)`. The results:

* `rayClassCMAb_of_leaves2 : DeligneComponentsX6PrintedAb → QMReciprocityL3 → UniformizationLeafAll →
  GAGAMorphism → MumfordTorsionAlgClosed → RayClassCMAb` (only the fine witness (R) of the first is used);
* `shimuraFamilyAb_of_leaves2 : DeligneComponentsX6PrintedAb → ShimuraHolModAll → ShimuraFamilyAb`.

New leaves:
* **`QMReciprocityL3`** (§2): if `P` is `T(z, g)` at a CM point `z` and `P'` is its conjugate by `σ = [s, K]`, then
  `P'` is `T(z, q̂(s)^ε g)`. No `Ψ`, no witness, hence no normalization problem. A consequence of the main theorem
  of complex multiplication for the CM algebra `F ⊗ K` acting on `H₁ = L_g`.
* **`ShimuraHolModAll`** (§12): Shimura's Main Theorem I, complex part, for every fine witness (no existence claim);
  equivalent, given one fine witness, to the `∃` form `ShimuraHolFamilyAb` (§2) (`shimuraHolModAll_of_hol`,
  `shimuraHolFamilyAb_of_all`).

Glue, all proved: `DCRelTransport` (§7), `UnifDetermines` (§8, from `HomLatticeCorr`), `ComplexUnifL3` (§9, from the
chain's `QMComplexUnif`, with a 72-entry table of units of `𝒪` checked by `decide`), `vecLat_unit` (§4), and the
ray-class argument on objects `embed_core_obj` (§5).
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

/-- **The level structure of `T(τ, g)`**: for every `a ∈ 𝒪`, `η(a) = Φ(ι(x)(τ, 1)ᵀ / 3)` for some `x ∈ B` with
`x g ∈ a + 3𝒪̂` (`x ≡ a g⁻¹ mod 3 L̂_g`; all such `x` give the same point, since two of them differ by `3 L_g`). -/
def LevelAt (P : QML3 ℂ) (Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ)) (τ : ℂ) (g : BAQˣ) : Prop :=
  ∀ a : LeafQM.O, ∃ x : LeafQM.B,
    (∃ y ∈ OhatQ, bEmb x * (g : BAQ) = bEmb (a : LeafQM.B) + 3 * y) ∧
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

/-- **`RayClassCMAb` from one fine witness, the leaf `QMReciprocityL3` and the glue** (no map `Ψ`, no class-number
argument: `ComplexUnifL3` gives a representative with `u ∈ 𝒪̂^×` directly; the proof reads only `R1fpPropsAb`'s
naturality clause and `Φ`, so any fine witness will do). -/
theorem rayClassCMAb_of_witness (hW : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y),
      LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (hS : QMReciprocityL3) (hT : DCRelTransport)
    (hD : UnifDetermines) (hC : ComplexUnifL3) (hHL : ZInQ.HomUnify.HomLinearLift) :
    ShimuraGlue.Ray.RayClassCMAb := by
  obtain ⟨Y, Φ, hAb⟩ := hW
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

/-- **`RayClassCMAb` from the two leaves and the glue**, with the witness of `ShimuraHolFamilyAb`. -/
theorem rayClassCMAb_of_split (hH : ShimuraHolFamilyAb) (hS : QMReciprocityL3) (hT : DCRelTransport)
    (hD : UnifDetermines) (hC : ComplexUnifL3) (hHL : ZInQ.HomUnify.HomLinearLift) :
    ShimuraGlue.Ray.RayClassCMAb := by
  obtain ⟨Y, Φ, hAb, -⟩ := hH
  exact rayClassCMAb_of_witness ⟨Y, Φ, hAb⟩ hS hT hD hC hHL

/-- **`ShimuraFamilyAb` from `ShimuraHolFamilyAb`** (shimura-split's `isR1bFamily_of_hol` for every `π`). -/
theorem shimuraFamilyAb_of_hol (hH : ShimuraHolFamilyAb) : HDec.QMSplit.Moduli.ShimuraFamilyAb := by
  obtain ⟨Y, Φ, h1, yτ, hy⟩ := hH
  exact ⟨Y, Φ, h1, fun π => ⟨yτ, HDec.HSyn.G0Split.FibreQM.isR1bFamily_of_hol hy π⟩⟩

/-! ## §7 Proof of `DCRelTransport` -/

/-- The scaling `z ↦ j z` of `ℂ²`. -/
def smulEquiv (j : ℂ) (hj : j ≠ 0) : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun z := j • z
  invFun z := j⁻¹ • z
  map_add' z w := smul_add j z w
  map_smul' c z := smul_comm j c z
  left_inv z := by simp [smul_smul, inv_mul_cancel₀ hj]
  right_inv z := by simp [smul_smul, mul_inv_cancel₀ hj]

/-- `ι(γ)(τ, 1)ᵀ = j(γ, τ)·(γτ, 1)ᵀ` for `nrd γ > 0`. -/
theorem iotaC_mulVec_eq (γ : LeafQM.B) (M : GL (Fin 2) ℝ)
    (hM : (M : Matrix (Fin 2) (Fin 2) ℝ) = BPAnalytic.QM.iota γ)
    (hpos : 0 < ShimuraGlue.nrdQ ℚ γ) (τ : UpperHalfPlane) :
    (iotaC γ).mulVec ![(τ : ℂ), 1] =
      UpperHalfPlane.denom M τ • ![((M • τ : UpperHalfPlane) : ℂ), 1] := by
  have hdet : 0 < (M : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hM, det_iota]; exact_mod_cast hpos
  rw [UpperHalfPlane.coe_smul_of_det_pos
    (by simpa [Matrix.GeneralLinearGroup.val_det_apply] using hdet)]
  have hd := UpperHalfPlane.denom_ne_zero M τ
  ext i; fin_cases i
  · simp [iotaC_apply, ← hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [mul_div_cancel₀ _ hd]
    simp [UpperHalfPlane.num]
  · simp [iotaC_apply, ← hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom]

/-- `k⁻¹ = 1 − 3 k⁻¹ y₀` for `k = 1 + 3 y₀`. -/
theorem inv_eq_of_K3 {k : BAQˣ} {y₀ : BAQ} (hky : (k : BAQ) = 1 + 3 * y₀) :
    ((k⁻¹ : BAQˣ) : BAQ) = 1 - 3 * (((k⁻¹ : BAQˣ) : BAQ) * y₀) := by
  have h1 : ((k⁻¹ : BAQˣ) : BAQ) * (k : BAQ) = 1 := Units.inv_mul k
  rw [hky] at h1
  have h3 : ((k⁻¹ : BAQˣ) : BAQ) * 3 = 3 * ((k⁻¹ : BAQˣ) : BAQ) := (Commute.ofNat_right _ 3).eq
  calc ((k⁻¹ : BAQˣ) : BAQ) = ((k⁻¹ : BAQˣ) : BAQ) * (1 + 3 * y₀) - (((k⁻¹ : BAQˣ) : BAQ) * 3) * y₀ := by
        noncomm_ring
    _ = 1 - 3 * (((k⁻¹ : BAQˣ) : BAQ) * y₀) := by rw [h1, h3]; noncomm_ring

theorem dcRelTransport_proof : DCRelTransport := by
  rintro P τ g τ' g' ⟨γ, hγ, ⟨M, hM, hMτ⟩, k, hk, hg'⟩ ⟨Φu', hU', hI', hL'⟩
  obtain ⟨hk1, hk2, y₀, hy₀, hky⟩ := hk
  have hj : UpperHalfPlane.denom M τ ≠ 0 := UpperHalfPlane.denom_ne_zero M τ
  set j := UpperHalfPlane.denom M τ with hjdef
  have hγb : γ * binv γ = 1 := mul_binv hγ.ne'
  have hbγ : binv γ * γ = 1 := binv_mul hγ.ne'
  have hvec : ∀ x : LeafQM.B, (iotaC x).mulVec ![(τ : ℂ), 1] =
      j • (iotaC (x * binv γ)).mulVec ![(τ' : ℂ), 1] := by
    intro x
    have e := iotaC_mulVec_eq γ M hM hγ τ
    rw [hMτ] at e
    rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, ← map_mul, mul_assoc, hbγ, mul_one]
  have hmem : ∀ x : LeafQM.B, bEmb (x * binv γ) * (g' : BAQ) = bEmb x * (g : BAQ) * (k : BAQ) := by
    intro x
    rw [hg', map_mul]
    calc bEmb x * bEmb (binv γ) * (bEmb γ * (g : BAQ) * (k : BAQ))
        = bEmb x * (bEmb (binv γ) * bEmb γ) * (g : BAQ) * (k : BAQ) := by noncomm_ring
      _ = bEmb x * (g : BAQ) * (k : BAQ) := by rw [← map_mul, hbγ, map_one, mul_one]
  have hback : ∀ x' : LeafQM.B, bEmb (x' * γ) * (g : BAQ) =
      bEmb x' * (g' : BAQ) * ((k⁻¹ : BAQˣ) : BAQ) := by
    intro x'
    have e := hmem (x' * γ)
    rw [mul_assoc x' γ, hγb, mul_one] at e
    rw [e, mul_assoc, Units.mul_inv, mul_one]
  have hx'γ : ∀ x' : LeafQM.B, x' * γ * binv γ = x' := fun x' => by rw [mul_assoc, hγb, mul_one]
  let F := smulEquiv j hj
  have hFs : ∀ z, F.symm z = j⁻¹ • z := fun z => rfl
  refine ⟨fun z => Φu' (F.symm z), ?_, ?_, ?_⟩
  · have hlat : (vecLat (τ' : ℂ) g').map (F.toLinearMap.restrictScalars ℤ) = vecLat (τ : ℂ) g := by
      ext v
      rw [Submodule.mem_map, mem_vecLat]
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x', hx', rfl⟩ := mem_vecLat.1 hw
        refine ⟨x' * γ, ?_, ?_⟩
        · rw [hback]; exact OhatQ_mul hx' hk2
        · rw [hvec, hx'γ]; rfl
      · rintro ⟨x, hx, rfl⟩
        refine ⟨(iotaC (x * binv γ)).mulVec ![(τ' : ℂ), 1], mem_vecLat.2 ⟨x * binv γ, ?_, rfl⟩, ?_⟩
        · rw [hmem]; exact OhatQ_mul hx hk1
        · rw [hvec x]; rfl
    rw [← hlat]
    exact HDec.HSyn.G0Split.FibreQM.isUniformization_comp hU' F
  · intro a z
    show Φu' (F.symm _) = Φu' (F.symm z) ≫ _
    rw [hFs, hFs, ← Matrix.mulVec_smul]
    exact hI' a _
  · intro a
    obtain ⟨x', ⟨y', hy', hx'⟩, hΦ'⟩ := hL' a
    have hyO : y' * ((k⁻¹ : BAQˣ) : BAQ) - bEmb (a : LeafQM.B) * (((k⁻¹ : BAQˣ) : BAQ) * y₀) ∈ OhatQ := by
      rw [sub_eq_add_neg]
      exact OhatQ_add (OhatQ_mul hy' hk2)
        (OhatQ_neg (OhatQ_mul (bEmb_mem_of_inO a.2) (OhatQ_mul hk2 hy₀)))
    refine ⟨x' * γ, ⟨_, hyO, ?_⟩, ?_⟩
    · rw [hback, hx', inv_eq_of_K3 hky]
      have h3 : bEmb (a : LeafQM.B) * 3 = 3 * bEmb (a : LeafQM.B) := (Commute.ofNat_right _ 3).eq
      have h3' : ∀ w : BAQ, w * 3 = 3 * w := fun w => (Commute.ofNat_right _ 3).eq
      calc (bEmb (a : LeafQM.B) + 3 * y') * (1 - 3 * (((k⁻¹ : BAQˣ) : BAQ) * y₀))
          = bEmb (a : LeafQM.B) + 3 * (y' * (1 - 3 * (((k⁻¹ : BAQˣ) : BAQ) * y₀)))
            - (bEmb (a : LeafQM.B) * 3) * (((k⁻¹ : BAQˣ) : BAQ) * y₀) := by noncomm_ring
        _ = _ := by
          rw [h3, ← inv_eq_of_K3 hky]
          noncomm_ring
    · show Φu' (F.symm _) = _
      rw [hFs, hvec, hx'γ, smul_comm (3 : ℂ)⁻¹ j, smul_smul, inv_mul_cancel₀ hj, one_smul]
      exact hΦ'

/-! ## §8 Proof of `UnifDetermines` (from the textbook leaf `HomLatticeCorr`) -/

theorem qmMat_eq (a : LeafQM.O) : HDec.HSyn.G0Split.FibreQM.qmMat a = iotaC (a : LeafQM.B) := rfl

theorem mulVec_mem_vecLat {τ : ℂ} {g : BAQˣ} (a : LeafQM.O) {v : Fin 2 → ℂ} (hv : v ∈ vecLat τ g) :
    (iotaC (a : LeafQM.B)).mulVec v ∈ vecLat τ g := by
  obtain ⟨x, hx, rfl⟩ := mem_vecLat.1 hv
  refine mem_vecLat.2 ⟨a * x, ?_, ?_⟩
  · rw [map_mul, mul_assoc]; exact OhatQ_mul (bEmb_mem_of_inO a.2) hx
  · rw [map_mul, ← Matrix.mulVec_mulVec]

theorem iotaC_smul_mulVec (r : ℚ) (x : LeafQM.B) (w : Fin 2 → ℂ) :
    (iotaC (r • x)).mulVec w = (r : ℂ) • (iotaC x).mulVec w := by
  rw [map_smul]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Rat.smul_def] <;> ring

theorem three_mul_eq_smul (z : BAQ) : (3 : BAQ) * z = (3 : ℚ) • z := by
  rw [Algebra.smul_def, map_ofNat]

theorem three_mul_eq_smulB (z : LeafQM.B) : (3 : LeafQM.B) * z = (3 : ℚ) • z := by
  rw [Algebra.smul_def, map_ofNat]

theorem three_mul_eq_smulB' (z : LeafQM.B) : z * (3 : LeafQM.B) = (3 : ℚ) • z := by
  rw [(Commute.ofNat_right z 3).eq, three_mul_eq_smulB]

open scoped MonObj in
/-- Two representatives of the level structure give the same point. -/
theorem level_rep_eq {P : QML3 ℂ} {Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ)} {τ : ℂ} {g : BAQˣ}
    (hU : IsUniformization (RingHom.id ℂ) (vecLat τ g) Φu) {a : LeafQM.B} {x x'' : LeafQM.B} {y y'' : BAQ}
    (hy : y ∈ OhatQ) (hy'' : y'' ∈ OhatQ) (hx : bEmb x * (g : BAQ) = bEmb a + 3 * y)
    (hx'' : bEmb x'' * (g : BAQ) = bEmb a + 3 * y'') :
    Φu ((3 : ℂ)⁻¹ • (iotaC x).mulVec ![τ, 1]) = Φu ((3 : ℂ)⁻¹ • (iotaC x'').mulVec ![τ, 1]) := by
  set c : LeafQM.B := (1 / 3 : ℚ) • (x - x'') with hc
  have hcm : (iotaC c).mulVec ![τ, 1] =
      (3 : ℂ)⁻¹ • (iotaC x).mulVec ![τ, 1] - (3 : ℂ)⁻¹ • (iotaC x'').mulVec ![τ, 1] := by
    rw [hc, iotaC_smul_mulVec, map_sub, Matrix.sub_mulVec, smul_sub]
    norm_num
  have hcL : (iotaC c).mulVec ![τ, 1] ∈ vecLat τ g := by
    refine mem_vecLat.2 ⟨c, ?_, rfl⟩
    have e : bEmb c * (g : BAQ) = y - y'' := by
      rw [hc, map_smul, smul_mul_assoc, map_sub, sub_mul, hx, hx'', three_mul_eq_smul,
        three_mul_eq_smul, add_sub_add_left_eq_sub, ← smul_sub, smul_smul]
      norm_num
    rw [e, sub_eq_add_neg]
    exact OhatQ_add hy (OhatQ_neg hy'')
  have h1 := (hU.2.1 _).2 hcL
  have e2 := hU.1 ((3 : ℂ)⁻¹ • (iotaC x'').mulVec ![τ, 1]) ((iotaC c).mulVec ![τ, 1])
  rw [h1, _root_.mul_one, hcm, add_sub_cancel] at e2
  exact e2

theorem unifDetermines_of (hC : ZInQ.HomUnify.HomLatticeCorr) : UnifDetermines := by
  rintro P Q τ g ⟨ΦP, hUP, hIP, hLP⟩ ⟨ΦQ, hUQ, hIQ, hLQ⟩
  have h2 := hC.2
  have hid : ∀ z ∈ vecLat (τ : ℂ) g, (LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈ vecLat (τ : ℂ) g :=
    fun z hz => hz
  obtain ⟨f, hf, -⟩ := h2 P.A Q.A 2 2 _ _ ΦP ΦQ (dim_two P) (dim_two Q) hUP hUQ LinearMap.id hid
  obtain ⟨f', hf', -⟩ := h2 Q.A P.A 2 2 _ _ ΦQ ΦP (dim_two Q) (dim_two P) hUQ hUP LinearMap.id hid
  have hPP := h2 P.A P.A 2 2 _ _ ΦP ΦP (dim_two P) (dim_two P) hUP hUP LinearMap.id hid
  have hQQ := h2 Q.A Q.A 2 2 _ _ ΦQ ΦQ (dim_two Q) (dim_two Q) hUQ hUQ LinearMap.id hid
  have hf0 : ∀ z, ΦQ z = ΦP z ≫ f.hom := hf
  have hf0' : ∀ z, ΦP z = ΦQ z ≫ f'.hom := hf'
  apply Quotient.sound
  refine ⟨⟨f, f', ?_, ?_, fun a => ?_, fun a => ?_⟩⟩
  · have := hPP.unique (y₁ := PkgI3.AbVar.Hom.mk' (f.hom ≫ f'.hom)) (y₂ := PkgI3.AbVar.Hom.mk' (𝟙 _))
      (fun z => by
        show ΦP z = ΦP z ≫ (f.hom ≫ f'.hom)
        rw [← Category.assoc, ← hf0, ← hf0'])
      (fun z => by
        show ΦP z = ΦP z ≫ 𝟙 _
        rw [Category.comp_id])
    exact congrArg PkgI3.AbVar.Hom.hom this
  · have := hQQ.unique (y₁ := PkgI3.AbVar.Hom.mk' (f'.hom ≫ f.hom)) (y₂ := PkgI3.AbVar.Hom.mk' (𝟙 _))
      (fun z => by
        show ΦQ z = ΦQ z ≫ (f'.hom ≫ f.hom)
        rw [← Category.assoc, ← hf0', ← hf0])
      (fun z => by
        show ΦQ z = ΦQ z ≫ 𝟙 _
        rw [Category.comp_id])
    exact congrArg PkgI3.AbVar.Hom.hom this
  · have hMa := h2 P.A Q.A 2 2 _ _ ΦP ΦQ (dim_two P) (dim_two Q) hUP hUQ
      (Matrix.mulVecLin (HDec.HSyn.G0Split.FibreQM.qmMat a))
      (fun z hz => by
        show (HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec z ∈ _
        rw [qmMat_eq]; exact mulVec_mem_vecLat a hz)
    have := hMa.unique (y₁ := PkgI3.AbVar.Hom.mk' ((P.q.iota a).hom ≫ f.hom))
      (y₂ := PkgI3.AbVar.Hom.mk' (f.hom ≫ (Q.q.iota a).hom))
      (fun z => by
        show ΦQ ((HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec z) = ΦP z ≫ ((P.q.iota a).hom ≫ f.hom)
        rw [← Category.assoc, ← hIP a z, ← hf0])
      (fun z => by
        show ΦQ ((HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec z) = ΦP z ≫ (f.hom ≫ (Q.q.iota a).hom)
        rw [← Category.assoc, ← hf0, hIQ a z])
    exact congrArg PkgI3.AbVar.Hom.hom this
  · obtain ⟨x, ⟨y, hy, hx⟩, hΦx⟩ := hLP a
    obtain ⟨x'', ⟨y'', hy'', hx''⟩, hΦx''⟩ := hLQ a
    have e : Additive.toMul (P.e.eta a) ≫ f.hom = Additive.toMul (Q.e.eta a) := by
      have h1 := (hf0 _).symm.trans (level_rep_eq hUQ hy hy'' hx hx'')
      rw [hΦx, hΦx''] at h1
      exact h1
    rw [e]
    rfl

/-! ## §9 Proof of `ComplexUnifL3` (from `QMComplexUnif`, proved in the chain from textbook leaves)

The level structure `η` of an object uniformized by `Λ_τ` is `η(a) = [ι(ab)(τ,1)ᵀ/3]` for some `b ∈ 𝒪` with
`nrd b ≢ 0 mod 3` (the kernel of `η` is `3𝒪`). The units of `𝒪` (reduced norm `±1`) reach every class of
`(𝒪/3𝒪)^×` (72 classes; `𝒪 ⊗ ℤ₃` is the maximal order of the division algebra `B ⊗ ℚ₃`): the table `tabU`, with
inverses `tabV`, was found by `scratch/shimura-split2/py/units.py` and is checked by `decide`. With `ε ≡ b`,
`u = ε⁻¹ ∈ 𝒪^× ⊆ 𝒪̂^×` gives `L_u = 𝒪` and the level structure of `T(τ, u)`. -/

/-- `nrd(ofInt m)`. -/
def nrdZ (m : Fin 4 → ℤ) : ℤ :=
  m 0 ^ 2 + m 0 * m 2 - 2 * m 1 ^ 2 - 2 * m 1 * m 3 + m 2 ^ 2 - 2 * m 3 ^ 2

theorem star_mul_ofInt (m : Fin 4 → ℤ) :
    star (LeafQM.ofInt m) * LeafQM.ofInt m = ((nrdZ m : ℤ) : ℚ) • (1 : LeafQM.B) := by
  ext <;> simp [LeafQM.ofInt, nrdZ] <;> ring

/-- Units of `𝒪` (coordinates of `ofInt`) indexed by their classes mod `3` (`0` at non-units). -/
def tabU : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 4 → ℤ :=
  ![![![![![0, 0, 0, 0], ![-3, 0, 0, -2], ![-3, 0, 0, 2]], ![![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 1, -1]], ![![0, 0, -1, 0], ![0, 0, -1, 1], ![0, 0, -1, -1]]],
    ![![![-3, -2, 0, 0], ![0, 0, 0, 0], ![-3, -2, 0, 2]], ![![0, 1, 1, 0], ![-3, 1, 1, 1], ![0, 1, 1, -1]], ![![0, 1, -1, 0], ![3, 1, -1, 1], ![0, 1, -1, -1]]],
    ![![![-3, 2, 0, 0], ![-3, 2, 0, -2], ![0, 0, 0, 0]], ![![0, -1, 1, 0], ![0, -1, 1, 1], ![-3, -1, 1, -1]], ![![0, -1, -1, 0], ![0, -1, -1, 1], ![3, -1, -1, -1]]]],
  ![![![![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 0, -1]], ![![0, 0, 0, 0], ![1, 0, 1, 1], ![1, 0, 1, -1]], ![![1, 0, -1, 0], ![1, 0, -1, 1], ![1, 0, -1, -1]]],
    ![![![1, 1, 0, 0], ![1, 1, -3, 1], ![1, 1, 0, -1]], ![![1, 1, 1, 0], ![0, 0, 0, 0], ![1, 1, 1, -1]], ![![1, 1, -1, 0], ![-2, 1, -1, 1], ![1, 1, -1, -1]]],
    ![![![1, -1, 0, 0], ![1, -1, 0, 1], ![1, -1, -3, -1]], ![![1, -1, 1, 0], ![1, -1, 1, 1], ![0, 0, 0, 0]], ![![1, -1, -1, 0], ![1, -1, -1, 1], ![-2, -1, -1, -1]]]],
  ![![![![-1, 0, 0, 0], ![-1, 0, 0, 1], ![-1, 0, 0, -1]], ![![-1, 0, 1, 0], ![-1, 0, 1, 1], ![-1, 0, 1, -1]], ![![0, 0, 0, 0], ![-1, 0, -1, 1], ![-1, 0, -1, -1]]],
    ![![![-1, 1, 0, 0], ![-1, 1, 3, 1], ![-1, 1, 0, -1]], ![![-1, 1, 1, 0], ![-1, 1, -2, 1], ![-1, 1, 1, -1]], ![![-1, 1, -1, 0], ![0, 0, 0, 0], ![-1, 1, -1, -1]]],
    ![![![-1, -1, 0, 0], ![-1, -1, 0, 1], ![-1, -1, 3, -1]], ![![-1, -1, 1, 0], ![-1, -1, 1, 1], ![-1, -1, -2, -1]], ![![-1, -1, -1, 0], ![-1, -1, -1, 1], ![0, 0, 0, 0]]]]]

/-- Their inverses. -/
def tabV : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 4 → ℤ :=
  ![![![![![0, 0, 0, 0], ![-3, 0, 0, 2], ![-3, 0, 0, -2]], ![![1, 0, -1, 0], ![-1, 0, 1, 1], ![-1, 0, 1, -1]], ![![-1, 0, 1, 0], ![1, 0, -1, 1], ![1, 0, -1, -1]]],
    ![![![-3, 2, 0, 0], ![0, 0, 0, 0], ![-3, 2, 0, -2]], ![![-1, 1, 1, 0], ![-2, -1, -1, -1], ![-1, 1, 1, -1]], ![![1, 1, -1, 0], ![2, -1, 1, -1], ![1, 1, -1, -1]]],
    ![![![-3, -2, 0, 0], ![-3, -2, 0, 2], ![0, 0, 0, 0]], ![![-1, -1, 1, 0], ![-1, -1, 1, 1], ![-2, 1, -1, 1]], ![![1, -1, -1, 0], ![1, -1, -1, 1], ![2, 1, 1, 1]]]],
  ![![![![1, 0, 0, 0], ![-1, 0, 0, 1], ![-1, 0, 0, -1]], ![![0, 0, 0, 0], ![2, 0, -1, -1], ![2, 0, -1, 1]], ![![0, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, -1]]],
    ![![![-1, 1, 0, 0], ![-2, -1, 3, -1], ![-1, 1, 0, -1]], ![![2, -1, -1, 0], ![0, 0, 0, 0], ![2, -1, -1, 1]], ![![0, 1, -1, 0], ![-3, -1, 1, -1], ![0, 1, -1, -1]]],
    ![![![-1, -1, 0, 0], ![-1, -1, 0, 1], ![-2, 1, 3, 1]], ![![2, 1, -1, 0], ![2, 1, -1, -1], ![0, 0, 0, 0]], ![![0, -1, -1, 0], ![0, -1, -1, 1], ![-3, 1, 1, 1]]]],
  ![![![![-1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 0, -1]], ![![0, 0, -1, 0], ![0, 0, 1, 1], ![0, 0, 1, -1]], ![![0, 0, 0, 0], ![-2, 0, 1, -1], ![-2, 0, 1, 1]]],
    ![![![1, 1, 0, 0], ![2, -1, -3, -1], ![1, 1, 0, -1]], ![![0, 1, 1, 0], ![-3, -1, 2, -1], ![0, 1, 1, -1]], ![![-2, -1, 1, 0], ![0, 0, 0, 0], ![-2, -1, 1, 1]]],
    ![![![1, -1, 0, 0], ![1, -1, 0, 1], ![2, 1, -3, 1]], ![![0, -1, 1, 0], ![0, -1, 1, 1], ![-3, 1, 2, 1]], ![![-2, 1, 1, 0], ![-2, 1, 1, -1], ![0, 0, 0, 0]]]]]

theorem tab_spec : ∀ a b c d : ZMod 3,
    a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 ≠ 0 →
      (((tabU a b c d 0 : ℤ) : ZMod 3) = a ∧ ((tabU a b c d 1 : ℤ) : ZMod 3) = b ∧
        ((tabU a b c d 2 : ℤ) : ZMod 3) = c ∧ ((tabU a b c d 3 : ℤ) : ZMod 3) = d) ∧
      LeafQM.mulCoord (tabU a b c d) (tabV a b c d) = ![1, 0, 0, 0] ∧
      LeafQM.mulCoord (tabV a b c d) (tabU a b c d) = ![1, 0, 0, 0] := by
  decide +kernel

/-- **A unit congruent to `b` mod `3`**: if `nrd b ≢ 0 mod 3` for `b = ofInt m ∈ 𝒪`, then `b = ε + 3d` with
`ε ∈ 𝒪^×` (inverse `ε'`) and `d ∈ 𝒪`. -/
theorem exists_unit_cong (m : Fin 4 → ℤ) (h : ¬ (3 : ℤ) ∣ nrdZ m) :
    ∃ ε ε' d : LeafQM.B, InO ε ∧ InO ε' ∧ InO d ∧ ε * ε' = 1 ∧ ε' * ε = 1 ∧
      LeafQM.ofInt m = ε + 3 * d := by
  have hcond : ((m 0 : ℤ) : ZMod 3) ^ 2 + (m 0 : ZMod 3) * (m 2 : ZMod 3) - 2 * (m 1 : ZMod 3) ^ 2 -
      2 * (m 1 : ZMod 3) * (m 3 : ZMod 3) + (m 2 : ZMod 3) ^ 2 - 2 * (m 3 : ZMod 3) ^ 2 ≠ 0 := by
    intro h0
    apply h
    have h3 : ((3 : ℕ) : ℤ) ∣ nrdZ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 (by push_cast [nrdZ]; exact h0)
    exact_mod_cast h3
  obtain ⟨⟨c0, c1, c2, c3⟩, h1, h2⟩ := tab_spec _ _ _ _ hcond
  set t := tabU (m 0 : ZMod 3) (m 1 : ZMod 3) (m 2 : ZMod 3) (m 3 : ZMod 3) with ht
  set t' := tabV (m 0 : ZMod 3) (m 1 : ZMod 3) (m 2 : ZMod 3) (m 3 : ZMod 3) with ht'
  have hdvd : ∀ j, (3 : ℤ) ∣ m j - t j := by
    intro j
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (t j) (m j) 3)
    push_cast at this
    rw [← this]
    fin_cases j
    · exact c0
    · exact c1
    · exact c2
    · exact c3
  choose d hd using hdvd
  refine ⟨LeafQM.ofInt t, LeafQM.ofInt t', LeafQM.ofInt d, ⟨t, rfl⟩, ⟨t', rfl⟩, ⟨d, rfl⟩, ?_, ?_, ?_⟩
  · rw [LeafQM.ofInt_mul, h1, LeafQM.ofInt_one]
  · rw [LeafQM.ofInt_mul, h2, LeafQM.ofInt_one]
  · have hm : ∀ j, m j = t j + 3 * d j := fun j => by linarith [hd j]
    rw [three_mul_eq_smulB]
    ext <;> simp [LeafQM.ofInt, hm] <;> ring

theorem one_ne_three_mul (c : LeafQM.O) : (1 : LeafQM.O) ≠ 3 * c := by
  intro h
  have h' := congrArg (fun x : LeafQM.O => (x : LeafQM.B)) h
  simp only [Subring.coe_one, Subring.coe_mul] at h'
  obtain ⟨n, hn⟩ := c.2
  rw [show ((3 : LeafQM.O) : LeafQM.B) = 3 from rfl, hn, three_mul_eq_smulB] at h'
  have hre := congrArg QuaternionAlgebra.re h'
  have hj := congrArg QuaternionAlgebra.imJ h'
  simp [LeafQM.ofInt] at hre hj
  have hn2 : (n 2 : ℚ) = 0 := by exact_mod_cast hj
  rw [hn2] at hre
  have : (1 : ℤ) = 3 * n 0 := by exact_mod_cast (by linarith : (1 : ℚ) = 3 * n 0)
  omega

open scoped MonObj in
/-- **`ComplexUnifL3` from `QMComplexUnif`** (the chain's `qmComplexUnif_of_textbook`). -/
theorem complexUnifL3_of (hQ : HDec.HSyn.G0Split.FibreQM.QMComplexUnif) : ComplexUnifL3 := by
  intro P
  obtain ⟨τc, hτ, Φu, hU, hI⟩ := hQ P
  let τ : UpperHalfPlane := ⟨τc, hτ⟩
  have hU' : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu := hU
  obtain ⟨v, hv⟩ := hU.2.2.1 (Additive.toMul (P.e.eta 1))
  have h3v : v + v + v ∈ BPAnalytic.QM.qmLattice hτ.ne' := by
    rw [← hU.2.1, hU.1, hU.1, hv]
    show Additive.toMul (P.e.eta 1 + P.e.eta 1 + P.e.eta 1) = _
    rw [← map_add, ← map_add]
    have e : (1 + 1 + 1 : LeafQM.O) = 3 * 1 := by norm_num
    rw [e, (P.e.ker _).2 ⟨1, rfl⟩]
    rfl
  obtain ⟨b, hbO, hbv⟩ := exists_of_mem_qmLattice hτ.ne' h3v
  have hv3 : v = (3 : ℂ)⁻¹ • (iotaC b).mulVec ![τc, 1] := by
    rw [hbv]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have heta : ∀ a : LeafQM.O,
      Φu ((3 : ℂ)⁻¹ • (iotaC ((a : LeafQM.B) * b)).mulVec ![τc, 1]) = Additive.toMul (P.e.eta a) := by
    intro a
    have e1 : P.e.eta a = P.e.eta (a * 1) := by rw [_root_.mul_one]
    rw [e1, P.e.linear]
    show _ = Additive.toMul (P.e.eta 1) ≫ (P.q.iota a).hom
    have k1 := hI a v
    have k2 : (3 : ℂ)⁻¹ • (iotaC ((a : LeafQM.B) * b)).mulVec ![τc, 1] =
        (HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec v := by
      rw [hv3, Matrix.mulVec_smul, qmMat_eq, map_mul, ← Matrix.mulVec_mulVec]
    rw [k2]
    rw [hv] at k1
    exact k1
  obtain ⟨m, rfl⟩ := hbO
  have hnd : ¬ (3 : ℤ) ∣ nrdZ m := by
    rintro ⟨n, hn⟩
    let sb : LeafQM.O := ⟨star (LeafQM.ofInt m), inO_star ⟨m, rfl⟩⟩
    have h0 : P.e.eta sb = 0 := by
      have h := heta sb
      have hmem : (3 : ℂ)⁻¹ • (iotaC ((sb : LeafQM.B) * LeafQM.ofInt m)).mulVec ![τc, 1] ∈
          BPAnalytic.QM.qmLattice hτ.ne' := by
        have e : (3 : ℂ)⁻¹ • (iotaC ((sb : LeafQM.B) * LeafQM.ofInt m)).mulVec ![τc, 1] =
            n • ![τc, 1] := by
          show (3 : ℂ)⁻¹ • (iotaC (star (LeafQM.ofInt m) * LeafQM.ofInt m)).mulVec ![τc, 1] = _
          rw [star_mul_ofInt, iotaC_smul_mulVec, map_one, Matrix.one_mulVec, hn, smul_smul,
            ← Int.cast_smul_eq_zsmul ℂ]
          congr 1
          push_cast
          ring
        rw [e]
        exact Submodule.smul_mem _ _ (qmVec0_mem hτ.ne')
      have h1 := (hU.2.1 _).2 hmem
      rw [h1] at h
      exact (congrArg Additive.ofMul h).symm
    obtain ⟨c, hc⟩ := (P.e.ker sb).1 h0
    have hb3 : LeafQM.ofInt m = (3 : ℚ) • star (c : LeafQM.B) := by
      have e := congrArg (fun x : LeafQM.O => star (x : LeafQM.B)) hc
      simp only [sb, star_star, Subring.coe_mul] at e
      have hs3 : star (3 : LeafQM.B) = 3 := by ext <;> simp
      rw [e, show ((3 : LeafQM.O) : LeafQM.B) = 3 from rfl, star_mul, hs3, three_mul_eq_smulB']
    have h1 : P.e.eta 1 = 0 := by
      have hv' : v ∈ BPAnalytic.QM.qmLattice hτ.ne' := by
        rw [hv3, hb3, iotaC_smul_mulVec, smul_smul,
          show ((3 : ℂ)⁻¹ * ((3 : ℚ) : ℂ)) = 1 by norm_num, one_smul]
        exact mem_qmLattice_of_inO hτ.ne' (inO_star c.2)
      have h := (hU.2.1 v).2 hv'
      rw [hv] at h
      exact congrArg Additive.ofMul h
    obtain ⟨c', hc'⟩ := (P.e.ker 1).1 h1
    exact one_ne_three_mul c' hc'
  obtain ⟨ε, ε', d, hε, hε', hd, h1, h2, hbe⟩ := exists_unit_cong m hnd
  let u : BAQˣ := bUnit ε' ε h2 h1
  have hu : u ∈ OhatU := ⟨bEmb_mem_of_inO hε', bEmb_mem_of_inO hε⟩
  refine ⟨τ, u, hu, Φu, by rw [vecLat_unit hu τ]; exact hU', hI, fun a => ?_⟩
  refine ⟨(a : LeafQM.B) * LeafQM.ofInt m, ⟨bEmb ((a : LeafQM.B) * (d * ε')),
    bEmb_mem_of_inO (LeafQM.O.mul_mem a.2 (LeafQM.O.mul_mem hd hε')), ?_⟩, heta a⟩
  show bEmb ((a : LeafQM.B) * LeafQM.ofInt m) * bEmb ε' = _
  have e : (a : LeafQM.B) * LeafQM.ofInt m * ε' = (a : LeafQM.B) + 3 * ((a : LeafQM.B) * (d * ε')) := by
    rw [hbe]
    have h3 : (a : LeafQM.B) * 3 = 3 * (a : LeafQM.B) := (Commute.ofNat_right _ 3).eq
    calc (a : LeafQM.B) * (ε + 3 * d) * ε' = (a : LeafQM.B) * (ε * ε') + ((a : LeafQM.B) * 3) * (d * ε') := by
          noncomm_ring
      _ = _ := by rw [h1, h3]; noncomm_ring
  rw [← map_mul, e, map_add, map_mul, map_ofNat]

/-- **`ComplexUnifL3` from the textbook fields** `uniformizationLeafAll`, `gagaMorphism`,
`mumfordTorsionAlgClosed` (through the chain's `AvSplit.Final.h38`, `h69` and the proved `QMLatticeAlgebra`). -/
theorem complexUnifL3_of_textbook (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : ComplexUnifL3 :=
  complexUnifL3_of (HDec.HSyn.G0Split.FibreQM.qmComplexUnif_of_textbook (AvSplit.Final.h38 hUL hM)
    (ZInQ.HomUnify.t11a_riemannEnd_of_corr (AvSplit.Final.h69 hUL hG))
    (HDec.HSyn.G0Split.FibreQM.qmLatticeAlgebra_of_free
      (HDec.HSyn.G0Split.FibreQM.qmLatticeFree_of HDec.HSyn.G0Split.FibreQM.qmSkolemNoetherC_proof
        HDec.QMSplit.CNO.qmClassNumberOne_proof)))

/-! ## §10 The two fields from the two leaves and the kept textbook fields -/

/-- **The field `rayClassCMAb`** from the two leaves `ShimuraHolFamilyAb` (only its witness `(Y, Φ)` with
`R1fpPropsAb` is used) and `QMReciprocityL3`, and the textbook fields `uniformizationLeafAll`, `gagaMorphism`,
`mumfordTorsionAlgClosed` that the bundles keep. All glue is proved: `DCRelTransport` (`dcRelTransport_proof`),
`UnifDetermines` (from `HomLatticeCorr = AvSplit.Final.h69`), `ComplexUnifL3` (from the chain's `QMComplexUnif`),
`HomLinearLift`, and rayclass-cft's `QHatIntegral`, `CMBaseChange`, `CMAnalytic`, `RingOfIntegersGen`. -/
theorem rayClassCMAb_of_printed (hH : ShimuraHolFamilyAb) (hS : QMReciprocityL3)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : ShimuraGlue.Ray.RayClassCMAb :=
  rayClassCMAb_of_split hH hS dcRelTransport_proof (unifDetermines_of (AvSplit.Final.h69 hUL hG))
    (complexUnifL3_of_textbook hUL hG hM) (ZInQ.HomUnify.homLinearLift_of_corr (AvSplit.Final.h69 hUL hG))

/-- **The field `shimuraFamilyAb`** from the leaf `ShimuraHolFamilyAb` (the same theorem as `shimuraFamilyAb_of_hol`,
under the name used in the report). -/
theorem shimuraFamilyAb_of_printed (hH : ShimuraHolFamilyAb) : HDec.QMSplit.Moduli.ShimuraFamilyAb :=
  shimuraFamilyAb_of_hol hH

/-! ## §11 Non-vacuity checks -/

/-- `MIsAt` is not vacuous: under the textbook fields every object over `ℂ` is some `T(τ, u)`. -/
theorem mIsAt_exists (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) (P : QML3 ℂ) : ∃ (τ : UpperHalfPlane) (u : BAQˣ), MIsAt P τ u := by
  obtain ⟨τ, u, -, h⟩ := complexUnifL3_of_textbook hUL hG hM P
  exact ⟨τ, u, h⟩

/-- `ShimuraHolFamilyAb` is gt-rayclass's composite with clauses 1, 2 (`g ≠ 1`), U and 4 dropped. -/
theorem shimuraHolFamilyAb_of_composite (h : ShimuraMainThmIDeligneY3AbU) : ShimuraHolFamilyAb := by
  obtain ⟨Y, Φ, h1, Ψ, hb, -⟩ := h
  exact ⟨Y, Φ, h1, fun τ => Ψ τ 1, hb.2.2.2.1⟩

/-! ## §12 The moduli leaf without its existence clause: `ShimuraHolModAll`

`ShimuraHolFamilyAb` bundles the representability clause (R) (`∃ (Y, Φ)` with `R1fpPropsAb`) with the analytic
statement. Following the bundle's convention for `gonzalezRotgerProp56X6` (a printed statement "for every witness,
with no existence claim"), the analytic statement is stated here **for every fine witness**, and (R) is taken from a
leaf the bundles already have (`deligneComponentsX6PrintedAb`). The two forms are equivalent given (R)
(`shimuraHolModAll_of_hol`, `shimuraHolFamilyAb_of_all`): a fine witness `(Y', Φ')` maps to every other one by the
universal property `R1univAbProps` (`exists_map_of_r1fp`), compatibly with the moduli bijections, and holomorphic
families compose with morphisms of schemes (`isHolFamily_comp`). So the `∀` form is not stronger than the `∃` form. -/

/-- **LEAF `ShimuraHolModAll` (Shimura's Main Theorem I, complex part, for every fine witness).** For every `(Y, Φ)`
with `R1fpPropsAb` (the fine moduli scheme `Y₃` of QM abelian surfaces with level 3 and its moduli bijections) there
is a holomorphic `τ ↦ y_τ ∈ Y(ℂ)` whose object at `y_τ` is, as a QM pair, `ℂ²/ι(𝒪)(τ, 1)ᵀ` (`IsShimuraHolFamily`).

*Published statements* (UNVERIFIED locators): Shimura, Ann. of Math. 85 (1967), Main Theorem I and §§2-3 (the
holomorphic `φ : ℍ → V(ℂ)`, `φ(τ)` the moduli point of `ℂ²/ι(𝒪)(τ, 1)ᵀ`); Deligne, Sém. Bourbaki 389 (1971), §4
(the moduli scheme and its complex uniformization; analytic families). *Form*: one family on the component of
`Y₃(ℂ)` through the points `[τ, 1]`; the moduli clause describes only the QM pair; no existence claim (it is
equivalent, given one fine witness, to `ShimuraHolFamilyAb`, proved below). -/
def ShimuraHolModAll : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ →
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ

/-- The point of `y ≫ h` is the image of the point of `y`. -/
theorem ptC_comp {X X' : Scheme.{0}} (h : X' ⟶ X) (y : Spec (CommRingCat.of ℂ) ⟶ X') :
    ShimuraSplit.ptC (y ≫ h) = h.base (ShimuraSplit.ptC y) := rfl

/-- Values of regular functions along `h`: `f(h(y)) = (h^* f)(y)`. -/
theorem regVal_comp {X X' : Scheme.{0}} (h : X' ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (y : Spec (CommRingCat.of ℂ) ⟶ X') :
    ShimuraSplit.regVal U f (y ≫ h) = ShimuraSplit.regVal (h ⁻¹ᵁ U) (h.app U f) y := by
  unfold ShimuraSplit.regVal
  by_cases hm : ShimuraSplit.ptC y ∈ h ⁻¹ᵁ U
  · have hm' : ShimuraSplit.ptC (y ≫ h) ∈ U := by rw [ptC_comp]; exact hm
    rw [dif_pos hm', dif_pos hm]
    show (X.descResidueField (Scheme.stalkClosedPointTo (y ≫ h))).hom
        (X.evaluation U (h.base (ShimuraSplit.ptC y)) hm f) =
      (X'.descResidueField (Scheme.stalkClosedPointTo y)).hom
        (X'.evaluation (h ⁻¹ᵁ U) (ShimuraSplit.ptC y) hm (h.app U f))
    have key := Scheme.descResidueField_stalkClosedPointTo_comp (f := h) y
    erw [key, CommRingCat.comp_apply, Scheme.evaluation_naturality_apply]
    rfl
  · have hm' : ¬ ShimuraSplit.ptC (y ≫ h) ∈ U := by rw [ptC_comp]; exact hm
    rw [dif_neg hm', dif_neg hm]

/-- **Holomorphic families compose with morphisms of schemes.** -/
theorem isHolFamily_comp {X X' : Scheme.{0}} (h : X' ⟶ X)
    {φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X')} (hφ : ShimuraSplit.IsHolFamily φ) :
    ShimuraSplit.IsHolFamily (fun τ => φ τ ≫ h) := by
  refine ⟨fun U => hφ.1 (h ⁻¹ᵁ U), fun U f τ hτ => ?_⟩
  obtain ⟨g, hg, hev⟩ := hφ.2 (h ⁻¹ᵁ U) (h.app U f) τ hτ
  refine ⟨g, hg, hev.mono fun z hz hz' => ?_⟩
  rw [regVal_comp]
  exact hz hz'

/-- **Maps between fine witnesses**: for fine witnesses `(Y', Φ')`, `(Y, Φ)` there is `g : Y' → Y` with
`Φ(s ≫ g) = Φ'(s)` at every field point (`R1univAbProps` of `Y` applied to the universal family of `Y'`). -/
theorem exists_map_of_r1fp {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (h : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (h' : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), Φ K (s ≫ g) = Φ' K s := by
  obtain ⟨hp', hs', -, -, ⟨𝒜', h𝒜'⟩, -⟩ := h'
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜'.toQMFamily s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ' K s)
    exact ⟨P, h𝒜' K s P hP.symm⟩
  obtain ⟨g, hg⟩ := h.2.2.2.2.2 Y' hp' hs' 𝒜' hfib
  refine ⟨g, fun K _ _ s => ?_⟩
  obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ' K s)
  rw [hg K s P (h𝒜' K s P hP.symm), ← hP]
  rfl

/-- **The `∀` form from the `∃` form** (so `ShimuraHolModAll` is not stronger than `ShimuraHolFamilyAb`). -/
theorem shimuraHolModAll_of_hol (hH : ShimuraHolFamilyAb) : ShimuraHolModAll := by
  obtain ⟨Y', Φ', h1', yτ, hmod, hhol⟩ := hH
  intro Y Φ h1
  obtain ⟨g, hg⟩ := exists_map_of_r1fp h1 h1'
  refine ⟨fun τ => yτ τ ≫ g, fun τ => ?_, isHolFamily_comp g.left hhol⟩
  obtain ⟨P, hP, rest⟩ := hmod τ
  exact ⟨P, (hg ℂ (yτ τ)).trans hP, rest⟩

/-- **The `∃` form from the `∀` form and one fine witness.** -/
theorem shimuraHolFamilyAb_of_all (hW : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (hH : ShimuraHolModAll) : ShimuraHolFamilyAb := by
  obtain ⟨Y, Φ, h1⟩ := hW
  exact ⟨Y, Φ, h1, hH Y Φ h1⟩

/-- A fine witness from Deligne's `π₀` leaf on `X₆` (its clause (R)). -/
theorem witness_of_x6 (h : ShimuraGlue.DeligneComponentsX6PrintedAb) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ := by
  obtain ⟨Y, Φ, -, -, -, h1, -⟩ := h
  exact ⟨Y, Φ, h1⟩

/-- **The field `rayClassCMAb`** from (R) of `deligneComponentsX6PrintedAb`, the leaf `QMReciprocityL3`, and the
textbook fields `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`. No holomorphy is used. -/
theorem rayClassCMAb_of_leaves2 (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hS : QMReciprocityL3)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : ShimuraGlue.Ray.RayClassCMAb :=
  rayClassCMAb_of_witness (witness_of_x6 hR) hS dcRelTransport_proof
    (unifDetermines_of (AvSplit.Final.h69 hUL hG)) (complexUnifL3_of_textbook hUL hG hM)
    (ZInQ.HomUnify.homLinearLift_of_corr (AvSplit.Final.h69 hUL hG))

/-- **The field `shimuraFamilyAb`** from (R) of `deligneComponentsX6PrintedAb` and the leaf `ShimuraHolModAll`. -/
theorem shimuraFamilyAb_of_leaves2 (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hH : ShimuraHolModAll) :
    HDec.QMSplit.Moduli.ShimuraFamilyAb :=
  shimuraFamilyAb_of_hol (shimuraHolFamilyAb_of_all (witness_of_x6 hR) hH)

end ShimuraSplit2

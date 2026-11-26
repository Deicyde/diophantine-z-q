import ZInQKernel.Contrib.OneProof.Y3HodgePrint
import ZInQKernel.Contrib.OneProof.DeligneY3Bridges.Similitude
import ZInQKernel.Contrib.OneProof.DeligneY3Bridges.LevelCompat

/-!
# `deligneCanonicalModelY3EveryPrint` read against Deligne's PEL datum (Bourbaki 389)

P. Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971). The Lean statement
`Y3Hodge.DeligneCanonicalModelY3EveryPrint` writes the group of the Shimura datum as `B^×` and
`(B ⊗ 𝔸_f)^×`, the level as the kernel's `K3Q` and the units as `OhatU`. The print (4.9–4.12,
Scholie 4.11, Ex. 5.8) writes them as the group `G` of `B`-linear symplectic similitudes of
`(V, ψ) = (B, trd(μ⁻¹ x ȳ))`, the level as `K_n = {g ∈ G(𝔸^f) | (g − 1) V̂_ℤ ⊂ n V̂_ℤ}` (4.12) with
`V_ℤ = 𝒪`, and the integral structure as the stabilizer `G(Ẑ)` of `V̂_ℤ`. This file proves the
identifications and restates the leaf with the print's objects:

* `psi_rat`, `psi_alt`, `psi_rosati`: `ψ` over `ℚ` is the kernel's `RvQMPolar.E0`, alternating,
  with adjoint the involution `x† = μ⁻¹ x̄ μ` (4.9: a PEL datum);
* `toGQ : B^× ≃* G(ℚ)` and `toGAf : (B ⊗ 𝔸_f)^× ≃* G(𝔸_f)`, `γ ↦ (x ↦ x γ⁻¹)` (from
  `DeligneY3Bridges.simEquiv`), with multiplier `nrd(γ)⁻¹` (`psi_toGQ`);
* `baseChange : G(ℚ) →* G(𝔸_f)`, the unique extension along `B ⊂ B ⊗ 𝔸_f`
  (`eq_baseChange_iff`), and `toGAf (bEmb γ) = baseChange (toGQ γ)`;
* `mem_K3Q_iff`: `k ∈ K3Q ↔ toGAf k ∈ G(Ẑ) ∩ K_3`; `mem_OhatU_iff`: `u ∈ OhatU ↔ toGAf u ∈ G(Ẑ)`;
* `dcRelPEL_iff`: the print's relation on `X × G(𝔸_f)` (`DCRelPEL`) is `DCRelPM` after `toGAf`;
  `dcRelDel_iff_PM`: the same for Deligne's own convention `K \ X × G(𝔸^f) / G(ℚ)` (1.8);
* `print_iff_PEL`: `DeligneCanonicalModelY3EveryPrint ↔ DeligneCanonicalModelY3EveryPEL`, the
  same leaf with `G(ℚ)`, `G(𝔸_f)`, `G(Ẑ) ∩ K_3` and `G(Ẑ)` in place of `B^×`, `(B ⊗ 𝔸_f)^×`,
  `K3Q` and `OhatU`.

The action of `G(ℚ)` on `X = ℍ^±` is through `G(ℚ) ⊂ G(ℝ) ≅ B_ℝ^× ≅ GL₂(ℝ)` (Möbius maps of
`ι(γ)`); that this is the conjugation action on the `h`'s is `Y3Hodge.iota_mul_Jmat` (and
`Y3Hodge.F0_iff` fixes the sign of `h`). The comparison of the polarized PEL moduli problem with
the polarization-free one is a reading step (see the README).
-/

noncomputable section

namespace DeligneY3Bridges.PEL

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid ShimuraCFT RayClassCFT
open NumberField IsDedekindDomain TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

/-! ## The PEL datum over `ℚ` -/

theorem muInv_rat : DeligneY3Bridges.muInv ℚ = RvQMPolar.muInv := rfl

/-- **`ψ` over `ℚ` is the kernel's `E₀`**: `trd(μ⁻¹ x ȳ)`. -/
theorem psi_rat (x y : LeafQM.B) : DeligneY3Bridges.psi ℚ x y = RvQMPolar.E0 x y := by
  simp only [DeligneY3Bridges.psi, RvQMPolar.E0, RvQMPolar.trd, muInv_rat]

/-- `ψ` is alternating (4.9). -/
theorem psi_alt (x : LeafQM.B) : DeligneY3Bridges.psi ℚ x x = 0 := by
  rw [psi_rat]; exact RvQMPolar.E0_alt x

/-- `ψ(a x, y) = ψ(x, a† y)` with `a† = μ⁻¹ ā μ` (4.9: `B` acts on `V = B` with adjoint `†`). -/
theorem psi_rosati (a x y : LeafQM.B) :
    DeligneY3Bridges.psi ℚ (a * x) y = DeligneY3Bridges.psi ℚ x (RvQMPolar.dag a * y) := by
  rw [psi_rat, psi_rat]; exact RvQMPolar.E0_rosati a x y

/-- The kernel's `nrd` is `x x̄`. -/
theorem nrdQ_eq (x : LeafQM.B) : ShimuraGlue.nrdQ ℚ x = DeligneY3Bridges.nrd ℚ x := by
  simp [ShimuraGlue.nrdQ_apply, DeligneY3Bridges.nrd]
  ring

/-! ## `G(ℚ)`, `G(𝔸_f)`, base change -/

/-- Deligne's `G(ℚ)`: `B`-linear symplectic similitudes of `(B, ψ)`. -/
abbrev GQ : Type := ↥(DeligneY3Bridges.simGroup ℚ)

/-- Deligne's `G(𝔸_f)`: `B ⊗ 𝔸_f`-linear symplectic similitudes of `(B ⊗ 𝔸_f, ψ)`. -/
abbrev GAf : Type := ↥(DeligneY3Bridges.simGroup ShimuraCFT.AQ)

/-- **`B^× ≅ G(ℚ)`**, `γ ↦ (x ↦ x γ⁻¹)`. -/
def toGQ : (LeafQM.B)ˣ ≃* GQ := DeligneY3Bridges.simEquiv ℚ

/-- **`(B ⊗ 𝔸_f)^× ≅ G(𝔸_f)`**, `g ↦ (x ↦ x g⁻¹)`. -/
def toGAf : ShimuraCFT.BAQˣ ≃* GAf := DeligneY3Bridges.simEquiv ShimuraCFT.AQ

theorem app_toGQ (γ : (LeafQM.B)ˣ) (x : LeafQM.B) :
    DeligneY3Bridges.app (toGQ γ) x = x * ((γ⁻¹ : (LeafQM.B)ˣ) : LeafQM.B) := rfl

theorem app_toGAf (g : ShimuraCFT.BAQˣ) (x : ShimuraCFT.BAQ) :
    DeligneY3Bridges.app (toGAf g) x = x * ((g⁻¹ : ShimuraCFT.BAQˣ) : ShimuraCFT.BAQ) := rfl

/-- `nrd γ ≠ 0` for `γ ∈ B^×`. -/
theorem nrdQ_ne_zero (γ : (LeafQM.B)ˣ) : ShimuraGlue.nrdQ ℚ (γ : LeafQM.B) ≠ 0 := by
  rw [nrdQ_eq]
  intro h
  have := DeligneY3Bridges.nrd_mul_nrd_inv γ
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- `γ ∈ B` with `nrd γ ≠ 0` is a unit. -/
theorem exists_unit_of_nrdQ {x : LeafQM.B} (h : ShimuraGlue.nrdQ ℚ x ≠ 0) :
    ∃ u : (LeafQM.B)ˣ, (u : LeafQM.B) = x := by
  rw [nrdQ_eq] at h
  exact DeligneY3Bridges.isUnit_of_isUnit_nrd (isUnit_iff_ne_zero.mpr h)

/-- **The multiplier of `toGQ γ` is `nrd(γ)⁻¹`.** -/
theorem psi_toGQ (γ : (LeafQM.B)ˣ) (x y : LeafQM.B) :
    DeligneY3Bridges.psi ℚ (DeligneY3Bridges.app (toGQ γ) x) (DeligneY3Bridges.app (toGQ γ) y) =
      (ShimuraGlue.nrdQ ℚ (γ : LeafQM.B))⁻¹ * DeligneY3Bridges.psi ℚ x y := by
  rw [app_toGQ, app_toGQ, DeligneY3Bridges.psi_mul_right, nrdQ_eq]
  congr 1
  exact (eq_inv_of_mul_eq_one_right (DeligneY3Bridges.nrd_mul_nrd_inv γ))

/-- The coordinatewise embedding `B → B ⊗ 𝔸_f` (the kernel's `bEmb`) as a monoid map. -/
def bEmbHom : DeligneY3Bridges.QB ℚ →* DeligneY3Bridges.QB ShimuraCFT.AQ :=
  ShimuraCFT.bEmb.toRingHom.toMonoidHom

theorem bEmbHom_apply (x : LeafQM.B) : bEmbHom x = ShimuraCFT.bEmb x := rfl

/-- **Base change `G(ℚ) → G(𝔸_f)`** (the inclusion `G(ℚ) ⊂ G(𝔸_f)` of the print). -/
def baseChange : GQ →* GAf := DeligneY3Bridges.baseChangeOf bEmbHom

/-- **`baseChange f` is the unique element of `G(𝔸_f)` extending `f` along `B ⊂ B ⊗ 𝔸_f`.** -/
theorem eq_baseChange_iff (f : GQ) (h : GAf) :
    (∀ x : LeafQM.B, DeligneY3Bridges.app h (ShimuraCFT.bEmb x) =
      ShimuraCFT.bEmb (DeligneY3Bridges.app f x)) ↔ h = baseChange f := by
  constructor
  · exact DeligneY3Bridges.eq_baseChangeOf bEmbHom f h
  · rintro rfl x
    exact DeligneY3Bridges.app_baseChangeOf bEmbHom f x

theorem baseChange_toGQ (γ : (LeafQM.B)ˣ) :
    baseChange (toGQ γ) = toGAf (Units.map bEmbHom γ) := by
  show toGAf (Units.map bEmbHom ((DeligneY3Bridges.simEquiv ℚ).symm (toGQ γ))) = _
  rw [show (DeligneY3Bridges.simEquiv ℚ).symm (toGQ γ) = γ from
    (DeligneY3Bridges.simEquiv ℚ).symm_apply_apply γ]

/-! ## `V̂_ℤ = 𝒪̂`, `G(Ẑ)` and `K_3` -/

/-- `V̂_ℤ = 𝒪̂ ⊂ B ⊗ 𝔸_f` (4.12 with `V_ℤ = L_ℤ = 𝒪`). -/
def VZhat : Set (DeligneY3Bridges.QB ShimuraCFT.AQ) := ShimuraCFT.OhatQ

/-- `G(Ẑ)`: the stabilizer of `V̂_ℤ` in `G(𝔸_f)`. -/
def GZhat : Set GAf := {g | DeligneY3Bridges.IsStab VZhat g}

/-- **`G(Ẑ) ∩ K_3`**, with `K_3 = {g ∈ G(𝔸^f) | (g − 1) V̂_ℤ ⊂ 3 V̂_ℤ}` (4.12, p. 148). -/
def K3PEL : Set GAf :=
  {g | DeligneY3Bridges.IsStab VZhat g ∧ DeligneY3Bridges.IsCongr VZhat 3 g}

theorem one_mem_VZhat : (1 : DeligneY3Bridges.QB ShimuraCFT.AQ) ∈ VZhat :=
  RayClassCFT.OhatQ_one

theorem mul_mem_VZhat (x y : DeligneY3Bridges.QB ShimuraCFT.AQ) (hx : x ∈ VZhat)
    (hy : y ∈ VZhat) : x * y ∈ VZhat :=
  RayClassCFT.OhatQ_mul hx hy

theorem neg_mem_VZhat (x : DeligneY3Bridges.QB ShimuraCFT.AQ) (hx : x ∈ VZhat) : -x ∈ VZhat :=
  RayClassCFT.OhatQ_neg hx

/-- **`OhatU` is `G(Ẑ)`** under `toGAf`. -/
theorem mem_OhatU_iff (u : ShimuraCFT.BAQˣ) : u ∈ RayClassCFT.OhatU ↔ toGAf u ∈ GZhat :=
  DeligneY3Bridges.unit_iff VZhat one_mem_VZhat mul_mem_VZhat u

/-- **`K3Q` is `G(Ẑ) ∩ K_3`** under `toGAf`. -/
theorem mem_K3Q_iff (k : ShimuraCFT.BAQˣ) : k ∈ ShimuraCFT.K3Q ↔ toGAf k ∈ K3PEL :=
  DeligneY3Bridges.level_iff VZhat one_mem_VZhat mul_mem_VZhat neg_mem_VZhat 3 k

/-! ## The relation and the leaf with the print's objects -/

/-- The element `γ ∈ B^×` of `f ∈ G(ℚ)` (`f = (x ↦ x γ⁻¹)`). -/
def gammaQ (f : GQ) : LeafQM.B := ((toGQ.symm f : (LeafQM.B)ˣ) : LeafQM.B)

/-- **The print's relation on `X × G(𝔸_f)`** (Def. 1.8, `Sh_K(ℂ) = G(ℚ) \ X × G(𝔸_f) / K`):
`(z, g) ~ (f z, f g k)` with `f ∈ G(ℚ)` acting on `X = ℍ^±` through `ι(γ_f) ∈ GL₂(ℝ)` and on
`G(𝔸_f)` through `baseChange`, and `k ∈ K = G(Ẑ) ∩ K_3`. -/
def DCRelPEL (z : Y3Hodge.HPM) (g : GAf) (z' : Y3Hodge.HPM) (g' : GAf) : Prop :=
  ∃ (f : GQ) (hγ : ShimuraGlue.nrdQ ℚ (gammaQ f) ≠ 0),
    Y3Hodge.mobPM (RayClassCFT.iotaGL (gammaQ f) hγ) z = z' ∧
    ∃ k ∈ K3PEL, g' = baseChange f * g * k

/-- **`DCRelPEL` is `DCRelPM`** after `toGAf`. -/
theorem dcRelPEL_iff (z : Y3Hodge.HPM) (g : ShimuraCFT.BAQˣ) (z' : Y3Hodge.HPM)
    (g' : ShimuraCFT.BAQˣ) : DCRelPEL z (toGAf g) z' (toGAf g') ↔ Y3Hodge.DCRelPM z g z' g' := by
  constructor
  · rintro ⟨f, hγ, hmob, k, hk, hg'⟩
    refine ⟨gammaQ f, hγ, hmob, toGAf.symm k, ?_, ?_⟩
    · rw [mem_K3Q_iff, MulEquiv.apply_symm_apply]
      exact hk
    · have h1 : g' = Units.map bEmbHom (toGQ.symm f) * g * toGAf.symm k := by
        apply toGAf.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← baseChange_toGQ,
          MulEquiv.apply_symm_apply]
        exact hg'
      rw [h1]
      rfl
  · rintro ⟨gm, hγ, hmob, k, hk, hg'⟩
    obtain ⟨u, rfl⟩ := exists_unit_of_nrdQ hγ
    have hgam : gammaQ (toGQ u) = (u : LeafQM.B) := by
      simp only [gammaQ, MulEquiv.symm_apply_apply]
    have key : ∀ (x : LeafQM.B) (hx : x = (u : LeafQM.B)) (h : ShimuraGlue.nrdQ ℚ x ≠ 0),
        Y3Hodge.mobPM (RayClassCFT.iotaGL x h) z = z' := by
      rintro x rfl h
      exact hmob
    refine ⟨toGQ u, by rw [hgam]; exact hγ, key _ hgam _, toGAf k, (mem_K3Q_iff k).1 hk, ?_⟩
    have h1 : g' = Units.map bEmbHom u * g * k := Units.ext (by rw [hg']; rfl)
    rw [h1, map_mul, map_mul, baseChange_toGQ]

/-- **The relation in Deligne's own convention** (1.8, p. 129:
`K\X × G(𝔸^f)/G(ℚ)`, with `K` on the left and `G(ℚ)` on the right): `(z, g) ~ (z', g')` when
`z = f z'` and `g' = k g f` for `f ∈ G(ℚ)`, `k ∈ K = G(Ẑ) ∩ K_3`. -/
def DCRelDel (z : Y3Hodge.HPM) (g : GAf) (z' : Y3Hodge.HPM) (g' : GAf) : Prop :=
  ∃ (f : GQ) (hγ : ShimuraGlue.nrdQ ℚ (gammaQ f) ≠ 0),
    Y3Hodge.mobPM (RayClassCFT.iotaGL (gammaQ f) hγ) z' = z ∧
    ∃ k ∈ K3PEL, g' = k * g * baseChange f

/-- **Deligne's right-hand convention is the left-hand one after `g ↦ g⁻¹`.** -/
theorem dcRelDel_iff (z : Y3Hodge.HPM) (g : GAf) (z' : Y3Hodge.HPM) (g' : GAf) :
    DCRelDel z g z' g' ↔ DCRelPEL z' g'⁻¹ z g⁻¹ :=
  exists_congr fun _ => exists_congr fun _ => and_congr Iff.rfl <|
    exists_congr fun _ => and_congr Iff.rfl (DeligneY3Bridges.rel_inv_iff _ _ _ _)

/-- **Deligne's relation (1.8) is the kernel's `DCRelPM`** after `g ↦ toGAf(g)` on the print's side
and `g ↦ g⁻¹` (the kernel uses `B^× \ (ℍ^± × (B ⊗ 𝔸_f)^×) / K₃`). -/
theorem dcRelDel_iff_PM (z : Y3Hodge.HPM) (g : ShimuraCFT.BAQˣ) (z' : Y3Hodge.HPM)
    (g' : ShimuraCFT.BAQˣ) :
    DCRelDel z (toGAf g) z' (toGAf g') ↔ Y3Hodge.DCRelPM z' g'⁻¹ z g⁻¹ := by
  rw [dcRelDel_iff, ← map_inv, ← map_inv, dcRelPEL_iff]

/-- **The leaf's body with the print's objects**: `Ψ : X × G(𝔸_f) → Y(ℂ)` onto, fibres the print's
`DCRelPEL`, holomorphic in `τ ∈ ℍ`, the `H₁` form at `g = 1`, and reciprocity at CM points with
`q̂(s)^ε` acting on `G(𝔸_f)` through `toGAf`. Clause by clause the same text as
`Y3Hodge.DeligneBodyAtPM`, with `G(𝔸_f)` for `(B ⊗ 𝔸_f)^×` and `DCRelPEL` for `DCRelPM`. -/
def DeligneBodyAtPEL (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : Y3Hodge.HPM → GAf → (fieldPt ℂ ⟶ Y)) : Prop :=
    (∀ y : fieldPt ℂ ⟶ Y, ∃ z g, Ψ z g = y) ∧
    (∀ z g z' g', Ψ z g = Ψ z' g' ↔ DCRelPEL z g z' g') ∧
    (∀ g, ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ (Y3Hodge.toPM τ) g).left)) ∧
    Y3Hodge.IsShimuraHolFamilyHP Y Φ (fun τ => Ψ (Y3Hodge.toPM τ) 1) ∧
    ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : GAf, galPt σ (Ψ (Y3Hodge.toPM z) g) =
        Ψ (Y3Hodge.toPM z) (toGAf (qHatU q s ^ (ε : ℤ)) * g)

/-- The moduli clause at `[τ, u]`, `u ∈ G(Ẑ)`, in the print's `H₁` form. -/
def ModuliAtGZhat (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : Y3Hodge.HPM → GAf → (fieldPt ℂ ⟶ Y)) : Prop :=
  ∀ u ∈ GZhat, ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ,
    Φ ℂ (Ψ (Y3Hodge.toPM τ) u) = M3.mk P ∧ Y3Hodge.IsHodgeH1Print P τ

/-- **`DeligneCanonicalModelY3EveryPrint` with the print's objects**: `G(ℚ)`, `G(𝔸_f)` (similitude
groups of `(B, ψ)`), `K = G(Ẑ) ∩ K_3` and `G(Ẑ)`. -/
def DeligneCanonicalModelY3EveryPEL : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), Y3Fix.R1fpPropsAbP Y Φ →
    ∃ Ψ, DeligneBodyAtPEL Y Φ Ψ ∧ ModuliAtGZhat Y Φ Ψ

/-- **The leaf from its PEL form**, through `toGAf`. -/
theorem print_of_PEL (h : DeligneCanonicalModelY3EveryPEL) :
    Y3Hodge.DeligneCanonicalModelY3EveryPrint := by
  intro Y Φ hY
  obtain ⟨Ψ, ⟨h1, h2, h3, h4, ε, δ, h5⟩, hU⟩ := h Y Φ hY
  refine ⟨fun z g => Ψ z (toGAf g), ⟨fun y => ?_, fun z g z' g' => ?_, fun g => h3 (toGAf g),
    ?_, ε, δ, ?_⟩, ?_⟩
  · obtain ⟨z, g, hg⟩ := h1 y
    exact ⟨z, toGAf.symm g, by simp only [MulEquiv.apply_symm_apply]; exact hg⟩
  · exact (h2 _ _ _ _).trans (dcRelPEL_iff z g z' g')
  · show Y3Hodge.IsShimuraHolFamilyHP Y Φ (fun τ => Ψ (Y3Hodge.toPM τ) (toGAf 1))
    rw [map_one]
    exact h4
  · intro K _ _ _ hK κ q z hz σ s hs g
    show galPt σ (Ψ (Y3Hodge.toPM z) (toGAf g)) =
      Ψ (Y3Hodge.toPM z) (toGAf (qHatU q s ^ (ε : ℤ) * g))
    rw [map_mul]
    exact h5 K hK κ q z hz σ s hs (toGAf g)
  · intro u hu τ
    exact hU (toGAf u) ((mem_OhatU_iff u).1 hu) τ

/-- **The PEL form from the leaf**, through `toGAf⁻¹`. -/
theorem PEL_of_print (h : Y3Hodge.DeligneCanonicalModelY3EveryPrint) :
    DeligneCanonicalModelY3EveryPEL := by
  intro Y Φ hY
  obtain ⟨Ψ, ⟨h1, h2, h3, h4, ε, δ, h5⟩, hU⟩ := h Y Φ hY
  refine ⟨fun z g => Ψ z (toGAf.symm g), ⟨fun y => ?_, fun z g z' g' => ?_,
    fun g => h3 (toGAf.symm g), ?_, ε, δ, ?_⟩, ?_⟩
  · obtain ⟨z, g, hg⟩ := h1 y
    exact ⟨z, toGAf g, by simp only [MulEquiv.symm_apply_apply]; exact hg⟩
  · have e := dcRelPEL_iff z (toGAf.symm g) z' (toGAf.symm g')
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at e
    exact (h2 _ _ _ _).trans e.symm
  · show Y3Hodge.IsShimuraHolFamilyHP Y Φ (fun τ => Ψ (Y3Hodge.toPM τ) (toGAf.symm 1))
    rw [map_one]
    exact h4
  · intro K _ _ _ hK κ q z hz σ s hs g
    show galPt σ (Ψ (Y3Hodge.toPM z) (toGAf.symm g)) =
      Ψ (Y3Hodge.toPM z) (toGAf.symm (toGAf (qHatU q s ^ (ε : ℤ)) * g))
    rw [map_mul, MulEquiv.symm_apply_apply]
    exact h5 K hK κ q z hz σ s hs (toGAf.symm g)
  · intro u hu τ
    exact hU (toGAf.symm u) ((mem_OhatU_iff _).2 (by rw [MulEquiv.apply_symm_apply]; exact hu)) τ

/-- **The leaf is its PEL form**: no clause is changed, only the groups are renamed through the
proved identifications. -/
theorem print_iff_PEL :
    Y3Hodge.DeligneCanonicalModelY3EveryPrint ↔ DeligneCanonicalModelY3EveryPEL :=
  ⟨PEL_of_print, print_of_PEL⟩

end DeligneY3Bridges.PEL

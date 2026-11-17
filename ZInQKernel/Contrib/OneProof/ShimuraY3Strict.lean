import ZInQKernel.Contrib.OneProof.ShimuraY3Print

/-! # y3abu-strict: Deligne's leaf split into the moduli interpretation and the canonical-model property

Task y3abu-strict (2026-11-16/17). Report: `docs/research/y3abu-strict.md`; log: `scratch/y3abu-strict/log.md`.

y3abu-print proved the research field `RayClassCFT.ShimuraMainThmIDeligneY3AbU` from two leaves,
`Y3ABUPrint.Y3FineModuliAb` and `Y3ABUPrint.DeligneCanonicalModelY3Every`. The second reads two printed theorems
as one: the **moduli interpretation** of `Sh_{K₃}(B^×, ℍ^±)(ℂ)` (Milne, *Introduction to Shimura varieties*, §8;
Deligne, *Travaux de Shimura*, §4) and the **canonical-model property** of the moduli scheme (Milne §14; Deligne
§§4-5, Cor. 5.7 / Ex. 5.8; Shimura 1967 Main Theorem I). This file splits it:

1. `DeligneModuliY3Every` (new leaf, moduli interpretation): on every fine witness `(Y, Φ)` there is
   `Ψ : ℍ × (B ⊗ 𝔸_f)^× → Y(ℂ)`, onto, with fibres the `B^×_+ \ · / K₃` classes, holomorphic in `τ`, whose value
   at `(τ, u)`, `u ∈ 𝒪̂^×`, is the moduli point of the QM torus `ℂ²/Λ_τ`, `Λ_τ = ι(𝒪)(τ, 1)ᵀ`, **with its
   level structure** `η_u(a) = (1/3) ι(a w)(τ, 1)ᵀ mod Λ_τ`, `w ∈ 𝒪`, `w ≡ u⁻¹ mod 3𝒪̂`
   (`ModuliLevelAtUnits`). The level structure is what pins `Ψ` (y3abu-print §4.2, gt-rayclass §3: without it,
   a right translation on one geometric component keeps every other clause and breaks reciprocity).
2. `DeligneReciprocityY3Every` (new leaf, canonical-model property): on every fine witness, **every** `Ψ` with
   the moduli interpretation of 1 satisfies Shimura's reciprocity law at CM points (conventions `ε, δ`
   existential). No existence claim.
3. The glue, proved: `deligneCanonicalModelY3Every_of_split` (the two leaves give y3abu-print's leaf) and the
   discharge `shimuraMainThmIDeligneY3AbU_of_strict` from `Y3FineModuliAb` and the two new leaves.

No `sorry`; standard axioms only.
-/

set_option linter.all false

noncomputable section

namespace Y3ABUStrict

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)
open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible IsShimuraHolFamily)

/-! ## 1. The clauses -/

/-- **The moduli clause at every `u ∈ 𝒪̂^×`, with the level structure.** The object at `Ψ(τ, u)` is the QM torus
`ℂ²/Λ_τ`, `Λ_τ = ι(𝒪)(τ, 1)ᵀ`, with its `ι` (an `ι`-compatible analytic uniformization `Φu` with kernel `Λ_τ`;
this part is `RayClassCFT.ModuliAtUnits`, verbatim) **and with the level structure**
`η(a) = Φu((1/3) ι(a w)(τ, 1)ᵀ)` for some `w ∈ 𝒪` with `w ≡ u⁻¹ mod 3𝒪̂`.

In Deligne's moduli description (Deligne 1971 §4; Milne ISV §8, PEL case), `[τ, g]` is the class of
`(ℂ²/ι(L_g)(τ, 1)ᵀ, ι, η_g)`, `L_g = B ∩ 𝒪̂ g⁻¹`, where `η_g` is the canonical identification
`B ⊗ 𝔸_f ≅ V_f(A_τ)`, `x ↦ ι(x)(τ, 1)ᵀ`, composed with right multiplication by `g⁻¹`. For `g = u ∈ 𝒪̂^×`,
`L_u = 𝒪` and on `(1/3)𝒪/𝒪` this is `a ↦ (1/3) ι(a u⁻¹)(τ, 1)ᵀ`. The inverse is forced by `DCRel`: for
`γ ∈ 𝒪^×`, `nrd γ > 0`, `k ∈ K₃`, the map `v ↦ j(γ, τ)⁻¹ v` is an `ι`-equivariant isomorphism
`ℂ²/Λ_τ → ℂ²/Λ_{γτ}` carrying `η_w` to `η_{wγ⁻¹}`, and `(γ u k)⁻¹ ≡ u⁻¹ γ⁻¹ mod 3`. Any `w ≡ u⁻¹` gives the same
`η` (`ι(3𝒪)(τ, 1)ᵀ/3 ⊆ Λ_τ`). -/
def ModuliLevelAtUnits (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
  ∀ u ∈ OhatU, ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (Ψ τ u) = M3.mk P ∧
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu ∧
      ∃ w : LeafQM.O, (∃ y ∈ OhatQ, bEmb (w : LeafQM.B) = ((u⁻¹ : BAQˣ) : BAQ) + 3 * y) ∧
        ∀ a : LeafQM.O, (Additive.toMul (P.e.eta a) : CPts P.A (RingHom.id ℂ)) =
          Φu ((1 / 3 : ℂ) • (qmMat (a * w)).mulVec ![(τ : ℂ), 1])

/-- **The moduli interpretation of `Sh_{K₃}(ℂ)` on a fine witness `(Y, Φ)`**: `Ψ` is onto `Y(ℂ)`, its fibres are
the `B^×_+ \ · / K₃` classes (`DCRel`), it is holomorphic in `τ` (`ShimuraSplit.IsHolFamily`), and its values at
`𝒪̂^×` are the QM tori with their level structures (`ModuliLevelAtUnits`). The first three clauses are those of
`RayClassCFT.DeligneBodyAt`, verbatim. -/
def ModuliInterpAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ y : fieldPt ℂ ⟶ Y, ∃ τ g, Ψ τ g = y) ∧
  (∀ τ g τ' g', Ψ τ g = Ψ τ' g' ↔ DCRel τ g τ' g') ∧
  (∀ g, ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ τ g).left)) ∧
  ModuliLevelAtUnits Y Φ Ψ

/-- **Shimura's reciprocity law at CM points for `Ψ`** (the last clause of `RayClassCFT.DeligneBodyAt`,
verbatim): for an imaginary quadratic `K`, an embedding `q : K → B` with CM point `z` (reflex embedding `κ` or its
conjugate, `δ`), and `σ ∈ Aut(ℂ)` acting on `K^ab` as `[s, K]`, `σ Ψ(z, g) = Ψ(z, q̂(s)^ε g)`. -/
def ReciprocityAt (Y : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
  ∃ (ε : ℤˣ) (δ : Bool),
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
      IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
    ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
    ∀ g : BAQˣ, galPt σ (Ψ z g) = Ψ z (qHatU q s ^ (ε : ℤ) * g)

/-! ## 2. The two new leaves -/

/-- **LEAF `DeligneModuliY3Every`: the moduli interpretation of `Sh_{K₃}(B^×, ℍ^±)(ℂ)` on the fine moduli scheme
`Y₃`** (one object: `Y₃(ℂ)` with its complex uniformization; no Galois action).

*Published statement* (locators recalled, UNVERIFIED; no network): for a PEL datum, the complex points of the
moduli scheme `M_K` are `G(ℚ) \ X × G(𝔸_f) / K`, `[x, g] ↦ (A_x, ι, λ_x, η_x ∘ g)`, an isomorphism of complex
analytic spaces (of algebraic varieties, by Borel's extension theorem / Baily–Borel): J. S. Milne, *Introduction
to Shimura varieties* (2005), §8 (PEL Shimura varieties as moduli; Thm 8.17 recalled); P. Deligne, *Travaux de
Shimura*, Sém. Bourbaki 389 (1971), §4 (moduli description); for quaternion algebras over `ℚ`, G. Shimura,
Ann. of Math. 85 (1967), §§2-3, and K. Buzzard, Duke Math. J. 87 (1997), §1 (`M_U(ℂ) = B^× \ (ℂ − ℝ) ×
(B ⊗ 𝔸_f)^× / U`). Here `G = B^×`, `B = (2, −3 | ℚ)`, `K = K₃`, `X = ℍ^±`.

*Lean form*: on every fine witness `(Y, Φ)` (`R1fpPropsAb`), some `Ψ` satisfies `ModuliInterpAt`.

*Form*: a **consequence**: `ℍ` with `B^×_+` replaces `ℍ^±` with `B^×`; the moduli clause is kept at
`g ∈ 𝒪̂^×` (`L_u = 𝒪`), which with `DCRel` and class number one (`(B ⊗ 𝔸_f)^× = B^×_+ 𝒪̂^×`) determines `Ψ`
everywhere; the analytic isomorphism is weakened to "bijective modulo `DCRel`, holomorphic in `τ`"; the moduli
point is read through the witness's `Φ`. -/
def DeligneModuliY3Every : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ →
    ∃ Ψ, ModuliInterpAt Y Φ Ψ

/-- **LEAF `DeligneReciprocityY3Every`: the moduli scheme `Y₃`, with its moduli interpretation, satisfies
Shimura's reciprocity law at CM points** (the canonical-model property; one object: `Y₃` with the Galois action
on its CM points; no existence claim).

*Published statement* (locators recalled, UNVERIFIED; no network): the PEL moduli scheme `M_K` over the reflex
field, with the identification of its complex points by the moduli interpretation, is the canonical model of
`Sh_K(G, X)`: at every special point `[x, g]`, `σ ∈ Aut(ℂ/E(T, x))` acts by `σ[x, g] = [x, r(T, x)(s) g]` for
`σ|E^ab = art(s)`. Milne, ISV §14 (the PEL moduli variety is a canonical model; via the main theorem of complex
multiplication, §12); Deligne, *Travaux de Shimura*, §§4-5 (Cor. 5.7 / Ex. 5.8 per docs/research/locators.md
row R1); Shimura, Ann. of Math. 85 (1967), Main Theorem I. Here `E(G, X) = ℚ`, `T = Res_{K/ℚ} 𝔾_m` through
`q : K → B`, `r(T, x)(s) = q̂(s)^{±1}`.

*Lean form*: on every fine witness `(Y, Φ)`, **every** `Ψ` with the moduli interpretation (`ModuliInterpAt`,
the hypothesis of the print: the identification by the moduli interpretation) satisfies `ReciprocityAt`.

*Form*: a **consequence**: specialized to the CM points of imaginary quadratic `K` with the reflex conventions
(`ε`, `δ`) existential, and read through `Φ`. `ModuliInterpAt` pins `Ψ`: the level structure at
`𝒪̂^×` fixes the moduli point `Φ(Ψ(τ, u))` (an analytic isomorphism of QM tori compatible with `ι` and `η` is
algebraic, GAGA), and `DCRel` with class number one extends this to all `g`, so `Ψ` is the moduli identification
of the print, up to nothing. -/
def DeligneReciprocityY3Every : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ →
    ∀ Ψ, ModuliInterpAt Y Φ Ψ → ReciprocityAt Y Ψ

/-! ## 3. The glue -/

/-- `1 ∈ 𝒪̂^×`. -/
theorem one_mem_OhatU : (1 : BAQˣ) ∈ OhatU :=
  ⟨by simpa using OhatQ_one, by simpa using OhatQ_one⟩

/-- The level clause forgets to `RayClassCFT.ModuliAtUnits`. -/
theorem moduliAtUnits_of_level {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : ModuliLevelAtUnits Y Φ Ψ) :
    ModuliAtUnits Y Φ Ψ := by
  intro u hu τ
  obtain ⟨P, hP, Φu, hunif, hiota, -⟩ := h u hu τ
  exact ⟨P, hP, Φu, hunif, hiota⟩

/-- **The moduli interpretation and reciprocity give the body of y3abu-print's leaf.** -/
theorem body_of_split {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (hI : ModuliInterpAt Y Φ Ψ) (hR : ReciprocityAt Y Ψ) :
    DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ := by
  obtain ⟨hsurj, hfib, hhol, hlev⟩ := hI
  have hU := moduliAtUnits_of_level hlev
  refine ⟨⟨hsurj, hfib, hhol, ⟨fun τ => hU 1 one_mem_OhatU τ, hhol 1⟩, hR⟩, hU⟩

/-- **The split leaves give y3abu-print's `DeligneCanonicalModelY3Every`.** -/
theorem deligneCanonicalModelY3Every_of_split (hI : DeligneModuliY3Every)
    (hR : DeligneReciprocityY3Every) : Y3ABUPrint.DeligneCanonicalModelY3Every := by
  intro Y Φ h1
  obtain ⟨Ψ, hΨ⟩ := hI Y Φ h1
  exact ⟨Ψ, body_of_split hΨ (hR Y Φ h1 Ψ hΨ)⟩

/-- **The discharge**: the field from `Y3FineModuliAb` and the two new leaves. -/
theorem shimuraMainThmIDeligneY3AbU_of_strict (hM : Y3ABUPrint.Y3FineModuliAb)
    (hI : DeligneModuliY3Every) (hR : DeligneReciprocityY3Every) :
    ShimuraMainThmIDeligneY3AbU :=
  Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print hM (deligneCanonicalModelY3Every_of_split hI hR)

end Y3ABUStrict

import ZInQKernel.Contrib.OneProof.H.PicZeroCharZeroCopy

/-! # c8-conrad: step C8 by the manuscript's own argument (local algebraicity and class field theory)

diophantine_zq.tex L758-764 (step C8 of `docs/research/h-trust.md`): the twisting character of Pan's theorem is a de
Rham (Hodge–Tate suffices) subrepresentation of a Hom representation, unramified outside finitely many primes; "Local
algebraicity [conrad-local-characters, Appendix B, pp. 32-33] and class field theory over ℚ" make it a finite
character times a power of the cyclotomic character; the weight comparison makes the power zero.

The chain's consumer at C8 is `HDec.G0Galois.G12DetPZ` (`ZInQKernel/Contrib/OneProof/H/PicZeroCharZeroCopy.lean`), today proved
from `DetTate` (`det V₅(A) = χ²`, from the Weil pairing, i.e. from the Picard rows `picRepresentableAbVar`,
`kleimanPicZeroProper954SiteQ`). This file proves `G12DetPZ` instead from

* `ConradAppBQp` — Conrad's Appendix B in the case of base field `ℚ_p` (the only case C8 uses), over Tau Ceti's local
  Artin map of `ℚ_p` (`TauCeti.ClassFieldTheory.artinMap`);
* three glue Props: `TwistCharHT0` (the twisting character is Hodge–Tate of weight `0` at 5 and unramified almost
  everywhere), `LocAlgExponentEqWeight` (the exponent of a locally algebraic character is its Hodge–Tate weight),
  `FiniteOfLocAlgTrivialQ` (class field theory over `ℚ`: a character trivial near `1` on local Artin symbols of
  `ℤ_p^×` and unramified almost everywhere has finite image);
* the chain's own G9 inputs (`G9GlueNoT23` and `PkgI4.DeRhamComparison`), which give the weights `{0, −1}` of `r`.

No statement of the chain is changed. -/

set_option linter.style.longLine false



noncomputable section

namespace HDec.G0Galois.C8Conrad

open _root_.PkgI4 (GaloisRep GaloisChar)

/-! ## §1. The local Artin map of `ℚ_p` and locally algebraic characters (Conrad, Def. B.1, base field `ℚ_p`) -/

section Local

variable (p : ℕ) [Fact p.Prime]

/-- A unit of `ℤ_p` as a unit of `ℚ_p`. -/
def unitsQp (u : ℤ_[p]ˣ) : ℚ_[p]ˣ := Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom u

/-- `σ ∈ G_{ℚ_p}` represents the local Artin symbol of `x ∈ ℚ_p^×`: its class in the topological abelianization of
`G_{ℚ_p}` is Tau Ceti's absolute local Artin map at `x` (normalization: `χ_cyc(Art(p^k u)) = u⁻¹`, Tau Ceti's
`abelianizedLocalCyclotomicCharacter_artinMap_padic`). -/
def IsArtinLift (σ : PkgI4.GQp p) (x : ℚ_[p]ˣ) : Prop :=
  (QuotientGroup.mk (show Field.absoluteGaloisGroup ℚ_[p] from σ) : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = TauCeti.ClassFieldTheory.artinMap ℚ_[p] x

variable {p}

/-- A character `ψ : G_{ℚ_p} → E^×` as the one-dimensional `E`-linear representation (as `PkgI4.cycRep`). -/
def charRep {E : Type*} [Field E] (ψ : PkgI4.GQp p →* Eˣ) : PkgI4.GQp p →* GL (Fin 1) E :=
  (Units.map (algebraMap E (Matrix (Fin 1) (Fin 1) E)).toMonoidHom).comp ψ

variable (p)

/-- **Locally algebraic of exponent `n`** (Conrad, Def. B.1, for the base field `ℚ_p`: the only algebraic characters
of `Res_{ℚ_p/ℚ_p} 𝔾_m = 𝔾_m` are `x ↦ x^n`): `ψ ∘ Art_{ℚ_p}` agrees with `x ↦ x^n` on an open subgroup of `ℤ_p^×`,
here `1 + p^k ℤ_p`. -/
def IsLocallyAlgebraic {E : Type*} [Field E] [Algebra ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) : Prop :=
  ∃ k : ℕ, ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : PkgI4.GQp p,
    IsArtinLift p σ (unitsQp p u) → ((ψ σ : Eˣ) : E) = (algebraMap ℚ_[p] E ((u : ℤ_[p]) : ℚ_[p])) ^ n

end Local

/-! ## §2. The leaf: Conrad, Appendix B, base field `ℚ_p` -/

/-- **LEAF candidate (printed-form instance; unrefereed preprint).** B. Conrad, *Lifting global representations with
local properties*, author preprint, December 11, 2011, Appendix B, pp. 32-33 (the manuscript's citation
`conrad-local-characters`, diophantine_zq.tex L761, L11046-11049): the paragraph after Definition B.1, "a continuous
character with values in a finite extension of `ℚ_p` is locally algebraic exactly when its underlying
`ℚ_p`-representation is Hodge–Tate" (as reported by the theorem-application audit,
`docs/theorem-application-audit/evidence/parallel-galois-height-report.md` L102; not read on this host), in the case
of base field `L = ℚ_p`, direction Hodge–Tate ⇒ locally algebraic. Coefficient field: a finite extension `E/ℚ_p` inside
`ℚ̄_p`. Hodge–Tate is the project's `PkgI4.HasHTWeights` with a single weight `w` (that is, `dim_{ℚ_p} H_{−w} ≥ [E:ℚ_p]`,
which forces the underlying `ℚ_p`-representation to be Hodge–Tate by the Serre–Tate inequality `Σᵢ dim Hᵢ ≤ [E:ℚ_p]`:
a dictionary step, so this Lean form is a consequence of the printed statement, not verbatim). -/
def ConradAppBQp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ), Continuous (fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p)) →
    (∃ w : ℤ, PkgI4.HasHTWeights p (charRep ψ) {w}) → ∃ n : ℤ, IsLocallyAlgebraic p ψ n

/-! ## §3. Glue -/

instance fact_five' : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `ψ` is unramified at `q`: every inertia group above `q` lies in its kernel (as `PkgI4.GaloisRep.UnramifiedAt`). -/
def CharUnramifiedAt {ℓ : ℕ} [Fact ℓ.Prime] (ψ : GaloisChar ℓ) (q : ℕ) : Prop :=
  ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v q →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ψ.toHom ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = 1

/-- **GLUE (C8, first sentence of N5 L758-760: the twisting character is Hodge–Tate, of weight `0` after the weight
comparison, and unramified outside finitely many primes).** If `r : G_ℚ → GL₂(ℚ̄₅)` has Hodge–Tate weights `{0, −1}`
at 5 and is attached up to the twist `ψ` (outside `S`) to a normalized eigenform `g` of weight 2, then `ψ` is
unramified outside a finite set, and `ψ|G_{ℚ₅}` takes values in a finite `E/ℚ₅` and is Hodge–Tate of weight `0` as
an `E`-character. Proof plan (A), for semisimple `r` (the consumer's `r` is irreducible): R14 gives a semisimple
`ρ_g` (`EigenformRepExists`), Chebotarev and Brauer–Nesbitt (`AttachedConj`, proved in TailS §13) give `r ≅ ψ ⊗ ρ_g`, so
`ψ` is unramified wherever `r` and `ρ_g` are; R13 (`EigenformHT`) gives `ρ_g` the weights `{0, −1}`; `HTCharOfTwist`
(TailS, GLUE S1) makes `ψ` Hodge–Tate of some weight `s`, and `HTTwistShift` with `HTWeightsUnique` (proved) give
`{0, −1} = {s, s − 1}`, so `s = 0`. Plan (B), with no semisimplicity: `det r = ε_g χ_cyc ψ²` (R14's determinant clause and
Chebotarev, as in `g12Det_of`), `det r` is Hodge–Tate of weight `−1` (the sum of the weights of `r`), so `ψ²` has Sen
weight `0`, hence `ψ` too, and a character with Sen operator `0` is Hodge–Tate of weight `0` (Sen 1980); `ψ²` is
unramified outside a finite set and `ψ` composed with `O_E^× → O_E^×/U` (`U` open, pro-5, torsion-free) has open kernel,
so `ψ` is unramified outside a finite set. In both plans a continuous character of the compact `G_{ℚ₅}` has values in a
finite extension (Baire). -/
def TwistCharHT0 : Prop :=
  HSyn.EigenformRepExists → PkgI4.EigenformHT →
  ∀ (r : GaloisRep 5 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ),
    0 < N → PkgI4.IsNormalizedEigenform g χ →
    PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    (∃ T : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ T → CharUnramifiedAt ψ q) ∧
    ∃ (E : IntermediateField ℚ_[5] (PadicAlgCl 5)) (_ : FiniteDimensional ℚ_[5] E) (ψE : PkgI4.GQp 5 →* Eˣ),
      (∀ σ, (((ψE σ : Eˣ) : E) : PadicAlgCl 5) = ((ψ.toHom (PkgI4.decomp 5 σ) : (PadicAlgCl 5)ˣ) : PadicAlgCl 5)) ∧
      PkgI4.HasHTWeights 5 (charRep ψE) {0}

/-- **GLUE (C8, "removing its integral local Hodge–Tate weight", N5 L763-764; STANDARD: Serre 1968 Ch. III App.,
Tate 1967 §3.3).** The exponent of a locally algebraic character of `G_{ℚ_p}` is its Hodge–Tate weight (in the
convention where `χ_cyc` has weight `−1`; with `χ_cyc(Art(u)) = u⁻¹`, `χ_cyc^{-w}` has weight `w` and is `u ↦ u^w` on
Artin symbols of units). On-the-spot sketch: if `ψ(Art u) = u^n` on `1 + p^kℤ_p`, then `φ = ψ χ_cyc^{n}` is trivial on
an open subgroup of the inertia group of `G_{ℚ_p}^{ab}` (the closure of `Art(ℤ_p^×)`), so `φ` is a finite character
times an unramified one; both have Hodge–Tate weight `0` (Ax–Sen–Tate and Hilbert 90), so `ψ = φ χ^{−n}` has weight
`n`, and a Hodge–Tate character has one weight. -/
def LocAlgExponentEqWeight : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) (w n : ℤ), Continuous (fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p)) →
    PkgI4.HasHTWeights p (charRep ψ) {w} → IsLocallyAlgebraic p ψ n → n = w

/-- **GLUE (C8, "class field theory over ℚ", N5 L761-765: "finite inertia at five and at every other prime, hence a
finite ray-class character").** A continuous `ψ : G_ℚ → ℚ̄_p^×`, unramified outside a finite set, which is trivial on
the local Artin symbols (through `decomp`) of the units `1 + p^kℤ_p`, has finite image. Proof plan: `ψ` factors through
`G_ℚ^{ab} ≅ ℤ̂^×` (Kronecker–Weber, proved: `ZInQKernel/Contrib/KroneckerWeber`); the image of the inertia at `q`
is `ℤ_q^×`, on which `ψ` is trivial for `q` outside the finite set; at `q = p` the hypothesis and Tau Ceti's
`localArtinMap_cyclotomic_padic_primePow` (Artin symbols of units act on `μ_{p^∞}` by `u⁻¹`) make `ψ` trivial on
`1 + p^kℤ_p`; at `q ≠ p` the image of `ℤ_q^×` (virtually pro-`q`) in the virtually pro-`p` group `O_E^×` is finite
(rv-h-c8 §4 item 3: N5 states this without argument; elementary). So `ψ` is trivial on an open subgroup of `ℤ̂^×`. -/
def FiniteOfLocAlgTrivialQ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ψ : GaloisChar p),
    (∃ T : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ T → CharUnramifiedAt ψ q) →
    (∃ k : ℕ, ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : PkgI4.GQp p,
      IsArtinLift p σ (unitsQp p u) → ψ.toHom (PkgI4.decomp p σ) = 1) →
    (Set.range ψ.toHom).Finite

/-- **C8's conclusion, the finiteness of the twist** (what the consumer `G12DetPZ` needs; N5 L758-766). -/
def C8TwistFinite : Prop :=
  ∀ (r : GaloisRep 5 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ),
    0 < N → PkgI4.IsNormalizedEigenform g χ →
    PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    (Set.range ψ.toHom).Finite

/-! ## §4. Proofs -/

/-- **C8 from Conrad's Appendix B and the glue** (N5 L758-766). -/
theorem c8TwistFinite_of_conrad (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (hC : ConradAppBQp) (hT : TwistCharHT0) (hW : LocAlgExponentEqWeight) (hF : FiniteOfLocAlgTrivialQ) :
    C8TwistFinite := by
  intro r N χ g ψ ιC ιL S hN hg hr hatt
  obtain ⟨hram, E, hE, ψE, hlift, hwt⟩ := hT hR hHT r N χ g ψ ιC ιL S hN hg hr hatt
  -- continuity of `ψE`, through `ψ ∘ decomp`
  have hcont : Continuous (fun σ => (((ψE σ : Eˣ) : E) : PadicAlgCl 5)) := by
    have h1 : Continuous (fun σ : PkgI4.GQp 5 => ((ψ.toHom (PkgI4.decomp 5 σ) : (PadicAlgCl 5)ˣ) : PadicAlgCl 5)) :=
      Units.continuous_val.comp (ψ.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[5])).continuous)
    exact (funext hlift : _) ▸ h1
  obtain ⟨n, hn⟩ := hC 5 E ψE hcont ⟨0, hwt⟩
  have hn0 : n = 0 := hW 5 E ψE 0 n hcont hwt hn
  subst hn0
  obtain ⟨k, hk⟩ := hn
  refine hF 5 ψ hram ⟨k, fun u hu σ hσ => ?_⟩
  have h := hk u hu σ hσ
  rw [zpow_zero] at h
  apply Units.ext
  rw [← hlift σ, h]
  simp

/-- **The consumer `G12DetPZ` from C8's conclusion and the chain's G9 inputs.** Once `ψ` has finite image, the
determinant identities hold trivially (`H = ker ψ`, `det r := ψ²`, `ε = χ_cyc := 1`): `G12DetPZ` carries no more
information than the finiteness of `ψ`. -/
theorem g12DetPZ_of_twistFinite (hC8 : C8TwistFinite) (h9 : G9GlueNoT23) (hdR : PkgI4.DeRhamComparison) :
    G12DetPZ := by
  intro _ K _ _ A r e N χ g ψ ιC ιL S hdim hint hN hg hatt
  have hr : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1} := (h9 hdR K A 5 r e hdim hint).2
  have hfin : (Set.range ψ.toHom).Finite := hC8 r N χ g ψ ιC ιL S hN hg hr hatt
  have : Finite (ψ.toHom.range) := by
    rw [← MonoidHom.coe_range] at hfin
    exact hfin.to_subtype
  refine ⟨ψ.toHom.ker, inferInstance, ψ.toHom ^ 2, 1, 1, fun x => ?_, fun h hh => ?_, ?_⟩
  · simp
  · rw [MonoidHom.mem_ker] at hh
    simp [hh]
  · exact Set.finite_range_const.subset (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)

/-- **`G12DetPZ` from Conrad's Appendix B** (with the three glue Props and the chain's R13, R14 and G9 inputs): the
determinant argument, hence `DetTate` and the Weil pairing, is not used. -/
theorem g12DetPZ_of_conrad (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (hC : ConradAppBQp) (hT : TwistCharHT0) (hW : LocAlgExponentEqWeight) (hF : FiniteOfLocAlgTrivialQ)
    (h9 : G9GlueNoT23) (hdR : PkgI4.DeRhamComparison) : G12DetPZ :=
  g12DetPZ_of_twistFinite (c8TwistFinite_of_conrad hR hHT hC hT hW hF) h9 hdR

end HDec.G0Galois.C8Conrad

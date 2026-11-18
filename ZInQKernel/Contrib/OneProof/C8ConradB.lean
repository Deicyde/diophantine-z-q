import ZInQKernel.Contrib.OneProof.C8CFT

/-! # conrad-b3: step C8's weight comparison from Conrad's App. B (Prop. B.3), Tate 1967 off the route

diophantine_zq.tex L760-764: "Local algebraicity [conrad-local-characters, Appendix B, pp. 32-33] and class field
theory over ℚ make it a finite character times an integral power of the cyclotomic character: removing its integral
local Hodge–Tate weight …". c8-conrad2 proved the weight comparison `LocAlgExponentEqWeight` (`C8Conrad.lean`) from
`TateTwistInvariantsInertia` (Tate 1967 §3.3 Thm 2 over `\hat{K^{ur}}`, a source the manuscript does not cite). This
file proves it instead from Conrad's Prop. B.3 (App. B, p. 33, the manuscript's own citation), specialised to the base
field `L = ℚ_p` and stated in Conrad's conventions (`ConradPropB3Qp`):

* Conrad's Artin map is arithmetically normalized (p. 32), as Tau Ceti's (`IsArtinLift`: uniformizers go to arithmetic
  Frobenius, `TauCeti.ClassFieldTheory.isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer`, and `χ_cyc(Art u) = u⁻¹`
  for `u ∈ ℤ_p^×`, `cyc_of_isArtinLift`);
* Conrad's local algebraicity has exponent `n` when `ψ ∘ r_L` is `x ↦ x^{-n}` near `1` (p. 33, `L = ℚ_p`: one
  embedding `τ`), `IsLocallyAlgebraicConrad`; the project's `IsLocallyAlgebraic p ψ n` (`x ↦ x^n`) is Conrad's exponent
  `-n` (`isLocallyAlgebraic_iff_conrad`, definitional);
* Conrad's Hodge–Tate weights give `χ_cyc` the weight `+1` (p. 33: `V_σ = ℂ_L(w_σ)`); the multiplicity of the Conrad
  weight `w` of the underlying `ℚ_p`-representation is `dim_{ℚ_p} (ℂ_p(w) ⊗ V^∨)^{G_{ℚ_p}} = dim_{ℚ_p} H_w`
  (`conradHTMult`), and the project's `htMult` (weight of `χ_cyc` is `−1`) is `htMult w = conradHTMult (−w) / [E:ℚ_p]`
  (`htMult_eq_conradHTMult_neg`, definitional).

`ConradAppB` merges the two Conrad leaves of the C8 reroute: c8-conrad's `ConradAppBQp` (p. 32, Hodge–Tate ⇒ locally
algebraic) and `ConradPropB3Qp` (Prop. B.3, p. 33, the weight is the exponent). `c8TwistFinite_of_conradB` is C8 from
`ConradAppB` alone (with R13, R14 and the three proved glue Props). -/

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad

open Module

section Conventions

variable (p : ℕ) [Fact p.Prime]

/-- **Locally algebraic of exponent `n` in Conrad's normalization** (Conrad, *Lifting global representations with local
properties*, author preprint Dec. 11, 2011, App. B, p. 33, for the base field `L = ℚ_p`, whose only embedding is the
identity): near `1`, `ψ ∘ r_{ℚ_p}` agrees with `x ↦ x^{-n}`, where `r_{ℚ_p}` is the arithmetically normalized local
Artin map (p. 32; here Tau Ceti's, through `IsArtinLift`). "Near `1`" is read on the open subgroups `1 + p^k ℤ_p`,
which form a basis of neighbourhoods of `1` in `ℚ_p^×`. -/
def IsLocallyAlgebraicConrad {E : Type*} [Field E] [Algebra ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) : Prop :=
  ∃ k : ℕ, ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : PkgI4.GQp p,
    IsArtinLift p σ (unitsQp p u) → ((ψ σ : Eˣ) : E) = (algebraMap ℚ_[p] E ((u : ℤ_[p]) : ℚ_[p])) ^ (-n)

/-- **Multiplicity of the Hodge–Tate weight `w` in Conrad's convention** (`χ_cyc` has weight `+1`; Conrad App. B p. 33:
`ℂ_L ⊗ V = ⊕ V_σ` with `V_σ ≅ ℂ_L(w_σ)`, and `{w_σ}` is the set of Hodge–Tate weights) of the underlying
`ℚ_p`-representation of `ρ`: `dim_{ℚ_p} H_w(ρ)`, where `H_w(ρ) = (ℂ_p(w) ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}` is the project's
`htSpace` (equivariant `ℚ_p`-linear maps `V → ℂ_p(w)`). Check: for `V = ℚ_p(1)`, `H_w ≠ 0` iff `w = 1` (`htMult`'s
docstring, by Tate's theorem), i.e. `χ_cyc` has Conrad weight `+1`. Dictionary: if `ℂ_p ⊗_{ℚ_p} V ≅ ⊕_σ ℂ_p(w_σ)` then
`H_w ≅ ⊕_σ ℂ_p(w − w_σ)^{G_{ℚ_p}}`, of `ℚ_p`-dimension `#{σ : w_σ = w}` (Tate's two theorems over `ℚ_p`, both proved in
the tree: `CloudB3W11.tateTwistInvariants_proof`, `CloudB3W11.axSenTate_proof`). -/
def conradHTMult {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {m : ℕ}
    (ρ : PkgI4.GQp p →* GL (Fin m) E) (w : ℤ) : ℕ :=
  finrank ℚ_[p] (PkgI4.htSpace p ρ w)

/-- **The exponent translation** (definitional): the project's exponent `n` (`ψ(Art u) = u^n`) is Conrad's exponent
`−n` (`ψ(r(u)) = u^{−(−n)}`). -/
theorem isLocallyAlgebraic_iff_conrad {E : Type*} [Field E] [Algebra ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) :
    IsLocallyAlgebraic p ψ n ↔ IsLocallyAlgebraicConrad p ψ (-n) := by
  unfold IsLocallyAlgebraic IsLocallyAlgebraicConrad
  simp only [neg_neg]

/-- **The weight-sign translation** (definitional): the project's multiplicity of the weight `w` (Tate convention,
`χ_cyc` of weight `−1`) is Conrad's multiplicity of `−w`, divided by `[E : ℚ_p]` (from `ℚ_p`- to `E`-dimension). -/
theorem htMult_eq_conradHTMult_neg {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {m : ℕ}
    (ρ : PkgI4.GQp p →* GL (Fin m) E) (w : ℤ) :
    PkgI4.htMult p ρ w = conradHTMult p ρ (-w) / finrank ℚ_[p] E :=
  rfl

/-- `[E : ℚ_p] > 0` for a finite intermediate field (as in `htMult_eq_finrank_Ysp`). -/
theorem finrank_pos_intermediateField (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] :
    0 < finrank ℚ_[p] E := by
  have : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
  exact (finrank_pos_iff_of_free ℚ_[p] E).2 inferInstance

end Conventions

/-- **LEAF candidate, CITED (diophantine_zq.tex L760-762; Conrad, *Lifting global representations with local
properties*, author preprint, December 11, 2011, App. B, p. 33, Prop. B.3 (proof pp. 33-34); bibitem
`conrad-local-characters`, L11046-11049; flag: AI page read 11-17, unrefereed preprint, the manuscript's own
citation).** Prop. B.3 says that for a locally algebraic `ψ` the Hodge–Tate weight `w_σ` equals `n_i`, for the factor
`i` through which `σ ⊗ 1` factors. Specialised to the base field `L = ℚ_p` (one embedding, one factor, one exponent
`n`) and a coefficient field `E/ℚ_p` finite inside `ℚ̄_p`, in Conrad's conventions (arithmetic Artin map; `χ_cyc` of
weight `+1`): if `ψ : G_{ℚ_p} → E^×` is continuous and `ψ ∘ r_{ℚ_p}` is `x ↦ x^{-n}` near `1`, then every one of the
`[E : ℚ_p]` Hodge–Tate weights `w_σ` of the underlying `ℚ_p`-representation is `n`, i.e. `conradHTMult n = [E : ℚ_p]`.
The Lean conclusion is a consequence of the printed one: `ℂ_p ⊗_{ℚ_p} V ≅ ℂ_p(n)^{[E:ℚ_p]}` gives
`H_n ≅ (ℂ_p^{G_{ℚ_p}})^{[E:ℚ_p]} = ℚ_p^{[E:ℚ_p]}` (Ax–Sen–Tate over `ℚ_p`, proved in the tree as
`CloudB3W11.axSenTate_proof`). -/
def ConradPropB3Qp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ), Continuous (fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p)) →
    IsLocallyAlgebraicConrad p ψ n → conradHTMult p (charRep ψ) n = finrank ℚ_[p] E

/-- **LEAF candidate, CITED: Conrad's App. B for the base field `ℚ_p`** (diophantine_zq.tex L760-762, "[Appendix B,
pp. 32-33]{conrad-local-characters}"): p. 32 (`ConradAppBQp`: a Hodge–Tate character is locally algebraic) and p. 33,
Prop. B.3 (`ConradPropB3Qp`: its Hodge–Tate weight is the exponent). Flags: unrefereed author preprint (the
manuscript's own citation); p. 32's Hodge–Tate ⇒ locally algebraic paragraph as reported by the theorem-application
audit, Prop. B.3 by the AI page read of 11-17. -/
def ConradAppB : Prop :=
  ConradAppBQp ∧ ConradPropB3Qp

/-- **`LocAlgExponentEqWeight` from Conrad's Prop. B.3** (the manuscript's "removing its integral local Hodge–Tate
weight", diophantine_zq.tex L763-764). With the project's exponent `n` (Conrad's `−n`), Prop. B.3 gives
`conradHTMult (−n) = [E : ℚ_p]`, i.e. `htMult n = 1`; the single weight `w` of `ψ` then equals `n`. -/
theorem locAlgExponentEqWeight_of_conradPropB3 (hB3 : ConradPropB3Qp) : LocAlgExponentEqWeight := by
  intro p _ E _ ψ w n hcont hHT hLA
  have hC := hB3 p E ψ (-n) hcont ((isLocallyAlgebraic_iff_conrad p ψ n).1 hLA)
  have hd : 0 < finrank ℚ_[p] E := finrank_pos_intermediateField p E
  have h1 : PkgI4.htMult p (charRep ψ) n = 1 := by
    rw [htMult_eq_conradHTMult_neg, hC]
    exact Nat.div_self hd
  rw [hHT n] at h1
  by_contra hne
  rw [Multiset.count_singleton] at h1
  simp [hne] at h1

/-- `LocAlgExponentEqWeight` from the merged Conrad leaf. -/
theorem locAlgExponentEqWeight_of_conradAppB (hC : ConradAppB) : LocAlgExponentEqWeight :=
  locAlgExponentEqWeight_of_conradPropB3 hC.2

/-- **C8 from Conrad's App. B (pp. 32-33, base field `ℚ_p`), the two inertia dictionaries and `TwistCharHTWt0`**
(c8-conrad2's `c8TwistFinite_of_leaves` with Tate's theorem over `\hat{K^{ur}}` replaced by Conrad's Prop. B.3). -/
theorem c8TwistFinite_of_conradB (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (hC : ConradAppB) (hT : TwistCharHTWt0) (hB : InertiaAtPDecomp) (hM : MinkowskiInertiaQ) : C8TwistFinite := by
  intro r N χ g ψ ιC ιL S hN hg hr hatt
  obtain ⟨E, hE, ψE, hlift, hwt⟩ := hT hR hHT r N χ g ψ ιC ιL S hN hg hr hatt
  have hcont : Continuous (fun σ => (((ψE σ : Eˣ) : E) : PadicAlgCl 5)) := by
    have h1 : Continuous (fun σ : PkgI4.GQp 5 => ((ψ.toHom (PkgI4.decomp 5 σ) : (PadicAlgCl 5)ˣ) : PadicAlgCl 5)) :=
      Units.continuous_val.comp (ψ.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[5])).continuous)
    exact (funext hlift : _) ▸ h1
  obtain ⟨n, hn⟩ := hC.1 5 E ψE hcont ⟨0, hwt⟩
  have hn0 : n = 0 := locAlgExponentEqWeight_of_conradAppB hC 5 E ψE 0 n hcont hwt hn
  subst hn0
  obtain ⟨k, hk⟩ := hn
  refine finiteOfLocAlgTrivialQNoRam_of_dicts hB hM 5 ψ ⟨k, fun u hu σ hσ => ?_⟩
  have h := hk u hu σ hσ
  rw [zpow_zero] at h
  apply Units.ext
  rw [← hlift σ, h]
  simp

end HDec.G0Galois.C8Conrad

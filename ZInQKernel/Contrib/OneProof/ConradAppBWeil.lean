import ZInQKernel.Contrib.CloudB3E1ConradTori.WeilTorus

/-!
# Conrad's Appendix B as printed: Definition B.1 over tori, and Proposition B.3 under Hodge–Tate

Step C8, sec:height, diophantine_zq.tex L760–764: "Local algebraicity [conrad-local-characters,
Appendix B, pp. 32–33] and class field theory over ℚ make it a finite character times an integral
power of the cyclotomic character". The source is Brian Conrad, *Lifting global representations with
local properties*, author preprint dated December 11, 2011, Appendix B, pp. 32–34. Bibitem
`conrad-local-characters`, L11046–11049.

This file states the print's two statements for the local base `L = ℚ_p`, with Conrad's own
definitions, as the leaf `ConradAppBWeil`:

* `ConradLocAlgIffHT` (p. 32, the paragraph after Definition B.1): a continuous character
  `ψ : G_{ℚ_p}^{ab} → K^×` is locally algebraic if and only if its underlying `ℚ_p`-linear
  representation is Hodge–Tate. Local algebraicity is Definition B.1 itself
  (`IsLocallyAlgebraicWeil`): a `ℚ_p`-homomorphism of tori `G_m → R_{K/ℚ_p} G_m`
  (`WeilTorus.WeilTorusHom`) whose restriction to `ℚ_p`-points agrees with `ψ ∘ r_{ℚ_p}` near 1.
  Hodge–Tate is the decomposition of `ℂ_p ⊗_{ℚ_p} V` into semilinear lines `ℂ_p(w)`
  (`HTLines`), Conrad's p. 33 description, one line for each of the `[K : ℚ_p]` embeddings.
* `ConradB3HT` (p. 33, Proposition B.3, "with notation as above", i.e. for Hodge–Tate `ψ`): if
  `ψ` is Hodge–Tate and `ψ ∘ r_{ℚ_p}` agrees near 1 with the display (B.1), which for `L = ℚ_p`
  (one factor field `K ⊗_{ℚ_p} ℚ_p = K`, `N_{K/K} = id`) reads `x ↦ x^{-n}`, then every
  Hodge–Tate weight `w_σ` equals `n`: `ℂ_p ⊗ V` is a sum of `[K : ℚ_p]` copies of `ℂ_p(n)`
  (`PureHT`, Conrad's sign, `χ_cyc` of weight `+1`).

The arithmetic normalization of the Artin map (p. 32) is Tau Ceti's (`IsArtinLift`). `K` is any
finite extension of `ℚ_p` inside `ℚ̄_p`. The lines `V_σ` of p. 33 are read as a semilinear
decomposition, since for `K ≠ ℚ_p` the eigenlines of the `K`-action are permuted by `G_{ℚ_p}`.

Proved here (the bridges, kind PROVED):

* `conradNearOnePrint_of_weil`: `ConradLocAlgIffHT → ConradNearOnePrint`. A torus homomorphism is
  a power on `ℚ_p`-points (`WeilTorus.weilTorusHom_pow`).
* `conradB3Print_of_weil`: `ConradAppBWeil → ConradB3Print`. The display gives the torus
  homomorphism `x ↦ (1 ⊗ x)^{-n}` (`WeilTorus.powTorusHom`), hence Hodge–Tate by p. 32, and B.3
  applies.
* `conradAppBPrint_of_weil : ConradAppBWeil → ConradAppBPrint` and
  `conradAppB_of_weil : ConradAppBWeil → ConradAppB`.

Kinds: the leaf `ConradAppBWeil` is CITED (the manuscript's citation; an unrefereed author
preprint), printed form at `L = ℚ_p`; the rest is definitions and PROVED.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Bridges

open Module
open scoped TensorProduct Topology Filter
open HDec.G0Galois.C8Conrad.WeilTori

variable (p : ℕ) [Fact p.Prime]

/-- **Locally algebraic, Conrad's Definition B.1** (App. B, p. 32), for the local base `ℚ_p`:
there is a `ℚ_p`-homomorphism of tori `G_m → R_{K/ℚ_p} G_m` whose restriction to `ℚ_p`-points
agrees with `ψ ∘ r_{ℚ_p}` near 1, where `ψ` is read on the topological abelianization and
`r_{ℚ_p}` is the arithmetic Artin map. Kind: definition. -/
def IsLocallyAlgebraicWeil {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ψ : PkgI4.GQp p →* Kˣ) (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))) :
    Prop :=
  ∃ χ : WeilTorusHom p K, ∀ᶠ x : ℚ_[p]ˣ in 𝓝 1,
    ((conradAbelianChar p ψ hc (TauCeti.ClassFieldTheory.artinMap ℚ_[p] x) : Kˣ) : K) =
      χ.onPoints x

/-- **Hodge–Tate in Conrad's line form** (App. B, p. 33): `ℂ_p ⊗_{ℚ_p} V` (for `V = K` via `ψ`)
is a direct sum of `[K : ℚ_p]` semilinear lines `ℂ_p(w_j)` (Conrad's sign: `ℂ_p(w)` has the
action `χ^w · σ`); the `w_j` are the Hodge–Tate weights. Kind: definition. -/
def HTLines {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) : Prop :=
  ∃ (wt : Fin (finrank ℚ_[p] E) → ℤ)
    (e : (ℂ_[p] ⊗[ℚ_[p]] (Fin 1 → E)) ≃ₗ[ℂ_[p]] (Fin (finrank ℚ_[p] E) → ℂ_[p])),
    ∀ (σ : PkgI4.GQp p) (a : ℂ_[p]) (v : Fin 1 → E) j,
      e ((PkgI4.cpAct p σ a) ⊗ₜ[ℚ_[p]]
          ((charRep ψ σ : Matrix (Fin 1) (Fin 1) E).mulVec v)) j =
        PkgI4.cycPow p σ (wt j) • PkgI4.cpAct p σ (e (a ⊗ₜ[ℚ_[p]] v) j)

/-- A pure splitting is a Hodge–Tate decomposition with constant weights. Kind: PROVED. -/
theorem htLines_of_pureHT {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    {ψ : PkgI4.GQp p →* Eˣ} {i : ℤ} (h : PureHT p ψ i) : HTLines p ψ := by
  obtain ⟨e, he⟩ := h
  exact ⟨fun _ => i, e, he⟩

/-- **CITED** (C8, diophantine_zq.tex L760–762; Conrad, author preprint Dec. 11, 2011, App. B,
p. 32, the paragraph after Definition B.1, attributed there to Tate, [S6, III, A6, Cor. 2]): for
the local base `ℚ_p` and a finite extension `K` of `ℚ_p`, a continuous character
`ψ : G_{ℚ_p} → K^×` is locally algebraic (Definition B.1, tori) if and only if its underlying
`ℚ_p`-linear representation is Hodge–Tate. Kind: PRINT (printed form at `L = ℚ_p`). -/
def ConradLocAlgIffHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))),
    IsLocallyAlgebraicWeil p ψ hc ↔ HTLines p ψ

/-- **CITED** (C8, diophantine_zq.tex L760–764; Conrad, same preprint, App. B, p. 33,
Proposition B.3, proof pp. 33–34): for the local base `ℚ_p` and a finite extension `K` of `ℚ_p`,
if `ψ` is Hodge–Tate (the standing assumption "with notation as above", p. 32) and `ψ ∘ r_{ℚ_p}`
agrees near 1 with the display (B.1), here `x ↦ x^{-n}` (one factor field `K`), then every
Hodge–Tate weight is `n`. Kind: PRINT (printed form at `L = ℚ_p`). -/
def ConradB3HT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))),
    HTLines p ψ → ArtinNearOnePrint p ψ hc n → PureHT p ψ n

/-- **CITED: Conrad, Appendix B, pp. 32–34, as printed, at the local base `ℚ_p`**
(diophantine_zq.tex L760–764): the p. 32 equivalence with Definition B.1 over tori, and
Proposition B.3 for Hodge–Tate `ψ`. Kind: PRINT (unrefereed author preprint, the manuscript's own
citation). -/
def ConradAppBWeil : Prop :=
  ConradLocAlgIffHT ∧ ConradB3HT

/-- **The p. 33 near-one display from Definition B.1** (C8, L760–762): `ConradNearOnePrint`
follows from the p. 32 equivalence, since a torus homomorphism `G_m → R_{K/ℚ_p} G_m` is a power
on `ℚ_p`-points. Kind: PROVED. -/
theorem conradNearOnePrint_of_weil (h : ConradLocAlgIffHT) : ConradNearOnePrint := by
  intro p _ K _ _ ψ i hc hP
  obtain ⟨χ, hχ⟩ := (h p K ψ hc).mpr (htLines_of_pureHT p hP)
  obtain ⟨m, hm⟩ := weilTorusHom_pow p χ
  refine ⟨-m, ?_⟩
  unfold ArtinNearOnePrint
  filter_upwards [hχ] with x hx
  rw [hx, hm x, neg_neg]

/-- **Proposition B.3 in the old form from the print** (C8, L760–764): `ConradB3Print` follows
from the leaf. The display gives the torus homomorphism `x ↦ (1 ⊗ x)^{-n}`, so `ψ` is Hodge–Tate
by p. 32, and B.3 applies. Kind: PROVED. -/
theorem conradB3Print_of_weil (h : ConradAppBWeil) : ConradB3Print := by
  intro p _ K _ _ ψ n hc hn
  refine h.2 p K ψ n hc ((h.1 p K ψ hc).mp ⟨powTorusHom p K (-n), ?_⟩) hn
  have hn' := hn
  unfold ArtinNearOnePrint at hn'
  filter_upwards [hn'] with x hx
  rw [hx, powTorusHom_onPoints]

/-- **`ConradAppBPrint` from Conrad's Appendix B as printed** (C8, L760–764). Kind: PROVED. -/
theorem conradAppBPrint_of_weil (h : ConradAppBWeil) : ConradAppBPrint :=
  ⟨conradNearOnePrint_of_weil h.1, conradB3Print_of_weil h⟩

/-- **The C8 input `ConradAppB` from Conrad's Appendix B as printed** (C8, L760–764).
Kind: PROVED. -/
theorem conradAppB_of_weil (h : ConradAppBWeil) : ConradAppB :=
  conradAppB_of_print (conradAppBPrint_of_weil h)

end HDec.G0Galois.C8Conrad.Bridges

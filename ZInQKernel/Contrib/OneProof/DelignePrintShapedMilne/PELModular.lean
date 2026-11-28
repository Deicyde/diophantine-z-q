import ZInQKernel.Contrib.OneProof.DelignePrintShapedMilne.Bridges

/-! # The row `deligneCanonicalModelY3EveryPrint`: the PEL modular variety at level `K₃` (Milne, §8)

This file states M1′, a variant of the complex input M1 of the Milne route, drawn from one print: Milne's PEL modular
variety `M_{K₃}` over `ℂ`, which for the simple type C datum `(B, *, V = B, ψ)` coincides with `Sh_{K₃}(G, X)`
(*Introduction to Shimura varieties*, pp. 327–329), with the algebraic and analytic structure of `Sh_{K₃}(G, X)`
(§§3 and 5 of the same article). Like M1, it is a consequence of the print, not a direct instance: in Milne's usage
"classifies" is a bijection on complex points (p. 320: "The set ShK(G, X) classifies the triples … modulo
isomorphism, i.e., there is a canonical bijection"), with isomorphisms in the category of abelian varieties up to
isogeny, so the universal family, the integral structures, properness and smoothness are reading steps. Its Lean form
is `DelignePSMilne.MilneShimuraFamilyPrint` together with the fibres of the uniformization, so M1′ gives M1
(`milneShimuraFamilyPrint_of_pelModular`), and the row follows from T2a, T2c′, T2c″, M1′ and M2
(`deligneCanonicalModelY3EveryPrint_of_milnePEL`).
-/

set_option autoImplicit false

noncomputable section

namespace DelignePSMilne

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open ShimuraCFT RayClassCFT
open Y3Hodge (HPM DCRelPM toPM)
open DelignePS

/-- **M1′ (a consequence of printed statements, like M1): the PEL modular variety at level `K₃` over `ℂ` is
`Sh_{K₃}(G, X)`; with its universal family and its uniformization by `ℍ^± × (B ⊗ 𝔸_f)^×`.**

*Print.* J. S. Milne, *Introduction to Shimura varieties*, in: *Harmonic analysis, the trace formula, and Shimura
varieties*, Clay Mathematics Proceedings 4, American Mathematical Society, 2005, pp. 265–378 (page numbers of the
volume).
* pp. 328–329, "PEL modular varieties": "Let B be a semisimple algebra over Q with a positive involution ∗, and let
  (V, ψ) be a symplectic (B, ∗)-module. Let K be a compact open subgroup of G(Af). There exists an algebraic variety MK
  over C classifying the isomorphism classes of quadruples (A, s, i, ηK) satisfying (a) and (b) of (8.18) (but not
  necessarily condition (**)), which is called the PEL modular variety attached to (B, ∗, V, ψ). In the simple cases
  (Aeven) and (C), Proposition 8.17 shows that MK coincides with ShK(G, X), but in general it is a finite disjoint
  union of Shimura varieties." ("Proposition 8.17" is Theorem 8.17.)
* Theorem 8.17, p. 327: "Let (G, X) be a simple PEL datum of type A or C associated with (B, ∗, V, ψ) as in the last
  subsection, and let K be a compact open subgroup of G(Af). Then ShK(G, X)(C) classifies the isomorphism classes of
  quadruples (A, s, i, ηK) in which ◦ A is a complex abelian variety, ◦ ±s is a polarization of the hodge structure
  H1(A, Q), ◦ i is a homomorphism B → End(A) ⊗ Q, and ◦ ηK is a K-orbit of B⊗Af-linear isomorphisms
  η: V(Af) → H¹(A, Q)⊗Af sending ψ to an A×f-multiple of s, satisfying the following condition: (**) there exists a
  B-linear isomorphism a: H1(A, Q) → V sending s to a Q×-multiple of ψ." (The target of `η` is printed `H¹`; it is
  read as `H₁`, as in the rest of the theorem and in Proposition 7.3.) Its proof applies Theorem 7.4, the form for
  abelian varieties of Proposition 7.3, whose proof gives the map (p. 321): "The proof that (W, . . .) ↦ [ah, a ◦ η]K
  gives a bijection from the set of isomorphism classes of triples in HK onto ShK(G, X)(C) is now routine (cf. the proof
  of 6.3)."
* Remark 8.18, p. 327: "(a) s(bu, v) = s(u, b∗v), and (b) Tr(i(b)|Tgt0A) = TrX(b) for all b ∈ B ⊗ C." Proposition 8.19,
  p. 328: "For types Aeven and C, the condition (**) of Theorem 8.17 is implied by conditions (a) and (b) of (8.18)."
* Lemma 5.13, pp. 306–307: "Let C be a set of representatives for the double coset space G(Q)+\G(Af)/K, and let X+ be a
  connected component of X. Then G(Q)\X × G(Af)/K ≅ ⊔_{g∈C} Γg\X+ where Γg is the subgroup gKg−1 ∩ G(Q)+ of G(Q)+.
  When we endow X with its usual topology and G(Af) with its adèlic topology (equivalently, the discrete topology),
  this becomes a homeomorphism." p. 307: "Moreover, when K is sufficiently small, Γg will be neat for all g ∈ C
  (apply 3.5) and so its image in Aut(X+)+ will also be neat and hence torsion free. Then Γg\X+ is an arithmetic
  locally symmetric variety, and ShK(G, X) is finite disjoint of such varieties." (Sic.)
* Theorem 3.12 (Baily and Borel 1966), pp. 291–292: "Let D(Γ) = Γ\D be the quotient of a hermitian symmetric domain by
  a torsion free arithmetic subgroup Γ of Hol(D)⁺. Then D(Γ) has a canonical realization as a zariski-open subset of a
  projective algebraic variety D(Γ)*. In particular, it has a canonical structure as an algebraic variety." Proposition
  3.8, p. 290: "There is a unique functor (V, O_V) ↦ (V^an, O_{V^an}) from nonsingular varieties over C to complex
  manifolds with the following properties: (a) as sets, V = V^an, every zariski-open subset is open for the complex
  topology, and every regular function is holomorphic; …"

*Lean form.* There are a proper smooth curve `T` over `ℂ` (`M_{K₃} = Sh_{K₃}(G, X)`), a family `𝒜` over `T` of abelian
surfaces with `𝒪`-action and printed level-3 structure (`Y3Fix.QMAbSchemeP`; the universal family), and
`ψ : ℍ^± × (B ⊗ 𝔸_f)^× → T(ℂ)` (`ℂ`-points of `T` over `ℂ`; `ψ(z, g) = [z, g]`) which is onto, has fibres exactly the
double cosets (`DelignePS.DCRelPM`), and is holomorphic in `τ ∈ ℍ` for every `g`, such that the fibre of `𝒜` at
`ψ(z, g)` is a moduli object of `[z, g]` (`DelignePS.IsLevelPoint`).

*Identifications.* The datum is the simple PEL datum of type C attached to `(B, *, V, ψ)` with `B = (2, −3 | ℚ)`,
`b* = μ⁻¹ b̄ μ` (`μ = 2j + ij`), `V = B` with `B` acting on the left and `ψ` the alternating form of the polarization;
`G(ℚ) = B^×` acts on `V` by right multiplication by `γ⁻¹`, on `X = ℍ^±` by Möbius transformations through `ι`, and
`G(𝔸_f) = (B ⊗ 𝔸_f)^×`; `K = K₃` (`K3Q`). Type C is proved in Lean (`DelignePSMilne.Datum.Sd_mul_iota_dagO`,
`DelignePSMilne.Datum.Sd_posDef`), and (b) of 8.18 is the trace condition (`DelignePSMilne.Datum.trace_iota`).

*Reading steps (to be read; not printed as such).*
1. "Classifying" is read as a fine moduli variety: `M_{K₃}` carries a universal family of quadruples whose fibre at a
   point is the quadruple that point classifies (the objects have no automorphisms at level `K₃`).
2. "Coincides" is read as the identification `M_{K₃}(ℂ) = Sh_{K₃}(G, X)(ℂ)` through the classification of Theorem 8.17:
   the point `[x, a]_K` classifies the quadruple `(W, …)` with `[ah, a ∘ η]_K = [x, a]_K` (Proposition 7.3). So `ψ` is
   onto with fibres the double cosets.
3. "K sufficiently small" holds for `K₃`: `Γg = B^× ∩ g K₃ g⁻¹` acts freely on `ℍ`. For `γ = g k g⁻¹ ∈ Γg`
   (`k ∈ K₃`), `nrd γ = nrd k` lies in `ℚ^× ∩ ℤ̂^× = {±1}` (`k` and `k⁻¹` are integral) and in `1 + 3ℤ̂`, so `nrd γ = 1`;
   `γ` lies in the maximal order `B ∩ g 𝒪̂ g⁻¹` (so `trd γ ∈ ℤ`), and `nrd(γ − 1) = nrd(k − 1) ∈ 9ℤ`; while an element
   `γ ≠ 1` of `B` with `nrd γ = 1` and `trd γ ∈ ℤ` fixing a point of `ℍ` is `−1` or elliptic with `trd γ ∈ {−1, 0, 1}`,
   so `nrd(γ − 1) = 2 − trd γ ∈ {1, 2, 3, 4}`. So `T` is smooth of dimension 1; it is proper because each `Γg\ℍ` is
   compact (`B` is a division algebra: Example 3.4, p. 288; the same complex points are printed as "une surface de
   Riemann compacte" in Boutot–Carayol III.0.1, p. 125).
4. Holomorphy: the analytic space of `Sh_{K₃}(G, X)` is `⊔ Γg\X⁺` (Lemma 5.13 with Theorem 3.12), on which regular
   functions are holomorphic (Proposition 3.8(a)); `X⁺ → Γg\X⁺` is holomorphic, so `ψ(·, g)` is a holomorphic family
   (`ShimuraSplit.IsHolFamily`).
5. The kernel's objects: a family of quadruples `(A, s, i, ηK₃)` gives the family of abelian surfaces with
   `T̂ = η(𝒪̂)` (well defined since `K₃` stabilizes `𝒪̂`), the `𝒪`-action induced by `i` (it preserves `η(𝒪̂)`), the
   level-3 sections `η mod 3` (`a ↦ η(a)/3` on `T̂/3T̂`), and `s` forgotten; this
   is a `Y3Fix.QMAbSchemeP`. The quadruple at `[z, g]` (Proposition 7.3: `W = V`, `h = h_z`, `η = g`) gives
   `ℂ² / ι(L_g)(z, 1)ᵀ` with `L_g = B ∩ 𝒪̂ g⁻¹`, i.e. the moduli object of `[z, g]` (`DelignePS.IsLevelPoint`, the
   lattice form of `H₁ = L_g` with the Hodge structure `h_z`). That every `[z, g]` has a representative `(τ, u)`,
   `τ ∈ ℍ`, `u ∈ 𝒪̂^×`, is proved in Lean (`DelignePS.exists_unit_rep`).

*Dropped clauses* (weaker): the universal property of `M_{K₃}` beyond the existence of the universal family (only its
fibres at `ℂ`-points are used); the polarization; the compactification `D(Γ)*`; all levels other than `K₃`.
*Refereeing:* the project counts the Clay volume as published. -/
def MilnePELModularVarietyPrint : Prop :=
  ∃ (T : Over (Spec (CommRingCat.of ℂ))), IsProper T.hom ∧ SmoothOfRelativeDimension 1 T.hom ∧
    ∃ (𝒜 : Y3Fix.QMAbSchemeP T.left) (ψ : HPM → BAQˣ → (Spec (CommRingCat.of ℂ) ⟶ T.left)),
      (∀ (z : HPM) (g : BAQˣ), ψ z g ≫ T.hom = 𝟙 _) ∧
      (∀ s : Spec (CommRingCat.of ℂ) ⟶ T.left, s ≫ T.hom = 𝟙 _ → ∃ (z : HPM) (g : BAQˣ), ψ z g = s) ∧
      (∀ (z : HPM) (g : BAQˣ) (z' : HPM) (g' : BAQˣ), ψ z g = ψ z' g' ↔ DCRelPM z g z' g') ∧
      (∀ g : BAQˣ, ShimuraSplit.IsHolFamily (X := T.left) (fun τ => ψ (toPM τ) g)) ∧
      ∀ (z : HPM) (g : BAQˣ), ∃ P : QML3 ℂ, IsLevelPoint P z g ∧ IsFibreOf 𝒜.toQMFamily (ψ z g) P

/-- **M1′ gives M1**: forget the fibres of the uniformization. -/
theorem milneShimuraFamilyPrint_of_pelModular (h : MilnePELModularVarietyPrint) : MilneShimuraFamilyPrint := by
  obtain ⟨T, hp, hs, 𝒜, ψ, hT, hon, -, hhol, hfib⟩ := h
  exact ⟨T, hp, hs, 𝒜, ψ, hT, hon, hhol, hfib⟩

/-- **The discharge from T2a, T2c′, T2c″, M1′ and M2.** T2a (Voight), T2c′ (Boutot–Carayol 1.5), T2c″ (Boutot–Carayol
1.4), M1′ (Milne, the PEL modular variety at level `K₃`, pp. 327–329) and M2 (Milne, §14 PEL case with Definition 12.8)
give `Y3Hodge.DeligneCanonicalModelY3EveryPrint`, through `deligneCanonicalModelY3EveryPrint_of_milne`. -/
theorem deligneCanonicalModelY3EveryPrint_of_milnePEL (hV : VoightQMComplexModuliPrint)
    (hP : BoutotCarayolPolarizationPrint) (hR : BoutotCarayolRepresentabilityPrint)
    (hF : MilnePELModularVarietyPrint) (hM : MilneCanonicalModelPrint) :
    Y3Hodge.DeligneCanonicalModelY3EveryPrint :=
  deligneCanonicalModelY3EveryPrint_of_milne hV hP hR (milneShimuraFamilyPrint_of_pelModular hF) hM

end DelignePSMilne

# Statement review: MainTheoremCMPolMax / MainTheoremCMPolSign / MainTheoremCMPol / CMAbVarExists
(read-only; no Lean run; F = ZInQKernel/Contrib/OneProof/MainCMPolar.lean)

## Bottom line
No soundness problem found. All three statements are true as mathematics, and each is implied by the cited prints
(it drops clauses or adds hypotheses). The ε = 1 normalization is the only unverified point, and it is inherited
unchanged from HcmPrinted.MainTheoremCMArith.

## 1. Helper definitions
- IsOLattice (F:432-435): 𝓞-stable, c𝓞 ⊆ 𝔞, d𝔞 ⊆ 𝓞 (integral). This holds exactly when 𝔞 is a nonzero fractional
  𝓞_E-ideal. Correct.
- IsRiemannDatum (F:443-445): ζ̄ = −ζ, Im φᵢ(ζ) > 0, Tr(ζ x ȳ) ∈ ℤ on 𝔞. This matches Shimura's "Tr(ζ𝔞𝔞^ρ) ⊆ ℤ".
  Sign: with φᵢ(ζ) = i tᵢ, E(Φx,Φy) extended ℝ-linearly gives E(iu,u) = −2Σ tᵢ|uᵢ|², so tᵢ > 0 makes E a Riemann
  form under the E(u,iv) > 0 convention, and −E one under E(iu,v) > 0. The integrality clause is invariant under
  ζ ↦ −ζ, and no conclusion mentions ζ. So the convention cannot make anything false. The docstring (F:441-442)
  says this correctly.
- Not vacuous: for every IsOLattice 𝔞 a datum exists. exists_zeta (F:356) gives ζ, and multiplying it by an integer
  clears the bounded denominators of Tr on 𝔞𝔞̄. So "∃ ζ" never empties a case, and it adds nothing beyond IsOLattice.
- `1 ⊗ₜ y`: its type is forced to AQ ⊗[ℚ] E by the multiplication, so it is includeRight y, matching latAct
  (QMRecPrinted.lean:76-78). The cast `(c : E)` is a harmless ℕ→E cast. latHat (QMRecPrinted.lean:70) is the
  closure of ZhatQ ⊗ 𝔞 = 𝔞̂. ZhatQ (RayClassShimura.lean:342) is the product of the adic integers. Correct.

## 2. MainTheoremCMPolMax (F:472-497) and MainTheoremCMPolSign / MainTheoremCMPol (F:521-553)
- Exact diff check (`diff` on the source text):
  - PolSign ε vs HcmPrinted.MainTheoremCMSign ε (ShimuraMainCMPrinted.lean:828-852): identical except one added
    line, F:533 `IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →`. It sits after `IsOfType Φ 𝔞 θ →`, so it is
    within the scope of 𝔞, θ and the [IsCMField E] binder.
  - PolMax vs PolSign: they differ only in the two `reflexNorm … ^ (ε : ℤ)` occurrences, which PolMax writes
    without the power. So PolMax is the ε = 1 instance.
  - The bridges polSign_one_of_polMax (F:555), mainTheoremCMPolMax_of_arith (F:569) and
    mainTheoremCMPol_of_mainTheoremCM (F:563) are proved by direct application. If they compile (I did not build),
    the bodies agree up to definitional equality, despite the different `open`s (HcmPrinted has `open Classical`
    at line 626; the bodies contain no decidable terms).
- Truth: the conclusion is exactly MainTheoremCMArith's, with strictly more hypotheses, so it is true whenever that
  one is. Conventions checked:
  - A' / h is A^σ = A ×_{Spec σ} Spec ℂ. `θ'(Φy) ≫ h = Spec σ ≫ θ(Φx)` says θ'(Φy) = θ(Φx)^σ.
  - latAct t 𝔞 = E ∩ t⁻¹𝔞̂ = t⁻¹𝔞.
  - `t y − x ∈ 𝔞̂` says y represents t⁻¹x ∈ E/t⁻¹𝔞, which is Shimura's ξ(u)^σ = ξ'(N(s)⁻¹u).
  - Consistency: x ∈ 𝔞 gives y ∈ t⁻¹𝔞, and both sides are 1, using the identity clause.
- Hypotheses mean what they should:
  - IsUniformization (R22.lean:50-56) is a holomorphic surjective homomorphism with kernel Φ(𝔞). Since Φ(𝔞) is a
    lattice and dim A = g, this forces θ = exp_A ∘ (linear iso), so it is a genuine analytic uniformization.
  - IsOfType is then automatic, by GAGA.
  - The identity clause plus rigidity makes A' ≅ A^σ as groups.
- Is it implied by the print? Yes. The hypothesis "∃ ζ" is not tied to A, but transporting the Riemann form
  Tr(ζxȳ) (or −ζ) through θ gives a polarization C of A (Riemann forms ↔ NS(A^an) = NS(A), ample). So (A, C, θ)
  is of type (E,Φ;𝔞,±ζ). Restricting to 𝓞_E-ideals and dropping the uniqueness of θ' and the C^σ and type clauses
  only weakens the statement. Nothing in the conclusion constrains every uniformization; it is only ∃ θ'.
- Sign (UNVERIFIED, inherited): ε = 1 with Tau Ceti's arithmetic Artin map (ArtinCondC, RayClassShimura.lean:393)
  and lattice N(s)⁻¹𝔞.
  - Sanity check, E = K imaginary quadratic: n = 1, ρ = id (a conjugate ρ would contradict j's E-linearity plus
    span), so N(s) = s. That gives j(𝔞)^{Frob_𝔭} = j(𝔭⁻¹𝔞), the standard formula (Frobenius lifts to an isogeny
    with kernel E[𝔭] = 𝔭⁻¹𝔞/𝔞).
  - MainTheoremCMPol (∃ ε) does not depend on this.

## 3. CMAbVarExists (F:511-516)
- True, and implied by Shimura–Taniyama/Shimura 1998 §6.2 Thm 4, or by Riemann's theorem plus GAGA. Since ±Tr(ζxȳ)
  is a Riemann form (point 1), the torus ℂ^g/Φ(𝔟) is algebraizable to a projective B with dim B = g.
- The analytic iso, normalized so 0 ↦ 1, is a homomorphism (rigidity of tori). It is holomorphic, so the preimages
  of U(ℂ) are open and regular functions pull back to holomorphic ones. That is IsUniformization with cmLat Φ 𝔟.
- The conclusion is only ∃ B ∃ θ. There is no uniqueness or "for every θ" clause, and no claim about End(B).
  Strictly weaker than the print.
- Φ(𝔟) is a lattice because of `finrank = 2g` plus injectivity of Sum.elim. g ≥ 1 automatically.

## 4. Remaining reading risks
- Primitivity (UNVERIFIED from the books): the consumers use the non-primitive type on E = K(√2) induced from
  (K, κ). For that type the reflex field is κ(K), n = 1, V = E and N(a) = a, which is correct.
  - As mathematics the main theorem holds for arbitrary CM types. Milne's CM notes, Thm 9.10 (Main theorem), are
    stated for any CM pair (E,Φ) with no primitivity assumption, as I recall (UNVERIFIED).
  - I recall Shimura 1971 Thm 5.15 / 1998 Thm 18.6 as also stated for an arbitrary CM type (K,Φ), with A not
    assumed simple, but I cannot check the text. If a reviewer insists on the literal Shimura locator, Milne's
    theorem is the safer citation for the non-primitive case. Existence (CMAbVarExists) has no primitivity issue.
- "Polarized" is rendered as ∃ ζ rather than "C corresponds to ζ". This is a correct, weaker rendering (point 2),
  but the docstring wording "the polarization C of A is given through its Riemann form" slightly overstates the
  link: nothing ties ζ to a polarization on A. Suggested wording: "A admits a polarization of type ζ, via θ".
- The ε = 1 normalization and the locator numbers (Thm 5.15, 18.6, §6.2 Thm 4) are UNVERIFIED (no books). This is
  unchanged from HcmPrinted.MainTheoremCMArith; MainTheoremCMPol avoids it.

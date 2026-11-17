import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Transfer

/-!
# Lane RC10 (Heegner algebra), part 10: the Shapiro/transfer input and (4.2) assembled

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 7, tex lines 3202–3280.

* `ShapiroTransferInput` records the printed input (Nekovář, *Selmer complexes*, Sections
  8.1.1–8.1.6): on cohomology, the explicit transfer (H21) computes Shapiro's isomorphism followed
  by the equivariant coefficient map (H20).  It is stated for one chosen section; that the same
  holds for every section ("changing sections gives the integral homotopy in Section 8.1.4") is
  then `PROVED` from the degree-one homotopy `T1_change_section`.
* `eq42_assembled` combines the transported local relations (H19) with the weights of (H21) into
  (4.2): `f(P_{I∪ℓ,m}) = 0`, `s(P_{I∪ℓ,m}) = J f(P_{I,m})` in the common coordinates (`PROVED`).
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open Finset

section Shapiro

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- `PRINT` (Nekovář, *Selmer complexes*, Astérisque 310, Sections 8.1.1–8.1.6, pp. 189–194,
read and confirmed; Nekovář writes the corestriction on cochains with right cosets `U\G`, the
manuscript with the mirror left-coset convention, as it says), tex 3202–3249.  `G = G_K`, `H = G_{H_f}` (normal, `Δ_f = G/H`),
`M = E[2^m] ⊗ A` with the Tate action `ρ`, `θ` a character of `Δ_f`.  `clsH` and `clsG` send
1-cocycles of `H` (coefficients `M`) and of `G` (coefficients `M(θ)`, action `R = θ ρ`) to their
classes in abstract groups `H1H = H¹(H_f, M)` and `H1G = H¹(K, M(θ))`; `clsG` is additive and
kills coboundaries; `shapiro` is Shapiro's isomorphism followed by the coefficient map (H20).  The
printed input: for one chosen section `r₀`, the explicit transfer (H21) of a cocycle represents
`shapiro` of its class. -/
structure ShapiroTransferInput (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (H1H H1G : Type*)
    [AddCommGroup H1H] [AddCommGroup H1G] where
  clsH : (H → M) → H1H
  clsG : (G → M) → H1G
  shapiro : H1H →+ H1G
  clsG_add : ∀ c c' : G → M, clsG (c + c') = clsG c + clsG c'
  clsG_cob : ∀ w : M, clsG (fun g => Rtw H ρ θ g w - w) = 0
  r₀ : G ⧸ H → G
  hr₀ : ∀ δ, (QuotientGroup.mk (r₀ δ) : G ⧸ H) = δ
  computes : ∀ b : H → M, (∀ x y : H, b (x * y) = b x + ρ x (b y)) →
    clsG (T1 H ρ θ r₀ hr₀ b) = shapiro (clsH b)

/-- tex 3247–3249, `PROVED` from `ShapiroTransferInput` and `T1_change_section`: the explicit
transfer computes the same class for every choice of sections (the integral homotopy of
Nekovář 8.1.4 in degree one); no averaging factor occurs in (H21). -/
theorem ShapiroTransferInput.computes_any {ρ : G →* Module.End A M} {θ : G ⧸ H →* Aˣ}
    {H1H H1G : Type*} [AddCommGroup H1H] [AddCommGroup H1G]
    (S : ShapiroTransferInput H ρ θ H1H H1G) (r : G ⧸ H → G)
    (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ) (b : H → M)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    S.clsG (T1 H ρ θ r hr b) = S.shapiro (S.clsH b) := by
  obtain ⟨w, hw⟩ := T1_change_section H ρ θ S.r₀ S.hr₀ r hr b hb
  have : T1 H ρ θ r hr b = T1 H ρ θ S.r₀ S.hr₀ b + (fun g => Rtw H ρ θ g w - w) := by
    funext g; rw [hw g]; rfl
  rw [this, S.clsG_add, S.clsG_cob, add_zero, S.computes b hb]

end Shapiro

/-- (4.2), tex 3268–3277, `PROVED`: at a derivative prime the Mackey terms use the transported
places `r_δ⁻¹ λ`; if each transported new finite coordinate vanishes (H19) and each transported
singular coordinate is `s'_δ = ρ(r_δ)⁻¹ J ρ(r_δ) f'_δ` (H19 in transported coordinates), then the
weighted sums of (H21) satisfy `f(P_{I∪ℓ,m}) = 0` and `s(P_{I∪ℓ,m}) = J f(P_{I,m})`, where
`f(P_{I,m}) = ∑_δ θ(δ) ρ(r_δ) f'_δ`. -/
theorem eq42_assembled {Δ A M : Type*} [Fintype Δ] [CommRing A] [AddCommGroup M] [Module A M]
    (θ : Δ → A) (ρr : Δ → (M ≃ₗ[A] M)) (J : M →ₗ[A] M) (fnew' s' f' : Δ → M)
    (hf : ∀ δ, fnew' δ = 0) (hs : ∀ δ, s' δ = (ρr δ).symm (J (ρr δ (f' δ)))) :
    ∑ δ, θ δ • ρr δ (fnew' δ) = 0 ∧
      ∑ δ, θ δ • ρr δ (s' δ) = J (∑ δ, θ δ • ρr δ (f' δ)) := by
  refine ⟨by simp [hf], ?_⟩
  simp_rw [hs]
  exact weights_42 θ ρr J f'

end ZInQ.Manuscript.RC.HeegnerAlgebra

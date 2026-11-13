import ZInQKernel.Contrib.TYZGenus.RingClassBridge

/-!
# tyz-cm: Shimura reciprocity for Heegner points on `X₀(32) = A` (the leaf)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

This file states the one textbook leaf of task tyz-cm, **the main theorem of complex multiplication
for the Heegner points of `X₀(32)`, in Gross's form** (`ShimuraReciprocityPic`), over genuine
definitions:

* the order `O = ℤ + f𝓞_K` of `K = ℚ(√−m)` (ring-class's `conductorOrder`), its ring class field and
  Tau Ceti's Artin isomorphism `Pic(O) ≃* Gal(H_O/K)`, Picard classes of ideals of `𝓞_K` prime to
  `f` (Tau Ceti's `picClass`: the class of `J ∩ O`);
* the normalized complex embedding `κ : K → ℂ`, `√−m ↦ i√m` (`kappa`), and the lattice
  `κ(J ∩ O) ⊂ ℂ` of such an ideal (`idealLat`);
* cm-points' Heegner forms of level 32, their lattices `⟨1, τ_Q⟩`, `⟨1/32, τ_Q⟩` and Heegner points
  `heegnerPt Q ∈ A(ℚ̄)` through x0-32's `X0.phiC`.

The two targets of tyz-cm are derived from it in `ShimuraField.lean`
(`CM.CMFieldOfDefinition ringClassFieldD`) and `ShimuraZn.lean` (`Package.TYZSigmaFixesZn`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

/-- The normalized complex embedding `κ : ℚ(√−m) → ℂ`, `a + b√−m ↦ a + b·i√m` (as a function). -/
def kappa (m : ℕ) (x : QNeg m) : ℂ := (x.re : ℂ) + (x.im : ℂ) * (I * (Real.sqrt m : ℂ))

/-- The set `J ∩ O ⊂ K` for an ideal `J` of `𝓞_K` and the order `O = ℤ + f𝓞_K`. -/
def idealMeetOrder (m f : ℕ) [NeZero m] [NeZero f] (J : Ideal (𝓞 (QNeg m))) : Set (QNeg m) :=
  {x | x ∈ (conductorOrder (QNeg m) f).toSubalgebra ∧ ∃ y ∈ J, (y : QNeg m) = x}

/-- The lattice `κ(J ∩ O) ⊂ ℂ` (the `ℤ`-span of the image; `J ∩ O` is already a `ℤ`-module). -/
def idealLat (m f : ℕ) [NeZero m] [NeZero f] (J : Ideal (𝓞 (QNeg m))) : Submodule ℤ ℂ :=
  Submodule.span ℤ (kappa m '' idealMeetOrder m f J)

/-- The discriminant `f²·d_K` of `ℤ + f𝓞_K` in `K = ℚ(√−m)`, `m` squarefree:
`d_K = −m` for `m ≡ 3 (mod 4)` and `d_K = −4m` otherwise. -/
def discOf (m f : ℕ) : ℤ := if m % 4 = 3 then -((f : ℤ) ^ 2 * m) else -(4 * (f : ℤ) ^ 2 * m)

/-- **Leaf SHIMURA-PIC (main theorem of complex multiplication for Heegner points of `X₀(32)`,
Gross's form).** Let `K = ℚ(√−m)` (`m` squarefree), `O = ℤ + f𝓞_K` the order of discriminant `D`,
`H_O` its ring class field, and `e : Kˢ → ℚ̄` an embedding inducing on `K` the normalized complex
embedding `√−m ↦ i√m` (through cm-points' `ιC : ℚ̄ → ℂ`). Let `J` be an ideal of `𝓞_K` prime to
`f`, and `ρ ∈ Gal(ℚ̄/ℚ)` an automorphism acting on `e(H_O)` as the Artin symbol of the class of
`J ∩ O`. Then for Heegner forms `Q, Q'` of level 32 and discriminant `D` whose pairs of lattices
satisfy `κ(J ∩ O)·(⟨1,τ_{Q'}⟩, ⟨1/32,τ_{Q'}⟩) = c·(⟨1,τ_Q⟩, ⟨1/32,τ_Q⟩)` for one `c ∈ ℂ`
(i.e. `(L', L'_N) = c·(J∩O)⁻¹(L, L_N)`), `ρ` maps the Heegner point of `Q` to that of `Q'`:
`Art(𝔟)(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔟⁻¹𝔞])`.

Sources (refereed; theorem numbers UNVERIFIED, from memory, no network on this host):
the main theorem of complex multiplication, Shimura, *Introduction to the arithmetic theory of
automorphic functions* (1971), Thm. 5.4 (`E^{[s,K]} ≅ ℂ/s⁻¹𝔞`, with the action on torsion
`f(t)^σ = f'(s⁻¹t)`, which gives the action on the cyclic subgroup `L_N/L`); Silverman, *Advanced
topics in the arithmetic of elliptic curves*, GTM 151, Thm. II.8.2; Gross, *Heegner points on
`X₀(N)`*, in *Modular forms* (Durham 1983), 1984, §3 (`σ_𝔟(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔞𝔟⁻¹])`);
Cox, *Primes of the form x² + ny²*, Thm. 11.1 and Cor. 11.37 (the `j`-part). Normalization: the
idele `s` with `s_𝔭` a uniformizer has `[s, K] = ` arithmetic Frobenius (Tau Ceti's Artin map), so
`Art(J)` corresponds to `s⁻¹𝔞 = J⁻¹𝔞`. The theorem holds for every lattice pair (Shimura's form
needs no condition on the orders of `L` and `L_N`), so no Heegner condition `(f, 32) = 1` is
needed. It is stated through x0-32's eta-quotient model `X0.phiC` and cm-points' `ιC`, so it is
true because (and only if) that model is the `ℚ`-rational modular parametrization of `X₀(32)`
(x0-32's leaves `X0.X0AnalyticModel`; Shimura 1971 Ch. 6–7 for the canonical model). -/
def ShimuraReciprocityPic : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm 32 D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      galPt ρ (heegnerPt Q) = heegnerPt Q'

end ZInQ.Contrib.TYZGenus.Shimura

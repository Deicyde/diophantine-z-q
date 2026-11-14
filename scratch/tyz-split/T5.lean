import ZInQKernel.Contrib.TYZGenus.ShimuraModFn

/-!
# tyz-split, row T-5: `Shimura.ShimuraReciprocityModFn` split into its CM part and its modular-curve part

Task tyz-split (2026-11-14). Report: `docs/research/tyz-split.md` §3; log: `scratch/tyz-split/log.md`.

`Shimura.ShimuraReciprocityModFn` (kernel, `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean`, verbatim
here by import) is a composite of two published theorems (shimura-modfn §1): the main theorem of
complex multiplication with its torsion clause (Shimura 1971, Thm. 5.4) and the canonical model of
`X₀(N)` over `ℚ` (Shimura 1971, §6.7 / Thm. 6.23 / Prop. 6.9; Deligne–Rapoport). Neither can be
stated in its printed form over genuine Lean definitions today (§3 of the report). This file
separates the two parts along the moduli interpretation `τ ↦ (ℂ/⟨1, τ⟩, ⟨1/N⟩)`, with explicit
moduli coordinates over Mathlib's Weierstrass theory (`PeriodPair`, `weierstrassP`, `g₂`, `g₃`):

* `modCoord N τ`: `j(τ)` and the elementary symmetric functions of the Weber values
  `h(k/N)`, `1 ≤ k ≤ N − 1` (Weber's function `h`, Shimura 1971 (4.1.3), UNVERIFIED number);
* `CMModuli` (CM part, GLUE: consequence of Shimura Thm. 5.4 with the lattice computation of
  shimura-modfn §1): `ShimuraReciprocityModFn` for the coordinate functions only;
* `X0RatStructure` (modular-curve part, GLUE: consequence of the canonical model; no CM): points of
  `Y₀(N)` with algebraic, `ρ`-conjugate moduli coordinates have algebraic, `ρ`-conjugate values of
  every `g ∈ ℚ(X₀(N))` regular on `ℍ`;
* `shimuraReciprocityModFn_of_split : CMModuli → X0RatStructure → ShimuraReciprocityModFn`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.TYZSplitT5

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura

/-! ## §1. Moduli coordinates of `(ℂ/⟨1, τ⟩, ⟨1/N⟩)` over Mathlib's Weierstrass theory -/

theorem linIndep_one_tau (τ : UpperHalfPlane) : LinearIndependent ℝ ![(1 : ℂ), (τ : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have him : t * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa [Complex.real_smul] using this
  have ht : t = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt τ.im_pos)
  subst ht
  simp only [zero_smul, add_zero, Complex.real_smul, mul_one] at h
  exact ⟨by exact_mod_cast h, rfl⟩

/-- The period pair `(1, τ)`: lattice `ℤ + ℤτ`, elliptic curve `ℂ/⟨1, τ⟩`. -/
def pp (τ : UpperHalfPlane) : PeriodPair := ⟨1, τ, linIndep_one_tau τ⟩

/-- `Δ(L) = g₂³ − 27 g₃²`. -/
def discL (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/-- `j(L) = 1728 g₂³/Δ`. -/
def jL (L : PeriodPair) : ℂ := 1728 * L.g₂ ^ 3 / discL L

/-- **Weber's function** `h_L(z)`: `(g₂g₃/Δ)℘(z)` if `g₂g₃ ≠ 0`, `(g₂²/Δ)℘(z)²` if `g₃ = 0`,
`(g₃/Δ)℘(z)³` if `g₂ = 0` (Shimura 1971, (4.1.3), constants dropped; UNVERIFIED number). It is
invariant under homotheties and under `Aut(E_L)`, and `h_L(z) = h_L(z')` iff `z' ∈ Aut(E_L)·z`. -/
def weber (L : PeriodPair) (z : ℂ) : ℂ :=
  if L.g₃ = 0 then L.g₂ ^ 2 / discL L * L.weierstrassP z ^ 2
  else if L.g₂ = 0 then L.g₃ / discL L * L.weierstrassP z ^ 3
  else L.g₂ * L.g₃ / discL L * L.weierstrassP z

/-- **Moduli coordinates of the point `(ℂ/⟨1, τ⟩, ⟨1/N⟩)` of `Y₀(N)`**: index `0` is `j(τ)`; index
`1 ≤ i ≤ N − 1` is the `i`-th elementary symmetric function of the Weber values `h(k/N)`,
`1 ≤ k ≤ N − 1` (the nonzero points of the cyclic subgroup `⟨1/N⟩`). They are functions in
`ℚ(X₀(N))` away from the elliptic points (rational `q`-expansions: `Gal(ℚ(ζ_N)/ℚ)` permutes the
`k`), and they separate the points of `Y₀(N)` (`j` fixes `E`; the multiset of Weber values fixes
`Aut(E)·⟨1/N⟩`, since a generator's orbit is met only by `C` and its `Aut(E)`-translates). -/
def modCoord (N : ℕ) (τ : UpperHalfPlane) (i : ℕ) : ℂ :=
  if i = 0 then jL (pp τ)
  else ((Multiset.range (N - 1)).map fun k : ℕ => weber (pp τ) (((k : ℂ) + 1) / N)).esymm i

/-! ## §2. The two parts -/

/-- **GLUE CM-MODULI (the CM part of `ShimuraReciprocityModFn`).** Same data and hypotheses as
`Shimura.ShimuraReciprocityModFn` (Heegner forms `Q, Q'` of level `N ≥ 1` and discriminant `D` of
the order `O = ℤ + f𝓞_K`, an ideal `J` prime to `f`, `ρ` acting as `Art(J ∩ O)` on `H_O`,
`κ(J ∩ O)·(L', L'_N) = c·(L, L_N)`); conclusion: the moduli coordinates of `τ_Q` are algebraic and
`ρ` maps them to those of `τ_{Q'}`.

Source: the main theorem of CM with its torsion clause, Shimura 1971 Thm. 5.4
(`E_L^σ ≅ E_{s⁻¹L}`, `ξ(u)^σ = ξ'(s⁻¹u)`), for `σ ∈ Aut(ℂ/K)` extending `ρ` and the idele `s` of `J`,
with `s⁻¹(L, L_N) = 𝔟⁻¹(L, L_N) ∼ (L', L'_N)` (shimura-modfn §1); the Weber function is
model-independent and algebraic, `h(E^σ, P^σ) = h(E, P)^σ`. A consequence of one theorem (a short
derivation), not its printed form. -/
def CMModuli : Prop :=
  ∀ (N : ℕ), 0 < N →
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      ∃ x : ℕ → Qbar, (∀ i < N, ιC (x i) = modCoord N Q.tauH i) ∧
        ∀ i < N, ιC (ρ (x i)) = modCoord N Q'.tauH i

/-- **GLUE X0-RAT (the modular-curve part; no CM).** For `N ≥ 1`, `g ∈ ℚ(X₀(N))` regular on `ℍ`
(`IsRatModFn N g`), points `τ, τ'` and `ρ ∈ Gal(ℚ̄/ℚ)`: if the moduli coordinates of `τ` are
algebraic and `ρ` maps them to those of `τ'`, then `g(τ), g(τ')` are algebraic and `ρ` maps the first
to the second.

Content: the `ℚ`-structure of `X₀(N)` given by rational `q`-expansions (`IsRatModFn`) is the moduli
`ℚ`-structure (Shimura 1971, §6.7, Thm. 6.23, Prop. 6.9; Deligne–Rapoport; Diamond–Shurman Ch. 7;
UNVERIFIED numbers): `j` and the `modCoord`s are `ℚ`-rational functions separating the points of
`Y₀(N)(ℂ)`, so `τ'` is the point `ρ(τ)` and `g(ρ(τ)) = ρ(g(τ))`. A composite (canonical model +
separation of points by Weber coordinates), not a printed statement. -/
def X0RatStructure : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (τ τ' : UpperHalfPlane) (ρ : GalQ) (x : ℕ → Qbar),
      (∀ i < N, ιC (x i) = modCoord N τ i) → (∀ i < N, ιC (ρ (x i)) = modCoord N τ' i) →
      ∃ b b' : Qbar, ιC b = g τ ∧ ιC b' = g τ' ∧ ρ b = b'

/-! ## §3. The row from the two parts -/

/-- `HeegnerForm 0 D` is empty (`0 ∣ A` forces `A = 0`, against `A > 0`). -/
theorem heegnerForm_level_pos {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    have := Q.N_dvd
    simp only [Nat.cast_zero, zero_dvd_iff] at this
    exact absurd this (ne_of_gt Q.A_pos)
  · exact h

/-- **Row T-5 from its CM part and its modular-curve part.** -/
theorem shimuraReciprocityModFn_of_split (hCM : CMModuli) (hX : X0RatStructure) :
    ShimuraReciprocityModFn := by
  intro N g hg m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN
  have hN := heegnerForm_level_pos Q
  obtain ⟨x, hx, hx'⟩ := hCM N hN m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  exact hX N hN g hg Q.tauH Q'.tauH ρ x hx hx'

end ZInQ.Contrib.TYZGenus.TYZSplitT5

#print axioms ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split

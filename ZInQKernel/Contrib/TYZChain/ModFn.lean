import ZInQKernel.Contrib.TYZGenus.ShimuraMain

/-!
# TYZ chain: shimura-modfn (review and split of the CM leaf `ShimuraReciprocityModFn`; not used by the main theorem)

Task tyz-chain (2026-11-14). This module is `scratch/shimura-modfn/ModFn.lean` unchanged except that its `#print axioms`
lines were moved to `scratch/tyz-chain/Check.lean`. The original header follows.
-/


/-!
# shimura-modfn: `Shimura.ShimuraReciprocityModFn` against the main theorem of CM for `j`

Task shimura-modfn (2026-11-14). Report: `docs/research/shimura-modfn.md`; log:
`scratch/shimura-modfn/log.md`.

* §0 verbatim copies of tyz-cm's `IsRatModFn` and `ShimuraReciprocityModFn` (`rfl` checks).
* §1 Klein's `j = E₄³/Δ` (Mathlib's Eisenstein series and discriminant) and the leaf
  `MainTheoremCMj` (main theorem of complex multiplication for `j` at lattices `⟨1, τ⟩` stable
  under an order `O`, ideal-class form: `Art(𝔟) j(L) = j(𝔟⁻¹L)`).
* §2 the `j`-part of the reciprocity law at Heegner pairs: `ρ(j(τ_Q)) = j(τ_{Q'})` and
  `ρ(j(Nτ_Q)) = j(Nτ_{Q'})` from `MainTheoremCMj` (glue, proved).
* §3 evaluation glue: if `B(j, j_N)·g = A(j, j_N)` on `ℍ` with `A, B ∈ ℚ[X, Y]` and
  `B(j(τ_Q), j(Nτ_Q)) ≠ 0`, the conclusion of `ShimuraReciprocityModFn` holds for `(g, Q, Q')`
  (proved).
* §4 the non-CM leaf `RatX0Rep` (`ℚ(X₀(N)) = ℚ(j, j_N)` with the conductor bound
  `Φ_N,Y(j, j_N)·g ∈ ℚ[j, j_N]`), isolated points, and the split
  `ShimuraReciprocityModFn ⇐ MainTheoremCMj ∧ RatX0Rep ∧ ShimuraReciprocityModFnSingular`
  (proved), where the last Prop is the statement restricted to Heegner points at which the plane
  model `(j, j_N)` of `X₀(N)` is singular. Such points occur among the points the project uses
  (`isolated_check.out`), so the `j`-form of the main theorem of CM does not replace the leaf.

No `sorry`, no `axiom`.
-/

set_option maxRecDepth 8000

noncomputable section

namespace ZInQ.Contrib.TYZGenus.ShimuraModFnTask

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
open ZInQ.Contrib.TYZGenus.Shimura (kappa idealLat discOf)

/-! ## §0. Verbatim copies (tyz-cm, `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean`) -/

/-- Verbatim copy of `Shimura.IsRatModFn`. -/
def IsRatModFn (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) ∧
  (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ k : ℕ,
      (fun τ : UpperHalfPlane => g (γ • τ)) =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
  ∃ (k : ℕ) (a : ℕ → ℚ), ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (a n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n)
      (cexp (2 * Real.pi * I * τ) ^ k * g τ)

/-- Verbatim copy of `Shimura.ShimuraReciprocityModFn` (tyz-cm's leaf SHIMURA-MODFN). -/
def ShimuraReciprocityModFn : Prop :=
  ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
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
      ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'

theorem isRatModFn_eq : IsRatModFn = Shimura.IsRatModFn := rfl

theorem shimuraReciprocityModFn_eq : ShimuraReciprocityModFn = Shimura.ShimuraReciprocityModFn :=
  rfl

/-! ## §1. Klein's `j` and the main theorem of complex multiplication for `j` -/

/-- **Klein's modular invariant** `j(τ) = E₄(τ)³/Δ(τ)` (Mathlib's normalized Eisenstein series
`E₄ = 1 + 240q + …` and discriminant `Δ = q∏(1 − qⁿ)²⁴`), so `j = q⁻¹ + 744 + …`;
`j(τ) = j(ℂ/⟨1, τ⟩)`. -/
def jInv (τ : UpperHalfPlane) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

/-- The lattice `⟨1, τ⟩ ⊂ ℂ`. -/
def latH (τ : UpperHalfPlane) : Submodule ℤ ℂ := Submodule.span ℤ {1, (τ : ℂ)}

/-- `L` is stable under `κ(O)`, `O = ℤ + f𝓞_K` (equivalently: the multiplier ring of `L`
contains `O`, so `L` is a proper ideal of an order `O' ⊇ O`). -/
def IsOStable (m f : ℕ) [NeZero m] [NeZero f] (L : Submodule ℤ ℂ) : Prop :=
  ∀ o ∈ (conductorOrder (QNeg m) f).toSubalgebra, ∀ x ∈ L, kappa m o * x ∈ L

/-- `N·τ ∈ ℍ` (junk `τ` for `N = 0`). -/
def scaleH (N : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if h : 0 < N then
    ⟨(N : ℂ) * τ, by
      have h1 : (0 : ℝ) < N := by exact_mod_cast h
      simpa [Complex.mul_im] using mul_pos h1 τ.im_pos⟩
  else τ

/-- **Leaf CM-J (main theorem of complex multiplication for `j`; ideal-class form).** Let
`K = ℚ(√−m)` (`m` squarefree), `O = ℤ + f𝓞_K`, `H_O` its ring class field, `e : Kˢ → ℚ̄` inducing
the normalized embedding `√−m ↦ i√m` on `K` (through `ιC : ℚ̄ → ℂ`), and `τ ∈ ℍ` with
`κ(O)·⟨1, τ⟩ ⊆ ⟨1, τ⟩`. Then

* `j(τ) ∈ e(H_O)` (`K(j(𝔞)) = H_{O'} ⊆ H_O` for the order `O' ⊇ O` of `𝔞 = ⟨1, τ⟩`), and
* for an ideal `J` of `𝓞_K` prime to `f`, `ρ ∈ Gal(ℚ̄/ℚ)` acting on `e(H_O)` as the Artin symbol
  of the class of `𝔟 = J ∩ O`, and `τ' ∈ ℍ` with `⟨1, τ'⟩` also `κ(O)`-stable and
  `κ(𝔟)·⟨1, τ'⟩ = c·⟨1, τ⟩` (i.e. `⟨1, τ'⟩ = c·𝔟⁻¹⟨1, τ⟩`): `ρ(j(τ)) = j(τ')`, i.e.
  `j(𝔞)^{Art(𝔟)} = j(𝔟⁻¹𝔞)`.

Sources (refereed textbooks; theorem numbers from memory, UNVERIFIED): Shimura, *Introduction to
the arithmetic theory of automorphic functions* (1971), Thm. 5.4 and its corollary for `j`
(`j(𝔞)^{[s,K]} = j(s⁻¹𝔞)`), Thm. 5.7; Cox, *Primes of the form x² + ny²*, Thm. 11.1
(`K(j(O)) = H_O`) and Cor. 11.37 (`σ_𝔭(j(𝔞)) = j(𝔭̄𝔞)`, `𝔭̄𝔞 ∼ 𝔭⁻¹𝔞`); Lang, *Elliptic
functions*, Ch. 10, Thm. 5 and Ch. 11; Silverman, *Advanced topics*, GTM 151, Thm. II.4.3 (maximal
order). For a lattice whose order `O'` strictly contains `O` the statement follows from the one for
`O'` and the functoriality `Art_O(𝔟)|_{H_{O'}} = Art_{O'}(𝔟O')` of the Artin map
(`H_{O'} ⊆ H_O`). Normalization: Tau Ceti's Artin map sends a prime to the arithmetic Frobenius,
and the arithmetic Frobenius of `𝔭` sends `j(𝔞)` to `j(𝔭⁻¹𝔞)`. The `κ(O)`-stability of `⟨1, τ'⟩`
is needed: without it `κ(𝔟)·L'` only determines `O·L'`. -/
def MainTheoremCMj : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ τ : UpperHalfPlane, IsOStable m f (latH τ) →
      (∃ x : ringClassField (conductorOrder (QNeg m) f), ιC (e x) = jInv τ) ∧
      ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
        (∀ x : ringClassField (conductorOrder (QNeg m) f),
          ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
            ((conductorOrder (QNeg m) f).picClass J) x)) →
        ∀ (τ' : UpperHalfPlane) (c : ℂ), IsOStable m f (latH τ') →
          idealLat m f J * latH τ' = (latH τ).map (LinearMap.mulLeft ℤ c) →
          ∃ a a' : Qbar, ιC a = jInv τ ∧ ιC a' = jInv τ' ∧ ρ a = a'

/-! ## §2. The `j`-part of the reciprocity law at Heegner pairs (glue) -/

theorem latH_tauH {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : latH Q.tauH = Q.lat := rfl

theorem heegnerForm_N_pos {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exfalso
    obtain ⟨k, hk⟩ := Q.N_dvd
    have h2 := Q.A_pos
    have h0 : (N : ℤ) = 0 := by exact_mod_cast h
    rw [h0, zero_mul] at hk
    omega
  · exact h

theorem latH_scaleH {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    latH (scaleH N Q.tauH) = Q.latN.map (LinearMap.mulLeft ℤ (N : ℂ)) := by
  have hN := heegnerForm_N_pos Q
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [latH, scaleH, dif_pos hN, HeegnerForm.latN, Submodule.map_span, Set.image_pair]
  congr 1
  simp only [LinearMap.mulLeft_apply]
  rw [mul_one_div_cancel hN0]
  rfl

theorem isOStable_map {m f : ℕ} [NeZero m] [NeZero f] {L : Submodule ℤ ℂ} (hL : IsOStable m f L)
    (c : ℂ) : IsOStable m f (L.map (LinearMap.mulLeft ℤ c)) := by
  intro o ho x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  refine Submodule.mem_map.2 ⟨kappa m o * y, hL o ho y hy, ?_⟩
  simp only [LinearMap.mulLeft_apply]
  ring

theorem mul_map_mulLeft (I M : Submodule ℤ ℂ) (c : ℂ) :
    I * M.map (LinearMap.mulLeft ℤ c) = (I * M).map (LinearMap.mulLeft ℤ c) := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro i hi y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨i * z, Submodule.mul_mem_mul hi hz, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    ring
  · rw [Submodule.map_le_iff_le_comap, Submodule.mul_le]
    intro i hi z hz
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    have : c * (i * z) = i * (c * z) := by ring
    rw [this]
    exact Submodule.mul_mem_mul hi (Submodule.mem_map.2 ⟨z, hz, rfl⟩)

theorem map_mulLeft_comm (M : Submodule ℤ ℂ) (a b : ℂ) :
    (M.map (LinearMap.mulLeft ℤ a)).map (LinearMap.mulLeft ℤ b) =
      (M.map (LinearMap.mulLeft ℤ b)).map (LinearMap.mulLeft ℤ a) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  ring

section JPart
variable {m f : ℕ} [NeZero m] [NeZero f]

/-- **The `j`-part of the reciprocity law at a Heegner pair.** Under the hypotheses of
`ShimuraReciprocityModFn`, `MainTheoremCMj` gives `ρ(j(τ_Q)) = j(τ_{Q'})` and
`ρ(j(Nτ_Q)) = j(Nτ_{Q'})` (`j(Nτ) = j(⟨1/N, τ⟩)`). -/
theorem jPair_reciprocity (hj : MainTheoremCMj) (hsq : Squarefree m)
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ)
    (hρ : ∀ x : ringClassField (conductorOrder (QNeg m) f),
      ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
        ((conductorOrder (QNeg m) f).picClass J) x))
    {N : ℕ} {D : ℤ} (hD : D = discOf m f) (Q Q' : HeegnerForm N D) (c : ℂ)
    (hL : idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c))
    (hLN : idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c)) :
    (∃ a a' : Qbar, ιC a = jInv Q.tauH ∧ ιC a' = jInv Q'.tauH ∧ ρ a = a') ∧
    (∃ b b' : Qbar, ιC b = jInv (scaleH N Q.tauH) ∧ ιC b' = jInv (scaleH N Q'.tauH) ∧ ρ b = b') := by
  have hQ : IsOStable m f (latH Q.tauH) := fun o ho =>
    Shimura.kappa_mul_mem_lat hsq hD Q ho
  have hQ' : IsOStable m f (latH Q'.tauH) := fun o ho =>
    Shimura.kappa_mul_mem_lat hsq hD Q' ho
  have hQN : IsOStable m f (latH (scaleH N Q.tauH)) := by
    rw [latH_scaleH]
    exact isOStable_map (fun o ho => Shimura.kappa_mul_mem_latN_gen hsq hD Q ho) _
  have hQN' : IsOStable m f (latH (scaleH N Q'.tauH)) := by
    rw [latH_scaleH]
    exact isOStable_map (fun o ho => Shimura.kappa_mul_mem_latN_gen hsq hD Q' ho) _
  refine ⟨(hj m f hsq e he Q.tauH hQ).2 J ρ hρ Q'.tauH c hQ' hL, ?_⟩
  refine (hj m f hsq e he (scaleH N Q.tauH) hQN).2 J ρ hρ (scaleH N Q'.tauH) c hQN' ?_
  rw [latH_scaleH, latH_scaleH, mul_map_mulLeft, hLN, map_mulLeft_comm]

end JPart

/-! ## §3. From `j, j_N` to `g` at points where a representation is regular (glue) -/

/-- `P(j(τ), j(Nτ))` for `P ∈ ℚ[X₀, X₁]`. -/
def evalJ (N : ℕ) (P : MvPolynomial (Fin 2) ℚ) (τ : UpperHalfPlane) : ℂ :=
  MvPolynomial.aeval (![jInv τ, jInv (scaleH N τ)]) P

theorem ιCA_comp_vec (a b : Qbar) : (fun i => ιCA (![a, b] i)) = ![ιCA a, ιCA b] := by
  funext i
  fin_cases i <;> rfl

theorem gal_comp_vec (ρ : GalQ) (a b : Qbar) :
    (fun i => ρ.toAlgHom (![a, b] i)) = ![ρ a, ρ b] := by
  funext i
  fin_cases i <;> rfl

section Rep
variable {m f : ℕ} [NeZero m] [NeZero f]

/-- **Reciprocity for `g` at a Heegner pair, from `MainTheoremCMj` and a representation
`B(j, j_N)·g = A(j, j_N)` (`A, B ∈ ℚ[X, Y]`) with `B(j(τ_Q), j(Nτ_Q)) ≠ 0`.** No condition on
`g` beyond the representation. -/
theorem reciprocity_of_rep (hj : MainTheoremCMj) {N : ℕ} (g : UpperHalfPlane → ℂ)
    (A B : MvPolynomial (Fin 2) ℚ) (hrep : ∀ τ, evalJ N B τ * g τ = evalJ N A τ)
    (hsq : Squarefree m) (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ)
    (hρ : ∀ x : ringClassField (conductorOrder (QNeg m) f),
      ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
        ((conductorOrder (QNeg m) f).picClass J) x))
    {D : ℤ} (hD : D = discOf m f) (Q Q' : HeegnerForm N D) (c : ℂ)
    (hL : idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c))
    (hLN : idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c))
    (hB : evalJ N B Q.tauH ≠ 0) :
    ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a' := by
  obtain ⟨⟨a0, a0', ha0, ha0', hρa⟩, ⟨b0, b0', hb0, hb0', hρb⟩⟩ :=
    jPair_reciprocity hj hsq e he J ρ hρ hD Q Q' c hL hLN
  -- evaluation through `ιCA`
  have hev : ∀ (P : MvPolynomial (Fin 2) ℚ) (x y : Qbar) (τ : UpperHalfPlane),
      ιC x = jInv τ → ιC y = jInv (scaleH N τ) →
      ιCA (MvPolynomial.aeval ![x, y] P) = evalJ N P τ := by
    intro P x y τ hx hy
    rw [MvPolynomial.comp_aeval_apply, ιCA_comp_vec, evalJ]
    rw [show ιCA x = jInv τ from hx, show ιCA y = jInv (scaleH N τ) from hy]
  have hgal : ∀ (P : MvPolynomial (Fin 2) ℚ) (x y : Qbar),
      ρ (MvPolynomial.aeval ![x, y] P) = MvPolynomial.aeval ![ρ x, ρ y] P := by
    intro P x y
    have := MvPolynomial.comp_aeval_apply (f := ![x, y]) ρ.toAlgHom P
    rw [gal_comp_vec] at this
    exact this
  set vB := MvPolynomial.aeval ![a0, b0] B
  set vA := MvPolynomial.aeval ![a0, b0] A
  have hvB : ιCA vB = evalJ N B Q.tauH := hev B a0 b0 Q.tauH ha0 hb0
  have hvA : ιCA vA = evalJ N A Q.tauH := hev A a0 b0 Q.tauH ha0 hb0
  have hvB' : ιCA (ρ vB) = evalJ N B Q'.tauH := by
    rw [hgal, hρa, hρb]; exact hev B a0' b0' Q'.tauH ha0' hb0'
  have hvA' : ιCA (ρ vA) = evalJ N A Q'.tauH := by
    rw [hgal, hρa, hρb]; exact hev A a0' b0' Q'.tauH ha0' hb0'
  have hvB0 : vB ≠ 0 := fun h => hB (by rw [← hvB, h, map_zero])
  have hvB0' : evalJ N B Q'.tauH ≠ 0 := by
    rw [← hvB']
    intro h
    exact hvB0 (ρ.injective (by rw [map_zero]; exact ιCA.toRingHom.injective (by rw [map_zero]; exact h)))
  refine ⟨vA / vB, ρ (vA / vB), ?_, ?_, rfl⟩
  · show ιCA (vA / vB) = _
    rw [map_div₀, hvA, hvB, ← hrep Q.tauH]
    field_simp
  · show ιCA (ρ (vA / vB)) = _
    rw [map_div₀, map_div₀, hvA', hvB', ← hrep Q'.tauH]
    field_simp

end Rep

/-! ## §4. Isolated points, the non-CM leaf `RatX0Rep`, and the split -/

/-- Index set of the `ψ(N)` cyclic `N`-isogenies of `ℂ/⟨1, τ⟩`: pairs `(a, b)` with `a ∣ N`,
`0 ≤ b < d = N/a`, `gcd(a, b, d) = 1` (the lattices `⟨1, (aτ + b)/d⟩` up to homothety). -/
def isogIdx (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Nat.divisors N) ×ˢ Finset.range N).filter
    (fun p => p.2 < N / p.1 ∧ Nat.gcd (Nat.gcd p.1 p.2) (N / p.1) = 1)

/-- `(aτ + b)/d ∈ ℍ` for `(a, b) ∈ isogIdx N`, `d = N/a` (junk `τ` otherwise). -/
def isogPt (N : ℕ) (p : ℕ × ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if h : 0 < p.1 ∧ 0 < N / p.1 then
    ⟨((p.1 : ℂ) * τ + p.2) / ((N / p.1 : ℕ) : ℂ), by
      have h1 : (0 : ℝ) < p.1 := by exact_mod_cast h.1
      have h2 : (0 : ℝ) < (N / p.1 : ℕ) := by exact_mod_cast h.2
      have : (((p.1 : ℂ) * τ + p.2) / ((N / p.1 : ℕ) : ℂ)).im = p.1 * τ.im / (N / p.1 : ℕ) := by
        rw [show ((N / p.1 : ℕ) : ℂ) = (((N / p.1 : ℕ) : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
        simp [Complex.mul_im]
      rw [this]
      have := τ.im_pos
      positivity⟩
  else τ

open Classical in
/-- **`τ` is an isolated point of the plane model `(j, j_N)` of `X₀(N)`**: `j(Nτ)` is a simple
root of `Φ_N(j(τ), Y) = ∏_{(a,b)} (Y − j((aτ + b)/d))`, i.e. exactly one of the `ψ(N)` values
`j((aτ+b)/d)` equals `j(Nτ)` (the term `(a, b) = (N, 0)` is one of them). -/
def IsIsolated (N : ℕ) (τ : UpperHalfPlane) : Prop :=
  ((isogIdx N).filter (fun p => jInv (isogPt N p τ) = jInv (scaleH N τ))).card = 1

/-- For `N = 1` every point is isolated (`Φ₁ = Y − X`). -/
theorem isIsolated_one (τ : UpperHalfPlane) : IsIsolated 1 τ := by
  classical
  have hidx : isogIdx 1 = {(1, 0)} := by decide
  have hpt : isogPt 1 (1, 0) τ = scaleH 1 τ := by
    rw [isogPt, dif_pos (by norm_num), scaleH, dif_pos (by norm_num)]
    ext
    simp
  unfold IsIsolated
  rw [hidx, Finset.filter_singleton, if_pos (by rw [hpt])]
  rfl

/-- **Non-CM leaf RAT-X0 (`ℚ(X₀(N)) = ℚ(j, j_N)` with the conductor bound).** For `N ≥ 1` and
`g ∈ ℚ(X₀(N))` regular on `ℍ` (`IsRatModFn N g`) there are `A, B ∈ ℚ[X, Y]` with
`B(j, j_N)·g = A(j, j_N)` on `ℍ` and `B(j(τ), j(Nτ)) ≠ 0` at every isolated point `τ`.

Content (textbook; theorem numbers from memory, UNVERIFIED): take `B = ∂Φ_N/∂Y` for the modular
polynomial `Φ_N ∈ ℤ[X, Y]`, monic in `Y`, with `Φ_N(j(τ), Y) = ∏_{(a,b)} (Y − j((aτ+b)/d))`
(Cox, *Primes of the form x² + ny²*, Thm. 11.18; Lang, *Elliptic functions*, Ch. 5 §2), so
`B(j(τ), j(Nτ)) = ∏_{other roots} (j(Nτ) − root) ≠ 0` at isolated points. `g` is integral over
`ℚ[j]` (its poles are at the cusps, like those of `j`), `ℚ(X₀(N)) = ℚ(j, j_N)` (Shimura 1971,
Prop. 6.9 and §6.7 for the rational structure; Diamond–Shurman, *A first course in modular forms*,
§7.5–7.7), and for the integral closure `R` of the PID `ℚ[j]` in `ℚ(j)(j_N)` one has
`Φ_N'(j_N)·R ⊆ ℚ[j][j_N]` (Euler's lemma on the different: Serre, *Local fields*, Ch. III §6;
Neukirch, *Algebraic number theory*, Ch. III §2). Nothing about complex multiplication. -/
def RatX0Rep : Prop :=
  ∀ N : ℕ, 0 < N → ∀ g : UpperHalfPlane → ℂ, IsRatModFn N g →
    ∃ A B : MvPolynomial (Fin 2) ℚ, (∀ τ, evalJ N B τ * g τ = evalJ N A τ) ∧
      ∀ τ, IsIsolated N τ → evalJ N B τ ≠ 0

/-- **`ShimuraReciprocityModFn` at isolated Heegner points**, from the `j`-form of the main
theorem of CM and the non-CM leaf `RatX0Rep`. -/
theorem shimuraReciprocityModFn_isolated (hj : MainTheoremCMj) (hR : RatX0Rep) :
    ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
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
        IsIsolated N Q.tauH →
        ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a' := by
  intro N g hg m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN hiso
  obtain ⟨A, B, hrep, hB⟩ := hR N (heegnerForm_N_pos Q) g hg
  exact reciprocity_of_rep hj g A B hrep hsq e he J ρ hρ hD Q Q' c hL hLN (hB _ hiso)

/-- **Leaf SHIMURA-MODFN-SINGULAR (the level-structure part).** `ShimuraReciprocityModFn`
restricted to Heegner points `τ_Q` that are *not* isolated points of the plane model `(j, j_N)`
(two of the `ψ(N)` cyclic `N`-isogenies of `ℂ/⟨1, τ_Q⟩` have the same target `j`). A restriction of
`ShimuraReciprocityModFn`, hence a consequence of the same sources (Shimura 1971, Thm. 5.4 with
its action on torsion and the canonical model of `X₀(N)`, §6.7; Gross 1984, §1–§3; UNVERIFIED
numbers). At such points `j(τ), j(Nτ)` do not determine `g(τ)`: e.g. `N = 32`,
`Q = [32, 10, 1]`, `D = −28`: `j(τ_Q) = j(32τ_Q) = 255³`, but `x(τ_Q) = −1 + √−7`
(`jpair_check.out`), and among TYZ's class-7 points the cases `n = 7, 15, 47`
(`isolated_check.out`). -/
def ShimuraReciprocityModFnSingular : Prop :=
  ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
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
      ¬ IsIsolated N Q.tauH →
      ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'

/-- **The split:** `ShimuraReciprocityModFn ⇐ MainTheoremCMj ∧ RatX0Rep ∧
ShimuraReciprocityModFnSingular`. -/
theorem shimuraReciprocityModFn_of_split (hj : MainTheoremCMj) (hR : RatX0Rep)
    (hS : ShimuraReciprocityModFnSingular) : ShimuraReciprocityModFn := by
  intro N g hg m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN
  by_cases hiso : IsIsolated N Q.tauH
  · exact shimuraReciprocityModFn_isolated hj hR N g hg m f hsq e he J ρ hρ D hD Q Q' c hL hLN
      hiso
  · exact hS N g hg m f hsq e he J ρ hρ D hD Q Q' c hL hLN hiso

/-- The same split for tyz-cm's statement. -/
theorem shimuraReciprocityModFn_of_split' (hj : MainTheoremCMj) (hR : RatX0Rep)
    (hS : ShimuraReciprocityModFnSingular) : Shimura.ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_split hj hR hS

/-- Conversely the singular part is a restriction of the leaf. -/
theorem singular_of_shimuraReciprocityModFn (h : ShimuraReciprocityModFn) :
    ShimuraReciprocityModFnSingular := by
  intro N g hg m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN _
  exact h N g hg m f hsq e he J ρ hρ D hD Q Q' c hL hLN

/-! ## §5. `j` and `j_N` are rational modular functions (q-expansion bookkeeping, proved) -/

section JRational
open Metric Filter

theorem E4_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (w : UpperHalfPlane) :
    ModularForm.E₄ (γ • w) = UpperHalfPlane.denom γ w ^ 4 * ModularForm.E₄ w := by
  have h := SlashInvariantForm.slash_action_eqn'' (k := 4) ModularForm.E₄
    (γ := (γ : GL (Fin 2) ℝ)) (MonoidHom.mem_range.2 ⟨γ, rfl⟩) w
  rw [ModularGroup.sl_moeb]
  exact h

theorem discriminant_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (w : UpperHalfPlane) :
    ModularForm.discriminant (γ • w) =
      UpperHalfPlane.denom γ w ^ 12 * ModularForm.discriminant w :=
  Shimura.eta_pow_smul γ w

/-- **`j` is `SL₂(ℤ)`-invariant.** -/
theorem jInv_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    jInv (γ • τ) = jInv τ := by
  have hd : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have h0 := ModularForm.discriminant_ne_zero τ
  unfold jInv
  rw [E4_smul, discriminant_smul]
  field_simp

/-- `E₄` as a function of `q` (Mathlib's `cuspFunction` at the cusp `∞`, width 1). -/
def FE4 : ℂ → ℂ := UpperHalfPlane.cuspFunction 1 ModularForm.E₄

theorem qParam_one (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (τ : ℂ) = cexp (2 * Real.pi * I * τ) := by
  simp [Function.Periodic.qParam]

theorem FE4_q (τ : UpperHalfPlane) : FE4 (cexp (2 * Real.pi * I * τ)) = ModularForm.E₄ τ := by
  rw [← qParam_one]
  exact SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ τ one_mem_strictPeriods_SL
    one_ne_zero

theorem differentiableOn_FE4 : DifferentiableOn ℂ FE4 (ball (0 : ℂ) 1) := fun _ hq =>
  (ModularFormClass.differentiableAt_cuspFunction ModularForm.E₄ one_pos
    one_mem_strictPeriods_SL (mem_ball_zero_iff.1 hq)).differentiableWithinAt

theorem two_mem_Qc : (2 : ℂ) ∈ Shimura.Qc := ⟨2, by simp⟩

theorem isRatAt_FE4 : Shimura.IsRatAt FE4 := by
  have han : AnalyticAt ℂ FE4 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos one_mem_strictPeriods_SL
  refine ⟨fun n => han.contDiffAt, fun n => ?_⟩
  have hc := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) ⟨2, rfl⟩ n
  rw [UpperHalfPlane.qExpansion_coeff] at hc
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have he : iteratedDeriv n FE4 0 = n.factorial *
      (if n = 0 then 1 else -(2 * ((4 : ℕ) : ℂ) / (bernoulli 4 : ℂ)) * (ArithmeticFunction.sigma (4 - 1) n : ℂ)) := by
    rw [← hc]
    unfold FE4
    field_simp
  rw [he]
  refine Shimura.Qc.mul_mem (Shimura.natCast_mem_Qc _) ?_
  split_ifs
  · exact Shimura.Qc.one_mem
  · exact Shimura.Qc.mul_mem (Shimura.Qc.neg_mem (Shimura.Qc.div_mem
      (Shimura.Qc.mul_mem two_mem_Qc (Shimura.natCast_mem_Qc 4)) (Shimura.ratCast_mem_Qc _)))
      (Shimura.natCast_mem_Qc _)

/-- `q·j(τ)` as a function of `q`: `E₄(q)³/∏(1 − qⁿ)²⁴`. -/
def Gj (q : ℂ) : ℂ := FE4 q ^ 3 / Shimura.pd 1 q ^ 24

theorem isRatAt_Gj : Shimura.IsRatAt Gj :=
  (isRatAt_FE4.pow 3).div ((Shimura.isRatAt_pd one_pos).pow 24)
    (by simp [Shimura.pd_zero 1 one_pos])

theorem differentiableOn_Gj : DifferentiableOn ℂ Gj (ball (0 : ℂ) 1) :=
  (differentiableOn_FE4.pow 3).div ((Shimura.differentiableOn_pd one_pos).pow 24)
    (fun _ hq => pow_ne_zero _ (Shimura.pd_ne_zero one_pos hq))

theorem discriminant_eq_pd (τ : UpperHalfPlane) :
    ModularForm.discriminant τ =
      cexp (2 * Real.pi * I * τ) * Shimura.pd 1 (cexp (2 * Real.pi * I * τ)) ^ 24 := by
  show ModularForm.eta (τ : ℂ) ^ 24 = _
  rw [Shimura.eta_eq_prodF, mul_pow, Shimura.pd, pow_one]
  congr 1
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem Gj_q (τ : UpperHalfPlane) :
    Gj (cexp (2 * Real.pi * I * τ)) = cexp (2 * Real.pi * I * τ) * jInv τ := by
  have hq : cexp (2 * Real.pi * I * τ) ≠ 0 := Complex.exp_ne_zero _
  have hp : Shimura.pd 1 (cexp (2 * Real.pi * I * τ)) ≠ 0 :=
    Shimura.pd_ne_zero one_pos (Shimura.q_mem_ball τ)
  rw [Gj, FE4_q, jInv, discriminant_eq_pd]
  field_simp

/-- **Rational `q`-expansion of `j`**: `q·j(τ) = Σ aₙ qⁿ` on `ℍ`, `aₙ ∈ ℚ`. -/
theorem jInv_qexp : ∃ a : ℕ → ℚ, ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (a n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n)
      (cexp (2 * Real.pi * I * τ) ^ 1 * jInv τ) := by
  obtain ⟨a, ha⟩ := Shimura.exists_rat_hasSum differentiableOn_Gj isRatAt_Gj
  refine ⟨a, fun τ => ?_⟩
  rw [pow_one, ← Gj_q]
  exact ha _ (Shimura.q_mem_ball τ)

theorem norm_q (τ : UpperHalfPlane) :
    ‖cexp (2 * Real.pi * I * τ)‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **`|j(τ)| ≤ C·e^{2π Im τ}` for `Im τ ≥ 1`.** -/
theorem jInv_bound : ∃ C : ℝ, ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
    ‖jInv τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  have hr1 : Real.exp (-(2 * Real.pi)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  have hsub : closedBall (0 : ℂ) (Real.exp (-(2 * Real.pi))) ⊆ ball 0 1 :=
    closedBall_subset_ball hr1
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (Real.exp (-(2 * Real.pi)))).exists_bound_of_continuousOn
    (differentiableOn_Gj.continuousOn.mono hsub)
  refine ⟨C, fun τ hτ => ?_⟩
  have hqb : cexp (2 * Real.pi * I * τ) ∈ closedBall (0 : ℂ) (Real.exp (-(2 * Real.pi))) :=
    mem_closedBall_zero_iff.2 (Shimura.norm_q_le τ hτ)
  have h1 := hC _ hqb
  rw [Gj_q, norm_mul, norm_q] at h1
  have hE : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (2 * Real.pi * τ.im)
  calc ‖jInv τ‖ = Real.exp (-(2 * Real.pi * τ.im)) * ‖jInv τ‖ * Real.exp (2 * Real.pi * τ.im) := by
        rw [mul_comm (Real.exp _) ‖jInv τ‖, mul_assoc, hE, mul_one]
    _ ≤ C * Real.exp (2 * Real.pi * τ.im) := mul_le_mul_of_nonneg_right h1 hpos.le

theorem bigO_of_bound {F : UpperHalfPlane → ℂ} {C : ℝ} {k : ℕ} (T : ℝ)
    (h : ∀ τ : UpperHalfPlane, T ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (2 * Real.pi * k * τ.im)) :
    F =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (2 * Real.pi * k * τ.im) := by
  refine Asymptotics.IsBigO.of_bound C ?_
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
  refine ⟨T, fun τ hτ => ?_⟩
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact h τ hτ

/-- **`j ∈ ℚ(X₀(N))` (no poles on `ℍ`), for every `N`.** -/
theorem isRatModFn_jInv (N : ℕ) : IsRatModFn N jInv := by
  obtain ⟨C, hC⟩ := jInv_bound
  obtain ⟨a, ha⟩ := jInv_qexp
  refine ⟨fun γ _ τ => jInv_smul γ τ, fun γ => ⟨1, ?_⟩, ⟨1, a, ha⟩⟩
  simp_rw [jInv_smul]
  refine bigO_of_bound (C := C) 1 fun τ hτ => ?_
  simpa using hC τ hτ

theorem coe_scaleH {N : ℕ} (hN : 0 < N) (τ : UpperHalfPlane) :
    ((scaleH N τ : UpperHalfPlane) : ℂ) = (N : ℂ) * τ := by
  rw [scaleH, dif_pos hN]

theorem scaleH_gamma0 {N : ℕ} (hN : 0 < N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ, scaleH N (γ • τ) = γ' • scaleH N τ := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  let γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![γ 0 0, N * γ 0 1; c', γ 1 1], by
      rw [Matrix.det_fin_two_of]; rw [hc'] at hdet; linear_combination hdet⟩
  refine ⟨γ', ?_⟩
  apply UpperHalfPlane.ext
  rw [coe_scaleH hN, UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply, coe_scaleH hN]
  simp only [γ', Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    algebraMap_int_eq, eq_intCast]
  have hden : ((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    simpa [ModularGroup.denom_apply] using this
  have hc'C : ((γ 1 0 : ℝ) : ℂ) = (N : ℂ) * (c' : ℂ) := by
    rw [hc']; push_cast; ring
  have hden' : ((c' : ℝ) : ℂ) * ((N : ℂ) * τ) + ((γ 1 1 : ℝ) : ℂ) ≠ 0 := by
    convert hden using 1
    rw [hc'C]; push_cast; ring
  have hc'C2 : ((γ 1 0 : ℤ) : ℂ) = (N : ℂ) * (c' : ℂ) := by
    rw [hc']; push_cast; ring
  rw [mul_div_assoc', div_eq_div_iff hden hden']
  push_cast
  rw [hc'C2]
  ring

/-- **`j_N = j(N·)` is invariant under `Γ₀(N)`.** -/
theorem jN_gamma0 {N : ℕ} (hN : 0 < N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    jInv (scaleH N (γ • τ)) = jInv (scaleH N τ) := by
  obtain ⟨γ', h⟩ := scaleH_gamma0 hN γ hγ τ
  rw [h, jInv_smul]

/-- **Growth of `j_N` at every cusp**: `j(Nγτ) = O(e^{2πN Im τ})`. -/
theorem jN_growth {N : ℕ} (hN : 0 < N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (fun τ : UpperHalfPlane => jInv (scaleH N (γ • τ))) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (2 * Real.pi * N * τ.im) := by
  obtain ⟨C, hC⟩ := jInv_bound
  refine bigO_of_bound (C := |C|) N fun τ hτ => ?_
  obtain ⟨γ', w, hw, h1, h2⟩ := Shimura.exists_smul_decomp hN γ τ
  have hsw : scaleH N (γ • τ) = γ' • w := by
    apply UpperHalfPlane.ext
    rw [coe_scaleH hN]
    exact hw
  rw [hsw, jInv_smul]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw1 : 1 ≤ w.im := le_trans (by rw [le_div_iff₀ hNR]; linarith) h1
  calc ‖jInv w‖ ≤ C * Real.exp (2 * Real.pi * w.im) := hC w hw1
    _ ≤ |C| * Real.exp (2 * Real.pi * w.im) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (2 * Real.pi * N * τ.im) := by
        have hpi := Real.pi_pos
        have hle : 2 * Real.pi * w.im ≤ 2 * Real.pi * N * τ.im := by nlinarith
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) (abs_nonneg C)

theorem q_scaleH {N : ℕ} (hN : 0 < N) (τ : UpperHalfPlane) :
    cexp (2 * Real.pi * I * (scaleH N τ : ℂ)) = cexp (2 * Real.pi * I * τ) ^ N := by
  rw [coe_scaleH hN, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- **`j_N = j(N·) ∈ ℚ(X₀(N))`** (no poles on `ℍ`), `N ≥ 1`. -/
theorem isRatModFn_jN {N : ℕ} (hN : 0 < N) : IsRatModFn N fun τ => jInv (scaleH N τ) := by
  obtain ⟨a, ha⟩ := jInv_qexp
  refine ⟨fun γ hγ τ => jN_gamma0 hN γ hγ τ, fun γ => ⟨N, jN_growth hN γ⟩, ?_⟩
  classical
  refine ⟨N, fun m => if N ∣ m then a (m / N) else 0, fun τ => ?_⟩
  set q := cexp (2 * Real.pi * I * τ)
  have hinj : Function.Injective fun n : ℕ => N * n := fun x y h =>
    Nat.eq_of_mul_eq_mul_left hN h
  have hz : ∀ x ∉ Set.range (fun n : ℕ => N * n),
      (fun m : ℕ => (((if N ∣ m then a (m / N) else 0 : ℚ)) : ℂ) * q ^ m) x = 0 := by
    intro x hx
    have : ¬ N ∣ x := fun ⟨k, hk⟩ => hx ⟨k, hk.symm⟩
    simp [this]
  refine (hinj.hasSum_iff hz).1 ?_
  have h1 := ha (scaleH N τ)
  rw [q_scaleH hN, pow_one] at h1
  convert h1 using 1
  funext n
  simp only [Function.comp, Nat.dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hN, pow_mul]
  rfl

/-- **Consistency: the `j`-part at Heegner pairs follows from `ShimuraReciprocityModFn`**
(apply it to `g = j` and `g = j_N`, both in `ℚ(X₀(N))`). So on Heegner lattices the new leaf
`MainTheoremCMj` asks for nothing beyond tyz-cm's leaf. -/
theorem jPair_of_modFn (hS : ShimuraReciprocityModFn) {m f : ℕ} [NeZero m] [NeZero f]
    (hsq : Squarefree m) (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ)
    (hρ : ∀ x : ringClassField (conductorOrder (QNeg m) f),
      ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
        ((conductorOrder (QNeg m) f).picClass J) x))
    {N : ℕ} {D : ℤ} (hD : D = discOf m f) (Q Q' : HeegnerForm N D) (c : ℂ)
    (hL : idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c))
    (hLN : idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c)) :
    (∃ a a' : Qbar, ιC a = jInv Q.tauH ∧ ιC a' = jInv Q'.tauH ∧ ρ a = a') ∧
    (∃ b b' : Qbar, ιC b = jInv (scaleH N Q.tauH) ∧ ιC b' = jInv (scaleH N Q'.tauH) ∧ ρ b = b') :=
  ⟨hS N jInv (isRatModFn_jInv N) m f hsq e he J ρ hρ D hD Q Q' c hL hLN,
    hS N (fun τ => jInv (scaleH N τ)) (isRatModFn_jN (heegnerForm_N_pos Q)) m f hsq e he J ρ hρ
      D hD Q Q' c hL hLN⟩

end JRational

end ZInQ.Contrib.TYZGenus.ShimuraModFnTask


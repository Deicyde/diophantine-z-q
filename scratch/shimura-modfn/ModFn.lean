import ZInQKernel.Contrib.TYZGenus.ShimuraMain

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

theorem HeegnerForm.N_pos {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exfalso
    have h1 := Q.N_dvd
    have h2 := Q.A_pos
    rw [h, Nat.cast_zero, zero_dvd_iff] at h1
    omega
  · exact h

theorem latH_scaleH {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    latH (scaleH N Q.tauH) = Q.latN.map (LinearMap.mulLeft ℤ (N : ℂ)) := by
  have hN := Q.N_pos
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [latH, scaleH, dif_pos hN, HeegnerForm.latN, Submodule.map_span, Set.image_pair]
  congr 1
  simp only [LinearMap.mulLeft_apply, UpperHalfPlane.coe_mk]
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
    congr 2
    · exact hx
    · exact hy
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
  obtain ⟨A, B, hrep, hB⟩ := hR N Q.N_pos g hg
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

end ZInQ.Contrib.TYZGenus.ShimuraModFnTask

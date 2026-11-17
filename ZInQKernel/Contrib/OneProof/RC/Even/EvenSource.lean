import ZInQKernel.Contrib.CloudB3RC53.Basic
import ZInQKernel.Contrib.OneProof.RC.Even.Lengths
import ZInQKernel.Contrib.OneProof.RC.Even.Calibration
import ZInQKernel.Contrib.OneProof.RC.Even.Membership
import ZInQKernel.Contrib.OneProof.RC.Even.Phase

/-!
# Theorem 5.3, Lane RC11-even: the even coefficient source — statements and assembly

The 11/5 manuscript (`diophantine_zq.tex`), Section 7.1 (Proposition `ex:sec7-even-scalar`,
tex 1825–1966) and Appendix E (`app:even-source`, tex 6825–8205). This file states, in Elliot's
order, what each proposition provides, names the inputs that are Elliot's constructions (ELLIOT),
printed theorems (PRINT) or textbook facts (GLUE), and PROVES the deductions that turn them into
the outputs used later in the proof of Theorem 5.3:

* vocabulary: `CorankZero E h` (`corank_{ℤ₂} Sel_{2^∞}(E^{(h)}/ℚ) = 0`, genuine), `shaLen E h`
  (`s(h) = length_{ℤ₂} Ш(E^{(h)}/ℚ)[2^∞]`, genuine), `CentralNormalization` (the normalized central
  values `L_*(h)` with the fixed periods, anchored to the genuine `L`-values,
  `CentralNormalization.lstar_ne_zero_iff` PROVED), `BinaryFamily` (a family of quadratic
  characters `χ_x = χ_0(x ∘ ε)` with one real sign and fixed squareclasses at `2N`);
* `EvenScalar32` — **Proposition `ex:sec7-even-scalar`, (3.2)** (tex 1832–1844, 1945–1946);
* `CentralLengthInput` with `CentralLengthInput.E7` — the Kummer-duality bookkeeping (E.6)–(E.7)
  of Proposition `ex:app-central-calibration` (tex 7631–7754), PROVED from its exact sequences;
* `CentralLocalInput` with `CentralLocalInput.E8` — (E.8) (tex 7755–7775), PROVED;
* `EvenFamilyOutput`, `AppEOutputs` — what Propositions `ex:app-kato-system` (K1)–(K3),
  `ex:app-even-scalar` (E.3)–(E.5) and `ex:app-central-calibration` provide for one family
  (ELLIOT, with the PRINT inputs named in the docstrings);
* `evenScalar32_of_appE` — **(3.2) from Appendix E** (PROVED);
* `EvenLowerBound`, `evenLowerBound_of_evenScalar32` — **(E.9)** (tex 7782–7785; PROVED, with the
  forward rank-zero theorem as input);
* `EvenFormInput`, `EvenFormInput.E11`, `EvenFormInput.minimum` — Proposition
  `ex:app-even-phase`: (E.11) and the finite attained minimum of `v₂ a(D) − ω(D)` (tex 7792–8200;
  PROVED from the form's interface).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Even

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Module Submodule

attribute [local instance] Nat.fact_prime_two

/-! ## Vocabulary -/

/-- **`E^{(h)}` has Selmer corank zero**: `corank_{ℤ₂} Sel_{2^∞}(E^{(h)}/ℚ) = 0` (genuine, over the
tree's `Sel_{2^∞}` and the shared layer's twist `qtwist`). -/
def CorankZero (E : WeierstrassCurve ℚ) (h : ℤ) : Prop :=
  Z2Corank (selmerTwoPower (qtwist E h)) 0

/-- **`s(h) = length_{ℤ₂} Ш(E^{(h)}/ℚ)[2^∞]`** (tex 1829–1830): `log₂` of the order of the
`2`-primary part of the tree's genuine `Ш(E^{(h)}/ℚ)`. Used only where that group is finite (at
corank zero); otherwise the value is the junk `0`. -/
def shaLen (E : WeierstrassCurve ℚ) (h : ℤ) : ℕ :=
  Nat.log 2 (Nat.card (AddCommGroup.primaryComponent (sha (qtwist E h)) 2))

/-- The central value `u(0)` of `u ∈ ℚ₂[[t]]`. -/
def central (u : PowerSeries ℚ_[2]) : ℚ_[2] := PowerSeries.coeff 0 u

/-- **The normalized central values `L_*(h)`** (tex 1826–1828, 7175–7177): fixed real and
imaginary periods `Ω⁺ = |Ω⁺|`, `|Ω⁻|` (chosen once, by `π` and the integral lattice) and rational
numbers `L_*(h)` with `L_*(h) = √|h| L(E^{(h)}, 1)/|Ω^ε|`, `ε = sign h`, for the value at `1` of
every entire continuation of `L(E^{(h)}, s)`. Its existence is GLUE: the rationality of
`√|h| L(E^{(h)},1)/Ω^ε` is the theorem of Birch and Manin on modular symbols. The anchor ties
`L_*` to the genuine `L`-series of the twists; the periods are the only free data. -/
structure CentralNormalization (E : WeierstrassCurve ℚ) where
  /-- `|Ω⁺|` -/
  Ωp : ℝ
  /-- `|Ω⁻|` -/
  Ωm : ℝ
  Ωp_pos : 0 < Ωp
  Ωm_pos : 0 < Ωm
  /-- `L_*(h) ∈ ℚ` -/
  Lstar : ℤ → ℚ
  /-- `L_*(h) = √|h| F(1)/|Ω^{sign h}|` for every entire continuation `F` of `L(E^{(h)}, s)`. -/
  anchor : ∀ h : ℤ, h ≠ 0 → ∀ F : ℂ → ℂ, IsLContinuation (qtwist E h) F →
    (((Lstar h : ℚ) : ℝ) : ℂ) =
      (Real.sqrt |(h : ℝ)| : ℂ) * F 1 / (((if 0 < h then Ωp else Ωm : ℝ)) : ℂ)

/-- Two entire continuations of the same `L`-series agree (PROVED; identity theorem). -/
theorem IsLContinuation.unique {W : WeierstrassCurve ℚ} {F G : ℂ → ℂ}
    (hF : IsLContinuation W F) (hG : IsLContinuation W G) : F = G := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.1.analyticAt z
  have hGa : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.1.analyticAt z
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by
    show (3 : ℝ) / 2 < (2 : ℂ).re
    norm_num
  have hev : F =ᶠ[nhds (2 : ℂ)] G := by
    filter_upwards [hopen.mem_nhds h2] with s hs
    rw [hF.2 s hs, hG.2 s hs]
  funext z
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_univ (Set.mem_univ 2) hev
    (Set.mem_univ z)

/-- **`L_*(h) ≠ 0` exactly when `L(E^{(h)}, 1) ≠ 0`** (tex 1825–1830, 1841–1843; PROVED from the
anchor, given one entire continuation — modularity, BCDT with Hecke's theory). This is the
`lstar_ne_zero_iff` input of the deduction skeleton. -/
theorem CentralNormalization.lstar_ne_zero_iff {E : WeierstrassCurve ℚ}
    (N : CentralNormalization E) {h : ℤ} (hh : h ≠ 0) {F : ℂ → ℂ}
    (hF : IsLContinuation (qtwist E h) F) :
    N.Lstar h ≠ 0 ↔ AnalyticRank (qtwist E h) 0 := by
  have hval : (((N.Lstar h : ℚ) : ℝ) : ℂ) ≠ 0 ↔ F 1 ≠ 0 := by
    rw [N.anchor h hh F hF]
    have hsq : (Real.sqrt |(h : ℝ)| : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt |(h : ℝ)| :=
        Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr hh))
      exact_mod_cast this.ne'
    have hΩ : (((if 0 < h then N.Ωp else N.Ωm : ℝ)) : ℂ) ≠ 0 := by
      have : (if 0 < h then N.Ωp else N.Ωm) ≠ 0 := by
        split_ifs
        · exact N.Ωp_pos.ne'
        · exact N.Ωm_pos.ne'
      exact_mod_cast this
    constructor
    · intro h1 h0
      exact h1 (by rw [h0, mul_zero, zero_div])
    · intro h1
      exact div_ne_zero (mul_ne_zero hsq h1) hΩ
  have hcast : N.Lstar h ≠ 0 ↔ (((N.Lstar h : ℚ) : ℝ) : ℂ) ≠ 0 := by
    simp
  rw [hcast, hval]
  constructor
  · intro h1
    refine ⟨F, hF.1, hF.2, ?_⟩
    have := (hF.1.analyticAt (1 : ℂ)).analyticOrderAt_eq_zero.mpr h1
    exact_mod_cast this
  · rintro ⟨G, hGd, hGe, hGo⟩
    have hG : IsLContinuation (qtwist E h) G := ⟨hGd, hGe⟩
    rw [IsLContinuation.unique hF hG]
    have : analyticOrderAt G 1 = 0 := by exact_mod_cast hGo
    exact (hGd.analyticAt (1 : ℂ)).analyticOrderAt_eq_zero.mp this

/-! ## Binary families -/

/-- **An admissible binary family** (tex 1834–1837, 1864–1873, 6851–6859). The characters
`χ_x = χ_0(x ∘ ε)` of `G = 𝔽₂^b`, indexed by `x ∈ Ĝ ≅ 𝔽₂^b`, are the quadratic characters
`χ_{h(x)}` of the odd squarefree signed parameters `h(x)`, with
* one real sign: `ε(c) = 1` for complex conjugation, i.e. `sign h(x) = sign h(0)`;
* the same restrictions at every place dividing `2N`: `ε|_{G_{ℚ_v}} = 1`, i.e. `h(x) h(0)` is a
  square in `ℚ_p` for every prime `p ∣ 2N`;
* the character law `χ_{x+y} χ_0 = χ_x χ_y`, i.e. `h(x+y) h(x) h(y) h(0)` is a square. -/
structure BinaryFamily (N : ℕ) where
  /-- the binary dimension `b`, `G = 𝔽₂^b` -/
  b : ℕ
  /-- the signed parameter of the constituent `x` -/
  h : (Fin b → ZMod 2) → ℤ
  odd : ∀ x, Odd (h x)
  sqfree : ∀ x, Squarefree (h x)
  sign : ∀ x, (0 < h x ↔ 0 < h 0)
  local_sq : ∀ x, ∀ p : Nat.Primes, (p : ℕ) ∣ 2 * N → IsSquare (((h x * h 0 : ℤ) : ℚ_[(p : ℕ)]))
  hom : ∀ x y, IsSquare (h (x + y) * h x * h y * h 0)

/-- The one-element family `G = 1` at a single odd squarefree parameter (the lower bound uses
`G = 1`, tex 1871). -/
def BinaryFamily.single (N : ℕ) (h : ℤ) (hodd : Odd h) (hsq : Squarefree h) : BinaryFamily N where
  b := 0
  h := fun _ => h
  odd := fun _ => hodd
  sqfree := fun _ => hsq
  sign := fun _ => Iff.rfl
  local_sq := fun _ _ _ => ⟨(h : ℚ_[_]), by push_cast; ring⟩
  hom := fun _ _ => ⟨h * h, by ring⟩

/-! ## (3.2): Proposition `ex:sec7-even-scalar` -/

/-- **(3.2), Proposition `ex:sec7-even-scalar`** (tex 1832–1844, 1945–1946, 1956–1957): there are
a clearing exponent `C_ev` and a bound `C`, fixed before the binary group and the support, such
that for every admissible family there is one scalar `u^{ev} ∈ Λ[1/2][G]` (its group-basis
coefficients `u g ∈ ℚ₂[[t]]`) with
* `2^{C_ev} u^{ev} ∈ Λ[G]`;
* at a corank-zero constituent, `u_h(0) = 0 ↔ L_*(h) = 0`;
* at a corank-zero constituent with `L_*(h) ≠ 0`,
  `v₂ u_h(0) = v₂ L_*(h) − 2ω(h) − s(h) + O(1)`, `|O(1)| ≤ C`.

Non-vacuity: the integrality is uniform in `b` while `u_x = Σ_g x(g) u_g`, so (3.2) is a genuine
constraint; at `b = 0` it already gives the lower bound (E.9) (`evenLowerBound_of_evenScalar32`). -/
def EvenScalar32 (E : WeierstrassCurve ℚ) (N : ℕ) (L : CentralNormalization E) : Prop :=
  ∃ Cev C : ℕ, ∀ fam : BinaryFamily N, ∃ u : (Fin fam.b → ZMod 2) → PowerSeries ℚ_[2],
    (∀ g, InLam ((2 : ℚ_[2]) ^ Cev • u g)) ∧
    (∀ x, CorankZero E (fam.h x) → (central (charEval u x) = 0 ↔ L.Lstar (fam.h x) = 0)) ∧
    (∀ x, CorankZero E (fam.h x) → L.Lstar (fam.h x) ≠ 0 →
      |(central (charEval u x)).valuation -
        (padicValRat 2 (L.Lstar (fam.h x)) - 2 * (omega (fam.h x) : ℤ) -
          (shaLen E (fam.h x) : ℤ))| ≤ C)

/-! ## (E.6)–(E.7): the Kummer-duality bookkeeping -/

/-- **The exact sequences of the central calibration at one corank-zero constituent**
(Proposition `ex:app-central-calibration`, tex 7631–7754), over `ℤ₂`. ELLIOT inputs (each field
names its source):
* the orthogonal-Kummer Poitou–Tate sequence
  `0 → L₂/J₂ → Sel^∨ → H²_glob → ⊕_{v∈S_f} H²(ℚ_v,T) ⊕ H²(ℝ,T) → H⁰(ℚ,D)^∨ → 0` (tex 7695–7714;
  Nekovář, *Selmer complexes*, 5.7.1.4–5.7.1.7, then compact/discrete limits), with the lengths
  `i`, `s = s(h)` (corank zero: `Sel_{2^∞} = Ш[2^∞]`), `G = Σ_v g_v` (local Tate duality, GLUE),
  `r₂`, `g` (Pontryagin duality, GLUE);
* the real map `ρ : H¹_glob → H¹(ℝ, T)` (`ℓ H¹(ℝ,T) = r₁`, `ℓ H¹_glob,tors = g`, GLUE:
  `H¹(T)_tors = H⁰(ℚ, D)`), its kernel `K` with torsion length `k` and free index `m`;
* the positive cone `0 → T⁺ →a P → K → 0` (`P = H¹(C_h⁺)`, `T⁺ = H⁰(ℝ, T)` torsion-free) with
  `p₀ = ℓ P_tors` and the saturation index `a_s` (tex 7737–7747);
* the positive cone in degree two `0 → coker ρ → H²(C_h⁺) → H²_glob → H²(ℝ,T) → 0` (tex 7736–7740);
* the wedge (E.4) contributes `a_s + 1 + v_free(z) − m` and the inverse determinant conversion
  `p₀ − ℓ H²(C_h⁺)` (tex 7653–7654, 7748–7750; GLUE: the determinant of a perfect complex over a
  DVR), and `v₂ exp* z = v_free(z) + i + e₂` (tex 7752). -/
structure CentralLengthInput where
  X₁ : Type
  X₂ : Type
  X₃ : Type
  Xloc : Type
  XR : Type
  X₅ : Type
  [g₁ : AddCommGroup X₁]
  [m₁ : Module ℤ_[2] X₁]
  [g₂ : AddCommGroup X₂]
  [m₂ : Module ℤ_[2] X₂]
  [g₃ : AddCommGroup X₃]
  [m₃ : Module ℤ_[2] X₃]
  [gl : AddCommGroup Xloc]
  [ml : Module ℤ_[2] Xloc]
  [gR : AddCommGroup XR]
  [mR : Module ℤ_[2] XR]
  [g₅ : AddCommGroup X₅]
  [m₅ : Module ℤ_[2] X₅]
  f₁ : X₁ →ₗ[ℤ_[2]] X₂
  f₂ : X₂ →ₗ[ℤ_[2]] X₃
  f₃ : X₃ →ₗ[ℤ_[2]] Xloc × XR
  f₄ : Xloc × XR →ₗ[ℤ_[2]] X₅
  ex₁ : Function.Injective f₁
  ex₁₂ : Function.Exact f₁ f₂
  ex₂₃ : Function.Exact f₂ f₃
  ex₃₄ : Function.Exact f₃ f₄
  ex₄ : Function.Surjective f₄
  i : ℕ
  s : ℕ
  G : ℕ
  r₂ : ℕ
  g : ℕ
  len₁ : length ℤ_[2] X₁ = i
  len₂ : length ℤ_[2] X₂ = s
  lenloc : length ℤ_[2] Xloc = G
  lenR : length ℤ_[2] XR = r₂
  len₅ : length ℤ_[2] X₅ = g
  /-- `H¹_glob` -/
  M : Type
  /-- `H¹(ℝ, T)` -/
  HR1 : Type
  [gM : AddCommGroup M]
  [mM : Module ℤ_[2] M]
  [gH : AddCommGroup HR1]
  [mH : Module ℤ_[2] HR1]
  ρ : M →ₗ[ℤ_[2]] HR1
  r₁ : ℕ
  k : ℕ
  m : ℕ
  lenHR1 : length ℤ_[2] HR1 = r₁
  lenTors : length ℤ_[2] ↥(torsion ℤ_[2] M) = g
  lenK : length ℤ_[2] ↥(LinearMap.ker ρ ⊓ torsion ℤ_[2] M) = k
  lenFree : length ℤ_[2] (M ⧸ (LinearMap.ker ρ ⊔ torsion ℤ_[2] M)) = m
  /-- `T⁺ = H⁰(ℝ, T)` -/
  Tp : Type
  /-- `P = H¹(C_h⁺)` -/
  P : Type
  [gT : AddCommGroup Tp]
  [mT : Module ℤ_[2] Tp]
  [gP : AddCommGroup P]
  [mP : Module ℤ_[2] P]
  a : Tp →ₗ[ℤ_[2]] P
  π : P →ₗ[ℤ_[2]] ↥(LinearMap.ker ρ)
  exa : Function.Injective a
  exaπ : Function.Exact a π
  exπ : Function.Surjective π
  torsFree : torsion ℤ_[2] Tp = ⊥
  p₀ : ℕ
  aₛ : ℕ
  lenP : length ℤ_[2] ↥(torsion ℤ_[2] P) = p₀
  lenSat : length ℤ_[2] (↥((torsion ℤ_[2] ↥(LinearMap.ker ρ)).comap π) ⧸
    (LinearMap.range a ⊔ torsion ℤ_[2] P).comap
      ((torsion ℤ_[2] ↥(LinearMap.ker ρ)).comap π).subtype) = aₛ
  /-- `H²(C_h⁺)` -/
  H2p : Type
  [gH2 : AddCommGroup H2p]
  [mH2 : Module ℤ_[2] H2p]
  j₁ : (HR1 ⧸ LinearMap.range ρ) →ₗ[ℤ_[2]] H2p
  j₂ : H2p →ₗ[ℤ_[2]] X₃
  j₃ : X₃ →ₗ[ℤ_[2]] XR
  exj₁ : Function.Injective j₁
  exj₁₂ : Function.Exact j₁ j₂
  exj₂₃ : Function.Exact j₂ j₃
  exj₃ : Function.Surjective j₃
  lH2p : ℕ
  lenH2p : length ℤ_[2] H2p = lH2p
  /-- `v₂ u_h^{ev}(0)` -/
  v2u : ℤ
  /-- `v_free(z)` -/
  vfree : ℤ
  /-- `e₂`, the valuation of `exp*` on a generator of `L₂` -/
  e₂ : ℤ
  /-- `v₂ exp* z` -/
  v2exp : ℤ
  wedge : v2u = ((aₛ : ℤ) + 1 + vfree - m) + ((p₀ : ℤ) - lH2p)
  expStar : v2exp = vfree + i + e₂

attribute [instance] CentralLengthInput.g₁ CentralLengthInput.m₁ CentralLengthInput.g₂
  CentralLengthInput.m₂ CentralLengthInput.g₃ CentralLengthInput.m₃ CentralLengthInput.gl
  CentralLengthInput.ml CentralLengthInput.gR CentralLengthInput.mR CentralLengthInput.g₅
  CentralLengthInput.m₅ CentralLengthInput.gM CentralLengthInput.mM CentralLengthInput.gH
  CentralLengthInput.mH CentralLengthInput.gT CentralLengthInput.mT CentralLengthInput.gP
  CentralLengthInput.mP CentralLengthInput.gH2 CentralLengthInput.mH2

/-- **(E.7)** (tex 7653–7660, 7748–7754; PROVED from the exact sequences of
`CentralLengthInput` by `E6_length`, `length_coker_eq`, `length_torsion_quotient`,
`length_exact_four` and `E7_of_lengths`):
`v₂ u_h^{ev}(0) = v₂ exp* z − s(h) − Σ_v g_v + 2g + 1 − r₁ − e₂`. -/
theorem CentralLengthInput.E7 (C : CentralLengthInput) :
    C.v2u = C.v2exp - C.s - C.G + 2 * C.g + 1 - C.r₁ - C.e₂ := by
  -- (E.6)
  obtain ⟨n, hn, hE6⟩ := E6_length C.f₁ C.f₂ C.f₃ C.f₄ C.ex₁ C.ex₁₂ C.ex₂₃ C.ex₃₄ C.ex₄
    C.i C.s C.G C.r₂ C.g C.len₁ C.len₂ C.lenloc C.lenR C.len₅
  -- the cokernel of the real map
  obtain ⟨c, hc, hcoker⟩ := length_coker_eq C.ρ C.r₁ C.g C.k C.m C.lenHR1 C.lenTors C.lenK
    C.lenFree
  -- `k = p₀ + a_s`
  have hk : length ℤ_[2] ↥(torsion ℤ_[2] ↥(LinearMap.ker C.ρ)) = C.p₀ + C.aₛ := by
    rw [length_torsion_quotient C.a C.π C.exa C.exaπ C.exπ C.torsFree, C.lenP, C.lenSat]
  have hk' : (C.k : ℕ∞) = C.p₀ + C.aₛ := by
    rw [← C.lenK, ← length_torsion_submodule, hk]
  have hk'' : C.k = C.p₀ + C.aₛ := by exact_mod_cast hk'
  -- the positive cone in degree two
  have hplus := length_exact_four C.j₁ C.j₂ C.j₃ C.exj₁ C.exj₁₂ C.exj₂₃ C.exj₃
  rw [hc, hn, C.lenH2p, C.lenR] at hplus
  have hplus' : c + n = C.lH2p + C.r₂ := by exact_mod_cast hplus
  exact E7_of_lengths C.v2u C.v2exp C.s C.G C.g C.r₁ C.r₂ C.e₂ C.i C.k C.m C.p₀ C.aₛ C.vfree n
    C.lH2p c hE6 (by omega) (by exact_mod_cast hk'') (by omega) C.wedge C.expStar

/-! ## (3.1) at the centre -/

/-- **The unused-prime factor (3.1)/(K9) at the centre** (tex 1876–1877, 7012–7015, 7202–7203;
PROVED): at `t = 0` the cyclotomic Frobenius is trivial, and
`E_q(χ)(0) = 1 − a_q χ(q)/q + 1/q = (q + 1 − χ(q) a_q)/q`, which is `#E^h(𝔽_q)/q` because
`a_q(E^h) = χ_h(q) a_q(E)` (GLUE). For odd `q` its two-adic valuation is that of `q + 1 − χ(q)a_q`,
the `v₂ #E^h(𝔽_q)` of (K3). -/
theorem unusedFactor_central {q : ℕ} (hq : Odd q) (a χ : ℤ) :
    ((1 : ℚ) - (a * χ : ℤ) / q + 1 / q) = ((q : ℚ) + 1 - (χ * a : ℤ)) / q ∧
      padicValRat 2 (((q : ℚ) + 1 - (χ * a : ℤ)) / q) = padicValRat 2 ((q : ℚ) + 1 - (χ * a : ℤ)) := by
  have hq0 : (q : ℚ) ≠ 0 := by
    have : q ≠ 0 := fun h => by simp [h] at hq
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · field_simp
    push_cast
    ring
  · by_cases h0 : ((q : ℚ) + 1 - (χ * a : ℤ)) = 0
    · rw [h0, zero_div]
    · rw [padicValRat.div h0 hq0]
      have : padicValRat 2 (q : ℚ) = 0 := by
        rw [padicValRat.of_nat]
        have : ¬ 2 ∣ q := by
          rintro ⟨k, rfl⟩
          exact (Nat.not_even_iff_odd.mpr hq) (even_two_mul k)
        exact_mod_cast padicValNat.eq_zero_of_not_dvd this
      rw [this, sub_zero]

/-! ## (E.8): the local terms -/

/-- **One corank-zero constituent with nonzero central value** (tex 7632–7787): the exact
sequences of `CentralLengthInput` together with the local terms of (E.8), for the places of
`S = prime(2NF)` split into the active good primes `act`, the unused good primes `unused` and the
fixed places `fix` (two and the bad primes), with the bounds `C_E, C_fix, C_g, C_r, C_e` of the
fixed local types. ELLIOT/GLUE inputs (each field names its source):
* `sumG` — the local `H²` term of (E.6) is `⊕_{v ∈ S_f} H²(ℚ_v,T)` of length `Σ_v g_v`;
* `K3` — (K3) for the retained class `z = F_E(Z_F)_h`, smoothing and old-support factors absorbed
  into `ε_rec` (tex 6880–6887, 7755–7766);
* `unusedEq` — `g_q = v₂ #E^h(𝔽_q)` at unused good primes (GLUE: at a good odd prime reduction is an
  isomorphism on `2`-primary torsion; tex 7767);
* `actEq` — `g_q = 2` at active good primes (tex 1963, 7768–7769: inertia acts by `−1`, so the
  invariants are `E[2]`; PROVED supports: `fixed_iff_two_nsmul_eq_zero`,
  `length_two_torsion_curveF`);
* `fixBd`, `gBd`, `r₁Bd`, `e₂Bd`, `recBd` — the remaining local types, the global torsion (by its
  injection at two), the real terms and `e₂` have fixed bounds (tex 7770–7771). -/
structure ConstituentOutput (act unused fix : Finset ℕ) (CE Cfix Cg Cr Ce : ℤ) where
  /-- the exact sequences of the central calibration -/
  len : CentralLengthInput
  /-- `g_v = ℓ E^h(ℚ_v)[2^∞]` -/
  gv : ℕ → ℤ
  /-- `v₂ #E^h(𝔽_q)` -/
  nq : ℕ → ℤ
  /-- `v₂ L_*(h)` -/
  v2L : ℤ
  /-- the bounded error of (K3) -/
  εrec : ℤ
  sumG : (len.G : ℤ) = ∑ v ∈ act ∪ unused ∪ fix, gv v
  K3 : len.v2exp = v2L + ∑ q ∈ unused, nq q + εrec
  recBd : |εrec| ≤ CE
  unusedEq : ∀ q ∈ unused, gv q = nq q
  actEq : ∀ q ∈ act, gv q = 2
  fixBd : ∀ v ∈ fix, 0 ≤ gv v ∧ gv v ≤ Cfix
  gBd : (len.g : ℤ) ≤ Cg
  r₁Bd : (len.r₁ : ℤ) ≤ Cr
  e₂Bd : |len.e₂| ≤ Ce

/-- **(E.8) at one constituent** (tex 7755–7775; PROVED from `CentralLengthInput.E7` and
`E8_of_E7_K3`): the unused-prime terms cancel, every active good prime contributes `−2`, and
`|v₂ u_h(0) − (v₂ L_*(h) − 2·#act − s(h))| ≤ C_E + #fix·C_fix + 2C_g + 1 + C_r + C_e`. -/
theorem ConstituentOutput.E8 {act unused fix : Finset ℕ} {CE Cfix Cg Cr Ce : ℤ}
    (hdau : Disjoint act unused) (hdaf : Disjoint act fix) (hduf : Disjoint unused fix)
    (O : ConstituentOutput act unused fix CE Cfix Cg Cr Ce) :
    |O.len.v2u - (O.v2L - 2 * (act.card : ℤ) - O.len.s)| ≤
      CE + fix.card * Cfix + 2 * Cg + 1 + Cr + Ce := by
  have hE7 := O.len.E7
  rw [O.sumG] at hE7
  exact E8_of_E7_K3 act unused fix hdau hdaf hduf O.gv O.nq O.len.v2u O.len.v2exp O.v2L O.len.s
    O.len.g O.len.r₁ O.len.e₂ O.εrec CE Cfix Cg Cr Ce hE7 O.K3 O.recBd O.unusedEq O.actEq O.fixBd
    ⟨Nat.cast_nonneg _, O.gBd⟩ ⟨Nat.cast_nonneg _, O.r₁Bd⟩ O.e₂Bd

/-! ## Appendix E for one family -/

/-- The prime support of a family: the primes of `F`, the squarefree least common multiple of the
odd parts of the primitive conductors (tex 6859–6860); the odd part of the conductor of `χ_h` is
`|h|` for odd `h`. -/
def BinaryFamily.support {N : ℕ} (fam : BinaryFamily N) : Finset ℕ :=
  Finset.univ.biUnion fun x => (fam.h x).natAbs.primeFactors

/-- The unused good primes of the constituent `h` of a family with prime support `F`: the primes of
`F` not dividing `h` (all good: `unused_disjoint_fixed`). -/
def unusedPrimes (F : Finset ℕ) (h : ℤ) : Finset ℕ := F.filter (fun q => ¬ (q : ℤ) ∣ h)

/-- A square in `ℚ_q` of a product of nonzero integers has even total valuation (PROVED). -/
theorem even_padicValInt_of_isSquare {q : ℕ} [Fact q.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsq : IsSquare (((a * b : ℤ) : ℚ_[q]))) : Even (padicValInt q a + padicValInt q b) := by
  obtain ⟨y, hy⟩ := hsq
  have hab : ((a * b : ℤ) : ℚ_[q]) ≠ 0 := by exact_mod_cast mul_ne_zero ha hb
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hab (by rw [hy, mul_zero])
  have hv := congrArg Padic.valuation hy
  rw [Padic.valuation_intCast, Padic.valuation_mul hy0 hy0, padicValInt.mul ha hb] at hv
  exact (Int.even_coe_nat _).mp ⟨y.valuation, by push_cast at hv ⊢; omega⟩

/-- For squarefree `h`, `v_q(h) = 1` if `q ∣ h` and `0` otherwise (PROVED). -/
theorem padicValInt_squarefree {q : ℕ} [hq : Fact q.Prime] {h : ℤ} (hsq : Squarefree h) :
    padicValInt q h = if (q : ℤ) ∣ h then 1 else 0 := by
  have hh : h ≠ 0 := hsq.ne_zero
  split_ifs with hdvd
  · have h1 : 1 ≤ padicValInt q h := by
      unfold padicValInt
      exact one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hh) (Int.natCast_dvd.mp hdvd)
    have h2 : padicValInt q h ≤ 1 := by
      unfold padicValInt
      rw [← Nat.factorization_def _ hq.out]
      exact (Int.squarefree_natAbs.mpr hsq).natFactorization_le_one q
    omega
  · exact padicValInt.eq_zero_of_not_dvd hdvd

/-- **The unused primes are good** (tex 7313–7315: "the family has identical local characters at
primes dividing `N`, so a bad prime cannot ramify in one constituent and be unramified in
another"; PROVED from the local squareclass condition of `BinaryFamily`). -/
theorem unused_disjoint_fixed {N : ℕ} (fam : BinaryFamily N) (x : Fin fam.b → ZMod 2) :
    Disjoint (unusedPrimes fam.support (fam.h x)) (2 * N).primeFactors := by
  rw [Finset.disjoint_left]
  intro q hqu hqf
  simp only [unusedPrimes, BinaryFamily.support, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Nat.mem_primeFactors] at hqu hqf
  obtain ⟨⟨x', hq, hqx', -⟩, hnx⟩ := hqu
  obtain ⟨-, hq2N, -⟩ := hqf
  have : Fact q.Prime := ⟨hq⟩
  have hx0 := fam.local_sq x ⟨q, hq⟩ hq2N
  have hx'0 := fam.local_sq x' ⟨q, hq⟩ hq2N
  have hne : ∀ y, fam.h y ≠ 0 := fun y => (fam.sqfree y).ne_zero
  have e1 := even_padicValInt_of_isSquare (hne x) (hne 0) hx0
  have e2 := even_padicValInt_of_isSquare (hne x') (hne 0) hx'0
  rw [padicValInt_squarefree (fam.sqfree x), padicValInt_squarefree (fam.sqfree 0)] at e1
  rw [padicValInt_squarefree (fam.sqfree x'), padicValInt_squarefree (fam.sqfree 0)] at e2
  have hdx' : (q : ℤ) ∣ fam.h x' := Int.natCast_dvd.mpr hqx'
  simp only [hdx', hnx, ite_true, ite_false] at e1 e2
  by_cases h0 : (q : ℤ) ∣ fam.h 0
  · simp [h0] at e1
  · simp [h0] at e2

/-- **What Appendix E provides for one admissible family** (ELLIOT; tex 6846–7787), with the
constants `c_E, C_E, C_fix, C_g, C_r, C_e` fixed before the family:
* `u` — the single scalar `u^{ev}` of (E.4), by its group-basis coefficients (tex 7519–7526);
* `charEval_mem` — every constituent `u_x` lies in `A = Λ[1/2]`: (E.4a) from (K2) at every
  height-one prime, then the intersection of the height-one valuation rings of the normal domain
  `A` (tex 7545–7592; GLUE: Krull);
* `outer` — `2^{c_E} u^{ev} ∈ 𝒪[G]`: the free rank-two model (E.3) and the integral wedge
  (tex 7596–7599; `det_integral`);
* `const` — at a corank-zero constituent with `L_*(h) ≠ 0`, the central data of (E.6)–(E.8) with
  `v₂ u_h(0)` the central valuation of `u_x`, `v₂ L_*(h)`, `s(h)`, the active primes of `h` and the
  fixed places `prime(2N)`, the unused primes being those of the family's support `F` not dividing
  `h` (tex 7613–7787);
* `zero_iff` — at a corank-zero constituent, `u_h(0) = 0 ↔ L_*(h) = 0` (corank-zero duality,
  tex 7777–7779, 1956–1957).

The PRINT inputs behind (K1)–(K3) are Kato's (Astérisque 295): Prop. 8.12 (p. 186) with (13.1.1)
(p. 225), Thm. 13.4(1)(2) (p. 226) with 13.5(2) (p. 227), Thms. 6.6 (p. 163) and 9.7 (p. 189),
(4.2.4) (p. 143) and (12.2.1)–(12.2.3) (p. 220), stated by lane RC9 (`KatoZetaLeaf`,
`KatoThm13_5_2`); the smoothing valuation `v₂ s_F = 2e` is `padicValNat_sF_smoothing`. -/
structure EvenFamilyOutput (E : WeierstrassCurve ℚ) (N : ℕ) (L : CentralNormalization E)
    (cE : ℕ) (CE Cfix Cg Cr Ce : ℤ) (fam : BinaryFamily N) where
  u : (Fin fam.b → ZMod 2) → PowerSeries ℚ_[2]
  charEval_mem : ∀ x, InLamHalf (charEval u x)
  outer : ∀ g, ∃ f : ℤ → ℤ_[2], ∀ n : ℕ,
    ((f n : ℤ_[2]) : ℚ_[2]) = PowerSeries.coeff n ((2 : ℚ_[2]) ^ cE • u g)
  const : ∀ x, CorankZero E (fam.h x) → L.Lstar (fam.h x) ≠ 0 →
    ∃ O : ConstituentOutput (activePrimes (fam.h x) N) (unusedPrimes fam.support (fam.h x))
      (2 * N).primeFactors CE Cfix Cg Cr Ce,
      O.len.v2u = (central (charEval u x)).valuation ∧
      O.v2L = padicValRat 2 (L.Lstar (fam.h x)) ∧ O.len.s = shaLen E (fam.h x)
  zero_iff : ∀ x, CorankZero E (fam.h x) → (central (charEval u x) = 0 ↔ L.Lstar (fam.h x) = 0)

/-- **Appendix E** (Propositions `ex:app-kato-system`, `ex:app-even-scalar`,
`ex:app-central-calibration`; ELLIOT): one choice of the constants for the fixed curve and local
types, and for every admissible family the outputs of `EvenFamilyOutput`. -/
def AppEOutputs (E : WeierstrassCurve ℚ) (N : ℕ) (L : CentralNormalization E) : Prop :=
  ∃ (cE : ℕ) (CE Cfix Cg Cr Ce : ℤ), 0 ≤ CE ∧ 0 ≤ Cfix ∧ 0 ≤ Cg ∧ 0 ≤ Cr ∧ 0 ≤ Ce ∧
    ∀ fam : BinaryFamily N, Nonempty (EvenFamilyOutput E N L cE CE Cfix Cg Cr Ce fam)

/-- The active and unused primes of `h` are disjoint (PROVED). -/
theorem active_unused_disjoint (N : ℕ) (F : Finset ℕ) (h : ℤ) :
    Disjoint (activePrimes h N) (unusedPrimes F h) := by
  rw [Finset.disjoint_left]
  intro q hqa hqu
  simp only [activePrimes, unusedPrimes, Finset.mem_filter, Nat.mem_primeFactors] at hqa hqu
  exact hqu.2 (Int.natCast_dvd.mpr hqa.1.2.1)

/-- For odd `h`, the active primes of `h` are disjoint from the fixed places `prime(2N)`
(PROVED). -/
theorem active_fixed_disjoint (N : ℕ) {h : ℤ} (hodd : Odd h) :
    Disjoint (activePrimes h N) (2 * N).primeFactors := by
  rw [Finset.disjoint_left]
  intro q hqa hqf
  simp only [activePrimes, Finset.mem_filter, Nat.mem_primeFactors] at hqa hqf
  obtain ⟨⟨hq, hqh, -⟩, hqN⟩ := hqa
  obtain ⟨-, hq2N, -⟩ := hqf
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : (2 : ℤ) ∣ h := Int.natCast_dvd.mpr (by simpa using hqh)
    exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hcop : Nat.Coprime q 2 := (Nat.coprime_primes hq Nat.prime_two).mpr hq2
  exact hqN (hcop.dvd_of_dvd_mul_left hq2N)

/-- **(3.2) from Appendix E** (Proposition `ex:sec7-even-scalar`, tex 1845–1966; PROVED).
Membership in `Λ[G]`: characterwise membership and Fourier inversion give `u^{ev} ∈ Λ[1/2][G]`
without estimating the Fourier denominator; intersecting coefficientwise with the integral
`𝒪[G]` result gives `2^{c_E} u^{ev} ∈ Λ[G]` (tex 1950–1954; `inLamHalf_of_charEval`,
`E5_coefficientwise`). The central identity: (E.8) at each constituent, with the active-prime
count replaced by `ω(h)` at the cost of `2ω(N)` (`ConstituentOutput.E8`, `E8_omega`). -/
theorem evenScalar32_of_appE {E : WeierstrassCurve ℚ} {N : ℕ} (hN : N ≠ 0)
    {L : CentralNormalization E} (h : AppEOutputs E N L) : EvenScalar32 E N L := by
  obtain ⟨cE, CE, Cfix, Cg, Cr, Ce, hCE, hCfix, hCg, hCr, hCe, hfam⟩ := h
  set B : ℤ := CE + ((2 * N).primeFactors.card : ℤ) * Cfix + 2 * Cg + 1 + Cr + Ce +
    2 * (N.primeFactors.card : ℤ) with hB
  refine ⟨cE, B.toNat, fun fam => ?_⟩
  obtain ⟨O⟩ := hfam fam
  refine ⟨O.u, ?_, O.zero_iff, ?_⟩
  · -- membership in `Λ[G]`: Fourier inversion, then the coefficientwise intersection (E.5)
    have hA : ∀ g, InLamHalf (O.u g) := inLamHalf_of_charEval O.u O.charEval_mem
    choose f hf using O.outer
    exact E5_coefficientwise O.u cE hA f hf
  · intro x hcz hL
    obtain ⟨CO, hv2u, hv2L, hs⟩ := O.const x hcz hL
    have h8 := CO.E8 (active_unused_disjoint N fam.support (fam.h x))
      (active_fixed_disjoint N (fam.odd x)) (unused_disjoint_fixed fam x)
    have h8' := E8_omega h8 (card_active_le_omega (fam.h x) N)
      (omega_le_card_active_add (fam.h x) hN)
    rw [hv2u, hv2L, hs] at h8'
    calc _ ≤ _ := h8'
      _ = B := by rw [hB]
      _ ≤ (B.toNat : ℤ) := Int.self_le_toNat B

/-! ## (E.9): the lower bound -/

/-- **The forward rank-zero theorem for the twists** (`lem:forward-rank`, tex 1086–1108; PRINT:
Kato, Astérisque 295, Cor. 14.3, with BCDT — lane RC9's `forward_rank_zero`):
`L(E^{(h)}, 1) ≠ 0` gives Selmer corank zero (and finite `Ш`). -/
def ForwardRankZero (E : WeierstrassCurve ℚ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → AnalyticRank (qtwist E h) 0 → CorankZero E h

/-- **(E.9)** (tex 7624–7627, 7782–7785): one constant `C` such that every odd squarefree `h`
with `L_*(h) ≠ 0` has `v₂ L_*(h) ≥ 2ω(h) + s(h) − C`. -/
def EvenLowerBound (E : WeierstrassCurve ℚ) (L : CentralNormalization E) : Prop :=
  ∃ C : ℤ, ∀ h : ℤ, Odd h → Squarefree h → L.Lstar h ≠ 0 →
    2 * (omega h : ℤ) + shaLen E h - C ≤ padicValRat 2 (L.Lstar h)

/-- **(E.9) from (3.2) at `G = 1`** (tex 7780–7786: "Equations (E.5) and (E.8), already with
`G = 1`, yield (E.9). No binary-family dimension is needed for this lower bound"; PROVED). The
forward rank-zero theorem supplies the corank-zero hypothesis, and every continuation of
`L(E^{(h)}, s)` exists by modularity (`hcont`). -/
theorem evenLowerBound_of_evenScalar32 {E : WeierstrassCurve ℚ} {N : ℕ}
    {L : CentralNormalization E} (h32 : EvenScalar32 E N L) (hfwd : ForwardRankZero E)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist E h) F) : EvenLowerBound E L := by
  obtain ⟨Cev, C, h32⟩ := h32
  refine ⟨(Cev : ℤ) + C, fun h hodd hsq hL => ?_⟩
  have hh : h ≠ 0 := fun h0 => by simp [h0] at hodd
  obtain ⟨F, hF⟩ := hcont h hh
  have hcz : CorankZero E h := hfwd h hh ((L.lstar_ne_zero_iff hh hF).mp hL)
  obtain ⟨u, hint, hzero, hbd⟩ := h32 (BinaryFamily.single N h hodd hsq)
  have : IsEmpty (Fin (BinaryFamily.single N h hodd hsq).b) := by
    change IsEmpty (Fin 0); infer_instance
  have : Unique (Fin (BinaryFamily.single N h hodd hsq).b → ZMod 2) := Pi.uniqueOfIsEmpty _
  set x : Fin (BinaryFamily.single N h hodd hsq).b → ZMod 2 := default with hxdef
  have hx : charEval u x = u x := by
    simp only [charEval]
    rw [Fintype.sum_unique]
    simp only [chi, dotProduct, Finset.univ_eq_empty, Finset.sum_empty, ite_true, Int.cast_one,
      one_smul]
    exact congrArg u (Subsingleton.elim _ _)
  have hcz' : CorankZero E ((BinaryFamily.single N h hodd hsq).h x) := hcz
  have hL' : L.Lstar ((BinaryFamily.single N h hodd hsq).h x) ≠ 0 := hL
  have hne : central (charEval u x) ≠ 0 := fun h0 => hL' ((hzero x hcz').mp h0)
  have hb := hbd x hcz' hL'
  have hv : -(Cev : ℤ) ≤ (central (charEval u x)).valuation := by
    rw [hx] at hne ⊢
    exact valuation_central_ge (hint x) hne
  change |(central (charEval u x)).valuation - (padicValRat 2 (L.Lstar h) - 2 * (omega h : ℤ) -
    (shaLen E h : ℤ))| ≤ C at hb
  have := (abs_le.mp hb).2
  linarith

end ZInQ.Manuscript.RC.Even

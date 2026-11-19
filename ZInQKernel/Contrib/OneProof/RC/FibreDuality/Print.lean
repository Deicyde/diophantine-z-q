import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Bridge
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncPrints

/-!
# Lane RC31, part 1: Nekovář's localized duality for the characteristic-zero fibres, as PRINTs

Manuscript `diophantine_zq.tex`: the height-one regularity step (tex 4976–5200; "Fix a height-one
prime `𝔭 ≠ (2)`, put `R = Λ_𝔭` and `k = Frac(Λ/𝔭)` … Here `R` is a DVR and `k` has characteristic
zero", tex 4977–4980), the derivative switch (tex 4878–4897: "Exact annihilator and dimension
assertions in the switch argument are made after passage to the stated fraction or test field,
using these integral diagrams and their retained dualities"; "The transported duality and
localization identities identify the relaxed localization image with the kernel of its dual
localization map, hence with its exact annihilator [Nekovář 6.3.3–6.3.4]"), "Exact duality makes
the relaxed localization image equal to the finite plane" (tex 5000–5001), and "The retained
localization-duality diagrams give `U = U^⊥` … this is the exactness in [Nekovář 6.3.3–6.3.4]"
(tex 5065–5070). The global field of the text is imaginary quadratic: "Let `K` be imaginary
quadratic" (tex 2839), "There are no real places of `K`" (tex 4584).

**Source.** J. Nekovář, *Selmer complexes*, Astérisque 310 (2006). Every locator below was read by
lane RC31 from page images of the printed edition (Numdam scan); quotations are verbatim. In the
case `R = Λ/𝔭` of 5.6.1 described below, admissibility is conditional on the lattice topologies of
`V_𝔭` and of its dual, which are PROVED in `Comparison.lean`.

* 2.1 (p. 51): "Throughout Chapters 2–11 (with the exception of Sect. 2.10), `R` will be a complete
  Noetherian local ring with maximal ideal `𝔪` and residue field `k = R/𝔪`." Chapter 5 (p. 113):
  "Throughout Chapter 5 we assume that `k = 𝔽_{p^r}` is a finite field of characteristic `p`."
* 2.5 (p. 54): "(i) There exists a dualizing complex `ω ∈ D^b_ft(_R Mod)` (unique up to
  isomorphism) …; (ii) `ω` can be represented by a bounded complex of injective `R`-modules `ω•`,
  supported in degrees `[0, d]`." 2.7(ii) (p. 55): "`R` is Cohen-Macaulay (i.e., `depth(R) = d`)
  iff `ω ≅ H⁰(ω)` is concentrated in degree zero"; 2.7(iii): "`R` is Gorenstein … iff `ω ≅ R`".
* 3.2.1 (p. 76): admissible `R[G]`-modules ("the image of `ρ_M` is an `R`-module of finite type;
  and … `G → Im(ρ_M)` is continuous (if `Im(ρ_M)` is equipped with `𝔪`-adic topology)"); 3.3.1,
  3.3.4, 3.3.5(v) (p. 79): ind-admissible modules (`M = ⋃ M_α`, `M_α` of finite type with
  `𝔪`-adically continuous action), admissible iff `Im(ρ_M)` is of finite type; 3.4.1.1 (p. 82):
  their continuous cochains `C^i_cont(G, M) = lim→ C^i_cont(G, M_α)`.
* 3.7.1 (p. 93): "Let `R_𝒮 = 𝒮⁻¹R` be the localization of `R` at a multiplicative subset
  `𝒮 ⊂ R`. Put `ω_{R_𝒮} = 𝒮⁻¹ω_R = ω_R ⊗_R R_𝒮` …; then the canonical map
  `ε : M → 𝒟_{R_𝒮}(𝒟_{R_𝒮}(M))` is an isomorphism in `D_ft(_{R_𝒮}Mod)`". 3.7.2 (p. 94): "An
  `R_𝒮[G]`-module `M` is admissible (resp., ind-admissible) if it is admissible
  (resp., ind-admissible) as an `R[G]`-module." 3.7.3 (p. 94): such an `M` of finite type over `R_𝒮`
  is `𝒮⁻¹N` with `N` admissible of finite type over `R`.
* 5.1 (p. 113): "Let `K` be a global field of characteristic `char(K) ≠ p` and `S` a finite set of
  primes of `K` containing all primes above `p` and all archimedean primes of `K` … In Sections
  5.1–5.6, we assume that the following condition is satisfied (the general case is treated in
  5.7): (P) If `p = 2`, then `K` has no real prime."
* **5.6.1 (p. 130)**: "Let `𝒮 ⊂ R` be a multiplicative subset. Everything in Sections 5.2.1–5.2.2,
  5.2.7–5.2.9, 5.4.1–5.4.2 and 5.4.4 remains valid if we replace `R` by `R_𝒮`." 5.6.2: "`J =
  ω•_{R_𝒮}[n]` for some `n ∈ ℤ` (hence `D_J = 𝒟_{R_𝒮,n}`) and all cohomology groups of `X` are of
  finite type over `R_𝒮`."
* **5.6.3 Proposition (p. 130)**: "Assume that `J = ω•_{R_𝒮}[n]` for some `n ∈ ℤ`. Then: (i) For
  every `X ∈ D^b_{R_𝒮-ft}(ad R_𝒮[G_v]Mod)`, the canonical map `α_{J,X} : RΓ_cont(G_v, X) →
  𝒟_{R_𝒮,n−2}(RΓ_cont(G_v, 𝒟_{R_𝒮,n}(X)(1)))` is an isomorphism in `D^b_ft(_{R_𝒮}Mod)` (and the
  same is true for `α'_{J,X}`). (ii) For every `X ∈ D^b_{R_𝒮-ft}(ad R_𝒮[G_{K,S}]Mod)`, the canonical
  map `_cβ_{J,X} : RΓ_{c,cont}(G_{K,S}, X) → 𝒟_{R_𝒮,n−2}(RΓ_cont(G_{K,S}, 𝒟_{R_𝒮,n}(X)(1)))` is
  an isomorphism in `D^b_ft(_{R_𝒮}Mod)` (and the same is true for `_cβ'_{J,X}`, `β_{c,J,X}` and
  `β'_{c,J,X}`)." Proof: dévissage to `X = 𝒮⁻¹Y`, `Y` admissible of finite type over `R` (3.7.3),
  and localization of Proposition 5.2.4 (p. 116), resp. 5.4.3 (p. 127). (In (ii) the index reads
  `n − 2` in the page image; the global maps of 5.4.2–5.4.3 take values in `D_{J[−3]} =
  𝒟_{R_𝒮,n−3}`, and the proof of (ii) is the localization of 5.4.3 ("with 5.4.3 replacing 5.2.4"),
  so the global shift is `−3`, the local one `−2`; we use these, as in lane RC26's
  `InducesIsoH3` (global) and `InducesIsoH2` (local).)
* 6.8.1 (p. 154): "Everything in Sections 6.1–6.7 is still valid for `R_𝒮` instead of `R`; the only
  difference is that references to 5.2.3 should be replaced by those to 5.6.2. For example, the
  same proof as in 5.6.3 gives a localized version of the duality Theorem 6.3.4."

**The instance (lane RC31's route).** Take `R = Λ/𝔭`: a quotient of `Λ = ℤ₂⟦t⟧`, hence complete
Noetherian local with residue field `𝔽₂` (2.1, Chapter 5); for `𝔭 ≠ (2)` of height one it is a
domain finite over `ℤ₂` (lane RC28, `finite_quotient`). Take `𝒮 = R ∖ {0}`; then
`R_𝒮 = Frac(Λ/𝔭) = k(𝔭)` (`ResAt 𝔭`, the residue field of `Λ_𝔭`). Neither 5.6.1 nor 3.7.1–3.7.2
restricts `R` or `𝒮` further.
*Dualizing complex.* `R = Λ/𝔭` is a one-dimensional local domain, hence Cohen–Macaulay, so by
2.7(ii) its dualizing complex `ω_R` is a module in degree `0`; in fact `𝔭 = (f)` is principal
(`Λ` is a regular local UFD), so `R = Λ/(f)` is a hypersurface, hence Gorenstein, and `ω_R ≅ R`
(2.7(iii)). Only the degree matters here: 2.5 provides `ω` for every complete Noetherian local
`R`, and 5.2.4 and 5.4.3 are stated for `J = ω•[n]`. By 3.7.1,
`ω_{R_𝒮} = ω_R ⊗_R k(𝔭)` is a dualizing complex of the field `k(𝔭)` (`ε` is an isomorphism),
concentrated in degree `0`, hence one-dimensional: `ω_{R_𝒮} ≅ k(𝔭)`. We take `n = 0`, so
`J = ω_{R_𝒮} ≅ k(𝔭)[0]`, `𝒟_{R_𝒮,0} = Hom_{k(𝔭)}(−, k(𝔭))`, and the canonical local and global
traces are `k(𝔭)`-valued; the choice of `ω_{R_𝒮} ≅ k(𝔭)` is a unit of `k(𝔭)` (DEPARTURE 1).
*Coefficients.* A finite-dimensional `k(𝔭)`-vector space `X` with a `G`-stable finitely generated
`Λ`-lattice `Y`, `X = ⋃ 2^{−n} Y`, whose topology has the neighbourhood basis `2^n Y` and on which
`G` acts continuously, is an admissible `R_𝒮[G]`-module of finite type: its `2^{−n} Y` lie in
`S(X)` (3.3.1), and the image of `R[G]` lies in the finitely generated `End_R(Y)` (3.3.5(v)); the
`𝔪`-adic and `2`-adic topologies of a finitely generated `R`-module agree since `R` is finite over
`ℤ₂`. Lane RC26's continuous cochains of `X` are Nekovář's (3.4.1.1): a continuous cochain on the
compact `G^n` lands in some `2^{−N} Y`, and there the topology is the `2`-adic one
(`Comparison.lean`). No `ℚ₂`-linear statement and no coefficient trace `k(𝔭)(1) → ℚ₂(1)` is
involved. (The alternative fit `R₀ = ℤ₂`, `𝒮 = 2^ℕ`, `R₀[1/2] = ℚ₂` gives the `ℚ₂`-linear duality;
transporting it to `k(𝔭)` needs the coefficient trace first and the canonical `ℚ₂`-trace after,
which is not used here.)

**Real places (a separate step).** The finite-place cones of lane RC26 omit the real places.
That this needs no condition on `K` is a MATHEMATICAL CONSEQUENCE of the book (of 5.6.1–5.6.3
together with 5.7.5–5.7.6 and 6.9.1, after inverting `2`), not a literal statement in it: the
coefficients are `k(𝔭)`-modules, in which `2` is a unit, and 5.7.6 (p. 133): "As
`2 · Ĥ^i(G_v, M) = 0` for each real prime `v` and each `G_v`-module `M`, the canonical map in
`D(_R Mod)` `RΓ_{c,cont}(G_{K,S}, M•) → R̂Γ_{c,cont}(G_{K,S}, M•)` … becomes an isomorphism in
`D^b(_{R[1/2]}Mod)`" (with 5.7.5: the duality of 5.4 holds with `R̂Γ_c`); 6.9.1
(p. 154): with `U_v^+ = 0` at the real primes, "the complex `⊕_{K_v = ℝ} Err_v(Δ_v(X), Δ_v(Y), π)`
becomes acyclic in `D(_{R[1/2]}Mod)`". In the text `K` is imaginary quadratic (tex 2839, 4584), so
`(P)` holds and this step is not needed there.

**Kinds.**
* `NekovarFibreSetting`, `IsLatticeTop`, `IsTateTwistFibre`: hypotheses (definitions), each with a
  non-vacuity instance (`NonVacuity.lean`).
* `NekovarFibreGlobalDuality`: PRINT (Nekovář 5.6.3(ii), with 5.4.3; for real places a
  consequence of 5.7.5–5.7.6, see above, not a literal line).
* `NekovarFibreLocalDuality`: PRINT (Nekovář 5.6.3(i), with 5.2.4).
* `NekovarFibreTraces`: PRINT (Nekovář 5.1.3, 5.1.5, 5.2.1, 5.4.1 with 5.6.1: the canonical local
  and global traces, compatible).

**DEPARTUREs (form).**
1. Traces are quantified over all cochain traces killing coboundaries and inducing `H³ ≅ k(𝔭)`
   (locally `H² ≅ k(𝔭)`), not Nekovář's specific `r_S` (`r_v`). Over a field every complex is
   homotopy equivalent to its cohomology, so traces up to homotopy are `Hom(H³, k(𝔭))`, and any
   such trace is `u · r_S` up to homotopy with `u ∈ k(𝔭)ˣ`; homotopic or rescaled traces do not
   change quasi-isomorphy (Nekovář 6.3.1: the homotopy class of `γ` is independent of `r`). The
   canonical traces themselves are supplied by `NekovarFibreTraces`.
2. The cones are lane RC26's (finite places, product over `S`, cone signs of `nekIso`, local
   target `τ≥2` as in Nekovář 6.3.1).
3. `T ≅ k(𝔭)(1)` is encoded by `IsTateTwistFibre` (a `ℤ₂`-valued cyclotomic character with
   `K_S ⊇ μ_{2^∞}`) together with the lattice topology of `T`; `J(1) = J ⊗_{ℤ₂} ℤ₂(1)` in
   Nekovář 5.2.1.
4. Nekovář's topology on an admissible `R_𝒮[G]`-module is encoded by `IsLatticeTop` (above).
5. ROUTE. The text applies the integral duality over `R = Λ_𝔭` to its actual primitive scalar
   Selmer complex and passes to `k = Frac(Λ/𝔭)` by `C ⊗_R k` (tex 4977–4990; integral uses at
   tex 5166–5179). These PRINTs give the duality for the Galois cochains of the fibre `V_𝔭` over
   `k(𝔭)` (5.6.3 at `R = Λ/𝔭`). Neither the identification `C ⊗^L_R k ≃ C_{U ⊗ k}(V_𝔭)` for the
   text's local conditions nor the `Λ_𝔭`-linear duality is supplied here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain CategoryTheory Filter Topology
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.LambdaCoef (IsHeightOneOdd resN)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (truncSub)
open scoped Pointwise

variable (K : Type) [Field K] [NumberField K]

/-! ### The standing hypotheses -/

/-- **Nekovář's standing hypotheses for the fibres** (5.1, p. 113): `S` is a finite set of primes
containing the primes above `p = 2` (the archimedean primes are implicit). Condition `(P)` is not
required: the coefficients are `k(𝔭)`-vector spaces, in which `2` is a unit, and over `R[1/2]` the
real places do not change the compactly supported cochains (5.7.6, p. 133) nor the Selmer
complexes (6.9.1, p. 154). Kind: hypothesis (PRINT setting). -/
structure NekovarFibreSetting (S : Set (HeightOneSpectrum (𝓞 K))) : Prop where
  finite_S : S.Finite
  above_two : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S

/-- **Nekovář's topology on an admissible `k(𝔭)[G]`-module** (3.3.1, 3.3.4, 3.7.2, 3.7.3): a
finitely generated `G`-stable `Λ`-submodule `Y` (a lattice; `Λ` acts through `k(𝔭)`) with
`X = ⋃ 2^{−n} Y`, whose `2`-adic neighbourhoods `2^n Y` form a basis of neighbourhoods of `0`.
For `R = Λ/𝔭` (finite over `ℤ₂`) the `2`-adic and the `𝔪`-adic topologies of `Y` agree. Kind:
hypothesis (definition). -/
structure IsLatticeTop (G X : Type) [Group G] [AddCommGroup X] [Module Lambda X]
    [DistribMulAction G X] [TopologicalSpace X] : Prop where
  exists_lattice : ∃ Y : Submodule Lambda X, Y.FG ∧ (∀ (g : G) (y : X), y ∈ Y → g • y ∈ Y) ∧
    (∀ x : X, ∃ n : ℕ, ((2 : Lambda) ^ n) • x ∈ Y) ∧
    (𝓝 (0 : X)).HasBasis (fun _ : ℕ => True)
      (fun n => ((((2 : Lambda) ^ n) • Y : Submodule Lambda X) : Set X))

/-- **`T ≅ k(𝔭)(1)`** as `k(𝔭)[G_{K,S}]`-modules (Nekovář 5.2.1: `A(1) = A ⊗_{ℤ_p} ℤ_p(1)`):
`K_S` contains all `2`-power roots of unity, and there are an isomorphism `e : T ≃ k(𝔭)` and a
`ℤ₂`-valued character `c` with `g ζ = ζ ^ (c(g) mod 2^n)` for every `2^n`-th root of unity
`ζ ∈ K_S` (the `2`-adic cyclotomic character) and `e (g • t) = c(g) · e t`. The topology of `T` is
required separately (`IsLatticeTop`). Kind: hypothesis (definition). -/
def IsTateTwistFibre (S : Set (HeightOneSpectrum (𝓞 K))) (P : Ideal Lambda) [P.IsPrime]
    (T : Type) [AddCommGroup T] [Module (ResAt P) T] [DistribMulAction (GKS K S) T] : Prop :=
  ∃ (e : T ≃ₗ[ResAt P] ResAt P) (c : GKS K S → ℤ_[2]),
    (∀ n : ℕ, Nat.card {ζ : unramifiedOutside K S // ζ ^ (2 ^ n) = 1} = 2 ^ n) ∧
    (∀ (g : GKS K S) (n : ℕ) (ζ : unramifiedOutside K S), ζ ^ (2 ^ n) = 1 →
      toGal K g ζ = ζ ^ resN n (c g)) ∧
    ∀ (g : GKS K S) (t : T), e (g • t) = algebraMap ℤ_[2] (ResAt P) (c g) * e t

/-! ### The genuine data with non-discrete coefficients -/

section Data

variable {K} (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type) [CommRing k]
  {X X' T : Type}
  [AddCommGroup X] [Module k X] [DistribMulAction (GKS K S) X] [SMulCommClass (GKS K S) k X]
  [TopologicalSpace X] [ContinuousAdd X] [ContinuousConstSMul k X] [ContinuousSMul (GKS K S) X]
  [AddCommGroup X'] [Module k X'] [DistribMulAction (GKS K S) X'] [SMulCommClass (GKS K S) k X']
  [TopologicalSpace X'] [ContinuousAdd X'] [ContinuousConstSMul k X']
  [ContinuousSMul (GKS K S) X']
  [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul (GKS K S) T]
  (β : X →ₗ[k] X' →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a : X) (b : X'), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : X × X' => β x.1 x.2)

/-- Truncated isotropy data (Nekovář 6.2.1.3, 6.3.1: local products into `τ_{≥2}`) for the genuine
Galois Selmer data with arbitrary topological coefficients (lane RC26's `TruncIsotropyData` at
`G_{K,S}`, `G_{K_v}`, `p_v`). -/
abbrev GalTruncIsotropyData (ΔA : GaloisLocalConditions K S k X)
    (ΔB : GaloisLocalConditions K S k X') : Type :=
  TruncIsotropyData k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
    hβc ΔA ΔB

/-- **The genuine Selmer pairing data over `τ≥2`** (Nekovář 6.3.1) for the Galois Selmer data
with arbitrary topological coefficients: lane RC26's generic `genuinePairDataT` at `G_{K,S}`,
`G_{K_v}`, `p_v`. Its Selmer data are definitionally `galoisSelData K S k X ΔA` and
`galoisSelData K S k X' ΔB` (for `X = V_𝔭`: lane RC28's `fibreSelData`). -/
abbrev galPairDataT (ΔA : GaloisLocalConditions K S k X) (ΔB : GaloisLocalConditions K S k X')
    (I : GalTruncIsotropyData S k β hβ hβc ΔA ΔB) :
    SelPairData (galoisSelData K S k X ΔA) (galoisSelData K S k X' ΔB) :=
  genuinePairDataT k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
    hβc ΔA ΔB I

/-- The truncated compact cone `Cone(C(G_{K,S}, T) → ⊕_v τ_{≥2} C(G_v, T))[−1]` (Nekovář 5.4.1),
the domain of the global trace. -/
abbrev galCompactTT (ΔA : GaloisLocalConditions K S k X) (ΔB : GaloisLocalConditions K S k X')
    (I : GalTruncIsotropyData S k β hβ hβc ΔA ΔB) : GCx k :=
  coneCx (galPairDataT S k β hβ hβc ΔA ΔB I).resE

theorem galPairDataT_eq (ΔA : GaloisLocalConditions K S k X) (ΔB : GaloisLocalConditions K S k X')
    (I : GalTruncIsotropyData S k β hβ hβc ΔA ΔB) :
    galPairDataT S k β hβ hβc ΔA ΔB I =
      genuinePairDataT k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
        hβ hβc ΔA ΔB I :=
  rfl

end Data

/-! ### The PRINTs -/

/-- **PRINT — Nekovář, *Selmer complexes* (Astérisque 310, 2006), Proposition 5.6.3(ii), p. 130**
(localized global duality; the localization of Proposition 5.4.3, p. 127, along
`R = Λ/𝔭 → R_𝒮 = k(𝔭)`, `𝒮 = R ∖ {0}`, `J = ω•_{R_𝒮}[n] = k(𝔭)`; without `(P)` with 5.7.5–5.7.6,
p. 133), for the genuine continuous cochains of lane RC26: for a height-one prime `𝔭 ≠ (2)` of `Λ`,
`S` finite containing the primes above `2`, finite-dimensional `k(𝔭)`-vector spaces `X`, `X'` with
continuous `G_{K,S}`-actions and Nekovář's topology (`IsLatticeTop`), `T ≅ k(𝔭)(1)` with its
lattice topology, a perfect jointly continuous equivariant `k(𝔭)`-bilinear `β : X × X' → T`, any
local conditions with truncated isotropy data, and any global trace on
`Cone(C(G_{K,S}, T) → ⊕_v τ_{≥2} C(G_v, T))[−1]` killing coboundaries and inducing
`H³_c(G_{K,S}, T) ≅ k(𝔭)`, the global duality map
`C(G_{K,S}, X) → Hom_{k(𝔭)}(C_c(G_{K,S}, X'), k(𝔭))[−3]`,
`a ↦ ((b, y) ↦ tr(a ∪ b, (−1)^i res a ∪ y))` (Nekovář's `β_{c,J,X}` of 5.4.2, p. 127, built from
`∪_c` ("using `U_c` instead of `cU`"), with values in `D_{J[−3]}(RΓ_{c,cont}(G_{K,S}, D_J(X)(1)))`;
5.6.3(ii) asserts that `_cβ_{J,X}`, `_cβ'_{J,X}`, `β_{c,J,X}` and `β'_{c,J,X}` are isomorphisms) is
a quasi-isomorphism. It does not depend on `ΔA`, `ΔB`, `I`: they enter only through the cup product
of `(a, 0, 0)` with `(b, 0, y)`, where the local-condition terms vanish.

Hypotheses side by side with the print: `NekovarFibreSetting` = 5.1 (`S` finite, `S ⊇ S_2`;
`(P)` replaced by `2 ∈ k(𝔭)ˣ` through 5.7.6); `[P.IsPrime] [IsHeightOneOdd P]` = `R = Λ/𝔭` a
complete Noetherian local domain with residue field `𝔽₂` (2.1, Chapter 5) and `R_𝒮 = Frac R`
(5.6.1); `IsLatticeTop X`, `IsLatticeTop X'` with the continuous actions = `X ∈ D^b_{R_𝒮-ft}` of
admissible `R_𝒮[G]`-modules (3.2.1, 3.7.2–3.7.3, 5.6.2), and Nekovář's cochains (3.4.1.1);
`IsTateTwistFibre`, `IsLatticeTop T` = `J(1)` (5.2.1); bijectivity of `β`, `β.flip` = `X' ≅
𝒟_{R_𝒮,n}(X)(1)` (the dual entering 5.6.3); the trace hypotheses = `r_S` of 5.4.1 up to homotopy and
a unit (DEPARTURE 1 of the file header). -/
def NekovarFibreGlobalDuality : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P],
    NekovarFibreSetting K S →
    ∀ (X X' T : Type)
      [AddCommGroup X] [Module (ResAt P) X] [Module Lambda X] [IsScalarTower Lambda (ResAt P) X]
      [DistribMulAction (GKS K S) X] [SMulCommClass (GKS K S) (ResAt P) X] [TopologicalSpace X]
      [IsTopologicalAddGroup X] [ContinuousConstSMul (ResAt P) X] [ContinuousSMul (GKS K S) X]
      [AddCommGroup X'] [Module (ResAt P) X'] [Module Lambda X']
      [IsScalarTower Lambda (ResAt P) X'] [DistribMulAction (GKS K S) X']
      [SMulCommClass (GKS K S) (ResAt P) X'] [TopologicalSpace X'] [IsTopologicalAddGroup X']
      [ContinuousConstSMul (ResAt P) X'] [ContinuousSMul (GKS K S) X']
      [AddCommGroup T] [Module (ResAt P) T] [Module Lambda T] [IsScalarTower Lambda (ResAt P) T]
      [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) (ResAt P) T] [TopologicalSpace T]
      [IsTopologicalAddGroup T] [ContinuousConstSMul (ResAt P) T] [ContinuousSMul (GKS K S) T],
      IsLatticeTop (GKS K S) X → IsLatticeTop (GKS K S) X' → IsLatticeTop (GKS K S) T →
      IsTateTwistFibre K S P T →
      ∀ (β : X →ₗ[ResAt P] X' →ₗ[ResAt P] T)
        (hβ : ∀ (g : GKS K S) (a : X) (b : X'), β (g • a) (g • b) = g • β a b)
        (hβc : Continuous fun x : X × X' => β x.1 x.2),
        Function.Bijective β → Function.Bijective β.flip →
        ∀ (ΔA : GaloisLocalConditions K S (ResAt P) X) (ΔB : GaloisLocalConditions K S (ResAt P) X')
          (I : GalTruncIsotropyData S (ResAt P) β hβ hβc ΔA ΔB)
          (tr : (galCompactTT S (ResAt P) β hβ hβc ΔA ΔB I).X 3 →ₗ[ResAt P] ResAt P)
          (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc ΔA ΔB I).d 2 3 rfl z) = 0),
          InducesIsoH3 tr →
          QuasiIso (GHom.toCC (globalDualityMap (galPairDataT S (ResAt P) β hβ hβc ΔA ΔB I) tr htr))

/-- **PRINT — Nekovář, *Selmer complexes*, Proposition 5.6.3(i), p. 130** (localized local
duality; the localization of Proposition 5.2.4, p. 116, along `R = Λ/𝔭 → k(𝔭)`), for the genuine
local continuous cochains: under the hypotheses of `NekovarFibreGlobalDuality`, at every place
`v ∈ S` and for every local trace `tr_v : C²_cont(G_{K_v}, T) → k(𝔭)` killing coboundaries and
inducing `H²(G_{K_v}, T) ≅ k(𝔭)`, the map
`C^•_cont(G_{K_v}, X) → Hom_{k(𝔭)}(C^•_cont(G_{K_v}, X'), k(𝔭))[−2]`, `a ↦ (b ↦ tr_v(a ∪ b))`
(Nekovář's `α_{J,X}` of 5.2.2) is a quasi-isomorphism. -/
def NekovarFibreLocalDuality : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P],
    NekovarFibreSetting K S →
    ∀ (X X' T : Type)
      [AddCommGroup X] [Module (ResAt P) X] [Module Lambda X] [IsScalarTower Lambda (ResAt P) X]
      [DistribMulAction (GKS K S) X] [SMulCommClass (GKS K S) (ResAt P) X] [TopologicalSpace X]
      [IsTopologicalAddGroup X] [ContinuousConstSMul (ResAt P) X] [ContinuousSMul (GKS K S) X]
      [AddCommGroup X'] [Module (ResAt P) X'] [Module Lambda X']
      [IsScalarTower Lambda (ResAt P) X'] [DistribMulAction (GKS K S) X']
      [SMulCommClass (GKS K S) (ResAt P) X'] [TopologicalSpace X'] [IsTopologicalAddGroup X']
      [ContinuousConstSMul (ResAt P) X'] [ContinuousSMul (GKS K S) X']
      [AddCommGroup T] [Module (ResAt P) T] [Module Lambda T] [IsScalarTower Lambda (ResAt P) T]
      [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) (ResAt P) T] [TopologicalSpace T]
      [IsTopologicalAddGroup T] [ContinuousConstSMul (ResAt P) T] [ContinuousSMul (GKS K S) T],
      IsLatticeTop (GKS K S) X → IsLatticeTop (GKS K S) X' → IsLatticeTop (GKS K S) T →
      IsTateTwistFibre K S P T →
      ∀ (β : X →ₗ[ResAt P] X' →ₗ[ResAt P] T)
        (hβ : ∀ (g : GKS K S) (a : X) (b : X'), β (g • a) (g • b) = g • β a b)
        (hβc : Continuous fun x : X × X' => β x.1 x.2),
        Function.Bijective β → Function.Bijective β.flip →
        ∀ (v : Places K S)
          (trv : (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T v).X 2 →ₗ[ResAt P] ResAt P)
          (htrv : ∀ z, trv ((localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0),
          InducesIsoH2 trv →
          QuasiIso (GHom.toCC (adjHom (localPair (ResAt P) (GKS K S)
            (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc v) 2 trv htrv))

/-! ### The trace packet (one trivialization) -/

section Traces

variable {K} (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type) [CommRing k] (T : Type)
  [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul (GKS K S) T]

/-- **Local traces at every place of `S`** (Nekovář 5.2.1, p. 114–115: `r_v`, induced by the
inverse of `inv_v` on `H²_cont(G_v, J(1)) ≅ J`): cochain traces on `C²_cont(G_{K_v}, T)` killing
coboundaries and inducing `H²(G_{K_v}, T) ≅ k`. In the trace packet they are chosen ONCE, for all
coefficients and local conditions. Kind: definition. -/
structure FibreLocalTraces where
  /-- The trace at `v`. -/
  trv : ∀ v : Places K S, (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T v).X 2 →ₗ[k] k
  /-- It kills coboundaries. -/
  htrv : ∀ v z, trv v ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0
  /-- It induces `H²(G_{K_v}, T) ≅ k`. -/
  iso : ∀ v, InducesIsoH2 (trv v)

variable {S k T}

/-- **A global trace normalized by the local traces** (lane RC26's `hsum`; Nekovář 5.4.1:
`r_S ∘ j ∼ ∑_v r_v`): on the local part of the truncated compact cone, `tr(0, z) = ∑_v tr_v(z_v)`.
With one fixed `L`, this forces every global trace to use the same trivialization as all the local
ones (independently rescaled local traces have no such global trace in general). Kind:
definition. -/
def FibreLocalTraces.Normalizes [Fintype (Places K S)] (L : FibreLocalTraces S k T)
    {X X' : Type}
    [AddCommGroup X] [Module k X] [DistribMulAction (GKS K S) X] [SMulCommClass (GKS K S) k X]
    [TopologicalSpace X] [ContinuousAdd X] [ContinuousConstSMul k X] [ContinuousSMul (GKS K S) X]
    [AddCommGroup X'] [Module k X'] [DistribMulAction (GKS K S) X']
    [SMulCommClass (GKS K S) k X'] [TopologicalSpace X'] [ContinuousAdd X']
    [ContinuousConstSMul k X'] [ContinuousSMul (GKS K S) X']
    {β : X →ₗ[k] X' →ₗ[k] T} {hβ : ∀ (g : GKS K S) (a : X) (b : X'), β (g • a) (g • b) = g • β a b}
    {hβc : Continuous fun x : X × X' => β x.1 x.2}
    {ΔA : GaloisLocalConditions K S k X} {ΔB : GaloisLocalConditions K S k X'}
    {I : GalTruncIsotropyData S k β hβ hβc ΔA ΔB}
    (tr : (galCompactTT S k β hβ hβc ΔA ΔB I).X 3 →ₗ[k] k) : Prop :=
  ∀ z : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T).X (3 - 1),
    tr ((0 : (globalCx k (GKS K S) T).X 3), (truncSub (localSumCx k
      (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T)
      (3 - 1)).mkQ z) = ∑ v, L.trv v (z v)

end Traces

/-- **PRINT — the canonical traces for ONE trivialization** (Nekovář 5.1.3, p. 114: `inv_v`; 5.2.1,
pp. 114–115: `H²_cont(G_v, A(1)) ≅ A` and the trace `r_v`; 5.1.5, p. 114: the reciprocity law
`∑_v inv_v ∘ res_v = 0`; 5.4.1, pp. 125–126: `H³_c(G_{K,S}, A(1)) ≅ A` and `r_S` with
`r_S ∘ j ∼ ∑_v r_v`; all valid over `R_𝒮` by 5.6.1, and without `(P)` by 5.7.3 and 5.7.6): for
`T ≅ k(𝔭)(1)` there are local traces `tr_v` (`FibreLocalTraces`: the canonical `r_v` for one fixed
identification `T ≅ k(𝔭)(1)` and one `ω_{R_𝒮} ≅ k(𝔭)`), chosen once for all coefficients and
local conditions, such that for any genuine data there is a global trace on the truncated compact
cone, killing coboundaries and inducing `H³_c(G_{K,S}, T) ≅ k(𝔭)`, normalized by them
(`Normalizes`: lane RC26's `hsum`) — the canonical `r_S` for the same trivialization.
DEPARTURE: Nekovář's `r_S ∘ j ∼ ∑ r_v` holds up to homotopy; over the field `k(𝔭)` the homotopy is
absorbed into the choice of `r_S` (extend `−∑_v tr_v ∘ res_v`, which vanishes on `2`-cocycles by
reciprocity, from the coboundaries).
Intended discharge route (not carried out here): the local invariants and the reciprocity law are
proved in the vendored class field theory library — `TauCeti.ClassFieldTheory.invMap :
Br K ≃+ AddCircle (1 : ℚ)` (module
`ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant`) and
`TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_eq_zero : sumLocalInv K (brLocalization K x)
= 0` (module
`ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula`);
what is missing is the Kummer map `H²(G, μ_{2^n}) → Br[2^n]` (not in the library) and its
comparison with lane RC26's continuous cochains. With these, `r_v = e ∘ inv_v ∘ (Kummer)` for the
fixed `e : T ≅ k(𝔭)(1)`, and the normalization `Normalizes` is the sum formula. -/
def NekovarFibreTraces : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P],
    NekovarFibreSetting K S → ∀ [Fintype (Places K S)] (T : Type)
      [AddCommGroup T] [Module (ResAt P) T] [Module Lambda T] [IsScalarTower Lambda (ResAt P) T]
      [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) (ResAt P) T] [TopologicalSpace T]
      [IsTopologicalAddGroup T] [ContinuousConstSMul (ResAt P) T] [ContinuousSMul (GKS K S) T],
      IsLatticeTop (GKS K S) T → IsTateTwistFibre K S P T →
      ∃ L : FibreLocalTraces S (ResAt P) T,
        ∀ (X X' : Type)
          [AddCommGroup X] [Module (ResAt P) X] [DistribMulAction (GKS K S) X]
          [SMulCommClass (GKS K S) (ResAt P) X] [TopologicalSpace X] [ContinuousAdd X]
          [ContinuousConstSMul (ResAt P) X] [ContinuousSMul (GKS K S) X]
          [AddCommGroup X'] [Module (ResAt P) X'] [DistribMulAction (GKS K S) X']
          [SMulCommClass (GKS K S) (ResAt P) X'] [TopologicalSpace X'] [ContinuousAdd X']
          [ContinuousConstSMul (ResAt P) X'] [ContinuousSMul (GKS K S) X']
          (β : X →ₗ[ResAt P] X' →ₗ[ResAt P] T)
          (hβ : ∀ (g : GKS K S) (a : X) (b : X'), β (g • a) (g • b) = g • β a b)
          (hβc : Continuous fun x : X × X' => β x.1 x.2)
          (ΔA : GaloisLocalConditions K S (ResAt P) X) (ΔB : GaloisLocalConditions K S (ResAt P) X')
          (I : GalTruncIsotropyData S (ResAt P) β hβ hβc ΔA ΔB),
          ∃ (tr : (galCompactTT S (ResAt P) β hβ hβc ΔA ΔB I).X 3 →ₗ[ResAt P] ResAt P)
            (_ : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc ΔA ΔB I).d 2 3 rfl z) = 0),
            InducesIsoH3 tr ∧ L.Normalizes tr

end ZInQ.Manuscript.RC.FibreDuality

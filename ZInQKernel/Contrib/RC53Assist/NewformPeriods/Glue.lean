import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Leaves

/-!
# The named translation steps (GLUE) of the reduction of `NewformPeriodsRational`

Each `Prop` below is a precise, standard mathematical statement used, together with the two
printed leaves of `Leaves.lean`, to prove `NewformPeriodsRational` (`Reduction.lean`). None of them
is proved here, none is a print, and none mentions the scalar sought by the target except as a
conclusion derived from stated data.

* `NewformOfModularCurveGlue` (G0): a modular `E/ℚ` has, at some level `M`, a normalized full Hecke
  eigenform with trivial character whose coefficients are exactly those of `L(E, s)` (the newform
  of `E`, at the conductor).
* `ParametrizationPeriodsGlue` (G1): periods of the pull-back of the invariant differential along a
  `ℚ`-rational map `X₀(M) → A` lie in the period lattice: if `(x, y)` is a nonconstant point of
  `A` over `ℚ(j, j_M)` and `θx = c · ĝ · (2y + a₁x + a₃)`, then `c · Π_M(g) ⊆ Λ_A` for every
  period lattice of `A`.
* `IsogenyLatticeGlue` (G2): an isogeny `E₁ → E₂` over `ℚ` maps the period lattice of `E₁` into
  that of `E₂` after multiplication by a nonzero RATIONAL number (the pull-back of `ω_{E₂}` is a
  rational multiple of `ω_{E₁}`).

The rationality of the pull-back scalar is not an assumption: it is PROVED from the `q`-expansion
form (`exists_rat_eq_of_pullbackIsMultiple`, `RationalParametrization.lean`). The level transport
is PROVED (`Transport.lean`).
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.NewformPeriods

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.PoleS12
open CongruenceSubgroup UpperHalfPlane

/-- **G0 — the newform of a modular elliptic curve, with its exact coefficients** (GLUE). If
`E/ℚ` has a weight-two cusp form on `Γ₀(N)`, `N > 0`, whose positive coefficients are the
Dirichlet coefficients of `L(E, s)` (`IsModular E`), then for some `M > 0` there is a cusp form
`g ∈ S₂(Γ₀(M))` which is a normalized eigenform of every Hecke operator `T_n`, `n ≥ 1` (the
indices not prime to `M` included), with trivial character, and whose coefficients are
`a_n(g) = E.LFunction n` for every `n ≥ 1`.

Classical content: the newform `g` of level the conductor `N(E)` (Atkin–Lehner–Li theory, Li 1975,
bibitem `li-newforms`; its coefficients at the bad primes agree with the local factors of `E` by
Carayol 1986, bibitem `carayol`), whose coefficients satisfy the same multiplicativity and prime
power recurrences as the Euler product `E.LFunction`. The hypothesis `IsModular E` replaces BCDT's
modularity. Not proved here. -/
def NewformOfModularCurveGlue : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic → IsModular E →
    ∃ (M : ℕ) (_ : NeZero M) (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2),
      IsNormalizedFullEigenformGamma0 M g ∧
        ∀ n : ℕ, 0 < n → (qExpansion 1 g).coeff n = (E.LFunction n : ℂ)

/-- **G1 — periods of the pull-back of a rational differential lie in the period lattice**
(GLUE). Let `g ∈ S₂(Γ₀(M))`, `A/ℚ` an elliptic curve, `(x, y)` a nonconstant point of `A` over
`ℚ(j, j_M) ⊆ ℚ((q))` (a `ℚ`-morphism `X₀(M) → A`), and `c ≠ 0` with
`θx = c · ĝ · (2y + a₁x + a₃)` (the pull-back of `ω_A` is `c · 2πi g(τ) dτ`). Then for every
period lattice `Lat` of `A` (`IsLatticeOf`), `c (F_g(γτ) − F_g(τ)) ∈ Lat` for all `γ ∈ Γ₀(M)` and
`τ ∈ ℍ` (`IsParamScale`).

Classical proof: the elements of `ℚ(j, j_M)` are `q`-expansions of meromorphic `Γ₀(M)`-invariant
functions on `ℍ` (`j(γτ) = j(τ)` and `j(M γτ) = j(γ'(Mτ))`), so `(x, y)` defines a holomorphic
`Γ₀(M)`-invariant map `P : ℍ → A(ℂ) = ℂ/Λ` (normalized uniformization `x = ℘_Λ − b₂/12`,
`y = (℘'_Λ − a₁x − a₃)/2`, which pulls `ω_A` back to `dz`, for `Λ` with `g₂ = c₄/12`,
`g₃ = c₆/216`). A lift `u : ℍ → ℂ` of `P` has `u' = 2πi c g` by the differential identity, hence
`u = c F_g + const`, and `P(γτ) = P(τ)` gives `c (F_g(γτ) − F_g(τ)) ∈ Λ`. This is the analytic
content of the period model of Shimura 1973, §3, Proposition 3 and the Remark after it (p. 530:
"Then A is isomorphic, via F, to C^m/P", the periods being `[γ, g] = ∫_z^{γ(z)} g(z)dz`, p. 529),
transported along the normalized uniformization. Not proved here. -/
def ParametrizationPeriodsGlue : Prop :=
  ∀ (M : ℕ) [NeZero M] (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : WeierstrassCurve ℚ), A.IsElliptic →
    ∀ x y : LaurentSeries ℚ, IsModularPointQ M A x y →
    ∀ c : ℂ, c ≠ 0 → PullbackIsMultiple A x y (qExpansion 1 g) c →
    ∀ Lat : PeriodPair, IsLatticeOf A Lat → IsParamScale M g Lat c

/-- **G2 — isogenous curves over `ℚ` have period lattices commensurable by a rational scalar**
(GLUE). If there is an isogeny `E₁ → E₂` over `ℚ` (`TauCeti.Isogeny`) and `Lat₁`, `Lat₂` are
period lattices of `E₁`, `E₂` (`IsLatticeOf`), then `r · Lat₁ ⊆ Lat₂` for some nonzero `r ∈ ℚ`.

Classical proof: the isogeny `β` pulls the invariant differential back as `β^* ω_{E₂} = r ω_{E₁}`
with `r ∈ ℚ^×` (both differentials are defined over `ℚ`, the invariant differentials of `E₁` over
`ℚ` form the line `ℚ ω_{E₁}`, and `β` is separable in characteristic `0`); over `ℂ`, through the
normalized uniformizations (which pull `ω_{Eᵢ}` back to `dz`), `β` is induced by `z ↦ r z`, so
`r Λ₁ ⊆ Λ₂`. Not proved here. -/
def IsogenyLatticeGlue : Prop :=
  ∀ E₁ E₂ : WeierstrassCurve ℚ, E₁.IsElliptic → E₂.IsElliptic →
    Nonempty (TauCeti.Isogeny E₁.toAffine E₂.toAffine) →
    ∀ Lat₁ Lat₂ : PeriodPair, IsLatticeOf E₁ Lat₁ → IsLatticeOf E₂ Lat₂ →
      ∃ r : ℚ, r ≠ 0 ∧ ∀ l ∈ Lat₁.lattice, (r : ℂ) * l ∈ Lat₂.lattice

end ZInQ.Contrib.RC53Assist.NewformPeriods




noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

/-! ## §0. Cheap definitions -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. (Its restriction to `ℚ` is then `ℤ_(p)`.) -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`: it stabilizes `v` and acts as
`x ↦ x^p` on its residue field. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- A continuous `n`-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` (Mathlib's normed
`PadicAlgCl ℓ`). Continuity for the norm topology is equivalent to the usual notion (the image
lies in `GL_n` of a finite extension of `ℚ_ℓ`), by compactness and Baire. -/
structure GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where
  toHom : GQ →* GL (Fin n) (PadicAlgCl ℓ)
  continuous_toHom : Continuous toHom

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- `ρ` is unramified at `p`: every inertia group above `p` acts trivially. -/
def GaloisRep.UnramifiedAt (ρ : GaloisRep ℓ n) (p : ℕ) : Prop :=
  ∀ v : ValuationSubring Qbar, LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ρ.toHom ((σ : v.decompositionSubgroup ℚ) : GQ) = 1

/-- Every arithmetic Frobenius above `p` has trace `a` (meaningful at unramified `p`). -/
def GaloisRep.FrobTrace (ρ : GaloisRep ℓ n) (p : ℕ) (a : PadicAlgCl ℓ) : Prop :=
  ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
    Matrix.trace (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = a

/-- `c` is a complex conjugation: it is induced by `z ↦ z̄` through some embedding `ℚ̄ → ℂ`. -/
def IsComplexConj (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- `ρ` is odd: `det ρ(c) = −1` for every complex conjugation `c`. -/
def GaloisRep.IsOdd (ρ : GaloisRep ℓ 2) : Prop :=
  ∀ c, IsComplexConj c → Matrix.det (ρ.toHom c : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = -1

/-- `ρ` is (absolutely) irreducible, in Burnside's form: its image spans `M_n(ℚ̄_ℓ)`. Over the
algebraically closed `ℚ̄_ℓ` this is equivalent to irreducibility. -/
def GaloisRep.IsIrreducible (ρ : GaloisRep ℓ n) : Prop :=
  Algebra.adjoin (PadicAlgCl ℓ)
    (Set.range fun σ => (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) = ⊤

/-- `ρ` is semisimple: every invariant subspace has an invariant complement. -/
def GaloisRep.IsSemisimple (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, W.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W) →
    ∃ W', IsCompl W W' ∧
      ∀ σ, W'.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W'

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all Hecke operators with nebentypus `χ`, expressed through
its coefficients: `a₁ = 1` and `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}` (with `χ(d) = 0`
for `(d, N) > 1`). For a form with nebentypus `χ` this is equivalent to the Hecke definition
(Diamond–Shurman, Prop. 5.3.1; locator UNVERIFIED). -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `ρ` is attached to the eigenform `g` (through embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`): for
`p ∤ Nℓ`, `ρ` is unramified at `p` and its Frobenius trace is `ιL(α)` where `ιC(α) = a_p(g)`. -/
def GaloisRep.AttachedTo (ρ : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : CF N k) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧ ρ.FrobTrace p (ιL α)

/-! ## §1. Leaves statable today over the cheap definitions (not proved here; copied from the
hdec-faithful draft). Numbering of the note: T13 Skolem–Noether, T14 HasseBrauerQ, T17
Kronecker–Weber, T18 FrobeniusDense, T19 Brauer–Nesbitt, R14 EigenformRepExists, R15
DeligneSerreConseq, T24 EigenformTwist. -/

/-- **L14. Skolem–Noether** (Reiner, *Maximal orders*, Thm 7.21; Tau Ceti `skolemNoether`).
Exact. -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

/-- **L15(a). Hasse principle for `Br(ℚ)`, in the form used** (Albert–Brauer–Hasse–Noether with
the sum formula; Milne, *Arithmetic duality theorems*, Ch. I). A central simple `ℚ`-algebra that
splits over every `ℚ_p` splits over `ℚ`. Consequence (the real invariant is forced to 0). -/
def HasseBrauerQ : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℚ A] [Algebra.IsCentral ℚ A] [IsSimpleRing A]
    [FiniteDimensional ℚ A] (n : ℕ), Module.finrank ℚ A = n ^ 2 →
    (∀ p : ℕ, ∀ _ : Fact p.Prime,
      Nonempty (TensorProduct ℚ ℚ_[p] A ≃ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) ℚ_[p])) →
    Nonempty (A ≃ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ)

/-- **L17. Kronecker–Weber** (Washington, *Cyclotomic fields*, Thm 14.1; Tau Ceti
`kroneckerWeber`). Exact. -/
def KroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

/-- **L18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- **L19. Brauer–Nesbitt** (Curtis–Reiner §30). Semisimple representations of a group over a
field of characteristic 0 with equal traces are isomorphic. Exact. -/
def BrauerNesbitt : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

/-- **L27(a). Galois representations of eigenforms** (Eichler–Shimura `k = 2`, Deligne 1971
`k ≥ 2`, Deligne–Serre 1974 `k = 1`). Consequence (the published statements also give the
determinant). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **L27(b). Deligne–Serre, in the form used** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with L18 and
L19). A semisimple representation attached to a weight-one eigenform has finite image.
Consequence. -/
def DeligneSerreConseq : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **L28(a). Twisting an eigenform** (Shimura 1971, Prop. 3.64; Atkin–Li 1978). The twist of a
normalized eigenform of level `N` by a character mod `m` is a normalized eigenform of level
`Nm²` with coefficients `ψ(p) a_p` at `p ∤ Nm`. Consequence. -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p


/-! ## §2. Leaves that need definitions Mathlib lacks: placeholders (no content)

Each docstring gives the statement in the form the proof uses, the reference (UNVERIFIED unless
the note says otherwise), and the missing definitions with their cost tier. -/

/-! leaf-adopt (2026-11-12): the placeholders `R01_ShimuraDeligne`, `R02_BabaGranath` and
`R05_GonzalezRotger` are replaced by leaf-qm-fp's concrete field-point statements (section
`LeafQMSec`), with rv-blueprints' repairs Q2, Q4, Q5 (section `LeafAdoptSec`): the bundle uses
`LeafAdopt.R1R2fpRep` (R1(a), (c), (d), R1 at level one, `π₀(X₆) = 1`, R2 with biconditional CM
clauses, R5 on points), `LeafQM.AV.R1rec` (R1(d), object form), `LeafQM.AV.R5fp` (= R5fpStrong,
`LeafAdopt.R5fp_iff_R5fpStrong`) and `LeafQM.AV.R5fpCount`. All of them rest on Lemma P of
rv-qm-polar (type `μ` fixed, characteristic 0, `𝒪` maximal; see `LeafAdopt.R1R2fpRep`;
leaf-adopt2). Part (b) of R1 stays a placeholder: -/

/-- **R1(b). Complex uniformization, in family form** (rv-blueprints Q3; R1an of bp-qmmoduli).
For `Y₃` and `π : Y₃ → P¹` of `LeafAdopt.R1R2fpRep`: (a) for every `P : QML3 ℂ` there is `τ ∈ ℍ`
with `P.A(ℂ) ≅ ℂ²/ι(𝒪)(τ, 1)ᵀ` compatibly with `ι`; (b) for every `τ ∈ ℍ` there are `P_τ : QML3 ℂ`
and such an isomorphism; (c) `τ ↦ π(Φ⁻¹[P_τ]) ∈ P¹(ℂ)` is holomorphic on `ℍ`. The Hauptmodul
comparison of F1 (`PkgI1.QMHauptmodul` against `π`) uses (b) and (c); a statement at each point
separately is too weak. Shimura, Ann. of Math. 85 (1967), Main Thm I; Deligne, Sém. Bourbaki 389
(1971), §4.15 (analytic families) (UNVERIFIED locators). Missing: analytification of `ℂ`-schemes
and of abelian varieties (large; bp-qmmoduli N14). Rests on Lemma P (rv-qm-polar) as R1R2fpRep.
Part (a) at a single point would follow from `ZInQ.LeafPush2.UniformizationExists` (T35) with
T11a (the `ℂ`-linear action of `ι(𝒪)` on the lattice), class number one of `𝒪` (Eichler) and the
QM lattice computation (bp-analytic Q1); that reduction is not carried out. (b) and (c) are the
family statements. -/
opaque R01b_ComplexUniformization : Prop

/-! leaf-adopt2 (2026-11-12): the placeholder `R03_LinYang` is replaced by leaf-push2's
`ZInQ.LeafPush2.R03_LinYang` (section `LeafPush2Sec`): over `ℂ`, every abelian surface with
`𝒪 ↪ End A` is `≅ Jac C` for a curve `C` with a sextic model on the Lin–Yang family at some
`j ≠ 0`, or a product of elliptic curves. A consequence of Lin–Yang Example 29 with Weil's
dichotomy and Lemma P (rv-qm-polar). The `J`/Igusa–Clebsch convention is tied to hdec-elementary's
`OnQMLocus` (`ZInQ.LeafPush2.linYangTuple_onQMLocus`, proved). The `ℚ̄`-form
`R03_LinYang_algClosed` is a glue target (Lefschetz principle). -/



/-! leaf-adopt (2026-11-12): the placeholder `R16_EichlerShimuraJ1` is replaced by
leaf-modcurves' `LeafModCurves.R16_EichlerShimuraJ1'` (section `LeafModCurvesSec`), stated for
every `K_N` model of `X₁(N)` (`IsJ1`), so bp-modcurves' leaf MC9 is not needed (rv-blueprints M1).
Its 2-dimensional constituent of `V_ℓ(J₁(N))` is derived (`LeafModCurves.g13_constituent`, from
the glue target `VSurjOfSurjective`). New textbook leaves from the same file:
`LeafModCurves.JacobianExists ℚ` (T33) and `LeafModCurves.DimJ1Genus` (T34). -/


/-- **R17. Carayol's local–global compatibility** (docstring repaired by rv-loc-leaves, adopted 2026-11-12 by loc-fix; the concrete statement is
`LadicCond.CarayolR17'` of scratch/def-ladic-cond, unchanged). For a weight-2 newform of level `N`,
any prime `ℓ` (including `ℓ = 2`) and any prime `p ≠ ℓ` (including `p ∣ N`), the Artin conductor
exponent of `ρ_{f,λ}|G_{ℚ_p}` is `v_p(N)`. Ann. Sci. ÉNS 19 (1986), Théorème (A), pp. 409-411,
§0.8 p. 411 (coverage of `p ∣ N` and `ℓ = 2` YES per the audit; the extra discrete-series
hypothesis concerns only totally real `F` of even degree, not `ℚ`), with the newform conductor
`a(π_p) = v_p(N)` (Casselman 1973; UNVERIFIED locator). Duals and unramified twists do not change
the conductor. Do not replace by Théorème (B) or by the `Γ₀` elliptic-curve corollary. -/
opaque R17_Carayol : Prop

/-! leaf-adopt2 (2026-11-12): the placeholder `R18_Javanpeykar` is replaced by leaf-push2's
`ZInQ.LeafPush2.R18_Javanpeykar` (section `LeafPush2Sec`): over a number field `K`, for a pointed
curve `X` with Jacobian `J` (`IsJacobian`), `g = dim J ≥ 1` and a Belyi function `t ∈ K(X)` of
degree `d > 0`, `stableFaltingsHeight J ≤ 13·10⁶ · g · d⁵` (in `EReal`). A consequence of ANT 8
(2014) Thm 1.1.1 with H5. Its height is leaf-push2's copy of def-faltings' height over
`PkgI3.AbVar`. -/

/-! leaf-adopt (2026-11-12): the placeholders `R19_GaudronRemond`, `R20_FaltingsHeightLemma`,
`R21_Bost` are replaced by def-faltings' `ZInQ.DefFaltings.R19_GaudronRemond`,
`R20_FaltingsLemma5`, `R21_Bost` over `stableFaltingsHeight` (section `DefFaltingsSec`), with H5
as an explicit leaf `LeafAdopt.H5` (rv-blueprints F2). **Not yet known to be non-vacuous**: the
three Props `AnalyticUniformizationExists`, `AnalyticUniformizationUnique`,
`HodgeLatticeTheorem` (node AN3 and the Hodge lattice) are open, and until they are proved the
index set of the infimum may be empty (`h = ⊤`): then R21 holds trivially and R19, R20 have no
instance. R19 is normalization-sensitive (a consequence only if Gaudron–Rémond's `h` is Faltings'
original normalization, rv-blueprints F4). -/


/-! leaf-adopt2 (2026-11-12): the placeholder `R22_Pazuki` is replaced by leaf-push2's
`ZInQ.LeafPush2.R22_Pazuki` (section `LeafPush2Sec`): the audit's upper half
`h([θ_m(0, Ω)]) ≤ X/2 + C₂ log(X + 2)` for `X ≥ max(1, h_F + log π)`, for every abelian surface
over a number field, every analytic uniformization at every complex place and every `Ω ∈ 𝔥₂`
that is a period matrix of its lattice (all principal polarizations, no polarization object).
Consequence of Bull. SMF 140 (2012) Cor. 1.3(2) with H5; the identification of Pazuki's level-2
coordinates (Def. 2.6) with `θ[a;b](0, Ω)` is UNVERIFIED (the main risk). The glue form with
`X = max(1, h_F + 3)` is `ZInQ.LeafPush2.R22_plus3` (proved). -/


/-! leaf-adopt3 (2026-11-13): the placeholder `T10_TateDuality` is removed. T10 is now t10-etale's
concrete Galois-equivariant `T10Etale.T10_TateDuality` over Mathlib's pro-étale `ℓ`-adic cohomology
(section `T10EtaleSec`, below the bundles' reopening point). -/

/-! leaf-adopt2 (2026-11-12): the placeholders `T11_RiemannGAGA` and `T12_ArtinComparison` are
removed. T11 is now the two concrete textbook leaves `ZInQ.LeafPush2.T11a_RiemannEnd`
(endomorphisms of `A/ℂ` = `ℂ`-linear maps preserving the lattice of a uniformization) and
`ZInQ.LeafPush2.T11b_Rigidity` (`Hom(A_L, B_L) = Hom(A, B)` over `k = k̄` of characteristic 0).
T12 is glue: its used form `ZInQ.LeafPush2.T12_ComplexConjEigen` (the `±1`-eigenspaces of complex
conjugation on `V_ℓ(A)` have dimension `dim A`) is a glue target from T35, T5, T26 and the
antiholomorphy of complex conjugation. The new textbook leaf T35 is
`ZInQ.LeafPush2.UniformizationExists` (AN3 for abelian varieties: Mumford §1 with GAGA); it is
kept instead of bp-analytic's `UniformizationLeaf` (docs/research/leaf-adopt2.md §2): its
predicate is the one R22 and T11a quantify over, it ties `g` to `dim A`, and it covers every
`K` with `σ : K → ℂ`. -/




/-! hsyn-fold: R8, T9, T23, T29 and T32 are no longer placeholders. Their concrete statements
(task leaf-push) are `PkgI2.GrothendieckMonodromy` (= `LeafPush.R08_GrothendieckMonodromy`,
consequence form), `LeafPush.T09_WeilPairing` (consequence, polarization hidden),
`PkgI4.T23_FontaineClosure` (exact, matrix form, `ℚ_p` coefficients),
`LeafPush.T29a_DivisionNormalizer` and `LeafPush.T29b_SplitNormalizer` (exact),
`LeafPush.T32a_TameQuadratic` and `LeafPush.T32b_QuadraticRamification` (consequences).
leaf-adopt (2026-11-12): T32 is now glue, proved (`HSyn.t32a_glue`, `HSyn.t32b_glue`, §3).
leaf-adopt2 (2026-11-12): T12 is now glue (target `ZInQ.LeafPush2.T12_ComplexConjEigen`,
unproved). -/

/-! ## §3. Glue -/

/-- **T32(a) is glue** (leaf-adopt, 2026-11-12): proved in scratch/glue-t32a (`GlueB3Unram.t32a`,
copied in section `GlueT32aSec`), with no leaf. -/
theorem t32a_glue : LeafPush.T32a_TameQuadratic := GlueB3Unram.t32a

/-- **T32(b) is glue** (leaf-adopt, 2026-11-12): proved in scratch/glue-b3b (`GlueB3Unram.t32b`,
copied with scratch/glue-t32a in section `GlueT32aSec`), with no leaf. -/
theorem t32b_glue : LeafPush.T32b_QuadraticRamification := GlueB3Unram.t32b

/-- **The two complex-conjugation predicates agree** (leaf-adopt2): leaf-push2's
`ZInQ.LeafPush2.IsComplexConj` (used by `T12_ComplexConjEigen`) is pkg-I4's
`PkgI4.IsComplexConj` (used by the oddness of `GaloisRep`s, G10), by definition. -/
theorem isComplexConj_leafPush2_iff (c : Field.absoluteGaloisGroup ℚ) :
    ZInQ.LeafPush2.IsComplexConj c ↔ PkgI4.IsComplexConj c :=
  Iff.rfl

/-- **Glue target (leaf-adopt2, unproved): the two copies of the stable Faltings height agree.**
R18 and R22 (leaf-push2) are stated over `ZInQ.LeafPush2.stableFaltingsHeight` on `PkgI3.AbVar`;
R19-R21 and H5 (def-faltings) over `ZInQ.DefFaltings.stableFaltingsHeight` on def-faltings' copy
of the structure. The two definitions are textual copies (leaf-push2 Part I = def-faltings §§1-18
with `AbVar` replaced), so this is pure transport along `LeafAdopt.abVarEquiv` (every structure of
the Arakelov layer is duplicated, so the proof needs an equivalence of `GroupModel`, `HodgeData`
and `MetrizedModel` and equality of model heights). It is what lets the glue apply H5 to R18 and
R22. Not a leaf. -/
def HeightCopiesAgree : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ZInQ.LeafPush2.stableFaltingsHeight A =
      ZInQ.DefFaltings.stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm A)

/-- **B3(v) with no leaf** (glue-t32a): `LeafB3a` of glue-b3-unram is proved. -/
theorem leafB3a_glue : GlueB3Unram.LeafB3a := GlueB3Unram.leafB3a

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization; from the hdec-faithful draft). -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **G15 (D3), pkg-I6's `sq_principalUnits` proved** from glue-conductor's
`exists_sq_eq_one_add` (same statement as `PkgI6.sq_principalUnits`, which is `sorry` there). -/
theorem sq_principalUnits_proved (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] (e : ℕ) (_he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = IsLocalRing.maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ IsLocalRing.maximalIdeal B ^ (r + e)) :
    ∃ x ∈ IsLocalRing.maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y := by
  obtain ⟨w, hw, h⟩ := GlueConductor.exists_sq_eq_one_add e (r - e) (by omega) he y
    (by rwa [show 2 * e + (r - e) = r + e by omega])
  exact ⟨w, by rwa [show e + (r - e) = r by omega] at hw, h⟩

/-- **D3 (GLUE, proved)**: pkg-I6's `sq_principalUnits`, from glue-conductor's Hensel argument. -/
theorem _root_.PkgI6.sq_principalUnits (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] (e : ℕ) (he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = IsLocalRing.maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ IsLocalRing.maximalIdeal B ^ (r + e)) :
    ∃ x ∈ IsLocalRing.maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y :=
  sq_principalUnits_proved B e he1 he r hr y hy

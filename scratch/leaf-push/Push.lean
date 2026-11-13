/-
leaf-push: concrete Lean statements for placeholders of docs/research/h-decomposition.md
(scratch/h-decomposition/Leaves.lean §2).

Each leaf is a `def … : Prop` over genuine Mathlib objects (no structure invented for the
purpose). §1 copies verbatim, from scratch/pkg-I2/I2.lean, the definitions of abelian varieties,
points, Galois action and inertia (scratch files cannot import each other). No `sorry`, no `axiom`.
-/
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Squarefree.Basic

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj Quaternion

namespace LeafPush

/-! ## 1. Abelian varieties, points, Galois action, inertia (copied from pkg-I2) -/

section AV

variable {K : Type u} [Field K]

/-- `Spec L` as a scheme over `Spec K`. -/
noncomputable def specOver (K L : Type u) [Field K] [CommRing L] [Algebra K L] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- An abelian variety over `K`: a group object of `Over (Spec K)` whose structure morphism is
proper, smooth and geometrically integral (Mathlib's notions). Mathlib proves that such a group
object is commutative (`isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
class IsAbelianVariety (A : Grp (Over (Spec (.of K)))) : Prop where
  proper : IsProper A.X.hom
  smooth : Smooth A.X.hom
  geomIntegral : GeometricallyIntegral A.X.hom

/-- An abelian scheme over a ring `O`: a group object of `Over (Spec O)`, proper, smooth, with
geometrically connected fibres (Mumford, GIT, Def. 6.1). -/
class IsAbelianScheme {O : Type u} [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) : Prop where
  proper : IsProper 𝒜.X.hom
  smooth : Smooth 𝒜.X.hom
  geomConnected : GeometricallyConnected 𝒜.X.hom

/-- The `L`-points `A(L)` of a scheme over `K`, for a `K`-algebra `L`; for a group object this
is a group (`MonObj.Hom.group`). -/
abbrev Pts (A : Grp (Over (Spec (.of K)))) (L : Type u) [CommRing L] [Algebra K L] :=
  specOver K L ⟶ A.X

/-- The `m`-torsion `A(L)[m]`. -/
def torsion (A : Grp (Over (Spec (.of K)))) (L : Type u) [CommRing L] [Algebra K L] (m : ℕ) :
    Set (Pts A L) :=
  {x | x ^ m = 1}

/-- The automorphism of `Spec L` over `Spec K` induced by `σ ∈ Aut(L/K)`. -/
noncomputable def galHom (L : Type u) [CommRing L] [Algebra K L] (σ : L ≃ₐ[K] L) :
    specOver K L ⟶ specOver K L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [specOver, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

/-- The Galois action on points: `(σ • x)` has coordinates `σ ∘ x^*`. -/
noncomputable def galAct (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : Pts A L :=
  galHom L σ ≫ x

/-- `σ` lies in the inertia group of the valuation subring `w` of `L` (Mathlib's
`ValuationSubring.inertiaSubgroup`). -/
def IsInertia {L : Type u} [Field L] [Algebra K L] (w : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    Prop :=
  ∃ h : σ ∈ w.decompositionSubgroup K,
    (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K

/-- `A` has good reduction at the valuation subring `O` of `K`: there is an abelian scheme over
`O` whose generic fibre is isomorphic to `A` as a group object over `K` (Serre–Tate 1968, §1). -/
def HasGoodReduction (A : Grp (Over (Spec (.of K)))) (O : ValuationSubring K) : Prop :=
  ∃ 𝒜 : Grp (Over (Spec (.of O))), IsAbelianScheme 𝒜 ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)

/-- The inertia group of `w` acts trivially on `A(L)[m]`. -/
def InertiaTrivialOn (A : Grp (Over (Spec (.of K)))) {L : Type u} [Field L] [Algebra K L]
    (w : ValuationSubring L) (m : ℕ) : Prop :=
  ∀ σ : L ≃ₐ[K] L, IsInertia w σ → ∀ x ∈ torsion A L m, galAct A σ x = x

/-- `(σ - 1)² x = 0`, written multiplicatively (the group of points is commutative). -/
def UnipSq (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : Prop :=
  galAct A σ (galAct A σ x) * (galAct A σ x)⁻¹ * (galAct A σ x)⁻¹ * x = 1

end AV

/-! ## 2. R8: Grothendieck's semistable reduction theorem, monodromy form -/

/-- **R8 (consequence form). Grothendieck's semistable reduction theorem.**
Published statement: SGA 7 I, Exp. IX, Thm 3.6 (UNVERIFIED numbering): an abelian variety `A`
over the fraction field `K` of a discrete valuation ring acquires semistable reduction over a
finite separable extension; Prop. 3.5 of the same exposé (UNVERIFIED): semistable reduction at
`w` is equivalent to "every inertia element `σ` acts on `T_ℓ A` with `(σ - 1)² = 0`" (`ℓ`
invertible in the residue field). Lean form: there is a finite `K' ⊆ K̄` such that every inertia
element of `w` fixing `K'` satisfies `(σ - 1)² = 0` on every `A(K̄)[ℓⁿ]`. This is the image of
Thm 3.6 under the direction "semistable ⇒ unipotent of echelon 2" of Prop. 3.5, applied over
`K'` (whose inertia at `w` is `I_w ∩ G_{K'}`); the finite-level form is equivalent to the
Tate-module form because `T_ℓ A → A[ℓⁿ]` is onto. It is therefore a consequence, never stronger.
Identical to `PkgI2.GrothendieckMonodromy` (pkg-I2), restated here so that R8 is counted as a
concrete leaf. Used only on h-b1's route for A6 (Raynaud's route R6 avoids it). -/
def R08_GrothendieckMonodromy : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
          (∀ x ∈ K', σ x = x) →
          ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-! ## 3. T9: the Weil pairing, finite-level Galois form -/

/-- **T9 (consequence form). Weil pairing of a polarization.**
Published statements (Mumford, *Abelian varieties*, §20: the Weil pairing
`e_n : A[n] × Â[n] → μ_n` is bilinear, perfect, Galois-equivariant, with `e_{mn}(x, y) = e_n(mx, y)`;
§23: for `λ = φ_L`, `e^L_n(x, y) := e_n(x, λ y)` is skew-symmetric with `e^L_n(x, x) = 1`;
Milne, *Abelian varieties* (in Cornell–Silverman 1986), §§13, 16; numbering UNVERIFIED), with the
existence over `K` of an ample line bundle `L` (Mumford §6), whose polarization `λ = φ_L` has
kernel killed by some `d ≥ 1`. Lean form: for an abelian variety `A/K` there are `d ≥ 1` and a
family `e n : A(K̄) × A(K̄) → K̄` such that for every `n ≥ 1` invertible in `K`, on `A[n]`:
values in `μ_n`, bimultiplicative, alternating, Galois-equivariant (`e(σx, σy) = σ(e(x, y))`),
compatible (`e_n(x^m, y^m) = e_{mn}(x, y)^m`), and nondegenerate up to `d` (if `e_n(x, y) = 1`
for all `y ∈ A[n]` then `x^d = 1`). Take `e n x y := e_n(x, λ y)`. The last clause: there is
`ψ : Â → A` with `λ ∘ ψ = [d]`, so `d·Â[n] ⊆ λ(A[n])`, and perfectness of `e_n` gives `d x = 0`.
Equivariance holds since `λ` is defined over `K`. Hence a consequence, never stronger.
The form used at C8 step 1 (h-trust; `ℓ = 5`): passing to the limit over `n = ℓᵏ` gives a
`G_K`-equivariant alternating pairing on `T_ℓ A` with values in `ℤ_ℓ(1)` whose kernel is killed by
`d`, hence perfect on `V_ℓ A`: `G_K` acts through `GSp` with cyclotomic multiplier, for every `ℓ`
invertible in `K` (glue). The group of points is written multiplicatively, as in pkg-I2. -/
def T09_WeilPairing : Prop :=
  ∀ (K : Type u) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
    ∃ d : ℕ, 0 < d ∧ ∃ e : ℕ → Pts A (AlgebraicClosure K) → Pts A (AlgebraicClosure K) →
        AlgebraicClosure K,
      ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
        (∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ y ∈ torsion A (AlgebraicClosure K) n,
          e n x y ^ n = 1) ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ x' ∈ torsion A (AlgebraicClosure K) n,
          ∀ y ∈ torsion A (AlgebraicClosure K) n,
            e n (x * x') y = e n x y * e n x' y ∧ e n y (x * x') = e n y x * e n y x') ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n, e n x x = 1) ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n,
          (∀ y ∈ torsion A (AlgebraicClosure K) n, e n x y = 1) → x ^ d = 1) ∧
        (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ y ∈ torsion A (AlgebraicClosure K) n,
            e n (galAct A σ x) (galAct A σ y) = σ (e n x y)) ∧
        (∀ m : ℕ, 0 < m → (m : K) ≠ 0 →
          ∀ x ∈ torsion A (AlgebraicClosure K) (m * n),
          ∀ y ∈ torsion A (AlgebraicClosure K) (m * n),
            e n (x ^ m) (y ^ m) = e (m * n) x y ^ m)

/-! ## 4. T29: local normalizers of maximal quaternion orders -/

section T29

variable (p : ℕ) [Fact p.Prime]

/-- `x ∈ ℚ_p` lies in `ℤ_p`. -/
def IsPadicInt (x : ℚ_[p]) : Prop := ‖x‖ ≤ 1

/-- An element of `ℍ[ℚ_p, a, b] = (a, b)_{ℚ_p}` is integral: its reduced trace `x + x̄` and
reduced norm `x x̄` (scalars) lie in `ℤ_p`. -/
def QIntegral {a b : ℚ_[p]} (x : ℍ[ℚ_[p], a, b]) : Prop :=
  (∃ t : ℚ_[p], IsPadicInt p t ∧ x + star x = (t : ℍ[ℚ_[p], a, b])) ∧
  (∃ n : ℚ_[p], IsPadicInt p n ∧ x * star x = (n : ℍ[ℚ_[p], a, b]))

/-- `u` is a unit of the ring of integral elements: `u` and some integral `v` with `u v = 1`. -/
def IsOUnit {a b : ℚ_[p]} (u : ℍ[ℚ_[p], a, b]) : Prop :=
  QIntegral p u ∧ ∃ v : ℍ[ℚ_[p], a, b], QIntegral p v ∧ u * v = 1 ∧ v * u = 1

/-- **T29(a) (division case). Vignéras, LNM 800, Ch. II, §1 (UNVERIFIED numbering: Lemme 1.5,
Thm 1.6 / Cor. 1.7).** Published statement: if `H` is the quaternion division algebra over
`ℚ_p`, the integral elements form a ring `𝒪`, the unique maximal order; there is `π` with
`v(nrd π) = 1`, every `x ∈ H^×` is `π^k u` with `u ∈ 𝒪^×`, and hence (with `ℚ_p^× = p^ℤ ℤ_p^×`,
`p = π²·unit`) `H^× / ℚ_p^× 𝒪^×` has order 2, generated by `π`; and `N(𝒪) = H^×` since `𝒪` is
defined by `nrd`, `trd`, which are conjugation-invariant. Lean form, for `(a, b)_{ℚ_p}` whose
norm form is anisotropic (`x x̄ = 0 → x = 0`, i.e. a division algebra): the integral elements
are closed under `+` and `*`; there is an integral `π` that is not a scalar multiple of a unit of
`𝒪`; and every nonzero `x` is `c·u` or `c·π·u` with `c ∈ ℚ_p^×`, `u ∈ 𝒪^×`. This is the
statement "index exactly 2" written out; it is a restatement of the published one. -/
def T29a_DivisionNormalizer : Prop :=
  ∀ a b : ℚ_[p], (∀ x : ℍ[ℚ_[p], a, b], x * star x = 0 → x = 0) →
    (∀ x y : ℍ[ℚ_[p], a, b], QIntegral p x → QIntegral p y →
      QIntegral p (x + y) ∧ QIntegral p (x * y)) ∧
    ∃ π : ℍ[ℚ_[p], a, b], QIntegral p π ∧
      (¬ ∃ c : ℚ_[p], ∃ u : ℍ[ℚ_[p], a, b], IsOUnit p u ∧
          π = (c : ℍ[ℚ_[p], a, b]) * u) ∧
      ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 →
        ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ u : ℍ[ℚ_[p], a, b], IsOUnit p u ∧
          (x = (c : ℍ[ℚ_[p], a, b]) * u ∨ x = (c : ℍ[ℚ_[p], a, b]) * π * u)

/-- A `2 × 2` matrix over `ℚ_p` with entries in `ℤ_p`. -/
def IsIntMat (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) : Prop := ∀ i j, IsPadicInt p (g i j)

/-- **T29(b) (split case). Vignéras, LNM 800, Ch. II, §2 (UNVERIFIED numbering).** Published
statement: the normalizer of `M₂(ℤ_p)` in `GL₂(ℚ_p)` is `ℚ_p^× GL₂(ℤ_p)`. Lean form, exactly
that: if `g` is invertible and `g M₂(ℤ_p) g⁻¹ = M₂(ℤ_p)`, then `g = c·k` with `c ∈ ℚ_p^×` and
`k ∈ GL₂(ℤ_p)` (entries in `ℤ_p`, determinant a unit of `ℤ_p`). -/
def T29b_SplitNormalizer : Prop :=
  ∀ g : Matrix (Fin 2) (Fin 2) ℚ_[p], IsUnit g.det →
    (∀ m, IsIntMat p m ↔ IsIntMat p (g * m * g⁻¹)) →
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ k : Matrix (Fin 2) (Fin 2) ℚ_[p], IsIntMat p k ∧ ‖k.det‖ = 1 ∧
      g = c • k

end T29

/-! ## 5. T32: tame inertia and quadratic characters, over inertia subgroups of `G_ℚ` -/

/-- The absolute Galois group `G_ℚ = Aut(ℚ̄/ℚ)` (with Mathlib's Krull topology). -/
abbrev GQ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- `O` is the valuation subring `ℤ_(p)` of `ℚ`: a discrete valuation ring in which `p` is not a
unit (for any other valuation subring of `ℚ`, `p` is a unit). -/
def IsAtPrime (O : ValuationSubring ℚ) (p : ℕ) : Prop :=
  IsDiscreteValuationRing O ∧ ¬ IsUnit (p : O)

/-- The inertia subgroup `I_w ⊆ G_ℚ` of a valuation subring `w` of `ℚ̄` (Mathlib's
`ValuationSubring.inertiaSubgroup`, pushed into `G_ℚ`). -/
noncomputable def inertiaQ (w : ValuationSubring (AlgebraicClosure ℚ)) : Subgroup GQ :=
  ((w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype)

/-- **T32(a). Serre, *Local fields*, IV §2, Cor. 1-4 (tame inertia is `∏_{ℓ≠p} ℤ_ℓ(1)`, wild
inertia is pro-`p`), with the identification of `I_w ⊆ G_ℚ` with the inertia group of
`ℚ̄_p/ℚ_p` (Neukirch, ANT, II §9 / Serre II §3; numbering UNVERIFIED).** Published consequence:
for `p` odd, the continuous homomorphisms `I_p → {±1}` form a group of order 2 (a quadratic
character kills the pro-`p` wild inertia, and `Hom_cont(∏_{ℓ≠p} ℤ_ℓ, ℤ/2) = ℤ/2`). Lean form:
for `w` over `ℤ_(p)`, the continuous monoid maps `I_w →* ℤˣ` number exactly 2 (`ℤˣ = {±1}`,
discrete). "Unique nontrivial quadratic character of inertia" is exactly this. -/
def T32a_TameQuadratic : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (O : ValuationSubring ℚ), IsAtPrime O p →
    ∀ (w : ValuationSubring (AlgebraicClosure ℚ)), w.comap (algebraMap ℚ _) = O →
      Nat.card {χ : inertiaQ w →* ℤˣ // Continuous χ} = 2

/-- **T32(b). The quadratic character of `ℚ(√d)` ramifies exactly at the primes dividing `d`,
for `d ≡ 1 mod 4` squarefree** (the quadratic Dirichlet character of odd squarefree conductor
`P` is that of `ℚ(√d)`, `d = ±P ≡ 1 mod 4`). Published: the discriminant of `ℚ(√d)` is `d`
(Neukirch I (2.?); Washington Ch. 3) and `p` ramifies iff `p | disc` (Neukirch III (2.12)),
together with "ramified ⇔ inertia acts nontrivially" (Neukirch I §9; numbering UNVERIFIED).
Lean form: for a square root `s ∈ ℚ̄` of `d` and `w` over `ℤ_(p)`, some inertia element moves `s`
iff `p | d`. `σ ↦ σ(s)/s` is the quadratic character, so this is the published statement. -/
def T32b_QuadraticRamification : Prop :=
  ∀ (d : ℤ), Squarefree d → d % 4 = 1 →
    ∀ (s : AlgebraicClosure ℚ), s ^ 2 = (d : AlgebraicClosure ℚ) →
    ∀ (p : ℕ), p.Prime →
    ∀ (O : ValuationSubring ℚ), IsAtPrime O p →
    ∀ (w : ValuationSubring (AlgebraicClosure ℚ)), w.comap (algebraMap ℚ _) = O →
      ((∃ σ ∈ inertiaQ w, σ s ≠ s) ↔ (p : ℤ) ∣ d)

end LeafPush

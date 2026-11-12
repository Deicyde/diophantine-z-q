-- Copied from scratch/pkg-I2/I2.lean (lines 1-443, leaves and proved glue unchanged); rv-a6-route adds §10.
/-
pkg-I2: leaf statements for the reduction-theory package I2 of Theorem 4.1
(steps A5, A6, A8, C6, C10, D2 of docs/research/h-trust.md).

Every leaf is a `def … : Prop` over genuine Mathlib objects:
* abelian varieties are group objects in `Over (Spec K)` (Mathlib's `Grp`), proper, smooth and
  geometrically integral over `K`;
* points over a field extension `L/K` are morphisms `Spec L ⟶ A` over `Spec K`, with the group law
  of `CategoryTheory.MonObj.Hom.group`;
* inertia groups are Mathlib's `ValuationSubring.inertiaSubgroup`;
* good reduction is an abelian scheme (a group object in `Over (Spec O)`, proper, smooth, with
  geometrically connected fibres) whose base change along `Spec K ⟶ Spec O` is isomorphic to `A`
  in `Grp (Over (Spec K))`;
* purity and Abhyankar are stated with Mathlib's `IsRegularLocalRing`, `Algebra.IsEtaleAt`,
  `Algebra.IsUnramifiedAt`, `Algebra.QuasiFiniteAt`, `Ideal.ramificationIdx`.
No structure is invented for the purpose. No `sorry` and no `axiom` in this file.
-/
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.ZMod.Basic

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace RvA6

/-! ## 1. Purity of the branch locus (SGA 1 X 3.4; Stacks 0BMB), ring form -/

/-- **Leaf I2-P (Zariski–Nagata purity of the branch locus).**
Ring form of Stacks Tag 0BMB (SGA 1, Exp. X, Thm 3.4, numbering UNVERIFIED):
let `R → S` be of finite type with `R` Noetherian, `q` a prime of `S` over `p`, with `R_p` regular,
`S_q` a normal domain, `S` quasi-finite at `q`, `dim S_q = dim R_p ≥ 1`, and `R → S` unramified at
every prime `q' ⊆ q` of height one. Then `R → S` is étale at `q`. -/
def PurityBranchLocus : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-! ## 2. Abelian varieties, points, Galois action, inertia, good reduction -/

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

/-! ## 3. Néron–Ogg–Shafarevich and potential good reduction (Serre–Tate 1968) -/

/-- **Leaf I2-NOS (Serre–Tate 1968, Thm 1; criterion of Néron–Ogg–Shafarevich).**
`K` a field with a discrete valuation ring `O`, `w` a valuation ring of `K̄` over `O`, `A/K` an
abelian variety. Then (a) ⟺ (b) ⟺ (c), where (a) good reduction at `O`, (b) for every `m ≥ 1`
invertible in `O`, inertia at `w` fixes `A(K̄)[m]`, (c) the same for infinitely many such `m`. -/
def NeronOggShafarevich : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)


/-- Base change `A_{K'}` of a group object along a field extension `K → K'`. -/
noncomputable def baseChange {K : Type u} [Field K] (A : Grp (Over (Spec (.of K))))
    (K' : Type u) [Field K'] [Algebra K K'] : Grp (Over (Spec (.of K'))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K')))).mapGrp.obj A

/-- **Leaf I2-ST2 (Serre–Tate 1968, Thm 2; potential good reduction).** For a prime `ℓ`
invertible in `O`: `A` acquires good reduction over a finite extension `K' ⊆ K̄` (at `w ∩ K'`) iff
an open subgroup `I ∩ G_{K'}` of inertia acts trivially on every `A(K̄)[ℓⁿ]`, i.e. the image of
inertia in `Aut(T_ℓ A)` is finite. Used only on the h-b1 route for A6 (not on the route of §5 of
docs/research/pkg-I2.md). -/
def SerreTatePotentialGood : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (ℓ : ℕ), ℓ.Prime → IsUnit (ℓ : O) →
      ((∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          HasGoodReduction (baseChange A K') (w.comap (algebraMap K' (AlgebraicClosure K)))) ↔
       (∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
            (∀ x ∈ K', σ x = x) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), galAct A σ x = x))

/-! ## 4. Semistable reduction: Grothendieck (SGA 7 IX 3.5, 3.6) and Raynaud (SGA 7 IX 4.7) -/

/-- **Leaf I2-SS (Grothendieck's semistable reduction theorem, monodromy form).** Consequence of
SGA 7 I, Exp. IX, Thm 3.6 (`A` acquires semistable reduction over a finite extension `K'`) and
the direction "semistable ⇒ inertia acts unipotently of echelon ≤ 2" of Prop. 3.5 (numbers
UNVERIFIED): there is a finite `K' ⊆ K̄` such that every `σ` in the inertia group of `w` fixing
`K'` satisfies `(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`.
The finite-level form is equivalent to `(σ-1)² = 0` on `T_ℓ A`, since `T_ℓ A → A[ℓⁿ]` is onto. -/
def GrothendieckMonodromy : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
          (∀ x ∈ K', σ x = x) →
          ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-- **Leaf I2-Ray (Raynaud's criterion, Galois form).** Consequence of SGA 7 I, Exp. IX,
Prop. 4.7 (Raynaud: if `m ≥ 3` is invertible in `O` and the points of `A[m]` are rational over
`K`, then `A` has semistable reduction; also Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995),
Thm 3.5 per h-trust, ASTRA-READ there) and the direction "semistable ⇒ unipotent of echelon ≤ 2"
of SGA 7 IX Prop. 3.5 (numbers UNVERIFIED): every `σ` in the inertia group of `w` satisfies
`(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`. -/
def RaynaudCriterion : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-! ## 5. Néron mapping property for abelian schemes, and reduction of torsion -/

/-- **Leaf I2-NMP (Néron mapping property, abelian-scheme case).** Consequence of
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2, Def. 1 and Prop. 8 (an abelian scheme
over a DVR is the Néron model of its generic fibre; numbers UNVERIFIED): for abelian schemes
`𝒜, ℬ` over the DVR `O ⊆ K`, restriction to the generic fibre is a bijection
`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` (morphisms of schemes over the base). -/
def NeronMappingAbelianScheme : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] [IsAbelianScheme ℬ],
    Function.Bijective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

section Reduction

variable {K : Type u} [Field K]

/-- The ring map `O → w` for a valuation ring `w` of `L` lying over `O`. -/
def toW {L : Type u} [Field L] [Algebra K L] (O : ValuationSubring K) (w : ValuationSubring L)
    (hw : w.comap (algebraMap K L) = O) : O →+* w :=
  ((algebraMap K L).comp O.subtype).codRestrict w.toSubring (fun x => by
    have : (x : K) ∈ w.comap (algebraMap K L) := by rw [hw]; exact x.2
    exact this)

/-- `y ∈ 𝒜(κ(w))` is the reduction of `x ∈ A(L)`: some `x̃ ∈ 𝒜(w)` restricts to `x` on the
generic point (through `e : 𝒜_K ≅ A`) and to `y` on the closed point. -/
def IsReductionOf {L : Type u} [Field L] [Algebra K L] {O : ValuationSubring K}
    {A : Grp (Over (Spec (.of K)))} (𝒜 : Grp (Over (Spec (.of O))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (w : ValuationSubring L) (hw : w.comap (algebraMap K L) = O) (x : Pts A L)
    (y : Over.mk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue w).comp (toW O w hw)))) ⟶ 𝒜.X) : Prop :=
  ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw))) ⟶ 𝒜.X,
    (x ≫ (e.inv.hom.hom : A.X ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
        Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left ∧
    y.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ x'.left

end Reduction

/-- **Leaf I2-Red (reduction of prime-to-`p` torsion at good reduction).** Serre–Tate 1968, §1
(proof of Thm 1, (a) ⇒ (b); locator UNVERIFIED): if `A` has good reduction with abelian scheme
`𝒜` and `m ≥ 1` is invertible in `O`, reduction is a bijection
`A(K̄)[m] → 𝒜(κ(w))[m]`. -/
def ReductionTorsionBijective : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (m : ℕ), 0 < m → IsUnit (m : O) →
      (∀ x ∈ torsion A (AlgebraicClosure K) m,
        ∃! y, y ^ m = 1 ∧ IsReductionOf 𝒜 e w hw x y) ∧
      (∀ y, y ^ m = 1 → ∃! x, x ∈ torsion A (AlgebraicClosure K) m ∧ IsReductionOf 𝒜 e w hw x y)

/-! ## 6. Structure of torsion (Mumford, *Abelian varieties*, §4) -/

/-- **Leaf I2-Tors (structure of `A[n]`; boundary with I3).** Mumford, *Abelian varieties*
(1970), §4, Application 2 / §6 (locator UNVERIFIED): for an abelian variety of dimension `g` over
`K` and `n ≥ 1` invertible in `K`, `A(K̄)[n] ≅ (ℤ/n)^{2g}` as groups. The dimension is the
topological Krull dimension of the underlying space. -/
def TorsionStructure : Prop :=
  ∀ (K : Type u) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (g n : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : K) ≠ 0 →
      ∃ e : torsion A (AlgebraicClosure K) n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A (AlgebraicClosure K) n,
          ∀ h : x.1 * y.1 ∈ torsion A (AlgebraicClosure K) n, e ⟨x.1 * y.1, h⟩ = e x + e y

/-! ## 7. Abhyankar's lemma for discrete valuation rings -/

/-- **Leaf I2-AbDVR (Abhyankar's lemma, DVR form).** SGA 1, Exp. X, Lemme 3.6 (number
UNVERIFIED); also Stichtenoth, *Algebraic function fields and codes*, Thm 3.9.1, and Cornell,
Gold (classical). `R` a DVR with fraction field `K`, uniformizer `π`; `L/K` finite separable, tamely
ramified over `R` (every prime `Q` of the integral closure `S` of `R` in `L` over the maximal
ideal has `e(Q)` invertible in `R` and separable residue extension); `n` invertible in `R` with every
`e(Q) ∣ n`. Let `M = L(t)` with `tⁿ = π`. Then every prime of the integral closure of `R` in `M`
over the maximal ideal has ramification index exactly `n` and separable residue extension
(equivalently: `M/K(t)` is unramified above `R`, as `K(t)/K` is totally ramified of degree `n`). -/
def AbhyankarDVR : Prop :=
  ∀ (R K L M : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R), Irreducible π → ∀ (n : ℕ), 0 < n → IsUnit (n : R) →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ Q)) →
    ∀ t : M, t ^ n = algebraMap R M π → IntermediateField.adjoin L {t} = ⊤ →
      ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal R)],
        Q.ramificationIdx R = n ∧
        Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ Q)


/-! ## 8. Characteristic polynomial independent of `ℓ` (Mumford §19, Thm 4; boundary with I3) -/

/-- **Leaf I2-Char (Mumford, *Abelian varieties*, §19, Thm 4; locator UNVERIFIED).** For an
endomorphism `φ` of an abelian variety `B` of dimension `g` over a field `k` there is a monic
`P ∈ ℤ[X]` of degree `2g` which, for every prime `ℓ ≠ char k`, is the characteristic polynomial of
`φ` on `T_ℓ B`; finite-level form: reduced mod `ℓⁿ` it is the characteristic polynomial of the
matrix of `φ` on `B(k̄)[ℓⁿ]` in any `ℤ/ℓⁿ`-basis. Used in C10 (the trace of `Frob ∘ μ̄_σ` is one
integer for all `ℓ`). -/
def CharpolyIndependentOfEll : Prop :=
  ∀ (k : Type u) [Field k] (B : Grp (Over (Spec (.of k)))) [IsAbelianVariety B] (g : ℕ),
    topologicalKrullDim B.X.left = (g : WithBot ℕ∞) → ∀ φ : B ⟶ B,
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2 * g ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ : k) ≠ 0 → ∀ n : ℕ, 0 < n →
        ∀ e : torsion B (AlgebraicClosure k) (ℓ ^ n) ≃ (Fin (2 * g) → ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n),
          ∀ h : x.1 * y.1 ∈ torsion B (AlgebraicClosure k) (ℓ ^ n),
            e ⟨x.1 * y.1, h⟩ = e x + e y) →
        ∀ M : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n), y.1 = x.1 ≫ φ.hom.hom →
          e y = M.mulVec (e x)) →
        M.charpoly = P.map (Int.castRingHom (ZMod (ℓ ^ n)))

/-- **Leaf I2-Rank (Mumford, *Abelian varieties*, §19, Thm 3, rank part; boundary with I3;
locator UNVERIFIED).** For abelian varieties `A, B` over `k` of dimensions `g, g'`, the group of
homomorphisms `A → B` has rank at most `4gg'`: any `4gg' + 1` homomorphisms are `ℤ`-linearly
dependent in the (commutative) group `A.X ⟶ B.X`. Used in A8 (`r ≤ 16F₀²`). The instance argument
`IsCommMonObj B.X` holds for every abelian variety (Mathlib,
`isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
def HomRankBound : Prop :=
  ∀ (k : Type u) [Field k] (A B : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    [IsAbelianVariety B] [IsCommMonObj B.X] (g g' : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) →
    topologicalKrullDim B.X.left = (g' : WithBot ℕ∞) →
    ∀ f : Fin (4 * g * g' + 1) → (A ⟶ B),
      ∃ c : Fin (4 * g * g' + 1) → ℤ, c ≠ 0 ∧ ∏ i, (f i).hom.hom ^ c i = 1

/-! ## 9. Glue proved from the leaves -/

section Glue

variable {K : Type u} [Field K]

lemma galAct_mul (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x y : Pts A L) : galAct A σ (x * y) = galAct A σ x * galAct A σ y :=
  MonObj.comp_mul _ _ _

lemma galAct_inv (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : galAct A σ x⁻¹ = (galAct A σ x)⁻¹ :=
  GrpObj.comp_inv _ _

lemma galAct_pow (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) (n : ℕ) : galAct A σ (x ^ n) = (galAct A σ x) ^ n :=
  MonObj.comp_pow _ _ _

lemma galAct_one (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) : galAct A σ 1 = 1 :=
  MonObj.comp_one _

/-- **Glue C6/A8 (proved).** Good reduction at `O` makes inertia act trivially on `A[ℓⁿ]` for
every prime `ℓ` invertible in `O` (NOS, (a) ⇒ (b)): `r_ℓ` is unramified at such places. -/
theorem inertiaTrivial_of_goodReduction (hNOS : NeronOggShafarevich.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (hA : HasGoodReduction A O)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n : ℕ) :
    InertiaTrivialOn A w (ℓ ^ n) :=
  ((hNOS K O w hw A).1.mp hA) (ℓ ^ n) (pow_pos hℓ.pos n) (by
    rw [Nat.cast_pow]; exact hℓO.pow n)

/-- Algebraic core of D2 (proved): in a commutative group of points, if `σ` satisfies
`(σ - 1)² x = 0`, `x` has order dividing `ℓⁿ`, and `σ^{pᵃ} x = x` with `p` prime to `ℓ`,
then `σ x = x`. -/
theorem fixed_of_unipSq_of_iterate (A : Grp (Over (Spec (.of K)))) [IsCommMonObj A.X]
    {L : Type u} [CommRing L] [Algebra K L] (σ : L ≃ₐ[K] L) (x : Pts A L) (ℓ n p a : ℕ)
    (hcop : Nat.Coprime (p ^ a) (ℓ ^ n)) (hx : x ∈ torsion A L (ℓ ^ n))
    (hu : UnipSq A σ x) (hit : (galAct A σ)^[p ^ a] x = x) : galAct A σ x = x := by
  set N := galAct A σ x * x⁻¹ with hN
  have hσN : galAct A σ N = N := by
    rw [hN, galAct_mul, galAct_inv]
    unfold UnipSq at hu
    have h2 : galAct A σ (galAct A σ x) * (galAct A σ x)⁻¹ =
        ((galAct A σ x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, (galAct A σ)^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, galAct_mul, galAct_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (p ^ a) = 1 := by
    have := hiter (p ^ a)
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    have hx' : x ^ (ℓ ^ n) = 1 := hx
    rw [hN, mul_pow, ← galAct_pow, hx', galAct_one, inv_pow, hx']; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **Glue D2 (proved from Raynaud).** At a place of residue characteristic `p` where `A[m]` is
rational (`m ≥ 3` prime to `p`), every inertia element `σ` that acts on a point `x ∈ A[ℓⁿ]`
(`ℓ ≠ p`) with `p`-power order fixes it. Applied to wild inertia (pro-`p`, and the action on the
finite set `A[ℓⁿ]` factors through a finite quotient), this is D2's "wild inertia acts
trivially on `V_ℓ(A)`". The two facts in parentheses are I6/glue. -/
theorem D2_fixed_of_raynaud (hRay : RaynaudCriterion.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ) (hm : 3 ≤ m)
    (hmO : IsUnit (m : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : IsInertia w σ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n p a : ℕ)
    (hcop : Nat.Coprime (p ^ a) (ℓ ^ n))
    (x : Pts A (AlgebraicClosure K)) (hx : x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n))
    (hit : (galAct A σ)^[p ^ a] x = x) : galAct A σ x = x := by
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  exact fixed_of_unipSq_of_iterate A σ x ℓ n p a hcop hx
    (hRay K O w hw A m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx) hit

/-! ## 10. rv-a6-route: A6 (Lemma PR(ii)) by the Raynaud route, from the leaves plus one
pure-algebra glue statement -/

/-- **Glue (pure algebra, not a leaf; to be proved by the project).** Let `G` be a commutative
group whose `3^{2k}`-torsion `T` is isomorphic to `(ℤ/3^{2k})⁴` (`k ≥ 1`), with endomorphisms
`I, J` satisfying `I² = 2`, `J² = -3`, `IJ = -JI` (so `T` is a module over `Λ = ℤ⟨i,j⟩`, whose
`3`-adic completion is the maximal order of the quaternion division algebra over `ℚ₃`), and an
endomorphism `S` commuting with `I, J` with `(S - 1)² = 0` on `T`. Then `S` is the identity on
the `3^k`-torsion. Proof (docs/research/rv-a6-route.md §3): `T/JT` is an `𝔽₉`-space of dimension
1 (dimension 2 would force `J = 3J'` on the free `ℤ/3^{2k}`-module `T`, whence `3·unit = 0`), so
`T` is cyclic, hence free of rank one over `Λ/3^{2k}` by counting; `S - 1` is right
multiplication by some `c` with `c² = 0`, so `v_Π(c) ≥ 2k`, `c ∈ 3^kΛ`, and `S - 1` kills
`3^k T = G[3^k]`. -/
def QuatUnipotentTrivial : Prop :=
  ∀ (G : Type u) [CommGroup G] (k : ℕ), 1 ≤ k → ∀ (I J S : G →* G),
    (∀ x, I (I x) = x ^ 2) → (∀ x, J (J x) * x ^ 3 = 1) → (∀ x, J (I x) * I (J x) = 1) →
    (∀ x, S (I x) = I (S x)) → (∀ x, S (J x) = J (S x)) →
    (∃ e : {x : G | x ^ (3 ^ (2 * k)) = 1} ≃ (Fin (2 * 2) → ZMod (3 ^ (2 * k))),
      ∀ x y : {x : G | x ^ (3 ^ (2 * k)) = 1},
        ∀ h : x.1 * y.1 ∈ {x : G | x ^ (3 ^ (2 * k)) = 1}, e ⟨x.1 * y.1, h⟩ = e x + e y) →
    (∀ x, x ^ (3 ^ (2 * k)) = 1 → S (S x) * (S x)⁻¹ * (S x)⁻¹ * x = 1) →
    ∀ x, x ^ (3 ^ k) = 1 → S x = x

section A6

/-- The Galois action of `σ` as a group endomorphism of `A(L)`. -/
noncomputable def galHomPts (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L]
    [Algebra K L] (σ : L ≃ₐ[K] L) : Pts A L →* Pts A L where
  toFun := galAct A σ
  map_one' := galAct_one A σ
  map_mul' := galAct_mul A σ

/-- A homomorphism of group objects `f : A ⟶ A` as a group endomorphism of `A(L)`. -/
noncomputable def endPts (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L]
    [Algebra K L] (f : A ⟶ A) : Pts A L →* Pts A L where
  toFun x := x ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' x y := MonObj.mul_comp x y _

/-- **Glue A6 (Lemma PR(ii), Raynaud route), proved from the leaves `NeronOggShafarevich`,
`RaynaudCriterion`, `TorsionStructure` and the pure-algebra glue `QuatUnipotentTrivial`.**
Same statement as `PkgI2.goodReduction_of_QM_rational3` (scratch/pkg-I2/I2.lean). -/
theorem goodReduction_of_QM_rational3 (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (hAlg : QuatUnipotentTrivial.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O := by
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  have h3' : IsUnit ((3 : ℕ) : O) := by exact_mod_cast h3
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    apply h3.ne_zero
    apply Subtype.val_injective
    have h' : (3 : K) = 0 := by exact_mod_cast h
    have e3 : ((3 : O) : K) = 3 := rfl
    rw [e3, h']
    rfl
  -- inertia acts trivially on `A[3^k]` for every `k ≥ 1`
  have key : ∀ k : ℕ, 1 ≤ k → InertiaTrivialOn A w (3 ^ k) := by
    intro k hk σ hσ x hx
    obtain ⟨e, he⟩ := hTors K A 2 (3 ^ (2 * k)) hdim (by positivity)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ h3K)
    exact hAlg (Pts A (AlgebraicClosure K)) k hk (endPts A I) (endPts A J) (galHomPts A σ)
      hI hJ hIJ (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      ⟨e, he⟩ (fun y hy => hRay K O w hw A 3 le_rfl h3' hrat σ hσ 3 Nat.prime_three h3'
        (2 * k) y hy) x hx
  -- Néron–Ogg–Shafarevich (c) ⇒ (a)
  refine (hNOS K O w hw A).2.mpr ?_
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 ^ (k + 1)) ?_ ?_
  · intro a b hab
    simpa using (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hab)
  · intro k
    refine ⟨by positivity, ?_, key (k + 1) (by omega)⟩
    rw [Nat.cast_pow]; exact h3'.pow _

end A6

end Glue

end RvA6

#print axioms RvA6.goodReduction_of_QM_rational3

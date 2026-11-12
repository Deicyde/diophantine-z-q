import Mathlib
import ZInQKernel.Hypotheses.JHeight

/-!
# H = `ZInQ.SixContactMin` decomposed into literature leaves and glue (synthesis)

Companion of `docs/research/h-decomposition.md`. Check with
`lake env lean scratch/h-decomposition/Leaves.lean`.

Layout.
* `PkgI2` (copied from the report of the reduction-theory package): genuine Mathlib definitions
  of abelian varieties (`Grp (Over (Spec K))`, proper, smooth, geometrically integral), good
  reduction (abelian schemes over a DVR), torsion points and Galois/inertia actions, and the
  reduction-theory leaves stated over them, with two glue lemmas proved.
* `GlueConductor` (copied from the report on Glazer's conductor bound): the elementary core of
  steps D1-D5, proved; the two different-ideal leaves stated over Mathlib.
* `HSyn` §0-§1: cheap definitions (the absolute Galois group of `ℚ`, places, Frobenius,
  continuous `GL_n(ℚ̄_ℓ)`-representations, cusp forms with nebentypus, normalized eigenforms) and
  the leaves statable over them.
* `HSyn` §2: every other leaf as a **placeholder** `opaque … : Prop`. **A placeholder carries no
  content**: it is an uninterpreted proposition whose docstring records the exact statement and
  reference. A theorem with a placeholder among its hypotheses says nothing until the placeholder
  is replaced by a genuine statement.
* `HSyn` §3: glue proved here, and the top-level theorem from all the leaves to
  `ZInQ.SixContactMin`, through `ZInQ.JHeight.JHeightBound` and the existing Lean proof of the last
  step (`ZInQ.JHeight.sixContactMin_of_jHeightBound`). The glue G1-G19 is `sorry`.

No `axiom` declarations. Leaf numbering (R1-R22 research-level, T1-T25 textbook) is that of the
note's §2.
-/

section PkgI2Sec

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace PkgI2

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

/-- **Glue A6 (Lemma PR(ii), Raynaud route; statement, proof outlined).** Let `A/K` be an
abelian surface with `K`-endomorphisms `I, J` satisfying `I² = 2`, `J² = -3`, `IJ = -JI` on
`K̄`-points (an action of `ℤ⟨i, j⟩ ⊂ B = (2,-3)`, maximal at 3), and with `A[3]` rational over `K`.
Then `A` has good reduction at every DVR `O` in which `3` is invertible.
Outline. (1) `RaynaudCriterion` with `m = ℓ = 3`: `N = σ - 1` has `N² = 0` on `A[3ⁿ]` for `σ` in
inertia. (2) `TorsionStructure` (`g = 2`): `A[3ⁿ] ≅ (ℤ/3ⁿ)⁴`; with the action of `Λ = ℤ⟨i,j⟩`,
whose 3-adic completion is the maximal order of the quaternion division algebra over `ℚ₃`
(uniformizer `Π`, `Π² ∈ 3Λ₃ˣ`, residue field `𝔽₉`), a cardinality count gives `A[3ⁿ] ≅ Λ/3ⁿ`
free of rank one. (3) `N` commutes with `I, J` (defined over `K`), so `N` is right
multiplication by some `c`, and `N² = 0` gives `c² ≡ 0 mod 3^{2k}`, hence `c ∈ 3ᵏΛ` (the norm
form `x² - 2y² + 3z² - 6w²` is anisotropic mod 3), hence `N` kills `3ᵏ A[3^{2k}] = A[3ᵏ]`.
(4) `NeronOggShafarevich` (c) with `m = 3ᵏ`. -/
theorem goodReduction_of_QM_rational3 (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
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
  sorry

end Glue

end PkgI2

end PkgI2Sec

section ConductorBreaksSec

/-!
# glue-conductor: the elementary core of Glazer's uniform conductor bound (D1, D3, D4)

Manuscript `diophantine_zq.tex` L796-851 (h-trust steps D1-D4). Everything here is about
integers and rationals; the ramification data enter as the sequence `g i = |G_i|` of orders
of the lower ramification groups of a finite Galois extension of local fields at one prime
(`g 0 = e`, `g` antitone, `g i ≥ 1`, `g i = 1` for large `i`), as in Serre, *Corps locaux*,
IV §§1-3. The dictionary to the field-theoretic objects is:

* Hilbert's formula: `δ = v_P(𝔇) = ∑_{i ≥ 0} (|G_i| - 1)` (Serre IV §1 Prop. 4);
* Herbrand's function at an integer lower index `m ≥ 0`: `φ(m) = ∑_{i=1}^m |G_i|/|G_0|`
  (Serre IV §3), so the upper index of the lower break `b` is `φ b`;
* `G^u = G_i` for `φ(i-1) < u ≤ φ(i)`, so `∫ (1 - |G^u|⁻¹) du` is the sum of
  `(φ i - φ (i-1)) (1 - 1/|G_i|)`.

No `sorry`.
-/

namespace GlueConductor

open Finset

/-- Herbrand's `φ` at an integer lower index `m`: `φ(m) = ∑_{i=1}^m g_i / g_0`. -/
def phi (g : ℕ → ℕ) (m : ℕ) : ℚ := ∑ i ∈ Icc 1 m, (g i : ℚ) / g 0

/-- The different exponent through Hilbert's formula, truncated at `n`:
`δ = ∑_{i<n} (g_i - 1)` (equal to the full sum once `g i = 1` for `i ≥ n`). -/
def delta (g : ℕ → ℕ) (n : ℕ) : ℚ := ∑ i ∈ range n, ((g i : ℚ) - 1)

lemma phi_zero (g : ℕ → ℕ) : phi g 0 = 0 := by simp [phi]

lemma phi_succ (g : ℕ → ℕ) (m : ℕ) : phi g (m + 1) = phi g m + (g (m + 1) : ℚ) / g 0 := by
  unfold phi
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma phi_mono (g : ℕ → ℕ) {m m' : ℕ} (h : m ≤ m') : phi g m ≤ phi g m' := by
  unfold phi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
  · intro i _ _; positivity

/-- **The Herbrand integral (step-function form).** For `n ≥ 0`,
`δ_{n+1}/e = 1 - 1/e + ∑_{i=1}^n (φ(i) - φ(i-1)) (1 - 1/|G_i|)`, i.e.
`δ/e = 1 - 1/e + ∫₀^∞ (1 - |G^u|⁻¹) du` (N5 L807-808). -/
theorem herbrand_integral (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (n : ℕ) :
    delta g (n + 1) / g 0 =
      1 - 1 / (g 0 : ℚ) + ∑ i ∈ Icc 1 n, (phi g i - phi g (i - 1)) * (1 - 1 / (g i : ℚ)) := by
  have hpos : ∀ i, (0 : ℚ) < g i := fun i => by exact_mod_cast hg i
  induction n with
  | zero =>
    simp only [delta]
    simp
    have := hpos 0
    field_simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    simp only [delta, Finset.sum_range_succ _ (n + 1)]
    rw [show n + 1 - 1 = n by omega, phi_succ]
    have := hpos 0
    have := hpos (n + 1)
    field_simp
    ring

/-- `φ(m) ≤ m` (the slopes of `φ` are at most one), hence `ψ(u) ≥ u`; this is the elementary
half of the subgroup formula `ψ_{F/ℚ₂}(u) ≥ u` (N5 L838-840). -/
theorem phi_le_self (g : ℕ → ℕ) (hg0 : 0 < g 0) (hanti : Antitone g) (m : ℕ) :
    phi g m ≤ m := by
  induction m with
  | zero => simp [phi_zero]
  | succ m ih =>
    rw [phi_succ]
    have h1 : (g (m + 1) : ℚ) ≤ g 0 := by exact_mod_cast hanti (Nat.zero_le _)
    have h2 : (0 : ℚ) < g 0 := by exact_mod_cast hg0
    have : (g (m + 1) : ℚ) / g 0 ≤ 1 := (div_le_one h2).mpr h1
    push_cast; linarith

/-- **D1, break bound.** If `G_i ≠ 1` (i.e. `g i ≥ 2`) for all `i ≤ b`, then the upper index
`φ(b)` of the lower index `b` is at most `2δ/e`: before the last break the integrand
`1 - |G^u|⁻¹` is at least `1/2` (N5 L809-812). Here `δ = δ_n` for any `n > b`. -/
theorem phi_le_two_delta (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (b n : ℕ) (hb : ∀ i ≤ b, 2 ≤ g i)
    (hbn : b < n) : phi g b ≤ 2 * delta g n / g 0 := by
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg 0
  have key : (∑ i ∈ Icc 1 b, (g i : ℚ)) ≤ 2 * delta g n := by
    calc (∑ i ∈ Icc 1 b, (g i : ℚ)) ≤ ∑ i ∈ range (b + 1), (g i : ℚ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega
          · intro i _ _; positivity
      _ ≤ ∑ i ∈ range (b + 1), 2 * ((g i : ℚ) - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have : (2 : ℚ) ≤ g i := by
            exact_mod_cast hb i (by simp only [Finset.mem_range] at hi; omega)
          linarith
      _ = 2 * ∑ i ∈ range (b + 1), ((g i : ℚ) - 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * delta g n := by
          unfold delta
          have : ∑ i ∈ range (b + 1), ((g i : ℚ) - 1) ≤ ∑ i ∈ range n, ((g i : ℚ) - 1) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_subset_range.mpr hbn
            · intro i _ _
              have : (1 : ℚ) ≤ g i := by exact_mod_cast hg i
              linarith
          linarith
  unfold phi
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right key h0.le

/-! ## D1's arithmetic: `δ ≤ e - 1 + e v_p(e)` and `e ≤ a!` give `2δ/e ≤ 4a²` -/

/-- `a! ≤ 2^(a²)`. -/
lemma factorial_le_two_pow_sq (a : ℕ) : a.factorial ≤ 2 ^ (a ^ 2) := by
  calc a.factorial ≤ a ^ a := Nat.factorial_le_pow a
    _ ≤ (2 ^ a) ^ a := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le a
    _ = 2 ^ (a ^ 2) := by rw [← pow_mul, sq]

/-- `v_p(e) ≤ log₂ e`. -/
lemma padicValNat_le_log_two {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    padicValNat p e ≤ Nat.log 2 e := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ padicValNat p e ≤ p ^ padicValNat p e := Nat.pow_le_pow_left hp.two_le _
    _ ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero he) pow_padicValNat_dvd

/-- `1 + log₂(a!) ≤ 2a²` for `a ≥ 1`, the manuscript's `2(1 + log₂ a!) ≤ 4a²`. -/
lemma one_add_log_factorial_le (a : ℕ) (ha : 1 ≤ a) : 1 + Nat.log 2 a.factorial ≤ 2 * a ^ 2 := by
  have h1 : Nat.log 2 a.factorial ≤ a ^ 2 := by
    calc Nat.log 2 a.factorial ≤ Nat.log 2 (2 ^ (a ^ 2)) :=
          Nat.log_mono_right (factorial_le_two_pow_sq a)
      _ = a ^ 2 := Nat.log_pow (by norm_num) _
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  omega

/-- `v_p(e) ≤ a²` when `e ≤ a!`. -/
lemma padicValNat_le_sq {p e a : ℕ} (hp : p.Prime) (he : e ≠ 0) (hea : e ≤ a.factorial) :
    padicValNat p e ≤ a ^ 2 := by
  have := padicValNat_le_log_two hp he
  have h1 : Nat.log 2 e ≤ Nat.log 2 a.factorial := Nat.log_mono_right hea
  have h2 : Nat.log 2 a.factorial ≤ a ^ 2 := by
    calc Nat.log 2 a.factorial ≤ Nat.log 2 (2 ^ (a ^ 2)) :=
          Nat.log_mono_right (factorial_le_two_pow_sq a)
      _ = a ^ 2 := Nat.log_pow (by norm_num) _
  omega

/-- **D1, arithmetic.** If `δ ≤ e - 1 + e·v_p(e)` (Serre's different bound) and `e ≤ a!`
(the normal closure of a degree-`a` extension has degree at most `a!`), then
`2δ ≤ 2(1 + log₂ a!)·e ≤ 4a²·e`. -/
theorem two_delta_le (p e a δ : ℕ) (hp : p.Prime) (he : 1 ≤ e) (ha : 1 ≤ a)
    (hea : e ≤ a.factorial) (hδ : δ ≤ e - 1 + e * padicValNat p e) :
    2 * δ ≤ 2 * (1 + Nat.log 2 a.factorial) * e ∧ 2 * (1 + Nat.log 2 a.factorial) * e ≤ 4 * a ^ 2 * e := by
  have hv : padicValNat p e ≤ Nat.log 2 a.factorial :=
    (padicValNat_le_log_two hp (by omega)).trans (Nat.log_mono_right hea)
  have hl := one_add_log_factorial_le a ha
  constructor
  · have : e * padicValNat p e ≤ e * Nat.log 2 a.factorial := Nat.mul_le_mul_left e hv
    have h2 : e - 1 + e * padicValNat p e ≤ e * (1 + Nat.log 2 a.factorial) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    calc 2 * δ ≤ 2 * (e * (1 + Nat.log 2 a.factorial)) := by omega
      _ = 2 * (1 + Nat.log 2 a.factorial) * e := by ring
  · have : 2 * (1 + Nat.log 2 a.factorial) ≤ 4 * a ^ 2 := by omega
    exact Nat.mul_le_mul_right e this

/-- **D1, combined.** Let `g i = |G_i|` be the lower ramification data of a finite Galois
extension of `ℚ_p`-local fields with `e = g 0 ≤ a!`, let `b` be a lower index with `G_b ≠ 1`
(e.g. the last break), and suppose the different exponent `δ = ∑_{i<n}(g_i - 1)` (Hilbert)
satisfies Serre's bound `δ ≤ e - 1 + e v_p(e)`. Then the upper index of `b` is at most
`4a²`: `u_last ≤ 2δ/e ≤ 4a²` (N5 L796-812). -/
theorem upper_break_le (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (g : ℕ → ℕ) (hanti : Antitone g)
    (hg : ∀ i, 1 ≤ g i) (b n : ℕ) (hb : 2 ≤ g b) (hbn : b < n) (hea : g 0 ≤ a.factorial)
    (hSerre : ∑ i ∈ range n, (g i - 1) ≤ g 0 - 1 + g 0 * padicValNat p (g 0)) :
    phi g b ≤ 4 * a ^ 2 := by
  have hb' : ∀ i ≤ b, 2 ≤ g i := fun i hi => hb.trans (hanti hi)
  have h1 := phi_le_two_delta g hg b n hb' hbn
  have hδ : delta g n = ((∑ i ∈ range n, (g i - 1) : ℕ) : ℚ) := by
    unfold delta
    push_cast [Nat.cast_sub (hg _)]
    rfl
  obtain ⟨h2, h3⟩ := two_delta_le p (g 0) a _ hp (hg 0) ha hea hSerre
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg 0
  have h4 : (2 * delta g n : ℚ) ≤ 4 * a ^ 2 * g 0 := by
    rw [hδ]; exact_mod_cast h2.trans h3
  calc phi g b ≤ 2 * delta g n / g 0 := h1
    _ ≤ 4 * a ^ 2 * g 0 / g 0 := div_le_div_of_nonneg_right h4 h0.le
    _ = 4 * a ^ 2 := by field_simp

/-! ## D4: conductor exponents -/

/-- **D4, Swan term.** For a representation of dimension two through a finite Galois
extension with lower ramification data `g`, the Swan conductor is
`∑_{i ≥ 1} (|G_i|/|G_0|) codim V^{G_i}` (Serre VI §2). If every `G_i` with upper index
`φ(i) > U` acts trivially (`c i = 0`), and `c i ≤ 2`, then `Sw ≤ 2U` (N5 L845-846). -/
theorem swan_le (g : ℕ → ℕ) (hg0 : 0 < g 0) (c : ℕ → ℚ) (U : ℚ) (hU : 0 ≤ U) (n : ℕ)
    (hc2 : ∀ i, c i ≤ 2) (htriv : ∀ i, U < phi g i → c i = 0) :
    ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ 2 * U := by
  classical
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg0
  set s := (Icc 1 n).filter (fun i => phi g i ≤ U) with hs
  have step1 : ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ ∑ i ∈ s, 2 * ((g i : ℚ) / g 0) := by
    rw [hs, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    have hq : (0 : ℚ) ≤ (g i : ℚ) / g 0 := by positivity
    split_ifs with h
    · nlinarith [hc2 i]
    · rw [htriv i (lt_of_not_ge h), mul_zero]
  have step2 : ∑ i ∈ s, (g i : ℚ) / g 0 ≤ U := by
    rcases s.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; exact hU
    · obtain ⟨m, hm, hmax⟩ := s.exists_max_image id hne
      have hsub : s ⊆ Icc 1 m := by
        intro i hi
        have h1 := (Finset.mem_filter.mp hi).1
        simp only [Finset.mem_Icc] at h1 ⊢
        exact ⟨h1.1, hmax i hi⟩
      calc ∑ i ∈ s, (g i : ℚ) / g 0 ≤ ∑ i ∈ Icc 1 m, (g i : ℚ) / g 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        _ = phi g m := rfl
        _ ≤ U := (Finset.mem_filter.mp hm).2
  rw [← Finset.mul_sum] at step1
  linarith

/-- **D4, at `p ≤ R`.** The Artin exponent `a = codim V^I + Sw` of a two-dimensional
representation with `codim V^I ≤ 2` and with every upper group above `U` acting trivially is
at most `2 + 2U`. -/
theorem artin_le (g : ℕ → ℕ) (hg0 : 0 < g 0) (c : ℕ → ℚ) (c0 U : ℚ) (hU : 0 ≤ U) (n : ℕ)
    (hc00 : c0 ≤ 2) (hc2 : ∀ i, c i ≤ 2)
    (htriv : ∀ i, U < phi g i → c i = 0) :
    c0 + ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ 2 + 2 * U := by
  have := swan_le g hg0 c U hU n hc2 htriv
  linarith

/-- **D4, tame primes `p > R`.** If the ramification index `e` is less than `p`, the wild
group `G_1` (a `p`-group whose order divides `e`) is trivial. -/
lemma wild_trivial_of_tame {p e k : ℕ} (he : 0 < e) (hep : e < p)
    (hdvd : p ^ k ∣ e) : p ^ k = 1 := by
  rcases k with _ | k
  · simp
  · exfalso
    have := Nat.le_of_dvd he hdvd
    have : p ≤ p ^ (k + 1) := Nat.le_self_pow (by omega) p
    omega

/-- **D4, tame primes**, continued: if `G_1 = 1` then the Swan term vanishes, so the Artin
exponent is `codim V^I ≤ 2`. -/
theorem swan_eq_zero_of_tame (g : ℕ → ℕ) (hanti : Antitone g) (hg1 : g 1 = 1) (c : ℕ → ℚ)
    (hc : ∀ i, g i = 1 → c i = 0) (n : ℕ) :
    ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have : g i ≤ 1 := hg1 ▸ hanti hi1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h
  · simp [h]
  · simp [hc i h]

/-! ## D2: odd `p`, the character `β` on wild inertia -/

/-- **D2, last sentence.** Let `β : G →* H` be a homomorphism whose values have `p`-power
order, `p` odd (for `G = P_F` pro-`p` and `β` continuous into the finite group `μ_{2m}`, the
image is a finite `p`-group). If `β²` is trivial (`β² = χ` is tame, so trivial on wild
inertia), then `β` is trivial: a pro-`p` group has no quotient of order two (N5 L821-823). -/
theorem char_trivial_of_odd_pgroup {G H : Type*} [Group G] [Group H] (p : ℕ) (hp : p.Prime)
    (hodd : p ≠ 2) (β : G →* H) (himg : ∀ g, ∃ k : ℕ, β g ^ (p ^ k) = 1)
    (hsq : ∀ g, β g ^ 2 = 1) : ∀ g, β g = 1 := by
  intro g
  obtain ⟨k, h1⟩ := himg g
  have hcop : Nat.Coprime 2 (p ^ k) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)
  have h2 : orderOf (β g) ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq g)
  have h3 : orderOf (β g) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have : orderOf (β g) ∣ Nat.gcd 2 (p ^ k) := Nat.dvd_gcd h2 h3
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

/-- The image of a homomorphism from a finite `p`-group has `p`-power-order elements, so
`char_trivial_of_odd_pgroup` applies to `β` restricted to any finite `p`-group quotient. -/
lemma pow_card_eq_one_of_pgroup {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (β : G →* H) (g : G) : ∃ k : ℕ, β g ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hG g
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

/-! ## D2-D4: the constants -/

/-- `G₀ = |GL₄(𝔽₅)|` (the degree of `L_v(A[5])/L_v` is at most this). -/
theorem card_GL4_F5 : Nat.card (GL (Fin 4) (ZMod 5)) = 116064000000 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field (n := 4) (𝔽 := ZMod 5)]
  simp [Fin.prod_univ_four, ZMod.card]

/-- `|GL₄(𝔽₃)| = 24261120 ≤ G₀` (the degree of `L_v(A[3])/L_v`). -/
theorem card_GL4_F3 : Nat.card (GL (Fin 4) (ZMod 3)) = 24261120 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field (n := 4) (𝔽 := ZMod 3)]
  simp [Fin.prod_univ_four, ZMod.card]

/-- The subgroup-formula threshold at `p = 2`: `max(4D², 3e) ≤ U₀ = 4(D G₀)²` when
`e ≤ D` and `G₀ ≥ 1` (N5 L841-842). -/
theorem max_le_U0 (D G0 e : ℕ) (hD : 1 ≤ D) (hG : 1 ≤ G0) (he : e ≤ D) :
    max (4 * D ^ 2) (3 * e) ≤ 4 * (D * G0) ^ 2 := by
  have h1 : D ^ 2 ≤ (D * G0) ^ 2 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right D hG) 2
  have h2 : 3 * e ≤ 4 * D ^ 2 := by nlinarith
  omega

/-- `2 + 2U₀ ≤ E₀`, with `U₀ = 4(DG₀)²` and `E₀ = 10(DG₀)²` (N5 L845-846). -/
theorem two_add_two_U0_le_E0 (D G0 : ℕ) (hD : 1 ≤ D) (hG : 1 ≤ G0) :
    2 + 2 * (4 * (D * G0) ^ 2) ≤ 10 * (D * G0) ^ 2 := by
  have : 1 ≤ (D * G0) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hD hG)
  omega


/-! ## D1 over genuine definitions (Mathlib's rings of integers, inertia and different)

For a Galois number field `L/ℚ` and a prime `P` of `𝓞 L`, the lower ramification groups are
`G_i = {σ ∈ Gal(L/ℚ) | ∀ x ∈ 𝓞 L, σ x - x ∈ P^(i+1)}`, i.e. Mathlib's `Ideal.inertia` of
`P^(i+1)`; `G_0` is Mathlib's inertia group. (Serre, *Corps locaux*, IV §1 defines them for the
completion; they agree with these, Serre I §7 and IV §1, UNVERIFIED locators.) The two leaves
below are published theorems (local statements transported to number fields by completion). -/

open NumberField

/-- The lower ramification group `G_i` of `P` in `Gal(L/ℚ)`. -/
abbrev ramGroup (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) :
    Subgroup Gal(L/ℚ) :=
  (P ^ (i + 1)).inertia Gal(L/ℚ)

/-- `|G_i|`. -/
noncomputable abbrev ramCard (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) : ℕ :=
  Nat.card (ramGroup L P i)

/-- **Leaf (Hilbert's different formula; Serre, *Corps locaux*, IV §1, Prop. 4, with `G_i = 1`
for large `i`, IV §1; UNVERIFIED numbering).** For a Galois number field `L` and a nonzero prime
`P` of `𝓞 L`, some `G_n` is trivial and the exact power of `P` in the different of `𝓞 L/ℤ` is
`∑_{i<n} (|G_i| - 1)`. -/
def HilbertDifferentFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
    ∃ n, ramGroup L P n = ⊥ ∧
      P ^ (∑ i ∈ range n, (ramCard L P i - 1)) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (∑ i ∈ range n, (ramCard L P i - 1) + 1) ∣ differentIdeal ℤ (𝓞 L)

/-- **Leaf (Serre's bound for the different; Serre, *Corps locaux*, III §6, remark after
Prop. 13: `v_L(𝔇_{L/K}) ≤ e - 1 + v_L(e)`; UNVERIFIED numbering).** At `K = ℚ_p`,
`v_L(e) = e·v_p(e)`. Stated for any number field `L` and prime `P | p` of `𝓞 L`. -/
def SerreDifferentBound : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)

instance spanNatPrime_isPrime (p : ℕ) [hp : Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp.out)

/-- **D1 over genuine definitions.** From the two leaves: for a Galois number field `L`, a prime
`P | p` with ramification index `e ≤ a!` and a lower index `b` with `G_b ≠ 1`, the upper index
`φ(b)` (Herbrand's function of the genuine `|G_i|`) is at most `4a²`. -/
theorem D1_genuine (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ) [hpF : Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [hPl : P.LiesOver (Ideal.span {(p : ℤ)})]
    (a : ℕ) (ha : 1 ≤ a) (hea : P.ramificationIdx ℤ ≤ a.factorial)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 := by
  have hp : p.Prime := hpF.out
  have hP0 : P ≠ ⊥ := by
    intro h
    have := hPl.over
    rw [h, Ideal.under_bot] at this
    have h2 := Ideal.span_singleton_eq_bot.mp this
    simp [hp.ne_zero] at h2
  set g := ramCard L P with hg_def
  have hanti : Antitone g := by
    intro i j hij
    apply Subgroup.card_le_of_le
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have hg1 : ∀ i, 1 ≤ g i := fun i => Nat.card_pos
  have hgb : 2 ≤ g b := by
    have h1 := hg1 b
    have h2 : g b ≠ 1 := fun h => hb (Subgroup.card_eq_one.mp h)
    omega
  obtain ⟨n, hn, hdvd, -⟩ := hH L P hP0
  have hbn : b < n := by
    by_contra h
    apply hb
    rw [eq_bot_iff, ← hn]
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have he : g 0 = P.ramificationIdx ℤ := by
    show Nat.card ((P ^ (0 + 1)).inertia Gal(L/ℚ)) = _
    rw [zero_add, pow_one, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(p : ℤ)}) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ)]
  have hSer := hS L p hp P hPl
  have hsum : ∑ i ∈ range n, (g i - 1) ≤ g 0 - 1 + g 0 * padicValNat p (g 0) := by
    rw [he]
    by_contra hlt
    push Not at hlt
    exact hSer (dvd_trans (pow_dvd_pow P hlt) hdvd)
  exact upper_break_le p a hp ha g hanti hg1 b n hgb hbn (he ▸ hea) hsum

end GlueConductor



end ConductorBreaksSec

section ConductorDyadicSec

/-!
# glue-conductor: the dyadic unit step of D3 (N5 L828-832)

N5: "the logarithm for `Ĝ_m` identifies `U_F^{e+1}` with `𝔪_F^{e+1}` since `e+1 > e`
[Silverman IV.6.4]. Multiplication by four gives `(U_F^{e+1})^4 = U_F^{3e+1}`."

The direction used is `U_F^{3e+1} ⊆ (U_F^{e+1})^4` (so that `β⁴ = 1` on `U_F` forces `β = 1` on
`U_F^{3e+1}`). We prove both directions for any complete discrete valuation ring `A` with
`v(2) = e`, i.e. `(2) = 𝔪^e`, with no logarithm: a square root of `1 + z`, `z ∈ 𝔪^{2e+s}`,
`s ≥ 1`, is `1 + 2u` with `u² + u = z/4`, a simple root by Hensel's lemma (Mathlib's
`IsAdicComplete.henselianRing`). The ring of integers of a finite extension `F/ℚ₂` with
absolute ramification index `e` satisfies the hypotheses. No `sorry`.
-/

namespace GlueConductor

open IsLocalRing Polynomial

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Square roots near one: if `(2) = 𝔪^e`, `z ∈ 𝔪^{2e+s}` and `s ≥ 1`, then `1 + z = (1 + w)²`
for some `w ∈ 𝔪^{e+s}`. -/
theorem exists_sq_eq_one_add [IsAdicComplete (maximalIdeal A) A] (e s : ℕ) (hs : 1 ≤ s)
    (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (z : A)
    (hz : z ∈ maximalIdeal A ^ (2 * e + s)) :
    ∃ w ∈ maximalIdeal A ^ (e + s), (1 + w) ^ 2 = 1 + z := by
  set m := maximalIdeal A
  -- z = 4c with c ∈ 𝔪^s
  have h4 : m ^ (2 * e + s) = Ideal.span {(4 : A)} * m ^ s := by
    rw [pow_add, two_mul, pow_add, ← h2, Ideal.span_singleton_mul_span_singleton]
    norm_num
  rw [h4, Ideal.mem_span_singleton_mul] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  have hcm : c ∈ m := Ideal.pow_le_self (by omega) hc
  -- Hensel: u² + u = c
  let f : A[X] := X ^ 2 + (X - C c)
  have hmon : f.Monic :=
    (monic_X_pow 2).add_of_left (by rw [degree_X_sub_C, degree_X_pow]; norm_num)
  have heval0 : f.eval 0 ∈ m := by
    simp [f, hcm]
  have hder : IsUnit (Ideal.Quotient.mk m (f.derivative.eval 0)) := by
    simp [f]
  obtain ⟨u, hu, hu0⟩ := HenselianRing.is_henselian f hmon 0 heval0 hder
  rw [sub_zero] at hu0
  have hroot : u ^ 2 + u = c := by
    have := hu.eq_zero
    simp only [f, eval_sub, eval_add, eval_pow, eval_X, eval_C] at this
    linear_combination this
  -- u ∈ 𝔪^s, since u (u + 1) = c and u + 1 is a unit
  have hunit : IsUnit (u + 1) := by
    by_contra h
    have h1 : u + 1 ∈ m := (mem_maximalIdeal _).mpr h
    have : (1 : A) ∈ m := by simpa using sub_mem h1 hu0
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hus : u ∈ m ^ s := by
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have : u = c * v := by
      calc u = u * ((u + 1) * v) := by rw [hv, mul_one]
        _ = (u ^ 2 + u) * v := by ring
        _ = c * v := by rw [hroot]
    rw [this]
    exact Ideal.mul_mem_right _ _ hc
  refine ⟨2 * u, ?_, ?_⟩
  · rw [pow_add, ← h2]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self 2) hus
  · calc (1 + 2 * u) ^ 2 = 1 + 4 * (u ^ 2 + u) := by ring
      _ = 1 + 4 * c := by rw [hroot]

/-- **D3, `U^{3e+1} ⊆ (U^{e+1})⁴`.** In a complete DVR (complete local ring) with `(2) = 𝔪^e`,
every `y ∈ 1 + 𝔪^{3e+1}` is a fourth power of some `x ∈ 1 + 𝔪^{e+1}`. -/
theorem exists_fourth_root [IsAdicComplete (maximalIdeal A) A] (e : ℕ)
    (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (z : A)
    (hz : z ∈ maximalIdeal A ^ (3 * e + 1)) :
    ∃ w ∈ maximalIdeal A ^ (e + 1), (1 + w) ^ 4 = 1 + z := by
  obtain ⟨w₁, hw₁, h₁⟩ := exists_sq_eq_one_add e (e + 1) (by omega) h2 z
    (by rwa [show 2 * e + (e + 1) = 3 * e + 1 by ring])
  obtain ⟨w, hw, h⟩ := exists_sq_eq_one_add e 1 le_rfl h2 w₁
    (by rwa [show 2 * e + 1 = e + (e + 1) by ring])
  exact ⟨w, hw, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, h₁]⟩

/-- **D3, `(U^{e+1})⁴ ⊆ U^{3e+1}`** (the easy direction; no completeness needed). -/
theorem fourth_pow_mem (e : ℕ) (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (w : A)
    (hw : w ∈ maximalIdeal A ^ (e + 1)) :
    (1 + w) ^ 4 - 1 ∈ maximalIdeal A ^ (3 * e + 1) := by
  set m := maximalIdeal A
  have h2m : (2 : A) ∈ m ^ e := h2 ▸ Ideal.mem_span_singleton_self 2
  have hexp : (1 + w) ^ 4 - 1 = 2 * 2 * w + 2 * (3 * w * w) + 2 * 2 * (w * w * w) + w * w * w * w := by
    ring
  rw [hexp]
  have hww : w * w ∈ m ^ (2 * e + 2) := by
    rw [show 2 * e + 2 = (e + 1) + (e + 1) by ring, pow_add]; exact Ideal.mul_mem_mul hw hw
  have h22 : 2 * 2 ∈ m ^ (2 * e) := by rw [two_mul, pow_add]; exact Ideal.mul_mem_mul h2m h2m
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_
  · rw [show 3 * e + 1 = 2 * e + (e + 1) by ring, pow_add]; exact Ideal.mul_mem_mul h22 hw
  · have : 3 * w * w ∈ m ^ (2 * e + 2) := by
      rw [mul_assoc]; exact Ideal.mul_mem_left _ _ hww
    have h' := Ideal.mul_mem_mul h2m this
    rw [← pow_add] at h'
    exact Ideal.pow_le_pow_right (by omega) h'
  · have hwww : w * w * w ∈ m ^ (3 * e + 3) := by
      rw [show 3 * e + 3 = (2 * e + 2) + (e + 1) by ring, pow_add]
      exact Ideal.mul_mem_mul hww hw
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) hwww)
  · have : w * w * w * w ∈ m ^ (4 * e + 4) := by
      rw [show 4 * e + 4 = (2 * e + 2) + (2 * e + 2) by ring, pow_add, mul_assoc]
      exact Ideal.mul_mem_mul hww hww
    exact Ideal.pow_le_pow_right (by omega) this

end GlueConductor


end ConductorDyadicSec

section ConductorLevelSec

/-!
# glue-conductor: the level product `N ≤ Q_R M²` (h-trust D4-D5, N5 L846-857)

Over the repository's own definitions (`ZInQ.heightE0`, `ZInQ.heightQ`,
`ZInQ.contactSupport`). The conductor exponents `a_p = v_p(N)` (Carayol's Théorème A turns the
conductor exponents of `r₅` (and of `r₃` at `p = 5`) into the exponents of the level `N`) enter
through `N.factorization`. Hypotheses, as in N5:

* `a_p ≤ E₀` at primes `p ≤ R` (D4, first case);
* at primes `p > R`, `a_p ≤ 2` (D4, tame case), and `a_p = 0` unless `p ∈ T = S ∪ supp M_S(u)`
  (D4, third case: outside `T`, `L` is unramified, `A` has good reduction and `β` is unramified).

Since `max S ≤ R`, a prime `p > R` with `a_p > 0` divides `M = M_S(u)`, a product of distinct
primes, so the large part of `N` is at most `M²`; the small part is at most
`(∏_{p ≤ R} p)^{E₀} ≤ R^{R E₀} = Q_R`. No `sorry`.
-/

namespace GlueConductor

open ZInQ

/-- `M_S(u) > 0`. -/
lemma contactSupport_pos' (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  classical
  unfold contactSupport
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- `∏_{p prime, p ≤ R} p^E ≤ R^(R E)` for real `R ≥ 1`, over any finset of primes `≤ R`. -/
lemma prod_small_le (R : ℝ) (hR : 1 ≤ R) (E : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ R) :
    ∏ p ∈ s, (p : ℝ) ^ E ≤ R ^ (R * E) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hcard : (s.card : ℝ) ≤ R := by
    have hsub : s ⊆ Finset.Icc 1 ⌊R⌋₊ := by
      intro p hp
      obtain ⟨hpp, hpR⟩ := hs p hp
      simp only [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, Nat.le_floor hpR⟩
    have h1 : s.card ≤ ⌊R⌋₊ := by
      simpa using Finset.card_le_card hsub
    calc (s.card : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast h1
      _ ≤ R := Nat.floor_le hR0
  calc ∏ p ∈ s, (p : ℝ) ^ E = (∏ p ∈ s, (p : ℝ)) ^ E := by rw [Finset.prod_pow]
    _ ≤ (R ^ s.card) ^ E := by
        apply pow_le_pow_left₀ (Finset.prod_nonneg fun p _ => by positivity)
        calc ∏ p ∈ s, (p : ℝ) ≤ ∏ _p ∈ s, R :=
              Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hp => (hs p hp).2)
          _ = R ^ s.card := Finset.prod_const R
    _ = R ^ ((s.card : ℝ) * E) := by
        rw [Real.rpow_mul hR0, Real.rpow_natCast, Real.rpow_natCast]
    _ ≤ R ^ (R * E) := by
        apply Real.rpow_le_rpow_of_exponent_le hR
        exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **D5's product (N5 L852-857).** Let `N ≥ 1` have exponents `a_p = v_p(N)` with `a_p ≤ E₀`
at `p ≤ R`, and, at `p > R`, `a_p ≤ 2` and `a_p = 0` unless `p ∈ S` or `p ∣ M_S(u)`. If every
prime of `S` is at most `R` and `R ≥ 1`, then `N ≤ Q_R · M_S(u)²`. -/
theorem level_le (S : Finset ℕ) (u : ℚ) (R : ℝ) (hR : 1 ≤ R) (hS : ∀ p ∈ S, (p : ℝ) ≤ R)
    (N : ℕ) (hN : N ≠ 0)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ R → N.factorization p ≤ heightE0)
    (hlarge : ∀ p : ℕ, p.Prime → R < p → N.factorization p ≤ 2)
    (houtside : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S ∨ p ∣ contactSupport S u) :
    (N : ℝ) ≤ heightQ R * (contactSupport S u : ℝ) ^ 2 := by
  classical
  set M := contactSupport S u
  have hM : 0 < M := contactSupport_pos' S u
  have hN' : (N : ℝ) = ∏ p ∈ N.primeFactors, (p : ℝ) ^ (N.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hN]
    push_cast
    rfl
  rw [hN', ← Finset.prod_filter_mul_prod_filter_not N.primeFactors (fun p : ℕ => (p : ℝ) ≤ R)]
  set sm := N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R)
  set lg := N.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ R)
  -- small primes
  have h1 : ∏ p ∈ sm, (p : ℝ) ^ (N.factorization p) ≤ heightQ R := by
    calc ∏ p ∈ sm, (p : ℝ) ^ (N.factorization p) ≤ ∏ p ∈ sm, (p : ℝ) ^ heightE0 := by
          apply Finset.prod_le_prod₀ (fun p _ => by positivity)
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          have hpp := Nat.prime_of_mem_primeFactors hpN
          exact pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le) (hsmall p hpp hpR)
      _ ≤ R ^ (R * heightE0) := by
          apply prod_small_le R hR heightE0 sm
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          exact ⟨Nat.prime_of_mem_primeFactors hpN, hpR⟩
      _ = heightQ R := rfl
  -- large primes
  have h2 : ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p) ≤ (M : ℝ) ^ 2 := by
    have hdvd : (∏ p ∈ lg, p) ∣ M := by
      apply Finset.prod_primes_dvd
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
      · intro p hp
        obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
        have hpp := Nat.prime_of_mem_primeFactors hpN
        rcases houtside p hpp (Nat.dvd_of_mem_primeFactors hpN) with h | h
        · exact absurd (hS p h) hpR
        · exact h
    have hle : (∏ p ∈ lg, p) ≤ M := Nat.le_of_dvd hM hdvd
    calc ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p) ≤ ∏ p ∈ lg, (p : ℝ) ^ 2 := by
          apply Finset.prod_le_prod₀ (fun p _ => by positivity)
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          have hpp := Nat.prime_of_mem_primeFactors hpN
          exact pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le)
            (hlarge p hpp (lt_of_not_ge hpR))
      _ = ((∏ p ∈ lg, p : ℕ) : ℝ) ^ 2 := by push_cast; rw [Finset.prod_pow]
      _ ≤ (M : ℝ) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact_mod_cast hle
  have hQ : 0 ≤ heightQ R := Real.rpow_nonneg (by linarith) _
  calc (∏ p ∈ sm, (p : ℝ) ^ (N.factorization p)) * ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p)
      ≤ heightQ R * (M : ℝ) ^ 2 :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun p _ => by positivity) hQ

end GlueConductor


end ConductorLevelSec

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

/-- **R1. Shimura–Deligne: canonical model and moduli interpretation of the level-3 QM curve.**
`B = (2,−3)/ℚ`, `𝒪` maximal, `μ = 2j + ij`, `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`. (a) The functor on
`ℚ`-schemes of `(A, ι, λ, η)` (abelian scheme of relative dimension 2, `ι : 𝒪 → End A`, principal
polarization with Rosati involution `a ↦ μ⁻¹āμ`, `𝒪`-linear `η : 𝒪/3𝒪 ≅ A[3]`) is represented by
a smooth projective curve `Y₃/ℚ`; (b) complex uniformization compatible with the universal
family; (c) the finite-adelic normalizer acts over `ℚ`; (d) Shimura reciprocity at CM points.
Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21,
Cor. 5.7, Ex. 5.8, §§4.8-4.17; Kottwitz, JAMS 5 (1992), §5 (UNVERIFIED). Consequence (the PEL
theorem specialized to this datum). Missing: abelian schemes over a base with PEL structure,
moduli functors, representability (very large). -/
opaque R01_ShimuraDeligne : Prop

/-- **R2. Baba–Granath.** `X₆/W ≅ P¹_j`, branched over `0, ∞, −16/27` with indices 4, 6, 2 at the
CM points of discriminants −4, −3, −24; two QM surfaces with principal polarization of the fixed
type have the same polarized moduli point iff their points of `X₆` are `W`-conjugate. Canad. J.
Math. 60 (2008), Thm 2.1, Lemma 3.1 (journal numbering UNVERIFIED; 2005 preprint read by a model).
Exact. Missing: `X₆` and its Atkin–Lehner group (very large, via R1). -/
opaque R02_BabaGranath : Prop

/-- **R3. Lin–Yang.** On the finite nonzero `j`-locus the QM surface over `j` is the Jacobian of a
genus-2 curve with `[J₂ : J₄ : J₆ : J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`.
Math. Z. 295 (2020), Example 30, eqs. (13)-(14) (VERIFIED in arXiv v1 by a repository note;
journal numbering UNVERIFIED). Exact. Missing: the QM locus (very large). -/
opaque R03_LinYang : Prop

/-- **R4. Igusa: `ψ₄`, `χ₁₀` in theta constants.** `ψ₄ = 2⁻² Σ_{m even} θ_m⁸`,
`χ₁₀ = −2⁻¹⁴ Π_{m even} θ_m²`, with the conversion to `J₂, …, J₁₀`. Amer. J. Math. 89 (1967),
pp. 833-834, 848 (UNVERIFIED). Exact. Missing: theta constants with characteristics on `𝔥₂`,
Siegel modular forms of degree 2 (large). -/
opaque R04_IgusaTheta : Prop

/-- **R5. González–Rotger.** For an order `R` of conductor `f`, `(f,6) = 1`, in an imaginary
quadratic `k` embeddable in `𝒪`, `#CM(R) = h(R)` on `X₆` and `ℚ(x)` is the ring class field `H_R`
or has index 2 in it (according as some prime dividing 6 is inert in `k` or not). J. Math. Soc.
Japan 58 (2006), Thm 5.12, Prop. 5.6 (VERIFIED in arXiv:math/0612732 by a repository note;
journal numbering UNVERIFIED). Exact. Missing: as R2. -/
opaque R05_GonzalezRotger : Prop

/-- **R8. Grothendieck's semistable reduction theorem** (Néron-model form). An abelian variety over
the fraction field of a henselian DVR acquires semistable reduction over a finite extension. SGA 7
I, Exp. IX, Thm 3.6 (UNVERIFIED). Exact. Needed only on the reviewed route for A6 (Lemma PR(ii));
the Raynaud route of the reduction-theory report avoids it. Missing: Néron models (large). The
Galois consequence is stated as `PkgI2.GrothendieckMonodromy`. -/
opaque R08_SemistableReduction : Prop

/-- **R9. Faltings 1983, Satz 3, Satz 4, Korollar 1.** For abelian varieties `A, B` over a number
field `F`: `V_ℓ(A)` is a semisimple `G_F`-module and
`Hom_F(A, B) ⊗ ℚ_ℓ ≅ Hom_{G_F}(V_ℓA, V_ℓB)`. Invent. Math. 73 (1983), pp. 360-361 (read by a
model). Exact. Missing: Tate modules `V_ℓ` with Galois action, Hom groups (medium). -/
opaque R09_FaltingsTate : Prop

/-- **R10. de Rham comparison.** For `F/ℚ_ℓ` finite and `A/F` an abelian variety of dimension `g`,
`H¹_et(A_F̄, ℚ_ℓ)` is de Rham with `D_dR ≅ H¹_dR(A/F)`; hence `V_ℓ(A)` is de Rham with Hodge–Tate
weights `0, −1`, each of multiplicity `g`. Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 with
Thms 9.1, 9.3, corrigendum 2016; or Faltings 1989, Tsuji 1999 (UNVERIFIED). Exact (first clause).
Missing: `B_dR` with Galois action and filtration, de Rham representations (large). -/
opaque R10_DeRhamComparison : Prop

/-- **R11. Berger's p-adic monodromy theorem.** A de Rham representation of `G_K`, `K/ℚ_p` finite,
is potentially semistable. Invent. Math. 148 (2002), Thm 0.7 = Cor. 5.22 (read by a model).
Exact. Missing: `B_st`, potentially semistable representations (very large). -/
opaque R11_Berger : Prop

/-- **R12. Pan's Fontaine–Mazur theorem.** For an odd prime `p` and a continuous irreducible
`ρ : G_ℚ → GL₂(ℚ̄_p)`, ramified at finitely many primes, potentially semistable at `p`, odd, with
distinct Hodge–Tate weights (and, if `p = 3`, the residual clause): there are a normalized
eigenform `g` and a continuous character `ψ` with `tr ρ(Frob_v) = ψ(Frob_v)·ι(a_v(g))` for almost
all `v` (the trace reading of "comes from a cuspidal eigenform up to twist", implied by every
reading in the literature). JAMS 35 (2022), Thm 1.0.4 (arXiv v2 statement VERIFIED by a
repository note; JAMS numbering UNVERIFIED). Consequence. Expressible now except "potentially
semistable" (very large) and "Hodge–Tate weights" (large). -/
opaque R12_Pan : Prop

/-- **R13. Hodge–Tate weights of eigenform representations at every level.** For a normalized
eigenform `g` of weight `k ≥ 2`, any level and nebentypus, `ρ_{g,ι}` (Tate normalization) is
Hodge–Tate at `ℓ` with weights `{0, 1−k}`. Saito, Invent. Math. 129 (1997); or Kato, Astérisque
295 (2004), §9.4; or Scholl 1990 with R10 and T23 (UNVERIFIED). Consequence (normalization).
Missing: Hodge–Tate representations (large). -/
opaque R13_EigenformHT : Prop

/-- **R16. Eichler–Shimura in `J₁(N)`.** For a weight-2 newform `f` of level `N`,
`V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` has a `G_ℚ`-stable two-dimensional subquotient on which
`tr(Frob_p) = ι(a_p(f))` for `p ∤ Nℓ`. Shimura 1971, Thm 7.9, §7; Shimura, J. Math. Soc. Japan 25
(1973), Thm 1 (UNVERIFIED). Consequence. Missing: `X₁(N)`, `J₁(N)` over `ℚ` (very large). -/
opaque R16_EichlerShimuraJ1 : Prop

/-- **R17. Carayol's local–global compatibility.** For a weight-2 newform of level `N` and `p ≠ ℓ`,
the Artin conductor exponent of `ρ_{f,λ}|G_{ℚ_p}` is `v_p(N)`. Ann. Sci. ÉNS 19 (1986),
Théorème (A) (UNVERIFIED; that it covers `F = ℚ` at `p | N` is an open check). Consequence.
Missing: conductors of ℓ-adic representations, newforms (medium). -/
opaque R17_Carayol : Prop

/-- **R18. Javanpeykar.** A smooth projective connected curve `X/ℚ̄` of genus `g ≥ 1` with a Belyi
map of degree `d` has `h_F(Jac X) ≤ 13·10⁶ · g · d⁵`. Algebra Number Theory 8 (2014), Thm 1.1.1
(read by a model). Exact. Missing: Faltings height (very large), Belyi maps, Jacobians. -/
opaque R18_Javanpeykar : Prop

/-- **R19. Gaudron–Rémond isogeny theorem.** Isogenous abelian varieties `A, B` of dimension `g`
over a number field `K` admit an isogeny `A → B` of degree at most
`((14g)^{64g²}[K:ℚ] max(h_F(A), log[K:ℚ], 1)²)^{1024g³}`. Duke Math. J. 163 (2014), Thm 1.4 (read
by a model). Exact. Missing: Faltings height (very large). -/
opaque R19_GaudronRemond : Prop

/-- **R20. Faltings' height lemma.** For an isogeny `φ : A → B` over a number field,
`|h_F(A) − h_F(B)| ≤ ½ log deg φ`. Faltings 1983, Lemma 5; Raynaud, Astérisque 127 (1985),
Exp. VII, Cor. 2.1.3 (UNVERIFIED). Exact. Missing: Faltings height. -/
opaque R20_FaltingsHeightLemma : Prop

/-- **R21. Bost's lower bound.** `h_F(A) ≥ −(3/2)·dim A` (Bost: `≥ −log(π√2)·dim A`). Bost,
Sém. Bourbaki 795 (1996), as recorded in Gaudron–Rémond 2014, §9 (read by a model). Consequence.
Missing: Faltings height. -/
opaque R21_Bost : Prop

/-- **R22. Pazuki.** For a principally polarized abelian surface over a number field,
`h_Θ(A) ≤ ½X_D + C₂ log(X_D + 2)`, `X_D = max(1, h_F(A) + log π)`, `C₂ = 1000·2⁴(log 2⁴)⁵`,
`h_Θ` the height of the level-2 theta constants. Bull. Soc. Math. France 140 (2012), Cor. 1.3(2)
(read by a model). Exact. Missing: Faltings height, theta constants. -/
opaque R22_Pazuki : Prop

/-- **T8. Poincaré reducibility** (Mumford, *Abelian varieties*, §19 Thm 1, UNVERIFIED). Missing:
abelian subvarieties and isogenies (medium). -/
opaque T08_Poincare : Prop

/-- **T9. Weil pairing.** The Weil pairing of a polarization is Galois-equivariant with values in
`ℤ_ℓ(1)`, so `G_K` acts on `V_ℓ(A)` through `GSp` with cyclotomic multiplier (Mumford §§20, 23,
UNVERIFIED). Missing: polarizations, Tate modules (medium). -/
opaque T09_WeilPairing : Prop

/-- **T10. `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨`**, Galois-equivariantly (Milne in Cornell–Silverman 1986,
Thm 15.1(a), UNVERIFIED). Missing: ℓ-adic étale cohomology (large). -/
opaque T10_TateDuality : Prop

/-- **T11. Riemann's theorem, GAGA, rigidity.** `End⁰(A_ℂ)` is the algebra of endomorphisms of
the rational Hodge structure `H₁(A(ℂ), ℚ)`, and `Hom(A, B) = Hom(A_ℂ, B_ℂ)` over `ℚ̄` (Mumford
§§1-3; Serre 1956; Conrad 2006, §3; UNVERIFIED). Missing: analytification (large). -/
opaque T11_RiemannGAGA : Prop

/-- **T12. Artin comparison.** `V_ℓ(A) ≅ H₁(A(ℂ), ℚ) ⊗ ℚ_ℓ`, compatibly with complex conjugation
(SGA 4 XI 4.4, UNVERIFIED; elementary for abelian varieties via `ℂ²/Λ`). Missing: as T11. -/
opaque T12_ArtinComparison : Prop

/-- **T15. `H²(G_ℚ, ±1) ≅ Br(ℚ)[2]`**, compatibly with restriction to `G_{ℚ_v}` (Milne, *ADT*,
Ch. I; Tate in Cassels–Fröhlich VII; UNVERIFIED). Missing: crossed products, local invariants
(medium; Tau Ceti has the local-global sequence). -/
opaque T15_BrauerCohomology : Prop

/-- **T16. Local class field theory** for finite extensions of `ℚ_p`: the local Artin map, its
compatibility with norms, the upper numbering theorem (Serre, *Local fields*; UNVERIFIED). Missing:
local Artin map (medium; Tau Ceti). -/
opaque T16_LocalCFT : Prop

/-- **T22. Upper numbering and conductors.** Herbrand's theorem, the subgroup formula
`G^u ∩ H = H^{ψ(u)}` for absolute groups, Artin and Swan conductors of a representation with
finite wild image (Serre, *Corps locaux*, IV §§1-3, VI §2; UNVERIFIED). Missing: upper numbering
on `G_{ℚ_p}`, conductors of ℓ-adic representations (medium; Tau Ceti has finite levels). -/
opaque T22_UpperNumbering : Prop

/-- **T23. Fontaine's closure properties.** de Rham representations are closed under duals,
tensor products, sums and subquotients (Astérisque 223 (1994), Thm 3.8, UNVERIFIED). Missing: as
R10 (large). -/
opaque T23_FontaineClosure : Prop

/-- **T25. Newforms** (Atkin–Lehner–Li; Li, Math. Ann. 212 (1975), Thm 5; UNVERIFIED): each system
of Hecke eigenvalues of a normalized eigenform away from the level is that of a unique newform of
level dividing it; Galois conjugates of newforms are newforms. Missing: old space and newforms
(medium; Tau Ceti). -/
opaque T25_Newforms : Prop

/-! ## §3. Glue -/

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization; from the hdec-faithful draft). -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **The research-level leaves of route P** (note §2.1), bundled. Placeholders are uninterpreted.
`R6`, `R7` are the reduction-theory report's genuine statements; `R14`, `R15` are stated over §0. -/
structure ResearchLeaves : Prop where
  r1 : R01_ShimuraDeligne
  r2 : R02_BabaGranath
  r3 : R03_LinYang
  r4 : R04_IgusaTheta
  r5 : R05_GonzalezRotger
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : R08_SemistableReduction
  r9 : R09_FaltingsTate
  r10 : R10_DeRhamComparison
  r11 : R11_Berger
  r12 : R12_Pan
  r13 : R13_EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  r16 : R16_EichlerShimuraJ1
  r17 : R17_Carayol
  r18 : R18_Javanpeykar
  r19 : R19_GaudronRemond
  r20 : R20_FaltingsHeightLemma
  r21 : R21_Bost
  r22 : R22_Pazuki

/-- **The textbook foundations** (note §2.2), bundled. -/
structure TextbookLeaves : Prop where
  t1 : PkgI2.PurityBranchLocus.{0}
  t2 : PkgI2.AbhyankarDVR.{0}
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI2.HomRankBound.{0}
  t7 : PkgI2.CharpolyIndependentOfEll.{0}
  t8 : T08_Poincare
  t9 : T09_WeilPairing
  t10 : T10_TateDuality
  t11 : T11_RiemannGAGA
  t12 : T12_ArtinComparison
  t13 : SkolemNoether
  t14 : HasseBrauerQ
  t15 : T15_BrauerCohomology
  t16 : T16_LocalCFT
  t17 : KroneckerWeber
  t18 : FrobeniusDense
  t19 : BrauerNesbitt
  t20 : GlueConductor.HilbertDifferentFormula
  t21 : GlueConductor.SerreDifferentBound
  t22 : T22_UpperNumbering
  t23 : T23_FontaineClosure
  t24 : EigenformTwist
  t25 : T25_Newforms

/-- **G0 without G20: the glue G1-G19.** The leaves imply the `j`-form of H,
`JHeightBound Mult.S_mul` (steps A1-F3). Not proved: the glue needs the definitions of §4 of the
note, and most leaves are placeholders. -/
theorem jHeightBound_of_leaves (_r : ResearchLeaves) (_t : TextbookLeaves) :
    ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul := by
  sorry

/-- **G0. The leaves imply `SixContactMin`**, through G20, the existing Lean proof
`ZInQ.JHeight.sixContactMin_of_jHeightBound` (`ZInQKernel/Hypotheses/JHeight.lean`). -/
theorem sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) :
    ZInQ.SixContactMin :=
  ZInQ.JHeight.sixContactMin_of_jHeightBound (jHeightBound_of_leaves r t)

end HSyn

end

#print axioms HSyn.weight_match
#print axioms PkgI2.inertiaTrivial_of_goodReduction
#print axioms PkgI2.D2_fixed_of_raynaud
#print axioms GlueConductor.D1_genuine
#print axioms GlueConductor.level_le
#print axioms GlueConductor.fourth_pow_mem
#print axioms HSyn.sixContactMin_of_leaves

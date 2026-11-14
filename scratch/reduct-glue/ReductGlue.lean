import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.TailY
import ZInQKernel.Contrib.NeronC.NeronGroup
import ZInQKernel.Contrib.AbVarBC.Torsion
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
import ZInQKernel.Contrib.CloudW03NeronSurj.Main
import ZInQKernel.Contrib.FrobChain.Pieces

/-!
# reduct-split, part 1: the SGA 7 IX / Serre–Tate rows r6, r7b, r8 from published-form leaves

Task reduct-split (2026-11-14). The rows are the kernel's Props (imported, never restated):
`PkgI2.RaynaudCriterion.{0}` (r6), `PkgI2.SerreTatePotentialGood.{0}` (r7b),
`PkgI2.GrothendieckMonodromy.{0}` (r8), all in `ZInQKernel/HDecomp/Objects.lean`.

This file
* §1 proves the divisibility of `ℓ`-power torsion (`T_ℓ A → A(K̄)[ℓⁿ]` onto) from the kernel's
  `PkgI2.TorsionStructure` (itself proved from the bundle leaf `AvSplit.MumfordTorsionAlgClosed`);
* §2 defines Néron models over a valuation ring `O ⊆ K` (BLR 1.2 Def. 1) and semistable reduction
  (SGA 7 IX Déf. 3.2 read over `κ̄`), with `HeightSplit.HasSemiAbelianIdentityComponent`;
* §3 states the published theorems as leaves;
* §4-§6 prove the rows.
No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq HasGoodReduction)

set_option linter.style.haveILetI false

namespace ReductSplit

/-! ## §1. Divisibility of `ℓ`-power torsion over `K̄` -/

section Div

variable {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]

local notation "Kb" => AlgebraicClosure K

/-- The `n`-torsion subgroup of `A(K̄)`. -/
abbrev torsSub (n : ℕ) : Subgroup (Pts A Kb) := (powMonoidHom n : Pts A Kb →* Pts A Kb).ker

theorem mem_torsSub {n : ℕ} {x : Pts A Kb} : x ∈ torsSub A n ↔ x ^ n = 1 := Iff.rfl

theorem card_torsSub (hT : PkgI2.TorsionStructure.{0}) (g : ℕ)
    (hg : topologicalKrullDim A.X.left = (g : WithBot ℕ∞)) (n : ℕ) (hn : 0 < n)
    (hnK : (n : K) ≠ 0) : Nat.card (torsSub A n) = n ^ (2 * g) := by
  obtain ⟨e, -⟩ := hT K A g n hg hn hnK
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : Nat.card (torsSub A n) = Nat.card (torsion A Kb n) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  rw [h1, Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **`[ℓ] : A(K̄)[ℓ^{k+1}] → A(K̄)[ℓ^k]` is onto** (counting, from `TorsionStructure`). -/
theorem exists_pow_eq (hT : PkgI2.TorsionStructure.{0}) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓK : (ℓ : K) ≠ 0) (k : ℕ) (y : Pts A Kb) (hy : y ^ (ℓ ^ k) = 1) :
    ∃ z : Pts A Kb, z ^ ℓ = y ∧ z ^ (ℓ ^ (k + 1)) = 1 := by
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite (ObjBridge.ofGrp A)
  have hpow : ∀ j : ℕ, ((ℓ ^ j : ℕ) : K) ≠ 0 := fun j => by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hℓK
  have hpos : ∀ j : ℕ, 0 < ℓ ^ j := fun j => pow_pos hℓ.pos j
  have hc : ∀ j, Nat.card (torsSub A (ℓ ^ j)) = (ℓ ^ j) ^ (2 * g) := fun j =>
    card_torsSub A hT g hg (ℓ ^ j) (hpos j) (hpow j)
  -- `f : A[ℓ^{k+1}] → A(K̄)`, `z ↦ z^ℓ`
  let f : torsSub A (ℓ ^ (k + 1)) →* Pts A Kb :=
    (powMonoidHom ℓ).comp (torsSub A (ℓ ^ (k + 1))).subtype
  have hrange : f.range ≤ torsSub A (ℓ ^ k) := by
    rintro _ ⟨z, rfl⟩
    show (z.1 ^ ℓ) ^ (ℓ ^ k) = 1
    rw [← pow_mul, ← pow_succ']
    exact z.2
  -- the kernel of `f` is `A[ℓ]`
  have hker : Nat.card f.ker = Nat.card (torsSub A ℓ) := by
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1.1, z.2⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl }
    · show z.1 ^ (ℓ ^ (k + 1)) = 1
      rw [pow_succ', pow_mul, show z.1 ^ ℓ = 1 from z.2, one_pow]
    · exact z.2
  haveI : Finite (torsSub A (ℓ ^ k)) := Nat.finite_of_card_ne_zero (by
    rw [hc k]; exact pow_ne_zero _ (hpos k).ne')
  have hcard : Nat.card (torsSub A (ℓ ^ k)) ≤ Nat.card f.range := by
    have h := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hker, hc (k + 1)] at h
    have h1 : Nat.card (torsSub A ℓ) = ℓ ^ (2 * g) := by
      have := hc 1; rwa [pow_one] at this
    rw [h1] at h
    rw [hc k]
    have h2 : (ℓ ^ (k + 1)) ^ (2 * g) = ℓ ^ (2 * g) * (ℓ ^ k) ^ (2 * g) := by
      rw [← mul_pow, ← pow_succ']
    rw [h2] at h
    exact le_of_eq (Nat.eq_of_mul_eq_mul_left (pow_pos hℓ.pos _) h).symm
  have heq := Subgroup.eq_of_le_of_card_ge hrange hcard
  have hy' : y ∈ f.range := by rw [heq]; exact hy
  obtain ⟨z, hz⟩ := hy'
  exact ⟨z.1, hz, z.2⟩

/-- **Every `x ∈ A(K̄)[ℓⁿ]` is the `n`-th component of an element of `T_ℓ A`.** -/
theorem exists_tate_lift (hT : PkgI2.TorsionStructure.{0}) (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hℓK : (ℓ : K) ≠ 0) (n : ℕ) (x : Pts A Kb) (hx : x ^ (ℓ ^ n) = 1) :
    ∃ t : PkgI3.Tate.T ℓ (Additive (Pts A Kb)), t.1 n = Additive.ofMul x := by
  classical
  -- the sequence above level `n`: `s 0 = x`, `s (j+1)^ℓ = s j`, `s j ∈ A[ℓ^{n+j}]`
  have step : ∀ j : ℕ, ∀ y : {y : Pts A Kb // y ^ (ℓ ^ (n + j)) = 1},
      ∃ z : {z : Pts A Kb // z ^ (ℓ ^ (n + (j + 1))) = 1}, z.1 ^ ℓ = y.1 := by
    intro j y
    obtain ⟨z, hz, hz'⟩ := exists_pow_eq A hT ℓ hℓ.out hℓK (n + j) y.1 y.2
    exact ⟨⟨z, by rw [← add_assoc]; exact hz'⟩, hz⟩
  let s : (j : ℕ) → {y : Pts A Kb // y ^ (ℓ ^ (n + j)) = 1} :=
    fun j => Nat.rec ⟨x, by simpa using hx⟩ (fun j y => (step j y).choose) j
  have hs : ∀ j, (s (j + 1)).1 ^ ℓ = (s j).1 := fun j => (step j (s j)).choose_spec
  -- the full sequence: `u m = x^(ℓ^(n-m))` for `m ≤ n`, `u (n+j) = s j`
  let u : ℕ → Pts A Kb := fun m => if m ≤ n then x ^ (ℓ ^ (n - m)) else (s (m - n)).1
  refine ⟨⟨fun m => Additive.ofMul (u m), ?_, ?_⟩, ?_⟩
  · show Additive.ofMul (u 0) = 0
    simp only [u, Nat.zero_le, ite_true, Nat.sub_zero, hx]; rfl
  · intro m
    show ℓ • Additive.ofMul (u (m + 1)) = Additive.ofMul (u m)
    rw [← ofMul_pow]
    congr 1
    by_cases h : m + 1 ≤ n
    · simp only [u, h, ite_true, show m ≤ n by omega]
      rw [← pow_mul, ← pow_succ, show n - (m + 1) + 1 = n - m by omega]
    · by_cases h' : m = n
      · subst h'
        simp only [u, h, ite_false, le_refl, ite_true, Nat.sub_self, pow_zero, pow_one]
        rw [show m + 1 - m = 0 + 1 by omega, hs 0]; rfl
      · simp only [u, h, ite_false, show ¬ m ≤ n by omega]
        rw [show m + 1 - n = (m - n) + 1 by omega, hs]
  · show Additive.ofMul (u n) = Additive.ofMul x
    simp [u]

end Div

/-! ## §2. Néron models over a valuation ring; semistable reduction; `T_ℓ` over any `Ω` -/

section NeronDefs

variable {K : Type} [Field K]

/-- `Spec K → Spec O`. -/
abbrev jO (O : ValuationSubring K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O K))

/-- A smooth, separated, quasi-compact group scheme over the valuation ring `O ⊆ K` with an
isomorphism of group schemes from its generic fibre to `A` (the kernel's `GroupModel`, over `O`
instead of `𝓞_L`). -/
structure GroupModelO (A : PkgI3.AbVar K) (O : ValuationSubring K) where
  /-- the model -/
  G : Over (Spec (CommRingCat.of O))
  [grp : GrpObj G]
  [smooth : Smooth G.hom]
  [separated : IsSeparated G.hom]
  [qc : QuasiCompact G.hom]
  /-- the identification of the generic fibre with `A` -/
  gen : (Over.pullback (jO O)).obj G ≅ A.X
  /-- ... as group schemes -/
  gen_hom : letI : GrpObj ((Over.pullback (jO O)).obj G) := Functor.grpObjObj
    IsMonHom gen.hom

attribute [instance] GroupModelO.grp GroupModelO.smooth GroupModelO.separated GroupModelO.qc

variable {A : PkgI3.AbVar K} {O : ValuationSubring K}

/-- **The Néron mapping property** (BLR §1.2 Def. 1): every `K`-morphism from the generic fibre of a
smooth `O`-scheme to `A` extends uniquely. -/
def GroupModelO.IsNeronModel (𝒩 : GroupModelO A O) : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
    Function.Bijective fun f : Y ⟶ 𝒩.G => (Over.pullback (jO O)).map f ≫ 𝒩.gen.hom

/-- `κ̄`, an algebraic closure of the residue field of `O`. -/
abbrev ResBarO (O : ValuationSubring K) : Type := AlgebraicClosure (IsLocalRing.ResidueField O)

/-- The geometric special fibre `𝒩 ×_O κ̄`. -/
def geomSpecialFibre (𝒩 : GroupModelO A O) : Over (Spec (CommRingCat.of (ResBarO O))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))).obj 𝒩.G

instance (𝒩 : GroupModelO A O) : GrpObj (geomSpecialFibre 𝒩) := Functor.grpObjObj

/-- **Semistable special fibre** (SGA 7 IX Déf. 2.2/3.1-3.2, UNVERIFIED locators): the identity
component of the geometric special fibre is an extension of an abelian variety by a (split) torus
(height-split's `HasSemiAbelianIdentityComponent`; over `κ̄` every torus is split). -/
def GroupModelO.IsSemistable (𝒩 : GroupModelO A O) : Prop :=
  ZInQ.HeightSplit.HasSemiAbelianIdentityComponent (geomSpecialFibre 𝒩)

/-- Every Néron model of `A` over `O` has semistable special fibre (the conclusion form). -/
def SemistableNeronModels (A : PkgI3.AbVar K) (O : ValuationSubring K) : Prop :=
  ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → 𝒩.IsSemistable

/-- `A` has semistable reduction at `O`: a Néron model with semistable special fibre exists (the
hypothesis form). -/
def HasSemistableReduction (A : PkgI3.AbVar K) (O : ValuationSubring K) : Prop :=
  ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel ∧ 𝒩.IsSemistable

end NeronDefs

section TateOmega

variable {K : Type} [Field K]

/-- `T_ℓ(A) = lim A(Ω)[ℓⁿ]` over any `K`-field `Ω` (the kernel's `A.T ℓ` is the case
`Ω = AlgebraicClosure K`, by `rfl`). -/
abbrev TΩ (A : PkgI3.AbVar K) (Ω : Type) [Field Ω] [Algebra K Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  PkgI3.Tate.T ℓ (Additive (A.Pt Ω))

/-- The action of `σ ∈ Aut_K(Ω)` on `T_ℓ(A)`. -/
def galTΩ (A : PkgI3.AbVar K) {Ω : Type} [Field Ω] [Algebra K Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Ω ≃ₐ[K] Ω) : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct σ))

example (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : TΩ A (AlgebraicClosure K) ℓ = A.T ℓ := rfl
example (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K) :
    galTΩ A ℓ σ = A.galT σ := rfl

end TateOmega

/-! ## §3. The published theorems (leaves) and the glue -/

/-- **LEAF `NeronSchemeModelExistsDVR` (Néron's existence theorem over a discrete valuation
ring).** Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.4 Thm. 3 with §1.2 Def. 1
(locators UNVERIFIED, as in the kernel's `NeronC.NeronSchemeModelExists`, which is the same theorem
over the Dedekind ring `𝓞_L`): an abelian variety `A` over the fraction field of a discrete
valuation ring `O` has a Néron model over `O`, a smooth, separated, quasi-compact `O`-scheme `N` with
`e : N_K ≅ A` having the Néron mapping property. No group law is asked for. -/
def NeronSchemeModelExistsDVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O] (A : PkgI3.AbVar K),
    ∃ (N : Over (Spec (CommRingCat.of O))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (e : (Over.pullback (jO O)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
        Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom

/-- **LEAF `SemistableUnipotent` (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5, direction
"semistable ⇒ unipotent of echelon ≤ 2"; number UNVERIFIED).** `O ⊆ K` a discrete valuation ring,
`Ω` an algebraic closure of `K`, `w` a valuation ring of `Ω` over `O`, `ℓ` a prime invertible in
`O`. If `A` has semistable reduction at `O`, every `σ` in the inertia group of `w` satisfies
`(σ - 1)² = 0` on `T_ℓ(A)`. (SGA 7 states the criterion for a separable closure; for
`Ω ⊇ K^sep` the restriction `Aut(Ω/K) → Gal(K^sep/K)` is bijective and `A(Ω)[ℓⁿ] = A(K^sep)[ℓⁿ]`.
Reading: the weakest form, one `σ` at a time; the print gives `(σ-1)(τ-1) = 0` for `σ, τ ∈ I`
per pkg-I2's reading, UNVERIFIED.) -/
def SemistableUnipotent : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- **LEAF `RaynaudSemistable` (Raynaud's criterion, SGA 7 I, Exp. IX, Prop. 4.7; number
UNVERIFIED; also Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), per h-trust).** `O ⊆ K` a discrete
valuation ring, `m ≥ 3` invertible in `O`. If the points of order `m` of `A` are rational over `K`
(every `x ∈ A(K̄)[m]` comes from `A(K)`), then `A` has semistable reduction at `O` (every Néron
model of `A` over `O` has semistable special fibre). -/
def RaynaudSemistable : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O] (A : PkgI3.AbVar K)
    (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- **LEAF `SemistableReductionDVR` (Grothendieck's semistable reduction theorem, SGA 7 I,
Exp. IX, Thm. 3.6; number UNVERIFIED).** `O ⊆ K` a discrete valuation ring. There is a finite
extension `K' ⊆ K̄` such that `A_{K'}` has semistable reduction at every place of `K'` over `O`
(every discrete valuation ring `O' ⊆ K'` with `O' ∩ K = O`; these are the local rings of the
normalization of `O` in `K'`). SGA 7 gives `K'` finite separable (even Galois); the conclusion
here only asks for finite. -/
def SemistableReductionDVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O] (A : PkgI3.AbVar K),
    ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
      ∀ O' : ValuationSubring K', IsDiscreteValuationRing O' →
        O'.comap (algebraMap K K') = O → SemistableNeronModels (A.baseChange K') O'

/-- **GLUE `DVRFiniteExtension`.** A valuation ring of a finite extension `K' ⊆ K̄` lying over a
discrete valuation ring of `K` is a discrete valuation ring (Bourbaki AC VI §8.1; Serre, *Corps
locaux* I §4; UNVERIFIED locators). Needs the fundamental inequality `e ≤ [K' : K]` for an
arbitrary (possibly inseparable) finite extension, or Krull–Akizuki; neither is in Mathlib 4.35. -/
def DVRFiniteExtension : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)), w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (K' : IntermediateField K (AlgebraicClosure K)), FiniteDimensional K K' →
      IsDiscreteValuationRing (w.comap (algebraMap K' (AlgebraicClosure K)))

/-- **GLUE `FixedTorsionRational`.** For `m` invertible in `K`, a point of `A(K̄)[m]` fixed by
`Aut(K̄/K)` is rational over `K`. Needs: `A[m]` is étale (`[m]` étale, the bundle leaf
`mulEtaleAbelianScheme` over a field), so its `K̄`-points are `K^sep`-points; a `K^sep`-point fixed by
`Gal(K^sep/K)` is a `K`-point (Galois descent for points of a finite-type `K`-scheme: the point lies
in an affine open `Spec R` and the ring map `R → K^sep` lands in `(K^sep)^{Gal} = K`). Not in
Mathlib 4.35 in this form. -/
def FixedTorsionRational : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (m : ℕ), (m : K) ≠ 0 →
    (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x : A.Pt (AlgebraicClosure K),
      x ^ m = 1 → A.galAct σ x = x) →
    ∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x

/-! ## §4. Common lemmas -/

section Common

variable {K : Type} [Field K]

/-- A Néron model which is a group model, from the scheme-level leaf (group law from the mapping
property, neron-c's `grpObjOfNeron`). -/
theorem exists_neron_groupModel (hN : NeronSchemeModelExistsDVR) (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (A : PkgI3.AbVar K) :
    ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel := by
  obtain ⟨N, hS, hSep, hQC, e, hN⟩ := hN K O A
  let F := Over.pullback (jO O)
  let P : Over (Spec (CommRingCat.of O)) → Prop := fun Y => Smooth Y.hom
  have hP1 : P (𝟙_ _) := ZInQ.Contrib.NeronC.smooth_tensorUnit _
  have hP2 : ∀ X Y, P X → P Y → P (X ⊗ Y) := fun X Y hX hY =>
    ZInQ.Contrib.NeronC.smooth_tensor X Y hX hY
  have hB : ∀ Y, P Y → Function.Bijective fun f : Y ⟶ N => F.map f ≫ e.hom :=
    fun Y hY => @hN Y hY
  letI : GrpObj N := ZInQ.Contrib.NeronC.grpObjOfNeron F P hP1 hP2 N hS _ e hB
  let 𝒩 : GroupModelO A O :=
    { G := N
      gen := e
      gen_hom := ZInQ.Contrib.NeronC.isMonHom_of_neron F P hP1 hP2 N hS _ e hB }
  exact ⟨𝒩, fun Y _ => hN Y⟩

theorem hasSemistableReduction_of (hN : NeronSchemeModelExistsDVR) (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (A : PkgI3.AbVar K) (h : SemistableNeronModels A O) :
    HasSemistableReduction A O := by
  obtain ⟨𝒩, h𝒩⟩ := exists_neron_groupModel hN O A
  exact ⟨𝒩, h𝒩, h 𝒩 h𝒩⟩

theorem natCast_ne_zero_of_isUnit (O : ValuationSubring K) {m : ℕ} (h : IsUnit (m : O)) :
    (m : K) ≠ 0 := by
  intro h0
  have : ((m : O) : K) = 0 := by simpa using h0
  have h0' : (m : O) = 0 := by exact_mod_cast this
  rw [h0'] at h
  exact not_isUnit_zero h

/-- From `(σ - 1)² = 0` on `T_ℓ` to `(σ - 1)² x = 0` at a point lifted to level `n`. -/
theorem unipSq_of_tate {Ω : Type} [Field Ω] [Algebra K Ω] (B : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (σ : Ω ≃ₐ[K] Ω) (t : TΩ B Ω ℓ) (n : ℕ) (x : B.Pt Ω)
    (ht : t.1 n = Additive.ofMul x)
    (h : galTΩ B ℓ σ (galTΩ B ℓ σ t) - 2 • galTΩ B ℓ σ t + t = 0) :
    B.galAct σ (B.galAct σ x) * (B.galAct σ x)⁻¹ * (B.galAct σ x)⁻¹ * x = 1 := by
  have h' := congrArg (fun s : TΩ B Ω ℓ => Additive.toMul (s.1 n)) h
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub, AddSubgroup.coe_nsmul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, galTΩ, PkgI3.Tate.map_apply, ht, toMul_add, toMul_sub,
    toMul_nsmul, MonoidHom.toAdditive_apply_apply, toMul_ofMul, AddSubgroup.coe_zero,
    Pi.zero_apply, toMul_zero] at h'
  rw [← h', div_eq_mul_inv, pow_two, mul_inv_rev, ← _root_.mul_assoc]

end Common

open scoped Pointwise in
/-- Inertia for `K` restricts to inertia for an intermediate field `K'` (same underlying map). -/
theorem isInertia_restrict {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
    (K' : IntermediateField K Ω) (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (σ' : Ω ≃ₐ[K'] Ω)
    (hσσ' : ∀ y, σ' y = σ y) (h : IsInertia w σ) : IsInertia w σ' := by
  obtain ⟨hd, hi⟩ := h
  have hd' : σ' ∈ w.decompositionSubgroup K' := by
    have hs : σ • w = w := hd
    show σ' • w = w
    refine Eq.trans ?_ hs
    ext y
    simp only [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul, Set.mem_smul_set,
      AlgEquiv.smul_def, hσσ']
  refine ⟨hd', ?_⟩
  have key : ∀ a : w, (⟨σ', hd'⟩ : w.decompositionSubgroup K') • a =
      (⟨σ, hd⟩ : w.decompositionSubgroup K) • a := fun a => Subtype.ext (hσσ' a)
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi ⊢
  refine RingEquiv.ext fun r => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  have h1 := RingEquiv.congr_fun hi (IsLocalRing.residue w a)
  change (⟨σ', hd'⟩ : w.decompositionSubgroup K') • IsLocalRing.residue w a =
    IsLocalRing.residue w a
  change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w a =
    IsLocalRing.residue w a at h1
  rw [← IsLocalRing.ResidueField.residue_smul, key, IsLocalRing.ResidueField.residue_smul, h1]

/-! ## §5. r6: Raynaud's criterion, Galois form -/

/-- **r6 (`PkgI2.RaynaudCriterion`) from published-form leaves**: Raynaud's criterion (SGA 7 IX
4.7) gives semistable reduction, Grothendieck's criterion (SGA 7 IX 3.5) gives `(σ-1)² = 0` on
`T_ℓ`, which descends to `A(K̄)[ℓⁿ]` by divisibility (from `TorsionStructure`, i.e. the bundle leaf
`MumfordTorsionAlgClosed`). Glue left: `FixedTorsionRational` (Galois-fixed `m`-torsion is
rational). -/
theorem raynaudCriterion_of_leaves (hR : RaynaudSemistable) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVR) (hT : PkgI2.TorsionStructure.{0})
    (hF : FixedTorsionRational) : PkgI2.RaynaudCriterion.{0} := by
  intro K _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let B := ObjBridge.ofGrp A
  have hss : SemistableNeronModels B O :=
    hR K O B m hm hmO (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact unipSq_of_tate B ℓ σ t n x ht
    (hU K O (AlgebraicClosure K) w hw B (hasSemistableReduction_of hN O B hss) ℓ hℓO σ hσ t)

/-! ## §6. r8: Grothendieck's monodromy theorem, finite-level form -/

/-- `O → w ∩ K'` for `O = w ∩ K`. -/
def toO' {K : Type} [Field K] (O : ValuationSubring K) (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (K' : IntermediateField K (AlgebraicClosure K)) :
    O →+* w.comap (algebraMap K' (AlgebraicClosure K)) :=
  ((algebraMap K K').comp O.subtype).codRestrict
    (w.comap (algebraMap K' (AlgebraicClosure K))).toSubring (fun x => by
      have hx : (x : K) ∈ w.comap (algebraMap K (AlgebraicClosure K)) := by rw [hw]; exact x.2
      show algebraMap K' (AlgebraicClosure K) (algebraMap K K' x) ∈ w
      rw [← IsScalarTower.algebraMap_apply]
      exact hx)

/-- **r8 (`PkgI2.GrothendieckMonodromy`) from published-form leaves**: SGA 7 IX 3.6 gives `K'` with
`A_{K'}` semistable at `w ∩ K'`; SGA 7 IX 3.5 over `K'` (with `Ω = K̄`) gives `(σ-1)² = 0` on
`T_ℓ(A_{K'})` for `σ` in the inertia group fixing `K'`; it is transported to `A` by `bcPt` and
descends to `A(K̄)[ℓⁿ]` by divisibility. Glue left: `DVRFiniteExtension`. -/
theorem grothendieckMonodromy_of_leaves (hS : SemistableReductionDVR)
    (hU : SemistableUnipotent) (hN : NeronSchemeModelExistsDVR) (hT : PkgI2.TorsionStructure.{0})
    (hD : DVRFiniteExtension) : PkgI2.GrothendieckMonodromy.{0} := by
  intro K _ O _ w hw A _
  let B := ObjBridge.ofGrp A
  obtain ⟨K', hK', hss'⟩ := hS K O B
  refine ⟨K', hK', fun σ hσ hfix ℓ hℓ hℓO n x hx => ?_⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI := hD K O w hw K' hK'
  have hss := hss' (w.comap (algebraMap K' (AlgebraicClosure K))) inferInstance (by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw])
  haveI : IsAlgClosure K' (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (L := K') (A := AlgebraicClosure K)⟩
  let σ' : AlgebraicClosure K ≃ₐ[K'] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun y => hfix _ y.2)
  have hσ' : IsInertia w σ' := isInertia_restrict K' w σ σ' (fun _ => rfl) hσ
  have hℓO' : IsUnit (ℓ : w.comap (algebraMap K' (AlgebraicClosure K))) := by
    have := hℓO.map (toO' O w hw K')
    rwa [map_natCast] at this
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  let e := ZInQ.Contrib.AbVarBC.bcPt (L := K') B (AlgebraicClosure K)
  let t' : TΩ (B.baseChange K') (AlgebraicClosure K) ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive e.symm.toMonoidHom) t
  have ht' : t'.1 n = Additive.ofMul (e.symm x) := by
    show MonoidHom.toAdditive e.symm.toMonoidHom (t.1 n) = _
    rw [ht]; rfl
  have h := hU K' (w.comap (algebraMap K' (AlgebraicClosure K))) (AlgebraicClosure K) w rfl
    (B.baseChange K') (hasSemistableReduction_of hN _ _ hss) ℓ hℓO' σ' hσ' t'
  have hu := unipSq_of_tate (B.baseChange K') ℓ σ' t' n (e.symm x) ht' h
  have key : ∀ q, e ((B.baseChange K').galAct σ' q) = B.galAct σ (e q) := fun q => by
    rw [ZInQ.Contrib.AbVarBC.bcPt_galAct]
    congr 2
  have := congrArg e hu
  simp only [map_mul, map_inv, key, map_one] at this
  have hx' : e (e.symm x) = x := e.apply_symm_apply x
  erw [hx'] at this
  exact this

/-! ## §7. r7b: Serre–Tate potential good reduction -/

/-- **LEAF `SerreTateThm2` (Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88
(1968), §2, Thm. 2; locator UNVERIFIED).** `O ⊆ K` a discrete valuation ring, `w` a valuation ring
of `K̄` over `O`, `ℓ` a prime invertible in `O`. `A` has potential good reduction (good reduction
over a finite extension `K' ⊆ K̄`, at the place `w ∩ K'`) iff the image of the inertia group `I` of
`w` under `ρ_ℓ : Gal → Aut(T_ℓ A)` is finite. Printed form; the left side is Serre–Tate's
definition of potential good reduction (at the place of `K'` under `w`), written with the kernel's
`HasGoodReduction` exactly as in the row. -/
def SerreTateThm2 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (ℓ : ℕ) [Fact ℓ.Prime],
      IsUnit (ℓ : O) →
      ((∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          HasGoodReduction (PkgI2.baseChange A K') (w.comap (algebraMap K' (AlgebraicClosure K)))) ↔
       (Set.range fun σ : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K // IsInertia w σ} =>
          (ObjBridge.ofGrp A).galT (ℓ := ℓ) σ.1).Finite)

/-- **GLUE `TorsionFieldOfDefinition`.** The points of `A(K̄)[m]` are defined over a finite
extension: there is a finite `K'' ⊆ K̄` such that every `σ ∈ Aut(K̄/K)` fixing `K''` fixes
`A(K̄)[m]` pointwise. Needs: `A(K̄)[m]` is finite (proved here from `TorsionStructure` when `m` is
invertible) and every `K̄`-point of a finite-type `K`-scheme factors through `Spec K''` for a
finite `K'' ⊆ K̄` (the point lies in an affine open `Spec R`, `R` a finitely generated `K`-algebra,
whose image in `K̄` is a finite extension of `K`). Not in Mathlib 4.35 in this form. -/
def TorsionFieldOfDefinition : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (m : ℕ), (m : K) ≠ 0 →
    ∃ K'' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K'' ∧
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ K'', σ y = y) →
        ∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 → A.galAct σ x = x

section R7b

variable {K : Type} [Field K]

theorem galAct_mul' (B : PkgI3.AbVar K) (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : B.Pt (AlgebraicClosure K)) : B.galAct (σ * τ) x = B.galAct σ (B.galAct τ x) := by
  show PkgI3.AbVar.galHom (σ * τ) ≫ x = PkgI3.AbVar.galHom σ ≫ PkgI3.AbVar.galHom τ ≫ x
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

theorem isInertia_mul_inv (w : ValuationSubring (AlgebraicClosure K))
    {σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K} (hσ : IsInertia w σ) (hτ : IsInertia w τ) :
    IsInertia w (τ⁻¹ * σ) := by
  obtain ⟨hσd, hσi⟩ := hσ
  obtain ⟨hτd, hτi⟩ := hτ
  refine ⟨mul_mem (inv_mem hτd) hσd, ?_⟩
  have := mul_mem (inv_mem hτi) hσi
  exact this

/-- Elements of `T_ℓ` are fixed by `σ` once `σ` fixes all `ℓ`-power torsion. -/
theorem galT_eq_self (B : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ n, ∀ x : B.Pt (AlgebraicClosure K), x ^ (ℓ ^ n) = 1 → B.galAct σ x = x)
    (t : B.T ℓ) : B.galT σ t = t := by
  apply Subtype.ext
  funext n
  show Additive.ofMul (B.galAct σ (Additive.toMul (t.1 n))) = t.1 n
  rw [h n _ (by
    have := PkgI3.Tate.pow_smul_eq_zero t.2 n
    exact congrArg Additive.toMul this)]
  rfl

/-- `(⇐)`: an open subgroup `I ∩ G_{K'}` acting trivially makes the image of inertia finite. -/
theorem finite_image_of_open (A : PkgI3.AbVar K) (w : ValuationSubring (AlgebraicClosure K))
    (ℓ : ℕ) [Fact ℓ.Prime] (K' : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K K']
    (hK' : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
      (∀ x ∈ K', σ x = x) → ∀ n : ℕ, ∀ x : A.Pt (AlgebraicClosure K), x ^ (ℓ ^ n) = 1 →
        A.galAct σ x = x) :
    (Set.range fun σ : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K // IsInertia w σ} =>
      A.galT (ℓ := ℓ) σ.1).Finite := by
  classical
  let Φ : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K // IsInertia w σ} →
      (K' →ₐ[K] AlgebraicClosure K) := fun σ =>
      (σ.1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).toAlgHom.comp K'.val
  have hdep : ∀ σ τ : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K // IsInertia w σ}, Φ σ = Φ τ →
      A.galT (ℓ := ℓ) σ.1 = A.galT τ.1 := by
    intro σ τ hστ
    have hρ := isInertia_mul_inv w σ.2 τ.2
    have hfix : ∀ y ∈ K', (τ.1⁻¹ * σ.1) y = y := by
      intro y hy
      have := DFunLike.congr_fun hστ ⟨y, hy⟩
      change σ.1 y = τ.1 y at this
      rw [AlgEquiv.mul_apply, this, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    apply LinearMap.ext
    intro t
    have h1 : A.galT (ℓ := ℓ) (τ.1⁻¹ * σ.1) t = t :=
      galT_eq_self A ℓ _ (fun n x hx => hK' _ hρ hfix n x hx) t
    have h2 : σ.1 = τ.1 * (τ.1⁻¹ * σ.1) := by group
    apply Subtype.ext
    funext n
    show Additive.ofMul (A.galAct σ.1 (Additive.toMul (t.1 n))) =
      Additive.ofMul (A.galAct τ.1 (Additive.toMul (t.1 n)))
    have h3 := congrArg (fun s : A.T ℓ => s.1 n) h1
    change Additive.ofMul (A.galAct (τ.1⁻¹ * σ.1) (Additive.toMul (t.1 n))) = t.1 n at h3
    conv_lhs => rw [h2, galAct_mul']
    rw [show A.galAct (τ.1⁻¹ * σ.1) (Additive.toMul (t.1 n)) = Additive.toMul (t.1 n) from
      congrArg Additive.toMul h3]
  let g : (K' →ₐ[K] AlgebraicClosure K) → (A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ) := fun φ =>
    if h : ∃ σ, Φ σ = φ then A.galT (ℓ := ℓ) h.choose.1 else 0
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨Φ σ, ?_⟩
  have h : ∃ τ, Φ τ = Φ σ := ⟨σ, rfl⟩
  simp only [g, h, dif_pos]
  exact hdep _ _ h.choose_spec

/-- `(⇒)`: a finite image of inertia is trivial on an open subgroup `I ∩ G_{K'}`. -/
theorem open_of_finite_image (hT : PkgI2.TorsionStructure.{0}) (hD : TorsionFieldOfDefinition)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (w : ValuationSubring (AlgebraicClosure K)) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0)
    (hfin : (Set.range fun σ : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K // IsInertia w σ} =>
      (ObjBridge.ofGrp A).galT (ℓ := ℓ) σ.1).Finite) :
    ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
        (∀ x ∈ K', σ x = x) →
        ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), galAct A σ x = x := by
  classical
  let B := ObjBridge.ofGrp A
  set R := Set.range fun σ : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K // IsInertia w σ} =>
      B.galT (ℓ := ℓ) σ.1 with hRdef
  -- a level at which each non-identity element of `R` is seen to be non-identity
  let lev : (B.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) → ℕ := fun f =>
    if h : ∃ t : B.T ℓ, ∃ n : ℕ, (f t).1 n ≠ t.1 n then h.choose_spec.choose else 0
  let N := hfin.toFinset.sup lev
  obtain ⟨K', hK', hfixN⟩ := hD K B (ℓ ^ N) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓK)
  refine ⟨K', hK', fun σ hσ hσK' n x hx => ?_⟩
  -- `σ` acts trivially on `T_ℓ`
  have hid : B.galT (ℓ := ℓ) σ = LinearMap.id := by
    by_contra hne
    have hex : ∃ t : B.T ℓ, ∃ n : ℕ, (B.galT (ℓ := ℓ) σ t).1 n ≠ t.1 n := by
      by_contra hno
      push Not at hno
      exact hne (LinearMap.ext fun t => Subtype.ext (funext fun n => hno t n))
    have hmem : B.galT (ℓ := ℓ) σ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨⟨σ, hσ⟩, rfl⟩
    have hle : lev (B.galT (ℓ := ℓ) σ) ≤ N := Finset.le_sup hmem
    simp only [lev, hex, dif_pos] at hle
    apply hex.choose_spec.choose_spec
    set t := hex.choose
    set n0 := hex.choose_spec.choose
    show Additive.ofMul (B.galAct σ (Additive.toMul (t.1 n0))) = t.1 n0
    have htor : (Additive.toMul (t.1 n0)) ^ (ℓ ^ N) = 1 := by
      have h0 : (Additive.toMul (t.1 n0)) ^ (ℓ ^ n0) = 1 :=
        congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero t.2 n0)
      obtain ⟨c, hc⟩ := pow_dvd_pow ℓ hle
      rw [hc, pow_mul, h0, one_pow]
    rw [hfixN σ hσK' _ htor]
    rfl
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ hℓK n x hx
  have := congrArg (fun s : B.T ℓ => Additive.toMul (s.1 n)) (LinearMap.congr_fun hid t)
  change B.galAct σ (Additive.toMul (t.1 n)) = Additive.toMul (t.1 n) at this
  rw [ht] at this
  exact this

/-- **r7b (`PkgI2.SerreTatePotentialGood`) from the printed Serre–Tate Thm. 2**, with the glue
`TorsionFieldOfDefinition` (for `⇒`) and divisibility (from `TorsionStructure`). -/
theorem serreTatePotentialGood_of_leaves (hST : SerreTateThm2) (hT : PkgI2.TorsionStructure.{0})
    (hD : TorsionFieldOfDefinition) : PkgI2.SerreTatePotentialGood.{0} := by
  intro K _ O _ w hw A _ ℓ hℓ hℓO
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓK := natCast_ne_zero_of_isUnit O hℓO
  rw [hST K O w hw A ℓ hℓO]
  constructor
  · exact open_of_finite_image hT hD A w ℓ hℓK
  · rintro ⟨K', hK', hfix⟩
    haveI := hK'
    exact finite_image_of_open (ObjBridge.ofGrp A) w ℓ K'
      (fun σ hσ hσK' n x hx => hfix σ hσ hσK' n x hx)

end R7b

/-! ## §8. Transport of semistability along isomorphisms; base change in two steps -/

section Transport

variable {K : Type} [Field K]

/-- A Néron model of `B'` is a Néron model of `B` along a group isomorphism `B ≅ B'`, with the same
underlying group scheme. -/
def GroupModelO.transport {B B' : PkgI3.AbVar K} {O : ValuationSubring K} (e : B.X ≅ B'.X)
    (he : IsMonHom e.hom) (𝒩 : GroupModelO B' O) : GroupModelO B O where
  G := 𝒩.G
  gen := 𝒩.gen ≪≫ e.symm
  gen_hom := by
    letI : GrpObj ((Over.pullback (jO O)).obj 𝒩.G) := Functor.grpObjObj
    haveI := 𝒩.gen_hom
    show IsMonHom (𝒩.gen.hom ≫ e.inv)
    infer_instance

theorem GroupModelO.transport_isNeronModel {B B' : PkgI3.AbVar K} {O : ValuationSubring K}
    (e : B.X ≅ B'.X) (he : IsMonHom e.hom) (𝒩 : GroupModelO B' O) (h : 𝒩.IsNeronModel) :
    (𝒩.transport e he).IsNeronModel := by
  intro Y _
  have hb := h Y
  have : (fun f : Y ⟶ 𝒩.G => (Over.pullback (jO O)).map f ≫ (𝒩.gen ≪≫ e.symm).hom) =
      (fun g => g ≫ e.inv) ∘ (fun f : Y ⟶ 𝒩.G => (Over.pullback (jO O)).map f ≫ 𝒩.gen.hom) := by
    funext f; simp
  show Function.Bijective (fun f : Y ⟶ 𝒩.G =>
    (Over.pullback (jO O)).map f ≫ (𝒩.gen ≪≫ e.symm).hom)
  rw [this]
  exact Function.Bijective.comp
    ⟨fun a b hab => (cancel_mono e.inv).mp hab, fun c => ⟨c ≫ e.hom, by simp⟩⟩ hb

theorem semistableNeronModels_transport {B B' : PkgI3.AbVar K} {O : ValuationSubring K}
    (e : B.X ≅ B'.X) (he : IsMonHom e.hom) (h : SemistableNeronModels B O) :
    SemistableNeronModels B' O := fun 𝒩 h𝒩 =>
  h (𝒩.transport e he) (𝒩.transport_isNeronModel e he h𝒩)

/-- `(A_{K'})_L ≅ A_L` for a tower `K → K' → L`, as group schemes over `L`. -/
def bcbcGrpIso (A : PkgI3.AbVar K) (K' L : Type) [Field K'] [Field L] [Algebra K K']
    [Algebra K' L] [Algebra K L] [IsScalarTower K K' L] :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K' L)))).mapGrp.obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K')))).mapGrp.obj
          (Grp.mk A.X)) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapGrp.obj (Grp.mk A.X) :=
  let f1 := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  let f2 := Spec.map (CommRingCat.ofHom (algebraMap K' L))
  have hf : f2 ≫ f1 = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    simp only [f1, f2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  (Functor.mapGrpCompIso.app (Grp.mk A.X)).symm ≪≫
    (Functor.mapGrpNatIso (Over.pullbackComp f2 f1).symm).app (Grp.mk A.X) ≪≫
    (Functor.mapGrpNatIso (eqToIso (show Over.pullback (f2 ≫ f1) =
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))) by rw [hf]))).app (Grp.mk A.X)

/-- The underlying isomorphism `((A_{K'})_L).X ≅ (A_L).X`. -/
def bcbcIso (A : PkgI3.AbVar K) (K' L : Type) [Field K'] [Field L] [Algebra K K']
    [Algebra K' L] [Algebra K L] [IsScalarTower K K' L] :
    ((A.baseChange K').baseChange L).X ≅ (A.baseChange L).X :=
  (Grp.forget _).mapIso (bcbcGrpIso A K' L)

theorem bcbcIso_isMonHom (A : PkgI3.AbVar K) (K' L : Type) [Field K'] [Field L] [Algebra K K']
    [Algebra K' L] [Algebra K L] [IsScalarTower K K' L] :
    IsMonHom (bcbcIso A K' L).hom :=
  inferInstanceAs (IsMonHom (bcbcGrpIso A K' L).hom.hom.hom)

end Transport

/-! ## §9. The global height-split rows SS1 (`SemistableReductionThm`) and SS3
(`SemistablePersists`) from the local SGA 7 IX theorems -/

/-- **LEAF `SemistablePersistsDVR` (SGA 7 I, Exp. IX, Prop. 3.3, first assertion; number
UNVERIFIED).** `O ⊆ K` a discrete valuation ring, `K'/K` a finite extension, `O' ⊆ K'` a discrete
valuation ring over `O`. If `A` has semistable reduction at `O`, then `A_{K'}` has semistable
reduction at `O'` (every Néron model of `A_{K'}` over `O'` is semistable). SGA 7 allows any
extension of discrete valuation rings; here `K'/K` is finite (a specialization). -/
def SemistablePersistsDVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

/-- **GLUE `DVRComapFinite`.** The restriction of a discrete valuation ring of `K'` to a subfield
`K` with `[K' : K]` finite is a discrete valuation ring. Needs: the restricted valuation is
non-trivial (else `O' ⊇ K`, so `O' ⊇` the integral closure of `K` in `K'`, which is `K'`) and its
value group is a non-zero subgroup of `ℤ`. Short on paper; the Mathlib 4.35 API passing between
`ValuationSubring` and `IsDiscreteValuationRing` makes it a separate task. -/
def DVRComapFinite : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (O' : ValuationSubring K'), IsDiscreteValuationRing O' →
      IsDiscreteValuationRing (O'.comap (algebraMap K K'))

/-- **GLUE `SemistableLocalGlobal`.** For a Néron model `𝒩` of `A_L` over `𝓞_L` (`L` a number
field), height-split's `IsSemistable 𝒩` (the geometric fibre of `𝒩` at every maximal ideal `𝔭` has
semi-abelian identity component) holds iff `A_L` has semistable reduction at every discrete
valuation ring of `L`. Needs: (i) every discrete valuation ring of `L` is `(𝓞_L)_𝔭` for a maximal
`𝔭` (Mathlib has the valuation `v.valuation` of `𝔭`; the identification for valuation subrings is
not packaged); (ii) Néron models localize (BLR §1.2 Prop. 4, published: `𝒩 ⊗ (𝓞_L)_𝔭` is a Néron
model over `(𝓞_L)_𝔭`) and are unique up to unique isomorphism; (iii) the geometric special fibre of
`𝒩 ⊗ (𝓞_L)_𝔭` is the geometric fibre of `𝒩` at `𝔭` (pullback pasting along
`𝓞_L → (𝓞_L)_𝔭 → κ`, with `κ(𝔭) ≅ κ((𝓞_L)_𝔭)` and an isomorphism of their algebraic closures),
and `HasSemiAbelianIdentityComponent` is invariant under such isomorphisms. -/
def SemistableLocalGlobal : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : ZInQ.DefFaltings.GroupModel A L), 𝒩.IsNeronModel →
    (ZInQ.HeightSplit.IsSemistable 𝒩 ↔
      ∀ O : ValuationSubring L, IsDiscreteValuationRing O → HasSemistableReduction (A.baseChange L) O)

/-- **GLUE `SemistableAlmostAll`.** An abelian variety over a number field has semistable
reduction at all but finitely many discrete valuation rings of `K`. Needs: good reduction outside
a finite set of primes (spreading out: an abelian scheme over `𝓞_K[1/N]`, EGA IV 8.10.5 (xii), the
bundle leaf `egaIV_8_10_5_xii`, with smoothness and properness spread out); at a prime of good
reduction the abelian scheme is the Néron model (BLR §1.2 Prop. 8) and its special fibre is an
abelian variety, hence semi-abelian with trivial torus; finitely many primes give finitely many
discrete valuation rings (as in (i) of `SemistableLocalGlobal`). -/
def SemistableAlmostAll : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K),
    {O : ValuationSubring K | IsDiscreteValuationRing O ∧ ¬ HasSemistableReduction A O}.Finite

/-- **SS3 (`HeightSplit.SemistablePersists`) from the local SGA 7 IX 3.3**, Néron's existence
theorem over discrete valuation rings, and the glue `SemistableLocalGlobal`, `DVRComapFinite`. -/
theorem semistablePersists_of_leaves (h33 : SemistablePersistsDVR)
    (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistablePersists := by
  intro K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩'
  rw [hLG K A L 𝒩 h𝒩] at hss
  rw [hLG K A L' 𝒩' h𝒩']
  intro O' hO'
  haveI := hO'
  haveI : IsDiscreteValuationRing (O'.comap (algebraMap L L')) := hDown L L' O' hO'
  have h1 := h33 L (O'.comap (algebraMap L L')) L' O' rfl (A.baseChange L)
    (hss _ inferInstance)
  exact hasSemistableReduction_of hN O' _
    (semistableNeronModels_transport (bcbcIso A L L') (bcbcIso_isMonHom A L L') h1)

/-- **SS1 (`HeightSplit.SemistableReductionThm`) from the local SGA 7 IX 3.6 and 3.3**, Néron's
existence theorem over discrete valuation rings, and the glue `SemistableLocalGlobal`,
`SemistableAlmostAll`, `DVRComapFinite`: `L₀` is the compositum in `K̄` of the fields given by 3.6
at the finitely many places of non-semistable reduction. -/
theorem semistableReductionThm_of_leaves (h36 : SemistableReductionDVR)
    (h33 : SemistablePersistsDVR) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistableReductionThm := by
  classical
  intro K _ _ A
  set S := {O : ValuationSubring K | IsDiscreteValuationRing O ∧ ¬ HasSemistableReduction A O}
  have hS : S.Finite := hAA K A
  have hch : ∀ O : ValuationSubring K, ∃ K' : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K K' ∧ (IsDiscreteValuationRing O →
        ∀ O' : ValuationSubring K', IsDiscreteValuationRing O' →
          O'.comap (algebraMap K K') = O → SemistableNeronModels (A.baseChange K') O') := by
    intro O
    by_cases hO : IsDiscreteValuationRing O
    · obtain ⟨K', h1, h2⟩ := h36 K O A
      exact ⟨K', h1, fun _ => h2⟩
    · exact ⟨⊥, inferInstance, fun h => absurd h hO⟩
  choose F hFfin hF using hch
  let L₀ : IntermediateField K (AlgebraicClosure K) := ⨆ O ∈ hS.toFinset, F O
  haveI : FiniteDimensional K L₀ :=
    IntermediateField.finiteDimensional_iSup_of_finset' (fun O _ => hFfin O)
  haveI : NumberField L₀ := NumberField.of_module_finite K L₀
  refine ⟨L₀, inferInstance, inferInstance, inferInstance, fun 𝒩 h𝒩 => ?_⟩
  rw [hLG K A L₀ 𝒩 h𝒩]
  intro O'' hO''
  haveI := hO''
  haveI hO : IsDiscreteValuationRing (O''.comap (algebraMap K L₀)) := hDown K L₀ O'' hO''
  by_cases hOS : O''.comap (algebraMap K L₀) ∈ S
  · -- a place of bad reduction: go through `F O ≤ L₀`
    set O := O''.comap (algebraMap K L₀) with hOdef
    have hle : F O ≤ L₀ := le_iSup₂ (f := fun O _ => F O) O (hS.mem_toFinset.mpr hOS)
    letI : Algebra (F O) L₀ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsScalarTower K (F O) L₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : FiniteDimensional (F O) L₀ := by
      haveI := hFfin O
      exact FiniteDimensional.right K (F O) L₀
    haveI hOi : IsDiscreteValuationRing (O''.comap (algebraMap (F O) L₀)) :=
      hDown (F O) L₀ O'' hO''
    have hc : (O''.comap (algebraMap (F O) L₀)).comap (algebraMap K (F O)) = O := by
      rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
    have h1 : SemistableNeronModels (A.baseChange (F O)) (O''.comap (algebraMap (F O) L₀)) :=
      hF O hO _ hOi hc
    have h2 := hasSemistableReduction_of hN _ _ h1
    have h3 := h33 (F O) (O''.comap (algebraMap (F O) L₀)) L₀ O'' rfl (A.baseChange (F O)) h2
    exact hasSemistableReduction_of hN O'' _
      (semistableNeronModels_transport (bcbcIso A (F O) L₀) (bcbcIso_isMonHom A (F O) L₀) h3)
  · -- a place of semistable reduction of `A`
    have hgood : HasSemistableReduction A (O''.comap (algebraMap K L₀)) := by
      by_contra hc
      exact hOS ⟨hO, hc⟩
    exact hasSemistableReduction_of hN O'' _ (h33 K _ L₀ O'' rfl A hgood)

/-! ## §10. `K̄`-points are defined over finite extensions; `TorsionFieldOfDefinition` proved -/

section FieldOfDef

variable {K : Type} [Field K]

/-- Every `K̄`-point of a `K`-scheme locally of finite type is fixed by the automorphisms of `K̄`
fixing some finite subextension `K''` (the point lies in an affine open `Spec R`, `R` finitely
generated, and `K''` is generated by the images of generators of `R`). -/
theorem exists_fixing_field (X : Over (Spec (CommRingCat.of K))) [LocallyOfFiniteType X.hom]
    (q : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ X) :
    ∃ K'' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K'' ∧
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ K'', σ y = y) →
        PkgI3.AbVar.galHom σ ≫ q = q := by
  classical
  let q0 : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ X.left := q.left
  have hq0 : q0 ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    Over.w q
  let p : X.left := q0 (IsLocalRing.closedPoint (AlgebraicClosure K))
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q0 ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : s = IsLocalRing.closedPoint (AlgebraicClosure K) :=
      Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure K)) _ _
    rw [this]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q0 hrange
  have hq' : q' ≫ U.ι = q0 := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of (AlgebraicClosure K) := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q0 = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq0]
  have hft : θ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hθ]
    infer_instance
  letI : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  let φa : Γ(X.left, U) →ₐ[K] AlgebraicClosure K :=
    { φ.hom with
      commutes' := fun c => congrArg (fun f => CommRingCat.Hom.hom f c) hcomp }
  haveI : Finite ((φa : Γ(X.left, U) → AlgebraicClosure K) '' (s : Set Γ(X.left, U))) :=
    (s.finite_toSet.image _).to_subtype
  refine ⟨IntermediateField.adjoin K ((φa : Γ(X.left, U) → AlgebraicClosure K) '' (s : Set _)),
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral), fun σ hσ => ?_⟩
  have hfix : (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K).comp φa = φa := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro r hr
    exact hσ _ (IntermediateField.subset_adjoin _ _ ⟨r, hr, rfl⟩)
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ q0 = q0
  rw [hql, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact DFunLike.congr_fun hfix r

/-- **`TorsionFieldOfDefinition`, proved** from `TorsionStructure` (finiteness of `A(K̄)[m]`) and
`exists_fixing_field`. -/
theorem torsionFieldOfDefinition_of (hT : PkgI2.TorsionStructure.{0}) :
    TorsionFieldOfDefinition := by
  classical
  intro K _ B m hmK
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h => hmK (by rw [h, Nat.cast_zero]))
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite B
  obtain ⟨e, -⟩ := hT K (ObjBridge.toGrp B) g m hg hm hmK
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : Finite (torsion (ObjBridge.toGrp B) (AlgebraicClosure K) m) := Finite.of_equiv _ e.symm
  have hfin : {x : B.Pt (AlgebraicClosure K) | x ^ m = 1}.Finite :=
    Set.toFinite (torsion (ObjBridge.toGrp B) (AlgebraicClosure K) m)
  have hch : ∀ x : B.Pt (AlgebraicClosure K), ∃ K'' : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K K'' ∧ ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        (∀ y ∈ K'', σ y = y) → PkgI3.AbVar.galHom σ ≫ x = x := fun x =>
    exists_fixing_field B.X x
  choose F hF1 hF2 using hch
  refine ⟨⨆ x ∈ hfin.toFinset, F x,
    IntermediateField.finiteDimensional_iSup_of_finset' (fun x _ => hF1 x), ?_⟩
  intro σ hσ x hx
  have hle : F x ≤ ⨆ x ∈ hfin.toFinset, F x :=
    le_iSup₂ (f := fun x _ => F x) x (hfin.mem_toFinset.mpr hx)
  exact hF2 x σ (fun y hy => hσ y (hle hy))

/-- **r7b without glue**: `PkgI2.SerreTatePotentialGood` from the printed Serre–Tate Thm. 2 and
`TorsionStructure` (the bundle leaf `MumfordTorsionAlgClosed`). -/
theorem serreTatePotentialGood_of_printed (hST : SerreTateThm2)
    (hT : PkgI2.TorsionStructure.{0}) : PkgI2.SerreTatePotentialGood.{0} :=
  serreTatePotentialGood_of_leaves hST hT (torsionFieldOfDefinition_of hT)

end FieldOfDef

/-! ## §11. Final forms over the bundle leaf `MumfordTorsionAlgClosed` -/

/-- **r6** from Raynaud (SGA 7 IX 4.7), Grothendieck (SGA 7 IX 3.5), Néron (BLR 1.4/3), Mumford §4
(the bundle leaf) and the one glue `FixedTorsionRational`. -/
theorem raynaudCriterion_final (hR : RaynaudSemistable) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVR) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hF : FixedTorsionRational) : PkgI2.RaynaudCriterion.{0} :=
  raynaudCriterion_of_leaves hR hU hN (AvSplit.torsionStructure_of_mumford hM) hF

/-- **r8** from SGA 7 IX 3.6 and 3.5, Néron (BLR 1.4/3), Mumford §4 and the one glue
`DVRFiniteExtension`. -/
theorem grothendieckMonodromy_final (hS : SemistableReductionDVR) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVR) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hD : DVRFiniteExtension) : PkgI2.GrothendieckMonodromy.{0} :=
  grothendieckMonodromy_of_leaves hS hU hN (AvSplit.torsionStructure_of_mumford hM) hD

/-- **r7b, no glue**: from the printed Serre–Tate Thm. 2 and Mumford §4. -/
theorem serreTatePotentialGood_final (hST : SerreTateThm2) (hM : AvSplit.MumfordTorsionAlgClosed) :
    PkgI2.SerreTatePotentialGood.{0} :=
  serreTatePotentialGood_of_printed hST (AvSplit.torsionStructure_of_mumford hM)

/-! ## §12. SS2 (`HeightSplit.SemistableNeronBaseChange`): the local SGA 7 IX 3.3 (second
assertion) and the global glue -/

/-- `O → O'` for `O' ∩ K = O`. -/
def comapHom {K K' : Type} [Field K] [Field K'] [Algebra K K'] {O : ValuationSubring K}
    {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O) : O →+* O' :=
  ((algebraMap K K').comp O.subtype).codRestrict O'.toSubring (fun x => by
    have hx : (x : K) ∈ O'.comap (algebraMap K K') := by rw [hO]; exact x.2
    exact hx)

/-- **LEAF `IdentityComponentBaseChangeDVR` (SGA 7 I, Exp. IX, Prop. 3.3, second assertion; number
UNVERIFIED).** `O ⊆ K` a discrete valuation ring, `K'/K` finite, `O' ⊆ K'` a discrete valuation ring
over `O`, `A` with semistable reduction at `O`, `𝒩`, `𝒩'` the Néron models of `A` over `O` and of
`A_{K'}` over `O'`. For the identity component `𝒰 = 𝒩⁰` (an open subgroup scheme of `𝒩` with
connected generic and geometric special fibres), the base change `𝒰 ×_O O'` maps to `𝒩'` by an open
immersion of group schemes (SGA 7: the canonical map `𝒩⁰ ×_O O' → 𝒩'⁰` is an isomorphism; here only
"open immersion into `𝒩'`" is kept, a weakening). -/
def IdentityComponentBaseChangeDVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    ∀ (U : Over (Spec (CommRingCat.of O))) [GrpObj U] (i : U ⟶ 𝒩.G), IsOpenImmersion i.left →
      IsMonHom i → ConnectedSpace ((Over.pullback (jO O)).obj U).left →
      ConnectedSpace ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap O (ResBarO O))))).obj U).left →
      ∃ j : (Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj U ⟶ 𝒩'.G,
        IsOpenImmersion j.left ∧
        (letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj U) :=
          Functor.grpObjObj
         IsMonHom j)

/-- **GLUE `SemistableNeronBaseChangeLocalGlobal`.** The global form SS2 over `𝓞_L → 𝓞_{L'}` from the
local SGA 7 IX 3.3. Needs: (i) the identity component `𝒩⁰` of the smooth group scheme `𝒩` over the
Dedekind scheme `Spec 𝓞_L` is an open subgroup scheme (SGA 3 VI_B 3.10, published) and a group
model (quasi-compactness of `𝒩⁰`); (ii) `𝒱 = 𝒩 ×_{𝓞_L} 𝓞_{L'}` and `𝒩⁰ ×_{𝓞_L} 𝓞_{L'}` as group
models of `A_{L'}` (generic fibre `(A_L)_{L'} ≅ A_{L'}`, `bcbcIso` above); (iii) the map
`𝒩⁰ ×_{𝓞_L} 𝓞_{L'} → 𝒩'` given by the Néron mapping property of `𝒩'`; (iv) it is an open immersion
because it is one after localization at every maximal ideal of `𝓞_{L'}` (the leaf, with BLR §1.2
Prop. 4 and the uniqueness of Néron models, as in `SemistableLocalGlobal`). Mathlib 4.35 has no
identity component of a group scheme over a base. -/
def SemistableNeronBaseChangeLocalGlobal : Prop :=
  IdentityComponentBaseChangeDVR → SemistableLocalGlobal → ZInQ.HeightSplit.SemistableNeronBaseChange

/-- **SS2 from the local SGA 7 IX 3.3 (second assertion)** and the glue. The global content (the
identity component over `𝓞_L` and the gluing) is in the glue. -/
theorem semistableNeronBaseChange_of_leaves (h33b : IdentityComponentBaseChangeDVR)
    (hLG : SemistableLocalGlobal) (hG : SemistableNeronBaseChangeLocalGlobal) :
    ZInQ.HeightSplit.SemistableNeronBaseChange :=
  hG h33b hLG

/-! ## §13. `faltingsLemma5BC` from Faltings' Lemma 5 over the base field -/

section FL5

open ZInQ.DefFaltings

variable {K : Type} [Field K] {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Transport of a group model along a group isomorphism of generic fibres (generic in the
isomorphism, so that the kernel never unfolds a concrete one). -/
def gmTransport {K₁ K₂ : Type} [Field K₁] [Field K₂] [Algebra K₁ L] [Algebra K₂ L]
    {A₁ : PkgI3.AbVar K₁} {A₂ : PkgI3.AbVar K₂} (e : (A₂.baseChange L).X ≅ (A₁.baseChange L).X)
    (he : IsMonHom e.hom) (𝒩 : GroupModel A₁ L) : GroupModel A₂ L where
  G := 𝒩.G
  gen := 𝒩.gen ≪≫ e.symm
  gen_hom := by
    letI : GrpObj (genericFibre L 𝒩.G) := Functor.grpObjObj
    haveI := 𝒩.gen_hom
    show IsMonHom (𝒩.gen.hom ≫ e.inv)
    infer_instance

theorem gmTransport_isNeronModel {K₁ K₂ : Type} [Field K₁] [Field K₂] [Algebra K₁ L]
    [Algebra K₂ L] {A₁ : PkgI3.AbVar K₁} {A₂ : PkgI3.AbVar K₂}
    (e : (A₂.baseChange L).X ≅ (A₁.baseChange L).X) (he : IsMonHom e.hom) (𝒩 : GroupModel A₁ L)
    (h : 𝒩.IsNeronModel) : (gmTransport e he 𝒩).IsNeronModel := by
  intro Y _
  have hb := h Y
  have : (fun f : Y ⟶ 𝒩.G => (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (NumberField.RingOfIntegers L) L)))).map f ≫ (𝒩.gen ≪≫ e.symm).hom) =
      (fun g => g ≫ e.inv) ∘ (fun f : Y ⟶ 𝒩.G => (Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap (NumberField.RingOfIntegers L) L)))).map f ≫ 𝒩.gen.hom) := by
    funext f
    simp only [Iso.trans_hom, Iso.symm_hom, Function.comp_apply]
    exact (Category.assoc _ _ _).symm
  show Function.Bijective (fun f : Y ⟶ 𝒩.G => (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (NumberField.RingOfIntegers L) L)))).map f ≫ (𝒩.gen ≪≫ e.symm).hom)
  rw [this]
  exact Function.Bijective.comp
    ⟨fun a b hab => (cancel_mono e.inv).mp hab, fun c => ⟨c ≫ e.hom, by simp⟩⟩ hb

theorem gmTransport_isSemistable {K₁ K₂ : Type} [Field K₁] [Field K₂] [Algebra K₁ L]
    [Algebra K₂ L] {A₁ : PkgI3.AbVar K₁} {A₂ : PkgI3.AbVar K₂}
    (e : (A₂.baseChange L).X ≅ (A₁.baseChange L).X) (he : IsMonHom e.hom) (𝒩 : GroupModel A₁ L)
    (h : ZInQ.HeightSplit.IsSemistable 𝒩) :
    ZInQ.HeightSplit.IsSemistable (gmTransport e he 𝒩) := h

/-- The height depends only on the group scheme over `𝓞_L` (every field of `MetrizedModel` other than
`model` is about `model.G`). -/
theorem gmTransport_height {K₁ K₂ : Type} [Field K₁] [Field K₂] [Algebra K₁ L]
    [Algebra K₂ L] {A₁ : PkgI3.AbVar K₁} {A₂ : PkgI3.AbVar K₂}
    (e : (A₂.baseChange L).X ≅ (A₁.baseChange L).X) (he : IsMonHom e.hom) (𝒩 : GroupModel A₁ L) :
    (gmTransport e he 𝒩).height = 𝒩.height := by
  apply le_antisymm
  · refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
    subst hM
    exact iInf_le_of_le g (iInf_le_of_le ⟨gmTransport e he M.model, M.hodge, M.lattice_eq, M.arch⟩
      (iInf_le_of_le rfl le_rfl))
  · refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
    obtain ⟨model, hodge, lattice_eq, arch⟩ := M
    change model = gmTransport e he 𝒩 at hM
    subst hM
    exact iInf_le_of_le g (iInf_le_of_le ⟨𝒩, hodge, lattice_eq, arch⟩
      (iInf_le_of_le rfl le_rfl))

/-- A group model of `A_L` (kernel encoding `GroupModel A L`) as a group model of the abelian variety
`A_L` over `L` (`GroupModel (A.baseChange L) L`), along `(A_L)_L ≅ A_L`. -/
def toBC {A : PkgI3.AbVar K} (𝒩 : GroupModel A L) : GroupModel (A.baseChange L) L :=
  gmTransport (bcbcIso A L L) (bcbcIso_isMonHom A L L) 𝒩

/-- **GLUE `IsogenyBaseChangeDeg`.** For an isogeny `φ : A → B` over `K` and a number field `L ⊇ K`,
the base change `φ_L : A_L → B_L` is an isogeny of the same degree. Needs: `φ_L =
(Over.pullback _).map φ` is a homomorphism (monoidal functor), finite and surjective (stable under
base change); `#ker φ_L(L̄) = #ker φ(K̄)`: `A_L(L̄) = A(L̄)` (`bcPt`), `A(K̄) → A(L̄)` injective
(`extPt_injective`), and onto on `ker φ` because `ker φ` is finite over `K` (kernel's
`exists_lift_of_isFinite` applied to the scheme `ker φ`, which is not constructed in the kernel). -/
def IsogenyBaseChangeDeg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L],
      ∃ φ' : (A.baseChange L).X ⟶ (B.baseChange L).X, IsIsogeny φ' ∧ isogDeg φ' = isogDeg φ

/-- **`faltingsLemma5BC` from the base-field form** (`HeightSplit.FaltingsLemma5`, Faltings' Lemma 5
in the semistable inequality form over the field of definition) and the glue `IsogenyBaseChangeDeg`;
the encoding of Néron models of `A_L` is handled by `toBC` (proved). -/
theorem faltingsLemma5BC_of_base (hF : ZInQ.HeightSplit.FaltingsLemma5)
    (hI : IsogenyBaseChangeDeg) : ZInQ.HeightSplit.FaltingsLemma5BC := by
  intro K _ _ A B φ hφ L _ _ _ 𝒩A 𝒩B hA hB sA sB x y hx hy
  obtain ⟨φ', hφ', hdeg⟩ := hI K A B φ hφ L
  rw [← hdeg]
  exact hF L (A.baseChange L) (B.baseChange L) φ' hφ' (toBC 𝒩A) (toBC 𝒩B)
    (gmTransport_isNeronModel _ _ 𝒩A hA) (gmTransport_isNeronModel _ _ 𝒩B hB)
    (gmTransport_isSemistable _ _ 𝒩A sA) (gmTransport_isSemistable _ _ 𝒩B sB) x y
    ((gmTransport_height _ _ 𝒩A).trans hx) ((gmTransport_height _ _ 𝒩B).trans hy)

end FL5

/-! ## §14. `FixedTorsionRational` over perfect fields (proved); the glue narrowed to imperfect `K` -/

section Perfect

variable {K : Type} [Field K]

/-- Over a perfect field, a `K̄`-point of a `K`-scheme locally of finite type fixed by every
`σ ∈ Aut(K̄/K)` comes from a `K`-point. -/
theorem exists_rational_of_fixed [PerfectField K] (X : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType X.hom] (q : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ X)
    (hq : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, PkgI3.AbVar.galHom σ ≫ q = q) :
    ∃ y : PkgI3.AbVar.ptObj (K := K) K ⟶ X,
      ZInQ.Contrib.AbVarBC.extHom (Algebra.ofId K (AlgebraicClosure K)) ≫ y = q := by
  classical
  haveI : IsGalois K (AlgebraicClosure K) := ⟨⟩
  let q0 : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ X.left := q.left
  have hq0 : q0 ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    Over.w q
  let p : X.left := q0 (IsLocalRing.closedPoint (AlgebraicClosure K))
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q0 ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : s = IsLocalRing.closedPoint (AlgebraicClosure K) :=
      Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure K)) _ _
    rw [this]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q0 hrange
  have hq' : q' ≫ U.ι = q0 := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of (AlgebraicClosure K) := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q0 = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq0]
  -- every `φ r` is fixed by `Aut(K̄/K)`
  have hfixφ : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      φ ≫ CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K) = φ := by
    intro σ
    have h1 := congrArg Over.Hom.left (hq σ)
    change Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ q0 =
      q0 at h1
    rw [hql, ← Category.assoc, ← Spec.map_comp] at h1
    have h2 := (cancel_mono (e.inv ≫ U.ι)).mp h1
    exact Spec.map_injective h2
  have hmem : ∀ r, φ.hom r ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    intro r
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    exact congrArg (fun f => CommRingCat.Hom.hom f r) (hfixφ σ)
  choose c hc using hmem
  have hinj := (algebraMap K (AlgebraicClosure K)).injective
  let ψ : Γ(X.left, U) →+* K :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hc, map_mul, map_mul, hc, hc])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hc, map_add, map_add, hc, hc]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) = φ := by
    ext r
    exact hc r
  have hθψ : θ ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K K) := by
    ext a
    apply hinj
    have := congrArg (fun f => CommRingCat.Hom.hom f a) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this ⊢
    rw [show algebraMap K (AlgebraicClosure K) (ψ (θ.hom a)) = φ.hom (θ.hom a) from hc _, this]
    rfl
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ?_, ?_⟩
  · show (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K K))
    rw [Category.assoc, Category.assoc, ← hθ, ← Spec.map_comp, hθψ]
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom ((Algebra.ofId K (AlgebraicClosure K) : K →ₐ[K] _) :
        K →+* AlgebraicClosure K)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι = q0
    rw [hql, ← Category.assoc, ← Spec.map_comp]
    congr 2

/-- **`FixedTorsionRational` restricted to imperfect fields (the remaining glue of r6).** -/
def FixedTorsionRationalImperfect : Prop :=
  ∀ (K : Type) [Field K], ¬ PerfectField K → ∀ (A : PkgI3.AbVar K) (m : ℕ), (m : K) ≠ 0 →
    (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x : A.Pt (AlgebraicClosure K),
      x ^ m = 1 → A.galAct σ x = x) →
    ∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x

theorem fixedTorsionRational_of_imperfect (h : FixedTorsionRationalImperfect) :
    FixedTorsionRational := by
  intro K _ A m hm hfix x hx
  by_cases hp : PerfectField K
  · obtain ⟨y, hy⟩ := exists_rational_of_fixed A.X x (fun σ => hfix σ x hx)
    exact ⟨y, hy⟩
  · exact h K hp A m hm hfix x hx

/-- **r6** with the glue narrowed to imperfect fields: over a perfect field (in particular in
characteristic `0`, every use in the project) only published-form leaves are used. -/
theorem raynaudCriterion_final' (hR : RaynaudSemistable) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVR) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hF : FixedTorsionRationalImperfect) : PkgI2.RaynaudCriterion.{0} :=
  raynaudCriterion_final hR hU hN hM (fixedTorsionRational_of_imperfect hF)

end Perfect

/-! ## §15. `DVRComapFinite`, proved -/

section DVRDown

open IsDedekindDomain
open scoped WithZero

/-- **`DVRComapFinite`, proved**: with `v'` the `ℤᵐ⁰`-valuation of `O'`, the restriction
`v = v' ∘ (K → K')` has cyclic value group (a subgroup of `ℤᵐ⁰ˣ`) which is nontrivial: otherwise every
non-zero coefficient of the minimal polynomial of a uniformizer `ϖ'` has valuation `1`, and the
constant term dominates `minpoly(ϖ') = 0`. -/
theorem dvrComapFinite : DVRComapFinite := by
  intro K K' _ _ _ _ O' hO'
  classical
  let v' : Valuation K' ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal O').valuation K'
  have hmem' : ∀ y : K', y ∈ O' ↔ v' y ≤ 1 := by
    intro y
    have h := congrArg (fun S : Subring K' => y ∈ S)
      (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := O') (K := K'))
    change _ = (y ∈ v'.valuationSubring) at h
    rw [Valuation.mem_valuationSubring_iff] at h
    rw [← h]
    constructor
    · intro hy; exact Subring.mem_map.mpr ⟨⟨y, hy⟩, Subring.mem_top _, rfl⟩
    · intro hy
      obtain ⟨z, -, rfl⟩ := Subring.mem_map.mp hy
      exact z.2
  let v : Valuation K ℤᵐ⁰ := v'.comap (algebraMap K K')
  have heq : O'.comap (algebraMap K K') = v.valuationSubring := by
    ext x
    rw [Valuation.mem_valuationSubring_iff]
    exact hmem' (algebraMap K K' x)
  -- nontriviality
  have hnt : ∃ x : K, v x ≠ 0 ∧ v x ≠ 1 := by
    by_contra hno
    push Not at hno
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O'
    have hϖ0 : (ϖ : K') ≠ 0 := by
      intro h; exact hϖ.ne_zero (Subtype.ext h)
    have hϖ1 : v' (ϖ : K') < 1 := by
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K')
        (IsDiscreteValuationRing.maximalIdeal O') ϖ).mpr hϖ.not_isUnit
      exact this
    have hint : IsIntegral K (ϖ : K') := Algebra.IsIntegral.isIntegral _
    set p := minpoly K (ϖ : K')
    have hp0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hϖ0
    have hcoeff : ∀ i, v (p.coeff i) ≤ 1 := by
      intro i
      by_cases hi : p.coeff i = 0
      · rw [hi, map_zero]; exact zero_le
      · exact le_of_eq (hno _ ((map_ne_zero v).mpr hi))
    have hev : (∑ i ∈ Finset.range (p.natDegree + 1),
        algebraMap K K' (p.coeff i) * (ϖ : K') ^ i) = 0 := by
      have := minpoly.aeval K (ϖ : K')
      rw [Polynomial.aeval_eq_sum_range] at this
      simpa [Algebra.smul_def] using this
    rw [Finset.sum_range_succ'] at hev
    have hrest : v' (∑ i ∈ Finset.range p.natDegree,
        algebraMap K K' (p.coeff (i + 1)) * (ϖ : K') ^ (i + 1)) < 1 := by
      apply Valuation.map_sum_lt v' one_ne_zero
      intro i _
      rw [map_mul, map_pow]
      calc v' (algebraMap K K' (p.coeff (i + 1))) * v' (ϖ : K') ^ (i + 1)
          ≤ 1 * v' (ϖ : K') ^ (i + 1) := by
            gcongr
            exact hcoeff (i + 1)
        _ = v' (ϖ : K') ^ (i + 1) := one_mul _
        _ < 1 := pow_lt_one₀ zero_le hϖ1 (Nat.succ_ne_zero i)
    have h0 : v' (algebraMap K K' (p.coeff 0) * (ϖ : K') ^ 0) = 1 := by
      rw [pow_zero, _root_.mul_one]
      exact hno _ ((map_ne_zero v).mpr hp0)
    have := Valuation.map_add_eq_of_lt_left v' (h0 ▸ hrest)
    rw [add_comm, hev, map_zero, h0] at this
    exact zero_ne_one this
  obtain ⟨x, hx0, hx1⟩ := hnt
  haveI : Nontrivial v.valueGroup := by
    refine ⟨⟨⟨Units.mk0 (v x) hx0, MonoidWithZeroHom.mem_valueGroup _ ⟨x, rfl⟩⟩, 1, ?_⟩⟩
    intro h
    apply hx1
    have := congrArg (fun u : v.valueGroup => ((u : ℤᵐ⁰ˣ) : ℤᵐ⁰)) h
    simpa using this
  exact (congrArg (fun S : ValuationSubring K => IsDiscreteValuationRing S) heq).mpr
    (Valuation.valuationSubring_isDiscreteValuationRing v)

end DVRDown

/-- **SS3** with `DVRComapFinite` discharged. -/
theorem semistablePersists_final (h33 : SemistablePersistsDVR) (hN : NeronSchemeModelExistsDVR)
    (hLG : SemistableLocalGlobal) : ZInQ.HeightSplit.SemistablePersists :=
  semistablePersists_of_leaves h33 hN hLG dvrComapFinite

/-- **SS1** with `DVRComapFinite` discharged. -/
theorem semistableReductionThm_final (h36 : SemistableReductionDVR)
    (h33 : SemistablePersistsDVR) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) : ZInQ.HeightSplit.SemistableReductionThm :=
  semistableReductionThm_of_leaves h36 h33 hN hLG hAA dvrComapFinite

/-! ## §16. `DVRFiniteExtension`, proved (the fundamental inequality `e ≤ n`) -/

section DVRUp

/-- Elements of `K'` whose values lie in distinct cosets of `v'(K^×)` are `K`-linearly independent
(the argument behind `e ≤ [K' : K]`). -/
theorem linearIndependent_of_distinct_cosets {K K' : Type} [Field K] [Field K'] [Algebra K K']
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v' : Valuation K' Γ) (π : Γ) (hπ : π ≠ 0)
    (hdisc : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v' (algebraMap K K' x) = π ^ n)
    {N : ℕ} (z : Fin N → K') (hz : ∀ i, z i ≠ 0)
    (hsep : ∀ i j, ∀ k : ℤ, v' (z i) = π ^ k * v' (z j) → i = j) :
    LinearIndependent K z := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  set T := s.filter (fun i => g i ≠ 0)
  have hT : T.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  let f : Fin N → Γ := fun i => v' (g i • z i)
  obtain ⟨i0, hi0T, hmax⟩ := T.exists_max_image f hT
  have hi0 := (Finset.mem_filter.mp hi0T).2
  have hf0 : f i0 ≠ 0 := by
    simp only [f, Algebra.smul_def, map_mul, ne_eq, mul_eq_zero, not_or]
    exact ⟨(Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (algebraMap K K').injective).mpr hi0),
      (Valuation.ne_zero_iff _).mpr (hz i0)⟩
  have hlt : ∀ j ∈ T.erase i0, f j < f i0 := by
    intro j hj
    obtain ⟨hji0, hjT⟩ := Finset.mem_erase.mp hj
    refine lt_of_le_of_ne (hmax j hjT) (fun heq => hji0 ?_)
    have hgj := (Finset.mem_filter.mp hjT).2
    obtain ⟨a, ha⟩ := hdisc (g j) hgj
    obtain ⟨b, hb⟩ := hdisc (g i0) hi0
    simp only [f, Algebra.smul_def, map_mul, ha, hb] at heq
    apply hsep j i0 (b - a)
    have hπa : π ^ a ≠ 0 := zpow_ne_zero a hπ
    rw [zpow_sub₀ hπ]
    calc v' (z j) = (π ^ a)⁻¹ * (π ^ a * v' (z j)) := by rw [inv_mul_cancel_left₀ hπa]
      _ = (π ^ a)⁻¹ * (π ^ b * v' (z i0)) := by rw [heq]
      _ = π ^ b * (π ^ a)⁻¹ * v' (z i0) := by
        rw [← _root_.mul_assoc, mul_comm ((π ^ a)⁻¹) (π ^ b)]
      _ = π ^ b / π ^ a * v' (z i0) := by rw [div_eq_mul_inv]
  have hsumT : ∑ i ∈ s, g i • z i = g i0 • z i0 + ∑ j ∈ T.erase i0, g j • z j := by
    rw [Finset.add_sum_erase T (fun j => g j • z j) hi0T]
    exact (Finset.sum_filter_of_ne (fun x _ hx => by
      intro h0; apply hx; rw [h0, zero_smul])).symm
  have hrest : v' (∑ j ∈ T.erase i0, g j • z j) < f i0 :=
    Valuation.map_sum_lt v' hf0 hlt
  have := Valuation.map_add_eq_of_lt_left v' hrest
  rw [← hsumT, hsum, map_zero] at this
  exact hf0 this.symm

/-- **A valuation ring of a finite extension lying over a DVR is a DVR.** -/
theorem dvr_of_finiteExt {K K' : Type} [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (O' : ValuationSubring K')
    (h : O'.comap (algebraMap K K') = O) : IsDiscreteValuationRing O' := by
  classical
  set v' := O'.valuation with hv'
  have hK : ∀ x : K, v' (algebraMap K K' x) ≤ 1 ↔ x ∈ O := by
    intro x
    rw [ValuationSubring.valuation_le_one_iff, ← h]
    rfl
  have hinj := (algebraMap K K').injective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set π := v' (algebraMap K K' (ϖ : K)) with hπdef
  have hϖ0 : (ϖ : K) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hπ0 : π ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ hinj).mpr hϖ0)
  have hunit : ∀ u : Oˣ, v' (algebraMap K K' ((u : O) : K)) = 1 := by
    intro u
    apply le_antisymm ((hK _).mpr (u : O).2)
    have h2 : v' (algebraMap K K' (((u⁻¹ : Oˣ) : O) : K)) ≤ 1 := (hK _).mpr (u⁻¹ : Oˣ).1.2
    have h3 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 := by
      have := congrArg (fun t : O => (t : K)) u.mul_inv
      exact_mod_cast this
    have h4 : v' (algebraMap K K' ((u : O) : K)) * v' (algebraMap K K' (((u⁻¹ : Oˣ) : O) : K))
        = 1 := by
      rw [← map_mul, ← map_mul, h3, map_one, map_one]
    calc (1 : O'.ValueGroup) = _ := h4.symm
      _ ≤ v' (algebraMap K K' ((u : O) : K)) * 1 := by gcongr
      _ = _ := _root_.mul_one _
  have hπ1 : π < 1 := by
    refine lt_of_le_of_ne ((hK _).mpr ϖ.2) (fun h1 => hϖ.not_isUnit ?_)
    have hinv : (ϖ : K)⁻¹ ∈ O := by
      rw [← hK, map_inv₀, map_inv₀, ← hπdef, h1, inv_one]
    refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
    simp [hϖ0]
  have hdisc : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v' (algebraMap K K' x) = π ^ n := by
    intro x hx
    rcases O.mem_or_inv_mem x with hxO | hxO
    · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨x, hxO⟩ : O)) (fun h0 => hx (congrArg Subtype.val h0)) hϖ
      refine ⟨n, ?_⟩
      have hx' : x = ((u : O) : K) * (ϖ : K) ^ n := by
        have := congrArg Subtype.val hu
        simpa using this
      rw [hx', map_mul, map_mul, map_pow, map_pow, hunit, _root_.one_mul, zpow_natCast]
    · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨x⁻¹, hxO⟩ : O)) (fun h0 => hx (inv_eq_zero.mp (congrArg Subtype.val h0))) hϖ
      refine ⟨-n, ?_⟩
      have hx' : x⁻¹ = ((u : O) : K) * (ϖ : K) ^ n := by
        have := congrArg Subtype.val hu
        simpa using this
      have : v' (algebraMap K K' x⁻¹) = π ^ n := by
        rw [hx', map_mul, map_mul, map_pow, map_pow, hunit, _root_.one_mul]
      rw [map_inv₀, map_inv₀] at this
      rw [zpow_neg, zpow_natCast, ← this, inv_inv]
  -- the value group and the subgroup generated by `π`
  let πu : O'.ValueGroupˣ := Units.mk0 π hπ0
  let G := (v' : K' →*₀ O'.ValueGroup).valueGroup
  let H := Subgroup.zpowers πu
  have hπG : πu ∈ G := v'.mem_valueGroup (Set.mem_range_self _)
  have hHG : H ≤ G := (Subgroup.zpowers_le).mpr hπG
  have hval : ∀ g : G, ∃ y : K', y ≠ 0 ∧ v' y = ((g : O'.ValueGroupˣ) : O'.ValueGroup) := by
    intro g
    obtain ⟨a, ha, x, hx⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm _).mp g.2
    refine ⟨x / a, ?_, ?_⟩
    · intro h0
      have : v' (x / a) = 0 := by rw [h0, map_zero]
      rw [map_div₀] at this
      have hx0 : v' x = 0 := by
        rcases div_eq_zero_iff.mp this with h | h
        · exact h
        · exact absurd h ((Valuation.ne_zero_iff _).mpr (fun ha0 => ha (by
            change v' a = 0; rw [ha0, map_zero])))
      have := hx.trans hx0
      exact Units.ne_zero _ ((mul_eq_zero.mp this).resolve_left ha)
    · change v' (x / a) = _
      rw [map_div₀]
      change v' x / v' a = _
      have hx' : v' a * ((g : O'.ValueGroupˣ) : O'.ValueGroup) = v' x := hx
      have ha' : v' a ≠ 0 := ha
      rw [← hx', mul_div_cancel_left₀ _ ha']
  choose y hy0 hyv using hval
  let H' := H.subgroupOf G
  -- `G ⧸ H'` is finite
  haveI hfin : Finite (G ⧸ H') := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    let emb : Fin (Module.finrank K K' + 1) ↪ G ⧸ H' :=
      Fin.valEmbedding.trans (Infinite.natEmbedding _)
    let z : Fin (Module.finrank K K' + 1) → K' := fun i => y (Quotient.out (emb i))
    have hli : LinearIndependent K z := by
      refine linearIndependent_of_distinct_cosets v' π hπ0 hdisc z (fun i => hy0 _) ?_
      intro i j k hk
      apply emb.injective
      rw [← Quotient.out_eq (emb i), ← Quotient.out_eq (emb j)]
      change QuotientGroup.mk _ = QuotientGroup.mk _
      rw [QuotientGroup.eq]
      have hk' : ((Quotient.out (emb i) : G) : O'.ValueGroupˣ) =
          πu ^ k * ((Quotient.out (emb j) : G) : O'.ValueGroupˣ) := by
        apply Units.ext
        simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, πu]
        rw [← hyv, ← hyv]
        exact hk
      rw [Subgroup.mem_subgroupOf]
      have : ((Quotient.out (emb i) : G)⁻¹ * Quotient.out (emb j) : G) =
          (πu ^ k)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk']
        group
        rw [mul_comm, ← _root_.mul_assoc, zpow_neg_one, mul_inv_cancel, _root_.one_mul]
      rw [this]
      exact H.inv_mem (H.zpow_mem (Subgroup.mem_zpowers πu) k)
    have := hli.fintype_card_le_finrank
    simp at this
  have he : H'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  -- `g ↦ g^e` embeds `G` into the cyclic `H'`
  let φ : G →* H' :=
    { toFun := fun g => ⟨g ^ H'.index, H'.pow_index_mem g⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_pow] }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : ((a : O'.ValueGroupˣ) : O'.ValueGroup) ^ H'.index =
        ((b : O'.ValueGroupˣ) : O'.ValueGroup) ^ H'.index := by
      have := congrArg (fun t : H' => (((t : G) : O'.ValueGroupˣ) : O'.ValueGroup)) hab
      simpa [φ] using this
    have h2 := (pow_left_strictMonoOn₀ (M₀ := O'.ValueGroup) he).injOn (Set.mem_setOf.mpr zero_le')
      (Set.mem_setOf.mpr zero_le') h1
    exact Subtype.ext (Units.ext h2)
  haveI : IsCyclic H' :=
    isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHG).injective
  haveI : IsCyclic G := isCyclic_of_injective φ hφ
  haveI : v'.IsNontrivial := ⟨⟨algebraMap K K' (ϖ : K), hπ0, ne_of_lt hπ1⟩⟩
  have hdvr := Valuation.valuationSubring_isDiscreteValuationRing v'
  exact (congrArg (fun S : ValuationSubring K' => IsDiscreteValuationRing S)
    (O'.valuationSubring_valuation)).mp hdvr

/-- **`DVRFiniteExtension`, proved.** -/
theorem dvrFiniteExtension : DVRFiniteExtension := by
  intro K _ O _ w hw K' hK'
  exact dvr_of_finiteExt O (w.comap (algebraMap K' (AlgebraicClosure K))) (by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw])

/-- **r8, no glue**: from SGA 7 IX 3.6 and 3.5, Néron (BLR 1.4/3) and Mumford §4. -/
theorem grothendieckMonodromy_final' (hS : SemistableReductionDVR) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVR) (hM : AvSplit.MumfordTorsionAlgClosed) :
    PkgI2.GrothendieckMonodromy.{0} :=
  grothendieckMonodromy_final hS hU hN hM dvrFiniteExtension

end DVRUp

/-! ## §17. `IsogenyBaseChangeDeg`, proved -/

section IsogBC

open ZInQ.DefFaltings ZInQ.Contrib.AbVarBC
open scoped CategoryTheory.Obj

variable {K : Type} [Field K]

/-- `bcPt` is natural for morphisms `φ : A → B` (adjunction naturality). -/
theorem bcPt_comp {L : Type} [Field L] [Algebra K L] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X)
    (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (p : (A.baseChange L).Pt Ω) :
    bcPt B Ω (p ≫ (Over.pullback (sK K L)).map φ) = bcPt A Ω p ≫ φ := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (p ≫ (Over.pullback (sK K L)).map φ) =
    ((ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p) ≫ φ
  have hnat := Adjunction.homEquiv_naturality_right_symm (Over.mapPullbackAdj (sK K L))
    (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X) φ
  erw [hnat]
  rw [Category.assoc]

/-- The left part of the trivial homomorphism `X → B` is the structure map followed by the unit. -/
theorem one_left (B : PkgI3.AbVar K) (X : Over (Spec (CommRingCat.of K))) :
    (1 : X ⟶ B.X).left = X.hom ≫ (η[B.X]).left := by
  show (toUnit X ≫ η[B.X]).left = _
  rw [Over.comp_left]
  congr 1

/-- **Kernel points descend**: for a finite `φ : A → B`, every point `Q ∈ ker φ(Ω₂)` comes from
`ker φ(K̄)` along a `K`-embedding `K̄ → Ω₂` (the scheme `ker φ` is finite over `K`). -/
theorem exists_ker_lift {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) [IsFinite φ.left]
    {Ω₂ : Type} [Field Ω₂] [Algebra K Ω₂] (κ : AlgebraicClosure K →ₐ[K] Ω₂) (Q : A.Pt Ω₂)
    (hQ : Q ≫ φ = 1) : ∃ P : A.Pt (AlgebraicClosure K), P ≫ φ = 1 ∧ extPt A κ P = Q := by
  let e := (η[B.X]).left
  let gZ := pullback.snd φ.left e
  haveI : IsFinite gZ := MorphismProperty.of_isPullback (P := @IsFinite)
    (IsPullback.of_hasPullback φ.left e) inferInstance
  have hQ' : Q.left ≫ φ.left = (PkgI3.AbVar.ptObj (K := K) Ω₂).hom ≫ e := by
    have := congrArg Over.Hom.left hQ
    rw [Over.comp_left, one_left] at this
    exact this
  let q : Spec (CommRingCat.of Ω₂) ⟶ pullback φ.left e := pullback.lift Q.left _ hQ'
  have hq : q ≫ gZ = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂)) := pullback.lift_snd _ _ _
  obtain ⟨p, hp1, hp2⟩ := exists_lift_of_isFinite κ gZ q hq
  have hunit : e ≫ B.X.hom = 𝟙 _ := Over.w (η[B.X])
  have hover : (p ≫ pullback.fst φ.left e) ≫ A.X.hom =
      (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).hom := by
    rw [Category.assoc, ← Over.w φ, ← Category.assoc (pullback.fst _ _), pullback.condition,
      Category.assoc, hunit, Category.comp_id]
    exact hp2
  refine ⟨Over.homMk (p ≫ pullback.fst φ.left e) hover, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, one_left]
    show (p ≫ pullback.fst φ.left e) ≫ φ.left = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (κ : AlgebraicClosure K →+* Ω₂)) ≫
      p ≫ pullback.fst φ.left e = Q.left
    rw [← Category.assoc, hp1]
    exact pullback.lift_fst _ _ _

/-- **`IsogenyBaseChangeDeg`, proved.** -/
theorem isogenyBaseChangeDeg : IsogenyBaseChangeDeg := by
  intro K _ _ A B φ hφ L _ _ _
  obtain ⟨hmon, hfin, hsurj⟩ := hφ
  haveI := hmon
  haveI := hfin
  let φ' : (A.baseChange L).X ⟶ (B.baseChange L).X := (Over.pullback (sK K L)).map φ
  refine ⟨φ', ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (inferInstance : IsMonHom ((Over.pullback (sK K L)).map φ))
  · exact MorphismProperty.of_isPullback (P := @IsFinite)
      (AlgebraicGeometry.overPullback_isPullback (sK K L) A.X B.X φ) hfin
  · exact MorphismProperty.of_isPullback (P := @Surjective)
      (AlgebraicGeometry.overPullback_isPullback (sK K L) A.X B.X φ) hsurj
  -- the degrees: `ker φ'(L̄) ≃ ker φ(L̄) ≃ ker φ(K̄)`
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have e1 : {P : PkgI3.AbVar.ptObj (K := L) (AlgebraicClosure L) ⟶ (A.baseChange L).X //
      P ≫ φ' = 1} ≃ {Q : A.Pt (AlgebraicClosure L) // Q ≫ φ = 1} :=
    { toFun := fun P => ⟨bcPt A (AlgebraicClosure L) P.1, by
        rw [← bcPt_comp, P.2, map_one]⟩
      invFun := fun Q => ⟨(bcPt A (AlgebraicClosure L)).symm Q.1, by
        apply (bcPt B (AlgebraicClosure L)).injective
        rw [bcPt_comp, MulEquiv.apply_symm_apply, Q.2, map_one]⟩
      left_inv := fun P => Subtype.ext (MulEquiv.symm_apply_apply _ _)
      right_inv := fun Q => Subtype.ext (MulEquiv.apply_symm_apply _ _) }
  have e2 : {P : A.Pt (AlgebraicClosure K) // P ≫ φ = 1} ≃
      {Q : A.Pt (AlgebraicClosure L) // Q ≫ φ = 1} :=
    Equiv.ofBijective (fun P => ⟨extPt A κ P.1, by
        rw [extPt_apply, Category.assoc, P.2]
        exact MonObj.comp_one _⟩)
      ⟨fun P P' h => Subtype.ext (extPt_injective A κ (congrArg Subtype.val h)),
       fun Q => by
        obtain ⟨P, hP, hPQ⟩ := exists_ker_lift φ κ Q.1 Q.2
        exact ⟨⟨P, hP⟩, Subtype.ext hPQ⟩⟩
  show Nat.card _ = Nat.card _
  exact (Nat.card_congr e1).trans (Nat.card_congr e2).symm

/-- **`faltingsLemma5BC` from the base-field form alone.** -/
theorem faltingsLemma5BC_final (hF : ZInQ.HeightSplit.FaltingsLemma5) :
    ZInQ.HeightSplit.FaltingsLemma5BC :=
  faltingsLemma5BC_of_base hF isogenyBaseChangeDeg

end IsogBC

/-! ## §18. The bundles: published-form leaves and the remaining glue, and all seven rows -/

/-- The published theorems used (each in printed form, or a specialization read off the display). -/
structure ReductLeaves : Prop where
  neronDVR : NeronSchemeModelExistsDVR
  sga7_3_5 : SemistableUnipotent
  sga7_4_7 : RaynaudSemistable
  sga7_3_6 : SemistableReductionDVR
  sga7_3_3a : SemistablePersistsDVR
  sga7_3_3b : IdentityComponentBaseChangeDVR
  serreTate2 : SerreTateThm2
  mumford : AvSplit.MumfordTorsionAlgClosed

/-- The remaining project glue (each with a docstring saying what it needs). -/
structure ReductGlue : Prop where
  fixedTorsionImperfect : FixedTorsionRationalImperfect
  localGlobal : SemistableLocalGlobal
  almostAll : SemistableAlmostAll
  ss2LocalGlobal : SemistableNeronBaseChangeLocalGlobal

/-- **All seven split rows** (t10 is not split; `faltingsLemma5BC` also uses the base-field form
`HeightSplit.FaltingsLemma5`). -/
theorem rows_of_leaves (l : ReductLeaves) (g : ReductGlue) (hF5 : ZInQ.HeightSplit.FaltingsLemma5) :
    PkgI2.RaynaudCriterion.{0} ∧ PkgI2.SerreTatePotentialGood.{0} ∧
      PkgI2.GrothendieckMonodromy.{0} ∧ ZInQ.HeightSplit.SemistableReductionThm ∧
      ZInQ.HeightSplit.SemistableNeronBaseChange ∧ ZInQ.HeightSplit.SemistablePersists ∧
      ZInQ.HeightSplit.FaltingsLemma5BC :=
  ⟨raynaudCriterion_final' l.sga7_4_7 l.sga7_3_5 l.neronDVR l.mumford g.fixedTorsionImperfect,
   serreTatePotentialGood_final l.serreTate2 l.mumford,
   grothendieckMonodromy_final' l.sga7_3_6 l.sga7_3_5 l.neronDVR l.mumford,
   semistableReductionThm_final l.sga7_3_6 l.sga7_3_3a l.neronDVR g.localGlobal g.almostAll,
   semistableNeronBaseChange_of_leaves l.sga7_3_3b g.localGlobal g.ss2LocalGlobal,
   semistablePersists_final l.sga7_3_3a l.neronDVR g.localGlobal,
   faltingsLemma5BC_final hF5⟩

/-! ## §19. Consistency: the local definitions at the zero abelian variety

As height-split §I for the global definitions: at `AbVar.zero K` (the only abelian variety Mathlib
can construct) `Spec O` is a Néron model, every Néron model is trivial, and the trivial group
scheme is semistable. So `HasSemistableReduction` (hypothesis of 3.5) is satisfiable and
`SemistableNeronModels` (conclusion of 3.6, 3.3, 4.7) holds there. The torus and abelian parts are
not exercised. -/

section ZeroLocal

open ZInQ.H5Neron

variable (K : Type) [Field K] (O : ValuationSubring K)

/-- `Spec O`, the trivial group model of `Spec K`. -/
noncomputable def trivModelO : GroupModelO (PkgI3.AbVar.zero K) O where
  G := 𝟙_ _
  smooth := by dsimp; infer_instance
  separated := by dsimp; infer_instance
  qc := by dsimp; infer_instance
  gen := (Functor.Monoidal.εIso (Over.pullback (jO O))).symm
  gen_hom := by
    letI : GrpObj ((Over.pullback (jO O)).obj (𝟙_ (Over (Spec (CommRingCat.of O))))) :=
      Functor.grpObjObj
    exact isMonHom_of_iso_unit (Iso.refl _) _

theorem trivModelO_isNeronModel : (trivModelO K O).IsNeronModel := by
  intro Y _
  refine ⟨fun f g _ => toUnit_unique _ _, fun g => ⟨toUnit Y, toUnit_unique _ _⟩⟩

/-- Every Néron model of `Spec K` over `O` is the trivial group scheme. -/
theorem neronO_zero_iso_unit (𝒩 : GroupModelO (PkgI3.AbVar.zero K) O) (h : 𝒩.IsNeronModel) :
    Nonempty (𝒩.G ≅ 𝟙_ _) := by
  have hsm : Smooth (𝟙_ (Over (Spec (CommRingCat.of O)))).hom := by dsimp; infer_instance
  obtain ⟨s, -⟩ := (@h (𝟙_ _) hsm).2 (toUnit _)
  refine ⟨⟨toUnit _, s, ?_, toUnit_unique _ _⟩⟩
  exact (h 𝒩.G).1 (toUnit_unique _ _)

theorem semistableNeronModels_zero : SemistableNeronModels (PkgI3.AbVar.zero K) O := by
  intro 𝒩 h𝒩
  obtain ⟨i⟩ := neronO_zero_iso_unit K O 𝒩 h𝒩
  exact ZInQ.HeightSplit.hasSemiAbelianIdentityComponent_of_iso_unit _
    ((Over.pullback _).mapIso i ≪≫ (Functor.Monoidal.εIso (Over.pullback _)).symm)

theorem hasSemistableReduction_zero : HasSemistableReduction (PkgI3.AbVar.zero K) O :=
  ⟨trivModelO K O, trivModelO_isNeronModel K O,
    semistableNeronModels_zero K O _ (trivModelO_isNeronModel K O)⟩

end ZeroLocal

end ReductSplit

#print axioms ReductSplit.raynaudCriterion_of_leaves
#print axioms ReductSplit.grothendieckMonodromy_of_leaves
#print axioms ReductSplit.serreTatePotentialGood_of_leaves
#print axioms ReductSplit.semistablePersists_of_leaves
#print axioms ReductSplit.semistableReductionThm_of_leaves
#print axioms ReductSplit.serreTatePotentialGood_of_printed
#print axioms ReductSplit.raynaudCriterion_final
#print axioms ReductSplit.grothendieckMonodromy_final
#print axioms ReductSplit.serreTatePotentialGood_final
#print axioms ReductSplit.semistableNeronBaseChange_of_leaves
#print axioms ReductSplit.faltingsLemma5BC_of_base
#print axioms ReductSplit.raynaudCriterion_final'
#print axioms ReductSplit.dvrComapFinite
#print axioms ReductSplit.semistablePersists_final
#print axioms ReductSplit.semistableReductionThm_final
#print axioms ReductSplit.dvrFiniteExtension
#print axioms ReductSplit.grothendieckMonodromy_final'
#print axioms ReductSplit.faltingsLemma5BC_final
#print axioms ReductSplit.rows_of_leaves
#print axioms ReductSplit.hasSemistableReduction_zero


open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

open NumberField

namespace ReductGlue
open ReductSplit

variable {K : Type} [Field K]

/-- A separable element of `K̄` fixed by `Aut(K̄/K)` lies in `K`. -/
theorem mem_range_of_isSeparable_of_fixed (a : AlgebraicClosure K) (ha : IsSeparable K a)
    (hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ a = a) :
    a ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
  let L := separableClosure K (AlgebraicClosure K)
  have haL : a ∈ L := (mem_separableClosure_iff).mpr ha
  let a' : L := ⟨a, haL⟩
  have : a' ∈ Set.range (algebraMap K L) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    apply Subtype.ext
    have h1 := AlgEquiv.liftNormal_commutes τ (AlgebraicClosure K) a'
    have h2 : (algebraMap L (AlgebraicClosure K)) a' = a := rfl
    rw [h2, hfix] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by rw [IsScalarTower.algebraMap_apply K L (AlgebraicClosure K), hc]; rfl⟩

example (A : PkgI3.AbVar K) : GeometricallyConnected A.X.hom :=
  ⟨fun _ _ _ _ _ _ h => by
    have := GeometricallyIrreducible.geometrically_irreducibleSpace (f := A.X.hom) _ _ _ h
    infer_instance⟩


/-- Elements in the image of an étale `K`-algebra in `K̄` are separable over `K`. -/
theorem isSeparable_of_etale {R : Type} [CommRing R] [Algebra K R] [Algebra.Etale K R]
    (f : R →ₐ[K] AlgebraicClosure K) (r : R) : IsSeparable K (f r) := by
  let E : IntermediateField K (AlgebraicClosure K) :=
    Subalgebra.toIntermediateField' f.range (Subalgebra.isField_of_algebraic _)
  let f' : R →ₐ[K] E := f.codRestrict E.toSubalgebra (fun r => ⟨r, rfl⟩)
  have hsurj : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    obtain ⟨r, hr⟩ : y ∈ f.range := hy
    exact ⟨r, Subtype.ext hr⟩
  have : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_surjective f' hsurj
  have : Algebra.FiniteType K E := Algebra.FiniteType.of_surjective f' hsurj
  have : Algebra.IsSeparable K E := Algebra.FormallyUnramified.isSeparable K E
  have h := Algebra.IsSeparable.isSeparable K (f' r)
  have h2 : IsSeparable K (E.val (f' r)) := IsSeparable.map E.val Subtype.val_injective h
  exact h2

theorem exists_rational_of_fixed_etale (X : Over (Spec (CommRingCat.of K)))
    [Etale X.hom] (q : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ X)
    (hq : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, PkgI3.AbVar.galHom σ ≫ q = q) :
    ∃ y : PkgI3.AbVar.ptObj (K := K) K ⟶ X,
      ZInQ.Contrib.AbVarBC.extHom (Algebra.ofId K (AlgebraicClosure K)) ≫ y = q := by
  classical
  let q0 : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ X.left := q.left
  have hq0 : q0 ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    Over.w q
  let p : X.left := q0 (IsLocalRing.closedPoint (AlgebraicClosure K))
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q0 ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : s = IsLocalRing.closedPoint (AlgebraicClosure K) :=
      Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure K)) _ _
    rw [this]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q0 hrange
  have hq' : q' ≫ U.ι = q0 := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of (AlgebraicClosure K) := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q0 = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq0]
  -- every `φ r` is fixed by `Aut(K̄/K)`
  have hfixφ : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      φ ≫ CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K) = φ := by
    intro σ
    have h1 := congrArg Over.Hom.left (hq σ)
    change Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ q0 =
      q0 at h1
    rw [hql, ← Category.assoc, ← Spec.map_comp] at h1
    have h2 := (cancel_mono (e.inv ≫ U.ι)).mp h1
    exact Spec.map_injective h2
  have hθet : RingHom.Etale θ.hom := by
    have : Etale (Spec.map θ) := by rw [hθ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  have : Algebra.Etale K Γ(X.left, U) := hθet
  let f : Γ(X.left, U) →ₐ[K] AlgebraicClosure K :=
    { φ.hom with
      commutes' := fun a => congrArg (fun g => CommRingCat.Hom.hom g a) hcomp }
  have hmem : ∀ r, φ.hom r ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    intro r
    refine mem_range_of_isSeparable_of_fixed _ (isSeparable_of_etale f r) fun σ => ?_
    exact congrArg (fun f => CommRingCat.Hom.hom f r) (hfixφ σ)
  choose c hc using hmem
  have hinj := (algebraMap K (AlgebraicClosure K)).injective
  let ψ : Γ(X.left, U) →+* K :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hc, map_mul, map_mul, hc, hc])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hc, map_add, map_add, hc, hc]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) = φ := by
    ext r
    exact hc r
  have hθψ : θ ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K K) := by
    ext a
    apply hinj
    have := congrArg (fun f => CommRingCat.Hom.hom f a) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this ⊢
    rw [show algebraMap K (AlgebraicClosure K) (ψ (θ.hom a)) = φ.hom (θ.hom a) from hc _, this]
    rfl
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ?_, ?_⟩
  · show (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K K))
    rw [Category.assoc, Category.assoc, ← hθ, ← Spec.map_comp, hθψ]
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom ((Algebra.ofId K (AlgebraicClosure K) : K →ₐ[K] _) :
        K →+* AlgebraicClosure K)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι = q0
    rw [hql, ← Category.assoc, ← Spec.map_comp]
    congr 2

theorem comp_pow_one (A : PkgI3.AbVar K) {Y : Over (Spec (CommRingCat.of K))} (x : Y ⟶ A.X) (n : ℕ) :
    x ≫ (𝟙 A.X ^ n : A.X ⟶ A.X) = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

instance geometricallyConnected_abVar (A : PkgI3.AbVar K) : GeometricallyConnected A.X.hom :=
  ⟨fun _ _ _ _ _ _ h => by
    have := GeometricallyIrreducible.geometrically_irreducibleSpace (f := A.X.hom) _ _ _ h
    infer_instance⟩

/-- **`FixedTorsionRational` (all fields, perfect or not) from the bundle leaf
`MulEtaleAbelianScheme`** (BLR 7.3/2: `[m]` is étale for `m` invertible). The `m`-torsion
`A[m] = [m]⁻¹(0)` is étale over `K`; a `K̄`-point of an étale `K`-scheme fixed by `Aut(K̄/K)` is
`K`-rational (`exists_rational_of_fixed_etale`). -/
theorem fixedTorsionRational_of_mulEtale (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    FixedTorsionRational := by
  intro K _ A m hm hfix x hx
  haveI : PkgI2.IsAbelianScheme (Grp.mk A.X) := ⟨inferInstanceAs (IsProper A.X.hom),
    inferInstanceAs (Smooth A.X.hom), inferInstanceAs (GeometricallyConnected A.X.hom)⟩
  have het : Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) :=
    hE K (Grp.mk A.X) m (isUnit_iff_ne_zero.mpr hm)
  let M : A.X ⟶ A.X := 𝟙 A.X ^ m
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd M.left (η[A.X]).left)
  haveI : Etale P.hom := by
    change Etale (pullback.snd M.left (η[A.X]).left)
    infer_instance
  have hxm : x ≫ M = 1 := by rw [comp_pow_one]; exact hx
  have hw : x.left ≫ M.left =
      (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).hom ≫ (η[A.X]).left := by
    have h1 := congrArg Over.Hom.left hxm
    rw [Over.comp_left] at h1
    rw [h1]
    change (toUnit _ ≫ η[A.X]).left = _
    rw [Over.comp_left]
    congr 1
  let x' : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ P :=
    Over.homMk (pullback.lift x.left _ hw) (by simp [P])
  have hfix' : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      PkgI3.AbVar.galHom σ ≫ x' = x' := by
    intro σ
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_fst]
      exact congrArg Over.Hom.left (hfix σ x hx)
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_snd]
      exact Over.w (PkgI3.AbVar.galHom σ)
  obtain ⟨y', hy'⟩ := exists_rational_of_fixed_etale P x' hfix'
  have hpr : pullback.fst M.left (η[A.X]).left ≫ A.X.hom = P.hom := by
    change _ = pullback.snd M.left (η[A.X]).left
    rw [← Over.w M, ← Category.assoc, pullback.condition, Category.assoc, Over.w η[A.X]]
    simp
  let pr : P ⟶ A.X := Over.homMk (pullback.fst M.left (η[A.X]).left) hpr
  refine ⟨y' ≫ pr, ?_⟩
  change ZInQ.Contrib.AbVarBC.extHom _ ≫ y' ≫ pr = x
  rw [← Category.assoc, hy']
  apply Over.OverMorphism.ext
  simp [x', pr]

/-- **GLUE `FixedTorsionRationalImperfect` (reduct-split), PROVED** from the bundle leaf. -/
theorem fixedTorsionRationalImperfect_of_mulEtale (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    FixedTorsionRationalImperfect :=
  fun K _ _ A m hm hfix x hx => fixedTorsionRational_of_mulEtale hE K A m hm hfix x hx

/-- **r6 `PkgI2.RaynaudCriterion` from published-form leaves only** (over every field). -/
theorem raynaudCriterion_leaves (hR : RaynaudSemistable) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVR) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : PkgI2.RaynaudCriterion.{0} :=
  raynaudCriterion_final hR hU hN hM (fixedTorsionRational_of_mulEtale hE)


section DVRNumberField

variable {L : Type} [Field L] [NumberField L]

/-- Every valuation ring of a number field contains `𝓞_L` (it is integrally closed). -/
theorem int_mem (O : ValuationSubring L) (x : 𝓞 L) : (x : L) ∈ O := by
  have h1 : IsIntegral ℤ (x : L) := x.2
  have h2 : IsIntegral O (x : L) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

/-- `𝓞_L → O`. -/
def toOL (O : ValuationSubring L) : 𝓞 L →+* O :=
  (algebraMap (𝓞 L) L).codRestrict O.toSubring (fun x => int_mem O x)

@[simp] theorem toOL_coe (O : ValuationSubring L) (x : 𝓞 L) : ((toOL O x : O) : L) = (x : L) := rfl

/-- The center `𝔭_O = 𝓞_L ∩ 𝔪_O`. -/
def center (O : ValuationSubring L) : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal O).comap (toOL O)

theorem isUnit_toOL (O : ValuationSubring L) {s : 𝓞 L} (hs : s ∉ center O) : IsUnit (toOL O s) := by
  by_contra h
  exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)

theorem center_isMaximal (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    (center O).IsMaximal := by
  have hp : (center O).IsPrime := Ideal.comap_isPrime _ _
  refine hp.isMaximal ?_
  intro hbot
  apply IsDiscreteValuationRing.not_isField O
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
  -- every element of `L` lies in `O`
  have hall : ∀ z : L, z ∈ O := by
    intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) z
    have hy0 : y ∉ center O := by
      rw [hbot, Ideal.mem_bot]; exact nonZeroDivisors.ne_zero hy
    obtain ⟨u, hu⟩ := isUnit_toOL O hy0
    have h1 : ((u : O) : L) = algebraMap (𝓞 L) L y := by rw [hu]; rfl
    have h2 : (((u⁻¹ : Oˣ) : O) : L) * ((u : O) : L) = 1 := by
      exact congrArg (fun z : O => (z : L)) (Units.inv_mul u)
    rw [h1] at h2
    rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_left h2]
    exact mul_mem (int_mem O x) (u⁻¹ : Oˣ).1.2
  have ha0 : (a : L) ≠ 0 := fun h => ha (Subtype.ext h)
  refine ⟨⟨(a : L)⁻¹, hall _⟩, Subtype.ext ?_⟩
  change (a : L) * (a : L)⁻¹ = 1
  exact mul_inv_cancel₀ ha0

theorem mem_of_mul_eq (O : ValuationSubring L) {x : L} {a s : 𝓞 L} (hs : s ∉ center O)
    (h : x * (s : L) = a) : x ∈ O := by
  obtain ⟨u, hu⟩ := isUnit_toOL O hs
  have h1 : ((u : O) : L) = (s : L) := by rw [hu]; rfl
  have h2 : (((u⁻¹ : Oˣ) : O) : L) * ((u : O) : L) = 1 :=
    congrArg (fun z : O => (z : L)) (Units.inv_mul u)
  have : x = (a : L) * (((u⁻¹ : Oˣ) : O) : L) := by
    rw [← h, h1.symm, _root_.mul_assoc, mul_comm ((u : O) : L), h2, _root_.mul_one]
  rw [this]
  exact mul_mem (int_mem O a) (u⁻¹ : Oˣ).1.2

theorem center_ne_bot (O : ValuationSubring L) [IsDiscreteValuationRing O] : center O ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (center_isMaximal O) (RingOfIntegers.not_isField L)

/-- **A discrete valuation ring of a number field is the localization of `𝓞_L` at its center**:
`x ∈ O` iff `x = a/s` with `a, s ∈ 𝓞_L`, `s ∉ 𝔭_O`. Proof: `(𝓞_L)_𝔭 ⊆ O` is a valuation ring;
for `x = a/b ∈ O`, either `x` or `x⁻¹` is `r/s`, and `x⁻¹ = r/s` with `r ∈ 𝔭` would put
`1 = x·x⁻¹` in `𝔪_O`. -/
theorem mem_iff_exists (O : ValuationSubring L) [IsDiscreteValuationRing O] (x : L) :
    x ∈ O ↔ ∃ a s : 𝓞 L, s ∉ center O ∧ x * (s : L) = a := by
  constructor
  swap
  · rintro ⟨a, s, hs, h⟩; exact mem_of_mul_eq O hs h
  intro hx
  haveI := center_isMaximal O
  let 𝔭 := center O
  let B := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) (center_ne_bot O) B
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hb0 : (algebraMap (𝓞 L) L b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr (nonZeroDivisors.ne_zero hb)
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap (𝓞 L) B a) (algebraMap (𝓞 L) B b)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl c
  have hinj := IsLocalization.injective B 𝔭.primeCompl_le_nonZeroDivisors
  have hspec := IsLocalization.mk'_spec B r s
  have hs : (s : 𝓞 L) ∉ center O := s.2
  rcases hc with h | h
  · have h' : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    have hL : (algebraMap (𝓞 L) L a) * (algebraMap (𝓞 L) L r) =
        (algebraMap (𝓞 L) L b) * (algebraMap (𝓞 L) L s) := by
      rw [← map_mul, ← map_mul, h']
    by_cases hr : r ∈ 𝔭
    · exfalso
      apply hs
      have hX : (⟨_, hx⟩ : O) * toOL O r = toOL O s := by
        apply Subtype.ext
        change (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b) * (algebraMap (𝓞 L) L r) =
          algebraMap (𝓞 L) L s
        rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
      change toOL O s ∈ IsLocalRing.maximalIdeal O
      rw [← hX]
      exact Ideal.mul_mem_left _ _ hr
    · refine ⟨s, r, hr, ?_⟩
      change (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b) * (algebraMap (𝓞 L) L r) =
        algebraMap (𝓞 L) L s
      rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
  · have h' : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    refine ⟨r, s, hs, ?_⟩
    change (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b) * (algebraMap (𝓞 L) L s) =
      algebraMap (𝓞 L) L r
    rw [div_mul_eq_mul_div, ← map_mul, ← h', map_mul, mul_div_cancel_left₀ _ hb0]

/-- Two discrete valuation rings of `L` with the same center are equal. -/
theorem eq_of_center_eq {O₁ O₂ : ValuationSubring L} [IsDiscreteValuationRing O₁]
    [IsDiscreteValuationRing O₂] (h : center O₁ = center O₂) : O₁ = O₂ := by
  ext x
  rw [mem_iff_exists, mem_iff_exists, h]

instance (O : ValuationSubring L) : (center O).IsPrime := Ideal.comap_isPrime _ _

/-- `(𝓞_L)_𝔭 → O` for `𝔭` the center of `O`. -/
noncomputable def locToO (O : ValuationSubring L) : Localization.AtPrime (center O) →+* O :=
  IsLocalization.lift (M := (center O).primeCompl) (g := toOL O) (fun s => isUnit_toOL O s.2)

instance (O : ValuationSubring L) : IsLocalHom (locToO O) := by
  constructor
  intro y hy
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (center O).primeCompl y
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro hr
  have h1 : locToO O (IsLocalization.mk' _ r s) * toOL O s = toOL O r := by
    rw [mul_comm]
    exact ((IsLocalization.lift_mk'_spec _ _ _ _).mp rfl).symm
  have h2 : toOL O r ∈ IsLocalRing.maximalIdeal O := hr
  rw [← h1] at h2
  exact (IsLocalRing.mem_maximalIdeal _).mp
    ((Ideal.IsPrime.mem_or_mem inferInstance h2).resolve_right s.2) hy

/-- **The residue fields of `𝓞_L` at `𝔭_O` and of `O` agree.** -/
noncomputable def resIso (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    (center O).ResidueField ≃+* IsLocalRing.ResidueField O :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map (locToO O)) ⟨RingHom.injective _, by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, s, hs, h⟩ := (mem_iff_exists O (y : L)).mp y.2
    refine ⟨IsLocalRing.residue _ (IsLocalization.mk' _ a (⟨s, show s ∈ (center O).primeCompl from hs⟩ : (center O).primeCompl)), ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    unfold locToO
    rw [IsLocalization.lift_mk'_spec]
    apply Subtype.ext
    change (a : L) = (s : L) * (y : L)
    rw [← h, mul_comm]⟩

theorem resIso_algebraMap (O : ValuationSubring L) [IsDiscreteValuationRing O] (a : 𝓞 L) :
    resIso O (algebraMap (𝓞 L) (center O).ResidueField a) = IsLocalRing.residue O (toOL O a) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) (Localization.AtPrime (center O))]
  change IsLocalRing.ResidueField.map (locToO O) (IsLocalRing.residue _ _) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 1
  exact IsLocalization.lift_eq _ a

/-- The isomorphism `κ̄(𝔭_O) ≅ κ̄(O)` of the chosen algebraic closures, over `𝓞_L`. -/
noncomputable def barIso (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    ZInQ.HeightSplit.ResBar (center O) ≃+* ResBarO O :=
  IsAlgClosure.equivOfEquiv _ _ (resIso O)

theorem barIso_comp (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    ((barIso O : _ →+* _).comp (algebraMap (𝓞 L) (ZInQ.HeightSplit.ResBar (center O)))) =
      (algebraMap O (ResBarO O)).comp (toOL O) := by
  ext a
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (𝓞 L) (center O).ResidueField]
  have := congrArg (fun f => f (algebraMap (𝓞 L) (center O).ResidueField a))
    (IsAlgClosure.equivOfEquiv_comp_algebraMap (ZInQ.HeightSplit.ResBar (center O)) (ResBarO O)
      (resIso O))
  simp only [RingHom.comp_apply] at this
  change barIso O _ = _ at this
  change barIso O _ = _
  rw [this]
  change algebraMap (IsLocalRing.ResidueField O) (ResBarO O) (resIso O _) = _
  rw [resIso_algebraMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply O
    (IsLocalRing.ResidueField O) (ResBarO O)]
  rfl

open IsDedekindDomain in
/-- The valuation ring of the `𝔭`-adic valuation, for a maximal ideal `𝔭` of `𝓞_L`. -/
noncomputable def dvrAt (𝔭 : Ideal (𝓞 L)) [h𝔭 : 𝔭.IsMaximal] : ValuationSubring L :=
  ((⟨𝔭, h𝔭.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField L)⟩ :
    HeightOneSpectrum (𝓞 L)).valuation L).valuationSubring

open IsDedekindDomain in
instance (𝔭 : Ideal (𝓞 L)) [h𝔭 : 𝔭.IsMaximal] : IsDiscreteValuationRing (dvrAt 𝔭) := by
  set v : HeightOneSpectrum (𝓞 L) :=
    ⟨𝔭, h𝔭.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField L)⟩
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
  haveI : Nontrivial (v.valuation L).valueGroup := by
    have h0 : v.valuation L π ≠ 0 := by rw [hπ]; exact WithZero.coe_ne_zero
    refine ⟨⟨⟨Units.mk0 _ h0, MonoidWithZeroHom.mem_valueGroup _ ⟨π, rfl⟩⟩, 1, ?_⟩⟩
    intro h
    have := congrArg (fun u : (v.valuation L).valueGroup => ((u : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))) h
    simp only [Units.val_mk0, OneMemClass.coe_one, Units.val_one] at this
    rw [hπ] at this
    exact absurd this (by decide)
  exact Valuation.valuationSubring_isDiscreteValuationRing _

open IsDedekindDomain in
theorem center_dvrAt (𝔭 : Ideal (𝓞 L)) [h𝔭 : 𝔭.IsMaximal] : center (dvrAt 𝔭) = 𝔭 := by
  set v : HeightOneSpectrum (𝓞 L) :=
    ⟨𝔭, h𝔭.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField L)⟩
  ext a
  change toOL _ a ∈ IsLocalRing.maximalIdeal _ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hlt := v.valuation_lt_one_iff_mem (K := L) a
  change _ ↔ a ∈ v.asIdeal
  rw [← hlt]
  constructor
  · intro hnu
    rcases (v.valuation_le_one (K := L) a).lt_or_eq with h | h
    · exact h
    · exfalso; apply hnu
      have hv : v.valuation L (algebraMap (𝓞 L) L a) ≠ 0 := by rw [h]; exact one_ne_zero
      have ha0 : (a : L) ≠ 0 := (Valuation.ne_zero_iff _).mp hv
      refine ⟨⟨toOL _ a, ⟨(a : L)⁻¹, ?_⟩, ?_, ?_⟩, rfl⟩
      · change v.valuation L (a : L)⁻¹ ≤ 1
        rw [map_inv₀]
        change (v.valuation L (algebraMap (𝓞 L) L a))⁻¹ ≤ 1
        rw [h, inv_one]
      · exact Subtype.ext (mul_inv_cancel₀ ha0)
      · exact Subtype.ext (inv_mul_cancel₀ ha0)
  · rintro hlt1 ⟨u, hu⟩
    have h1 : ((u : dvrAt 𝔭) : L) * (((u⁻¹ : (dvrAt 𝔭)ˣ) : dvrAt 𝔭) : L) = 1 :=
      congrArg (fun z : dvrAt 𝔭 => (z : L)) (Units.mul_inv u)
    have h2 : v.valuation L (((u⁻¹ : (dvrAt 𝔭)ˣ) : dvrAt 𝔭) : L) ≤ 1 := (u⁻¹ : (dvrAt 𝔭)ˣ).1.2
    rw [hu] at h1
    have h3 := congrArg (v.valuation L) h1
    rw [map_mul, map_one] at h3
    have : v.valuation L (a : L) * v.valuation L (((u⁻¹ : (dvrAt 𝔭)ˣ) : dvrAt 𝔭) : L) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt1
    exact absurd h3 (ne_of_lt this)

end DVRNumberField


section AbSchemeNeron

variable {K : Type} [Field K]

/-- **An abelian scheme over a discrete valuation ring has the Néron mapping property** (BLR §1.2
Prop. 8), from the vendored FLT-project theorem in `Contrib/CloudW03NeronSurj` (Weil's extension
theorem; full mapping property for smooth test schemes). -/
theorem abelianScheme_neron (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 : Grp (Over (Spec (.of O)))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (Y : Over (Spec (CommRingCat.of O))) [hY : Smooth Y.hom] :
    Function.Bijective fun f : Y ⟶ 𝒜.X => (Over.pullback (jO O)).map f := by
  haveI : Smooth 𝒜.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper 𝒜.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : GeometricallyConnected 𝒜.X.hom := PkgI2.IsAbelianScheme.geomConnected
  haveI : GrpObj (Over.mk 𝒜.X.hom) := by
    change GrpObj 𝒜.X
    infer_instance
  let h𝒜' : ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle O
      𝒜.X.hom :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => 𝒜.X.hom.isConnected_preimage_singleton s
      hasGroupLaw := ⟨ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.relativeGroupLawOfGrpObj
        O 𝒜.X.hom⟩ }
  have hN := ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.solution
    O K h𝒜'
  have hb := hN.neronMapping Y.left Y.hom hY
  constructor
  · intro f g hfg
    have h1 : (ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.genericFibreRestrict O K 𝒜.X.hom
        Y.hom ⟨f.left, Over.w f⟩) =
        ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.genericFibreRestrict O K 𝒜.X.hom
        Y.hom ⟨g.left, Over.w g⟩ := by
      apply Subtype.ext
      exact congrArg Over.Hom.left hfg
    have := hb.1 h1
    exact Over.OverMorphism.ext (congrArg Subtype.val this)
  · intro uK
    let uK' : ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.SchemeHomOver
        (pullback.snd Y.hom (ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.specGenericFibreInclusion O K))
        (pullback.snd 𝒜.X.hom (ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.specGenericFibreInclusion O K)) :=
      ⟨uK.left, Over.w uK⟩
    obtain ⟨φ, hφ⟩ := hb.2 uK'
    refine ⟨Over.homMk φ.1 φ.2, ?_⟩
    ext1
    exact congrArg Subtype.val hφ

end AbSchemeNeron


section SemiAbelian

open ZInQ.HeightSplit

/-- `HasSemiAbelianIdentityComponent` is invariant under isomorphisms of group schemes. -/
theorem hasSemiAbelian_of_iso {k : Type} [Field k] {G G' : Over (Spec (CommRingCat.of k))}
    [GrpObj G] [GrpObj G'] (f : G ≅ G') [IsMonHom f.hom] (h : HasSemiAbelianIdentityComponent G) :
    HasSemiAbelianIdentityComponent G' := by
  obtain ⟨U, hU, inc, h1, h2, h3, rest⟩ := h
  exact ⟨U, hU, inc ≫ f.hom, by rw [Over.comp_left]; infer_instance, inferInstance, h3, rest⟩

/-- An abelian variety (over any field) has semi-abelian identity component: `U = G`, `π = 𝟙`,
torus of rank `0`. -/
theorem hasSemiAbelian_of_abVar {k : Type} [Field k] (B : PkgI3.AbVar k) :
    HasSemiAbelianIdentityComponent B.X := by
  haveI : GeometricallyConnected B.X.hom := geometricallyConnected_abVar B
  haveI : ConnectedSpace B.X.left := GeometricallyConnected.connectedSpace_of_subsingleton B.X.hom
  refine ⟨B.X, inferInstance, 𝟙 _, inferInstance, inferInstance, inferInstance, B, 𝟙 _,
    inferInstance, inferInstance, inferInstance, 0, fun R _ _ => 1, ?_, ?_, ?_⟩
  · intro R _ _ a b _
    exact Subsingleton.elim a b
  · intro R _ _ u
    rw [Category.comp_id, MonoidHom.range_one, Subgroup.mem_bot]
  · intro R S _ _ _ _ f t
    exact (MonObj.comp_one _).symm

end SemiAbelian

section GoodRed

variable {K : Type} [Field K]

/-- The group model over `O` given by an abelian scheme with generic fibre `≅ A`. -/
noncomputable def groupModelOfAbScheme (O : ValuationSubring K) (A : PkgI3.AbVar K)
    (𝒜 : Grp (Over (Spec (.of O)))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅
      Grp.mk A.X) : GroupModelO A O :=
  haveI : Smooth 𝒜.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper 𝒜.X.hom := PkgI2.IsAbelianScheme.proper
  { G := 𝒜.X
    gen := (Grp.forget _).mapIso e
    gen_hom := inferInstanceAs (IsMonHom e.hom.hom.hom) }

/-- **Good reduction ⇒ semistable reduction**: an abelian scheme over a DVR is a Néron model
(`abelianScheme_neron`), and its geometric special fibre is an abelian variety (smooth, proper,
geometrically connected ⇒ geometrically integral, `FrobPieces.smoothGeomConnIntegral`). -/
theorem hasSemistableReduction_of_goodReduction (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (h : PkgI2.HasGoodReduction (Grp.mk A.X) O) :
    HasSemistableReduction A O := by
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := h
  haveI := h𝒜
  haveI : Smooth 𝒜.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper 𝒜.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : GeometricallyConnected 𝒜.X.hom := PkgI2.IsAbelianScheme.geomConnected
  refine ⟨groupModelOfAbScheme O A 𝒜 e, ?_, ?_⟩
  · intro Y _
    have hb := abelianScheme_neron O 𝒜 Y
    have : (fun f : Y ⟶ 𝒜.X => (Over.pullback (jO O)).map f ≫ ((Grp.forget _).mapIso e).hom) =
        (fun g => g ≫ ((Grp.forget _).mapIso e).hom) ∘
          (fun f : Y ⟶ 𝒜.X => (Over.pullback (jO O)).map f) := rfl
    change Function.Bijective (fun f : Y ⟶ 𝒜.X =>
      (Over.pullback (jO O)).map f ≫ ((Grp.forget _).mapIso e).hom)
    rw [this]
    exact Function.Bijective.comp
      ⟨fun a b hab => (cancel_mono _).mp hab, fun c => ⟨c ≫ ((Grp.forget _).mapIso e).inv, by
        simp only; rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩⟩ hb
  · let G := geomSpecialFibre (groupModelOfAbScheme O A 𝒜 e)
    haveI hs : Smooth G.hom := by
      change Smooth (pullback.snd 𝒜.X.hom _); infer_instance
    haveI hp : IsProper G.hom := by
      change IsProper (pullback.snd 𝒜.X.hom _); infer_instance
    haveI hc : GeometricallyConnected G.hom := by
      change GeometricallyConnected (pullback.snd 𝒜.X.hom _); infer_instance
    haveI : GeometricallyIntegral G.hom :=
      FrobPieces.smoothGeomConnIntegral _ G.left G.hom hs hc inferInstance
    let B : PkgI3.AbVar (ResBarO O) := ⟨G⟩
    exact hasSemiAbelian_of_abVar B

end GoodRed

section AlmostAll

variable {K : Type} [Field K] [NumberField K]

open IsDedekindDomain in
/-- Only finitely many discrete valuation rings of `K` have a given nonzero `f ∈ 𝓞_K` in their
center. -/
theorem finite_dvr_mem_center {f : 𝓞 K} (hf : f ≠ 0) :
    {O : ValuationSubring K | IsDiscreteValuationRing O ∧ f ∈ center O}.Finite := by
  classical
  have hT := Ideal.finite_factors (R := 𝓞 K) (I := Ideal.span {f})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  let F : ValuationSubring K → Ideal (𝓞 K) := center
  refine Set.Finite.of_finite_image (f := F) ?_ ?_
  · refine (hT.image HeightOneSpectrum.asIdeal).subset ?_
    rintro _ ⟨O, ⟨hO, hfO⟩, rfl⟩
    haveI := hO
    refine ⟨⟨center O, inferInstance, center_ne_bot O⟩, ?_, rfl⟩
    change center O ∣ Ideal.span {f}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hfO
  · rintro O₁ ⟨h₁, -⟩ O₂ ⟨h₂, -⟩ h
    haveI := h₁; haveI := h₂
    exact eq_of_center_eq h

set_option synthInstance.maxHeartbeats 400000 in
/-- **GLUE `SemistableAlmostAll` (reduct-split), PROVED** from neron-lg's N1-g1 `AbVarSpreadsOut`
(itself proved in the kernel from the EGA IV leaves, `abVarSpreadsOut_of_ega4`) and frob-pieces'
leaf candidate `ProperSmoothGenConnected` (Zariski's connectedness theorem): spread `A` out to an
abelian scheme over `𝓞_K[1/f]`; at a DVR `O` with `f ∉ 𝔭_O`, `𝓞_K[1/f] → K` factors through `O`,
so `A` has good reduction at `O` (`hasGoodReduction_of_base`), hence semistable reduction
(`hasSemistableReduction_of_goodReduction`); only finitely many `O` have `f ∈ 𝔭_O`. -/
theorem semistableAlmostAll_of (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected) : SemistableAlmostAll := by
  intro K _ _ A
  obtain ⟨f, hf0, hf⟩ := hsp K A
  have hfL : IsUnit (algebraMap (𝓞 K) K f) :=
    isUnit_iff_ne_zero.2 (by simpa using hf0)
  let R := Localization.Away f
  letI : Algebra R K := (IsLocalization.Away.lift f hfL).toAlgebra
  haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.Away.lift_eq f hfL x).symm)
  obtain ⟨G, hG, hGs, hGp, gen, hgen⟩ := hf R
  have hgc : GeometricallyConnected G.hom := by
    refine hc K f R G hGs hGp ?_
    have h1 : GeometricallyConnected A.X.hom := geometricallyConnected_abVar A
    have h2 : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).hom =
        gen.hom.left ≫ A.X.hom := (Over.w gen.hom).symm
    rw [h2]
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{0}) gen.hom.left A.X.hom).2 h1
  refine (finite_dvr_mem_center hf0).subset ?_
  rintro O ⟨hO, hbad⟩
  refine ⟨hO, ?_⟩
  by_contra hfO
  haveI := hO
  apply hbad
  have hfu : IsUnit (toOL O f) := isUnit_toOL O hfO
  let φ : R →+* O := IsLocalization.Away.lift f hfu
  have hφ : (algebraMap O K).comp φ = algebraMap R K := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, φ, IsLocalization.Away.lift_eq]
    exact (IsLocalization.Away.lift_eq f hfL x).symm
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G) :=
    Functor.grpObjObj
  exact hasSemistableReduction_of_goodReduction O A
    (FrobPiecesNeron.hasGoodReduction_of_base _ (algebraMap R K) φ hφ _ (Grp.mk G) ⟨hGp, hGs, hgc⟩
      (Grp.mkIso' gen))

end AlmostAll


/-- The underlying isomorphism of an isomorphism of group objects. -/
def isoX {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : Grp C} (E : G ≅ H) :
    G.X ≅ H.X := (Grp.forget C).mapIso E

instance {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : Grp C} (E : G ≅ H) :
    IsMonHom (isoX E).hom := inferInstanceAs (IsMonHom E.hom.hom.hom)

section NeronUnique

variable {K : Type} [Field K]

/-- **Uniqueness of Néron models over a valuation ring**, as group schemes (from the mapping
property: the comparison maps are inverse, and postcomposition with them is a homomorphism on
`T`-points for every smooth `T`, in particular for `T = 𝟙_` and `T = 𝒩 ⊗ 𝒩`). -/
theorem neronO_unique {B : PkgI3.AbVar K} {O : ValuationSubring K} (𝒩₁ 𝒩₂ : GroupModelO B O)
    (h₁ : 𝒩₁.IsNeronModel) (h₂ : 𝒩₂.IsNeronModel) : ∃ e : 𝒩₁.G ≅ 𝒩₂.G, IsMonHom e.hom := by
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj 𝒩₁.G) := Functor.grpObjObj
  letI : GrpObj (F.obj 𝒩₂.G) := Functor.grpObjObj
  haveI := 𝒩₁.gen_hom
  haveI := 𝒩₂.gen_hom
  obtain ⟨f12, hf12⟩ := (h₂ 𝒩₁.G).2 𝒩₁.gen.hom
  obtain ⟨f21, hf21⟩ := (h₁ 𝒩₂.G).2 𝒩₂.gen.hom
  simp only at hf12 hf21
  have e1 : f12 ≫ f21 = 𝟙 _ := (h₁ 𝒩₁.G).1 (by
    simp only
    rw [Functor.map_comp, Category.assoc, hf21, hf12, CategoryTheory.Functor.map_id, Category.id_comp])
  have e2 : f21 ≫ f12 = 𝟙 _ := (h₂ 𝒩₂.G).1 (by
    simp only
    rw [Functor.map_comp, Category.assoc, hf12, hf21, CategoryTheory.Functor.map_id, Category.id_comp])
  -- postcomposition with `f12` on `T`-points, `T` smooth
  have key : ∀ (T : Over (Spec (CommRingCat.of O))) [Smooth T.hom] (a : T ⟶ 𝒩₁.G),
      F.map (a ≫ f12) ≫ 𝒩₂.gen.hom = F.map a ≫ 𝒩₁.gen.hom := by
    intro T _ a
    rw [Functor.map_comp, Category.assoc, hf12]
  have hmul : ∀ (T : Over (Spec (CommRingCat.of O))) [Smooth T.hom] (a b : T ⟶ 𝒩₁.G),
      (a * b) ≫ f12 = a ≫ f12 * b ≫ f12 := by
    intro T _ a b
    apply (h₂ T).1
    simp only
    rw [key, Functor.map_mul, Functor.map_mul, MonObj.mul_comp, MonObj.mul_comp, key, key]
  have hone : ∀ (T : Over (Spec (CommRingCat.of O))) [Smooth T.hom],
      (1 : T ⟶ 𝒩₁.G) ≫ f12 = 1 := by
    intro T _
    apply (h₂ T).1
    simp only
    rw [key, Functor.map_one, Functor.map_one, MonObj.one_comp, MonObj.one_comp]
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of O)))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (𝒩₁.G ⊗ 𝒩₁.G).hom :=
    ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  refine ⟨⟨f12, f21, e1, e2⟩, ⟨?_, ?_⟩⟩
  · change η[𝒩₁.G] ≫ f12 = η[𝒩₂.G]
    rw [MonObj.one_eq_one, MonObj.one_eq_one, hone]
  · change μ[𝒩₁.G] ≫ f12 = (f12 ⊗ₘ f12) ≫ μ[𝒩₂.G]
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, hmul, MonObj.comp_mul]
    simp

/-- Semistability transfers along an isomorphism of group models over `O`. -/
theorem isSemistable_of_iso {B : PkgI3.AbVar K} {O : ValuationSubring K} (𝒩₁ 𝒩₂ : GroupModelO B O)
    (e : 𝒩₁.G ≅ 𝒩₂.G) (he : IsMonHom e.hom) (h : 𝒩₁.IsSemistable) : 𝒩₂.IsSemistable := by
  let P := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))
  haveI := he
  let E : P.mapGrp.obj (Grp.mk 𝒩₁.G) ≅ P.mapGrp.obj (Grp.mk 𝒩₂.G) :=
    P.mapGrp.mapIso (Grp.mkIso' e)
  exact @hasSemiAbelian_of_iso _ _ (geomSpecialFibre 𝒩₁) (geomSpecialFibre 𝒩₂) _ _ (isoX E)
    (inferInstanceAs (IsMonHom E.hom.hom.hom)) h

/-- Semistable reduction (some Néron model) gives all Néron models semistable. -/
theorem semistableNeronModels_of_has {B : PkgI3.AbVar K} {O : ValuationSubring K}
    (h : HasSemistableReduction B O) : SemistableNeronModels B O := by
  obtain ⟨𝒩, h𝒩, hs⟩ := h
  intro 𝒩' h𝒩'
  obtain ⟨e, he⟩ := neronO_unique 𝒩 𝒩' h𝒩 h𝒩'
  exact isSemistable_of_iso 𝒩 𝒩' e he hs

end NeronUnique

section LocalGlobal

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- `(F_f ∘ F_g)(𝒢) ≅ F_h(𝒢)` for `f ≫ g = h`, as group objects (`F_• = Over.pullback •`). -/
noncomputable def pbCompIso {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hfg : f ≫ g = h) (𝒢 : Grp (Over Z)) :
    (Over.pullback f).mapGrp.obj ((Over.pullback g).mapGrp.obj 𝒢) ≅
      (Over.pullback h).mapGrp.obj 𝒢 :=
  (Functor.mapGrpCompIso.app 𝒢).symm ≪≫
    (Functor.mapGrpNatIso (Over.pullbackComp f g).symm).app 𝒢 ≪≫
    (Functor.mapGrpNatIso (eqToIso (show Over.pullback (f ≫ g) = Over.pullback h by rw [hfg]))).app 𝒢

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec O → Spec 𝓞_L`. -/
noncomputable abbrev gO (O : ValuationSubring L) : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (toOL O))

theorem jO_gO (O : ValuationSubring L) :
    jO O ≫ gO O = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
  rw [← Spec.map_comp]
  rfl

/-- **The base change `𝒩 ×_{𝓞_L} O` of a group model over `𝓞_L` to a valuation ring `O` of `L`**,
as a group model of `A_L` over `O` (generic fibre identified through `𝒩.gen`). -/
noncomputable def toO (𝒩 : GroupModel A L) (O : ValuationSubring L) : GroupModelO (A.baseChange L) O where
  G := (Over.pullback (gO O)).obj 𝒩.G
  grp := Functor.grpObjObj
  smooth := by change Smooth (pullback.snd 𝒩.G.hom (gO O)); infer_instance
  separated := by change IsSeparated (pullback.snd 𝒩.G.hom (gO O)); infer_instance
  qc := by change QuasiCompact (pullback.snd 𝒩.G.hom (gO O)); infer_instance
  gen := isoX (pbCompIso (jO O) (gO O) _ (jO_gO O) (Grp.mk 𝒩.G)) ≪≫ 𝒩.gen
  gen_hom := by
    letI : GrpObj ((Over.pullback (gO O)).obj 𝒩.G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (jO O)).obj ((Over.pullback (gO O)).obj 𝒩.G)) :=
      Functor.grpObjObj
    letI : GrpObj (genericFibre L 𝒩.G) := Functor.grpObjObj
    haveI := 𝒩.gen_hom
    have h1 : IsMonHom (pbCompIso (jO O) (gO O) _ (jO_gO O) (Grp.mk 𝒩.G)).hom.hom.hom :=
      inferInstance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1 𝒩.gen_hom

end LocalGlobal

section LocalGlobal2

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- **GLUE `SemiAbelianFieldIsoInvariant`** (new; pure transport). Having semi-abelian identity
component is invariant under base change along an isomorphism of fields `σ : k ≃ k'`. Needs only
transport of structure: `Over.pullback (Spec σ)` is an equivalence of categories which preserves
products, open immersions, connectedness, flatness, surjectivity, abelian varieties
(`AbVar.baseChange`) and, through `R ↦ R` with the `k`-algebra structure via `σ`, the functor of
points of `𝔾_m^r`. No algebraic geometry beyond `Over.pullback` of an isomorphism. -/
def SemiAbelianFieldIsoInvariant : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] (σ : k ≃+* k') (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G],
    HasSemiAbelianIdentityComponent G ↔
      (letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (σ : k →+* k')))).obj G) :=
        Functor.grpObjObj
       HasSemiAbelianIdentityComponent ((Over.pullback (Spec.map (CommRingCat.ofHom (σ : k →+* k')))).obj G))

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

theorem spec_barIso_comp (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    Spec.map (CommRingCat.ofHom ((barIso O : _ ≃+* _) : _ →+* _)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (ResBar (center O)))) =
    Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))) ≫ gO O := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    barIso_comp]

/-- **Fibre identification**: the geometric special fibre of `𝒩 ×_{𝓞_L} O` is the base change of
the geometric fibre of `𝒩` at `𝔭_O` along `κ̄(𝔭_O) ≅ κ̄(O)`, as group schemes. -/
noncomputable def fibreIso (𝒩 : GroupModel A L) (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    (Over.pullback (Spec.map (CommRingCat.ofHom ((barIso O : _ ≃+* _) : _ →+* _)))).mapGrp.obj
        (Grp.mk (geomFibre 𝒩 (center O))) ≅
      Grp.mk (geomSpecialFibre (toO 𝒩 O)) :=
  pbCompIso _ _ _ (spec_barIso_comp O) (Grp.mk 𝒩.G) ≪≫
    (pbCompIso _ _ _ rfl (Grp.mk 𝒩.G)).symm

theorem fibre_semistable_iff (hT : SemiAbelianFieldIsoInvariant) (𝒩 : GroupModel A L)
    (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    HasSemiAbelianIdentityComponent (geomFibre 𝒩 (center O)) ↔ (toO 𝒩 O).IsSemistable := by
  rw [hT _ _ (barIso O) (geomFibre 𝒩 (center O))]
  let E := fibreIso 𝒩 O
  exact ⟨fun h => @hasSemiAbelian_of_iso _ _ _ (geomSpecialFibre (toO 𝒩 O)) Functor.grpObjObj _
      (isoX E) (inferInstanceAs (IsMonHom E.hom.hom.hom)) h,
    fun h => @hasSemiAbelian_of_iso _ _ (geomSpecialFibre (toO 𝒩 O)) _ _ Functor.grpObjObj
      (isoX E.symm) (inferInstanceAs (IsMonHom E.inv.hom.hom)) h⟩

theorem fibre_semistable_iff' (hT : SemiAbelianFieldIsoInvariant) (𝒩 : GroupModel A L)
    (O : ValuationSubring L) [IsDiscreteValuationRing O] (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal]
    (h : center O = 𝔭) :
    HasSemiAbelianIdentityComponent (geomFibre 𝒩 𝔭) ↔ (toO 𝒩 O).IsSemistable := by
  subst h
  exact fibre_semistable_iff hT 𝒩 O

/-- **LEAF `NeronLocalizesDVR` (Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4;
number UNVERIFIED: over a Dedekind ring `R`, a smooth separated `R`-model of finite type is a
Néron model iff its localizations at the closed points are).** The direction used: for a Néron
model `𝒩` of `A_L` over `𝓞_L` and a discrete valuation ring `O` of `L` (necessarily `(𝓞_L)_𝔭`,
`mem_iff_exists`), `𝒩 ×_{𝓞_L} O` is a Néron model over `O`. (`𝒩` is quasi-compact and smooth,
hence of finite type.) -/
def NeronLocalizesDVR : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel A L), 𝒩.IsNeronModel →
    ∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], (toO 𝒩 O).IsNeronModel

/-- **GLUE `SemistableLocalGlobal` (reduct-split), PROVED** from the leaf `NeronLocalizesDVR`
(BLR §1.2 Prop. 4) and the transport glue `SemiAbelianFieldIsoInvariant`. Proved here: DVRs of
`L` are the `(𝓞_L)_𝔭` with matching residue fields (`mem_iff_exists`, `resIso`, `dvrAt`),
uniqueness of Néron models over a DVR (`neronO_unique`), and the fibre identification
(`fibreIso`). -/
theorem semistableLocalGlobal_of (hL : NeronLocalizesDVR) (hT : SemiAbelianFieldIsoInvariant) :
    SemistableLocalGlobal := by
  intro K _ A L _ _ _ 𝒩 h𝒩
  constructor
  · intro hss O hO
    haveI := hO
    haveI := center_isMaximal O
    exact ⟨toO 𝒩 O, hL K A L 𝒩 h𝒩 O, (fibre_semistable_iff hT 𝒩 O).mp (hss (center O))⟩
  · intro h 𝔭 _
    have hs := semistableNeronModels_of_has (h (dvrAt 𝔭) inferInstance)
    exact (fibre_semistable_iff' hT 𝒩 (dvrAt 𝔭) 𝔭 (center_dvrAt 𝔭)).mpr
      (hs _ (hL K A L 𝒩 h𝒩 (dvrAt 𝔭)))

end LocalGlobal2
end ReductGlue

import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.TailY
import ZInQKernel.Contrib.NeronC.NeronGroup

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

import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15Genuine
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedFiniteFree
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageArith
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageFlat

/-!
# The models of `C_∅` at the coefficient stages

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4399: "a bounded finite
free model of rank `dim_k Hⁿ(k ⊗ C)`"; tex 4401–4406: "retain a tuple whose model ranks are
bounded") for the complex `C_∅` of the chain of Lemma `ex:arith-common-coordinate`
(tex 4142–4194).

The initial state of a stage chain (`CMState m₀ m₁ m₂ C_∅ 0`) is a block-complex model of `C_∅` of
ranks `(m₀, m₀ + 1 + m₁, m₁ + 1 + m₂, m₂)` with a retract. It is produced from lane RC31's graded
finite free models (`exists_gradedModel`, `RC/Limits/GradedFiniteFree.lean`: over a local ring
with nilpotent maximal ideal, a complex of flat modules with finite residual cohomology has a
model of rank `dim_k Hⁿ(k ⊗ X)` in degree `n` with a `GRetract`):

* `ShapeRanks r m₀ m₁ m₂`: a rank function has the shape of a block complex; `finSumUnitSum`,
  `shapeE0`, `shapeE1`, `shapeE2`, `shapeE3`: the index equivalences.
* `gradedD0`, `gradedD1`, `gradedD2`, `gradedEquiv`, `gradedEquiv_comm`, **`gradedRetract`**:
  a graded model of these ranks re-indexed into the shape of step `0`, with the transported
  retract.
* **`CMState.ofGraded`**; **`exists_cmState_of_residual`**: over a local ring with nilpotent
  maximal ideal, a complex with flat terms and finite residual cohomology of residual ranks of this
  shape has an initial state, for any class and functional; `shapeRanks_minRank`: the minimal model
  (residual cohomology of dimensions `(0, 1, 1, 0)`) has the shape `(0, 0, 0)`.
* `stageRing_isLocalRing`, `stageRing_isNilpotent_maximalIdeal`: the stage rings `Λ ⧸ stageIdeal s`,
  `s ≠ 0`, are local with nilpotent maximal ideal (from `StageA s`, via `stageEquiv`).
* **`exists_shape_fixed`**: residual ranks bounded by `B`, vanishing outside `[0, 3]`, with Euler
  characteristic zero and `h⁰ < h¹` at `U`-many stages, have one shape `(m₀, m₁, m₂)` at `U`-many
  stages (lane RC6's `bounded_rank_tuples_fixed`).
* **`exists_genuine_st0`**: the initial states of the genuine chains, at the stages where the
  residual ranks of the genuine `C_∅ = suppCxS ∅` have the shape; `genResRank'`,
  **`exists_genuine_st0_eventually`**: from flat terms and finite residual cohomology at every
  stage, residual ranks bounded and vanishing outside `[0, 3]`, Euler characteristic zero and
  `h⁰ < h¹` at `U`-many stages, one shape and initial states at `U`-many stages.
* `frobCx_X_free`, **`genCx_free`**: the terms of the genuine `C_T` are free at the stages
  (finitely many places, free old condition modules, free unramified representations, free `M`;
  lane 3cc's `free_contCochains`, `free_selmerCochains`); **`exists_genuine_st0_eventually_free`**:
  the initial states with the flatness so PROVED.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Filter IsLocalRing ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.RC53Assist.InnerLimitArith (free_natX free_contCochains free_selmerCochains)
open scoped PowerSeries.WithPiTopology

/-! ### Graded models in the shape of a block complex -/

section Shape

variable {m0 m1 m2 : ℕ}

/-- `Fin a ⊕ Unit ⊕ Fin b ≃ Fin (a + 1 + b)` (tex 4185–4193). Kind: definition. -/
def finSumUnitSum (a b : ℕ) : Fin a ⊕ Unit ⊕ Fin b ≃ Fin (a + 1 + b) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr finOneEquiv.symm (Equiv.refl _)).trans finSumFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_assoc a 1 b).symm))

/-- **A rank function of the shape of a block complex** (tex 4185–4193, 4391–4399): ranks
`(m₀, m₀ + 1 + m₁, m₁ + 1 + m₂, m₂)` in degrees `0, 1, 2, 3` and `0` elsewhere.
Kind: definition. -/
structure ShapeRanks (r : ℤ → ℕ) (m0 m1 m2 : ℕ) : Prop where
  /-- degree `0` -/
  h0 : r 0 = m0
  /-- degree `1` -/
  h1 : r 1 = m0 + 1 + m1
  /-- degree `2` -/
  h2 : r 2 = m1 + 1 + m2
  /-- degree `3` -/
  h3 : r 3 = m2
  /-- outside `[0, 3]` -/
  hout : ∀ n, n < 0 ∨ 3 < n → r n = 0

variable {r : ℤ → ℕ} (hr : ShapeRanks r m0 m1 m2)

/-- The index equivalence in degree `0` (tex 4185–4193). Kind: definition. -/
def shapeE0 : Fin m0 ≃ Fin (r 0) := finCongr hr.h0.symm

/-- The index equivalence in degree `1` (tex 4185–4193). Kind: definition. -/
def shapeE1 : cD1 m0 m1 0 ≃ Fin (r 1) := (finSumUnitSum m0 m1).trans (finCongr hr.h1.symm)

/-- The index equivalence in degree `2` (tex 4185–4193). Kind: definition. -/
def shapeE2 : cD2 m1 m2 0 ≃ Fin (r 2) := (finSumUnitSum m1 m2).trans (finCongr hr.h2.symm)

/-- The index equivalence in degree `3` (tex 4185–4193). Kind: definition. -/
def shapeE3 : Fin m2 ≃ Fin (r 3) := finCongr hr.h3.symm

variable {A : Type} [CommRing A] {X : GCx A} (R : GradedModel X) (hR : ShapeRanks R.rank m0 m1 m2)

/-- The model in degrees `0 → 1`, re-indexed (tex 4391–4399). Kind: definition. -/
def gradedD0 : Matrix (cD1 m0 m1 0) (Fin m0) A :=
  (R.dC 0 1 rfl).submatrix (shapeE1 hR) (shapeE0 hR)

/-- The model in degrees `1 → 2`, re-indexed (tex 4391–4399). Kind: definition. -/
def gradedD1 : Matrix (cD2 m1 m2 0) (cD1 m0 m1 0) A :=
  (R.dC 1 2 rfl).submatrix (shapeE2 hR) (shapeE1 hR)

/-- The model in degrees `2 → 3`, re-indexed (tex 4391–4399). Kind: definition. -/
def gradedD2 : Matrix (Fin m2) (cD2 m1 m2 0) A :=
  (R.dC 2 3 rfl).submatrix (shapeE3 hR) (shapeE2 hR)

/-- The re-indexed model is a complex in degrees `0 → 2` (tex 4391–4399). Kind: PROVED. -/
theorem graded_h10 : gradedD1 R hR * gradedD0 R hR = 0 := by
  unfold gradedD1 gradedD0
  rw [submatrix_mul_equiv, R.dC_sq 0 1 2 rfl rfl]
  rfl

/-- The re-indexed model is a complex in degrees `1 → 3` (tex 4391–4399). Kind: PROVED. -/
theorem graded_h21 : gradedD2 R hR * gradedD1 R hR = 0 := by
  unfold gradedD2 gradedD1
  rw [submatrix_mul_equiv, R.dC_sq 1 2 3 rfl rfl]
  rfl

/-- The block complex of the shape of step `0` of a graded model (tex 4391–4399).
Kind: definition. -/
abbrev gradedBlock : BlockComplex A :=
  shapeBlock m0 m1 m2 0 (gradedD0 R hR) (gradedD1 R hR) (gradedD2 R hR) (graded_h10 R hR)
    (graded_h21 R hR)

include hR in
/-- The terms of the graded model vanish outside `[0, 3]` (tex 4391–4399). Kind: PROVED. -/
theorem graded_subsingleton (n : ℤ) (h : n < 0 ∨ 3 < n) :
    Subsingleton (Fin (R.rank n) → A) := by
  have : IsEmpty (Fin (R.rank n)) := by
    rw [hR.hout n h]
    exact Fin.isEmpty'
  infer_instance

/-- **The block complex is degreewise the graded model** (tex 4391–4399): `v ↦ v ∘ e⁻¹` in
degrees `0, …, 3`, the zero modules elsewhere. Kind: definition. -/
def gradedEquiv : (n : ℤ) → (gradedBlock R hR).toGCx.X n ≃ₗ[A] R.modelCx.X n
  | 0 => LinearEquiv.funCongrLeft A A (shapeE0 hR).symm
  | 1 => LinearEquiv.funCongrLeft A A (shapeE1 hR).symm
  | 2 => LinearEquiv.funCongrLeft A A (shapeE2 hR).symm
  | 3 => LinearEquiv.funCongrLeft A A (shapeE3 hR).symm
  | Int.ofNat (k + 4) =>
    have := graded_subsingleton R hR (Int.ofNat (k + 4))
      (Or.inr (by show (3 : ℤ) < ((k + 4 : ℕ) : ℤ); omega))
    LinearEquiv.ofSubsingleton (Empty → A) (Fin (R.rank (Int.ofNat (k + 4))) → A)
  | Int.negSucc k =>
    have := graded_subsingleton R hR (Int.negSucc k) (Or.inl (Int.negSucc_lt_zero k))
    LinearEquiv.ofSubsingleton (Empty → A) (Fin (R.rank (Int.negSucc k)) → A)

/-- The identification commutes with the differentials (tex 4391–4399). Kind: PROVED. -/
theorem gradedEquiv_comm (a b : ℤ) (h : a + 1 = b) (y : (gradedBlock R hR).toGCx.X a) :
    R.modelCx.d a b h (gradedEquiv R hR a y) =
      gradedEquiv R hR b ((gradedBlock R hR).toGCx.d a b h y) := by
  subst h
  match a with
  | 0 =>
    funext x
    have key := congrFun (submatrix_mulVec_equiv (o := Fin m0) (R.dC 0 1 rfl) y
      (shapeE1 hR) (shapeE0 hR)) ((shapeE1 hR).symm x)
    rw [Function.comp_apply, Equiv.apply_symm_apply] at key
    exact key.symm
  | 1 =>
    funext x
    have key := congrFun (submatrix_mulVec_equiv (o := cD1 m0 m1 0) (R.dC 1 2 rfl) y
      (shapeE2 hR) (shapeE1 hR)) ((shapeE2 hR).symm x)
    rw [Function.comp_apply, Equiv.apply_symm_apply] at key
    exact key.symm
  | 2 =>
    funext x
    have key := congrFun (submatrix_mulVec_equiv (o := cD2 m1 m2 0) (R.dC 2 3 rfl) y
      (shapeE3 hR) (shapeE2 hR)) ((shapeE3 hR).symm x)
    rw [Function.comp_apply, Equiv.apply_symm_apply] at key
    exact key.symm
  | 3 =>
    have := graded_subsingleton R hR 4 (Or.inr (by omega))
    exact Subsingleton.elim (α := Fin (R.rank 4) → A) _ _
  | Int.ofNat (k + 4) =>
    obtain rfl : y = 0 := Subsingleton.elim (α := Empty → A) _ _
    simp only [map_zero]
  | Int.negSucc k =>
    obtain rfl : y = 0 := Subsingleton.elim (α := Empty → A) _ _
    simp only [map_zero]

/-- **The retract onto the re-indexed graded model** (tex 4391–4399, 4423–4437).
Kind: definition. -/
def gradedRetract : GRetract X (gradedBlock R hR).toGCx :=
  retractOfModelEquiv R.retract (gradedEquiv R hR) (gradedEquiv_comm R hR)

/-- **The initial state of a chain from a graded model** (tex 4391–4399, 4185–4193): the
re-indexed model with its retract, and the given class and functional of `X`.
Kind: definition. -/
def CMState.ofGraded (z : X.X 1) (hz : X.d 1 2 rfl z = 0) (lam : X.X 2 →ₗ[A] A)
    (hlam : lam ∘ₗ X.d 1 2 rfl = 0) : CMState m0 m1 m2 X 0 where
  d0 := gradedD0 R hR
  d1 := gradedD1 R hR
  d2 := gradedD2 R hR
  h10 := graded_h10 R hR
  h21 := graded_h21 R hR
  R := gradedRetract R hR
  z := z
  hz := hz
  lam := lam
  hlam := hlam

end Shape

/-! ### Existence at a local stage -/

/-- **An initial state from the residual cohomology** (tex 4391–4399): over a local ring with
nilpotent maximal ideal, a complex with flat terms and finite residual cohomology whose residual
ranks `dim_k Hⁿ(k ⊗ X)` have the shape `(m₀, m₁, m₂)` has an initial state (the graded model of
lane RC31, re-indexed), for any class and functional. Kind: PROVED. -/
theorem exists_cmState_of_residual {A : Type} [CommRing A] [IsLocalRing A]
    (hnil : IsNilpotent (maximalIdeal A)) (X : GCx A) [∀ n, Module.Flat A (X.X n)]
    (hfin : ∀ n, Module.Finite (ResidueField A) (residualCohomologyAt X n)) {m0 m1 m2 : ℕ}
    (hr : ShapeRanks (fun n => Module.finrank (ResidueField A) (residualCohomologyAt X n))
      m0 m1 m2)
    (z : X.X 1) (hz : X.d 1 2 rfl z = 0) (lam : X.X 2 →ₗ[A] A)
    (hlam : lam ∘ₗ X.d 1 2 rfl = 0) :
    Nonempty (CMState m0 m1 m2 X 0) := by
  obtain ⟨R, hR⟩ := exists_gradedModel hnil X hfin
  have hR' : R.rank = fun n => Module.finrank (ResidueField A) (residualCohomologyAt X n) :=
    funext hR
  have hs : ShapeRanks R.rank m0 m1 m2 := by
    rw [hR']
    exact hr
  exact ⟨CMState.ofGraded R hs z hz lam hlam⟩

/-- **The minimal model has the shape `(0, 0, 0)`** (tex 4391–4399): residual cohomology of
dimensions `(0, 1, 1, 0)`. Kind: PROVED. -/
theorem shapeRanks_minRank : ShapeRanks minRank 0 0 0 where
  h0 := minRank_zero 0 (by omega) (by omega)
  h1 := minRank_one
  h2 := minRank_two
  h3 := minRank_zero 3 (by omega) (by omega)
  hout := fun n hn => minRank_zero n (by omega) (by omega)

/-! ### The stage rings -/

/-- **The stage rings are local** (tex 4385–4391): `Λ ⧸ stageIdeal s`, `s ≠ 0`, through
`stageEquiv` from `StageA s`. Kind: PROVED (instance). -/
instance stageRing_isLocalRing (s : ℕ) [NeZero s] : IsLocalRing (StageRing s) :=
  have : Nontrivial (StageRing s) := (stageEquiv s).toEquiv.nontrivial
  IsLocalRing.of_surjective' (stageEquiv s).symm.toRingHom (stageEquiv s).symm.surjective

/-- **The maximal ideals of the stage rings are nilpotent** (tex 4385–4391). Kind: PROVED. -/
theorem stageRing_isNilpotent_maximalIdeal (s : ℕ) [NeZero s] :
    IsNilpotent (maximalIdeal (StageRing s)) := by
  obtain ⟨n, hn⟩ := ZInQ.Manuscript.RC.FibreDuality.stageA_isNilpotent_maximalIdeal s
  have hmax : Ideal.map (stageEquiv s).symm (maximalIdeal (StageA s)) =
      maximalIdeal (StageRing s) :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _)
  refine ⟨n, ?_⟩
  rw [← hmax, ← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
  rfl

/-! ### The ranks fixed along the ultrafilter -/

/-- **One shape at `U`-many stages** (tex 4401–4406: "retain a tuple whose model ranks are bounded
over the finite coefficient stages"): if the residual ranks `h s n` are bounded by `B`, vanish
outside `[0, 3]`, and at `U`-many stages have Euler characteristic zero and `h⁰ < h¹`, then one
shape `(m₀, m₁, m₂)` holds at `U`-many stages. Kind: PROVED. -/
theorem exists_shape_fixed (U : Ultrafilter ℕ) {B : ℕ} (h : ℕ → ℤ → ℕ)
    (hB : ∀ s n, h s n ≤ B) (hout : ∀ s n, n < 0 ∨ 3 < n → h s n = 0)
    (heul : ∀ᶠ s in (U : Filter ℕ), h s 0 + h s 2 = h s 1 + h s 3)
    (hpos : ∀ᶠ s in (U : Filter ℕ), h s 0 < h s 1) :
    ∃ m0 m1 m2 : ℕ, ∀ᶠ s in (U : Filter ℕ), ShapeRanks (h s) m0 m1 m2 := by
  obtain ⟨r₀, -, hr₀⟩ := bounded_rank_tuples_fixed U (fun s (j : Fin 4) => h s (j : ℤ))
    (fun s j => hB s _)
  refine ⟨r₀ 0, r₀ 1 - r₀ 0 - 1, r₀ 3, ?_⟩
  filter_upwards [hr₀, heul, hpos] with s hs he hp
  have e : ∀ j : Fin 4, h s (j : ℤ) = r₀ j := fun j => congrFun hs j
  have e0 : h s 0 = r₀ 0 := e 0
  have e1 : h s 1 = r₀ 1 := e 1
  have e2 : h s 2 = r₀ 2 := e 2
  have e3 : h s 3 = r₀ 3 := e 3
  refine ⟨e0, ?_, ?_, e3, hout s⟩ <;> omega

/-- The unramified complex `[W --(Ψ−1)--> W]` has free terms when `W` is free (tex 3470–3487).
Kind: PROVED. -/
theorem frobCx_X_free {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W]
    [Module.Free R W] (Ψ : W →ₗ[R] W) (n : ℤ) : Module.Free R ((frobCx Ψ).X n) := by
  by_cases h0 : n = 0
  · subst h0
    exact Module.Free.of_equiv
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Ψ - 1)) rel01).toLinearEquiv.symm
  by_cases h1 : n = 1
  · subst h1
    exact Module.Free.of_equiv
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Ψ - 1)) rel01
        (by decide)).toLinearEquiv.symm
  have := ModuleCat.subsingleton_of_isZero
    (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.isZero_X Ψ n h0 h1)
  exact Module.Free.of_basis (Module.Basis.empty _ : Module.Basis Empty R ((frobCx Ψ).X n))

/-! ### The genuine `C_∅` at a stage -/

section GenuineModel

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  [∀ s, TopologicalSpace (StageRing s)]
  (M : ℕ → Type) [∀ s, AddCommGroup (M s)] [∀ s, Module (StageRing s) (M s)]
  [∀ s, DistribMulAction (GKS K S) (M s)] [∀ s, SMulCommClass (GKS K S) (StageRing s) (M s)]
  [∀ s, TopologicalSpace (M s)] [∀ s, DiscreteTopology (M s)]
  [∀ s, ContinuousSMul (GKS K S) (M s)]
  (Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (M s))
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : ∀ s, (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1))
  (EU : ∀ s j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X s j))
    (genuineLq K S (StageRing s) (M s) (place j)))

/-- **The terms of the genuine `C_T` are free at the stages** (tex 3470–3498, 4391–4414): with
finitely many places, the old condition modules free and the unramified representations free,
the global and local continuous cochains of the free `M` are free (`free_contCochains`, after
Nöbeling) and so are the unramified complexes; hence the Selmer cochains (`free_selmerCochains`).
Kind: PROVED. -/
theorem genCx_free (s : ℕ) [NeZero s] [Fintype (Places K S₀)] [Fintype ι]
    [∀ s, Module.Free (StageRing s) (M s)] [∀ s j, Module.Free (StageRing s) (X s j).V]
    (hold : ∀ (v : Places K S₀) (m : ℤ), Module.Free (StageRing s) (((Δ s).U v).X m))
    (T : Finset ι) (n : ℤ) :
    Module.Free (StageRing s) ((genCx K S₀ S M Δ place X EU s T).X n) := by
  have hnil := stageRing_isNilpotent_maximalIdeal s
  have hLq : ∀ (w : Places K S) (m : ℤ),
      Module.Free (StageRing s) ((genuineLq K S (StageRing s) (M s) w).X m) := fun w m => by
    have : Module.Flat (StageRing s) (ResMod (locMap K S w.1) (M s)) :=
      inferInstanceAs (Module.Flat (StageRing s) (M s))
    exact free_natX _ (fun k => free_contCochains (R := StageRing s) (G := Gloc K w.1)
      (M := ResMod (locMap K S w.1) (M s)) hnil k) m
  refine free_selmerCochains hnil (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) (M s)
    (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) T) (fun v m => ?_) n
  rcases v with v | j
  · exact hold v m
  · change Module.Free (StageRing s)
      ((condCxS K S (StageRing s) (M s) place (X s) j (decide (j.1 ∈ T))).X m)
    cases decide (j.1 ∈ T)
    · exact frobCx_X_free (frob (eUr K (place j).1) (X s j)) m
    · exact hLq (place j) m

/-- **The residual ranks of the genuine `C_∅` at a stage** (tex 4391–4399):
`dim_k Hⁿ(k ⊗ C_∅)`, `k` the residue field of `A_s`. Kind: definition. -/
abbrev genResRank (s : ℕ) [NeZero s] (n : ℤ) : ℕ :=
  Module.finrank (ResidueField (StageRing s))
    (residualCohomologyAt (genCx K S₀ S M Δ place X EU s ∅) n)

/-- **The initial state of a genuine stage chain** (tex 4391–4399, 4142–4194): at a stage
`s ≠ 0` where the terms of the genuine `C_∅ = suppCxS ∅` are flat, its residual cohomology is
finite and its residual ranks have the shape `(m₀, m₁, m₂)`, the graded model of lane RC31
re-indexed is an initial state, with the primitive class `z_P` and functional `λ_P`.
Kind: PROVED. -/
theorem exists_genuine_st0 (s : ℕ) [NeZero s]
    [∀ n, Module.Flat (StageRing s) ((genCx K S₀ S M Δ place X EU s ∅).X n)]
    (hfin : ∀ n, Module.Finite (ResidueField (StageRing s))
      (residualCohomologyAt (genCx K S₀ S M Δ place X EU s ∅) n))
    {m0 m1 m2 : ℕ} (hr : ShapeRanks (genResRank K S₀ S M Δ place X EU s) m0 m1 m2)
    (z : (genCx K S₀ S M Δ place X EU s ∅).X 1)
    (hz : (genCx K S₀ S M Δ place X EU s ∅).d 1 2 rfl z = 0)
    (lam : (genCx K S₀ S M Δ place X EU s ∅).X 2 →ₗ[StageRing s] StageRing s)
    (hlam : lam ∘ₗ (genCx K S₀ S M Δ place X EU s ∅).d 1 2 rfl = 0) :
    Nonempty (CMState m0 m1 m2 (genCx K S₀ S M Δ place X EU s ∅) 0) :=
  exists_cmState_of_residual (stageRing_isNilpotent_maximalIdeal s) _ hfin hr z hz lam hlam

/-- **The residual ranks of the genuine `C_∅` at every stage** (tex 4391–4406): `genResRank` at
the stages `s ≠ 0`, `0` at the zero stage. Kind: definition. -/
def genResRank' (s : ℕ) (n : ℤ) : ℕ :=
  if hs : s = 0 then 0 else
    haveI : NeZero s := ⟨hs⟩
    genResRank K S₀ S M Δ place X EU s n

/-- **The initial states of the genuine chains at `U`-many stages, with one shape**
(tex 4391–4406): if at every stage `s ≠ 0` the terms of the genuine `C_∅` are flat and its residual
cohomology is finite, its residual ranks are bounded by `B` and vanish outside `[0, 3]`, and at
`U`-many stages they have Euler characteristic zero and `h⁰ < h¹`, then for one shape
`(m₀, m₁, m₂)` there is, at `U`-many stages, an initial state of the genuine chain with the given
primitive class and functional. Kind: PROVED. -/
theorem exists_genuine_st0_eventually (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (hflat : ∀ s [NeZero s] n, Module.Flat (StageRing s) ((genCx K S₀ S M Δ place X EU s ∅).X n))
    (hfin : ∀ s [NeZero s] n, Module.Finite (ResidueField (StageRing s))
      (residualCohomologyAt (genCx K S₀ S M Δ place X EU s ∅) n))
    {B : ℕ} (hB : ∀ s n, genResRank' K S₀ S M Δ place X EU s n ≤ B)
    (hout : ∀ s n, n < 0 ∨ 3 < n → genResRank' K S₀ S M Δ place X EU s n = 0)
    (heul : ∀ᶠ s in (U : Filter ℕ), genResRank' K S₀ S M Δ place X EU s 0 +
      genResRank' K S₀ S M Δ place X EU s 2 =
        genResRank' K S₀ S M Δ place X EU s 1 + genResRank' K S₀ S M Δ place X EU s 3)
    (hpos : ∀ᶠ s in (U : Filter ℕ),
      genResRank' K S₀ S M Δ place X EU s 0 < genResRank' K S₀ S M Δ place X EU s 1)
    (z : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).X 1)
    (hz : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).d 1 2 rfl (z s) = 0)
    (lam : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).X 2 →ₗ[StageRing s] StageRing s)
    (hlam : ∀ s, lam s ∘ₗ (genCx K S₀ S M Δ place X EU s ∅).d 1 2 rfl = 0) :
    ∃ m0 m1 m2 : ℕ, ∀ᶠ s in (U : Filter ℕ),
      Nonempty (CMState m0 m1 m2 (genCx K S₀ S M Δ place X EU s ∅) 0) := by
  obtain ⟨m0, m1, m2, hsh⟩ := exists_shape_fixed U (genResRank' K S₀ S M Δ place X EU) hB hout
    heul hpos
  have hne : ∀ᶠ s in (U : Filter ℕ), s ≠ 0 :=
    hU (Set.Finite.compl_mem_cofinite (Set.finite_singleton 0))
  refine ⟨m0, m1, m2, ?_⟩
  filter_upwards [hsh, hne] with s hs hs0
  have : NeZero s := ⟨hs0⟩
  have : ∀ n, Module.Flat (StageRing s) ((genCx K S₀ S M Δ place X EU s ∅).X n) := hflat s
  have e : genResRank' K S₀ S M Δ place X EU s = genResRank K S₀ S M Δ place X EU s := by
    funext n
    unfold genResRank'
    rw [dite_eq_right hs0]
  rw [e] at hs
  exact exists_genuine_st0 K S₀ S M Δ place X EU s (hfin s) hs (z s) (hz s) (lam s) (hlam s)

/-- **The initial states with flatness PROVED** (tex 4391–4414): as
`exists_genuine_st0_eventually`, the flatness of the terms of the genuine `C_∅` now coming from
`genCx_free` (finitely many places, free old condition modules, free unramified representations,
free `M`). Kind: PROVED. -/
theorem exists_genuine_st0_eventually_free (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    [Fintype (Places K S₀)] [Fintype ι] [∀ s, Module.Free (StageRing s) (M s)]
    [∀ s j, Module.Free (StageRing s) (X s j).V]
    (hold : ∀ s (v : Places K S₀) (m : ℤ), Module.Free (StageRing s) (((Δ s).U v).X m))
    (hfin : ∀ s [NeZero s] n, Module.Finite (ResidueField (StageRing s))
      (residualCohomologyAt (genCx K S₀ S M Δ place X EU s ∅) n))
    {B : ℕ} (hB : ∀ s n, genResRank' K S₀ S M Δ place X EU s n ≤ B)
    (hout : ∀ s n, n < 0 ∨ 3 < n → genResRank' K S₀ S M Δ place X EU s n = 0)
    (heul : ∀ᶠ s in (U : Filter ℕ), genResRank' K S₀ S M Δ place X EU s 0 +
      genResRank' K S₀ S M Δ place X EU s 2 =
        genResRank' K S₀ S M Δ place X EU s 1 + genResRank' K S₀ S M Δ place X EU s 3)
    (hpos : ∀ᶠ s in (U : Filter ℕ),
      genResRank' K S₀ S M Δ place X EU s 0 < genResRank' K S₀ S M Δ place X EU s 1)
    (z : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).X 1)
    (hz : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).d 1 2 rfl (z s) = 0)
    (lam : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).X 2 →ₗ[StageRing s] StageRing s)
    (hlam : ∀ s, lam s ∘ₗ (genCx K S₀ S M Δ place X EU s ∅).d 1 2 rfl = 0) :
    ∃ m0 m1 m2 : ℕ, ∀ᶠ s in (U : Filter ℕ),
      Nonempty (CMState m0 m1 m2 (genCx K S₀ S M Δ place X EU s ∅) 0) :=
  exists_genuine_st0_eventually K S₀ S M Δ place X EU U hU (fun s _ n => by
      have := genCx_free K S₀ S M Δ place X EU s (hold s) ∅ n
      infer_instance) hfin hB hout heul hpos z hz lam hlam

end GenuineModel

end ZInQ.Manuscript.RC.Wiring

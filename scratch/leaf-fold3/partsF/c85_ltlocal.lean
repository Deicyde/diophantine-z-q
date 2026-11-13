-- (leaf-fold3) mk_ltlocal.py: lt-local LtLocal4.lean, unram-roots UnramRoots.lean, frob-pieces FrobPiecesFull.lean, deduplicated against the chain
/-! ## leaf-fold3: scratch/lt-local/LtLocal4.lean, declarations already in the chain dropped -/


-- BEGIN scratch/lg-kerwild/KerWild.lean body with g0-assemble3's G7Data fix (mk_base4.py)

-- BEGIN verbatim body of scratch/local-glue/LocalGlue.lean

/-! # local-data: `LocalData p r` (scratch/g15-ram) on G8's `r`

Assembled by `scratch/local-data/build.sh`. Check with
`lake env lean scratch/local-data/LocalData.lean`. The first part (through `end Reduction`) is a
verbatim copy of `scratch/g15-ram/G15Ram.lean` lines 8-1384; then verbatim definitions from
`scratch/g0-mod-galois/part_galois.lean`; then §4 (new). -/

/-!
# g15-ram: the open Prop `G15RamG` of g0-mod-newform (G15, clauses (i)-(ii))

Check with `lake env lean scratch/g15-ram/G15Ram.lean`.

* §0. Verbatim copies (from `scratch/g0-mod-newform/part_new.lean`, `NewForm.lean` lines
  1684-1690, 2037, 2448-2464) of `ModData`, `U0`, `LocalRamG`, `G15RamG`, and (from
  `scratch/g0-mod-galois/part_galois.lean` line 164) of `G0Galois.G11Out`.
* §1. The named smaller Props (glue), each with its glue step and source.
* §2. Local field: `upperBreakFix_of_hilbertSerre` (proved): Glazer's break bound
  `G_{ℚ_p}^t ⊆ G_F` for `t > 4a²` when `e(F/ℚ_p) ≤ a!`, at the level of `LadicCond`'s
  `upperAbs`, from the transport `HilbertSerreLadic` of T20 + T21 and the kernel's D1 arithmetic
  `GlueConductor.upper_break_le`.
* §3. The reduction `g15RamG_of_pieces` (proved).

Leaves and glue targets are hypotheses (`def … : Prop`); no `sorry`, no `axiom`.
-/

noncomputable section

/-! ## §0. Verbatim copies -/

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

end G0Galois

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar

section LocalRamSec

open LadicCond
open PkgI4 (GQp)

end LocalRamSec

end G0ModNewform

/-! ## §1. The smaller named Props -/

namespace G15Ram

open PkgI4 (GQp GaloisRep)
open LadicCond G0ModNewform

section Local

variable (p : ℕ) [Fact p.Prime]

variable {ℓ : ℕ} [Fact ℓ.Prime]

end Local

/-! ## §2. Local field: the break bound at the level of `upperAbs` (proved) -/

section Break

variable {p : ℕ} [Fact p.Prime] {F : Fld p}

end Break

/-! ## §2b. Positive upper groups are wild (proved) -/

section Wild

variable {p : ℕ} [Fact p.Prime]

end Wild

/-! ## §2d. Wild inertia fixes tame extensions (proved) -/

section Tame

variable {p : ℕ} [Fact p.Prime]

end Tame

/-! ## §2c. `HilbertSerreLadic` from T20 + T21 (proved by t-different) and a DVR model -/

section Bridge

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

end Bridge

/-! ## §2e. The DVR model over `ℤ_p`: the arithmetic conjuncts are automatic -/

section BridgeZp

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

end BridgeZp

/-! ## §2f. The `ℤ_p`-model `𝓞_F = integralClosure ℤ_p F` (proved): `LadicDVRModelZp` -/

section DVRModelSec

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

section Model

variable (F : Fld p)

attribute [local instance] algZpF

variable [FiniteDimensional ℚ_[p] F]

end Model

section Model2

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] algZpF

omit [FiniteDimensional ℚ_[p] F] in
variable {F}

end Model2

section Galois

attribute [local instance] algZpF FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] torsionFree_OF

end Galois

section Filtration

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

end Filtration

section Card

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

end Card

section FinalZp

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

end FinalZp

end DVRModelSec

/-! ## §3. The reduction (proved) -/

section Reduction

end Reduction

end G15Ram

/-! ## §3' (local-data). Verbatim copies from scratch/g0-mod-galois/part_galois.lean -/

section G0GaloisSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### Objects -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

end G0Galois

end

end G0GaloisSec

/-! ## §4 (local-data). `LocalData p r` on G8's `r`, from G7's data

The copied `LocalData p r` (§1) is a predicate on a bare `r : GaloisRep ℓ 2`. Here:

* `largePrimeData_iff`, `localData_large_iff` (proved): for `p > D`, `LocalData p r ↔ r` is
  trivial on wild inertia. So `LocalData` fails for any `r` wildly ramified at some `p > D`
  (e.g. `ψ ⊕ 1`, `ψ` a Dirichlet character of conductor `p²`), and cannot be proved for
  arbitrary `r`: it is a claim about the `r` that G8 builds.
* **Main result** `localData_of_g7` (proved): for `r` as in G8's output (`G0Galois.G8Out`) on
  `ρ = GlueDescent.rho Tm a β`, `LocalData p r` follows, at every prime `p`, from
  `G7Clauses β ε L` (clauses of G4/G7) and `LocalGlue p Tm a β L` (the Tate-module glue
  `TorsionFieldWild` at `p ≤ D`, `TateWildTrivialL` at `p > D`, and `BetaUpper` at `p = 2`).
  `g15RamG_of_g7` composes it with g15-ram's `g15RamG_of_localData`.
* On the way (all proved): `twistShape_of_g8` (`r` is scalar where `ρ` is), `betaTame_of_odd`,
  `betaOpen_of_isLocallyConstant`, `wild_fix_root` (wild inertia fixes `μ_n`, `p² ∤ n`),
  `galChar_decomp_wild`, `betaSqWild_of_chi`, `betaCharOn_of_cocycle`, `wild_fix_small_degree`
  (wild inertia fixes every `E` with `[E:ℚ_p] < p`), `exists_finGal_ramCard_le` (Galois closure
  with `e ≤ [E:ℚ_p]!`), `exists_local_field_le` (`[L_v:ℚ_p] ≤ [L:ℚ]`).
-/

namespace G15Ram

open PkgI4 (GQp GaloisRep GQ decomp)
open LadicCond G0ModNewform

section LocalDataSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### The characterization at `p > D` -/

/-- At `p > D` the local data say exactly that `r` is trivial on wild inertia: `F` is tame, so
`P_p ⊆ G_F` (`wildFixTame`), and `r = β = 1` on `G_F ∩ P_p`. Conversely take `F = ℚ_p`. -/
theorem largePrimeData_iff (r : GaloisRep ℓ 2) :
    LargePrimeData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1 := by
  constructor
  · rintro ⟨F, β, hF, hpe, hsh, htm⟩ σ hσ
    have hfix : σ ∈ fixSet F := wildFixTame F hF hpe hσ
    have h1 := hsh σ ⟨hfix, hσ⟩
    rw [htm σ ⟨hfix, hσ⟩, Matrix.scalar_apply, Matrix.diagonal_one] at h1
    exact Units.ext h1
  · intro h
    have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
    have hcard : ramCard (⊥ : Fld p) 0 = 1 := by
      have h1 := one_le_ramCard hF 0
      have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
        unfold ramCard
        have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
        refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
        apply Subtype.ext
        obtain ⟨σ, -, hσ⟩ := a.2
        obtain ⟨τ, -, hτ⟩ := b.2
        rw [← hσ, ← hτ]
        funext x
        obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
        simp only [restr, ← hq, AlgEquiv.commutes]
      omega
    refine ⟨⊥, fun _ => 1, hF, ?_, ?_, fun _ _ => rfl⟩
    · rw [hcard]; exact (Fact.out : p.Prime).not_dvd_one
    · intro σ hσ
      rw [h σ hσ.2, Matrix.scalar_apply, Matrix.diagonal_one]
      rfl

/-- **`LocalData` at `p > D`, characterized (proved).** -/
theorem localData_large_iff (r : GaloisRep ℓ 2) (hp : (ZInQ.heightD : ℝ) < p) :
    LocalData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1 := by
  rw [← largePrimeData_iff]
  constructor
  · exact fun h => h.2 hp
  · exact fun h => ⟨fun hle => absurd hp (not_lt.mpr hle), fun _ => h⟩

/-! ### From `ρ` to `r` (linear algebra) -/

/-- If `e` intertwines `ρ` with `m ⊕ m` and `ρ(g)` is the scalar `c`, then `m(g)` is the scalar
`c`. -/
theorem mat_eq_scalar_of_intertwines {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {f : G → Module.End (PadicAlgCl ℓ) V} {m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines f m e) {g : G} {c : PadicAlgCl ℓ} (hg : f g = c • 1) :
    m g = Matrix.scalar (Fin 2) c := by
  have hv : ∀ x : Fin 2 → PadicAlgCl ℓ, (m g).mulVec x = c • x := by
    intro x
    have := h g (e.symm (x, x))
    rw [hg, LinearMap.smul_apply, Module.End.one_apply, map_smul,
      LinearEquiv.apply_symm_apply] at this
    exact (congrArg Prod.fst this).symm
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv x, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

/-! ### The smaller Props on G7's data at `p` -/

/-- **Glue on G4/G7 + R6 + D2 (N5 L719-727, L819-823; at `p > D` G3 + Néron–Ogg–Shafarevich,
N5 L848-851).** On `G_F ∩ P_p` (pushed to `G_ℚ` by `decomp`) the twisted Tate action
`a_σ μ_σ ∘ σ` (`a σ • Tm σ`) is the identity. Glazer: for `σ ∈ G_L` (`F ⊇ L_v`) the descent
datum has `a_σ μ_σ = 1`, so `a_σ Tm σ` is the Tate action of `A/L`; `A` is semistable over
`F ⊇ L_v(A[3])` (`A[5]` if `p = 3`) by Raynaud's criterion (R6, `PkgI2.RaynaudCriterion`), and
then wild inertia acts trivially on `V_ℓ` (D2, `PkgI2.D2_fixed_of_raynaud`); at `p > D`, `A` has
good reduction (G3) and inertia acts trivially (`PkgI2.inertiaTrivial_of_goodReduction`).
Only claimed for `p ≠ ℓ` (D2 and Néron–Ogg–Shafarevich are about `V_ℓ`, `ℓ ≠ p`; at `p = ℓ` it is
false in general); `g15RamG_of_g8` uses it only at `p ≠ ℓ`. -/
def TateWildTrivial {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, a (decomp p σ) • Tm (decomp p σ) = 1

/-- **Glue on G7's `β` (D3 + T16; N5 L823-844).** `β` is trivial on `G_{ℚ_p}^t ∩ G_F` for
`t > U`. At odd `p` it follows from `BetaTame` (`betaUpper_of_betaTame`); at `p = 2` from local
reciprocity with the upper numbering theorem (T16, `PkgI6.LocalReciprocityUpper`) and
`(U_F^{e+1})⁴ = U_F^{3e+1}` (D3, `GlueConductor.fourth_pow_mem`) applied to the character
`β|_{G_F}`, `ψ ≥ id`, and `max(4D², 3e) ≤ U₀` (`GlueConductor.max_le_U0`). -/
def BetaUpper (β : GQ → PadicAlgCl ℓ) (F : Fld p) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β (decomp p σ) = 1

/-- **Glue on G7's `β` at odd `p` (N5 L835-838, L848-851).** `β` is trivial on `G_F ∩ P_p`.
Proved for odd `p` from `BetaCharOn`, `BetaSqWild`, `BetaOpen` (`betaTame_of_odd`). -/
def BetaTame (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) = 1

/-- **Glue on G7 (`∂β = ε` with `ε` inflated from `Gal(L/ℚ)` and normalized; N5 L664-700).**
On `G_F` (`F ⊇ L_v`, so `decomp(G_F) ⊆ G_L`) the cochain `β` is a character. -/
def BetaCharOn (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, β (decomp p (σ * τ)) = β (decomp p σ) * β (decomp p τ)

/-- **Glue on G7 (`β² = χ`, `χ` a Dirichlet character of level `N = ∏ lev q`, `lev p = p` for
odd `p`, so `χ` is tame at odd `p`; N5 L677-683; g0-mod-field `G7Data`).** `β² = 1` on
`G_F ∩ P_p`. -/
def BetaSqWild (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) ^ 2 = 1

/-- **Glue (local constancy of `β`, g0-mod-field `G7Data`: `IsLocallyConstant β`, and the
continuity of `decomp`).** `β ∘ decomp` is trivial on `G_{F'}` for some finite Galois `F'`. -/
def BetaOpen (β : GQ → PadicAlgCl ℓ) : Prop :=
  ∃ F' : Fld p, IsFinGal F' ∧ ∀ σ ∈ fixSet F', β (decomp p σ) = 1

/-! ### The reduction -/

/-- **`TwistShape` from G8's output (proved).** With `ρ = β⁻¹ a Tm` and `a Tm = 1` on
`G_F ∩ P_p`, `ρ = β⁻¹` there, and `r` is the same scalar (`e` intertwines `ρ` with `r ⊕ r`). -/
theorem twistShape_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r) {F : Fld p}
    (hT : TateWildTrivial Tm a F) :
    TwistShape p r F (fun σ => (β (decomp p σ))⁻¹) := by
  obtain ⟨-, e, he, -⟩ := hG8
  intro σ hσ
  have hρ : GlueDescent.rho Tm a β (decomp p σ) = (β (decomp p σ))⁻¹ • 1 := by
    unfold GlueDescent.rho
    rw [mul_smul, hT σ hσ]
  exact mat_eq_scalar_of_intertwines he hρ

theorem twistUpper_of_betaUpper {β : GQ → PadicAlgCl ℓ} {F : Fld p} {U : ℝ}
    (h : BetaUpper β F U) : TwistUpper p F (fun σ => (β (decomp p σ))⁻¹) U := by
  intro t ht σ hσ
  simp only [h t ht σ hσ, inv_one]

theorem twistTame_of_betaTame {β : GQ → PadicAlgCl ℓ} {F : Fld p}
    (h : BetaTame β F) : TwistTame p F (fun σ => (β (decomp p σ))⁻¹) := by
  intro σ hσ
  simp only [h σ hσ, inv_one]

/-- **`BetaUpper` from `BetaTame` (proved):** `G_{ℚ_p}^t ⊆ P_p` for `t > 0` (`upperWild`). -/
theorem betaUpper_of_betaTame {β : GQ → PadicAlgCl ℓ} {F : Fld p} {U : ℝ} (hU : 0 ≤ U)
    (h : BetaTame β F) : BetaUpper β F U := by
  intro t ht σ hσ
  exact h σ ⟨hσ.2, upperWild t (lt_of_le_of_lt hU ht) hσ.1⟩

/-- **Corrected form of `LocalData p r`: the local data of G7 at `p` (GLUE on G4/G7 + R6 + D2 +
D3 + T16; N5 L813-851).** A Prop on G7's data `(Tm, a, β)` instead of on the bare `r`: at
`p ≤ D` a finite Galois `F ⊆ ℚ̄_p` with `e(F/ℚ_p) ≤ (DG₀)!` (Glazer: the Galois closure of
`L_v(A[3])`, `A[5]` if `p = 3`, of degree `≤ (DG₀)!`) on which `TateWildTrivial` and
`BetaUpper` (bound `U₀`) hold; at `p > D` a tame finite Galois `F` (the Galois closure of `L_v`,
`[L_v:ℚ_p] ≤ D < p`) with `TateWildTrivial` and `BetaTame`. -/
def G7LocalData {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TateWildTrivial Tm a F ∧ BetaUpper β F U0) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TateWildTrivial Tm a F ∧ BetaTame β F)

/-- **`LocalData p r` for G8's `r` (proved).** For `r` as in G8's output on
`ρ = GlueDescent.rho Tm a β`, `G7LocalData p Tm a β` gives `LocalData p r`, with the local
twist `σ ↦ β(σ)⁻¹`. -/
theorem localData_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (h : G7LocalData (p := p) Tm a β) : LocalData p r := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨F, hF, he, hT, hB⟩ := h.1 hp
    exact ⟨F, _, hF, he, twistShape_of_g8 hG8 hT, twistUpper_of_betaUpper hB⟩
  · obtain ⟨F, hF, he, hT, hB⟩ := h.2 hp
    exact ⟨F, _, hF, he, twistShape_of_g8 hG8 hT, twistTame_of_betaTame hB⟩

/-- **`G15RamG D u` from G8's outputs for `D.r5`, `D.r3` and G7's local data (proved).**
Composes `localData_of_g8` with g15-ram's `g15RamG_of_localData`. The G7/G8 data for `r₅` and
`r₃` may live on different models (`K₅`, `A₅`) and (`K₃`, `A₃`). -/
theorem g15RamG_of_g8 {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A) (u : ℚ)
    {K₅ : Type} [Field K₅] [NumberField K₅] {A₅ : PkgI3.AbVar K₅}
    {Tm₅ : GQ → Module.End (PadicAlgCl 5) (G0Galois.Vb A₅ 5)} {a₅ β₅ : GQ → PadicAlgCl 5}
    (hG8₅ : G0Galois.G8Out A₅ 5 (GlueDescent.rho Tm₅ a₅ β₅) D.r5)
    {K₃ : Type} [Field K₃] [NumberField K₃] {A₃ : PkgI3.AbVar K₃}
    {Tm₃ : GQ → Module.End (PadicAlgCl 3) (G0Galois.Vb A₃ 3)} {a₃ β₃ : GQ → PadicAlgCl 3}
    (hG8₃ : G0Galois.G8Out A₃ 3 (GlueDescent.rho Tm₃ a₃ β₃) D.r3)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G7LocalData p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅)
    (h3 : G7LocalData (p := 5) Tm₃ a₃ β₃)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_localData D u (fun p hp hp5 => @localData_of_g8 p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hG8₅
    (h5 p hp hp5)) (localData_of_g8 hG8₃ h3) h11₅ h11₃

/-! ### `BetaTame` at odd `p` (proved) -/

/-- A wild `σ` has `σ^{p^a}` fixing a given finite Galois `F'` for some `a`: the restriction
`s ∈ Gal(F'/ℚ_p)` has order `p^a m` with `p ∤ m`, and the wild `σ^{p^a}` has restriction of
order `m` prime to `p`, so it fixes `F'` (`fix_of_wild_pow`). -/
theorem exists_pow_fix_of_wild {σ : GQp p} (hσ : σ ∈ wildSet) {F' : Fld p} (hF' : IsFinGal F') :
    ∃ a : ℕ, σ ^ (p ^ a) ∈ fixSet F' := by
  haveI : FiniteDimensional ℚ_[p] F' := hF'.1
  haveI : Normal ℚ_[p] F' := hF'.2.to_normal
  set s := AlgEquiv.restrictNormalHom F' σ with hs
  have hm0 : 0 < orderOf s := orderOf_pos s
  obtain ⟨a, m, hpm, hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p
    (Fact.out : p.Prime).ne_one
  refine ⟨a, ?_⟩
  have hm0' : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hdec; omega
  intro x hx
  have hsm : AlgEquiv.restrictNormalHom F' ((σ ^ (p ^ a)) ^ m) = 1 := by
    rw [map_pow, map_pow, ← hs, ← pow_mul, ← hdec, pow_orderOf_eq_one]
  have hfix : ((σ ^ (p ^ a)) ^ m) x = x :=
    (AlgEquiv.restrictNormal_eq_one_iff F' _).mp hsm x hx
  exact fix_of_wild_pow (wildSet_pow hσ _) hm0' hpm hfix

theorem fixSet_pow {F : Fld p} {σ : GQp p} (hσ : σ ∈ fixSet F) (k : ℕ) : σ ^ k ∈ fixSet F := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ, AlgEquiv.mul_apply, hσ x hx, ih x hx]

/-- **`BetaTame` at odd `p` (proved).** If `β` is a character on `G_F`, `β² = 1` on
`G_F ∩ P_p`, and `β ∘ decomp` dies on an open `G_{F'}`, then `β = 1` on `G_F ∩ P_p` for odd `p`:
`β(σ)^{p^a} = β(σ^{p^a}) = 1` with `σ^{p^a} ∈ G_{F'}`, and `β(σ)² = 1`, `gcd(p^a, 2) = 1`. -/
theorem betaTame_of_odd (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {F : Fld p}
    (hmul : BetaCharOn β F) (hsq : BetaSqWild β F) (hopen : BetaOpen (p := p) β) :
    BetaTame β F := by
  obtain ⟨F', hF', h1⟩ := hopen
  intro σ hσ
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ.2 hF'
  have hpow : ∀ k : ℕ, β (decomp p (σ ^ (k + 1))) = β (decomp p σ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ σ (k + 1), hmul _ (fixSet_pow hσ.1 _) _ hσ.1, ih, ← pow_succ]
  have hpa : β (decomp p σ) ^ (p ^ a) = 1 := by
    have hpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
    obtain ⟨k, hk⟩ : ∃ k, p ^ a = k + 1 := ⟨p ^ a - 1, by omega⟩
    rw [hk, ← hpow k, ← hk]
    exact h1 _ ha
  have hcop : Nat.Coprime (p ^ a) 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2
  have := pow_gcd_eq_one.mpr ⟨hpa, hsq σ hσ⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this

/-- `β(1) = 1` for a nonzero `β` that is a character on `G_F`. -/
theorem beta_one_of_charOn {β : GQ → PadicAlgCl ℓ} {F : Fld p} (hm : BetaCharOn β F)
    (h0 : β 1 ≠ 0) : β 1 = 1 := by
  have h := hm 1 (fun _ _ => rfl) 1 (fun _ _ => rfl)
  rw [mul_one, map_one] at h
  have h' : β 1 * β 1 = β 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ h0 h'

/-- **`BetaOpen` from local constancy (proved).** If `β : G_ℚ → ℚ̄_ℓ` is locally constant
(g0-mod-field's `G7Data` has `IsLocallyConstant β` for the `ℂ^×`-valued `β`; any transport of
the values preserves it) and `β(1) = 1`, then `β ∘ decomp` is trivial on `G_{F'}` for a finite
Galois `F'`: `decomp` is continuous (Mathlib's `Field.absoluteGaloisGroup.map`), the fibre over
`1` is an open neighbourhood of `1`, so it contains the fixer of a finite `E`
(`krullTopology_mem_nhds_one_iff`), and of its normal closure `F'`. -/
theorem betaOpen_of_isLocallyConstant {β : GQ → PadicAlgCl ℓ} (hβ : IsLocallyConstant β)
    (h1 : β 1 = 1) : BetaOpen (p := p) β := by
  set S : Set (GQp p) := {σ | β (decomp p σ) = 1} with hSdef
  have hcont : Continuous (decomp p) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous
  have hS : S ∈ nhds (1 : GQp p) := by
    have hopen : IsOpen S := (hβ.comp_continuous hcont).isOpen_fiber 1
    refine hopen.mem_nhds ?_
    show β (decomp p 1) = 1
    rw [map_one, h1]
  obtain ⟨E, hEfin, hE⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] (Kbar p) S).mp hS
  set F' := IntermediateField.normalClosure ℚ_[p] E (Kbar p) with hF'
  haveI : FiniteDimensional ℚ_[p] F' := normalClosure.is_finiteDimensional ℚ_[p] E (Kbar p)
  haveI : Normal ℚ_[p] F' := normalClosure.normal ℚ_[p] E (Kbar p)
  refine ⟨F', ⟨inferInstance, IsGalois.mk⟩, fun σ hσ => ?_⟩
  have hσE : σ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hσ x (E.le_normalClosure hx)
  exact hE hσE

/-- **Corrected form at odd `p` (GLUE).** `G7LocalData` with the `β`-side replaced by
`BetaCharOn` and `BetaSqWild` on the same `F` (local constancy and `β(1) ≠ 0` are separate
hypotheses of `g7LocalData_of_odd`). -/
def G7LocalDataOdd {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TateWildTrivial Tm a F ∧ BetaCharOn β F ∧ BetaSqWild β F) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TateWildTrivial Tm a F ∧ BetaCharOn β F ∧ BetaSqWild β F)

/-- **`G7LocalData` at odd `p` (proved)** from `G7LocalDataOdd`, local constancy of `β` and
`β(1) ≠ 0` (`G0Galois.G7Out` has `∀ g, β g ≠ 0`). -/
theorem g7LocalData_of_odd (hp2 : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a β : GQ → PadicAlgCl ℓ}
    (hβ : IsLocallyConstant β) (h0 : β 1 ≠ 0) (h : G7LocalDataOdd (p := p) Tm a β) :
    G7LocalData (p := p) Tm a β := by
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨F, hF, he, hT, hm, hs⟩ := h.1 hp
    have hopen := betaOpen_of_isLocallyConstant (p := p) hβ (beta_one_of_charOn hm h0)
    exact ⟨F, hF, he, hT, betaUpper_of_betaTame hU0 (betaTame_of_odd hp2 hm hs hopen)⟩
  · obtain ⟨F, hF, he, hT, hm, hs⟩ := h.2 hp
    have hopen := betaOpen_of_isLocallyConstant (p := p) hβ (beta_one_of_charOn hm h0)
    exact ⟨F, hF, he, hT, betaTame_of_odd hp2 hm hs hopen⟩

/-! ### `BetaSqWild` at odd `p` from `β² = χ` (proved)

Wild inertia fixes every root of unity of order `n` with `p² ∤ n` (`wild_fix_root`, norms only);
so the cyclotomic character mod `N`, and every Dirichlet character mod `N`, is trivial on
`decomp(P_p)` when `p² ∤ N` (`galChar_decomp_wild`); and `p² ∤ chiLevel T₋` for odd `p`
(`not_sq_dvd_chiLevel`). -/

theorem norm_eq_one_of_pow_eq_one {η : Kbar p} {n : ℕ} (hn : 0 < n) (h : η ^ n = 1) :
    ‖η‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp this

theorem norm_sum_range_le_one {f : ℕ → Kbar p} (m : ℕ) (hf : ∀ k < m, ‖f k‖ ≤ 1) :
    ‖∑ k ∈ Finset.range m, f k‖ ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (ih fun k hk => hf k (by omega)) (hf m (by omega)))

theorem norm_pow_sub_one_le {η : Kbar p} (h1 : ‖η‖ = 1) (i : ℕ) : ‖η ^ i - 1‖ ≤ ‖η - 1‖ := by
  have he : η ^ i - 1 = (∑ k ∈ Finset.range i, η ^ k) * (η - 1) := (geom_sum_mul η i).symm
  rw [he, norm_mul]
  have hs : ‖∑ k ∈ Finset.range i, η ^ k‖ ≤ 1 :=
    norm_sum_range_le_one i fun k _ => by rw [norm_pow, h1, one_pow]
  calc ‖∑ k ∈ Finset.range i, η ^ k‖ * ‖η - 1‖ ≤ 1 * ‖η - 1‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖η - 1‖ := one_mul _

/-- A root of unity of order prime to `p` congruent to `1` is `1`. -/
theorem eq_one_of_pow_eq_one_of_norm_lt {η : Kbar p} {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m)
    (hη : η ^ m = 1) (hlt : ‖η - 1‖ < 1) : η = 1 := by
  by_contra hne
  have h1 : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one hm0 hη
  have hsub : η - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hgeom : ∑ k ∈ Finset.range m, η ^ k = 0 := by
    have := geom_sum_mul η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right hsub
  have hm : (m : Kbar p) = ∑ k ∈ Finset.range m, (1 - η ^ k) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hlt' : ‖∑ k ∈ Finset.range m, (1 - η ^ k)‖ < 1 :=
    norm_sum_range_lt one_pos m fun k _ => by
      rw [norm_sub_rev]; exact lt_of_le_of_lt (norm_pow_sub_one_le h1 k) hlt
  rw [← hm, norm_natCast_kbar hpm] at hlt'
  exact lt_irrefl _ hlt'

/-- Wild inertia fixes roots of unity of order prime to `p`. -/
theorem wild_fix_prime_to_p {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} {m : ℕ} (hm0 : 0 < m)
    (hpm : ¬ p ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0.ne'] at hζ; exact zero_ne_one hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηm : η ^ m = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : ‖η - 1‖ < 1 := by
    have he : η - 1 = (σ ζ - ζ) * ζ⁻¹ := by rw [hη, sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, norm_mul, norm_inv]
    have hw := hσ ζ hζ0
    have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    rw [mul_inv_lt_iff₀ hpos, one_mul]
    exact hw
  have := eq_one_of_pow_eq_one_of_norm_lt hm0 hpm hηm hlt
  rw [hη, mul_inv_eq_one₀ hζ0] at this
  exact this

/-- Wild inertia fixes the `p`-th roots of unity. -/
theorem wild_fix_p_root {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} (hζ : ζ ^ p = 1) :
    σ ζ = ζ := by
  have hp := (Fact.out : p.Prime)
  by_contra hne
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hζ; exact zero_ne_one hζ
  have hζ1 : ζ ≠ 1 := by rintro rfl; exact hne (map_one σ)
  have h1ζ : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hp.pos hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηp : η ^ p = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hη1 : η ≠ 1 := by
    intro h; rw [hη, mul_inv_eq_one₀ hζ0] at h; exact hne h
  have h1η : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one hp.pos hηp
  have hord : orderOf η = p := orderOf_eq_prime hηp hη1
  have hprim : IsPrimitiveRoot η p := by
    have := IsPrimitiveRoot.orderOf η
    rwa [hord] at this
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hζ
  have hx0 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  have hw := hσ (ζ - 1) hx0
  have he : σ (ζ - 1) - (ζ - 1) = ζ * (η - 1) := by
    rw [map_sub, map_one, hη]; field_simp; ring
  rw [he, norm_mul, h1ζ, one_mul, ← hi] at hw
  exact lt_irrefl _ (lt_of_lt_of_le hw (norm_pow_sub_one_le h1η i))

/-- **Wild inertia fixes `μ_n` for `p² ∤ n` (proved).** -/
theorem wild_fix_root {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} {n : ℕ} (hn0 : 0 < n)
    (hp2 : ¬ p ^ 2 ∣ n) (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hp := (Fact.out : p.Prime)
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hpm : ¬ p ∣ m := by
      rintro ⟨k, rfl⟩; exact hp2 ⟨k, by ring⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hn0
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [zero_pow hn0.ne'] at hζ; exact zero_ne_one hζ
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    have hy : σ (ζ ^ p) = ζ ^ p :=
      wild_fix_prime_to_p hσ hm0 hpm (by rw [← pow_mul, hζ])
    have hz : σ (ζ ^ m) = ζ ^ m :=
      wild_fix_p_root hσ (by rw [← pow_mul, mul_comm, hζ])
    have hb : ((p.gcd m : ℕ) : ℤ) = p * p.gcdA m + m * p.gcdB m := Nat.gcd_eq_gcd_ab p m
    rw [hcop.gcd_eq_one, Nat.cast_one] at hb
    have hdec : ζ = (ζ ^ p) ^ (p.gcdA m) * (ζ ^ m) ^ (p.gcdB m) := by
      rw [← zpow_natCast, ← zpow_natCast (ζ) m, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hb,
        zpow_one]
    rw [hdec, map_mul, map_zpow₀, map_zpow₀, hy, hz]
  · exact wild_fix_prime_to_p hσ hn0 hpn hζ

/-- The embedding `ℚ̄ → ℚ̄_p` that `decomp` uses. -/
def embP : PkgI4.Qbar →+* Kbar p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

/-- `embP ∘ decomp σ = σ ∘ embP` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
theorem decomp_spec (σ : GQp p) (x : PkgI4.Qbar) : embP (decomp p σ x) = σ (embP x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem decomp_fix_root {σ : GQp p} (hσ : σ ∈ wildSet) {x : PkgI4.Qbar} {n : ℕ} (hn0 : 0 < n)
    (hp2 : ¬ p ^ 2 ∣ n) (hx : x ^ n = 1) : decomp p σ x = x := by
  apply (embP (p := p)).injective
  rw [decomp_spec]
  exact wild_fix_root hσ hn0 hp2 (by rw [← map_pow, hx, map_one])

/-- **The cyclotomic character mod `N` is trivial on `decomp(P_p)` when `p² ∤ N` (proved).** -/
theorem cyc_decomp_wild {N : ℕ} [NeZero N] (hp2 : ¬ p ^ 2 ∣ N) {σ : GQp p}
    (hσ : σ ∈ wildSet) : GlueDescent.B2Q.cyc N (decomp p σ) = 1 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hN1 : N = 1
  · subst hN1; exact Subsingleton.elim _ _
  haveI : Fact (1 < N) := ⟨by omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  have hu := modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (GlueDescent.B2Q.toRingAut (decomp p σ)) (c := 1) (fun t ht => by
      rw [ZMod.val_one, pow_one]
      have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      exact decomp_fix_root hσ hN0 hp2 htN)
  have hc : GlueDescent.B2Q.cyc N (decomp p σ) = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (GlueDescent.B2Q.toRingAut (decomp p σ)) := rfl
  rw [hc, Units.val_one]
  exact hu.symm

/-- **Every Dirichlet character mod `N`, as a Galois character, is trivial on `decomp(P_p)`
when `p² ∤ N` (proved).** -/
theorem galChar_decomp_wild {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hp2 : ¬ p ^ 2 ∣ N) {σ : GQp p} (hσ : σ ∈ wildSet) :
    GlueDescent.B2Q.galChar χ (decomp p σ) = 1 := by
  change χ.toUnitHom (GlueDescent.B2Q.cyc N (decomp p σ)) = 1
  rw [cyc_decomp_wild hp2 hσ, map_one]

/-- **`p² ∤ chiLevel T₋` for odd `p` (proved)**, `T₋` a finite set of primes (`lev q = q` for odd
`q`, `lev 2 = 4`). -/
theorem not_sq_dvd_chiLevel (hp2 : p ≠ 2) {Tm : Finset ℕ} (hTm : ∀ q ∈ Tm, q.Prime) :
    ¬ p ^ 2 ∣ GlueDescent.chiLevel Tm := by
  have hp := (Fact.out : p.Prime)
  intro h
  have hpp : p ∣ GlueDescent.chiLevel Tm := (dvd_pow_self p two_ne_zero).trans h
  have hmem : p ∈ Tm := by
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpp
    have hqp := hTm q hq
    unfold GlueDescent.lev at hpq
    split_ifs at hpq with h2
    · subst h2
      have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpq)
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
    · rwa [(Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq]
  unfold GlueDescent.chiLevel at h
  rw [← Finset.mul_prod_erase Tm _ hmem] at h
  have hlev : GlueDescent.lev p = p := by unfold GlueDescent.lev; rw [if_neg hp2]
  rw [hlev, pow_two] at h
  have hdvd := Nat.dvd_of_mul_dvd_mul_left hp.pos h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have hqp := hTm q (Finset.mem_of_mem_erase hq)
  have hqne := Finset.ne_of_mem_erase hq
  unfold GlueDescent.lev at hpq
  split_ifs at hpq with h2
  · subst h2
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpq)
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
  · exact hqne ((Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq).symm

/-- **`BetaSqWild` at odd `p` (proved)** from `β² = ι ∘ χ` on `G_F` (`χ` a Dirichlet character
mod `N = chiLevel T₋` for a set `T₋` of primes, as in g0-mod-field's `G7Data`; `ι` the transport
of values `ℂ^× → ℚ̄_ℓ^×`). -/
theorem betaSqWild_of_chi (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {F : Fld p} {Tm : Finset ℕ}
    (hTm : ∀ q ∈ Tm, q.Prime) [NeZero (GlueDescent.chiLevel Tm)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tm)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ σ ∈ fixSet F, β (decomp p σ) ^ 2 = (ι (GlueDescent.B2Q.galChar χ (decomp p σ)) :
      PadicAlgCl ℓ)) :
    BetaSqWild β F := by
  intro σ hσ
  rw [hsq σ hσ.1, galChar_decomp_wild χ (not_sq_dvd_chiLevel hp2 hTm) hσ.2, map_one,
    Units.val_one]

/-! ### `BetaCharOn` from `∂β = ε` (proved) -/

/-- `decomp(G_F) ⊆ G_L` when `F ⊇ embP(L)` (`L ⊆ ℚ̄`; `F ⊇ L_v` for the place `v` of `embP`). -/
theorem decomp_fix_of_le {L : IntermediateField ℚ PkgI4.Qbar} {F : Fld p}
    (hLF : ∀ x ∈ L, embP x ∈ F) {σ : GQp p} (hσ : σ ∈ fixSet F) :
    ∀ x ∈ L, decomp p σ x = x := by
  intro x hx
  apply (embP (p := p)).injective
  rw [decomp_spec]
  exact hσ _ (hLF x hx)

/-- **`BetaCharOn` from G7's `∂β = ε` (proved).** If `β g β h = ε(g,h) β(gh)` (a clause of
`G0Galois.G7Out`), `ε = 1` on `G_L × G_L` (`ε` is inflated from `Gal(L/ℚ)` and normalized,
g0-mod-field `DescentDatum`), and `F ⊇ embP(L)`, then `β` is a character on `G_F`. -/
theorem betaCharOn_of_cocycle {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) {L : IntermediateField ℚ PkgI4.Qbar}
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    {F : Fld p} (hLF : ∀ x ∈ L, embP x ∈ F) : BetaCharOn β F := by
  intro σ hσ τ hτ
  rw [hβ, hε _ _ (decomp_fix_of_le hLF hσ) (decomp_fix_of_le hLF hτ), one_mul, map_mul]

/-! ### Wild inertia fixes fields of degree `< p` (proved) -/

/-- **Wild inertia fixes every finite `E ⊆ ℚ̄_p` with `[E:ℚ_p] < p` (proved).** For `x ∈ E`
and wild `σ`, `σ^{p^a}` fixes the Galois closure of `ℚ_p(x)` (`exists_pow_fix_of_wild`), so the
`σ`-orbit of `x` has `p`-power size; its elements are distinct roots of the minimal polynomial
of `x`, of degree `≤ [E:ℚ_p] < p`; so the orbit is `{x}`. (This replaces "the Galois closure of
`L_v` is tame" at `p > D`.) -/
theorem wild_fix_small_degree {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) : wildSet ⊆ fixSet E := by
  classical
  intro σ hσ x hx
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] ({x} : Set (Kbar p))
  have hF : IsFinGal F.toIntermediateField := ⟨inferInstance, inferInstance⟩
  have hxF : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] {x} rfl
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ hF
  have hper : Function.IsPeriodicPt σ (p ^ a) x := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [← AlgEquiv.coe_pow]
    exact ha x hxF
  set k := Function.minimalPeriod σ x with hk
  have hkdvd : k ∣ p ^ a := hper.minimalPeriod_dvd
  have hkpos : 0 < k := hper.minimalPeriod_pos (pow_pos (Fact.out : p.Prime).pos a)
  -- the orbit lies in the roots of the minimal polynomial
  have hint : IsIntegral ℚ_[p] x := IsIntegral.of_finite ℚ_[p] (⟨x, hx⟩ : E) |>.map E.val
  set P := minpoly ℚ_[p] x with hP
  have hroot : ∀ i : ℕ, (σ^[i] x) ∈ P.aroots (Kbar p) := by
    intro i
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [← AlgEquiv.coe_pow, Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval,
      map_zero]
  have hcard : k ≤ P.natDegree := by
    have hinj : Set.InjOn (fun i => σ^[i] x) (Finset.range k : Set ℕ) := by
      intro i hi j hj hij
      have := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x)
      exact this (by simpa using hi) (by simpa using hj) hij
    have hsub : (Finset.range k).image (fun i => σ^[i] x) ⊆ (P.aroots (Kbar p)).toFinset := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact Multiset.mem_toFinset.mpr (hroot i)
    calc k = ((Finset.range k).image (fun i => σ^[i] x)).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ (P.aroots (Kbar p)).toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (P.aroots (Kbar p)) := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := by
          rw [Polynomial.aroots_def]
          exact (Polynomial.card_roots' _).trans Polynomial.natDegree_map_le
  have hdeg : P.natDegree ≤ Module.finrank ℚ_[p] E := by
    have h1 : (minpoly ℚ_[p] (⟨x, hx⟩ : E)).natDegree ≤ Module.finrank ℚ_[p] E :=
      minpoly.natDegree_le _
    rwa [IntermediateField.minpoly_eq] at h1
  have hkp : k < p := lt_of_le_of_lt (hcard.trans hdeg) hE
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hkdvd
  have hb0 : b = 0 := by
    by_contra hb0
    have : p ≤ p ^ b := Nat.le_self_pow hb0 p
    omega
  rw [hb0, pow_zero] at hb
  have h1 : Function.IsPeriodicPt σ 1 x := by
    rw [← hb]; exact Function.isPeriodicPt_minimalPeriod σ x
  exact h1

/-- **`LocalData` at `p > D` from a field of degree `< p` (proved).** If `E ⊆ ℚ̄_p` has
`[E:ℚ_p] < p` (Glazer: `E = L_v`, `[L_v:ℚ_p] ≤ D < p`) and `a·Tm` and `β` are trivial on
`G_E ∩ P_p`, then `LocalData p r` holds at `p > D` for G8's `r`. -/
theorem localData_large_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hp : (ZInQ.heightD : ℝ) < p) {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) (hT : TateWildTrivial Tm a E) (hB : BetaTame β E) :
    LocalData p r := by
  rw [localData_large_iff r hp]
  intro σ hσ
  have hfix := wild_fix_small_degree hE hσ
  have h1 : ((r.restrictLocal p σ : GL (Fin 2) (PadicAlgCl ℓ)) :
      Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = Matrix.scalar (Fin 2) ((β (decomp p σ))⁻¹) :=
    twistShape_of_g8 hG8 hT σ ⟨hfix, hσ⟩
  rw [hB σ ⟨hfix, hσ⟩, inv_one, Matrix.scalar_apply, Matrix.diagonal_one] at h1
  exact Units.ext h1

/-! ### The Galois closure and `e ≤ [E:ℚ_p]!` (proved) -/

/-- `e(F/ℚ_p) ≤ [F:ℚ_p]` for finite Galois `F`. -/
theorem ramCard_zero_le_finrank {F : Fld p} (hF : IsFinGal F) :
    ramCard F 0 ≤ Module.finrank ℚ_[p] F := by
  haveI : FiniteDimensional ℚ_[p] F := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  rw [ramCard_zero_eq F hF, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_le_card_group _

/-- **A finite `E ⊆ ℚ̄_p` lies in a finite Galois `F` with `e(F/ℚ_p) ≤ n!` when
`[E:ℚ_p] ≤ n` (proved).** `F` = the splitting field in `ℚ̄_p` of the minimal polynomial `f` of a
primitive element of `E`; `Gal(F/ℚ_p)` acts faithfully on the `≤ deg f ≤ n` roots
(as in `GlueRepo.Numerics.splitting_degree_le`). -/
theorem exists_finGal_ramCard_le {E : Fld p} [FiniteDimensional ℚ_[p] E] {n : ℕ}
    (hE : Module.finrank ℚ_[p] E ≤ n) :
    ∃ F : Fld p, IsFinGal F ∧ E ≤ F ∧ ramCard F 0 ≤ n.factorial := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[p] E
  set a : Kbar p := (α : Kbar p) with ha
  have hint : IsIntegral ℚ_[p] a := (IsIntegral.of_finite ℚ_[p] α).map E.val
  set f := minpoly ℚ_[p] a with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  have hsplit : (f.map (algebraMap ℚ_[p] (Kbar p))).Splits := IsAlgClosed.splits _
  set F : Fld p := IntermediateField.adjoin ℚ_[p] (f.rootSet (Kbar p)) with hFdef
  haveI : Polynomial.IsSplittingField ℚ_[p] F f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  haveI : FiniteDimensional ℚ_[p] F := Polynomial.IsSplittingField.finiteDimensional F f
  have hsep : f.Separable := minpoly.irreducible hint |>.separable
  haveI : IsGalois ℚ_[p] F := IsGalois.of_separable_splitting_field hsep
  have hdeg : f.natDegree ≤ n := by
    have h1 : (minpoly ℚ_[p] α).natDegree ≤ Module.finrank ℚ_[p] E := minpoly.natDegree_le _
    rw [IntermediateField.minpoly_eq] at h1
    exact h1.trans hE
  have hfin : Module.finrank ℚ_[p] F ≤ n.factorial := by
    rw [(Polynomial.IsSplittingField.algEquiv F f).toLinearEquiv.finrank_eq,
      ← Polynomial.Gal.card_of_separable hsep]
    have : Fact ((f.map (algebraMap ℚ_[p] f.SplittingField)).Splits) :=
      ⟨Polynomial.SplittingField.splits f⟩
    calc Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
          Nat.card_le_card_of_injective _ (Polynomial.Gal.galActionHom_injective f _)
      _ = (Nat.card (f.rootSet f.SplittingField)).factorial := Nat.card_perm
      _ ≤ n.factorial := by
          apply Nat.factorial_le
          rw [Nat.card_coe_set_eq]
          exact (Polynomial.ncard_rootSet_le f _).trans hdeg
  have hEF : E ≤ F := by
    intro y hy
    have h1 : (⟨y, hy⟩ : E) ∈ IntermediateField.adjoin ℚ_[p] {α} := by rw [hα]; trivial
    have h2 : y ∈ (IntermediateField.adjoin ℚ_[p] {α}).map E.val :=
      ⟨⟨y, hy⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have hroot : a ∈ f.rootSet (Kbar p) := by
      rw [Polynomial.mem_rootSet]
      exact ⟨hf0, minpoly.aeval ℚ_[p] a⟩
    have hle : IntermediateField.adjoin ℚ_[p] {E.val α} ≤ F :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.subset_adjoin _ _ hroot)
    exact hle h2
  have hFG : IsFinGal F := ⟨inferInstance, inferInstance⟩
  exact ⟨F, hFG, hEF, (ramCard_zero_le_finrank hFG).trans hfin⟩

theorem tateWildTrivial_mono {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ} {E F : Fld p} (hEF : E ≤ F)
    (h : TateWildTrivial Tm a E) : TateWildTrivial Tm a F :=
  fun σ hσ => h σ ⟨fun x hx => hσ.1 x (hEF hx), hσ.2⟩

theorem betaUpper_mono {β : GQ → PadicAlgCl ℓ} {E F : Fld p} {U : ℝ} (hEF : E ≤ F)
    (h : BetaUpper β E U) : BetaUpper β F U :=
  fun t ht σ hσ => h t ht σ ⟨hσ.1, fun x hx => hσ.2 x (hEF hx)⟩

/-- **`LocalData` at `p ≤ D` from a field of degree `≤ DG₀` (proved).** If `E ⊆ ℚ̄_p` has
`[E:ℚ_p] ≤ DG₀` (Glazer: `E = L_v(A[3])`, `A[5]` if `p = 3`) and `TateWildTrivial`, `BetaUpper`
hold on `E`, then `LocalData p r` holds at `p ≤ D` for G8's `r` (`F` = the Galois closure,
`exists_finGal_ramCard_le`). -/
theorem localData_small_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0)
    (hT : TateWildTrivial Tm a E) (hB : BetaUpper β E U0) : SmallPrimeData p r := by
  obtain ⟨F, hF, hEF, he⟩ := exists_finGal_ramCard_le hE
  exact ⟨F, _, hF, he, twistShape_of_g8 hG8 (tateWildTrivial_mono hEF hT),
    twistUpper_of_betaUpper (betaUpper_mono hEF hB)⟩

/-! ### Assembly at odd `p` (proved) -/

/-- **`LocalData p r` at odd `p` for G8's `r`, from G7's clauses and one named glue Prop
(proved).** Hypotheses:
* G8's output for `ρ = GlueDescent.rho Tm a β` (`G0Galois.G8Out`, proved by g0-mod-galois `g8`);
* clauses of G7 (`G0Galois.G7Out`: `∂β = ε`, `β ≠ 0`; g0-mod-field `G7Data`/`DescentDatum`,
  with the values moved to `ℚ̄_ℓ` by `ι`: `β` locally constant, `β² = ι ∘ χ` for a Dirichlet
  character `χ` mod `chiLevel T₋`, `T₋` a set of primes, and `ε = 1` on `G_L × G_L`, as `ε` is
  inflated from `Gal(L/ℚ)` with `ε(1,1) = 1`);
* at `p ≤ D`: a finite `E ⊆ ℚ̄_p` containing `embP(L)` with `[E:ℚ_p] ≤ DG₀` (Glazer:
  `E = L_v(A[3])`, `A[5]` if `p = 3`) and `TateWildTrivial` on `E`;
* at `p > D`: a finite `E ⊇ embP(L)` with `[E:ℚ_p] < p` (Glazer: `E = L_v`, degree `≤ D`) and
  `TateWildTrivial` on `E`.
The `β`-side (`BetaUpper`, `BetaTame`) is fully proved from these clauses. -/
theorem localData_of_g7_odd (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hβε : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (hβlc : IsLocallyConstant β)
    {Tmin : Finset ℕ} (hTm : ∀ q ∈ Tmin, q.Prime) [NeZero (GlueDescent.chiLevel Tmin)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ))
    {L : IntermediateField ℚ PkgI4.Qbar}
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    (hsmall : (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 ∧
      TateWildTrivial Tm a E)
    (hlarge : (ZInQ.heightD : ℝ) < p → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E < p ∧ TateWildTrivial Tm a E) :
    LocalData p r := by
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  have htame : ∀ E : Fld p, (∀ x ∈ L, embP x ∈ E) → BetaTame β E := by
    intro E hLE
    have hm := betaCharOn_of_cocycle (p := p) hβε hε hLE
    have hs := betaSqWild_of_chi hp2 (F := E) hTm χ ι (fun σ _ => hsq _)
    have ho := betaOpen_of_isLocallyConstant (p := p) hβlc (beta_one_of_charOn hm (hβ0 1))
    exact betaTame_of_odd hp2 hm hs ho
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨E, hEfd, hLE, hdeg, hT⟩ := hsmall hp
    exact localData_small_of_g8 hG8 hdeg hT (betaUpper_of_betaTame hU0 (htame E hLE))
  · obtain ⟨E, hEfd, hLE, hdeg, hT⟩ := hlarge hp
    exact (localData_large_of_g8 hG8 hp hdeg hT (htame E hLE)).2 hp

/-! ### `p > D` from `[L:ℚ] ≤ D` (proved) -/

/-- **`[ℚ_p · embP(L) : ℚ_p] ≤ [L:ℚ]` (proved).** For a number field `L ⊆ ℚ̄`, the field
`E = ℚ_p(embP α)` (`α` a primitive element of `L`) contains `embP(L)` and has degree
`≤ deg minpoly_ℚ α = [L:ℚ]` (the minimal polynomial over `ℚ_p` divides the image of the one
over `ℚ`). This is `[L_v:ℚ_p] ≤ [L:ℚ]`. -/
theorem exists_local_field_le (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ (∀ x ∈ L, embP x ∈ E) ∧
      Module.finrank ℚ_[p] E ≤ Module.finrank ℚ L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  set αQ : PkgI4.Qbar := (α : PkgI4.Qbar) with hαQ
  have hintQ : IsIntegral ℚ αQ := (IsIntegral.of_finite ℚ α).map L.val
  set g := minpoly ℚ αQ with hg
  set a : Kbar p := embP αQ with ha
  have hroot : Polynomial.aeval a (g.map (algebraMap ℚ ℚ_[p])) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, ha]
    have : Polynomial.aeval (embP (p := p) αQ) g = embP (Polynomial.aeval αQ g) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_rat _ _
    rw [this, minpoly.aeval, map_zero]
  have hg0 : g.map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ_[p]).injective).mpr (minpoly.ne_zero hintQ)
  have hint : IsIntegral ℚ_[p] a :=
    ⟨_, (minpoly.monic hintQ).map _, by
      rw [← Polynomial.aeval_def]; exact hroot⟩
  set E : Fld p := IntermediateField.adjoin ℚ_[p] {a} with hE
  haveI : FiniteDimensional ℚ_[p] E := IntermediateField.adjoin.finiteDimensional hint
  refine ⟨E, inferInstance, ?_, ?_⟩
  · intro x hx
    have h1 : (⟨x, hx⟩ : L) ∈ IntermediateField.adjoin ℚ {α} := by rw [hα]; trivial
    have h2 : x ∈ (IntermediateField.adjoin ℚ {α}).map L.val := ⟨⟨x, hx⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have h3 : embP (p := p) x ∈
        (IntermediateField.adjoin ℚ {L.val α}).map (embP (p := p)).toRatAlgHom :=
      ⟨x, h2, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h3
    have hle : IntermediateField.adjoin ℚ {(embP (p := p)).toRatAlgHom (L.val α)} ≤
        E.restrictScalars ℚ := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ_[p] a
    exact hle h3
  · rw [IntermediateField.adjoin.finrank hint]
    have hdvd : minpoly ℚ_[p] a ∣ g.map (algebraMap ℚ ℚ_[p]) := minpoly.dvd ℚ_[p] a hroot
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hg0
    rw [Polynomial.natDegree_map] at h1
    have h2 : g.natDegree = Module.finrank ℚ L := by
      have h3 : (minpoly ℚ α).natDegree ≤ Module.finrank ℚ L := minpoly.natDegree_le _
      have h4 : Module.finrank ℚ L ≤ (minpoly ℚ α).natDegree := by
        have := IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ α)
        rw [hα, IntermediateField.finrank_top'] at this
        omega
      rw [hg, ← IntermediateField.minpoly_eq]
      omega
    omega

/-- **Glue on G3 + Néron–Ogg–Shafarevich + the descent datum on `G_L` (N5 L848-851).** At
`p > D`: on wild inertia elements whose image in `G_ℚ` lies in `G_L`, `a_σ μ_σ ∘ σ` is the
identity (it is the Tate action of `A/L`, which has good reduction at `v ∤ 3`, so inertia acts
trivially, `PkgI2.inertiaTrivial_of_goodReduction`). Only claimed for `p ≠ ℓ`. -/
def TateWildTrivialL {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ σ ∈ wildSet, (∀ x ∈ L, decomp p σ x = x) → a (decomp p σ) • Tm (decomp p σ) = 1

theorem tateWildTrivial_of_L {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (h : TateWildTrivialL (p := p) Tm a L) {E : Fld p}
    (hLE : ∀ x ∈ L, embP x ∈ E) : TateWildTrivial Tm a E :=
  fun σ hσ => h σ hσ.2 (decomp_fix_of_le hLE hσ.1)

/-- **`LocalData p r` at `p > D` for G8's `r` (proved)** from G7's clauses (as in
`localData_of_g7_odd`), `[L:ℚ] ≤ D` (G4's output `G4Out`), and `TateWildTrivialL`. -/
theorem localData_of_g7_large {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hβε : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (hβlc : IsLocallyConstant β)
    {Tmin : Finset ℕ} (hTm : ∀ q ∈ Tmin, q.Prime) [NeZero (GlueDescent.chiLevel Tmin)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ))
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (hp : (ZInQ.heightD : ℝ) < p)
    (hT : TateWildTrivialL (p := p) Tm a L) :
    LocalData p r := by
  have hpD : ZInQ.heightD < p := by exact_mod_cast hp
  have hp2 : p ≠ 2 := by
    have := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
    omega
  obtain ⟨E, hEfd, hLE, hdeg⟩ := exists_local_field_le (p := p) L
  refine localData_of_g7_odd hp2 hG8 hβε hβ0 hβlc hTm χ ι hsq hε
    (fun hle => absurd hp (not_lt.mpr hle)) (fun _ => ⟨E, hEfd, hLE, ?_, ?_⟩)
  · omega
  · exact tateWildTrivial_of_L hT hLE

/-! ### Final form: the glue on `L_v = ℚ_p · embP(L)` and the assembly for every `p` -/

/-- `L_v = ℚ_p · embP(L) ⊆ ℚ̄_p`, the completion of `L ⊆ ℚ̄` at the place of `embP`. -/
def Lv (L : IntermediateField ℚ PkgI4.Qbar) : Fld p :=
  IntermediateField.adjoin ℚ_[p] (embP '' (L : Set PkgI4.Qbar))

theorem embP_mem_Lv {L : IntermediateField ℚ PkgI4.Qbar} {x : PkgI4.Qbar} (hx : x ∈ L) :
    embP x ∈ Lv (p := p) L :=
  IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩

theorem Lv_le {L : IntermediateField ℚ PkgI4.Qbar} {E : Fld p} (h : ∀ x ∈ L, embP x ∈ E) :
    Lv (p := p) L ≤ E :=
  IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

/-- `[L_v:ℚ_p] ≤ [L:ℚ]` (proved, from `exists_local_field_le`). -/
theorem Lv_fin (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ_[p] (Lv (p := p) L) ∧
      Module.finrank ℚ_[p] (Lv (p := p) L) ≤ Module.finrank ℚ L := by
  obtain ⟨E, hEfd, hLE, hdeg⟩ := exists_local_field_le (p := p) L
  have hle := Lv_le (p := p) hLE
  have hfd : FiniteDimensional ℚ_[p] (Lv (p := p) L) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  exact ⟨hfd, (IntermediateField.finrank_le_of_le_right hle).trans hdeg⟩

/-- **The clauses of G4/G7 used here (GLUE: transport between g0-mod-field's `ℂ^×`-valued data
and g0-mod-galois's `ℚ̄_ℓ`-valued `G7Out`).** `L ⊆ ℚ̄` (G4's Hom field) is finite with
`[L:ℚ] ≤ D` (`G4Out`); `∂β = ε` and `β ≠ 0` (`G0Galois.G7Out`); `β` locally constant and
`β² = ι ∘ χ` for a Dirichlet character `χ` mod `chiLevel T₋`, `T₋` a set of primes (`G7Data`, with
`ι : ℂ^× → ℚ̄_ℓ^×` the transport of values); `ε = 1` on `G_L × G_L` (`DescentDatum`: `ε` inflated
from `Gal(L/ℚ)` with `ε(1,1) = 1`). Note: g0-mod-field's interface `G7Data` (and so `AfterG7`)
does not carry `[L:ℚ] ≤ D`; `G4Out` does. -/
def G7Clauses (β : GQ → PadicAlgCl ℓ) (ε : GQ → GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  FiniteDimensional ℚ L ∧ Module.finrank ℚ L ≤ ZInQ.heightD ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧ IsLocallyConstant β ∧
  (∃ (Tmin : Finset ℕ) (_ : ∀ q ∈ Tmin, q.Prime) (_ : NeZero (GlueDescent.chiLevel Tmin))
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ),
    ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ)) ∧
  (∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)

/-- **Glue on G4/G7 + R6 + D2 + the torsion field (N5 L813-818).** There is a finite
`E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` on which `a·Tm` is trivial on wild inertia. Glazer:
`E = L_v(A[3])` (`A[5]` if `p = 3`), `[E:L_v] ≤ |GL₄(𝔽₅)| = G₀ = 116064000000`
(`A[m] ≅ (ℤ/m)⁴`, `PkgI2.TorsionStructure`); `A` is semistable over `E` (R6,
`PkgI2.RaynaudCriterion`), so wild inertia acts trivially on `V_ℓ(A)` (D2,
`PkgI2.D2_fixed_of_raynaud`), and `a_σ μ_σ = 1` on `G_L` (`DescentDatum`). Only for `p ≠ ℓ`. -/
def TorsionFieldWild {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    TateWildTrivial Tm a E

/-- **The local glue at `p`.** `TorsionFieldWild` at `p ≤ D`, `TateWildTrivialL` at `p > D`, and
at `p = 2` the bound for `β` on `L_v` (`BetaUpper`, glue on T16 + D3 + Herbrand's `ψ ≥ id`,
N5 L826-844; `β|_{G_{L_v}}` is a character with `β⁴ = 1` on units since the 2-part of `χ` has
conductor `4`). -/
def LocalGlue {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → TorsionFieldWild (p := p) Tm a L) ∧
  ((ZInQ.heightD : ℝ) < p → TateWildTrivialL (p := p) Tm a L) ∧
  (p = 2 → BetaUpper β (Lv (p := p) L) U0)

/-- **`LocalData p r` for G8's `r`, every prime `p` (proved)** from G8's output, the G4/G7
clauses (`G7Clauses`) and the local glue (`LocalGlue`). -/
theorem localData_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2} {L : IntermediateField ℚ PkgI4.Qbar}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r) (hC : G7Clauses β ε L)
    (hG : LocalGlue (p := p) Tm a β L) : LocalData p r := by
  obtain ⟨hLfd, hLD, hβε, hβ0, hβlc, ⟨Tmin, hTm, hNZ, χ, ι, hsq⟩, hε⟩ := hC
  obtain ⟨hLvfd, hLvdeg⟩ := Lv_fin (p := p) L
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  -- the field of `TorsionFieldWild` has degree `≤ D G₀`
  have hsmall : (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 ∧
      TateWildTrivial Tm a E := by
    intro hp
    obtain ⟨E, hEfd, hLvE, hdeg, hT⟩ := hG.1 hp
    refine ⟨E, hEfd, fun x hx => hLvE (embP_mem_Lv hx), ?_, hT⟩
    calc Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) := hdeg
      _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul_left _ (hLvdeg.trans hLD)
      _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
  by_cases hp2 : p = 2
  · subst hp2
    have hle : ((2 : ℕ) : ℝ) ≤ (ZInQ.heightD : ℝ) := by exact_mod_cast (by omega : 2 ≤ ZInQ.heightD)
    refine ⟨fun hp => ?_, fun hp => absurd hp (not_lt.mpr hle)⟩
    obtain ⟨E, hEfd, hLvE, hdeg, hT⟩ := hG.1 hp
    obtain ⟨E', hE'fd, hLE', hdeg', hT'⟩ := hsmall hp
    exact localData_small_of_g8 hG8 hdeg' hT' (betaUpper_mono (Lv_le hLE') (hG.2.2 rfl))
  · refine localData_of_g7_odd hp2 hG8 hβε hβ0 hβlc hTm χ ι hsq hε hsmall (fun hp => ?_)
    have hpD : ZInQ.heightD < p := by exact_mod_cast hp
    exact ⟨Lv (p := p) L, hLvfd, fun x hx => embP_mem_Lv hx, by omega,
      tateWildTrivial_of_L (hG.2.1 hp) (fun x hx => embP_mem_Lv hx)⟩

/-- **`G15RamG D u` from G8's outputs, the G4/G7 clauses and the local glue (proved).**
The G7/G8 data for `r₅` and `r₃` (models `A₅/K₅`, `A₃/K₃`, Hom fields `L₅`, `L₃`). -/
theorem g15RamG_of_g7 {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A) (u : ℚ)
    {K₅ : Type} [Field K₅] [NumberField K₅] {A₅ : PkgI3.AbVar K₅}
    {Tm₅ : GQ → Module.End (PadicAlgCl 5) (G0Galois.Vb A₅ 5)} {a₅ β₅ : GQ → PadicAlgCl 5}
    {ε₅ : GQ → GQ → PadicAlgCl 5} {L₅ : IntermediateField ℚ PkgI4.Qbar}
    (hG8₅ : G0Galois.G8Out A₅ 5 (GlueDescent.rho Tm₅ a₅ β₅) D.r5) (hC₅ : G7Clauses β₅ ε₅ L₅)
    (hG₅ : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅ L₅)
    {K₃ : Type} [Field K₃] [NumberField K₃] {A₃ : PkgI3.AbVar K₃}
    {Tm₃ : GQ → Module.End (PadicAlgCl 3) (G0Galois.Vb A₃ 3)} {a₃ β₃ : GQ → PadicAlgCl 3}
    {ε₃ : GQ → GQ → PadicAlgCl 3} {L₃ : IntermediateField ℚ PkgI4.Qbar}
    (hG8₃ : G0Galois.G8Out A₃ 3 (GlueDescent.rho Tm₃ a₃ β₃) D.r3) (hC₃ : G7Clauses β₃ ε₃ L₃)
    (hG₃ : LocalGlue (p := 5) Tm₃ a₃ β₃ L₃)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_localData D u
    (fun p hp hp5 => @localData_of_g7 p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ _ _ hG8₅ hC₅ (hG₅ p hp hp5))
    (localData_of_g7 hG8₃ hC₃ hG₃) h11₅ h11₃

/-! ### Non-vacuity (proved) -/

/-- **`G7LocalData` is satisfiable (proved):** it holds for trivial data (`Tm = 1`, `a = 1`,
`β = 1`, `F = ℚ_p`), so it is not contradictory. -/
theorem g7LocalData_triv {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V] :
    G7LocalData (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1)
      (fun _ => 1) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have he : ramCard (⊥ : Fld p) 0 = 1 := by
    have h1 := one_le_ramCard hF 0
    have h2 := ramCard_zero_le_finrank hF
    rw [IntermediateField.finrank_bot] at h2
    omega
  have hT : TateWildTrivial (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V))
      (fun _ => (1 : PadicAlgCl ℓ)) ⊥ := fun _ _ => one_smul _ _
  refine ⟨fun _ => ⟨⊥, hF, ?_, hT, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, hF, ?_, hT, fun _ _ => rfl⟩⟩
  · rw [he]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [he]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

/-- **`G7Clauses` and `LocalGlue` are satisfiable (proved):** both hold for trivial data
(`β = 1`, `ε = 1`, `L = ℚ`, `Tm = 1`, `a = 1`, `χ = 1`, `ι = 1`). -/
theorem g7Clauses_triv : G7Clauses (ℓ := ℓ) (fun _ => 1) (fun _ _ => 1) ⊥ := by
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  refine ⟨inferInstance, ?_, fun _ _ => by simp, fun _ => one_ne_zero,
    IsLocallyConstant.const _, ⟨∅, fun q hq => absurd hq (Finset.notMem_empty q),
      ⟨by simp [GlueDescent.chiLevel]⟩, 1, 1, fun _ => by simp⟩, fun _ _ _ _ => rfl⟩
  rw [IntermediateField.finrank_bot]
  omega

theorem localGlue_triv {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    LocalGlue (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1) (fun _ => 1) L := by
  obtain ⟨hfd, -⟩ := Lv_fin (p := p) L
  have hG0 : 1 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
  refine ⟨fun _ => ⟨Lv (p := p) L, hfd, le_rfl, ?_, fun _ _ => one_smul _ _⟩,
    fun _ _ _ _ => one_smul _ _, fun _ _ _ _ _ => rfl⟩
  exact Nat.le_mul_of_pos_left _ hG0

end LocalDataSec

end G15Ram



/-! ## §5' (local-glue). Verbatim copy from scratch/g0-mod-galois/part_galois.lean lines 40-58 -/

noncomputable section

namespace G0Galois


end G0Galois

end

/-! ## §6 (local-glue). `LocalGlue p Tm a β L` on G7's data

`LocalGlue p Tm a β L` (§4 above, copied verbatim from scratch/local-data) is a predicate on
arbitrary operators `Tm`, scalars `a`, `β` and a field `L`. Here:

* `not_localGlue_zero` (proved): it fails for `Tm = 0` at every `p > D`, so it is not a closed
  theorem; it is a claim about the data that G7 builds.
* **Main result** `localGlue_of_g7` (proved): for G7's data (`G0Galois.G7Out`, with the clauses
  `G7Clauses`), `LocalGlue p Tm a β L` follows from three named Props about the abelian surface
  `A/K` and the kernel field, with no `Tm` or `a` left:
  - `KerWild K β L`: wild inertia elements of `G_L` killed by `β` lie in `G_K` (G7Data's kernel
    field clause `G_{L'} = G_L ∩ ker β`, transported);
  - `TateWildK p A ℓ` (`p ≥ 7`): wild inertia at `p` in `G_K` acts trivially on `V_ℓ(A)`;
  - `TateWildKE p A ℓ β L` (`p ≤ 5`): the same on `G_E` for a field `E ⊇ L_v` of degree
    `≤ G₀[L_v:ℚ_p]`, on which also `β` kills wild inertia;
  and `BetaUpper` at `p = 2` (unchanged).
* `tate_eq_one_of_torsFix` (proved): `σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` if it fixes every
  `ℓⁿ`-torsion point; so `TateWildK`, `TateWildKE` reduce to statements on torsion points
  (`TorsFixWild`, `TorsFixWildE`), the form in which Raynaud's criterion (R6) and D2 are stated.
-/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GaloisRep GQ decomp)
open LadicCond G0ModNewform
open CategoryTheory MonObj

section LocalGlueSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### `LocalGlue` is not a closed statement -/

/-- **`LocalGlue` fails for `Tm = 0` at every `p > D` (proved).** `σ = 1` is wild and fixes
`L`, and `1 • 0 ≠ 1` on the nonzero space `ℚ̄_ℓ`. -/
theorem not_localGlue_zero (hp : (ZInQ.heightD : ℝ) < p) (L : IntermediateField ℚ PkgI4.Qbar) :
    ¬ LocalGlue (p := p) (fun _ => (0 : Module.End (PadicAlgCl ℓ) (PadicAlgCl ℓ))) (fun _ => 1)
      (fun _ => 1) L := by
  intro h
  have h1 := h.2.1 hp 1 one_mem_wildSet (fun x _ => by rw [map_one]; rfl)
  have h2 := LinearMap.congr_fun h1 1
  simp at h2

/-! ### Fixing `L` and fixing `L_v` -/

/-- If `decomp σ` fixes `L`, then `σ` fixes `L_v = ℚ_p · embP(L)` (proved). -/
theorem fixSet_Lv_of_fix {L : IntermediateField ℚ PkgI4.Qbar} {σ : GQp p}
    (h : ∀ x ∈ L, decomp p σ x = x) : σ ∈ fixSet (Lv (p := p) L) := by
  have hle : Lv (p := p) L ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    apply Lv_le
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hσ : σ ∈ MulAction.stabilizer (GQp p) (embP (p := p) x) := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, ← decomp_spec, h x hx]
    have := (Subgroup.zpowers_le.mpr hσ) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  intro y hy
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hy) σ (Subgroup.mem_zpowers σ)

/-- `σ` fixes `L_v` iff `decomp σ` fixes `L` (proved). -/
theorem fixSet_Lv_iff {L : IntermediateField ℚ PkgI4.Qbar} {σ : GQp p} :
    σ ∈ fixSet (Lv (p := p) L) ↔ ∀ x ∈ L, decomp p σ x = x :=
  ⟨fun h => decomp_fix_of_le (fun _ hx => embP_mem_Lv hx) h, fixSet_Lv_of_fix⟩

/-! ### `β` on wild inertia of `G_L` at odd `p` -/

/-- **`β` kills wild inertia of `G_L` at odd `p` (proved)** from G7's clauses: on `G_{L_v}`,
`β` is a character (`∂β = ε`, `ε = 1` on `G_L²`) with `β² = χ` tame (`χ` mod `chiLevel T₋`) and
open kernel (local constancy), so `betaTame_of_odd` applies with `F = L_v`. -/
theorem beta_wild_of_clauses (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L) {σ : GQp p} (hσ : σ ∈ wildSet)
    (hfix : ∀ x ∈ L, decomp p σ x = x) : β (decomp p σ) = 1 := by
  obtain ⟨-, -, hβε, hβ0, hβlc, ⟨Tmin, hTm, hNZ, χ, ιc, hsq⟩, hε⟩ := hC
  have hm : BetaCharOn β (Lv (p := p) L) :=
    betaCharOn_of_cocycle hβε hε (fun _ hx => embP_mem_Lv hx)
  have hs : BetaSqWild β (Lv (p := p) L) :=
    betaSqWild_of_chi hp2 hTm χ ιc (fun _ _ => hsq _)
  have hopen := betaOpen_of_isLocallyConstant (p := p) hβlc (beta_one_of_charOn hm (hβ0 1))
  exact betaTame_of_odd hp2 hm hs hopen σ ⟨fixSet_Lv_of_fix hfix, hσ⟩

/-! ### The smaller named Props -/

/-- **Glue: G7Data's kernel field clause, transported (N5 L702-716; g0-mod-field `G7Data`,
clause `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`).** Every `g ∈ G_L` with `β(g) = 1` lies in `G_K`
(the image of `resQ K`), for the model field `K = L'` of `G0Galois.G7Out`. Notes: (i) `resQ K`
is taken along the embedding `K ↪ ℚ̄` that Mathlib's `Field.absoluteGaloisGroup.map` chooses;
`L'` is Galois over `ℚ`, so `G_{L'}` is normal and does not depend on that embedding; (ii) the
`ℚ̄_ℓ`-valued `β` here is `ι ∘ β_ℂ` (F5 of local-data), so `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` needs `ι`
injective on the roots of unity, which a transport `ℂ^× → ℚ̄_ℓ^×` can be chosen to be. -/
def KerWild (K : Type) [Field K] [NumberField K] (β : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ g : GQ, (∀ x ∈ L, g x = x) → β g = 1 → g ∈ (G0Galois.resQ K).range

/-- **Glue on R6 (`PkgI2.RaynaudCriterion`), D2 (`PkgI2.D2_fixed_of_raynaud`) and I2-Tors
(`PkgI2.TorsionStructure`) at `p ≥ 7`, `p ≠ ℓ` (N5 L813-818).** Wild inertia at `p` (at the place
of `embP`) inside `G_K` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)`. Proof plan: `m = 3` (`m = 4` if
`p = 13`); `|GL₄(ℤ/m)|` is prime to `p`, so a wild `σ' ∈ G_K` (whose action on the finite group
`A[m] ≅ (ℤ/m)⁴` has `p`-power order) fixes `A[m]`; over `K(A[m])` Raynaud gives `(σ'-1)² = 0` on
`A[ℓⁿ]`, and D2 gives `σ'` fixes `A[ℓⁿ]`; `tate_eq_one_of_torsFix`. Only true for `p ≠ ℓ`.
(Equivalently: for `p > 2g + 1` inertia acts tamely on `V_ℓ`, Grothendieck, SGA 7 I, Exp. IX;
locator UNVERIFIED.) -/
def TateWildK {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K,
    G0Galois.resQ K σ' = decomp p σ → G0Galois.tate A ℓ σ' = 1

/-- **Glue at `p ∈ {2, 3, 5}`, `p ≠ ℓ` (N5 L813-818, L826-833), on R6, D2, I2-Tors and the
descent of `A` to `L`.** There is a finite `E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` such that
every wild `σ` fixing `E` has `β(σ) = 1` and acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` through `G_K`.
Glazer: `A = (A_L)_{L'}` with `A_L` over `L`; `E = L_v'(A_L[3])` (`A_L[5]` if `p = 3`), where at
`p = 2` `L_v'/L_v` (degree `≤ 4`) kills `β` on wild inertia (`β|G_{L_v}` has order `≤ 4` on
inertia since the `2`-part of `χ` has conductor `4`; an unramified twist removes the rest; at odd
`p`, `L_v' = L_v` by `beta_wild_of_clauses`); `[E:L_v] ≤ 4·|GL₄(𝔽₃)| ≤ G₀`, resp.
`|GL₄(𝔽₅)| = G₀`. Raynaud and D2 on `A_L/E`. Not provable from `A/K` alone at these primes:
`|GL₄(ℤ/m)|` is divisible by `2`, `3` and `5` for every `m ≥ 3`. -/
def TateWildKE {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, β (decomp p σ) = 1 ∧
      ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
        G0Galois.tate A ℓ σ' = 1

/-! ### The reduction -/

/-- On a wild `σ` with `decomp σ ∈ G_L`, `β(decomp σ) = 1`, `a·Tm` is the Tate action through
`G_K` (proved, from `G7Out` and `KerWild`). -/
theorem aTm_eq_one_of_kerWild {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hK : KerWild K β L) {g : GQ} (hfix : ∀ x ∈ L, g x = x) (hβ : β g = 1)
    (htate : ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = g →
      G0Galois.tate A ℓ σ' = 1) :
    a g • Tm g = 1 := by
  obtain ⟨σ', rfl⟩ := hK g hfix hβ
  obtain ⟨hT, ha, -⟩ := h7.2.2.2.2.2.2.1 σ'
  rw [hT, ha, one_smul, htate σ' rfl]

/-- **`LocalGlue` on G7's data (proved).** For `Tm, a, β` as in `G0Galois.G7Out` with the
clauses `G7Clauses`, `LocalGlue p Tm a β L` follows from `KerWild` (all `p`), `TateWildK` at
`p ≥ 7`, `TateWildKE` at `p ≤ 5`, and `BetaUpper` at `p = 2`. At `p ≥ 7`, `p ≤ D`, the field of
`TorsionFieldWild` is `L_v` itself. -/
theorem localGlue_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaUpper β (Lv (p := p) L) U0) :
    LocalGlue (p := p) Tm a β L := by
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hpp : p.Prime := Fact.out
  have h7le : ¬ p ≤ 5 → 7 ≤ p := by
    intro h
    by_contra h'
    have : p = 6 := by omega
    exact absurd (this ▸ hpp) (by norm_num)
  -- at `p ≥ 7`: wild `σ` with `decomp σ ∈ G_L` has `a·Tm = 1`
  have hbig : 7 ≤ p → ∀ σ ∈ wildSet (p := p), (∀ x ∈ L, decomp p σ x = x) →
      a (decomp p σ) • Tm (decomp p σ) = 1 := by
    intro h7p σ hσ hfix
    have hp2 : p ≠ 2 := by omega
    exact aTm_eq_one_of_kerWild h7 hK hfix (beta_wild_of_clauses hp2 hC hσ hfix)
      (hW h7p σ hσ)
  refine ⟨fun hpD => ?_, fun hpD => ?_, hB⟩
  · by_cases h5 : p ≤ 5
    · obtain ⟨E, hEfd, hLvE, hdeg, hEw⟩ := hE h5
      refine ⟨E, hEfd, hLvE, hdeg, fun σ hσ => ?_⟩
      have hfix := decomp_fix_of_le (fun _ hx => hLvE (embP_mem_Lv hx)) hσ.1
      exact aTm_eq_one_of_kerWild h7 hK hfix (hEw σ hσ).1 (hEw σ hσ).2
    · have : FiniteDimensional ℚ L := hC.1
      obtain ⟨hfd, -⟩ := Lv_fin (p := p) L
      have hG0 : 1 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
      refine ⟨Lv (p := p) L, hfd, le_rfl, Nat.le_mul_of_pos_left _ hG0, fun σ hσ => ?_⟩
      exact hbig (h7le h5) σ hσ.2 (fixSet_Lv_iff.mp hσ.1)
  · have hpD' : ZInQ.heightD < p := by exact_mod_cast hpD
    exact fun σ hσ hfix => hbig (by omega) σ hσ hfix

/-! ### From torsion points to `V_ℓ` -/

/-- **`σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` if it fixes every `ℓⁿ`-torsion point (proved).**
`T_ℓ(A)` is the group of compatible sequences `(xₙ)` with `xₙ ∈ A(K̄)[ℓⁿ]`
(`PkgI3.Tate.pow_smul_eq_zero`), and `σ` acts termwise. -/
theorem tate_eq_one_of_torsFix {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K)
    (h : ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ P = P) :
    G0Galois.tate A ℓ σ = 1 := by
  have hT : A.galT (ℓ := ℓ) σ = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    have hx : (ℓ ^ n) • x.1 n = 0 := PkgI3.Tate.pow_smul_eq_zero x.2 n
    have hP : (Additive.toMul (x.1 n)) ^ (ℓ ^ n) = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    change Additive.ofMul (A.galAct σ (Additive.toMul (x.1 n))) = x.1 n
    rw [h n _ hP]; rfl
  have hR : A.galRep ℓ σ = LinearMap.id := by
    change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] = LinearMap.id
    rw [hT, LinearMap.baseChange_id]
  change (A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) = LinearMap.id
  rw [hR, LinearMap.baseChange_id]

/-- **Glue on R6 + D2 + I2-Tors, on torsion points (`p ≥ 7`, `p ≠ ℓ`; N5 L813-818).** Wild
inertia at `p` inside `G_K` fixes every `ℓⁿ`-torsion point of `A(K̄)`. This is the form of
`PkgI2.D2_fixed_of_raynaud`; what remains is the bridge from the number field `K` with the place
of `embP` (`resQ`, `decomp`, `wildSet`) to the valuation-ring setting of PkgI2 (a DVR `O ⊆ K(A[m])`
and a valuation ring `w` of `K̄` over it), the base change of `A` to `K(A[m])`, and the
`p`-power order of a wild `σ'` on the finite set `A[m]` (see `TateWildK`). -/
def TorsFixWild {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K,
    G0Galois.resQ K σ' = decomp p σ →
      ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

theorem tateWildK_of_torsFixWild {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (h : TorsFixWild (p := p) A ℓ) : TateWildK (p := p) A ℓ :=
  fun σ hσ σ' hσ' => tate_eq_one_of_torsFix A ℓ σ' (h σ hσ σ' hσ')

/-- **Glue at `p ∈ {2, 3, 5}` on torsion points** (as `TateWildKE`, with "acts trivially on
`V_ℓ`" replaced by "fixes every `ℓⁿ`-torsion point"). -/
def TorsFixWildE {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, β (decomp p σ) = 1 ∧
      ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
        ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

theorem tateWildKE_of_torsFixWildE {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {β : GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (h : TorsFixWildE (p := p) A ℓ β L) : TateWildKE (p := p) A ℓ β L := by
  obtain ⟨E, hEfd, hLvE, hdeg, hw⟩ := h
  exact ⟨E, hEfd, hLvE, hdeg, fun σ hσ =>
    ⟨(hw σ hσ).1, fun σ' hσ' => tate_eq_one_of_torsFix A ℓ σ' ((hw σ hσ).2 σ' hσ')⟩⟩

/-- **Glue at `p ∈ {3, 5}`, `p ≠ ℓ` (as `TorsFixWildE` without the `β` clause, which is
automatic at odd `p`: `torsFixWildE_of_odd`).** Some finite `E ⊇ L_v` with
`[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` has every wild `σ ∈ G_E` fixing `A(K̄)[ℓⁿ]` through `G_K`. Glazer:
`E = L_v(A_L[5])` (`p = 3`), `L_v(A_L[3])` (`p = 5`), for the model `A_L` over `L`; R6 and D2. -/
def TorsFixWildOdd {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
      G0Galois.resQ K σ' = decomp p σ →
        ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

/-- At odd `p`, `TorsFixWildOdd` and G7's clauses give `TorsFixWildE` (proved). -/
theorem torsFixWildE_of_odd (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L)
    (h : TorsFixWildOdd (p := p) A ℓ L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨E, hEfd, hLvE, hdeg, hw⟩ := h
  exact ⟨E, hEfd, hLvE, hdeg, fun σ hσ => ⟨beta_wild_of_clauses hp2 hC hσ.2
    (decomp_fix_of_le (fun _ hx => hLvE (embP_mem_Lv hx)) hσ.1), hw σ hσ⟩⟩

/-! ### `BetaUpper` at `p = 2` without T16 (proved from a degree-`4` twist field) -/

/-- **Glue at `p = 2` (N5 L826-844; replaces T16 + D3 + Herbrand).** Some finite `M ⊇ L_v` with
`[M:L_v] ≤ 4` has `β = 1` on wild inertia of `G_M`. Proof plan: on `G_{L_v}`, `β` is a character
(`betaCharOn_of_cocycle`) and `β⁴ = χ²` is unramified at `2` (the `2`-part of `χ` is the
character mod `4`, of order `2`; the odd parts are unramified at `2`); an unramified `η` with
`η⁴ = β⁴` exists (`G_{L_v}/I` is procyclic and `β⁴` has finite order), and `M` is the kernel
field of `β η⁻¹`, of order dividing `4`. On wild inertia `η = 1`. -/
def BetaTwist2 (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ M : Fld p, FiniteDimensional ℚ_[p] M ∧ Lv (p := p) L ≤ M ∧
    Module.finrank ℚ_[p] M ≤ 4 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet M ∩ wildSet, β (decomp p σ) = 1

/-- **`BetaUpper` from `BetaTwist2` and G7's clauses (proved), with no class field theory.**
`[M:ℚ_p] ≤ 4D ≤ DG₀`; its Galois closure `F` has `e(F) ≤ (DG₀)!` (`exists_finGal_ramCard_le`), so
`G_{ℚ_p}^t ⊆ G_F ⊆ G_M` for `t > U₀ = 4(DG₀)²` (`UpperBreakFix`, proved from T20 + T21 and
`ladicDVRModelZp`), and `G_{ℚ_p}^t` is wild (`upperWild`). -/
theorem betaUpper_of_twist {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L)
    (h : BetaTwist2 (p := p) β L) : BetaUpper β (Lv (p := p) L) U0 := by
  haveI : FiniteDimensional ℚ L := hC.1
  obtain ⟨M, hMfd, hLvM, hdeg, hM⟩ := h
  obtain ⟨-, hLv⟩ := Lv_fin (p := p) L
  have hG0 : 4 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
  have hMn : Module.finrank ℚ_[p] M ≤ ZInQ.heightD * ZInQ.heightG0 := by
    calc Module.finrank ℚ_[p] M ≤ 4 * Module.finrank ℚ_[p] (Lv (p := p) L) := hdeg
      _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul hG0 (hLv.trans hC.2.1)
      _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
  obtain ⟨F, hF, hMF, he⟩ := exists_finGal_ramCard_le hMn
  have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
    Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
  have hUB : UpperBreakFix p :=
    upperBreakFix_of_hilbertSerre (hilbertSerre_of_model (ladicDVRModel_of_Zp ladicDVRModelZp))
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  intro t ht σ hσ
  have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ.1
  have hwild : σ ∈ wildSet := upperWild (p := p) t (by linarith) hσ.1
  exact hM σ ⟨fun x hx => hfix x (hMF hx), hwild⟩

/-- **`LocalGlue` on G7's data with `BetaTwist2` at `p = 2` (proved)**: as `localGlue_of_g7`,
with `BetaUpper` replaced by the smaller `BetaTwist2` (`betaUpper_of_twist`). -/
theorem localGlue_of_g7_twist {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_g7 h7 hC hK hW hE (fun h => betaUpper_of_twist hC (hB h))

end LocalGlueSec

end G15Ram


/-! ## §7 (local-glue). `TorsFixWild` at `p ≥ 7` from Raynaud's criterion and I2-Tors

`torsFixWild_of_raynaud` (proved): `TorsFixWild` at `p ≥ 7`, `p ≠ ℓ`, follows from
* `WildIter`: a wild `σ'` has `p`-power period on each point of `A(K̄)` (proved in §7b, `wildIter`);
* `TorsGL A m` for `m = 3, 7`: `A(K̄)[m] ≅ (ℤ/m)⁴` as groups (the instance of the leaf I2-Tors,
  `torsGL_of_leaf`);
* `RaynaudPlace A m` for `m = 3` (`p ≠ 13`), `m = 7` (`p = 13`): a wild `σ'` fixing `A(K̄)[m]`
  satisfies `(σ' - 1)² = 0` on
  `A(K̄)[ℓⁿ]` (the instance of the leaf R6 at the place of `embP`; bridge glue).
The algebra in between is proved: `|GL₄(𝔽₃)| = 2⁹·3⁶·5·13` and `13 ∤ |GL₄(𝔽₇)|`, so the action of
a wild `σ'` on `A[m]` has order prime to `p` and `p`-power, hence is trivial
(`iterate_card_GL_fix`); then `(σ'-1)² = 0` and a `p`-power period force `σ' = 1` on
`A[ℓⁿ]` (`fixed_of_unipSq_of_iterate'`, the core of D2). -/

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj

section TorsSec

/-- **An additive structure of `S ≅ (ℤ/q)ⁿ` bounds the period (proved).** If `φ : G →* G` is
injective, maps the multiplicatively closed `S` into itself, and `S ≅ (ℤ/q)ⁿ` as groups, then
`φ^[N] = id` on `S`, `N = |GLₙ(𝔽_q)|`. -/
theorem iterate_card_GL_fix {G : Type*} [Group G] (φ : G →* G) (hinj : Function.Injective φ)
    (S : Set G) (hS : ∀ x ∈ S, φ x ∈ S) (hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (q : ℕ) [Fact q.Prime] (n : ℕ) (e : S ≃ (Fin n → ZMod q))
    (he : ∀ (x y : S) (h : x.1 * y.1 ∈ S), e ⟨x.1 * y.1, h⟩ = e x + e y) :
    ∀ x ∈ S, φ^[Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q))] x = x := by
  set φS : S → S := fun x => ⟨φ x, hS x x.2⟩ with hφS
  set f : (Fin n → ZMod q) → (Fin n → ZMod q) := fun v => e (φS (e.symm v)) with hf
  have hadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    set x := e.symm a
    set y := e.symm b
    have hxy : e.symm (a + b) = ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he x y, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hφxy : φS ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ =
        ⟨(φS x).1 * (φS y).1, hSmul _ (φS x).2 _ (φS y).2⟩ := by
      apply Subtype.ext
      simp [hφS, map_mul]
    simp only [hf]
    rw [hxy, hφxy, he]
  have hfinj : Function.Injective f := by
    intro a b h
    have h1 := e.injective h
    have h2 : φ (e.symm a).1 = φ (e.symm b).1 := congrArg Subtype.val h1
    exact e.symm.injective (Subtype.ext (hinj h2))
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  let fA : (Fin n → ZMod q) →+ (Fin n → ZMod q) := AddMonoidHom.mk' f hadd
  let fL := fA.toZModLinearMap q
  let fLE := LinearEquiv.ofBijective fL hfbij
  let u : LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q) :=
    ⟨fLE.toLinearMap, fLE.symm.toLinearMap, by ext v; simp, by ext v; simp⟩
  set N := Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q)) with hN
  have hcard : Nat.card (LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q)) = N :=
    (Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv).symm
  have huN : u ^ N = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hfN : ∀ v, f^[N] v = v := by
    intro v
    have h1 : ((u ^ N : LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q)) :
        Module.End (ZMod q) (Fin n → ZMod q)) v = v := by rw [huN]; rfl
    rw [Units.val_pow_eq_pow_val, Module.End.pow_apply] at h1
    exact h1
  have hsemi : Function.Semiconj e φS f := by
    intro x
    simp [hf]
  have hval : Function.Semiconj (Subtype.val : S → G) φS φ := fun x => rfl
  intro x hx
  have h1 : e (φS^[N] ⟨x, hx⟩) = e ⟨x, hx⟩ := by
    rw [(hsemi.iterate_right N) ⟨x, hx⟩]
    exact hfN _
  have h2 := congrArg Subtype.val (e.injective h1)
  rw [(hval.iterate_right N) ⟨x, hx⟩] at h2
  exact h2

/-- `|GL₄(𝔽₃)| = 80·78·72·54 = 24261120 = 2⁹·3⁶·5·13` (proved). -/
theorem card_GL4_three : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 3)) = 24261120 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

/-- `|GL₄(𝔽₇)| = 2400·2394·2352·2058` (proved). -/
theorem card_GL4_seven :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 7)) = 2400 * 2394 * 2352 * 2058 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

theorem coprime_card_GL4_three {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h13 : p ≠ 13) :
    Nat.Coprime p 24261120 := by
  rw [hp.coprime_iff_not_dvd]
  intro h
  have hfac : (24261120 : ℕ) = 2 ^ 9 * 3 ^ 6 * 5 * 13 := by norm_num
  rw [hfac] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h; omega

theorem coprime_card_GL4_seven : Nat.Coprime 13 (2400 * 2394 * 2352 * 2058) := by norm_num

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]

/-- **D2's algebraic core on PkgI3 points (proved; as `PkgI2.fixed_of_unipSq_of_iterate`).** If
`(σ - 1)² x = 0`, `x ∈ A(K̄)[ℓⁿ]`, and `σ^{qᵃ} x = x` with `qᵃ` prime to `ℓⁿ`, then `σ x = x`. -/
theorem fixed_of_unipSq_of_iterate' (A : PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (x : A.Pt (AlgebraicClosure K)) (ℓ n q a : ℕ) (hcop : Nat.Coprime (q ^ a) (ℓ ^ n))
    (hx : x ^ (ℓ ^ n) = 1)
    (hu : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ * (A.galAct σ x)⁻¹ * x = 1)
    (hit : (A.galAct σ)^[q ^ a] x = x) : A.galAct σ x = x := by
  set N := A.galAct σ x * x⁻¹ with hN
  have hσN : A.galAct σ N = N := by
    rw [hN, map_mul, map_inv]
    have h2 : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ =
        ((A.galAct σ x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, (A.galAct σ)^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (q ^ a) = 1 := by
    have := hiter (q ^ a)
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    rw [hN, mul_pow, ← map_pow, hx, map_one, inv_pow, hx]; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **Glue (bridge): wild elements have `p`-power period on points.** For wild `σ` and
`σ' ∈ G_K` over `decomp σ`, every `P ∈ A(K̄)` has `σ'^{pᵃ} P = P` for some `a`. Proof plan: `P` is
defined over a finite `F ⊆ K̄` (a `K̄`-point of a scheme of finite type over `K`); `qEmb K` is an
isomorphism `ℚ̄ ≅ K̄` (both are algebraic closures of `ℚ`), and `embP` sends `qEmb⁻¹(F)` into a
finite extension of `ℚ_p`, whose Galois closure is fixed by some `σ^{pᵃ}`
(`exists_pow_fix_of_wild`, local-data). -/
def WildIter (A : PkgI3.AbVar K) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    ∀ P : A.Pt (AlgebraicClosure K), ∃ a : ℕ, (A.galAct σ')^[p ^ a] P = P

/-- **The instance of the leaf I2-Tors on `A` (`A(K̄)[m] ≅ (ℤ/m)⁴` as groups).** Proved from
`ObjBridge.TorsionStructure` for `dim A = 2` in `torsGL_of_leaf`. -/
def TorsGL (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∃ e : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} ≃ (Fin 4 → ZMod m),
    ∀ (x y : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1})
      (h : x.1 * y.1 ∈ {P : A.Pt (AlgebraicClosure K) | P ^ m = 1}),
      e ⟨x.1 * y.1, h⟩ = e x + e y

/-- **Glue on the leaf R6 (`PkgI2.RaynaudCriterion`) at the place of `embP` (N5 L813-818).**
A wild `σ' ∈ G_K` (over `decomp σ`, `σ ∈ wildSet`) that fixes `A(K̄)[m]` satisfies
`(σ' - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ ≠ p`. Proof plan: R6 on `K' = K(A[m])`
(over which `A[m]` is rational, `m ≥ 3` prime to `p`) with the valuation ring of `K'` at the
place of `embP` (a DVR) and a valuation ring `w` of `K̄` over it; `σ'` fixes `K'`, and a wild
element is in the inertia group of `w`. What is missing is that bridge (PkgI2's setting is a
field with a DVR and `AlgebraicClosure`; here `G_K`, `resQ`, `decomp`) and the base change of
`A` to `K'`. Claimed only for `m ≥ 3` prime to `p` (used with `m = 3` for `p ≠ 13` and `m = 7`
for `p = 13`; for `m = p` Raynaud's criterion does not apply and the statement can fail). -/
def RaynaudPlace (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ (n : ℕ) (x : A.Pt (AlgebraicClosure K)), x ^ (ℓ ^ n) = 1 →
      A.galAct σ' (A.galAct σ' x) * (A.galAct σ' x)⁻¹ * (A.galAct σ' x)⁻¹ * x = 1

/-- **`TorsGL` from the leaf I2-Tors (proved)**, for `dim A = 2` (a clause of `G7Out`). -/
theorem torsGL_of_leaf (hT : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2)
    (m : ℕ) (hm : 0 < m) : TorsGL A m := by
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  obtain ⟨e, he⟩ := hT K (ObjBridge.toGrp A) 2 m (by exact_mod_cast hdim) hm hmK
  exact ⟨e, he⟩

/-- `σ⁻¹ (σ P) = P` on points (proved). -/
theorem galAct_inv_galAct (A : PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (P : A.Pt (AlgebraicClosure K)) :
    A.galAct σ⁻¹ (A.galAct σ P) = P := by
  change PkgI3.AbVar.galHom σ⁻¹ ≫ PkgI3.AbVar.galHom σ ≫ P = P
  rw [← Category.assoc, ← PkgI3.AbVar.galHom_mul, inv_mul_cancel, PkgI3.AbVar.galHom_one,
    Category.id_comp]

theorem galAct_injective (A : PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Function.Injective (A.galAct (L := AlgebraicClosure K) σ) := by
  intro x y h
  have h1 := congrArg (A.galAct σ⁻¹) h
  rwa [galAct_inv_galAct, galAct_inv_galAct] at h1

/-- A wild `σ'` fixes `A(K̄)[m]` when `p ∤ |GL₄(ℤ/m)|` (proved from `WildIter` and `TorsGL`). -/
theorem fix_torsion_of_coprime {A : PkgI3.AbVar K} (hI : WildIter (p := p) A) (m : ℕ)
    [Fact m.Prime] (hT : TorsGL A m)
    (hcop : Nat.Coprime p (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod m))))
    {σ : GQp p} (hσ : σ ∈ wildSet) {σ' : Field.absoluteGaloisGroup K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) :
    ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P := by
  obtain ⟨e, he⟩ := hT
  intro P hP
  have hfix := iterate_card_GL_fix (A.galAct σ') (galAct_injective A σ')
    {P : A.Pt (AlgebraicClosure K) | P ^ m = 1}
    (fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [← map_pow, hx, map_one])
    (fun x hx y hy => by
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [mul_pow, hx, hy, _root_.one_mul]) m 4 e he P hP
  obtain ⟨a, ha⟩ := hI σ hσ σ' hσ' P
  have h1 : Function.IsPeriodicPt (A.galAct σ') (p ^ a) P := ha
  have h2 : Function.IsPeriodicPt (A.galAct σ')
      (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod m))) P := hfix
  have h3 := h1.gcd h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left a hcop)] at h3
  exact h3

/-! ### `WildIter` from `PtFinite` (proved) -/

/-- `σ (τ P) = (στ) P` on points (proved). -/
theorem galAct_galAct (A : PkgI3.AbVar K) (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) : A.galAct σ (A.galAct τ P) = A.galAct (σ * τ) P := by
  change PkgI3.AbVar.galHom σ ≫ PkgI3.AbVar.galHom τ ≫ P = PkgI3.AbVar.galHom (σ * τ) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

theorem galAct_iterate (A : PkgI3.AbVar K) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) (k : ℕ) : (A.galAct σ)^[k] P = A.galAct (σ ^ k) P := by
  induction k with
  | zero =>
    change P = PkgI3.AbVar.galHom 1 ≫ P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  | succ k ih => rw [Function.iterate_succ_apply', ih, galAct_galAct, ← pow_succ']

/-- `qEmb K : ℚ̄ → K̄` is onto (proved): `K̄` is integral over `ℚ` (`K` is a number field), hence
over the algebraically closed `ℚ̄`. -/
theorem qEmbRing_surjective (K : Type) [Field K] [NumberField K] :
    Function.Surjective (G0Galois.qEmbRing K) := by
  have hint : Algebra.IsIntegral ℚ (AlgebraicClosure K) := Algebra.IsIntegral.trans K
  have h : ((G0Galois.qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ))).IsIntegral := by
    rw [Subsingleton.elim ((G0Galois.qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ)))
      (algebraMap ℚ (AlgebraicClosure K))]
    exact hint.isIntegral
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral _ (RingHom.IsIntegral.tower_top _ _ h)).2

theorem pow_fix_mono {G X : Type*} [Group G] [MulAction G X] {g : G} {x : X} {q b a : ℕ}
    (h : g ^ (q ^ b) • x = x) (hba : b ≤ a) : g ^ (q ^ a) • x = x := by
  have hmem : g ^ (q ^ b) ∈ MulAction.stabilizer G x := h
  have : g ^ (q ^ a) = (g ^ (q ^ b)) ^ (q ^ (a - b)) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hba]
  rw [this]
  exact (MulAction.stabilizer G x).pow_mem hmem _

/-- **A wild `σ'` has `p`-power period on each element of `K̄` (proved).** `x = qEmb y`;
`σ^{pᵃ}` fixes the normal closure of `ℚ_p(embP y)` (`exists_pow_fix_of_wild`), so
`decomp(σ^{pᵃ})` fixes `y` (`decomp_spec`), and `σ'^{pᵃ} x = qEmb(decomp(σ^{pᵃ}) y) = x`
(`resQ_spec`). -/
theorem wild_pow_fix_elem {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (x : AlgebraicClosure K) :
    ∃ a : ℕ, (σ' ^ (p ^ a)) x = x := by
  obtain ⟨y, rfl⟩ := qEmbRing_surjective K x
  set E : Fld p := IntermediateField.adjoin ℚ_[p] {embP (p := p) y}
  haveI : FiniteDimensional ℚ_[p] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  set F' := IntermediateField.normalClosure ℚ_[p] E (Kbar p)
  haveI : FiniteDimensional ℚ_[p] F' := normalClosure.is_finiteDimensional ℚ_[p] E (Kbar p)
  haveI : Normal ℚ_[p] F' := normalClosure.normal ℚ_[p] E (Kbar p)
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ (F' := F') ⟨inferInstance, IsGalois.mk⟩
  refine ⟨a, ?_⟩
  have hyE : embP (p := p) y ∈ F' :=
    E.le_normalClosure (IntermediateField.mem_adjoin_simple_self ℚ_[p] _)
  have hdec : decomp p (σ ^ (p ^ a)) y = y := by
    apply (embP (p := p)).injective
    rw [decomp_spec]
    exact ha _ hyE
  have h1 : G0Galois.qEmbRing K (G0Galois.resQ K (σ' ^ (p ^ a)) y) =
      (σ' ^ (p ^ a)) (G0Galois.qEmbRing K y) := G0Galois.resQ_spec K _ y
  have hpow : G0Galois.resQ K (σ' ^ (p ^ a)) = (G0Galois.resQ K σ') ^ (p ^ a) := map_pow _ _ _
  rw [hpow, hσ', ← map_pow, hdec] at h1
  exact h1.symm

/-- **A wild `σ'` has `p`-power period on each finite `F ⊆ K̄` over `K` (proved)**, from
`wild_pow_fix_elem` on a basis. -/
theorem wild_pow_fix_field {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K F] : ∃ a : ℕ, ∀ x ∈ F, (σ' ^ (p ^ a)) x = x := by
  set b := Module.finBasis K F
  choose c hc using fun i => wild_pow_fix_elem hσ hσ' ((b i : F) : AlgebraicClosure K)
  refine ⟨∑ i, c i, fun x hx => ?_⟩
  have hb : ∀ i, (σ' ^ (p ^ (∑ i, c i))) ((b i : F) : AlgebraicClosure K) = b i := fun i =>
    pow_fix_mono (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hc i)
      (Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i))
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : F) : AlgebraicClosure K) := by
    have h := congrArg (fun z : F => (z : AlgebraicClosure K)) (b.sum_repr ⟨x, hx⟩).symm
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    exact h
  rw [hx', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hb i, ← Algebra.smul_def]

/-- **Glue (Mathlib-level): `K̄`-points are defined over finite extensions.** Every
`P ∈ A(K̄)` is fixed by `G_F` for a finite `F ⊆ K̄` over `K` (a `K̄`-point of a scheme of finite
type over `K` factors through `Spec F`, `F` generated by the images of finitely many coordinates;
standard, e.g. EGA I/IV, locator UNVERIFIED). -/
def PtFinite (A : PkgI3.AbVar K) : Prop :=
  ∀ P : A.Pt (AlgebraicClosure K), ∃ F : IntermediateField K (AlgebraicClosure K),
    FiniteDimensional K F ∧ ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (∀ x ∈ F, τ x = x) → A.galAct τ P = P

/-- **`WildIter` from `PtFinite` (proved).** -/
theorem wildIter_of_ptFinite {A : PkgI3.AbVar K} (h : PtFinite A) : WildIter (p := p) A := by
  intro σ hσ σ' hσ' P
  obtain ⟨F, hF, hP⟩ := h P
  obtain ⟨a, ha⟩ := wild_pow_fix_field (σ' := σ') hσ hσ' F
  have hit := galAct_iterate A σ' P (p ^ a)
  exact ⟨a, hit.trans (hP _ ha)⟩

/-- **`TorsFixWild` at `p ≥ 7`, `p ≠ ℓ`, from `WildIter`, I2-Tors and Raynaud at the place
(proved).** `m = 3` (`m = 7` if `p = 13`): the wild `σ'` fixes `A[m]`
(`fix_torsion_of_coprime`), so `(σ'-1)² = 0` on `A[ℓⁿ]` (`RaynaudPlace`), and with a `p`-power
period it fixes `A[ℓⁿ]` (`fixed_of_unipSq_of_iterate'`). -/
theorem torsFixWild_of_raynaud {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hI : WildIter (p := p) A) (hT3 : TorsGL A 3) (hT7 : TorsGL A 7)
    (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3) (hR7 : p = 13 → RaynaudPlace (p := p) A 7) :
    TorsFixWild (p := p) A ℓ := by
  intro σ hσ σ' hσ' n x hx
  have hpp : p.Prime := Fact.out
  have hfixm : ∃ m, (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) ∧
      RaynaudPlace (p := p) A m := by
    by_cases h13 : p = 13
    · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      refine ⟨7, fix_torsion_of_coprime hI 7 hT7 ?_ hσ hσ', hR7 h13⟩
      rw [card_GL4_seven, h13]; exact coprime_card_GL4_seven
    · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      refine ⟨3, fix_torsion_of_coprime hI 3 hT3 ?_ hσ hσ', hR3 h13⟩
      rw [card_GL4_three]; exact coprime_card_GL4_three hpp h7 h13
  obtain ⟨m, hm, hR⟩ := hfixm
  obtain ⟨a, ha⟩ := hI σ hσ σ' hσ' x
  have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
    Nat.Coprime.pow a n ((Nat.coprime_primes hpp Fact.out).mpr (Ne.symm hℓp))
  exact fixed_of_unipSq_of_iterate' A σ' x ℓ n p a hcop hx
    (hR σ hσ σ' hσ' hm ℓ Fact.out hℓp n x hx) ha

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves I2-Tors and (through `RaynaudPlace`) R6,
and the bridge `WildIter` (proved).** `dim A = 2` is a clause of `G7Out`. -/
theorem tateWildK_of_leaves {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hI : WildIter (p := p) A) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_torsFixWild (torsFixWild_of_raynaud hℓp h7 hI (torsGL_of_leaf hTors A hdim 3
    (by norm_num)) (torsGL_of_leaf hTors A hdim 7 (by norm_num)) hR3 hR7)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors, `PtFinite` and `RaynaudPlace`
(proved).** -/
theorem tateWildK_of_leaves' {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hPt : PtFinite A) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter_of_ptFinite hPt) hR3 hR7

end TorsSec

end G15Ram

end


/-! ## §7b (local-glue). `PtFinite` proved: `K̄`-points come from finite extensions

`K̄ = colim F` over the finite subextensions `F` of `K̄/K` (as in scratch/morph-descend's
`ringCoconeIsColimit`, there for `ℚ̄`), so `Spec K̄ = lim Spec F`; since `A → Spec K` is smooth,
hence locally of finite presentation, Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(Stacks 01ZC) factors every `K`-morphism `Spec K̄ → A` through some `Spec F`. -/

noncomputable section

namespace G15Ram

open CategoryTheory Limits AlgebraicGeometry

section PtFiniteSec

variable {K : Type} [Field K]

/-- The finite subextensions of `K̄/K`, ordered by inclusion. -/
abbrev FIdx (K : Type) [Field K] : Type :=
  {F : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K F}

instance : IsDirectedOrder (FIdx K) where
  directed F₁ F₂ := by
    obtain ⟨F₁, h₁⟩ := F₁
    obtain ⟨F₂, h₂⟩ := F₂
    exact ⟨⟨F₁ ⊔ F₂, IntermediateField.finiteDimensional_sup F₁ F₂⟩,
      show F₁ ≤ F₁ ⊔ F₂ from le_sup_left, show F₂ ≤ F₁ ⊔ F₂ from le_sup_right⟩

instance : Nonempty (FIdx K) := ⟨⟨⊥, inferInstance⟩⟩

/-- The diagram `F ↦ F` of rings. -/
def fRingDiag (K : Type) [Field K] : FIdx K ⥤ CommRingCat where
  obj F := CommRingCat.of F.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `K̄` as a cocone. -/
def fRingCocone (K : Type) [Field K] : Cocone (fRingDiag K) where
  pt := CommRingCat.of (AlgebraicClosure K)
  ι := { app F := CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure K))
         naturality _ _ _ := rfl }

/-- `K̄ = colim F` over the finite subextensions (as morph-descend's `ringCoconeIsColimit`). -/
def fRingCoconeIsColimit (K : Type) [Field K] : IsColimit (fRingCocone K) := by
  haveI : ReflectsColimit (fRingDiag K) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : AlgebraicClosure K)
    have hx : _root_.IsIntegral K x := Algebra.IsIntegral.isIntegral _
    have : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, this⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [Subtype.ext h]⟩

/-- The diagram `F ↦ Spec F` of schemes. -/
def fSpecDiag (K : Type) [Field K] : (FIdx K)ᵒᵖ ⥤ Scheme where
  obj F := Spec (CommRingCat.of F.unop.1)
  map f := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)
  map_id F := by
    rw [show CommRingCat.ofHom (IntermediateField.inclusion (leOfHom (𝟙 F).unop)).toRingHom =
      𝟙 _ from rfl, Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp]
    rfl

/-- `Spec K̄` as a cone over `fSpecDiag`. -/
def fSpecCone (K : Type) [Field K] : Cone (fSpecDiag K) where
  pt := Spec (CommRingCat.of (AlgebraicClosure K))
  π := { app F := Spec.map (CommRingCat.ofHom (algebraMap F.unop.1 (AlgebraicClosure K)))
         naturality F F' f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          change _ = _ ≫ Spec.map _
          rw [← Spec.map_comp]
          rfl }

/-- `Spec K̄ = lim Spec F` (proved; `Spec` turns the colimit `fRingCoconeIsColimit` into a limit). -/
def fSpecConeIsLimit (K : Type) [Field K] : IsLimit (fSpecCone K) := by
  have h := isLimitOfPreserves Scheme.Spec (fRingCoconeIsColimit K).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro F F' f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro F
    simp only [Iso.refl_hom, Category.id_comp]

/-- **`PtFinite` holds for every abelian variety (proved).** -/
theorem ptFinite (A : PkgI3.AbVar K) : PtFinite A := by
  intro P
  have h3 : ∀ {i j : (FIdx K)ᵒᵖ} (f : i ⟶ j), IsAffineHom ((fSpecDiag K).map f) := fun f => by
    change IsAffineHom (Spec.map _); infer_instance
  have h1 : ∀ i, CompactSpace ((fSpecDiag K).obj i) := fun i => by
    change CompactSpace (Spec _); infer_instance
  have h2 : ∀ i, QuasiSeparatedSpace ((fSpecDiag K).obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _); infer_instance
  let t : fSpecDiag K ⟶ (Functor.const _).obj (Spec (CommRingCat.of K)) :=
    { app F := Spec.map (CommRingCat.ofHom (algebraMap K F.unop.1))
      naturality F F' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map]
        change Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp]
        rfl }
  have ha : (fSpecCone K).π ≫ t = (Functor.const _).map (P.left ≫ A.X.hom) := by
    ext F
    simp only [NatTrans.comp_app, Functor.const_map_app]
    change Spec.map _ ≫ Spec.map _ = P.left ≫ A.X.hom
    rw [← Spec.map_comp, Over.w P]
    rfl
  obtain ⟨F, g, hg, -⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (fSpecDiag K) t A.X.hom
      (fSpecCone K) (fSpecConeIsLimit K) P.left ha
  refine ⟨F.unop.1, F.unop.2, fun τ hτ => ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ P.left =
    P.left
  rw [← hg]
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) ?_)
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  ext x
  exact hτ x.1 x.2

/-- **`WildIter` holds for every abelian variety (proved)**: `wildIter_of_ptFinite` and
`ptFinite`. -/
theorem wildIter {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) : WildIter (p := p) A :=
  wildIter_of_ptFinite (ptFinite A)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors and the instances `RaynaudPlace`
of the leaf R6 alone (proved).** -/
theorem tateWildK_of_raynaud {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p)
    (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter A) hR3 hR7

end PtFiniteSec

end G15Ram

end


/-! ## §7c' (local-glue). Verbatim slices of scratch/neron-lg/NeronLG.lean (origin/wip/neron-lg)
l.207-215, l.225-236, l.1406-1472 -/

noncomputable section

namespace ZInQ.NeronLG

open NumberField
open CategoryTheory MonObj

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

section Classify

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

end Classify

section Restrict

variable {K : Type} [Field K] [NumberField K]

/-- The center of a valuation subring `O ≠ ⊤` of a number field on `𝓞_K`: a nonzero prime. -/
def center' (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
      by_contra h
      push_neg at h
      exact hO (eq_top_iff.2 fun y _ => h y)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let x : O := ⟨y⁻¹, hyi⟩
    have hx : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu
      apply hy
      have : ((u⁻¹ : Oˣ) : O) * x = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Oˣ) : O) : K)) * y⁻¹ = 1 := congrArg Subtype.val this
      have h3 : y = (((u⁻¹ : Oˣ) : O) : K) := by
        field_simp at h2
        exact h2.symm
      rw [h3]; exact (((u⁻¹ : Oˣ) : O)).2
    have hx0 : x ≠ 0 := fun h => inv_ne_zero hy0 (congrArg Subtype.val h)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

/-- **Every valuation subring `O ≠ ⊤` of a number field is `𝓞_{K,v}` (proved).** -/
theorem dvrAt_center' (O : ValuationSubring K) (hO : O ≠ ⊤) : dvrAt (center' O hO) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hO
  intro x hx
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center' O hO) x hx
  have hd : IsUnit (toO O d) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
  apply O.mem_of_valuation_le_one
  have h2 := congrArg O.valuation hnd
  rw [map_mul, hvd, _root_.mul_one] at h2
  rw [h2]
  exact O.valuation_le_one (toO O n)

/-- Every valuation subring `O ≠ ⊤` of a number field is a DVR. -/
theorem isDiscreteValuationRing_of_ne_top (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  rw [← dvrAt_center' O hO]
  infer_instance

end Restrict

end ZInQ.NeronLG

end


/-! ## §7c'' (local-glue). Verbatim copy of scratch/unram-tate/BCPoints.lean
(origin/wip/unram-tate) l.14-142 -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace UnramTate

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

end Tr

end UnramTate

end


/-! ## §7c (local-glue). Raynaud's criterion (R6) at the place of `embP`: the rational case

`raynaudPlace_rational` (proved): if `A[m]` is `K`-rational (`m ≥ 3`, `p ∤ m`), the leaf R6
(`ObjBridge.RaynaudCriterion`) gives `RaynaudPlace A m`. The valuation-theoretic bridge is proved:
* `wK`, `OK`: the valuation subrings of `K̄` and `K` at the place of `embP` (norm `≤ 1` after
  `K̄ ≅ ℚ̄ → ℚ̄_p`); `OK` is a DVR (`OK_ne_top` and neron-lg's `isDiscreteValuationRing_of_ne_top`);
* `m`, `ℓ` prime to `p` are units of `OK`;
* a wild `σ'` (over `decomp σ`) lies in the inertia group of `wK` (`isInertia_of_wild`).
The general case of `RaynaudPlace` needs R6 over `K(A[m])` and the base change of `A`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj
open scoped Pointwise

section RaynaudSec

/-- The valuation subring `{x : ‖f x‖ ≤ 1}` for a ring map `f` to an ultrametric normed field. -/
def normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E) :
    ValuationSubring F where
  carrier := {x | ‖f x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' x := by
    by_cases h : ‖f x‖ ≤ 1
    · exact Or.inl h
    · right
      show ‖f x⁻¹‖ ≤ 1
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h))

theorem mem_normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E)
    (x : F) : x ∈ normVS f ↔ ‖f x‖ ≤ 1 := Iff.rfl

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]

/-- `ℚ̄ ≅ K̄` (`qEmbRing` is bijective). -/
def eK (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

/-- `K̄ ≅ ℚ̄ → ℚ̄_p`, the place of `embP` on `K̄`. -/
def ιbar (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    AlgebraicClosure K →+* Kbar p :=
  (embP (p := p)).comp (eK K).symm.toRingHom

/-- The valuation ring of `K̄` at the place of `embP`. -/
def wK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    ValuationSubring (AlgebraicClosure K) :=
  normVS (ιbar p K)

/-- The valuation ring of `K` at the place of `embP`. -/
def OK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] : ValuationSubring K :=
  normVS ((ιbar p K).comp (algebraMap K (AlgebraicClosure K)))

theorem wK_comap : (wK p K).comap (algebraMap K (AlgebraicClosure K)) = OK p K := by
  ext x; exact Iff.rfl

theorem OK_ne_top : OK p K ≠ ⊤ := by
  intro h
  have hmem : ((p : K))⁻¹ ∈ OK p K := by rw [h]; exact ValuationSubring.mem_top _
  rw [OK, mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

instance OK_dvr : IsDiscreteValuationRing (OK p K) :=
  ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ OK_ne_top

/-- A natural number prime to `p` is a unit of `OK`. -/
theorem isUnit_natCast_OK {n : ℕ} (hn : ¬ p ∣ n) : IsUnit ((n : OK p K)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : K) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by
      have := congrArg ((ιbar p K).comp (algebraMap K (AlgebraicClosure K))) h0
      simpa using this
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : K))⁻¹ ∈ OK p K := by
    rw [OK, mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : OK p K) : K) * ((n : K))⁻¹ = 1
  rw [show ((n : OK p K) : K) = (n : K) from by simp]
  exact mul_inv_cancel₀ hn0

/-- `ιbar ∘ σ' = σ ∘ ιbar` for `σ'` over `decomp σ` (proved, from `resQ_spec`, `decomp_spec`). -/
theorem ιbar_apply {σ : GQp p} {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (y : AlgebraicClosure K) :
    ιbar p K (σ' y) = σ (ιbar p K y) := by
  obtain ⟨z, rfl⟩ := (eK K).surjective y
  have h1 : σ' (eK K z) = eK K (decomp p σ z) := by
    have := G0Galois.resQ_spec K σ' z
    rw [hσ'] at this
    exact this.symm
  simp only [ιbar, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, decomp_spec]

theorem norm_wild_eq {σ : GQp p} (hσ : σ ∈ wildSet) (u : Kbar p) : ‖σ u‖ = ‖u‖ := by
  by_cases hu : u = 0
  · rw [hu, map_zero]
  have h := hσ u hu
  have : σ u = u + (σ u - u) := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h),
    max_eq_left (le_of_lt h)]

/-- **A wild `σ'` lies in the inertia group of `wK` (proved).** -/
theorem isInertia_of_wild {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) : PkgI2.IsInertia (wK p K) σ' := by
  have hnorm : ∀ y, ‖ιbar p K (σ' y)‖ = ‖ιbar p K y‖ := fun y => by
    rw [ιbar_apply hσ', norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖ιbar p K (σ'⁻¹ y)‖ = ‖ιbar p K y‖ := fun y => by
    have := hnorm (σ'⁻¹ y)
    rw [show σ' (σ'⁻¹ y) = y from by
      change (σ' * σ'⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : σ' ∈ (wK p K).decompositionSubgroup K := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖ιbar p K (σ'⁻¹ x)‖ ≤ 1 ↔ ‖ιbar p K x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • IsLocalRing.residue (wK p K) a =
    IsLocalRing.residue (wK p K) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : wK p K := (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • a - a with hb
  have hbval : (b : AlgebraicClosure K) = σ' a - a := rfl
  have hlt : ‖ιbar p K (b : AlgebraicClosure K)‖ < 1 := by
    rw [hbval, map_sub, ιbar_apply hσ']
    by_cases ha0 : ιbar p K (a : AlgebraicClosure K) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : ιbar p K (b : AlgebraicClosure K) * ιbar p K (c : AlgebraicClosure K) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : wK p K) : AlgebraicClosure K) = (b : AlgebraicClosure K) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖ιbar p K (c : AlgebraicClosure K)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖ιbar p K (b : AlgebraicClosure K)‖ := norm_nonneg _
  nlinarith

/-- **`RaynaudPlace` when `A[m]` is `K`-rational, from the leaf R6 (proved).** -/
theorem raynaudPlace_rational (hR6 : ObjBridge.RaynaudCriterion) (A : PkgI3.AbVar K) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m)
    (hrat : ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P) :
    RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' _ ℓ hℓ hℓp n x hx
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  exact hR6 K (OK p K) (wK p K) wK_comap (ObjBridge.toGrp A) m hm3 (isUnit_natCast_OK hpm)
    hrat σ' (isInertia_of_wild hσ hσ') ℓ hℓ (isUnit_natCast_OK hℓp') n x hx

end RaynaudSec


/-! ### The general case: R6 over the field of `A[m]`, via the base change of `A` -/

section RaynaudGen

variable {p : ℕ} [Fact p.Prime]

/-- `normVS f ≠ ⊤` for a map of a field to `ℚ̄_p` (`1/p ∉`). -/
theorem normVS_ne_top {F : Type} [Field F] [CharZero F] (f : F →+* Kbar p) : normVS f ≠ ⊤ := by
  intro h
  have hmem : ((p : F))⁻¹ ∈ normVS f := by rw [h]; exact ValuationSubring.mem_top _
  rw [mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

/-- A natural number prime to `p` is a unit of `normVS f`. -/
theorem isUnit_natCast_normVS {F : Type} [Field F] (f : F →+* Kbar p) {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : normVS f)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : F) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by simpa using congrArg f h0
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : F))⁻¹ ∈ normVS f := by
    rw [mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : normVS f) : F) * ((n : F))⁻¹ = 1
  rw [show ((n : normVS f) : F) = (n : F) from by simp]
  exact mul_inv_cancel₀ hn0

/-- **Wild elements are inertial (general form, proved).** If `f ∘ τ = σ ∘ f` with `σ` wild, then
`τ` lies in the inertia group of `normVS f`. -/
theorem isInertia_of_wild_gen {K₀ Ω : Type} [Field K₀] [Field Ω] [Algebra K₀ Ω]
    (f : Ω →+* Kbar p) {σ : GQp p} (hσ : σ ∈ wildSet) (τ : Ω ≃ₐ[K₀] Ω)
    (hf : ∀ y, f (τ y) = σ (f y)) : PkgI2.IsInertia (normVS f) τ := by
  have hnorm : ∀ y, ‖f (τ y)‖ = ‖f y‖ := fun y => by rw [hf, norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖f (τ⁻¹ y)‖ = ‖f y‖ := fun y => by
    have := hnorm (τ⁻¹ y)
    rw [show τ (τ⁻¹ y) = y from by
      change (τ * τ⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : τ ∈ (normVS f).decompositionSubgroup K₀ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖f (τ⁻¹ x)‖ ≤ 1 ↔ ‖f x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • IsLocalRing.residue (normVS f) a =
    IsLocalRing.residue (normVS f) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : normVS f := (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • a - a with hb
  have hbval : (b : Ω) = τ a - a := rfl
  have hlt : ‖f (b : Ω)‖ < 1 := by
    rw [hbval, map_sub, hf]
    by_cases ha0 : f (a : Ω) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : f (b : Ω) * f (c : Ω) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : normVS f) : Ω) = (b : Ω) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖f (c : Ω)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖f (b : Ω)‖ := norm_nonneg _
  nlinarith

variable {K : Type} [Field K] [NumberField K]

/-- The stabilizer of `A(K̄)[m]` in `G_K`. -/
def torsStab (A : PkgI3.AbVar K) (m : ℕ) :
    Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  carrier := {τ | ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P}
  mul_mem' {a b} ha hb P hP := by
    rw [← galAct_galAct, hb P hP, ha P hP]
  one_mem' P _ := by
    change PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  inv_mem' {a} ha P hP := by
    calc A.galAct a⁻¹ P = A.galAct a⁻¹ (A.galAct a P) := by rw [ha P hP]
      _ = P := galAct_inv_galAct A a P

/-- The stabilizer of `A[m]` contains `G_{F'}` for a finite `F'/K` (from `ptFinite`, `A[m]`
finite by I2-Tors). -/
theorem exists_fin_le_torsStab (A : PkgI3.AbVar K) (m : ℕ) [NeZero m] (hT : TorsGL A m) :
    ∃ F' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K F' ∧
      F'.fixingSubgroup ≤ torsStab A m := by
  obtain ⟨e, -⟩ := hT
  haveI : Finite {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} := Finite.of_equiv _ e.symm
  choose F hF hP using fun P : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} => ptFinite A P.1
  haveI : ∀ i, FiniteDimensional K (F i) := hF
  refine ⟨⨆ i, F i, inferInstance, fun τ hτ P hPm => ?_⟩
  refine hP ⟨P, hPm⟩ τ (fun x hx => ?_)
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
  exact hτ x ((le_iSup F ⟨P, hPm⟩) hx)

/-- **`RaynaudPlace` from the leaves R6 and I2-Tors (proved), for `dim A = 2`, `3 ≤ m`,
`p ∤ m`.** R6 is applied over `F = K(A[m])` (the fixed field of the stabilizer of `A[m]`, finite
by `ptFinite`) to the base change `A_F`, with the valuation rings at the place of `embP`
transported along `K̄ ≅ F̄`; points of `A_F` are those of `A` (`bcPt`, `trPt`, copied from
scratch/unram-tate). -/
theorem raynaudPlace_of_R6 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) : RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' hfix ℓ hℓ hℓp n x hx
  set σg : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ' with hσg
  haveI : NeZero m := ⟨by omega⟩
  set H := torsStab A m with hHdef
  obtain ⟨F', hF'fd, hF'H⟩ := exists_fin_le_torsStab A m (torsGL_of_leaf hTors A hdim m (by omega))
  have hHopen : IsOpen (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isOpen_mono hF'H (IntermediateField.fixingSubgroup_isOpen F')
  have hHclosed : IsClosed (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isClosed_of_isOpen H hHopen
  set F : IntermediateField K (AlgebraicClosure K) := IntermediateField.fixedField H with hFdef
  have hFH : F.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hFF' : F ≤ F' := by
    intro y hy
    rw [← InfiniteGalois.fixedField_fixingSubgroup F']
    rw [IntermediateField.mem_fixedField_iff] at hy ⊢
    exact fun τ hτ => hy τ (hF'H hτ)
  haveI : FiniteDimensional K F :=
    Module.Finite.of_injective (IntermediateField.inclusion hFF').toLinearMap
      (IntermediateField.inclusion hFF').injective
  haveI : FiniteDimensional ℚ F := Module.Finite.trans K F
  haveI : NumberField F := ⟨⟩
  -- `σ'` fixes `F`
  have hσ'F : ∀ y ∈ F, σg y = y := fun y hy =>
    ((IntermediateField.mem_fixedField_iff _ _).mp hy) σg hfix
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  -- `K̄` is an algebraic closure of `F`
  haveI : IsAlgClosure F (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (L := F) (A := AlgebraicClosure K)⟩
  let Ω := AlgebraicClosure F
  let ψ : Ω ≃ₐ[F] AlgebraicClosure K := IsAlgClosure.equiv F Ω (AlgebraicClosure K)
  let σF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K :=
    { σg.toRingEquiv with commutes' := fun c => hσ'F c c.2 }
  let σ₁ : Ω ≃ₐ[F] Ω := (ψ.trans σF).trans ψ.symm
  have hσ₁ : ∀ y, ψ (σ₁ y) = σg (ψ y) := fun y => by
    simp only [σ₁, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    rfl
  let f₁ : Ω →+* Kbar p := (ιbar p K).comp (ψ : Ω →+* AlgebraicClosure K)
  have hf₁ : ∀ y, f₁ (σ₁ y) = σ (f₁ y) := fun y => by
    change ιbar p K (ψ (σ₁ y)) = σ (ιbar p K (ψ y))
    rw [hσ₁ y]
    exact ιbar_apply (σ' := σg) hσ' (ψ y)
  let w₁ : ValuationSubring Ω := normVS f₁
  let O₁ : ValuationSubring F := normVS (f₁.comp (algebraMap F Ω))
  have hw₁ : w₁.comap (algebraMap F Ω) = O₁ := by ext; exact Iff.rfl
  haveI : IsDiscreteValuationRing O₁ :=
    ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ (normVS_ne_top _)
  -- points of `A_F` over `Ω` are points of `A` over `K̄`
  let A₁ : PkgI3.AbVar F := A.baseChange F
  let ψK : Ω ≃ₐ[K] AlgebraicClosure K := ψ.restrictScalars K
  let Φ : A₁.Pt Ω ≃* A.Pt (AlgebraicClosure K) :=
    (UnramTate.bcPt A Ω).trans (UnramTate.trPt A ψK)
  have hΦ : ∀ (τ₁ : Ω ≃ₐ[F] Ω) (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      (∀ y, τ (ψ y) = ψ (τ₁ y)) → ∀ z, Φ (A₁.galAct τ₁ z) = A.galAct τ (Φ z) := by
    intro τ₁ τ h z
    change UnramTate.trPt A ψK (UnramTate.bcPt A Ω (A₁.galAct τ₁ z)) =
      A.galAct τ (UnramTate.trPt A ψK (UnramTate.bcPt A Ω z))
    rw [UnramTate.bcPt_galAct, UnramTate.trPt_galAct A ψK (τ₁.restrictScalars K) τ h]
  have hrat : ∀ τ₁ : Ω ≃ₐ[F] Ω, ∀ z ∈ PkgI2.torsion (ObjBridge.toGrp A₁) Ω m,
      PkgI2.galAct (ObjBridge.toGrp A₁) τ₁ z = z := by
    intro τ₁ z₀ hz
    let z : A₁.Pt Ω := z₀
    change A₁.galAct τ₁ z = z
    let τF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K := (ψ.symm.trans τ₁).trans ψ
    let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τF.restrictScalars K
    have hτ : ∀ y, τ (ψ y) = ψ (τ₁ y) := fun y => by
      change ψ (τ₁ (ψ.symm (ψ y))) = ψ (τ₁ y)
      rw [AlgEquiv.symm_apply_apply]
    have hτH : τ ∈ H := by
      rw [← hFH, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact τF.commutes ⟨y, hy⟩
    have hz' : z ^ m = 1 := hz
    have hzm : (Φ z) ^ m = 1 := by rw [← map_pow, hz', map_one]
    have h1 := hΦ τ₁ τ hτ z
    rw [hτH (Φ z) hzm] at h1
    exact Φ.injective h1
  have hxm : (Φ.symm x) ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hU := hR6 F O₁ w₁ hw₁ (ObjBridge.toGrp A₁) m hm3 (isUnit_natCast_normVS _ hpm) hrat σ₁
    (isInertia_of_wild_gen f₁ hσ σ₁ hf₁) ℓ hℓ (isUnit_natCast_normVS _ hℓp') n (Φ.symm x) hxm
  have hU' : A₁.galAct σ₁ (A₁.galAct σ₁ (Φ.symm x)) * (A₁.galAct σ₁ (Φ.symm x))⁻¹ *
      (A₁.galAct σ₁ (Φ.symm x))⁻¹ * Φ.symm x = 1 := hU
  have hcomm : ∀ z, Φ (A₁.galAct σ₁ z) = A.galAct σg (Φ z) :=
    hΦ σ₁ σg (fun y => (hσ₁ y).symm)
  have h2 := congrArg Φ hU'
  simp only [map_one, map_mul, map_inv, hcomm, MulEquiv.apply_symm_apply] at h2
  exact h2

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves R6 and I2-Tors alone (proved).**
`m = 3` for `p ≠ 13`, `m = 7` for `p = 13` (`raynaudPlace_of_R6`, `tateWildK_of_raynaud`). -/
theorem tateWildK_of_R6 (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    {A : PkgI3.AbVar K} (hdim : A.dim = 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p) :
    TateWildK (p := p) A ℓ := by
  have hp : p.Prime := Fact.out
  refine tateWildK_of_raynaud hℓp h7 hTors hdim (fun _ => raynaudPlace_of_R6 hR6 hTors A hdim
    (by norm_num) ?_) (fun h13 => raynaudPlace_of_R6 hR6 hTors A hdim (by norm_num) ?_)
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · intro h
    rw [h13] at h
    norm_num at h

/-- **`LocalGlue` on G7's data from the leaves R6 and I2-Tors (proved), with the remaining glue
`KerWild`, `TateWildKE` (`p ≤ 5`) and `BetaTwist2` (`p = 2`).** At `p ≥ 7`, `p ≠ ℓ`, no glue is
left. -/
theorem localGlue_of_leaves (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_g7_twist h7 hC hK (fun h => tateWildK_of_R6 hR6 hTors h7.1 (Ne.symm hpℓ) h) hE hB

end RaynaudGen

end G15Ram

end

namespace RQ

theorem numberField_of_fd (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def actQ (τ : Field.absoluteGaloisGroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
/-- An element of `G_K` as an automorphism of `\bar K`. -/
def actK {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `resQ K σ` is `σ` transported along the embedding `g : ℚ̄ → \bar K` that
`Field.absoluteGaloisGroup.map` chooses. -/
theorem resQ_comm' (K : Type) [Field K] [NumberField K] :
    ∃ g : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ σ x,
      g (actQ (G0Galois.resQ K σ) x) = actK σ (g x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ) (AlgebraicClosure ℚ) x

/-- **`ResQRange` proved**: for finite Galois `L ⊆ ℚ̄`, the image of `resQ L` is `Fix(L)`
(normality of `L` gives `g(L) = L` inside `\bar L`; `g` is bijective because `\bar L/ℚ` is
algebraic). -/
theorem resQ_range (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    (@G0Galois.resQ L _ (numberField_of_fd L)).range = L.fixingSubgroup := by
  haveI := numberField_of_fd L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  -- `g` is bijective (`AlgebraicClosure L` is algebraic over `ℚ`)
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : L →ₐ[ℚ] AlgebraicClosure L := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  let e : L ≃ₐ[ℚ] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal ℚ ψ.fieldRange := Normal.of_algEquiv e
  let f : ψ.fieldRange →ₐ[ℚ] AlgebraicClosure L := (g.comp L.val).comp e.symm.toAlgHom
  have hf := AlgHom.fieldRange_of_normal f
  have hgL : ∀ x : L, ∃ y : L, g x = ψ y := by
    intro x
    have hx : g x ∈ f.fieldRange := ⟨e x, by simp [f]⟩
    rw [hf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hLg : ∀ y : L, ∃ x : L, g x = ψ y := by
    intro y
    have hy : ψ y ∈ f.fieldRange := by rw [hf]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨e.symm z, by simpa [f] using hz⟩
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    refine (IntermediateField.mem_fixingSubgroup_iff L (actQ (G0Galois.resQ L σ))).mpr ?_
    intro x hx
    apply g.toRingHom.injective
    show g (actQ (G0Galois.resQ L σ) x) = g x
    rw [hg, hcomm σ x, ← hg]
    obtain ⟨y, hy⟩ := hgL ⟨x, hx⟩
    have hy' : g x = ψ y := hy
    rw [hy']
    exact (actK σ).commutes y
  · intro hτ'
    have hτ := (IntermediateField.mem_fixingSubgroup_iff L (actQ τ)).mp hτ'
    let eg : PkgI4.Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g.toRingHom hgbij
    let τ' : PkgI4.Qbar ≃ₐ[ℚ] PkgI4.Qbar := τ
    let σ₀ : AlgebraicClosure L ≃+* AlgebraicClosure L := (eg.symm.trans τ'.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ' x) := by
      intro x
      show eg (τ' (eg.symm (eg x))) = g (τ' x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hfix : ∀ y : L, σ₀ (algebraMap L (AlgebraicClosure L) y) =
        algebraMap L (AlgebraicClosure L) y := by
      intro y
      obtain ⟨x, hx⟩ := hLg y
      have hx' : g x = algebraMap L (AlgebraicClosure L) y := hx
      rw [← hx', hσ₀, show τ' (x : PkgI4.Qbar) = x from hτ x x.2]
    let σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (G0Galois.resQ L σ) x) = g (τ' x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x

end RQ

/-! ## §7d (local-glue). `p ≤ 5`: the torsion field of a model over `L` (proved from a descent Prop)

At `p ∈ {2, 3, 5}` the trick of §7 (`p ∤ |GL₄(𝔽_m)|`) is not available (finding G3), and Glazer
uses the model `A_L` over the Hom field `L` (N5 L813-818): `E = L_v(A_L[m])`, of degree
`≤ |GL₄(𝔽_m)|` over `L_v`. Here:
* `DescentPts A L` (GLUE, new): `L/ℚ` is Galois and `A` has a model `A₀` over `L` with
  `dim A₀ = 2` and a group isomorphism `A₀(L̄) ≅ A(K̄)` intertwining `σ₀ ∈ G_L` with `σ' ∈ G_K`
  whenever both restrict to the same element of `G_ℚ`;
* `index_torsStab_le` (proved): `[G_L : Stab(A₀[q])] ≤ |GL₄(𝔽_q)|` (I2-Tors);
* `torsFix_of_descent` (proved): from R6, I2-Tors and `DescentPts`, for `q ≠ p` prime, `q ≥ 3`, and
  any finite `M ⊇ L_v`, there is `E ⊇ M` with `[E:ℚ_p] ≤ |GL₄(𝔽_q)|·[M:ℚ_p]` on whose wild inertia
  every `ℓⁿ`-torsion point of `A(K̄)` is fixed (`ℓ ≠ p`). `E` is the fixed field of the open
  subgroup `decomp⁻¹(resQ_L(Stab)) ∩ G_M`; its degree is the index (Mathlib's
  `finrank_eq_fixingSubgroup_index`);
* `torsFixWildOdd_of_descent`, `torsFixWildE_two_of_descent`, `tateWildKE_of_descent`,
  `localGlue_of_descent` (proved). -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj

section DescentSec

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] RQ.numberField_of_fd

/-- **Glue (the descent of `A` to the Hom field `L`; N5 L813-818; g0-mod-field: `G7Data` carries
`A : AbVar L` and `TateBridge` takes `A_{L'}` to be its base change to `L'`).** `L/ℚ` is Galois, and
`A/K` has a model `A₀/L` (`dim A₀ = 2`) with a group isomorphism `φ : A₀(L̄) ≅ A(K̄)` such that
`φ ∘ σ₀ = σ' ∘ φ` whenever `σ₀ ∈ G_L` and `σ' ∈ G_K` have the same image in `G_ℚ` (`resQ`). For
`K = L'` and `A = (A₀)_{L'}` this is the base change of points (`bcPt`) along an identification
`L̄ ≅ L̄'` compatible with `qEmb L` and `qEmb L'`; if Mathlib's choices of the embeddings
`L ↪ ℚ̄` (inside `resQ L`, `resQ L'`) differ on `L` by `γ ∈ Gal(L/ℚ)`, the model is the conjugate
`A₀ ×_{L,γ} L`, so the existential is still met. -/
def DescentPts {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] : Prop :=
  IsGalois ℚ L ∧
  ∃ (A₀ : PkgI3.AbVar L) (φ : A₀.Pt (AlgebraicClosure L) ≃* A.Pt (AlgebraicClosure K)),
    A₀.dim = 2 ∧ ∀ (σ₀ : Field.absoluteGaloisGroup L) (σ' : Field.absoluteGaloisGroup K),
      G0Galois.resQ L σ₀ = G0Galois.resQ K σ' →
        ∀ P : A₀.Pt (AlgebraicClosure L), φ (A₀.galAct σ₀ P) = A.galAct σ' (φ P)

variable {K : Type} [Field K] [NumberField K]

/-- **`[G_K : Stab(A[q])] ≤ |GL₄(𝔽_q)|` (proved)** from `A(K̄)[q] ≅ (ℤ/q)⁴` (`TorsGL`): the
action on `A[q]` is a homomorphism `G_K → GL(𝔽_q⁴)` whose kernel is the stabilizer. -/
theorem index_torsStab_le (A : PkgI3.AbVar K) (q : ℕ) [Fact q.Prime] (hT : TorsGL A q) :
    (torsStab A q).index ≠ 0 ∧
      (torsStab A q).index ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) := by
  set S := {P : A.Pt (AlgebraicClosure K) | P ^ q = 1} with hSdef
  obtain ⟨e, he⟩ := hT
  have hS : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : S), A.galAct σ x.1 ∈ S :=
    fun σ x => by
      have hx : x.1 ^ q = 1 := x.2
      show (A.galAct σ x.1) ^ q = 1
      rw [← map_pow, hx, map_one]
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := fun x hx y hy => by
    simp only [hSdef, Set.mem_setOf_eq] at hx hy ⊢
    rw [mul_pow, hx, hy, _root_.one_mul]
  let f : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → (Fin 4 → ZMod q) → (Fin 4 → ZMod q) :=
    fun σ v => e ⟨A.galAct σ (e.symm v).1, hS σ _⟩
  have hadd : ∀ σ a b, f σ (a + b) = f σ a + f σ b := by
    intro σ a b
    set x := e.symm a
    set y := e.symm b
    have hxy : e.symm (a + b) = ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he x y, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have h1 : (⟨A.galAct σ (e.symm (a + b)).1, hS σ _⟩ : S) =
        ⟨(A.galAct σ x.1) * (A.galAct σ y.1), hSmul _ (hS σ x) _ (hS σ y)⟩ := by
      apply Subtype.ext
      simp only [hxy, map_mul]
    show e ⟨A.galAct σ (e.symm (a + b)).1, hS σ _⟩ = e ⟨A.galAct σ x.1, hS σ x⟩ +
      e ⟨A.galAct σ y.1, hS σ y⟩
    rw [h1, he ⟨A.galAct σ x.1, hS σ x⟩ ⟨A.galAct σ y.1, hS σ y⟩]
  have hmul : ∀ σ τ v, f (σ * τ) v = f σ (f τ v) := by
    intro σ τ v
    show e ⟨A.galAct (σ * τ) (e.symm v).1, _⟩ =
      e ⟨A.galAct σ (e.symm (e ⟨A.galAct τ (e.symm v).1, _⟩)).1, _⟩
    congr 1
    apply Subtype.ext
    simp only [Equiv.symm_apply_apply]
    rw [galAct_galAct]
  have hone : ∀ v, f 1 v = v := by
    intro v
    show e ⟨A.galAct 1 (e.symm v).1, _⟩ = v
    have h1 : (⟨A.galAct 1 (e.symm v).1, hS 1 _⟩ : S) = e.symm v := by
      apply Subtype.ext
      change PkgI3.AbVar.galHom 1 ≫ (e.symm v).1 = (e.symm v).1
      rw [PkgI3.AbVar.galHom_one, Category.id_comp]
    rw [h1, Equiv.apply_symm_apply]
  let fL : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →
      ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) := fun σ =>
    { ((AddMonoidHom.mk' (f σ) (hadd σ)).toZModLinearMap q) with
      invFun := f σ⁻¹
      left_inv := fun v => by
        change f σ⁻¹ (f σ v) = v
        rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun v => by
        change f σ (f σ⁻¹ v) = v
        rw [← hmul, mul_inv_cancel, hone] }
  let ρ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) :=
    { toFun := fL
      map_one' := LinearEquiv.ext hone
      map_mul' := fun σ τ => LinearEquiv.ext (hmul σ τ) }
  have hker : ρ.ker ≤ torsStab A q := by
    intro σ hσ P hP
    have h1 : f σ (e ⟨P, hP⟩) = e ⟨P, hP⟩ := by
      have := congrArg (fun g : (Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q) => g (e ⟨P, hP⟩))
        (MonoidHom.mem_ker.mp hσ)
      exact this
    have h2 := e.injective h1
    simp only [Equiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  set N := Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) with hN
  have hcard : Nat.card ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) = N :=
    (Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q)
      (Fin 4 → ZMod q)).toEquiv).symm.trans
      (Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv).symm
  haveI : Finite ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) :=
    Finite.of_equiv _ ((Matrix.GeneralLinearGroup.toLin).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q) (Fin 4 → ZMod q)).toEquiv)
  have hkerI : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have hr1 : 0 < Nat.card ρ.range := Nat.card_pos
  have hrN : Nat.card ρ.range ≤ N := hcard ▸ Subgroup.card_le_card_group _
  have hdvd : (torsStab A q).index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hker
  have hpos : 0 < (torsStab A q).index := Nat.pos_of_dvd_of_pos hdvd (hkerI ▸ hr1)
  exact ⟨hpos.ne', (Nat.le_of_dvd (hkerI ▸ hr1) hdvd).trans (hkerI ▸ hrN)⟩

/-- `resQ K` is injective (proved): `qEmb K ∘ resQ K τ = τ ∘ qEmb K` and `qEmb K` is onto. -/
theorem resQ_injective' : Function.Injective (G0Galois.resQ K) := by
  intro τ₁ τ₂ h
  let τ₁' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ₁
  let τ₂' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ₂
  show τ₁' = τ₂'
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := qEmbRing_surjective K y
  have h1 := G0Galois.resQ_spec K τ₁' x
  have h2 := G0Galois.resQ_spec K τ₂' x
  change τ₁' (G0Galois.qEmbRing K x) = τ₂' (G0Galois.qEmbRing K x)
  rw [← h1, ← h2]
  exact congrArg (fun g => G0Galois.qEmbRing K (g x)) h

/-- **The torsion field of the model over `L` (proved)** from the leaves R6 (`raynaudPlace_of_R6`)
and I2-Tors and the glue `DescentPts`. For a prime `q ≥ 3`, `q ≠ p`, and a finite `M ⊇ L_v`,
there is a finite `E ⊇ M` with `[E:ℚ_p] ≤ |GL₄(𝔽_q)|·[M:ℚ_p]` such that every wild `σ ∈ G_E` fixes
every `ℓⁿ`-torsion point of `A(K̄)` through `G_K` (`ℓ ≠ p`). `E` is the fixed field of
`H = decomp⁻¹(resQ_L(Stab(A₀[q]))) ∩ G_M`, which is open (it contains `G_{E₀}`, `E₀` generated over
`M` by a basis of `L(A₀[q])`, finite by `ptFinite`), and `[E:ℚ_p] = [G_{ℚ_p} : H]`. For wild
`σ ∈ G_E`, `decomp σ = resQ_L σ₀` with `σ₀` fixing `A₀[q]`; Raynaud (`RaynaudPlace A₀ q`) and the
`p`-power period (`wildIter`) give that `σ₀` fixes `A₀[ℓⁿ]` (D2), and `φ` carries this to `A`. -/
theorem torsFix_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q) (hpq : q ≠ p)
    (M : Fld p) [FiniteDimensional ℚ_[p] M] (hLvM : Lv (p := p) L ≤ M) :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ M ≤ E ∧
      Module.finrank ℚ_[p] E ≤
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) * Module.finrank ℚ_[p] M ∧
      ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
        G0Galois.resQ K σ' = decomp p σ →
          ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P := by
  obtain ⟨hGal, A₀, φ, hdim₀, hφ⟩ := hD
  have hp : p.Prime := Fact.out
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp Fact.out).mp h).symm
  have hT₀ : TorsGL A₀ q := torsGL_of_leaf hTors A₀ hdim₀ q (by omega)
  obtain ⟨hidx0, hidx⟩ := index_torsStab_le A₀ q hT₀
  obtain ⟨F', hF'fd, hF'⟩ := exists_fin_le_torsStab A₀ q hT₀
  let Stab : Subgroup (Field.absoluteGaloisGroup L) := torsStab A₀ q
  let ρL : Field.absoluteGaloisGroup L →* GQ := G0Galois.resQ L
  have hρinj : Function.Injective ρL := resQ_injective'
  have hrange : ρL.range = L.fixingSubgroup := RQ.resQ_range L
  let Hq : Subgroup GQ := Stab.map ρL
  let GM : Subgroup (GQp p) := M.fixingSubgroup
  let H : Subgroup (GQp p) := Hq.comap (decomp p) ⊓ GM
  -- `decomp` of `G_M` fixes `L`
  have hdecL : ∀ σ : GQp p, σ ∈ fixSet M → decomp p σ ∈ L.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      (decomp_fix_of_le (fun x hx => hLvM (embP_mem_Lv hx)) hσ)
  -- the open subgroup `G_{E₀}` inside `H`
  haveI : FiniteDimensional L F' := hF'fd
  haveI : Module.Free L F' := Module.Free.of_divisionRing L F'
  let b := Module.finBasis L F'
  let eL : AlgebraicClosure ℚ ≃+* AlgebraicClosure L :=
    RingEquiv.ofBijective (G0Galois.qEmbRing L)
      ⟨(G0Galois.qEmbRing L).injective, qEmbRing_surjective L⟩
  let S₀ : Set (Kbar p) := Set.range fun i => embP (eL.symm (b i : AlgebraicClosure L))
  haveI : Finite S₀ := Set.finite_range _ |>.to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] S₀) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E₀ : Fld p := M ⊔ IntermediateField.adjoin ℚ_[p] S₀
  have hE₀H : E₀.fixingSubgroup ≤ H := by
    intro σ hσ
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
    have hσM : σ ∈ fixSet M := fun x hx => hσ' x (le_sup_left (a := M) hx)
    have hσS : ∀ i, decomp p σ (eL.symm (b i : AlgebraicClosure L)) =
        eL.symm (b i : AlgebraicClosure L) := by
      intro i
      apply (embP (p := p)).injective
      rw [decomp_spec]
      exact hσ' _ (le_sup_right (a := M)
        (IntermediateField.subset_adjoin ℚ_[p] S₀ ⟨i, rfl⟩))
    obtain ⟨σ₀, hσ₀⟩ : decomp p σ ∈ ρL.range := hrange ▸ hdecL σ hσM
    let σ₀' : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L := σ₀
    have hσ₀b : ∀ i, σ₀' (b i : AlgebraicClosure L) = b i := by
      intro i
      have h1 := G0Galois.resQ_spec L σ₀' (eL.symm (b i : AlgebraicClosure L))
      have h2 : G0Galois.qEmbRing L (eL.symm (b i : AlgebraicClosure L)) = b i :=
        eL.apply_symm_apply _
      change G0Galois.qEmbRing L (ρL σ₀ _) = _ at h1
      rw [hσ₀, hσS i, h2] at h1
      exact h1.symm
    have hσ₀F : σ₀' ∈ F'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      have hsum := b.sum_repr ⟨z, hz⟩
      set c := b.repr ⟨z, hz⟩ with hc
      have hz' : z = ∑ i, c i • (b i : AlgebraicClosure L) := by
        have := congrArg (fun w : F' => (w : AlgebraicClosure L)) hsum
        simp only at this
        rw [← this, IntermediateField.coe_sum]
        rfl
      rw [hz', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hσ₀b i]
    refine ⟨?_, (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσM⟩
    show decomp p σ ∈ Hq
    exact ⟨σ₀', hF' hσ₀F, hσ₀⟩
  have hHopen : IsOpen (H : Set (GQp p)) :=
    Subgroup.isOpen_mono hE₀H (IntermediateField.fixingSubgroup_isOpen E₀)
  have hHclosed : IsClosed (H : Set (GQp p)) := Subgroup.isClosed_of_isOpen H hHopen
  let E : Fld p := IntermediateField.fixedField H
  have hEH : E.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  -- the index
  have hmapLe : GM.map (decomp p) ≤ ρL.range := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [hrange]
    exact hdecL σ ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ)
  have hrel1 : Hq.relIndex ρL.range = Stab.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hρinj,
      Subgroup.relIndex_top_right]
  have hrel2 : Hq.relIndex (GM.map (decomp p)) ≤ Stab.index := by
    rw [← hrel1]
    exact Subgroup.relIndex_le_of_le_right hmapLe (by rw [hrel1]; exact hidx0)
  have hrel3 : Hq.relIndex (GM.map (decomp p)) ≠ 0 := fun h0 =>
    hidx0 (hrel1 ▸ Subgroup.relIndex_eq_zero_of_le_right hmapLe h0)
  have hHidx : H.index = (Hq.comap (decomp p)).relIndex GM * GM.index := Subgroup.index_inf
  rw [Subgroup.relIndex_comap] at hHidx
  have hMfr : Module.finrank ℚ_[p] M = GM.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) M
  have hEfr : Module.finrank ℚ_[p] E = H.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) E, hEH]
  have hMpos : 0 < Module.finrank ℚ_[p] M := Module.finrank_pos
  have hEpos : 0 < Module.finrank ℚ_[p] E := by
    rw [hEfr, hHidx]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hrel3) (hMfr ▸ hMpos)
  refine ⟨E, Module.finite_of_finrank_pos hEpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (Subgroup.mem_inf.mp hτ).2 x hx
  · rw [hEfr, hHidx, hMfr]
    exact Nat.mul_le_mul_right _ (hrel2.trans hidx)
  · intro σ hσ σ' hσ' n P hP
    have hσE : σ ∈ E.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ.1
    rw [hEH] at hσE
    obtain ⟨σ₀, hσ₀S, hσ₀⟩ := (Subgroup.mem_inf.mp hσE).1
    have hσ₀' : G0Galois.resQ L σ₀ = decomp p σ := hσ₀
    have hR := raynaudPlace_of_R6 (p := p) hR6 hTors A₀ hdim₀ hq3 hpq'
    set Q := φ.symm P with hQdef
    have hQ : Q ^ (ℓ ^ n) = 1 := by rw [hQdef, ← map_pow, hP, map_one]
    have hu := hR σ hσ.2 σ₀ hσ₀' (fun R hR' => hσ₀S R hR') ℓ Fact.out hℓp n Q hQ
    obtain ⟨a, ha⟩ := wildIter (p := p) A₀ σ hσ.2 σ₀ hσ₀' Q
    have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
      Nat.Coprime.pow a n ((Nat.coprime_primes hp Fact.out).mpr (Ne.symm hℓp))
    have hfix := fixed_of_unipSq_of_iterate' A₀ σ₀ Q ℓ n p a hcop hQ hu ha
    have h1 := hφ σ₀ σ' (hσ₀'.trans hσ'.symm) Q
    rw [hfix, hQdef, MulEquiv.apply_symm_apply] at h1
    exact h1.symm

/-- `|GL₄(𝔽₅)| = G₀ = 116064000000` (proved). -/
theorem card_GL4_five :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 5)) = ZInQ.heightG0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  unfold ZInQ.heightG0
  norm_num

/-- **`TorsFixWildOdd` at every `p ≠ ℓ` (proved)** from the leaves R6, I2-Tors and the glue
`DescentPts`: `torsFix_of_descent` with `M = L_v` and `q = 3` (`q = 5` if `p = 3`);
`|GL₄(𝔽₃)| = 24261120 ≤ G₀` and `|GL₄(𝔽₅)| = G₀` (Glazer's `E = L_v(A_L[3])`, resp. `A_L[5]`). -/
theorem torsFixWildOdd_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : TorsFixWildOdd (p := p) A ℓ L := by
  obtain ⟨hLvfd, -⟩ := Lv_fin (p := p) L
  haveI := hLvfd
  have key : ∃ q : ℕ, ∃ _ : Fact q.Prime, 3 ≤ q ∧ q ≠ p ∧
      Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) ≤ ZInQ.heightG0 := by
    by_cases h3 : p = 3
    · exact ⟨5, ⟨by norm_num⟩, by norm_num, by omega, card_GL4_five.le⟩
    · refine ⟨3, ⟨by norm_num⟩, le_refl _, Ne.symm h3, ?_⟩
      rw [card_GL4_three]
      unfold ZInQ.heightG0
      norm_num
  obtain ⟨q, hq, hq3, hqp, hqN⟩ := key
  obtain ⟨E, hEfd, hLvE, hdeg, hfix⟩ :=
    torsFix_of_descent hR6 hTors hD hℓp q hq3 hqp (Lv (p := p) L) le_rfl
  exact ⟨E, hEfd, hLvE, hdeg.trans (Nat.mul_le_mul_right _ hqN), hfix⟩

/-- **`TorsFixWildE` from `BetaTwist2` (proved; used at `p = 2`, valid for `p ≠ 3`)**:
`torsFix_of_descent` with `q = 3` over `BetaTwist2`'s `M`; `4·|GL₄(𝔽₃)| ≤ G₀`. -/
theorem torsFixWildE_of_twist (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hp3 : p ≠ 3) {β : GQ → PadicAlgCl ℓ}
    (hB : BetaTwist2 (p := p) β L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨M, hMfd, hLvM, hMdeg, hMβ⟩ := hB
  haveI := hMfd
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨E, hEfd, hME, hdeg, hfix⟩ :=
    torsFix_of_descent hR6 hTors hD hℓp 3 le_rfl (Ne.symm hp3) M hLvM
  refine ⟨E, hEfd, hLvM.trans hME, ?_, fun σ hσ =>
    ⟨hMβ σ ⟨fun x hx => hσ.1 x (hME hx), hσ.2⟩, hfix σ hσ⟩⟩
  rw [card_GL4_three] at hdeg
  calc Module.finrank ℚ_[p] E ≤ 24261120 * Module.finrank ℚ_[p] M := hdeg
    _ ≤ 24261120 * (4 * Module.finrank ℚ_[p] (Lv (p := p) L)) := Nat.mul_le_mul_left _ hMdeg
    _ = 97044480 * Module.finrank ℚ_[p] (Lv (p := p) L) := by ring
    _ ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) :=
        Nat.mul_le_mul_right _ (by unfold ZInQ.heightG0; norm_num)

/-- **`TateWildKE` at every `p ≠ ℓ` (proved)** from R6, I2-Tors, `DescentPts`, G7's clauses and,
at `p = 2`, `BetaTwist2`. -/
theorem tateWildKE_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]
    {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hC : G7Clauses β ε L)
    (hD : DescentPts A L) (hℓp : ℓ ≠ p) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    TateWildKE (p := p) A ℓ β L := by
  by_cases h2 : p = 2
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_twist hR6 hTors hD hℓp (by omega) (hB h2))
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_odd h2 hC (torsFixWildOdd_of_descent hR6 hTors hD hℓp))

/-- **`LocalGlue p Tm a β L` on G7's data (proved)** from the leaves R6 and I2-Tors and the glue
`KerWild` (all `p`), `DescentPts` (`p ≤ 5`) and `BetaTwist2` (`p = 2`). -/
theorem localGlue_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L] (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hD : p ≤ 5 → DescentPts A L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_leaves hR6 hTors hpℓ h7 hC hK
    (fun h5 => tateWildKE_of_descent hR6 hTors hC (hD h5) (Ne.symm hpℓ) hB) hB

/-- **`KerWild` from G7Data's kernel-field clause (proved).** If `L'` is finite Galois,
`G_{L'} = G_L ∩ ker β_ℂ` (g0-mod-field `G7Data`/`G7Out`: `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`, with
`GQL L = L.fixingSubgroup`), and the `ℚ̄_ℓ`-valued `β` is `ι ∘ β_ℂ` for an injective
`ι : ℂ^× →* ℚ̄_ℓ^×`, then `KerWild L' β L` for G7Out's model field `K = L'`. This is the clause that
g0-assemble's `TateBridge` must add to its output (finding G8). -/
theorem kerWild_of_g7Data {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (βC : GQ → ℂˣ)
    (hker : ∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC) {β : GQ → PadicAlgCl ℓ}
    (hβ : ∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ)) : KerWild L' β L := by
  intro g hgL hg1
  have h1 : ιC (βC g) = ιC 1 := by
    rw [map_one]
    exact Units.ext (by rw [Units.val_one, ← hβ g, hg1])
  have h2 : βC g = 1 := hι h1
  have h3 : g ∈ L'.fixingSubgroup :=
    (hker g).mpr ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hgL, h2⟩
  rw [RQ.resQ_range L']
  exact h3

end DescentSec

end G15Ram

end


/-! ## §7e (local-glue). `BetaTwist2` from an unramified fourth root (proved)

`BetaTwist2 β L` (§7, `p = 2`) is reduced to two smaller Props:
* `Beta4Inertia β L` (GLUE on G7's `β² = ι ∘ χ`): `β⁴ = 1` on the inertia subgroup of `G_{L_v}`;
* `UnramRoots p ℓ` (GLUE, textbook: `G_F/I_F ≅ Ẑ` is topologically generated by a Frobenius and
  `F` has an unramified extension of every degree; Serre, *Local Fields*, Ch. III §5 and IV §2,
  locators UNVERIFIED): a continuous character of `G_F` trivial on inertia has an unramified
  continuous fourth root.
`betaTwist2_of_roots` (proved): `M` is the fixed field of `{σ ∈ G_{L_v} : β(σ) = η(σ)}`, the kernel
of the character `β/η` with values in `μ₄(ℚ̄_ℓ)`, so `[M:L_v] ≤ 4`, and `β = η = 1` on wild inertia
of `G_M`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond

section TwistSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Glue on G7's clauses at `p = 2` (N5 L826-833).** `β⁴ = 1` on the inertia subgroup of
`G_{L_v}` (`inertiaSet` is the inertia subgroup of `G_{ℚ_p}`). Proof plan: on `G_{L_v}`,
`β⁴ = ι ∘ χ²` (G7: `β² = ι ∘ galChar χ`), with `χ` mod `N = chiLevel T₋`, `N = 4^a N'`, `N'` odd
squarefree, `a ≤ 1`; inertia at `2` fixes the roots of unity of odd order (they are unramified:
distinct `N'`-th roots of unity are at distance `1`), so `cyc_N(σ) ∈ (ℤ/4)^× × {1}`, of exponent
`2`, and `χ² (cyc_N σ) = 1`. -/
def Beta4Inertia (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ σ ∈ fixSet (Lv (p := p) L) ∩ inertiaSet, β (decomp p σ) ^ 4 = 1

variable (p ℓ) in
/-- **Glue (textbook; Serre, *Local Fields*, Ch. III §5 and Ch. IV §2, locators UNVERIFIED): an
unramified fourth root.** For a finite `F/ℚ_p` and a character `ψ` of `G_F` with values in
`ℚ̄_ℓ^×` that is trivial on some open `G_{F''}` and on the inertia subgroup `G_F ∩ I`, there is a
character `η` of `G_F`, trivial on some open `G_{F₁}` and on `G_F ∩ I`, with `η⁴ = ψ` on `G_F`.
(`ψ` factors through `Gal(F_m/F) ≅ ℤ/m`, `F_m` unramified of degree `m`, generated by Frobenius;
take `ξ` with `ξ⁴ = ψ(Frob)`, of order `d ∣ 4m`, and `η(σ) = ξ^k` for `σ|_{F_d} = Frob^k`.) -/
def UnramRoots : Prop :=
  ∀ (F : Fld p), FiniteDimensional ℚ_[p] F → ∀ ψ : GQp p → PadicAlgCl ℓ,
    (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, ψ (σ * τ) = ψ σ * ψ τ) →
    (∃ F'' : Fld p, FiniteDimensional ℚ_[p] F'' ∧ ∀ σ ∈ fixSet F'', ψ σ = 1) →
    (∀ σ ∈ fixSet F ∩ inertiaSet, ψ σ = 1) →
    ∃ η : GQp p → PadicAlgCl ℓ,
      (∃ F₁ : Fld p, FiniteDimensional ℚ_[p] F₁ ∧ ∀ σ ∈ fixSet F₁, η σ = 1) ∧
      (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, η (σ * τ) = η σ * η τ) ∧
      (∀ σ ∈ fixSet F, η σ ^ 4 = ψ σ) ∧
      (∀ σ ∈ fixSet F ∩ inertiaSet, η σ = 1)

/-- **`BetaTwist2` from G7's clauses, `Beta4Inertia` and `UnramRoots` (proved).** -/
theorem betaTwist2_of_roots {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L) (hU : UnramRoots p ℓ)
    (h4 : Beta4Inertia (p := p) β L) : BetaTwist2 (p := p) β L := by
  haveI : FiniteDimensional ℚ L := hC.1
  obtain ⟨hFfd, -⟩ := Lv_fin (p := p) L
  set F : Fld p := Lv (p := p) L with hFdef
  haveI := hFfd
  have hLF : ∀ x ∈ L, embP x ∈ F := fun x hx => embP_mem_Lv hx
  have hmul : BetaCharOn (p := p) β F := betaCharOn_of_cocycle hC.2.2.1 hC.2.2.2.2.2.2 hLF
  have hβ0 : ∀ g, β g ≠ 0 := hC.2.2.2.1
  have hβ1 : β 1 = 1 := by
    have h := hC.2.2.1 1 1
    rw [hC.2.2.2.2.2.2 1 1 (fun _ _ => rfl) (fun _ _ => rfl), one_mul, mul_one] at h
    exact (mul_right_eq_self₀.mp h).resolve_right (hβ0 1)
  obtain ⟨F', hF'gal, hF'⟩ := betaOpen_of_isLocallyConstant (p := p) hC.2.2.2.2.1 hβ1
  haveI : FiniteDimensional ℚ_[p] F' := hF'gal.1
  -- the fourth root
  obtain ⟨η, ⟨F₁, hF₁fd, hF₁⟩, hηmul, hη4, hηI⟩ := hU F hFfd (fun σ => β (decomp p σ) ^ 4)
    (fun σ hσ τ hτ => by beta_reduce; rw [hmul σ hσ τ hτ, mul_pow])
    ⟨F', hF'gal.1, fun σ hσ => by beta_reduce; rw [hF' σ hσ, one_pow]⟩ h4
  haveI := hF₁fd
  have hη0 : ∀ σ ∈ fixSet F, η σ ≠ 0 := fun σ hσ h0 => by
    have := hη4 σ hσ
    rw [h0, zero_pow (by norm_num)] at this
    exact pow_ne_zero 4 (hβ0 _) this.symm
  have h1F : (1 : GQp p) ∈ fixSet F := fun _ _ => rfl
  have hη1 : η 1 = 1 := by
    have h := hηmul 1 h1F 1 h1F
    rw [mul_one] at h
    exact ((mul_right_eq_self₀.mp h.symm).resolve_right (hη0 1 h1F))
  have hβd1 : β (decomp p 1) = 1 := by rw [map_one]; exact hβ1
  have hinvF : ∀ σ ∈ fixSet F, σ⁻¹ ∈ fixSet F := fun σ hσ x hx => by
    conv_lhs => rw [← hσ x hx]
    exact σ.symm_apply_apply x
  have hmulF : ∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, σ * τ ∈ fixSet F := fun σ hσ τ hτ x hx => by
    show σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  -- the subgroup `U = {σ ∈ G_F : β σ = η σ}`
  let U : Subgroup (GQp p) :=
    { carrier := {σ | σ ∈ fixSet F ∧ β (decomp p σ) = η σ}
      mul_mem' := fun {σ τ} hσ hτ => ⟨hmulF σ hσ.1 τ hτ.1, by
        rw [hmul σ hσ.1 τ hτ.1, hηmul σ hσ.1 τ hτ.1, hσ.2, hτ.2]⟩
      one_mem' := ⟨h1F, by rw [hβd1, hη1]⟩
      inv_mem' := fun {σ} hσ => ⟨hinvF σ hσ.1, by
        have hb := hmul σ⁻¹ (hinvF σ hσ.1) σ hσ.1
        have he := hηmul σ⁻¹ (hinvF σ hσ.1) σ hσ.1
        rw [inv_mul_cancel, hβd1] at hb
        rw [inv_mul_cancel, hη1] at he
        rw [hσ.2] at hb
        have hne := hη0 σ hσ.1
        calc β (decomp p σ⁻¹) = β (decomp p σ⁻¹) * η σ * (η σ)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
          _ = η σ⁻¹ * η σ * (η σ)⁻¹ := by rw [← hb, he]
          _ = η σ⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]⟩ }
  let GF : Subgroup (GQp p) := F.fixingSubgroup
  have hmemGF : ∀ σ : GQp p, σ ∈ GF ↔ σ ∈ fixSet F := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  have hUGF : U ≤ GF := fun σ hσ => (hmemGF σ).mpr hσ.1
  -- the character `β/η : G_F → μ₄`
  let f : GF →* (PadicAlgCl ℓ)ˣ :=
    { toFun := fun σ => Units.mk0 (β (decomp p σ.1) * (η σ.1)⁻¹)
        (mul_ne_zero (hβ0 _) (inv_ne_zero (hη0 _ ((hmemGF _).mp σ.2))))
      map_one' := by
        ext
        show β (decomp p 1) * (η 1)⁻¹ = 1
        rw [hβd1, hη1, inv_one, mul_one]
      map_mul' := fun σ τ => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
        rw [hmul σ.1 ((hmemGF _).mp σ.2) τ.1 ((hmemGF _).mp τ.2),
          hηmul σ.1 ((hmemGF _).mp σ.2) τ.1 ((hmemGF _).mp τ.2), mul_inv]
        ring }
  have hker : U.subgroupOf GF = f.ker := by
    ext σ
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have hσF := (hmemGF _).mp σ.2
    constructor
    · intro h
      ext
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one]
      rw [h.2, mul_inv_cancel₀ (hη0 _ hσF)]
    · intro h
      refine ⟨hσF, ?_⟩
      have h' := congrArg Units.val h
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one] at h'
      have hne := hη0 _ hσF
      calc β (decomp p σ.1) = β (decomp p σ.1) * (η σ.1)⁻¹ * η σ.1 := by
            rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
        _ = η σ.1 := by rw [h', one_mul]
  have hrange : f.range ≤ rootsOfUnity 4 (PadicAlgCl ℓ) := by
    rintro _ ⟨σ, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    have hσF := (hmemGF _).mp σ.2
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_pow_eq_pow_val, Units.val_mk0,
      Units.val_one]
    rw [mul_pow, inv_pow, ← hη4 _ hσF, mul_inv_cancel₀ (pow_ne_zero 4 (hη0 _ hσF))]
  have hrel : U.relIndex GF ≤ 4 := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity _ _)
  have hrel0 : U.relIndex GF ≠ 0 := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    haveI : Finite f.range :=
      Finite.of_injective (Subgroup.inclusion hrange) (Subgroup.inclusion_injective hrange)
    exact Nat.card_pos.ne'
  -- `U` is open: it contains `G_{F ⊔ F' ⊔ F₁}`
  let E₀ : Fld p := F ⊔ F' ⊔ F₁
  have hE₀U : E₀.fixingSubgroup ≤ U := by
    intro σ hσ
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
    have hσF : σ ∈ fixSet F := fun x hx => hσ' x ((show F ≤ E₀ from le_sup_left.trans le_sup_left) hx)
    have hσF' : σ ∈ fixSet F' := fun x hx => hσ' x ((show F' ≤ E₀ from le_sup_right.trans le_sup_left) hx)
    have hσF₁ : σ ∈ fixSet F₁ := fun x hx => hσ' x ((show F₁ ≤ E₀ from le_sup_right) hx)
    exact ⟨hσF, by rw [hF' σ hσF', hF₁ σ hσF₁]⟩
  have hUopen : IsOpen (U : Set (GQp p)) :=
    Subgroup.isOpen_mono hE₀U (IntermediateField.fixingSubgroup_isOpen E₀)
  have hUclosed : IsClosed (U : Set (GQp p)) := Subgroup.isClosed_of_isOpen U hUopen
  let M : Fld p := IntermediateField.fixedField U
  have hMU : M.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUclosed⟩
  have hMfr : Module.finrank ℚ_[p] M = U.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) M, hMU]
  have hFfr : Module.finrank ℚ_[p] F = GF.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) F
  have hUidx : U.index = U.relIndex GF * GF.index := (Subgroup.relIndex_mul_index hUGF).symm
  have hFpos : 0 < Module.finrank ℚ_[p] F := Module.finrank_pos
  have hMpos : 0 < Module.finrank ℚ_[p] M := by
    rw [hMfr, hUidx]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hrel0) (hFfr ▸ hFpos)
  refine ⟨M, Module.finite_of_finrank_pos hMpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact hτ.1 x hx
  · rw [hMfr, hUidx, ← hFfr]
    exact Nat.mul_le_mul_right _ hrel
  · intro σ hσ
    have hσM : σ ∈ M.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ.1
    rw [hMU] at hσM
    rw [hσM.2]
    exact hηI σ ⟨hσM.1, wildSet_subset_inertiaSet hσ.2⟩

/-! ### `Beta4Inertia` at `p = 2` from G7's clauses (proved) -/

/-- Inertia fixes the roots of unity of order prime to `p` (proved; as `wild_fix_prime_to_p`). -/
theorem inertia_fix_prime_to_p {σ : GQp p} (hσ : σ ∈ inertiaSet) {ζ : Kbar p} {m : ℕ}
    (hm0 : 0 < m) (hpm : ¬ p ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0.ne'] at hζ; exact zero_ne_one hζ
  have h1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hm0 hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηm : η ^ m = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : ‖η - 1‖ < 1 := by
    have he : η - 1 = (σ ζ - ζ) * ζ⁻¹ := by rw [hη, sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, norm_mul, norm_inv, h1, inv_one, mul_one]
    exact hσ ζ h1.le
  have := eq_one_of_pow_eq_one_of_norm_lt hm0 hpm hηm hlt
  rw [hη, mul_inv_eq_one₀ hζ0] at this
  exact this

/-- `σ²` fixes the fourth roots of unity (proved): `σ(i) = ±i`. -/
theorem sq_fix_four (σ : GQp p) {ζ : Kbar p} (hζ : ζ ^ 4 = 1) : σ (σ ζ) = ζ := by
  have h2 : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 := by linear_combination hζ
  rcases mul_eq_zero.mp h2 with h | h
  · have h' : (ζ - 1) * (ζ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · rw [sub_eq_zero.mp h1, map_one, map_one]
    · rw [eq_neg_of_add_eq_zero_left h1]
      simp
  · have hτ : (σ ζ - ζ) * (σ ζ + ζ) = 0 := by
      have e2 : σ ζ ^ 2 = ζ ^ 2 := by
        have e1 : ζ ^ 2 = -1 := by linear_combination h
        rw [← map_pow, e1, map_neg, map_one]
      linear_combination e2
    rcases mul_eq_zero.mp hτ with h1 | h1
    · rw [sub_eq_zero.mp h1, sub_eq_zero.mp h1]
    · have e : σ ζ = -ζ := eq_neg_of_add_eq_zero_left h1
      rw [e, map_neg, e, neg_neg]

/-- `chiLevel T₋ ∣ 4M` with `M` odd (proved; `lev 2 = 4`, `lev q = q` for odd `q`). -/
theorem chiLevel_dvd_four_mul_odd {Tm : Finset ℕ} (hTm : ∀ q ∈ Tm, q.Prime) :
    ∃ M : ℕ, ¬ 2 ∣ M ∧ GlueDescent.chiLevel Tm ∣ 4 * M := by
  refine ⟨∏ q ∈ Tm.erase 2, GlueDescent.lev q, ?_, ?_⟩
  · refine Finset.prod_induction _ (fun n => ¬ 2 ∣ n) (fun a b ha hb h => ?_) (by norm_num)
      (fun q hq => ?_)
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
      · exact ha h
      · exact hb h
    · have hq2 : q ≠ 2 := Finset.ne_of_mem_erase hq
      have hqp := hTm q (Finset.mem_of_mem_erase hq)
      unfold GlueDescent.lev
      rw [if_neg hq2]
      intro h
      rcases (Nat.Prime.eq_one_or_self_of_dvd hqp 2 h) with h' | h'
      · omega
      · exact hq2 h'.symm
  · by_cases h2 : 2 ∈ Tm
    · unfold GlueDescent.chiLevel
      rw [← Finset.mul_prod_erase Tm GlueDescent.lev h2]
      unfold GlueDescent.lev
      rw [if_pos rfl]
    · unfold GlueDescent.chiLevel
      rw [Finset.erase_eq_self.mpr h2]
      exact dvd_mul_left _ _

/-- At `p = 2`, `decomp(σ²)` fixes the `4M`-th roots of unity for inertia `σ`, `M` odd (proved). -/
theorem decomp_sq_fix_root (hp2 : p = 2) {σ : GQp p} (hσ : σ ∈ inertiaSet) {M : ℕ}
    (hM : ¬ 2 ∣ M) {x : PkgI4.Qbar} (hx : x ^ (4 * M) = 1) : decomp p (σ * σ) x = x := by
  apply (embP (p := p)).injective
  rw [decomp_spec]
  set ζ := embP (p := p) x
  have hζ : ζ ^ (4 * M) = 1 := by rw [← map_pow, hx, map_one]
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hM (dvd_zero 2))
  have hζ0 : ζ ≠ 0 := by
    rintro h0; rw [h0, zero_pow (by omega)] at hζ; exact zero_ne_one hζ
  have hpM : ¬ p ∣ M := hp2 ▸ hM
  have hy : σ (ζ ^ 4) = ζ ^ 4 := inertia_fix_prime_to_p hσ hM0 hpM (by rw [← pow_mul, hζ])
  have hz : σ (σ (ζ ^ M)) = ζ ^ M := sq_fix_four σ (by rw [← pow_mul, mul_comm, hζ])
  have hcop : Nat.Coprime 4 M := by
    have := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hM)
    norm_num at this
    exact this
  have hb : ((Nat.gcd 4 M : ℕ) : ℤ) = 4 * Nat.gcdA 4 M + M * Nat.gcdB 4 M := Nat.gcd_eq_gcd_ab 4 M
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have hdec : ζ = (ζ ^ 4) ^ (Nat.gcdA 4 M) * (ζ ^ M) ^ (Nat.gcdB 4 M) := by
    have hb' : ((4 : ℕ) : ℤ) * Nat.gcdA 4 M + (M : ℤ) * Nat.gcdB 4 M = 1 := by
      exact_mod_cast hb.symm
    rw [← zpow_natCast ζ 4, ← zpow_natCast ζ M, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, hb',
      zpow_one]
  show σ (σ ζ) = ζ
  rw [hdec, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_zpow₀, hz, hy, hy]

/-- At `p = 2`, the cyclotomic character mod `N ∣ 4M` (`M` odd) kills `decomp(σ²)` for inertia
`σ` (proved; as `cyc_decomp_wild`). -/
theorem cyc_decomp_sq_inertia (hp2 : p = 2) {σ : GQp p} (hσ : σ ∈ inertiaSet) {N M : ℕ}
    [NeZero N] (hM : ¬ 2 ∣ M) (hNM : N ∣ 4 * M) :
    GlueDescent.B2Q.cyc N (decomp p (σ * σ)) = 1 := by
  by_cases hN1 : N = 1
  · subst hN1; exact Subsingleton.elim _ _
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : Fact (1 < N) := ⟨by omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  obtain ⟨k, hk⟩ := hNM
  have hu := modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (GlueDescent.B2Q.toRingAut (decomp p (σ * σ))) (c := 1) (fun t ht => by
      rw [ZMod.val_one, pow_one]
      have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      exact decomp_sq_fix_root hp2 hσ hM (by rw [hk, pow_mul, htN, one_pow]))
  have hc : GlueDescent.B2Q.cyc N (decomp p (σ * σ)) = modularCyclotomicCharacter
      (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (GlueDescent.B2Q.toRingAut (decomp p (σ * σ))) := rfl
  rw [hc, Units.val_one]
  exact hu.symm

/-- **`Beta4Inertia` at `p = 2` from G7's clauses (proved).** `β⁴ = ι(χ(cyc_N σ))² =
ι(χ(cyc_N σ²))`, and `cyc_N(σ²) = 1` (`cyc_decomp_sq_inertia`, `chiLevel_dvd_four_mul_odd`). -/
theorem beta4Inertia_of_clauses (hp2 : p = 2) {β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) : Beta4Inertia (p := p) β L := by
  intro σ hσ
  obtain ⟨Tmin, hTmin, hNZ, χ, ι, hβχ⟩ := hC.2.2.2.2.2.1
  obtain ⟨M, hM, hNM⟩ := chiLevel_dvd_four_mul_odd hTmin
  have hc := cyc_decomp_sq_inertia hp2 hσ.2 hM hNM
  have h2 : (GlueDescent.B2Q.galChar χ (decomp p σ)) ^ 2 = 1 := by
    have hd : (GlueDescent.B2Q.galChar χ) (decomp p (σ * σ)) = 1 := by
      change χ.toUnitHom (GlueDescent.B2Q.cyc _ (decomp p (σ * σ))) = 1
      rw [hc, map_one]
    have hm := map_mul (GlueDescent.B2Q.galChar χ) (decomp p σ) (decomp p σ)
    rw [sq]
    refine hm.symm.trans ?_
    refine Eq.trans ?_ hd
    exact congrArg (⇑(GlueDescent.B2Q.galChar χ)) (map_mul (decomp p) σ σ).symm
  calc β (decomp p σ) ^ 4 = (β (decomp p σ) ^ 2) ^ 2 := by ring
    _ = ((ι (GlueDescent.B2Q.galChar χ (decomp p σ)) : PadicAlgCl ℓ)) ^ 2 := by rw [hβχ]
    _ = ((ι (GlueDescent.B2Q.galChar χ (decomp p σ) ^ 2) : PadicAlgCl ℓ)) := by
        rw [map_pow, Units.val_pow_eq_pow_val]
    _ = 1 := by rw [h2, map_one, Units.val_one]

/-- **`BetaTwist2` at `p = 2` from G7's clauses and the textbook Prop `UnramRoots` (proved).** -/
theorem betaTwist2_of_unramRoots (hp2 : p = 2) {β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hU : UnramRoots p ℓ) : BetaTwist2 (p := p) β L :=
  betaTwist2_of_roots hC hU (beta4Inertia_of_clauses hp2 hC)

variable {K : Type} [Field K] [NumberField K]

/-- **`LocalGlue p Tm a β L` on G7's data (proved)** from the leaves R6 and I2-Tors, the textbook
Prop `UnramRoots` (used at `p = 2`), and the glue `KerWild` (all `p`) and `DescentPts` (`p ≤ 5`). -/
theorem localGlue_of_unramRoots (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L] (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hD : p ≤ 5 → DescentPts A L) : LocalGlue (p := p) Tm a β L :=
  localGlue_of_descent hR6 hTors hpℓ h7 hC hK hD (fun h2 => betaTwist2_of_unramRoots h2 hC hU)

end TwistSec

end G15Ram

end


/-! ## §7f (local-glue). `DescentPts` for a base change (proved)

For `L ≤ L'` finite inside `ℚ̄`, `L/ℚ` Galois, and `A₀ : AbVar L` of dimension `2`,
`DescentPts (A₀)_{L'} L` holds (`descentPts_baseChange`), with `(A₀)_{L'}` the base change along
g0-mod-field's `incAlg` (as in g0-assemble's `TateBridge`). The model is the conjugate
`A₁ = A₀ ×_{L,γ} L`, where `γ ∈ Aut(L)` corrects the difference between the embeddings `L ↪ ℚ̄`
that Mathlib chooses inside `resQ L` and inside `resQ L'` (`jL L`, `jL' hLL'`; both have image
`L` since `L/ℚ` is normal). Points: `A₁(L̄) ≅ A₀(L̄_tw) ≅ A₀(L̄') ≅ (A₀)_{L'}(L̄')` by `bcPt`,
`trPt` along `θ = qEmb_{L'} ∘ qEmb_L⁻¹` (`L`-linear for the twisted structure `tw`), and `bcPt`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQ)
open CategoryTheory AlgebraicGeometry Limits MonObj

section BCDescentSec

attribute [local instance] RQ.numberField_of_fd

/-- `qEmb K` as a ring isomorphism `ℚ̄ ≃ K̄`. -/
def qEquiv (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

theorem qEquiv_apply (K : Type) [Field K] [NumberField K] (x : AlgebraicClosure ℚ) :
    qEquiv K x = G0Galois.qEmbRing K x := rfl

/-- The embedding `K ↪ ℚ̄` inside `resQ K`. -/
def jK (K : Type) [Field K] [NumberField K] : K →ₐ[ℚ] AlgebraicClosure ℚ :=
  ((qEquiv K).symm.toRingHom.comp (algebraMap K (AlgebraicClosure K))).toRatAlgHom

theorem qEquiv_jK (K : Type) [Field K] [NumberField K] (x : K) :
    qEquiv K (jK K x) = algebraMap K (AlgebraicClosure K) x := by
  show qEquiv K ((qEquiv K).symm _) = _
  exact (qEquiv K).apply_symm_apply _

variable {L L' : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
  [FiniteDimensional ℚ L'] (hLL' : L ≤ L')

/-- The embedding `L ↪ L' ↪ ℚ̄` inside `resQ L'`. -/
def jL' : L →ₐ[ℚ] AlgebraicClosure ℚ := (jK L').comp (IntermediateField.inclusion hLL')

variable [IsGalois ℚ L]

theorem mem_range_jK (x : L) : jL' hLL' x ∈ (jK L).fieldRange := by
  have h1 := AlgHom.fieldRange_of_normal (jK L)
  have h2 := AlgHom.fieldRange_of_normal (jL' hLL')
  have hx : jL' hLL' x ∈ (jL' hLL').fieldRange := ⟨x, rfl⟩
  rw [h2] at hx
  rw [h1]
  exact hx

/-- `γ = jK_L⁻¹ ∘ jL'`, a ring endomorphism of `L`. -/
def γL : L →+* L :=
  (AlgEquiv.ofInjectiveField (jK L)).symm.toRingEquiv.toRingHom.comp
    ((jL' hLL').toRingHom.codRestrict (jK L).fieldRange (mem_range_jK hLL'))

theorem jK_γL (x : L) : jK L (γL hLL' x) = jL' hLL' x := by
  have h := congrArg Subtype.val
    ((AlgEquiv.ofInjectiveField (jK L)).apply_symm_apply ⟨jL' hLL' x, mem_range_jK hLL' x⟩)
  exact h

theorem γL_bijective : Function.Bijective (γL hLL') := by
  have hinj : Function.Injective (γL hLL') := (γL hLL').injective
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective
    (f := (γL hLL').toRatAlgHom.toLinearMap)).mp hinj

/-- g0-mod-field's `incAlg` (`L → L'`). -/
@[instance_reducible] def incAlgL : Algebra L L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra

/-- The `L`-algebra structure on `L` through `γ`. -/
@[instance_reducible] def γAlg : Algebra L L := (γL hLL').toAlgebra

/-- The twisted `L`-algebra structure on `L̄`: `x ↦ qEmb_L (jL' x)`. -/
@[instance_reducible] def twAlg : Algebra L (AlgebraicClosure L) :=
  ((qEquiv L).toRingHom.comp (jL' hLL').toRingHom).toAlgebra

/-- The `L`-algebra structure on `L̄'` through `L ⊆ L'`. -/
@[instance_reducible] def compAlg : Algebra L (AlgebraicClosure L') :=
  ((algebraMap L' (AlgebraicClosure L')).comp (IntermediateField.inclusion hLL').toRingHom).toAlgebra

theorem tower_tw : @IsScalarTower L L (AlgebraicClosure L) (γAlg hLL').toSMul
    Algebra.toSMul (twAlg hLL').toSMul :=
  @IsScalarTower.of_algebraMap_eq L L (AlgebraicClosure L) _ _ _ (γAlg hLL') _ (twAlg hLL')
    (fun x => by
      show qEquiv L (jL' hLL' x) = algebraMap L (AlgebraicClosure L) (γL hLL' x)
      rw [← qEquiv_jK, jK_γL])

theorem tower_comp : @IsScalarTower L L' (AlgebraicClosure L') (incAlgL hLL').toSMul
    Algebra.toSMul (compAlg hLL').toSMul :=
  @IsScalarTower.of_algebraMap_eq L L' (AlgebraicClosure L') _ _ _ (incAlgL hLL') _ (compAlg hLL')
    (fun x => rfl)

/-- `θ = qEmb_{L'} ∘ qEmb_L⁻¹ : L̄_tw ≃ L̄'`, `L`-linear. -/
def θL : @AlgEquiv L (AlgebraicClosure L) (AlgebraicClosure L') _ _ _ (twAlg hLL')
    (compAlg hLL') :=
  @AlgEquiv.ofRingEquiv L (AlgebraicClosure L) (AlgebraicClosure L') _ _ _ (twAlg hLL')
    (compAlg hLL') ((qEquiv L).symm.trans (qEquiv L')) (fun x => by
      show qEquiv L' ((qEquiv L).symm (qEquiv L (jL' hLL' x))) =
        algebraMap L' (AlgebraicClosure L') (IntermediateField.inclusion hLL' x)
      rw [RingEquiv.symm_apply_apply]
      exact qEquiv_jK L' _)

theorem θL_apply (x : AlgebraicClosure L) : θL hLL' x = qEquiv L' ((qEquiv L).symm x) := rfl

/-- `θ σ₀ = σ' θ` when `resQ_L σ₀ = resQ_{L'} σ'`. -/
theorem θL_galois (σ₀ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L')
    (h : G0Galois.resQ L σ₀ = G0Galois.resQ L' σ') (x : AlgebraicClosure L) :
    σ' (θL hLL' x) = θL hLL' (σ₀ x) := by
  obtain ⟨y, rfl⟩ := (qEquiv L).surjective x
  have hθ : ∀ z, θL hLL' (qEquiv L z) = qEquiv L' z := fun z => by
    rw [θL_apply, RingEquiv.symm_apply_apply]
  have h1 := G0Galois.resQ_spec L σ₀ y
  have h2 := G0Galois.resQ_spec L' σ' y
  calc σ' (θL hLL' (qEquiv L y)) = σ' (qEquiv L' y) := by rw [hθ]
    _ = qEquiv L' (G0Galois.resQ L' σ' y) := h2.symm
    _ = qEquiv L' (G0Galois.resQ L σ₀ y) :=
        congrArg (fun g : GQ => qEquiv L' (g y)) h.symm
    _ = θL hLL' (qEquiv L (G0Galois.resQ L σ₀ y)) := (hθ _).symm
    _ = θL hLL' (σ₀ (qEquiv L y)) := congrArg (θL hLL') h1

/-- The conjugate model `A₁ = A₀ ×_{L,γ} L`. -/
abbrev conjModel (A₀ : PkgI3.AbVar L) : PkgI3.AbVar L :=
  @PkgI3.AbVar.baseChange L _ A₀ L _ (γAlg hLL')

/-- The base change `(A₀)_{L'}` along `incAlg` (as in `TateBridge`). -/
abbrev bcL' (A₀ : PkgI3.AbVar L) : PkgI3.AbVar L' :=
  @PkgI3.AbVar.baseChange L _ A₀ L' _ (incAlgL hLL')

/-- `φ : A₁(L̄) ≅ A₀(L̄_tw) ≅ A₀(L̄') ≅ (A₀)_{L'}(L̄')`. -/
def φL (A₀ : PkgI3.AbVar L) :
    (conjModel hLL' A₀).Pt (AlgebraicClosure L) ≃* (bcL' hLL' A₀).Pt (AlgebraicClosure L') :=
  ((@UnramTate.bcPt L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _ (twAlg hLL')
      (tower_tw hLL')).trans
    (@UnramTate.trPt L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
      (compAlg hLL') (θL hLL'))).trans
    (@UnramTate.bcPt L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _ (compAlg hLL')
      (tower_comp hLL')).symm

/-- `φ` intertwines `σ₀ ∈ G_L` and `σ' ∈ G_{L'}` with the same image in `G_ℚ` (proved). -/
theorem φL_galAct (A₀ : PkgI3.AbVar L) (σ₀ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L')
    (h : G0Galois.resQ L σ₀ = G0Galois.resQ L' σ')
    (P : (conjModel hLL' A₀).Pt (AlgebraicClosure L)) :
    φL hLL' A₀ ((conjModel hLL' A₀).galAct σ₀ P) =
      (bcL' hLL' A₀).galAct σ' (φL hLL' A₀ P) := by
  set b₁ := @UnramTate.bcPt L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _ (twAlg hLL')
      (tower_tw hLL') with hb₁
  set t := @UnramTate.trPt L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
      (compAlg hLL') (θL hLL') with ht
  set b₂ := @UnramTate.bcPt L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _ (compAlg hLL')
      (tower_comp hLL') with hb₂
  have e1 := @UnramTate.bcPt_galAct L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _
    (twAlg hLL') (tower_tw hLL') σ₀ P
  have e3 := @UnramTate.bcPt_galAct L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _
    (compAlg hLL') (tower_comp hLL') σ' (b₂.symm (t (b₁ P)))
  show b₂.symm (t (b₁ ((conjModel hLL' A₀).galAct σ₀ P))) =
    (bcL' hLL' A₀).galAct σ' (b₂.symm (t (b₁ P)))
  apply b₂.injective
  rw [MulEquiv.apply_symm_apply, e3, MulEquiv.apply_symm_apply]
  erw [e1]
  exact @UnramTate.trPt_galAct L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
    (compAlg hLL') (θL hLL') _ _ (fun x => θL_galois hLL' σ₀ σ' h x) (b₁ P)

/-- The conjugate model has the dimension of `A₀` (proved): base change along the isomorphism
`Spec γ` is homeomorphic to `A₀`. -/
theorem dim_conjModel (A₀ : PkgI3.AbVar L) : (conjModel hLL' A₀).dim = A₀.dim := by
  let e : L ≃+* L := RingEquiv.ofBijective (γL hLL') (γL_bijective hLL')
  have hiso : IsIso (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))) :=
    e.toCommRingCatIso.isIso_hom
  have hiso2 : IsIso (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL')))) :=
    inferInstance
  have hiso3 : IsIso (pullback.fst (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))))) := inferInstance
  show topologicalKrullDim (pullback (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))))) =
    topologicalKrullDim A₀.X.left
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph (pullback.fst (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL')))))).isHomeomorph

/-- **`DescentPts` for a base change (proved).** For `L ≤ L'` finite in `ℚ̄`, `L/ℚ` Galois, and
`A₀ : AbVar L` with `dim A₀ = 2`, `DescentPts ((A₀)_{L'}) L` holds for G7Out's model field
`K = L'`, with the conjugate model `A₀ ×_{L,γ} L`. -/
theorem descentPts_baseChange (A₀ : PkgI3.AbVar L) (hdim : A₀.dim = 2) :
    DescentPts (K := L') (bcL' hLL' A₀) L :=
  ⟨inferInstance, conjModel hLL' A₀, φL hLL' A₀, (dim_conjModel hLL' A₀).trans hdim,
    fun σ₀ σ' h P => φL_galAct hLL' A₀ σ₀ σ' h P⟩

/-- **`LocalGlue` on G7's construction (proved).** For g0-mod-field's data: `L ≤ L'` finite
Galois in `ℚ̄`, `A₀ : AbVar L` with `dim A₀ = 2`, G7Out for `(A₀)_{L'}` over `K = L'`, G7's clauses,
the kernel-field clause `G_{L'} = G_L ∩ ker β_ℂ`, and the transport `β = ι ∘ β_ℂ` with `ι`
injective, `LocalGlue p Tm a β L` holds at every `p ≠ ℓ`, from the leaves R6 and I2-Tors and the
textbook Prop `UnramRoots` (used at `p = 2`). -/
theorem localGlue_of_baseChange {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ) [IsGalois ℚ L'] (A₀ : PkgI3.AbVar L)
    (hdim₀ : A₀.dim = 2)
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    {c ε : GQ → GQ → PadicAlgCl ℓ} {a β : GQ → PadicAlgCl ℓ}
    {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    (h7 : G0Galois.G7Out (bcL' hLL' A₀) ℓ Tm c ε a β u) (hC : G7Clauses β ε L)
    (βC : GQ → ℂˣ) (hker : ∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC)
    (hβ : ∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ)) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hC (kerWild_of_g7Data βC hker ιC hι hβ)
    (fun _ => descentPts_baseChange hLL' A₀ hdim₀)

end BCDescentSec


end G15Ram

end


noncomputable section

/-! ## §8 (local-glue). The packs: G8's data with the local glue replaced by Props on `A/K`

`G8LocalPack` is copied verbatim from scratch/local-data/tail_part.lean (the hypothesis of
local-data's tail `modularConstituent_tail_L`). `G7LocalPackK` asks instead for G7's data
(`G7Out`), G8's output, the clauses, `KerWild`, and the torsion-point Props `TorsFixWild`
(`p ≥ 7`), `TorsFixWildE` (`p ≤ 5`) and `BetaUpper` (`p = 2`) at the primes in `P`. -/

namespace G0ModNewform

open PkgI4 (Qbar GQ GaloisRep)
open PkgI3

attribute [local instance] RQ.numberField_of_fd

-- BEGIN verbatim copy (scratch/local-data/tail_part.lean)
/-- **G8's data for a representation `r` at coefficient prime `ℓ`, with the G4/G7 clauses and
the local glue at the primes `p ∈ P`** (`G15Ram.G7Clauses`, `G15Ram.LocalGlue`). -/
def G8LocalPack (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (a β : GQ → PadicAlgCl ℓ)
    (ε : GQ → GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ Qbar),
    G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧ G15Ram.G7Clauses β ε L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p → @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β L

-- END verbatim copy

/-- **G7's data for `r` at coefficient prime `ℓ`, with the local glue at `p ∈ P` as Props on the
abelian surface `A/K` (GLUE).** -/
def G7LocalPackK (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (7 ≤ p → @G15Ram.TorsFixWild p ⟨hp⟩ K _ _ A ℓ _) ∧
      (p ≤ 5 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L) ∧
      (p = 2 → @G15Ram.BetaUpper p ⟨hp⟩ ℓ _ β (@G15Ram.Lv p ⟨hp⟩ L) U0)

/-- **`G8LocalPack` from `G7LocalPackK` (proved)**, by `G15Ram.localGlue_of_g7`. -/
theorem g8LocalPack_of_K {ℓ : ℕ} [Fact ℓ.Prime] {r : GaloisRep ℓ 2} {P : ℕ → Prop}
    (h : G7LocalPackK ℓ r P) : G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hE, hB⟩ := hloc p hp hP
  exact G15Ram.localGlue_of_g7 h7 hC hK (fun h => G15Ram.tateWildK_of_torsFixWild (hW h))
    (fun h => G15Ram.tateWildKE_of_torsFixWildE (hE h)) hB

/-- **G15's open Prop `G15RamG` from the packs (proved)**: g15-ram's `G15RamG D u` follows from
G7's data for `D.r5` (local glue at `p ≠ 5`) and for `D.r3` (at `p = 5`), and G11's outputs. -/
theorem g15RamG_of_packK {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (u : ℚ) (h5 : G7LocalPackK 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackK 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ := g8LocalPack_of_K h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ := g8LocalPack_of_K h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` in leaf form (GLUE).**
At `p ≥ 7` nothing: the local glue there follows from the leaves R6 and I2-Tors
(`G15Ram.raynaudPlace_of_R6`, `G15Ram.ptFinite`); at
`p ∈ {3, 5}`: `TorsFixWildOdd`; at `p = 2`: `TorsFixWildE` and `BetaTwist2` (which replaces
`BetaUpper`, `G15Ram.betaUpper_of_twist`). With the leaves R6 and
I2-Tors and `p ≠ ℓ` on `P`, it gives `G7LocalPackK` (`g7LocalPackK_of_R`). -/
def G7LocalPackR (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (3 ≤ p → p ≤ 5 → @G15Ram.TorsFixWildOdd p ⟨hp⟩ K _ _ A ℓ _ L) ∧
      (p = 2 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L ∧ @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G7LocalPackK` from `G7LocalPackR`, the leaf I2-Tors and `p ≠ ℓ` on `P` (proved).** -/
theorem g7LocalPackK_of_R (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackR ℓ r P) :
    G7LocalPackK ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hO, h2⟩ := hloc p hp hP
  refine ⟨fun h7p => ?_, fun h5 => ?_, fun h2' => G15Ram.betaUpper_of_twist hC (h2 h2').2⟩
  · exact G15Ram.torsFixWild_of_raynaud (Ne.symm (hPℓ p hP)) h7p
      (G15Ram.wildIter A) (G15Ram.torsGL_of_leaf hTors A h7.1 3 (by norm_num))
      (G15Ram.torsGL_of_leaf hTors A h7.1 7 (by norm_num))
      (fun _ => G15Ram.raynaudPlace_of_R6 hR6 hTors A h7.1 (by norm_num)
        (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
      (fun h13 => G15Ram.raynaudPlace_of_R6 hR6 hTors A h7.1 (by norm_num)
        (by rw [h13]; norm_num))
  · by_cases hp2 : p = 2
    · exact (h2 hp2).1
    · have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact G15Ram.torsFixWildE_of_odd hp2 hC (hO h3 h5)

/-- **`G15RamG` from the leaf-and-bridge packs and I2-Tors (proved).** -/
theorem g15RamG_of_packR (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackR 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackR 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u :=
  g15RamG_of_packK D u (g7LocalPackK_of_R hR6 hTors (fun _ h => h) h5)
    (g7LocalPackK_of_R hR6 hTors (fun p h => by rw [h]; norm_num) h3) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` as the glue Props of §7d (GLUE).**
`KerWild` (G7Data's kernel-field clause), and at the primes `p ∈ P`: `DescentPts A L` (the model
of `A` over `L`) when `p ≤ 5`, `BetaTwist2` when `p = 2`. Nothing at `p ≥ 7`. With the leaves R6,
I2-Tors and `p ≠ ℓ` on `P` it gives `G8LocalPack` (`g8LocalPack_of_D`). -/
def G7LocalPackD (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (p ≤ 5 → G15Ram.DescentPts A L) ∧ (p = 2 → @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G8LocalPack` from `G7LocalPackD`, the leaves R6 and I2-Tors, and `p ≠ ℓ` on `P` (proved)**,
by `G15Ram.localGlue_of_descent`. -/
theorem g8LocalPack_of_D (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackD ℓ r P) :
    G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, _, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hD, hB⟩ := hloc p hp hP
  exact G15Ram.localGlue_of_descent hR6 hTors (hPℓ p hP) h7 hC hK hD hB

/-- **`G15RamG` from the descent packs and the leaves R6, I2-Tors (proved).** -/
theorem g15RamG_of_packD (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackD 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackD 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_D hR6 hTors (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_D hR6 hTors (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` reduced to two glue Props (GLUE).**
`KerWild` (G7Data's kernel-field clause) and, when some `p ∈ P` has `p ≤ 5`, `DescentPts A L`
(the model of `A` over `L`). At `p = 2` the twist is supplied by the textbook Prop
`G15Ram.UnramRoots` (`g8LocalPack_of_U`). -/
def G7LocalPackU (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ((∃ p, P p ∧ p.Prime ∧ p ≤ 5) → G15Ram.DescentPts A L)

/-- **`G8LocalPack` from `G7LocalPackU`, the leaves R6, I2-Tors, the textbook Prop `UnramRoots`
at `p = 2`, and `p ≠ ℓ` on `P` (proved)**, by `G15Ram.localGlue_of_unramRoots`. -/
theorem g8LocalPack_of_U (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : ∀ (hp : Nat.Prime 2), @G15Ram.UnramRoots 2 ⟨hp⟩ ℓ _)
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackU ℓ r P) :
    G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, _, h7, h8, hC, hK, hD⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  refine G15Ram.localGlue_of_descent hR6 hTors (hPℓ p hP) h7 hC hK
    (fun h5 => hD ⟨p, hP, hp, h5⟩) (fun h2 => ?_)
  subst h2
  exact G15Ram.betaTwist2_of_unramRoots rfl hC (hU hp)

/-- **`G15RamG` from the packs `G7LocalPackU` (proved).** -/
theorem g15RamG_of_packU (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU2 : ∀ (hp : Nat.Prime 2) (ℓ : ℕ) [Fact ℓ.Prime],
      @G15Ram.UnramRoots 2 ⟨hp⟩ ℓ _) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackU 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackU 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_U hR6 hTors (fun hp => hU2 hp 5) (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_U hR6 hTors (fun hp => hU2 hp 3) (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` in the form of g0-mod-field's construction (GLUE: the output of an
augmented `TateBridge`).** `L ≤ L'` finite Galois in `ℚ̄`, `A₀ : AbVar L` with `dim A₀ = 2`,
G7Out and G8Out for `(A₀)_{L'}` (base change along `incAlg`), G7's clauses, the kernel-field
clause `G_{L'} = G_L ∩ ker β_ℂ` of `G7Data`, and the transport `β = ι ∘ β_ℂ` with `ι` injective.
No local Prop is asked at any prime (`g8LocalPack_of_BC`). -/
def G7LocalPackBC (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) : Prop :=
  ∃ (L L' : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L) (_ : FiniteDimensional ℚ L')
    (_ : IsGalois ℚ L) (_ : IsGalois ℚ L') (hLL' : L ≤ L') (A₀ : AbVar L)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb (G15Ram.bcL' hLL' A₀) ℓ))
    (c ε : GQ → GQ → PadicAlgCl ℓ) (a β : GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb (G15Ram.bcL' hLL' A₀) ℓ))
    (βC : GQ → ℂˣ) (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ),
    A₀.dim = 2 ∧ G0Galois.G7Out (G15Ram.bcL' hLL' A₀) ℓ Tm c ε a β u ∧
    G0Galois.G8Out (G15Ram.bcL' hLL' A₀) ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧
    (∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1) ∧
    Function.Injective ιC ∧ (∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ))

/-- **`G8LocalPack` from `G7LocalPackBC`, the leaves R6, I2-Tors and the textbook Prop
`UnramRoots` (at `p = 2`), for `p ≠ ℓ` on `P` (proved)**, by `G15Ram.localGlue_of_baseChange`. -/
theorem g8LocalPack_of_BC (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : ∀ (p : ℕ) [Fact p.Prime], G15Ram.UnramRoots p ℓ)
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackBC ℓ r) :
    G8LocalPack ℓ r P := by
  obtain ⟨L, L', _, _, _, _, hLL', A₀, Tm, c, ε, a, β, u, βC, ιC, hdim, h7, h8, hC, hker, hι,
    hβ⟩ := h
  refine ⟨L', _, RQ.numberField_of_fd L', G15Ram.bcL' hLL' A₀, Tm, a, β, ε, L, h8, hC,
    fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  exact G15Ram.localGlue_of_baseChange hLL' hR6 hTors (hU p) (hPℓ p hP) A₀ hdim h7 hC βC hker ιC
    hι hβ

/-- **`G15RamG` from the packs `G7LocalPackBC` (proved).** -/
theorem g15RamG_of_packBC (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ) {L : Type}
    [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackBC 5 D.r5) (h3 : G7LocalPackBC 3 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_BC (P := fun p => p ≠ 5) hR6 hTors (fun p _ => hU p 5) (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_BC (P := fun p => p = 5) hR6 hTors (fun p _ => hU p 3)
      (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

end G0ModNewform

end

-- END verbatim body of scratch/local-glue/LocalGlue.lean
end

section FrobTraceSec
-- BEGIN verbatim body of scratch/frob-trace/FrobTrace.lean (minus l.1632-1754, see build.sh)

/-!
# g0-mod-field: glue steps G2, G4, G7 of the H decomposition (first range of `ModularConstituent`)

Task g0-mod-field (2026-11-13). `ModularConstituent` (scratch/g0-split/Split.lean, piece 10)
covers G2, G4, G7-G16 of docs/research/h-decomposition.md §3. This file takes the range
G2 (fibre field `K`), G4 (Hom field `L`, `[L:ℚ] ≤ D`), G7 (scalar descent to `L'`,
`[L':ℚ] ≤ Q·M`), for `S = S_mul`, `R = D` (the instance `SixContactMin`).

Outputs (`def … : Prop`): `G2Out Y Φ u P` (with `RationalFibre`), `G4Out u P`, `G7Out u P`, and the clause list `G7Data`
with `G7OutUnr u P` (G7 with the twist: `L'` unramified outside `T`), for a `ℚ̄`-object `P` of
`Y₃` over `J(u)` (`FibreCtx`). The descent datum of B1 on the actual `A` is `DescentDatum`
(maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`).

Proved (no `sorry`, standard axioms):
* `g2Out_of_cover`: G2's bookkeeping (a splitting field of a separable polynomial of degree
  `≤ 324` is Galois of degree `≤ 324!`).
* `descentDatum_of_conjugacy`: B1's normalization (N5 L645-663): conjugacy isogenies with
  rational discrepancy `c` give `a_σ = |ker m_σ|^{-1/4}` and the sign cocycle `ε = sgn c`.
* `g4Out_of_kernelField`: G4's bookkeeping (Hom field `L = E ⊔ K` Galois,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D` by Minkowski's bound, model by base change, B1).
* `g7Out_of_g4Out`, `g7OutUnr_of_g4Out`: G7 = B2-B3 on the actual descent datum
  (`b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf`, `b3_of_cochain`, `degree_le_QM`) and the
  model over `L'` (`isModelOver_baseChange`, transitivity of base change).
* `fieldDescent`, `fieldDescentUnr`: the composite G2 → G4 → G7.
* `modularConstituent_of_ranges`: `ModularConstituentG` (part_split's `ModularConstituent` over
  `PkgI3.AbVar`) from this range and the next ranges bundled as `AfterG7`.

Remaining (named Props): `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4:
Weil restriction, Galois image in `GL_r(ℤ)`, inertia on the Tate module, the conjugacy isogenies
`ConjugacyData`), `UnramifiedSup` (compositum of unramified fields; STANDARD), the four B2 leaves
of glue-descent (`LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit`, `LeafUnramified`), and `AfterG7`
(G8-G16, the other two tasks).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

/-! ## The outputs of G2, G4, G7 -/

/-! ## B1's normalization (proved): from conjugacy isogenies to the sign cocycle -/

/-! ## Sanity check: `DescentDatum` is satisfiable (an abelian variety over `ℚ`, `ε = 1`) -/

/-! ## Transitivity of base change -/

/-! ## G7 from G4 (proved) -/

/-! ## G7 with the twist: `L'` unramified outside `T` (proved) -/

/-! ## G2's bookkeeping (proved) -/

/-! ## G4's bookkeeping (proved) -/

/-! ## The remaining glue as Props, and the composite -/

/-! ## How G7's output feeds `ModularConstituent` -/

/-! ## Feeding g0-mod-galois' inputs (G8-G12): their `G2Out`, `G7Out` -/

namespace GaloisCopy
/-! Copied from scratch/g0-mod-galois/part_galois.lean (branch wip/g0-mod-galois at 20fa1287),
definitions `resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, verbatim (namespace renamed). -/

end GaloisCopy

end G0ModField

/-!
# unram-tate: `TateBridge` reduced to named glue pieces

Everything above `end G0ModField` is `scratch/g0-mod-field/ModField.lean` verbatim (lines 1-1036),
so `G0ModField.TateBridge` is the statement as written there. Below: the operators
`ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` (`opV`, a ring homomorphism, proved), the quaternion matrix units
(`matrixUnits_of_quat`, copied from scratch/unram-tate/QuatUnits.lean), five named glue Props, and
the assembly `tateBridge_of_pieces` (proved).
-/

namespace UnramTate

open G0ModField

/-! ## The Tate functor on additive maps of points -/

section Ops

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

end Ops

/-! ## Matrix units (copied from scratch/unram-tate/QuatUnits.lean, proved there) -/

section Quat

open GlueDescent

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

end Quat

/-! ## The order elements `i`, `j` of `𝒪` -/

/-! ## The named glue pieces -/

/-! ## The assembly -/

set_option maxHeartbeats 1000000 in
/-! ## Proofs of two pieces -/

set_option maxHeartbeats 1000000 in
/-! ## `EndBaseChange` (proof copied from scratch/bp-qmmoduli/QMAbVar.lean L533-557, `endBC`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
end BaseChangeEnd

/-! ## `TatePoints` (generic parts copied from scratch/unram-tate/BCPoints.lean) -/

section BCPoints

open scoped CategoryTheory.Obj


end BCPoints

/-! ## `UnramifiedSup` in this context (proof copied from scratch/unram-tate/UnramSup.lean) -/

section Sup

open NumberField

end Sup

end UnramTate


/-!
# g14-trace, second file: the linked Tate bridge at `ℓ = 3, 5`

Appended to a verbatim copy of `scratch/g0-mod-field/ModField.lean` (g0-mod-field's `G7Data`,
`TateBridge`, `GaloisCopy.G7Out`). `TateBridge` gives the `ℓ`-adic data at each `ℓ` separately
(`∀ ℓ, ∃ Tm c ε' a β' uu, G7Out …`), which does not determine the traces of `r₃` against `r₅`
(g14-trace §1, `g7Out_twist`). `TateBridge35` is the linked form at `ℓ = 3, 5` that
`G14Trace.g12Spec_g14_of_galois` consumes: one pair `a, β : G_ℚ → ℚ̄` mapped to `ℚ̄₅`, `ℚ̄₃` by
embeddings `j₅`, `j₃` (TateBridge's own docstring: "mapped into `ℚ̄_ℓ` by one embedding of the
number field they generate"), and the operators `Tm_ℓ` (from one points-level `m_σ`) in the
Frobenius link at Frobenius elements. No `sorry`, no `axiom`.
-/

noncomputable section

namespace G14Bridge

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField
open GlueC10Link (FrobCompare)

/-- (copy of `G14Trace.FrobTraceLink`, over `GaloisCopy.Vb`) **The Frobenius trace link (GLUE,
AV side; N5 L781-786).** Outside a finite set `S`, at every arithmetic Frobenius `τ` above `p`,
`N·Tm_ℓ(τ)` is conjugate to `V_ℓ(α')` for one endomorphism `α'` of an abelian variety over a
field of characteristic `p`, at `ℓ = 3` and `ℓ = 5` (kernel's `GlueC10Link.FrobCompare`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (GaloisCopy.Vb A 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (GaloisCopy.Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
    PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-- **The linked Tate bridge at `ℓ = 3, 5` (GLUE; replaces the `ℓ = 3, 5` instances of
`G0ModField.TateBridge`).** From G7's data, `dim A_{L'} = 2` and `rank End = 4`: one pair
`a, β : G_ℚ → ℚ̄` (N5's `a_σ` and `β(σ)`, algebraic), embeddings `j₅ : ℚ̄ → ℚ̄₅`, `j₃ : ℚ̄ → ℚ̄₃`, and
for `ℓ = 5, 3` the operators `Tm_ℓ` (`ℚ̄_ℓ ⊗ V_ℓ(m_σ)`), `c_ℓ`, `ε_ℓ` and matrix units with
`G7Out` for the scalars `j_ℓ ∘ a`, `j_ℓ ∘ β`, `FrobTraceLink` for `Tm₅`, `Tm₃`, and `β` an
algebraic form of `G7Data`'s `β` (`ιC ∘ βQ = β`; G15 needs this `β`). `aQ` is not tied to
`DescentDatum`'s `a` in the statement (`a_σ = deg(μ_σ)^{-1/4}`, N5 L647, is algebraic), nor `Tm_ℓ` to
its `m_σ`, as in `TateBridge`; for G14 only the common `aQ` and `FrobTraceLink` matter (a joint
twist at both `ℓ` keeps the system compatible). -/
def TateBridge35 : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      ∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)

instance fact_prime_five' : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- `TateBridge35` contains the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridge` (proved): it is a
strengthening at these two primes. -/
theorem tateBridge_five_three_of_35 (h : TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    (∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β' : PkgI4.GQ → PadicAlgCl 5)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm c ε' a β' uu) ∧
    (∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a β' : PkgI4.GQ → PadicAlgCl 3)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm c ε' a β' uu) := by
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, -, -⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨⟨Tm5, c5, ε5, _, _, u5, h5⟩, ⟨Tm3, c3, ε3, _, _, u3, h3⟩⟩

end G14Bridge

end


/-!
# frob-trace: `TateBridge35` and `FrobTraceLink` (g14-trace)

Appended (by `build.sh`) to verbatim copies of `scratch/unram-tate/TateBridge.lean` (which is
`scratch/g0-mod-field/ModField.lean` L1-1036 plus unram-tate's section `UnramTate`) and of
`scratch/g14-trace/part_bridge.lean` (`G14Bridge.FrobTraceLink`, `G14Bridge.TateBridge35`).

Main result: `FrobTrace.tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree)
(hR : AlgFrobRed) : G14Bridge.TateBridge35`, through the chain of proved implications
`AlgFrobRed → AlgFrobOne → AlgFrobLink` and `tateBridge35_of_algFrobLink`. The operators are
unram-tate's `Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (one points-level `m`, one `Θ`,
one `h`), the scalars are `aQ g = βQ g / γQ(hgh⁻¹)` and `βQ` with `ιC ∘ βQ = β` in `ℚ̄` (proved,
`scalarsQbar`), and the conjunct `FrobTraceLink` for these operators is derived from the glue
Prop `AlgFrobRed` (one reduction homomorphism `A(ℚ̄) → Ā(k̄)` intertwining `f = F ∘ - ∘ Spec(σ)`
with an endomorphism of the reduction, bijective on prime-to-`p` torsion).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace FrobTrace

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-! ## The Tate functor on an additive equivalence -/

/-- `T_ℓ(Θ)` for an additive equivalence `Θ : M ≃+ N`, as a `ℤ_ℓ`-linear equivalence. -/
def tateMapEquiv (ℓ : ℕ) [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (Θ : M ≃+ N) : PkgI3.Tate.T ℓ M ≃ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ N :=
  LinearEquiv.ofLinear (PkgI3.Tate.map (ℓ := ℓ) Θ.toAddMonoidHom)
    (PkgI3.Tate.map (ℓ := ℓ) Θ.symm.toAddMonoidHom)
    (LinearMap.ext fun x => Subtype.ext (funext fun n => Θ.apply_symm_apply (x.1 n)))
    (LinearMap.ext fun x => Subtype.ext (funext fun n => Θ.symm_apply_apply (x.1 n)))

/-- Conjugation commutes with base change. -/
theorem conj_baseChange {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (f : Module.End R M) :
    (e.baseChange R A M N).conj (f.baseChange A) = (e.conj f).baseChange A := by
  rw [LinearEquiv.conj_apply, LinearEquiv.conj_apply, ← LinearEquiv.baseChange_symm,
    LinearEquiv.coe_baseChange, LinearEquiv.coe_baseChange, LinearMap.baseChange_comp,
    LinearMap.baseChange_comp]

/-! ## The glue Prop: reduction of the algebraic maps `m_σ` modulo `p` -/

/-- **`AlgFrobLink` (GLUE, AV side; Glazer N5 L777-786; reduction of abelian varieties).** Let
`A` be an abelian variety over a finite Galois `L ⊆ ℚ̄` and `m_σ` (`σ ∈ G_ℚ`) additive maps of
`A(ℚ̄)` with three of `DescentDatum`'s clauses, copied verbatim: `m_σ` is the Galois action for
`σ ∈ G_L`; `m_{σk} = m_σ m_k`, `m_{kσ} = m_k m_σ` for `k ∈ G_L`; and `m_σ` is algebraic,
`m_σ(x) = F_σ ∘ x ∘ Spec(σ)` for a finite surjective morphism of schemes `F_σ : A → A`. Then there
is a finite set `S` of primes such that, for every arithmetic Frobenius `τ` at a place `v` above
`p ∉ S` and every `g ∈ G_ℚ` (`gτg⁻¹` is an arithmetic Frobenius at `g(v)`), there are an
abelian variety `Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and
`N ≠ 0` such that for every prime `ℓ ≠ p` some `ℚ_ℓ`-isomorphism
`ℚ_ℓ ⊗ T_ℓ(A(ℚ̄)) ≅ V_ℓ(Ā)` carries `N · V_ℓ(m_{gτg⁻¹})` to `V_ℓ(α')`.

Why it is true (SPECULATIVE in its Lean details; `N = 1` works): by the first two clauses one
`F_{σ_s}` serves the whole coset `σ_s G_L`, so finitely many morphisms occur (this is the proved
step `algFrobLink_of_one`). Put `σ' = gτg⁻¹` and `w = g(v) ∩ L`, not `v ∩ L`: `σ'` lies in the
decomposition group of `g(v)`. Put in `S` the primes of bad reduction of `A` and the primes below
which some `F_{σ_s}` does not extend to the abelian scheme. For `p ∉ S`, `Ā` is the reduction of
`A` at `w` over `k = κ(w)`. On prime-to-`p` torsion, reduction is a bijection
`A(ℚ̄)[ℓⁿ] ≅ Ā(k̄)[ℓⁿ]` (leaf I2-Red, `PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1).
Under it, `σ'` acting on coordinates becomes the `p`-power map of `k̄` (`IsArithFrob`), which on
`k̄`-points is the absolute Frobenius of `Ā`, and `F_{σ'}` becomes its reduction `F̄_{σ'}` (Néron
mapping property of the abelian scheme, leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme`). So
`m_{σ'}` becomes `α' = F̄_{σ'} ∘ Fr_Ā`, a `k`-morphism
fixing `0`, hence an endomorphism of `Ā`, the same for every `ℓ ≠ p`. -/
def AlgFrobLink : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (m : GQ → (PtQ L A →+ PtQ L A)),
    (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
    (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
    (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ g : PkgI4.GQ,
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
            ∃ Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ,
              Ψ.conj ((N : ℚ_[ℓ]) •
                  (PkgI3.Tate.map (ℓ := ℓ) (m (g * τ * g⁻¹))).baseChange ℚ_[ℓ]) =
                (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]

/-- **`AlgFrobOne` (GLUE, AV side; Glazer N5 L777-786; reduction of one morphism modulo `p`).**
`AlgFrobLink` for a single morphism of schemes. Let `A` be an abelian variety over a finite Galois
`L ⊆ ℚ̄` and `F : A → A` a finite surjective morphism of schemes. There is a finite set `S` of
primes such that: for every arithmetic Frobenius `τ` at a place `v` above `p ∉ S`, every
`g ∈ G_ℚ`, and every additive map `f` of `A(ℚ̄)` of the form `f(x) = F ∘ x ∘ Spec(gτg⁻¹)`, there
are an abelian variety `Ā` over a field `k` of characteristic `p`, `α' ∈ End(Ā)` and `N ≠ 0`
such that for every prime `ℓ ≠ p` some `ℚ_ℓ`-isomorphism `ℚ_ℓ ⊗ T_ℓ(A(ℚ̄)) ≅ V_ℓ(Ā)` carries
`N · V_ℓ(f)` to `V_ℓ(α')`.

Why it is true (SPECULATIVE in its Lean details; `N = 1` works). If such an `f` exists, `F` lies
over `Spec(s)` with `s = (gτg⁻¹)⁻¹|_L`, which is in the decomposition group of `w = g(v) ∩ L`;
so `F` is an `L`-morphism `A → A^{(s)}`. Put in `S` the primes below which `A` has bad
reduction or this `L`-morphism does not extend to the abelian-scheme models (spreading out; one
condition: `s` is determined by `F`, since `Γ(A, 𝒪) = L`; `S` depends on `F` only). For `p ∉ S`,
`Ā` is the reduction of `A` at `w`, over `k = κ(w)`. Reduction is a bijection on prime-to-`p`
torsion (leaf I2-Red, `PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1); under it,
`gτg⁻¹` acting on coordinates becomes the `p`-power map of `k̄`, i.e. the absolute Frobenius
`Fr_Ā` on `k̄`-points, and `F` becomes its reduction `F̄` (leaf I2-NMP,
`PkgI2.NeronMappingAbelianScheme`). So `f` becomes `F̄ ∘ Fr_Ā`, which lies over `Spec(id_k)`
and fixes `0` (`f` is additive), hence `α' := F̄ ∘ Fr_Ā ∈ End(Ā)` (rigidity, Mumford §4 Cor. 1,
UNVERIFIED locator), the same for every `ℓ ≠ p`. -/
def AlgFrobOne : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ (g : PkgI4.GQ)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
            ∃ Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ,
              Ψ.conj ((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]) =
                (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]

/-- **`AlgFrobLink` from `AlgFrobOne` (proved).** The maps `m_σ` take only finitely many shapes:
for each `s ∈ Gal(L/ℚ)` fix one `σ_s` restricting to `s`; then
`m_{σ_s k}(x) = F_{σ_s} ∘ x ∘ Spec(σ_s k)` for `k ∈ G_L` (second and first clauses), so one
morphism `F_{σ_s}` serves the whole coset, and `S` is the union of the `|Gal(L/ℚ)|` sets
`AlgFrobOne` gives for the `F_{σ_s}`. -/
theorem algFrobLink_of_one (hO : AlgFrobOne) : AlgFrobLink := by
  classical
  intro L _ _ A m hmL hmLL hFalg
  obtain ⟨F, hF⟩ := hFalg
  let res : GQ →* (L ≃ₐ[ℚ] L) := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L
  -- a representative of each restriction class
  let rep : (L ≃ₐ[ℚ] L) → GQ := fun s =>
    if h : ∃ σ : GQ, res σ = s then h.choose else 1
  have hrep : ∀ σ : GQ, res (rep (res σ)) = res σ := by
    intro σ
    have h : ∃ σ' : GQ, res σ' = res σ := ⟨σ, rfl⟩
    simp only [rep, h, dite_true]
    exact h.choose_spec
  choose Sf hSf using fun s : L ≃ₐ[ℚ] L => hO L A (F (rep s)) (hF (rep s)).1 (hF (rep s)).2.1
  refine ⟨Finset.univ.biUnion Sf, fun p hp hpS v τ hv hτ g => ?_⟩
  let σ' : GQ := g * τ * g⁻¹
  let σ0 : GQ := rep (res σ')
  have hpS0 : p ∉ Sf (res σ') := fun h' =>
    hpS (Finset.mem_biUnion.mpr ⟨res σ', Finset.mem_univ _, h'⟩)
  -- `k = σ0⁻¹ σ' ∈ G_L`
  have hk : σ0⁻¹ * σ' ∈ GQL L := by
    have h1 : res (σ0⁻¹ * σ') = 1 := by
      rw [map_mul, map_inv, hrep, inv_mul_cancel]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L _).mp h1 x hx
  have hσ' : σ' = σ0 * (σ0⁻¹ * σ') := by group
  have hf : ∀ x : PtQ L A, (Additive.toMul (m σ' x)).left =
      Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ F σ0 := by
    intro x
    have hm : m σ' = (m σ0).comp (m (σ0⁻¹ * σ')) := by
      conv_lhs => rw [hσ']
      exact (hmLL σ0 _ hk).1
    have hmk := hmL (σ0⁻¹ * σ') (toLAut _ hk) (fun _ => rfl)
    rw [hm, AddMonoidHom.comp_apply, (hF σ0).2.2, hmk]
    show Spec.map (CommRingCat.ofHom ((act σ0 : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (PkgI3.AbVar.galHom (toLAut _ hk) ≫ Additive.toMul x).left ≫ F σ0 = _
    have hSpec : Spec.map (CommRingCat.ofHom ((act σ0 : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        Spec.map (CommRingCat.ofHom ((toLAut _ hk : Qbar ≃ₐ[L] Qbar) : Qbar →+* Qbar)) =
        Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext y
      have h0 : σ0 * (σ0⁻¹ * σ') = σ' := by group
      exact congrArg (fun s : GQ => act s y) h0
    rw [← hSpec, Category.assoc]
    rfl
  exact hSf (res σ') p hp hpS0 v τ hv hτ g (m σ') hf

/-! ## `AlgFrobOne` from a reduction homomorphism on points -/

/-- `T_ℓ(r)` is bijective if `r` is injective on `ℓ`-power torsion and every `ℓⁿ`-torsion point
of the target has an `ℓⁿ`-torsion preimage. -/
theorem tateMap_bijective (ℓ : ℕ) [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (r : M →+ N)
    (hinj : ∀ (n : ℕ) (x : M), (ℓ ^ n) • x = 0 → r x = 0 → x = 0)
    (hsurj : ∀ (n : ℕ) (y : N), (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ r x = y) :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) r) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    funext n
    exact hinj n (x.1 n) (PkgI3.Tate.pow_smul_eq_zero x.2 n)
      (congrFun (congrArg Subtype.val hx) n)
  · intro y
    choose X hX using fun n => hsurj n (y.1 n) (PkgI3.Tate.pow_smul_eq_zero y.2 n)
    have h0 : X 0 = 0 := by simpa using (hX 0).1
    have hs : ∀ n, ℓ • X (n + 1) = X n := by
      intro n
      have := hinj n (ℓ • X (n + 1) - X n) (by
          rw [smul_sub, smul_smul, ← pow_succ, (hX (n + 1)).1, (hX n).1, sub_zero])
        (by rw [map_sub, map_nsmul, (hX (n + 1)).2, (hX n).2, y.2.2 n, sub_self])
      exact sub_eq_zero.mp this
    exact ⟨⟨X, h0, hs⟩, Subtype.ext (funext fun n => (hX n).2)⟩

/-- **`AlgFrobRed` (GLUE, AV side; Glazer N5 L777-786; the reduction map).** `AlgFrobOne` with
the `ℓ`-adic isomorphisms replaced by one homomorphism on points: for `F`, `S`, `p ∉ S`, `τ`, `g`
and `f(x) = F ∘ x ∘ Spec(gτg⁻¹)` as in `AlgFrobOne`, there are an abelian variety `Ā` over a
field `k` of characteristic `p`, `α' ∈ End(Ā)`, `N ≠ 0` and a group homomorphism
`red : A(ℚ̄) → Ā(k̄)` with `red ∘ (N·f) = α' ∘ red`, injective on `ℓ`-power torsion and with
every `ℓⁿ`-torsion point of `Ā(k̄)` the image of an `ℓⁿ`-torsion point, for every prime `ℓ ≠ p`.

Why it is true (SPECULATIVE in its Lean details; `N = 1`). `S` as in `AlgFrobOne`. Let
`v' = g(v)`, at which `σ' = gτg⁻¹` is an arithmetic Frobenius, `w = v' ∩ L`, `𝒜` the abelian
scheme over `O_w`, `Ā` its special fibre over `k = κ(w)`. `red` is the reduction map
`A(ℚ̄) = 𝒜(O_{v'}) → Ā(κ(v'))` (valuative criterion of properness), followed by a `k`-isomorphism
`κ(v') ≅ k̄`. Since `σ'` preserves `O_{v'}` and `F` extends to `𝒜` (leaf I2-NMP), `f` lifts to
`𝒜(O_{v'})` and reduces to `x̄ ↦ F̄ ∘ x̄ ∘ Spec(Frob_p) = (F̄ ∘ Fr_Ā)(x̄)`, which is
`α' := F̄ ∘ Fr_Ā ∈ End(Ā)` (see `AlgFrobOne`). The torsion clauses are leaf I2-Red
(`PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1) for `m = ℓⁿ`, prime to `p`. -/
def AlgFrobRed : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ (g : PkgI4.GQ)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobOne` from `AlgFrobRed` (proved):** `Ψ = ℚ_ℓ ⊗ T_ℓ(red)`. -/
theorem algFrobOne_of_red (hR : AlgFrobRed) : AlgFrobOne := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := hR L A F hF1 hF2
  refine ⟨S, fun p hp hpS v τ hv hτ g f hf => ?_⟩
  obtain ⟨k, _, hk, Ab, α, N, hN, red, hred, hbij⟩ := hS p hp hpS v τ hv hτ g f hf
  refine ⟨k, _, hk, Ab, α, N, hN, fun ℓ _ hℓp => ?_⟩
  let Ψ0 := LinearEquiv.ofBijective (PkgI3.Tate.map (ℓ := ℓ) red)
    (tateMap_bijective ℓ red (fun n => (hbij ℓ (Fact.out) hℓp n).1)
      (fun n => (hbij ℓ (Fact.out) hℓp n).2))
  refine ⟨Ψ0.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _, ?_⟩
  have h1 : Ψ0.conj (N • PkgI3.Tate.map (ℓ := ℓ) f) = PkgI3.AbVar.homT (ℓ := ℓ) α := by
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := Ψ0.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    funext n
    show (PkgI3.Tate.map red ((N • PkgI3.Tate.map f) w)).1 n =
      (PkgI3.AbVar.homT (ℓ := ℓ) α (PkgI3.Tate.map red w)).1 n
    rw [LinearMap.smul_apply, map_nsmul]
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, PkgI3.Tate.map_apply, PkgI3.AbVar.homT]
    rw [← map_nsmul, hred]
  have h2 : (N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ] =
      (N • PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ] := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ] N (PkgI3.Tate.map (ℓ := ℓ) f), LinearMap.baseChange_smul,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, conj_baseChange, h1]

/-! ## From the points-level comparison to `FrobCompare` for `opV(Θ ∘ f ∘ Θ⁻¹)` -/

/-- The comparison for `f` on `V_ℓ(A(ℚ̄))` gives the kernel's `FrobCompare` for the transported
operator `opV(Θ ∘ f ∘ Θ⁻¹)` on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`, for any additive bijection `Θ`. -/
theorem frobCompare_opV_conjE {L : IF} (A : PkgI3.AbVar L) {K : Type} [Field K]
    (A' : PkgI3.AbVar K) (Θ : PtQ L A ≃+ PtA A') (f : PtQ L A →+ PtQ L A)
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type} [Field k] (Ab : PkgI3.AbVar k)
    (α : PkgI3.AbVar.End Ab) (N : ℕ)
    (Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ)
    (hΨ : Ψ.conj ((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]) =
      (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]) :
    GlueC10Link.FrobCompare ℓ (opV A' ℓ (conjE Θ f)) α N := by
  let e := tateMapEquiv ℓ Θ
  let Ψ' : A'.V ℓ ≃ₗ[ℚ_[ℓ]] Ab.V ℓ :=
    (e.symm.baseChange ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtA A')) (PkgI3.Tate.T ℓ (PtQ L A))).trans Ψ
  refine ⟨Ψ'.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) (A'.V ℓ) (Ab.V ℓ), ?_⟩
  -- the `ℚ_ℓ`-level identity
  have h1 : Ψ'.conj ((N : ℚ_[ℓ]) •
      (PkgI3.Tate.map (ℓ := ℓ) (conjE Θ f)).baseChange ℚ_[ℓ]) =
      (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ] := by
    rw [← hΨ]
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.conj_apply_apply]
    show (e.symm.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).trans Ψ _ = _
    rw [LinearEquiv.trans_apply]
    congr 1
    rw [LinearEquiv.symm_trans_apply]
    generalize Ψ.symm x = y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul q t =>
      rw [← LinearEquiv.baseChange_symm, LinearEquiv.symm_symm, LinearEquiv.baseChange_tmul,
        LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, map_smul, LinearEquiv.baseChange_tmul]
      congr 2
      apply Subtype.ext
      funext n
      show Θ.symm (Θ (f (Θ.symm (Θ (t.1 n))))) = f (t.1 n)
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  -- base change to `ℚ̄_ℓ`
  have h2 : ((N : PadicAlgCl ℓ) • opV A' ℓ (conjE Θ f)) =
      (((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) (conjE Θ f)).baseChange ℚ_[ℓ])).baseChange
        (PadicAlgCl ℓ) := by
    rw [LinearMap.baseChange_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rfl
  rw [h2, conj_baseChange, h1]

/-! ## Rescaling the scalars of `G7Out` -/

/-- `G7Out` is preserved by multiplying `a` and `β` by one nonzero `φ` that is `1` on `G_K`
(with `ε` multiplied by `∂φ`); `ρ = β⁻¹ a T` does not change. -/
theorem g7Out_rescale {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β a₂ β₂ φ : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (hφ0 : ∀ g, φ g ≠ 0) (hφ1 : ∀ σ, φ (GaloisCopy.resQ K σ) = 1)
    (ha₂ : ∀ g, a₂ g = φ g * a g) (hβ₂ : ∀ g, β₂ g = φ g * β g)
    (h : GaloisCopy.G7Out A ℓ Tm c ε a β u) :
    GaloisCopy.G7Out A ℓ Tm c (fun g g₂ => ε g g₂ * (φ g * φ g₂ / φ (g * g₂))) a₂ β₂ u := by
  obtain ⟨hdim, hrk, hT, ha, hβ, hβ0, hres, hcomm, hcont⟩ := h
  have hrho : ∀ g, GlueDescent.rho Tm a₂ β₂ g = GlueDescent.rho Tm a β g := by
    intro g
    unfold GlueDescent.rho
    rw [ha₂, hβ₂]
    congr 1
    have h0 := hφ0 g
    have h1 := hβ0 g
    field_simp
  refine ⟨hdim, hrk, hT, fun g g₂ => ?_, fun g g₂ => ?_, fun g => ?_, fun σ => ?_, hcomm, ?_⟩
  · rw [ha₂, ha₂, ha₂]
    have h0 := hφ0 (g * g₂)
    have := ha g g₂
    calc φ g * a g * (φ g₂ * a g₂) * c g g₂ = φ g * φ g₂ * (a g * a g₂ * c g g₂) := by ring
      _ = φ g * φ g₂ * (ε g g₂ * a (g * g₂)) := by rw [this]
      _ = ε g g₂ * (φ g * φ g₂ / φ (g * g₂)) * (φ (g * g₂) * a (g * g₂)) := by
        field_simp
  · rw [hβ₂, hβ₂, hβ₂]
    have h0 := hφ0 (g * g₂)
    have := hβ g g₂
    calc φ g * β g * (φ g₂ * β g₂) = φ g * φ g₂ * (β g * β g₂) := by ring
      _ = φ g * φ g₂ * (ε g g₂ * β (g * g₂)) := by rw [this]
      _ = ε g g₂ * (φ g * φ g₂ / φ (g * g₂)) * (φ (g * g₂) * β (g * g₂)) := by
        field_simp
  · rw [hβ₂]; exact mul_ne_zero (hφ0 g) (hβ0 g)
  · obtain ⟨h1, h2, h3⟩ := hres σ
    exact ⟨h1, by rw [ha₂, hφ1, h2, _root_.one_mul], by rw [hβ₂, hφ1, h3, _root_.one_mul]⟩
  · intro f v
    have : (fun g => f (GlueDescent.rho Tm a₂ β₂ g v)) = fun g => f (GlueDescent.rho Tm a β g v) :=
      funext fun g => by rw [hrho]
    rw [this]
    exact hcont f v

/-! ## The scalars in `ℚ̄` -/

/-- **The scalar link (proved, no leaf).** From the data of B1/B2 (`a > 0` real, `c = n/d`,
`ε` a sign cocycle with `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}`, `∂β = ε`, `a = β = 1` on `G_{L'}`):
`γQ : G_ℚ → ℚ̄^×` with `∂γQ = c` and `γQ = 1` on `G_{L'}` (the algebraic form of `β/a`), and
`βQ : G_ℚ → ℚ̄` with `ιC ∘ βQ = β` for one embedding `ιC : ℚ̄ → ℂ`. The values of `β/a` and of `β`
are algebraic because their `r`-th powers lie in `ℚ`, resp. are `±1`, where `r` is the order of
`σ|_{L'}`. -/
theorem scalarsQbar (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ)
    (hd : ∀ σ τ, d σ τ ≠ 0)
    (hna : ∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ))
    (hβe : ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ))
    (hε2 : ∀ σ τ, ε σ τ ^ 2 = 1)
    (ha0 : ∀ σ, 0 < a σ)
    (hone : ∀ k ∈ GQL L', a k = 1 ∧ β k = 1) :
    ∃ (gamQ βQ : GQ → Qbar) (ιC : Qbar →ₐ[ℚ] ℂ), (∀ σ, gamQ σ ≠ 0) ∧
      (∀ σ τ, gamQ σ * gamQ τ = ((n σ τ : Qbar) / (d σ τ : Qbar)) * gamQ (σ * τ)) ∧
      (∀ k ∈ GQL L', gamQ k = 1) ∧ (∀ σ, ιC (βQ σ) = (β σ : ℂ)) := by
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) /
        ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  -- `β` is algebraic: `β(σ)^r = ±1`
  have hpowβ : ∀ (σ : GQ) (k : ℕ), ∃ e : ℂ, e ^ 2 = 1 ∧
      (β σ : ℂ) ^ k = e * (β (σ ^ k) : ℂ) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by norm_num, by rw [pow_zero, pow_zero, (hone 1 (one_mem _)).2]; simp⟩
    | succ k ih =>
      obtain ⟨e, he, hk⟩ := ih
      refine ⟨e * (ε (σ ^ k) σ : ℂ), ?_, ?_⟩
      · rw [mul_pow, he, _root_.one_mul, ← Units.val_pow_eq_pow_val, hε2, Units.val_one]
      · rw [pow_succ, hk, _root_.mul_assoc, ← Units.val_mul, hβe, Units.val_mul, pow_succ]
        ring
  have halgβ : ∀ σ, IsIntegral ℚ (β σ : ℂ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨e, he, ht⟩ := hpowβ σ r
    rw [(hone _ hr).2, Units.val_one, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ (r * 2) - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    simp [Polynomial.eval₂_sub, pow_mul, ht, he]
  let F : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (Set.range gC ∪ Set.range (fun σ => (β σ : ℂ)))
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
    · exact halg σ
    · exact halgβ σ)
  let ψ : F →ₐ[ℚ] Qbar := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ =>
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨σ, rfl⟩)
  have hmemβ : ∀ σ, (β σ : ℂ) ∈ F := fun σ =>
    IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨σ, rfl⟩)
  letI : Algebra F Qbar := ψ.toAlgebra
  haveI : IsScalarTower ℚ F Qbar := IsScalarTower.of_algebraMap_eq (fun x => (ψ.commutes x).symm)
  haveI : Algebra.IsAlgebraic F Qbar :=
    Algebra.IsAlgebraic.extendScalars (R := ℚ) (algebraMap ℚ F).injective
  let ιF : Qbar →ₐ[F] ℂ := IsAlgClosed.lift
  let ιC : Qbar →ₐ[ℚ] ℂ := ιF.restrictScalars ℚ
  have hιψ : ∀ x : F, ιC (ψ x) = x := fun x => ιF.commutes x
  refine ⟨fun σ => ψ ⟨gC σ, hmem σ⟩, fun σ => ψ ⟨β σ, hmemβ σ⟩, ιC, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    have : (⟨gC σ, hmem σ⟩ : F) = 0 := ψ.toRingHom.injective (h0.trans (map_zero ψ).symm)
    exact congrArg Subtype.val this
  · intro σ τ
    have hF : (⟨gC σ, hmem σ⟩ : F) * ⟨gC τ, hmem τ⟩ =
        algebraMap ℚ F (q σ τ) * ⟨gC (σ * τ), hmem (σ * τ)⟩ := Subtype.ext (hq σ τ)
    show ψ _ * ψ _ = _ * ψ _
    rw [← map_mul, hF, map_mul, AlgHom.commutes]
    congr 1
    simp only [q, map_div₀, map_intCast]
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))
  · intro σ
    exact hιψ ⟨β σ, hmemβ σ⟩

/-! ## The assembly -/

set_option maxHeartbeats 4000000 in
/-- **`TateBridge35` from the leaf I3.M0 (`TateModuleFree`) and the glue `AlgFrobLink`.**
`Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (unram-tate's operators, built from the one
points-level descent datum `m` of `G7Data`), `aQ g = βQ g / γQ(hgh⁻¹)`, `βQ` with `ιC ∘ βQ = β`
(`scalarsQbar`), `j_ℓ = IsAlgClosed.lift`. `G7Out` at `ℓ` is unram-tate's construction with
`γ = j_ℓ ∘ γQ`, rescaled by `φ = j_ℓ(βQ)/j_ℓ(γQ(h·h⁻¹))` (`g7Out_rescale`). `FrobTraceLink`
comes from `AlgFrobLink` (applied to `m` with `g = h`) via `frobCompare_opV_conjE`, with
`S ∪ {3, 5}`. -/
theorem tateBridge35_of_algFrobLink (hT : PkgI3.TateModuleFree) (hF : AlgFrobLink) :
    G14Bridge.TateBridge35 := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, hFalg⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gamQ, βQ, ιC, hg0, hgc, hg1, hιβ⟩ := scalarsQbar L' a β ε n d hd hna hβe hεc.2.1 ha0
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hβQ0 : ∀ g, βQ g ≠ 0 := by
    intro g h0
    have := hιβ g
    rw [h0, map_zero] at this
    exact Units.ne_zero _ this.symm
  have hβQ1 : ∀ k, k ∈ GQL L' → βQ k = 1 := by
    intro k hk
    apply ιC.toRingHom.injective
    show ιC (βQ k) = ιC 1
    rw [hιβ, hβL' k hk, map_one, Units.val_one]
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  -- the operators and `G7Out` at one `ℓ`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        @GaloisCopy.G7Out L' _ (numberField_of_fd L')
          (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _
          (fun g => opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
            (conjE Θ (m (h * g * h⁻¹)))) c ε'
          (fun g => j (βQ g / gamQ (h * g * h⁻¹))) (fun g => j (βQ g)) uu := by
    intro ℓ _ j
    let gam : GQ → PadicAlgCl ℓ := fun σ => j (gamQ σ)
    have hgam0 : ∀ σ, gam σ ≠ 0 := fun σ => (map_ne_zero j).mpr (hg0 σ)
    have hgamc : ∀ σ τ, gam σ * gam τ =
        ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ) := by
      intro σ τ
      show j _ * j _ = _ * j _
      rw [← map_mul, hgc, map_mul, map_div₀, map_intCast, map_intCast]
    have hgam1 : ∀ k ∈ GQL L', gam k = 1 := by
      intro k hk; show j _ = 1; rw [hg1 k hk, map_one]
    -- (from here: unram-tate's `tateBridge_of_pieces`, with this `gam`)
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
    have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
      show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
      group
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
    let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
    have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, iO_sq, map_add, map_one, two_smul]
    have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
      module
    have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
      rw [← map_mul, iO_jO, map_neg, map_mul]
    obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
    have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
      intro g o
      apply Commute.map _ R
      exact hmEnd (cj g) (iot o)
    have hTm : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
      intro g g₂
      have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
        hnd (cj g) (cj g₂)
      have h1 := congrArg R h0
      rw [map_zsmul, map_zsmul, ← hcj] at h1
      have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
        show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
        rw [← map_mul]; exact h1
      have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
          (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
        (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
          (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
      have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
      show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
      intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
    have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
      intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
    have hnorm : (L'.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
    have hres : ∀ σ : Field.absoluteGaloisGroup L',
        cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact hnorm.conj_mem _ this h
    have hres0 : ∀ σ : Field.absoluteGaloisGroup L',
        (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact this
    have hTres : ∀ σ : Field.absoluteGaloisGroup L',
        Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      have hτ := hres σ
      let σ' : Qbar ≃ₐ[L] Qbar :=
        AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
          (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
      have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
      rw [tate_eq_opV]
      show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
      congr 1
      refine DFunLike.ext _ _ fun x => ?_
      show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
      rw [hm]
      show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
      rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
    have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
        GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      unfold GlueDescent.rho
      rw [hTres σ]
      simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
    have hG7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c' c' a' β' uu := by
      refine ⟨_hdim, _hrank, hTm, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
        fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
      intro f v
      rw [continuous_iff_continuousAt]
      intro g₀
      let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
      have he₀ : Topology.IsOpenEmbedding e₀ :=
        (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
      have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
      have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
          fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
        funext σ
        simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
        rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hTm ha hβ hβ0, hrho1, Module.End.mul_apply]
      have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
        rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
      rw [he₀.continuousAt_iff, he₀1] at hc
      exact hc
    -- rescale by `φ = j(βQ)/γ(h·h⁻¹)`
    let φ : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (βQ g) / gam (cj g)
    have hφ0 : ∀ g, φ g ≠ 0 := fun g =>
      div_ne_zero ((map_ne_zero j).mpr (hβQ0 g)) (hgam0 _)
    have hφ1 : ∀ σ, φ (@GaloisCopy.resQ L' _ hNF σ) = 1 := by
      intro σ
      show j (βQ _) / gam (cj _) = 1
      rw [hβQ1 _ (hres0 σ), hgam1 _ (hres σ), map_one, div_one]
    refine ⟨c', _, uu, g7Out_rescale _ ℓ Tm c' c' a' β' _ _ φ uu hφ0 hφ1 (fun g => ?_)
      (fun g => ?_) hG7⟩
    · show j (βQ g / gamQ (cj g)) = j (βQ g) / j (gamQ (cj g)) * 1
      rw [map_div₀, _root_.mul_one]
    · show j (βQ g) = j (βQ g) / gam (cj g) * gam (cj g)
      rw [div_mul_cancel₀ _ (hgam0 _)]
  let j5 : Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift
  let j3 : Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, ε5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, ε3, u3, h3⟩ := key 3 j3
  refine ⟨fun g => βQ g / gamQ (h * g * h⁻¹), βQ, j5, j3, _, c5, ε5, u5, _, c3, ε3, u3, h5, h3,
    ?_, ιC, hιβ⟩
  -- `FrobTraceLink` from `AlgFrobLink`
  obtain ⟨S, hS⟩ := hF L A m hmL hmLL hFalg
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS' : p ∉ S := fun h' => hpS (Finset.mem_union_left _ h')
  have hp3 : (3 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  have hp5 : (5 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  obtain ⟨k, _, hk, Ab, α, N', hN', hΨ⟩ := hS p hp hpS' v τ hv hτ h
  obtain ⟨Ψ3, hΨ3⟩ := hΨ 3 hp3
  obtain ⟨Ψ5, hΨ5⟩ := hΨ 5 hp5
  exact ⟨k, _, hk, Ab, α, N', hN',
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 3 Ab α N' Ψ3 hΨ3,
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 5 Ab α N' Ψ5 hΨ5⟩

/-- **Main result: `TateBridge35` from the leaf I3.M0 and the single-morphism glue
`AlgFrobOne`.** -/
theorem tateBridge35_of_algFrobOne (hT : PkgI3.TateModuleFree) (hO : AlgFrobOne) :
    G14Bridge.TateBridge35 :=
  tateBridge35_of_algFrobLink hT (algFrobLink_of_one hO)

/-- **Main result, finest form: `TateBridge35` from the leaf I3.M0 and the glue `AlgFrobRed`
(the reduction homomorphism on points).** -/
theorem tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree) (hR : AlgFrobRed) :
    G14Bridge.TateBridge35 :=
  tateBridge35_of_algFrobOne hT (algFrobOne_of_red hR)

end FrobTrace

end

-- END verbatim body of scratch/frob-trace/FrobTrace.lean
end FrobTraceSec

section G0DimSec
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
open Order TensorProduct
-- BEGIN verbatim scratch/g0-dim/Dim.lean l.107-305, l.339-344
namespace G0Dim

/-! ## §1. Commutative algebra -/


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


open AlgebraicGeometry CategoryTheory Limits

end G0Dim

end G0DimSec

/-! ## lg-kerwild: `KerWild` from G7Data through the Tate bridge, `DescentPts` on G7Data's model

Task lg-kerwild (2026-11-13). local-glue (`G15Ram.localGlue_of_unramRoots`) left two glue Props:
`G15Ram.KerWild K β L` (G7Data's kernel-field clause, dropped by `G7Out` and by g0-mod-field's
`TateBridge`, local-glue finding G8) and `G15Ram.DescentPts A L` (used at `p ≤ 5`).

This part:
* `kerWild_of_ker`: `KerWild L' β L` from G7Data's clause `G_{L'} = G_L ∩ ker β_ℂ` and any
  transport with `β(g) = 1 → β_ℂ(g) = 1`; `kerWild_of_alg` for the transport of g14-trace's
  `TateBridge35` (`β = j ∘ β_ℚ̄`, `β_ℂ = ι_ℂ ∘ β_ℚ̄`, `j`, `ι_ℂ` field embeddings, so injective);
  `kerWild_of_g7Data_alg` reads the clause off `G7Data`.
* `TateBridgeK`: g0-mod-field's `TateBridge` with `KerWild` added to its output (the correction of
  finding G8); `TateBridgeT`: `TateBridge` with the scalar transport added to its output (as
  `TateBridge35` has it); `tateBridgeK_of_T`, `tateBridge_of_K` (proved).
* `TateBridge35K`: g14-trace's `TateBridge35` with `KerWild` at `ℓ = 5, 3` added;
  `tateBridge35K_of_35 : TateBridge35 → TateBridge35K` (proved: the clause is transported from
  `G7Data`, nothing new is assumed); `tateBridgeK_five_three_of_35` (the `ℓ = 5, 3` conclusions
  of `TateBridgeK` from `TateBridge35`).
* `dim_model_of_bc`: `dim A = 2` from `dim A_{L'} = 2` (g0-dim's `pkgI3_dim_baseChange`);
  `descentPts_of_g7` : `DescentPts (A_{L'}) L` for G7Data's model `A/L`.
* `localGlue_of_tateBridge35`: local-glue's `LocalGlue` on `TateBridge35`'s data at `ℓ = 5, 3`
  from R6, I2-Tors, `UnramRoots` and `G7Clauses`, with no `KerWild` or `DescentPts` hypothesis.
-/

section LGKerWildSec

noncomputable section

namespace LGKerWild

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField

/-! ### §1. `KerWild` from the kernel-field clause -/

/-- **`KerWild` from G7Data's kernel-field clause and a transport that detects `β = 1`
(proved).** `G_{L'} = G_L ∩ ker β_ℂ` (G7Data, `GQL L = L.fixingSubgroup`), `L'` finite Galois, and
`β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` give `KerWild L' β_ℓ L` for `G7Out`'s model field `K = L'`. -/
theorem kerWild_of_ker {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] (βC : PkgI4.GQ → ℂˣ)
    (hker : ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    {β : PkgI4.GQ → PadicAlgCl ℓ} (hβ : ∀ g, β g = 1 → βC g = 1) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') β L := by
  intro g hgL hg1
  have h3 : g ∈ L'.fixingSubgroup :=
    (hker g).mpr ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hgL, hβ g hg1⟩
  rw [RQ.resQ_range L']
  exact h3

/-- **The algebraic transport detects `β = 1` (proved).** If `β_ℓ = j ∘ β_ℚ̄` and
`β_ℂ = ι_ℂ ∘ β_ℚ̄` for `ℚ`-algebra maps `j : ℚ̄ → ℚ̄_ℓ`, `ι_ℂ : ℚ̄ → ℂ` (injective, `ℚ̄` a field),
then `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1`. -/
theorem transport_one {ℓ : ℕ} [Fact ℓ.Prime] (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (βC : PkgI4.GQ → ℂˣ)
    (hC : ∀ g, ιC (βQ g) = (βC g : ℂ)) (g : PkgI4.GQ) (h1 : j (βQ g) = 1) : βC g = 1 := by
  have hQ : βQ g = 1 := j.toRingHom.injective (show j (βQ g) = j 1 by rw [h1, map_one])
  apply Units.ext
  rw [← hC g, hQ, map_one, Units.val_one]

/-- **`KerWild` for the algebraic transport (proved).** -/
theorem kerWild_of_alg {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] (βC : PkgI4.GQ → ℂˣ)
    (hker : ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (βC g : ℂ)) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') (fun g => j (βQ g)) L :=
  kerWild_of_ker βC hker (fun g h1 => transport_one βQ j ιC βC hC g h1)

/-- G7Data's kernel-field clause (clause 9), as an equality of fixing subgroups. -/
theorem g7Data_ker {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ}
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') :
    ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ β σ = 1 :=
  h.2.2.2.2.2.2.2.2.1

/-- **`KerWild` transported from `G7Data` (proved).** For G7's data and an algebraic form `β_ℚ̄`
of its `β` (`ι_ℂ ∘ β_ℚ̄ = β`), every `j : ℚ̄ → ℚ̄_ℓ` gives `KerWild L' (j ∘ β_ℚ̄) L`. -/
theorem kerWild_of_g7Data_alg {ℓ : ℕ} [Fact ℓ.Prime] {u : ℚ} {P : QML3 Qbar} {L : IF}
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L'] {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (hC : ∀ g, ιC (βQ g) = (β g : ℂ)) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') (fun g => j (βQ g)) L :=
  kerWild_of_alg β (g7Data_ker h) βQ j ιC hC

/-! ### §2. The corrected bridges -/

/-- **Bridge 2 with the kernel-field clause (GLUE; correction of g0-mod-field's `TateBridge`,
local-glue finding G8).** `TateBridge`'s statement, with `KerWild L' β' L` (G7Data's clause
`G_{L'} = G_L ∩ ker β`, for the `ℚ̄_ℓ`-valued `β'`: `g ∈ G_L`, `β'(g) = 1` ⟹ `g ∈ G_{L'}`) added
to its output. Source: N5 L702-716 (`L'` is the kernel field of `β|G_L`). -/
def TateBridgeK : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L

/-- **Bridge 2 with the scalar transport (GLUE; the form in which `TateBridge35` states it).**
`TateBridge`'s statement with, in its output, an algebraic form `β_ℚ̄ : G_ℚ → ℚ̄` of G7Data's
`β` (`ι_ℂ ∘ β_ℚ̄ = β`) and an embedding `j : ℚ̄ → ℚ̄_ℓ` with `β' = j ∘ β_ℚ̄` (N5 L719-722: the
values of `β` are algebraic and are mapped into `ℚ̄_ℓ` by one embedding). -/
def TateBridgeT : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∃ (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
        (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ), (∀ g, β' g = j (βQ g)) ∧ ∀ g, ιC (βQ g) = (β g : ℂ)

/-- **`TateBridgeK` contains `TateBridge` (proved).** -/
theorem tateBridge_of_K (h : TateBridgeK) : TateBridge := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, -⟩ := h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  exact ⟨Tm, c, ε', a, β', uu, h7⟩

/-- **The transport form gives the kernel-field form (proved)**: `KerWild` is transported from
`G7Data` (`kerWild_of_g7Data_alg`). -/
theorem tateBridgeK_of_T (h : TateBridgeT) : TateBridgeK := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, βQ, j, ιC, hj, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, ?_⟩
  have hβ' : β' = fun g => j (βQ g) := funext hj
  subst hβ'
  exact kerWild_of_g7Data_alg hD βQ j ιC hC

/-- **g14-trace's `TateBridge35` with the kernel-field clause at `ℓ = 5, 3` (GLUE).**
`TateBridge35`'s statement with `KerWild L' (j_ℓ ∘ β_ℚ̄) L` for `ℓ = 5, 3` added to the output.
It follows from `TateBridge35` (`tateBridge35K_of_35`). -/
def TateBridge35K : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @G14Bridge.FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      @G15Ram.KerWild 5 _ L' _ (numberField_of_fd L') (fun g => j5 (βQ g)) L ∧
      @G15Ram.KerWild 3 _ L' _ (numberField_of_fd L') (fun g => j3 (βQ g)) L

/-- **`TateBridge35` gives `TateBridge35K` (proved)**: the kernel-field clause at `ℓ = 5, 3` is
transported from `G7Data` through `TateBridge35`'s own clause `ι_ℂ ∘ β_ℚ̄ = β`. -/
theorem tateBridge35K_of_35 (h : G14Bridge.TateBridge35) : TateBridge35K := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ⟨ιC, hC⟩,
    kerWild_of_g7Data_alg hD βQ j5 ιC hC, kerWild_of_g7Data_alg hD βQ j3 ιC hC⟩

/-- **`TateBridge35` gives the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridgeT` (proved).** -/
theorem tateBridgeT_at_of_35 (h : G14Bridge.TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    ∀ ℓ, (ℓ = 5 ∨ ℓ = 3) → ∀ [Fact ℓ.Prime],
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∃ (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
        (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ), (∀ g, β' g = j (βQ g)) ∧ ∀ g, ιC (βQ g) = (β g : ℂ) := by
  intro ℓ hℓ _
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, -, ιC, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  rcases hℓ with rfl | rfl
  · exact ⟨Tm5, c5, ε5, _, _, u5, h5, βQ, j5, ιC, fun _ => rfl, hC⟩
  · exact ⟨Tm3, c3, ε3, _, _, u3, h3, βQ, j3, ιC, fun _ => rfl, hC⟩

/-- **`TateBridge35` gives the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridgeK` (proved).** -/
theorem tateBridgeK_at_of_35 (h : G14Bridge.TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    ∀ ℓ, (ℓ = 5 ∨ ℓ = 3) → ∀ [Fact ℓ.Prime],
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L := by
  intro ℓ hℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, βQ, j, ιC, hj, hC⟩ :=
    tateBridgeT_at_of_35 h u P L A ε N χ β L' hLL' hD hdim hrk ℓ hℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, ?_⟩
  have hβ' : β' = fun g => j (βQ g) := funext hj
  subst hβ'
  exact kerWild_of_g7Data_alg hD βQ j ιC hC

/-! ### §3. `DescentPts` on G7Data's model -/

/-- **`dim A = 2` for the model `A/L` from `dim A_{L'} = 2` (proved)**, by g0-dim's
`pkgI3_dim_baseChange` (dimension is invariant under field base change, Stacks 00P4). -/
theorem dim_model_of_bc {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2) : A.dim = 2 :=
  (@G0Dim.pkgI3_dim_baseChange L _ L' _ (incAlg hLL') A).symm.trans hdim

/-- **`DescentPts` for `A_{L'}` and G7's model field `L` (proved)**: `TateBridge`'s abelian
variety is the base change `A_{L'}` of the model `A/L` (`G7Data`), so local-glue's
`descentPts_baseChange` (with the conjugate model when Mathlib's embeddings differ, finding G9)
applies; `dim A = 2` comes from `dim A_{L'} = 2` (`dim_model_of_bc`). -/
theorem descentPts_of_g7 {L L' : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [FiniteDimensional ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2) :
    @G15Ram.DescentPts L' _ (numberField_of_fd L')
      (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) L _ :=
  G15Ram.descentPts_baseChange hLL' A (dim_model_of_bc hLL' A hdim)

/-! ### §4. `LocalGlue` on the Tate bridge's data, with no local glue Prop -/

/-- **`LocalGlue` on the data of the transport form of the Tate bridge (proved).** For G7's
data, `dim A_{L'} = 2`, `G7Out` at `ℓ` for `A_{L'}` with `β' = j ∘ β_ℚ̄` where `ι_ℂ ∘ β_ℚ̄ = β`
(the output of `TateBridgeT`, or of `TateBridge35` at `ℓ = 5, 3`), and G7's clauses
(`G7Clauses`): `LocalGlue p Tm a β' L` at every `p ≠ ℓ`, from the leaves R6 and I2-Tors and the
textbook Prop `UnramRoots` (used at `p = 2`). -/
theorem localGlue_of_transport (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a
        (fun g => j (βQ g)) uu)
    (hCl : G15Ram.G7Clauses (fun g => j (βQ g)) ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => j (βQ g)) L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hCl
    (kerWild_of_g7Data_alg hD βQ j ιC hC) (fun _ => descentPts_of_g7 hLL' A hdim)

/-- **`LocalGlue` on `TateBridge35`'s data at `ℓ = 5` and `ℓ = 3` (proved).** For G7's data and the
output of g14-trace's `TateBridge35`, with G7's clauses for `j_ℓ ∘ β_ℚ̄`: `LocalGlue` at every
`p ≠ 5` for `Tm₅` and at every `p ≠ 3` for `Tm₃`, from R6, I2-Tors and `UnramRoots`. -/
theorem localGlue_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
    (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
    (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
    (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
    (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
    (h5 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5)
    (h3 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (hCl5 : G15Ram.G7Clauses (fun g => j5 (βQ g)) ε5 L)
    (hCl3 : G15Ram.G7Clauses (fun g => j3 (βQ g)) ε3 L) :
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 →
      @G15Ram.LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm5 (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) L) ∧
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 3 →
      @G15Ram.LocalGlue p ⟨hp⟩ 3 _ _ _ _ Tm3 (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) L) := by
  refine ⟨fun p hp hp5 => ?_, fun p hp hp3 => ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_transport hR6 hTors (hU p 5) hp5 hD βQ j5 ιC hC h5 hCl5
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_transport hR6 hTors (hU p 3) hp3 hD βQ j3 ιC hC h3 hCl3

end LGKerWild

end

end LGKerWildSec


/-! ## lg-kerwild §5: `TateBridgeK` proved from the leaf I3.M0 (unram-tate's proof with the
kernel-field clause)

unram-tate proved g0-mod-field's `TateBridge` from I3.M0 (`tateBridge_of_tateModuleFree`) with
`β' g = γ(h g h⁻¹)`, `γ = ψ ∘ (β/a)`, `ψ` a field embedding. Below: `ScalarTransferK` adds to
unram-tate's `ScalarTransfer` the clause `γ(σ) = 1 → β(σ) = a(σ)` (the same proof gives it, `ψ`
being injective), and `tateBridgeK_of_piecesK` is unram-tate's `tateBridge_of_pieces` (proof copied)
with the extra conclusion `KerWild L' β' L`: for `g ∈ G_L` with `β'(g) = 1`, `hgh⁻¹ ∈ G_L`
(normal), `a = 1` on `G_L` (DescentDatum), so `β(hgh⁻¹) = 1`, so `hgh⁻¹ ∈ G_{L'}` (G7Data's
clause), so `g ∈ G_{L'}` (normal) `= resQ_{L'}(G_{L'})`. -/

section LGTateBridgeKSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **Glue piece TB-iii with the kernel clause (GLUE, proved below: `scalarTransferK`).**
unram-tate's `ScalarTransfer` (statement copied) with the extra output `γ(σ) = 1 ⟹ β(σ) = a(σ)`:
the transfer of the scalars into `ℚ̄_ℓ` is injective on the values of `β/a`. -/
def ScalarTransferK : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (ℓ : ℕ) [Fact ℓ.Prime] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ),
    (∀ σ τ, d σ τ ≠ 0) →
    (∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
    (∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ)) →
    (∀ σ, 0 < a σ) →
    (∀ σ, ∀ k ∈ GQL L', a (σ * k) = a σ ∧ β (σ * k) = β σ) →
    (∀ k ∈ GQL L', a k = 1 ∧ β k = 1) →
    ∃ gam : GQ → PadicAlgCl ℓ, (∀ σ, gam σ ≠ 0) ∧
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ)) ∧
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) ∧ (∀ k ∈ GQL L', gam k = 1) ∧
      (∀ σ, gam σ = 1 → (β σ : ℂ) = ((a σ : ℝ) : ℂ))

/-- **`ScalarTransferK`, proved** (unram-tate's `scalarTransfer`, proof copied, plus the kernel
clause from the injectivity of `ψ`). -/
theorem scalarTransferK : ScalarTransferK := by
  intro L' _ _ ℓ _ a β ε n d hd hna hβe ha0 hcos hone
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) / ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hgcos : ∀ σ, ∀ k ∈ GQL L', gC (σ * k) = gC σ := by
    intro σ k hk; simp only [gC]; rw [(hcos σ k hk).1, (hcos σ k hk).2]
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  let F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range gC)
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x ⟨σ, rfl⟩; exact halg σ)
  let ψ : F →ₐ[ℚ] PadicAlgCl ℓ := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ => IntermediateField.subset_adjoin ℚ _ ⟨σ, rfl⟩
  let gam : GQ → PadicAlgCl ℓ := fun σ => ψ ⟨gC σ, hmem σ⟩
  refine ⟨gam, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    have : (⟨gC σ, hmem σ⟩ : F) = 0 := ψ.toRingHom.injective (h0.trans (map_zero ψ).symm)
    exact congrArg Subtype.val this
  · intro σ τ
    have hF : (⟨gC σ, hmem σ⟩ : F) * ⟨gC τ, hmem τ⟩ =
        algebraMap ℚ F (q σ τ) * ⟨gC (σ * τ), hmem (σ * τ)⟩ := Subtype.ext (hq σ τ)
    show ψ _ * ψ _ = _ * ψ _
    rw [← map_mul, hF, map_mul, AlgHom.commutes]
    congr 1
    simp only [q, map_div₀, map_intCast]
  · intro σ k hk
    exact congrArg ψ (Subtype.ext (hgcos σ k hk))
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))
  · intro σ h1
    have hF : (⟨gC σ, hmem σ⟩ : F) = 1 := ψ.toRingHom.injective (h1.trans (map_one ψ).symm)
    have hg : gC σ = 1 := congrArg Subtype.val hF
    have h2 := (div_eq_one_iff_eq (ha0' σ)).mp hg
    exact h2

set_option maxHeartbeats 1000000 in
/-- **`TateBridgeK` from the five glue pieces, with `ScalarTransferK` (proved)**: unram-tate's
`tateBridge_of_pieces` (proof copied verbatim up to the final `refine`), plus the kernel-field
clause. -/
theorem tateBridgeK_of_piecesK (hP : TatePoints) (hE : EndBaseChange) (hS : ScalarTransferK)
    (hC : TateCont) (hR : ResQEmbedding) : LGKerWild.TateBridgeK := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank ℓ _
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, -⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(hE K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := hP L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gam, hgam0, hgamc, hgamcos, hgam1, hgamK⟩ := hS L' ℓ a β ε n d hd hna hβe ha0
    (fun σ k hk => ⟨(haL σ k (hLL'G k hk)).2.1, by
      have := hβe σ k
      rw [hβL' k hk, _root_.mul_one, eps_right_one L ε hεc hinf h11 σ k (hLL'G k hk),
        _root_.one_mul] at this
      exact this.symm⟩)
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  -- notation
  let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
  let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
  have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
    show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
    group
  let m' : GQ → AddMonoid.End (PtQ L A) := m
  let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
  let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
    ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
  let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
  let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
  -- matrix units
  let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
  have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
    rw [← map_mul, iO_sq, map_add, map_one, two_smul]
  have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
    rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
    module
  have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
    rw [← map_mul, iO_jO, map_neg, map_mul]
  obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
  have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
    intro g o
    apply Commute.map _ R
    exact hmEnd (cj g) (iot o)
  -- the relations
  have hT : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
    intro g g₂
    have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
      hnd (cj g) (cj g₂)
    have h1 := congrArg R h0
    rw [map_zsmul, map_zsmul, ← hcj] at h1
    have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
      show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
      rw [← map_mul]; exact h1
    have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
        (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
      (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
        (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
    have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
    show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
    rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
    intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
  have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
    intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
  have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
  -- `G_{L'}` is normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  have hTres : ∀ σ : Field.absoluteGaloisGroup L',
      Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
    intro σ
    have hτ := hres σ
    let σ' : Qbar ≃ₐ[L] Qbar :=
      AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
        (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
    have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
    rw [tate_eq_opV]
    show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
    congr 1
    refine DFunLike.ext _ _ fun x => ?_
    show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
    rw [hm]
    show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
    rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
  have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
      GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
    intro σ
    unfold GlueDescent.rho
    rw [hTres σ]
    simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
  refine ⟨Tm, c', c', a', β', uu, ⟨_hdim, _hrank, hT, ha, hβ, hβ0,
    fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
    fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩, ?_⟩
  -- continuity
  intro f v
  rw [continuous_iff_continuousAt]
  intro g₀
  let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
  have he₀ : Topology.IsOpenEmbedding e₀ :=
    (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
  have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
  have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
      fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
    funext σ
    simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
    rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hT ha hβ hβ0, hrho1, Module.End.mul_apply]
  have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
    rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
  rw [he₀.continuousAt_iff, he₀1] at hc
  exact hc
  -- the kernel-field clause (lg-kerwild)
  intro g hgL hg1
  have hgL' : g ∈ GQL L := mem_GQL.mpr (fun x hx => hgL x hx)
  have hnormL : (L.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hcjL : cj g ∈ GQL L := hnormL.conj_mem _ hgL' h
  have haone : a (cj g) = 1 := (haL 1 (cj g) hcjL).1
  have hβC : (β (cj g) : ℂ) = 1 := by
    rw [hgamK (cj g) hg1, haone, Complex.ofReal_one]
  have hβ1 : β (cj g) = 1 := Units.ext (by rw [hβC, Units.val_one])
  have hcjL' : cj g ∈ GQL L' := (hL' (cj g)).mpr ⟨hcjL, hβ1⟩
  have hgL'' : g ∈ L'.fixingSubgroup := by
    have h4 : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ ∈ L'.fixingSubgroup := hnorm.conj_mem _ hcjL' h⁻¹
    have e : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g := by group
    rwa [e] at h4
  rw [RQ.resQ_range L']
  exact hgL''

/-- **`TateBridgeK` from the leaf I3.M0 alone (proved)**: g0-mod-field's `TateBridge` with the
kernel-field clause `KerWild L' β' L` in its output (lg-kerwild's correction of local-glue finding
G8), by unram-tate's construction (`tatePoints`, `endBaseChange`, `tateCont_of_tateModuleFree`,
`resQEmbedding`) and `scalarTransferK`. -/
theorem tateBridgeK_of_tateModuleFree (hT : PkgI3.TateModuleFree) : LGKerWild.TateBridgeK :=
  tateBridgeK_of_piecesK tatePoints endBaseChange scalarTransferK
    (tateCont_of_tateModuleFree hT) resQEmbedding

end UnramTate

/-- **`TateBridge35K` from I3.M0 and frob-trace's `AlgFrobRed` (proved)**: frob-trace's
`tateBridge35_of_algFrobRed` composed with `tateBridge35K_of_35`. -/
theorem LGKerWild.tateBridge35K_of_algFrobRed (hT : PkgI3.TateModuleFree)
    (hR : FrobTrace.AlgFrobRed) : LGKerWild.TateBridge35K :=
  LGKerWild.tateBridge35K_of_35 (FrobTrace.tateBridge35_of_algFrobRed hT hR)

end LGTateBridgeKSec


/-! ## lg-kerwild §6: `LocalGlue` on the data of `TateBridgeK`, every coefficient prime `ℓ` -/

section LGFinalSec

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField

namespace LGKerWild

/-- **`LocalGlue` from `G7Out` on `A_{L'}`, `KerWild` and `G7Clauses` (proved).** For a model
`A/L` with `L ≤ L'` finite Galois, `G7Out` at `ℓ` for `A_{L'}` (base change along `incAlg`, as in
`TateBridge`), the kernel-field clause and G7's clauses: `LocalGlue` at every `p ≠ ℓ`, from R6,
I2-Tors and `UnramRoots`. `DescentPts` is discharged by `descentPts_of_g7`. -/
theorem localGlue_of_kerWild (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {L L' : IF} [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [FiniteDimensional ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a β' : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu)
    (hK : @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L)
    (hCl : G15Ram.G7Clauses β' ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a β' L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hCl hK
    (fun _ => descentPts_of_g7 hLL' A hdim)

/-- **`TateBridgeK`'s data satisfy `LocalGlue` given G7's clauses (proved).** For G7's data,
`dim A_{L'} = 2`, `rank End(A_{L'}) = 4` and every coefficient prime `ℓ`, there are operator data
with `G7Out` at `ℓ` such that `G7Clauses β' ε' L` gives `LocalGlue p Tm a β' L` at every `p ≠ ℓ`,
from R6, I2-Tors and `UnramRoots`. No `KerWild` or `DescentPts` hypothesis. -/
theorem exists_localGlue_of_tateBridgeK (hB : TateBridgeK) (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ → G15Ram.G7Clauses β' ε' L →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β' L := by
  obtain ⟨Tm, c, ε', a, β', uu, h7, hK⟩ := hB u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, fun p hp hpℓ hCl => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact localGlue_of_kerWild hR6 hTors (hU p ℓ) hpℓ hLL' A h7 hK hCl

/-- **The same from the leaf I3.M0 (proved)**: `TateBridgeK` is `tateBridgeK_of_tateModuleFree`. -/
theorem exists_localGlue_of_tateModuleFree (hT : PkgI3.TateModuleFree)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ → G15Ram.G7Clauses β' ε' L →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β' L :=
  exists_localGlue_of_tateBridgeK (UnramTate.tateBridgeK_of_tateModuleFree hT) hR6 hTors hU
    u P L A ε N χ β L' hLL' hD hdim hrk ℓ

end LGKerWild

end LGFinalSec

-- END

/-! # lt-local, part 1: a field isomorphism `ℂ ≃ ℚ̄_ℓ` extending two given embeddings of `ℚ̄`

`exists_equiv_extending ιC j`: for embeddings `ιC : ℚ̄ → ℂ` and `j : ℚ̄ → ℚ̄_ℓ` there is a ring
isomorphism `Φ : ℂ ≃+* ℚ̄_ℓ` with `Φ ∘ ιC = j` (both fields are algebraically closed over `ℚ̄`
with transcendence bases of cardinality `𝔠`; Mathlib's `IsAlgClosure.equivOfEquiv` applied to the
`ℚ̄`-algebra isomorphism of the two polynomial rings on the bases). It transports `G7Data`'s
`ℂ^×`-valued cochain `β = ιC ∘ β_ℚ̄` to `j ∘ β_ℚ̄`, as `G7Clauses` asks.

`padic_card_le` and `padicAlgCl_card` are copied verbatim from g8-tate's `part_tools.lean`
(namespace `G8Tate`, renamed here to `LTLocal` to avoid a clash at integration). -/

noncomputable section

namespace LTLocal

open Cardinal LadicCond

/-- (copied from g8-tate) `#ℚ_p ≤ 𝔠`. -/
theorem padic_card_le (p : ℕ) [Fact p.Prime] : #ℚ_[p] ≤ 𝔠 := by
  have hex : ∀ x : ℚ_[p], ∀ n : ℕ, ∃ r : ℚ, ‖x - r‖ < 1 / ((n : ℝ) + 1) :=
    fun x n => Padic.rat_dense p x (by positivity)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hpos)
    have h1 := hf x n
    have h2 := hf y n
    rw [hxy] at h1
    have h3 : ‖x - y‖ ≤ ‖x - (f y n : ℚ_[p])‖ + ‖y - (f y n : ℚ_[p])‖ := by
      calc ‖x - y‖ = ‖(x - (f y n : ℚ_[p])) - (y - (f y n : ℚ_[p]))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  calc #ℚ_[p] ≤ #(ℕ → ℚ) := mk_le_of_injective hinj
    _ = 𝔠 := by
      rw [← power_def, Cardinal.mkRat, mk_nat, aleph0_power_aleph0]

/-- (copied from g8-tate) `#ℚ̄_ℓ = 𝔠`. -/
theorem padicAlgCl_card (ℓ : ℕ) [Fact ℓ.Prime] : #(PadicAlgCl ℓ) = 𝔠 := by
  apply le_antisymm
  · calc #(PadicAlgCl ℓ) ≤ max #ℚ_[ℓ] ℵ₀ :=
          Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[ℓ] (PadicAlgCl ℓ)
      _ ≤ 𝔠 := max_le (padic_card_le ℓ) aleph0_le_continuum
  · calc 𝔠 ≤ #ℚ_[ℓ] := continuum_le_cardinal_of_nontriviallyNormedField _
      _ ≤ #(PadicAlgCl ℓ) := mk_le_of_injective (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- `ℚ̄` is countable. -/
theorem qbar_card_le : #PkgI4.Qbar ≤ ℵ₀ := by
  calc #PkgI4.Qbar ≤ max #ℚ ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max ℚ PkgI4.Qbar
    _ = ℵ₀ := by rw [Cardinal.mkRat, max_self]

/-- **Two algebraically closed fields of cardinality `𝔠` containing `ℚ̄` are isomorphic over
`ℚ̄` (proved).** Stated for the `ℚ̄`-algebra structures given by `ι` and `j`. -/
theorem exists_equiv_extending_aux {K M : Type} [Field K] [Field M] [IsAlgClosed K]
    [IsAlgClosed M] (ι : PkgI4.Qbar →+* K) (j : PkgI4.Qbar →+* M) (hK : #K = 𝔠) (hM : #M = 𝔠) :
    ∃ Φ : K ≃+* M, ∀ x, Φ (ι x) = j x := by
  letI : Algebra PkgI4.Qbar K := ι.toAlgebra
  letI : Algebra PkgI4.Qbar M := j.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis PkgI4.Qbar K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis PkgI4.Qbar M
  have hc : ℵ₀ < 𝔠 := aleph0_lt_continuum
  have hs' : #K = #s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs qbar_card_le
      (hK ▸ hc)
  have ht' : #M = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht qbar_card_le
      (hM ▸ hc)
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.mp (by rw [← hs', ← ht', hK, hM])
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : s → K)) ≃ₐ[PkgI4.Qbar]
      Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : t → M)) :=
    (hs.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv PkgI4.Qbar e)).trans ht.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K M e'.toRingEquiv, fun x => ?_⟩
  have h1 : ι x = algebraMap (Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : s → K))) K
      (algebraMap PkgI4.Qbar _ x) := rfl
  rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
  show algebraMap _ M (e' (algebraMap PkgI4.Qbar _ x)) = j x
  rw [AlgEquiv.commutes]
  rfl

/-- **`ℂ ≃+* ℚ̄_ℓ` extending given embeddings of `ℚ̄` (proved).** -/
theorem exists_equiv_extending {ℓ : ℕ} [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ Φ : ℂ ≃+* PadicAlgCl ℓ, ∀ x, Φ (ιC x) = j x :=
  exists_equiv_extending_aux ιC.toRingHom j.toRingHom mk_complex (padicAlgCl_card ℓ)

end LTLocal

end

/-! # lt-local, part 2: `G7Clauses` and `dim A_{L'} = 2` for `TateBridge35`'s transported data

* `g7Clauses_of_transport`: local-data's `G7Clauses (j ∘ β_ℚ̄) ε' L` from `G7Data`, the bound
  `[L:ℚ] ≤ D` (local-data's finding F3: `G7Data` does not carry it), `ιC ∘ β_ℚ̄ = β` and
  `∂(j ∘ β_ℚ̄) = ε'` (both in `TateBridge35`'s output). The `ℂ^×`-valued clauses are carried to
  `ℚ̄_ℓ` by a field isomorphism `Φ : ℂ ≃ ℚ̄_ℓ` with `Φ ∘ ιC = j` (part 1), so that
  `j ∘ β_ℚ̄ = Φ ∘ β`; `ε' = 1` on `G_L × G_L` because `ε = 1` there (`DescentDatum`) and
  `j ∘ β_ℚ̄` has no zero. The proof of the clauses for `Φ ∘ β` follows g8-tate's
  `g7Clauses_of_g7Data` (copied, with `ε'` in place of `Φ ∘ ε`).
* `dim_bc_of_g7Data`: `dim A_{L'} = 2` from `G7Data`'s last clause `IsModelOver L' A_{L'} P`,
  `P.surface` and g0-dim's `pkgI3_dim_baseChange` (the proof of g0-split's `model_dim`). -/

noncomputable section

namespace LTLocal

open PkgI4 (GQ GQp decomp)
open LadicCond G0ModField
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent.B2
open CategoryTheory AlgebraicGeometry

/-- (copied from g8-tate) `T u` consists of primes. -/
theorem T_prime (u : ℚ) : ∀ q ∈ T u, q.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  intro q hq
  rcases Finset.mem_union.mp hq with h | h
  · exact hS q h
  · exact Nat.prime_of_mem_primeFactors h

/-- **`G7Clauses` for the transported cochain `j ∘ β_ℚ̄` (proved).** -/
theorem g7Clauses_of_transport {ℓ : ℕ} [Fact ℓ.Prime] {u : ℚ}
    {P : QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (hC : ∀ g, ιC (βQ g) = (β g : ℂ)) {ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ}
    (hε' : ∀ g h, j (βQ g) * j (βQ h) = ε' g h * j (βQ (g * h))) :
    G15Ram.G7Clauses (fun g => j (βQ g)) ε' L := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_extending ιC j
  have hjβ : ∀ g, j (βQ g) = Φ (β g : ℂ) := fun g => by rw [← hC, hΦ]
  have hne : ∀ g, Φ (β g : ℂ) ≠ 0 := fun g => (map_ne_zero Φ).mpr (Units.ne_zero _)
  obtain ⟨-, hDD, -, -, ⟨Tm, hTmT, hN⟩, hβlc, hβsq, hβε, -⟩ := h
  have hfun : (fun g => j (βQ g)) = fun g => Φ (β g : ℂ) := funext hjβ
  refine ⟨inferInstance, hLD, hε', fun g => by simp only [hjβ]; exact hne g, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hβlc.comp (fun z : ℂˣ => Φ (z : ℂ))
  · have hT : ∀ q ∈ Tm, q.Prime := fun q hq => T_prime u q (hTmT hq)
    subst hN
    refine ⟨Tm, hT, inferInstance, χ, Units.map Φ.toRingHom.toMonoidHom, fun g => ?_⟩
    show j (βQ g) ^ 2 = Φ ((GlueDescent.B2Q.galChar χ g : ℂˣ) : ℂ)
    rw [hjβ, ← map_pow, ← Units.val_pow_eq_pow_val, hβsq g]
  · intro g h hg _
    obtain ⟨hε, hinf, h11, -⟩ := hDD
    have h1 := GlueDescent.B3Q.inflatedNormalized_of L ε hε hinf h11 g h
      (Or.inl (GlueDescent.B3Q.mem_GQL.mpr hg))
    have h2 := hβε g h
    rw [h1, one_mul] at h2
    have h3 := hε' g h
    rw [hjβ, hjβ, hjβ, ← map_mul, ← Units.val_mul, h2] at h3
    exact mul_right_cancel₀ (hne (g * h)) (h3.symm.trans (one_mul _).symm)

/-- **`dim A_{L'} = 2` on G7's data (proved)**: G7Data's clause `IsModelOver L' A_{L'} P`,
`P.surface` and g0-dim's `pkgI3_dim_baseChange` (as g0-split's `model_dim`). -/
theorem dim_bc_of_g7Data {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL') :
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := by
  -- `first`: G7Data's model clause is its last (g0-assemble2) or second-to-last (g0-assemble3)
  have hm : IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P := by
    first
    | exact h.2.2.2.2.2.2.2.2.2.2.2
    | exact h.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨e⟩ := hm
  rw [← G0Dim.pkgI3_dim_baseChange Qbar (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')),
    ← P.surface]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso ((Over.forget _).mapIso e)).isHomeomorph

end LTLocal

end

/-! # lt-local, part 3: verbatim copies from `scratch/g0-assemble2/G0Assemble2.lean`

* `G0ModNewform.Vb` (G0Assemble2.lean l.41358-41360, g0-mod-newform §9's copy of g0-mod-galois'
  `Vb`; the base environment has `G0Galois.Vb` and `GaloisCopy.Vb`, the same `abbrev`);
* g14-trace's `G14Trace.FrobTraceLink` with its namespace header (l.62238-62242, l.62356-62373);
* g0-assemble2's `HSyn.G0AssembleMod.LinkedTateLocal` with its namespace header
  (l.63903-63947; GLUE field 39 of `GluePieces3`).
The rest of what these depend on (`G0Galois.G7Out`, `G0Galois.G8Out`, `G0Galois.Vb`,
`GlueDescent.rho`, `G15Ram.LocalData`, `G0ModField.G7Data`, `FibreCtx`, `incAlg`,
`numberField_of_fd`, `GlueC10Link.FrobCompare`) is in the base environment (lg-kerwild's
`KerWild.lean`, itself verbatim copies of the same sources). -/

noncomputable section

namespace G0ModNewform

end G0ModNewform

namespace G14Trace

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open PkgI3 G0ModNewform GlueC10Link


/-- **The Frobenius trace link (GLUE, AV side; N5 L781-786).** There is a finite set `S` of
primes such that at every arithmetic Frobenius `τ` above `p ∉ S` there are an abelian variety
`Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and `N ≠ 0` with
`FrobCompare` (kernel, `GlueC10Link`) at `ℓ = 3` and at `ℓ = 5`: some isomorphism
`ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ ⊗ V_ℓ(Ā)` carries `N·Tm_ℓ(τ)` to `V_ℓ(α')`. In N5, `S = T ∪ {3, 5}`
(`T` = bad primes of `A/L'`), `Ā` is the reduction of `A` at the place `v ∩ L'`, `α' = N·(μ̄_τ ∘ F)`
(relative `p`-Frobenius `F`, reduction `μ̄_τ` of the isogeny `μ_τ : {}^τA → A`, defined over
`L ⊆ L'` by N5 L638-640), and the
isomorphism is the Serre–Tate reduction isomorphism. It concerns the operators `Tm_ℓ` that
g0-mod-field's `TateBridge` builds from the points-level `m_σ = μ_σ ∘ σ` (one `m_σ` for all `ℓ`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N


end G14Trace

end

noncomputable section

-- Name resolution of `Qbar`, `GQ` in `LinkedTateLocal`: here through the section-level opens of
-- G0Assemble2.lean's `section G0A2_a85_linked` (l.61787-61789, which open `GlueC10`); every
-- candidate (`GlueC10.Qbar`, `PkgI4.Qbar`, ... ) is a reducible `abbrev` of `AlgebraicClosure ℚ`,
-- and `GQ` of `Qbar ≃ₐ[ℚ] Qbar`, so the statement is the same term up to reducible unfolding.
open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

end HSyn.G0AssembleMod

end

/-! # lt-local, part 4: `LinkedTateLocal` on `TateBridge35`'s data

* `LinkedTateLocalD` (the corrected statement): g0-assemble2's `LinkedTateLocal` with the premise
  `[L:ℚ] ≤ D` added (as g8-object's `LinkedTateDataD` adds it to `LinkedTateData`).
* `ModelEndRank4` (GLUE, named here): `rank_ℤ End(A_{L'}) = 4` on G7's model. It is
  `TateBridge35`'s second hypothesis, and a consequence of `LinkedTateLocal` itself (its `G7Out`
  contains it), so it costs no truth.
* `localGlue_at`: lg-kerwild's `localGlue_of_transport`, with `UnramRoots p ℓ` needed only at
  `p = 2` (its proof, through local-glue's `localGlue_of_descent`).
* **`linkedTateLocalD_of_tateBridge35`**: R6 + I2-Tors + `UnramRoots 2 5` + `UnramRoots 2 3` +
  `TateBridge35` + `ModelEndRank4` ⟹ `LinkedTateLocalD`.
* `linkedTateLocal_of_D`: `LinkedTateLocalD` + `G7DegreeBound` ⟹ `LinkedTateLocal` (trivial;
  shows what the unrestricted statement would need). -/

noncomputable section

-- the section-level opens of G0Assemble2.lean's `section G0A2_a85_linked`, as for the copy
open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct

namespace LTLocal

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue (G5-G6 on G7's model, N5 L528-563): the endomorphism ring of `A_{L'}` has rank 4.**
For every fibre context and G7 data, `rank_ℤ End(A_{L'}) = 4`. Proof plan (not formalized):
`≥ 4` from the QM structure `ι : 𝒪 → End(PK.A)` of `IsQMModel`, base-changed to `L'` (unram-tate's
`endBaseChange`; `𝒪` has rank 4 and `ι` is injective because `[n] ≠ 0`, cf. g0-assemble2's
`modelNoncomm_of_mulIsogeny`); `≤ 4` from `End(A_{L'})` a division-ring order (g0-split's
`FibreSimple`, already in `GluePieces3` through FS5) and Albert's bound `[End⁰(A):ℚ] ≤ 2g` for a
simple abelian variety in characteristic `0` (Mumford, *Abelian Varieties*, §21; locator
UNVERIFIED). This is `TateBridge35`'s (and g0-mod-field's `TateBridge`'s) second hypothesis. -/
def ModelEndRank4 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4

/-- **G4's degree bound on G7's data (GLUE, N5 L532-563).** `[L:ℚ] ≤ D` for every G7 datum in a
fibre context. g0-mod-field's `G4Out` carries this bound but its `G7Data` does not (local-data's
finding F3); `G7Data` admits fields `L` larger than G4's Hom field, so this Prop is not expected to
hold as stated (SPECULATIVE). It is named only to record what the unrestricted
`LinkedTateLocal` would need on this route; the fix is to add the bound to `G7Data`
(`LinkedTateLocalD`). -/
def G7DegreeBound : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' → Module.finrank ℚ L ≤ ZInQ.heightD

/-- **Glue (corrected `LinkedTateLocal`, for `GluePieces4`):** the text of g0-assemble2's
`HSyn.G0AssembleMod.LinkedTateLocal` (GLUE field 39 of `GluePieces3`) with the premise
`Module.finrank ℚ L ≤ ZInQ.heightD` added after `G7Data`. The local data at `p > D` (tame
closure of `L_v`) and the `G7Clauses` used at every `p` need this bound (N5 L848-851:
`[L_v:ℚ_p] ≤ D < p`). Proved from `TateBridge35`, `ModelEndRank4` and leaves
(`linkedTateLocalD_of_tateBridge35`). -/
def LinkedTateLocalD : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℚ L ≤ ZInQ.heightD →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ (fun g => j5 (aQ g)) (fun g => j5 (βQ g))) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ (fun g => j3 (aQ g)) (fun g => j3 (βQ g))) r₃ →
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ r₅) ∧
          G15Ram.LocalData 5 r₃

/-- **lg-kerwild's `localGlue_of_transport` with `UnramRoots` only at `p = 2` (proved; its proof,
through local-glue's `localGlue_of_descent`).** -/
theorem localGlue_at (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : p = 2 → G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a
        (fun g => j (βQ g)) uu)
    (hCl : G15Ram.G7Clauses (fun g => j (βQ g)) ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => j (βQ g)) L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_descent hR6 hTors hpℓ h7 hCl
    (LGKerWild.kerWild_of_g7Data_alg hD βQ j ιC hC)
    (fun _ => LGKerWild.descentPts_of_g7 hLL' A hdim)
    (fun h2 => G15Ram.betaTwist2_of_unramRoots h2 hCl (hU h2))

/-- **`LinkedTateLocalD` from `TateBridge35` (proved).** Inputs: the leaves R6
(`ObjBridge.RaynaudCriterion`) and I2-Tors (`ObjBridge.TorsionStructure`); local-glue's textbook
Prop `UnramRoots` at `p = 2` for `ℓ = 5, 3`; g14-trace's glue `TateBridge35`; the glue
`ModelEndRank4`. Steps: `dim A_{L'} = 2` (`dim_bc_of_g7Data`) and `ModelEndRank4` feed
`TateBridge35`; its output gives `G7Out` at 5 and 3, `FrobTraceLink` and `ιC ∘ βQ = β`;
`G7Clauses` for `j_ℓ ∘ βQ` (`g7Clauses_of_transport`, with `[L:ℚ] ≤ D`); `LocalGlue` at `p ≠ ℓ`
(`localGlue_at`: lg-kerwild's `KerWild` and `DescentPts` discharges); `LocalData` for every `r_ℓ`
with G8's output (local-data's `localData_of_g7`). -/
theorem linkedTateLocalD_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35) (hRk : ModelEndRank4) :
    LinkedTateLocalD := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD hLD
  letI : NumberField L' := numberField_of_fd L'
  have hdim := dim_bc_of_g7Data hD
  have hrk := hRk Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    hB u P L A ε N χ β L' hLL' hD hdim hrk
  have hCl5 := g7Clauses_of_transport hD hLD βQ j5 ιC hC h5.2.2.2.2.1
  have hCl3 := g7Clauses_of_transport hD hLD βQ j3 ιC hC h3.2.2.2.2.1
  refine ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF,
    fun r5 r3 h85 h83 => ⟨fun p hp hp5 => ?_, ?_⟩⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact G15Ram.localData_of_g7 h85 hCl5
      (localGlue_at hR6 hTors (fun h2 => by subst h2; exact hU5) hp5 hD βQ j5 ιC hC h5 hCl5)
  · exact G15Ram.localData_of_g7 h83 hCl3
      (localGlue_at hR6 hTors (fun h2 => absurd h2 (by norm_num)) (by norm_num) hD βQ j3 ιC hC
        h3 hCl3)

/-- `LinkedTateLocalD` and `G7DegreeBound` give g0-assemble2's `LinkedTateLocal` (proved,
trivially). -/
theorem linkedTateLocal_of_D (h : LinkedTateLocalD) (hB : G7DegreeBound) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD (hB Y Φ π u P hctx L A ε N χ β L' hLL' hD)

/-- The unrestricted Prop gives the restricted one (proved, trivially). -/
theorem linkedTateLocalD_of_local (h : HSyn.G0AssembleMod.LinkedTateLocal) : LinkedTateLocalD :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD _ =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD

/-- `ModelEndRank4` follows from `LinkedTateLocal` (its `G7Out` at `5` contains the rank), so
naming it costs no truth (proved). -/
theorem modelEndRank4_of_localD (h : LinkedTateLocalD) (hB : G7DegreeBound) :
    ModelEndRank4 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, -⟩ :=
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD (hB Y Φ π u P hctx L A ε N χ β L' hLL' hD)
  exact h5.2.1

end LTLocal

end

/-! # lt-local, part 5: `ModelEndRank4` from `FibreSimple` and linked-tate's `QMEndRank`

Verbatim copies from `scratch/linked-tate/LinkedTate.lean` (with their namespace headers and opens):
* def-faltings' `ZInQ.DefFaltings.AbVar`, `AbVar.baseChange` (l.17119, l.18210-18236);
* leaf-adopt's `LeafAdopt.abVarEquiv` (l.19042-19045, l.19196-19201);
* g0-split's `HSyn.G0Split.FibreOver` and `FibreSimple` (l.33338-33340, l.33577-33590,
  l.33712-33722; `FibreSimple` is the existing `GluePieces` piece, supplied in `GluePieces3`
  through FS5);
* linked-tate's `HSyn.LinkedTate.QMEndRank` (l.42841-42844, l.43121-43135; GLUE, literature-backed:
  Mumford §19 Thm 3 and Albert's classification, §21, numbering UNVERIFIED).
New: `endDivision_of_fibreSimple` (linked-tate's proof, copied) and `modelEndRank4_of_qmEndRank`
(the argument of linked-tate's `linkedTateCore_of`). -/

noncomputable section

namespace ZInQ.DefFaltings

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

end ModelsSec

end ZInQ.DefFaltings

namespace LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

end LeafAdopt

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

end G0Split

end HSyn

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

end HSyn.LinkedTate

namespace LTLocal

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- (copied from linked-tate; `Qbar` written `PkgI4.Qbar`) **`EndDivision` for every number-field model of the fibre, from the
glue piece `FibreSimple`** (proved). -/
theorem endDivision_of_fibreSimple (hFS : HSyn.G0Split.FibreSimple)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : LeafQM.AV.PtEquiv Y} {π : LeafQM.AV.ToP1 Y.left} {u : ℚ}
    {P : LeafQM.AV.QML3 PkgI4.Qbar} (hctx : FibreCtx Y Φ π u P) (L' : IF)
    [FiniteDimensional ℚ L'] (A' : PkgI3.AbVar L') (hA' : IsModelOver L' A' P) :
    PkgI3.EndDivision A' := by
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  haveI : NumberField L' := numberField_of_fd L'
  exact hFS Y Φ π h1 h2 u hu ⟨L'⟩ ((LeafAdopt.abVarEquiv L').symm A')
    ⟨algebraMap L' PkgI4.Qbar, y, P, hy, hπ, hA'⟩

/-- **`ModelEndRank4` from `FibreSimple` and `QMEndRank` (proved;** the argument of linked-tate's
`linkedTateCore_of`): G7Data's `IsQMModel` writes `A = (PK.A)_L`, its last clause gives
`EndDivision A_{L'}` through `FibreSimple`, and `QMEndRank` gives the rank. -/
theorem modelEndRank4_of_qmEndRank (hFS : HSyn.G0Split.FibreSimple)
    (hR : HSyn.LinkedTate.QMEndRank) : ModelEndRank4 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  have hmod : IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P := by
    first
    | exact hdata.2.2.2.2.2.2.2.2.2.2.2
    | exact hdata.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  exact hR K L L' hKL hLL' PK (endDivision_of_fibreSimple hFS hctx L' _ hmod)

/-- **`LinkedTateLocalD` from `TateBridge35`, `FibreSimple` and `QMEndRank` (proved).** -/
theorem linkedTateLocalD_of_tateBridge35' (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) : LinkedTateLocalD :=
  linkedTateLocalD_of_tateBridge35 hR6 hTors hU5 hU3 hB (modelEndRank4_of_qmEndRank hFS hR)

end LTLocal

end


/-! # lt-local, part 6 (GluePieces4 variant): `LinkedTateLocal` itself, over g0-assemble3's `G7Data`

Compiled only in the variant `LtLocal4.lean` (`build4.sh`), whose base `Base4.lean` is
`Base.lean` with g0-assemble3's fix of `G0ModField.G7Data` (the clause `[L:ℚ] ≤ D` appended,
`scratch/g0-assemble3/parts/75_modfield.lean`) and its three proof adjustments, ported by
`mk_base4.py`. Over that `G7Data`, `G7DegreeBound` is a projection, and g0-assemble2's
`LinkedTateLocal` (GLUE field 39, statement unchanged) is proved. -/

noncomputable section

namespace LTLocal

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **`G7DegreeBound` over g0-assemble3's `G7Data` (proved: its last clause).** -/
theorem g7DegreeBound_gp4 : G7DegreeBound := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  exact hD.2.2.2.2.2.2.2.2.2.2.2.2

/-- **g0-assemble2's `LinkedTateLocal` (GLUE field 39), over g0-assemble3's `G7Data` (proved)**
from the leaves R6 and I2-Tors, local-glue's textbook Prop `UnramRoots` at `p = 2` for `ℓ = 5, 3`,
g14-trace's glue `TateBridge35`, g0-split's `FibreSimple` and linked-tate's `QMEndRank`. -/
theorem linkedTateLocal_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  linkedTateLocal_of_D (linkedTateLocalD_of_tateBridge35' hR6 hTors hU5 hU3 hB hFS hR)
    g7DegreeBound_gp4

/-- The same with `TateBridge35` from frob-trace's reduction (`FrobTrace.tateBridge35_of_algFrobRed`:
the leaf I3.M0 `PkgI3.TateModuleFree` and the glue `FrobTrace.AlgFrobRed`). -/
theorem linkedTateLocal_of_algFrobRed (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hT : PkgI3.TateModuleFree) (hA : FrobTrace.AlgFrobRed)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  linkedTateLocal_of_tateBridge35 hR6 hTors hU5 hU3 (FrobTrace.tateBridge35_of_algFrobRed hT hA)
    hFS hR

end LTLocal

end



/-! ## leaf-fold3: scratch/unram-roots/UnramRoots.lean, declarations already in the chain dropped -/


/-! # unram-roots, step 1: `UnramRoots` from the procyclicity of `G_F / I_F` (proved)

`UnramRoots p ℓ` is copied verbatim from `scratch/local-glue/part_twist.lean` (namespace
`G15Ram`, `open PkgI4 (GQp)`, `open LadicCond`); its definitions (`GQp`, `Fld`, `fixSet`,
`inertiaSet`) are those of `ZInQKernel/HDecomp/Conductor/LadicCond.lean`, imported.

`UnramProcyclic p` (new, textbook) states that `G_F / I_F` is procyclic, topologically generated by
a Frobenius lift `φ`, in the two forms used: (F1) every `σ ∈ G_F` is `φ^k τ g` with `τ ∈ I_F` and `g`
in a given open `G_K`, and (F2) for every `n ≥ 1` there is an unramified character
`χ : G_F → ℤ/n` with `χ(φ) = 1`, trivial on an open subgroup.

`unramRoots_of_unramProcyclic` (proved, below). -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp)
open LadicCond

section TwistSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

variable (p ℓ) in
end TwistSec

end G15Ram

namespace UnramRootsTask

open PkgI4 (GQp)
open LadicCond

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- **Textbook (new): `G_F / I_F` is procyclic, topologically generated by a Frobenius lift.**
For a finite `F/ℚ_p` inside `ℚ̄_p` there is `φ ∈ G_F` such that
* (F1) for every finite `K ⊇ F`, every `σ ∈ G_F` is `φ^k τ g` with `k ∈ ℕ`, `τ ∈ G_F ∩ I` and
  `g ∈ G_K` (the image of `φ` generates the finite quotient `G_F / G_K I_F`);
* (F2) for every `n ≥ 1` there is a homomorphism `χ : G_F → ℤ/n` with `χ(φ) = 1`, trivial on
  `G_F ∩ I` and on some open `G_{K}` (the character of the unramified extension of degree `n`).
Sources: `G_F/I_F ≅ Gal(F^{ur}/F) ≅ Gal(k̄/k) ≅ Ẑ`, generated by Frobenius (Serre, *Local
Fields*, Ch. I §7 Prop. 20-21, Ch. III §5 Thm 2, Ch. XIII §1; Neukirch, *Algebraic Number Theory*,
Ch. II Prop. 9.9 and Ch. IV (1.4); locators UNVERIFIED). -/
def UnramProcyclic : Prop :=
  ∀ (F : Fld p), FiniteDimensional ℚ_[p] F → ∃ φ ∈ fixSet F,
    (∀ K : Fld p, FiniteDimensional ℚ_[p] K → F ≤ K → ∀ σ ∈ fixSet F,
        ∃ k : ℕ, ∃ τ ∈ fixSet F ∩ inertiaSet, ∃ g ∈ fixSet K, σ = φ ^ k * τ * g) ∧
    (∀ n : ℕ, 0 < n → ∃ χ : GQp p → ZMod n,
        (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, χ (σ * τ) = χ σ + χ τ) ∧ χ φ = 1 ∧
        (∀ σ ∈ fixSet F ∩ inertiaSet, χ σ = 0) ∧
        ∃ K : Fld p, FiniteDimensional ℚ_[p] K ∧ ∀ σ ∈ fixSet K, χ σ = 0)

theorem mul_mem_fixSet {F : Fld p} {σ τ : GQp p} (hσ : σ ∈ fixSet F) (hτ : τ ∈ fixSet F) :
    σ * τ ∈ fixSet F := by
  intro x hx
  rw [AlgEquiv.mul_apply, hτ x hx, hσ x hx]

theorem one_mem_fixSet (F : Fld p) : (1 : GQp p) ∈ fixSet F := fun _ _ => rfl

theorem pow_mem_fixSet {F : Fld p} {σ : GQp p} (hσ : σ ∈ fixSet F) (k : ℕ) :
    σ ^ k ∈ fixSet F := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_fixSet F
  | succ k ih => rw [pow_succ]; exact mul_mem_fixSet ih hσ

theorem fixSet_anti {F K : Fld p} (h : F ≤ K) : fixSet K ⊆ fixSet F :=
  fun _ hσ x hx => hσ x (h hx)

theorem inv_mem_fixSet {F : Fld p} {σ : GQp p} (hσ : σ ∈ fixSet F) : σ⁻¹ ∈ fixSet F := by
  intro x hx
  have h := hσ x hx
  calc σ⁻¹ x = σ⁻¹ (σ x) := by rw [h]
    _ = x := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- A multiplicative function on `G_F` is multiplicative on powers. -/
theorem map_pow_of_mul {M : Type*} [Monoid M] {F : Fld p} {f : GQp p → M}
    (hf : ∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, f (σ * τ) = f σ * f τ) (h1 : f 1 = 1)
    {σ : GQp p} (hσ : σ ∈ fixSet F) (k : ℕ) : f (σ ^ k) = f σ ^ k := by
  induction k with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, hf _ (pow_mem_fixSet hσ k) _ hσ, ih, pow_succ]

/-- Some positive power of `σ ∈ G_F` lies in `G_K` for `K` finite over `ℚ_p`. -/
theorem exists_pow_mem_fixSet {K : Fld p} (hK : FiniteDimensional ℚ_[p] K)
    {σ : GQp p} : ∃ j : ℕ, 0 < j ∧ σ ^ j ∈ fixSet K := by
  let r : ℕ → (K →ₐ[ℚ_[p]] Kbar p) := fun i => (σ ^ i : GQp p).toAlgHom.comp K.val
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite r
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨b - a, by omega, ?_⟩
    intro x hx
    have hx' := congrArg (fun f => f ⟨x, hx⟩) he
    change (σ ^ a) x = (σ ^ b) x at hx'
    have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [hb, AlgEquiv.mul_apply] at hx'
    exact (σ ^ a).injective hx'.symm
  · refine ⟨a - b, by omega, ?_⟩
    intro x hx
    have hx' := congrArg (fun f => f ⟨x, hx⟩) he
    change (σ ^ a) x = (σ ^ b) x at hx'
    have ha : σ ^ a = σ ^ b * σ ^ (a - b) := by rw [← pow_add]; congr 1; omega
    rw [ha, AlgEquiv.mul_apply] at hx'
    exact (σ ^ b).injective hx'

theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hx : x ^ n = 1) (m : ℕ) :
    x ^ (m % n) = x ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hx, one_pow, one_mul]

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`UnramRoots` from `UnramProcyclic` (proved).** -/
theorem unramRoots_of_unramProcyclic (h : UnramProcyclic p) : G15Ram.UnramRoots p ℓ := by
  intro F hF ψ hmul ⟨F'', hF'', hψ''⟩ hI
  obtain ⟨φ, hφF, hF1, hF2⟩ := h F hF
  have hψ1 : ψ 1 = 1 := hψ'' 1 (one_mem_fixSet F'')
  -- `ψ(φ)` is a root of unity
  obtain ⟨j, hj, hφj⟩ := exists_pow_mem_fixSet hF'' (σ := φ)
  have hψφj : ψ φ ^ j = 1 := by
    rw [← map_pow_of_mul hmul hψ1 hφF j]; exact hψ'' _ hφj
  obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_pow_nat_eq (ψ φ) (by norm_num : 0 < 4)
  set n := 4 * j with hn
  have hn0 : 0 < n := by omega
  have hξn : ξ ^ n = 1 := by rw [hn, pow_mul, hξ, hψφj]
  have hψφn : ψ φ ^ n = 1 := by rw [hn, mul_comm, pow_mul, hψφj, one_pow]
  obtain ⟨χ, hχmul, hχφ, hχI, Kn, hKn, hχK⟩ := hF2 n hn0
  have hχ1 : χ 1 = 0 := by
    have := hχmul 1 (one_mem_fixSet F) 1 (one_mem_fixSet F)
    rw [mul_one] at this
    exact left_eq_add.mp this
  classical
  let η : GQp p → PadicAlgCl ℓ := fun σ => if σ ∈ fixSet F then ξ ^ (χ σ).val else 1
  have hηF : ∀ σ ∈ fixSet F, η σ = ξ ^ (χ σ).val := fun σ hσ => if_pos hσ
  have hχk : ∀ k : ℕ, χ (φ ^ k) = k := by
    intro k
    induction k with
    | zero => rw [pow_zero, hχ1, Nat.cast_zero]
    | succ k ih =>
      rw [pow_succ, hχmul _ (pow_mem_fixSet hφF k) _ hφF, ih, hχφ, Nat.cast_succ]
  haveI : NeZero n := ⟨hn0.ne'⟩
  refine ⟨η, ⟨F ⊔ Kn, inferInstance, ?_⟩, ?_, ?_, ?_⟩
  · intro σ hσ
    rw [hηF σ (fixSet_anti le_sup_left hσ), hχK σ (fixSet_anti le_sup_right hσ), ZMod.val_zero,
      pow_zero]
  · intro σ hσ τ hτ
    rw [hηF _ (mul_mem_fixSet hσ hτ), hηF σ hσ, hηF τ hτ, hχmul σ hσ τ hτ, ZMod.val_add,
      pow_mod_of_pow_eq_one hξn, pow_add]
  · intro σ hσ
    let K : Fld p := F ⊔ F'' ⊔ Kn
    have hFK : F ≤ K := le_sup_left.trans le_sup_left
    obtain ⟨k, τ, ⟨hτF, hτI⟩, g, hg, rfl⟩ := hF1 K inferInstance hFK σ hσ
    have hgF : g ∈ fixSet F := fixSet_anti hFK hg
    have hg'' : g ∈ fixSet F'' := fixSet_anti (le_sup_right.trans le_sup_left) hg
    have hgn : g ∈ fixSet Kn := fixSet_anti le_sup_right hg
    have hφk := pow_mem_fixSet hφF k
    have hm1 := mul_mem_fixSet hφk hτF
    rw [hηF _ (mul_mem_fixSet hm1 hgF), hmul _ hm1 _ hgF, hmul _ hφk _ hτF,
      hχmul _ hm1 _ hgF, hχmul _ hφk _ hτF, hχI τ ⟨hτF, hτI⟩, hχK g hgn, hI τ ⟨hτF, hτI⟩,
      hψ'' g hg'', map_pow_of_mul hmul hψ1 hφF k, hχk k, add_zero, add_zero, mul_one, mul_one,
      ← pow_mul, mul_comm, pow_mul, hξ, ZMod.val_natCast, pow_mod_of_pow_eq_one hψφn]
  · intro σ hσ
    rw [hηF σ hσ.1, hχI σ hσ, ZMod.val_zero, pow_zero]

end UnramRootsTask

/-! # unram-roots, metric part: inertia and roots of unity in `ℚ̄_p` (proved)

`inertiaSet` (from `LadicCond`) is the metric inertia group: `σ ∈ G_{ℚ_p}` with `‖σx − x‖ < 1`
for all `‖x‖ ≤ 1` in `ℚ̄_p = PadicAlgCl p`.

* `fix_of_mem_inertiaSet_of_pow_eq_one`: metric inertia fixes every root of unity of order prime to
  `p` (distinct such roots are at distance `1`).
* `mem_inertiaSet_of_fix`: an element of `G_{ℚ_p}` fixing every root of `X^{p^m} − X` (`m ≥ 1`) lies
  in the metric inertia group (every `x` with `‖x‖ ≤ 1` is congruent to such a root: the residue
  of `x` is algebraic over `𝔽_p`, so a root of `X^{p^m} − X` in the residue field, and the roots of
  `X^{p^m} − X` in `ℚ̄_p` reduce onto them).
-/

noncomputable section

namespace UnramRootsTask

open PkgI4 (GQp)
open LadicCond Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem norm_aut (σ : GQp p) (x : Kbar p) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem norm_natCast_eq_one {N : ℕ} (h : ¬ p ∣ N) : ‖(N : Kbar p)‖ = 1 := by
  have e : ((N : ℚ_[p]) : Kbar p) = (N : Kbar p) := map_natCast _ N
  rw [← e, PadicAlgCl.norm_extends]
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)

theorem norm_add_le_max' (a b : Kbar p) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ :=
  IsUltrametricDist.norm_add_le_max a b

theorem norm_sub_le_max' (a b : Kbar p) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  exact (norm_add_le_max' a (-b)).trans (by rw [norm_neg])

theorem norm_sum_lt_one {ι : Type*} (s : Finset ι) (f : ι → Kbar p) (h : ∀ i ∈ s, ‖f i‖ < 1) :
    ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (norm_add_le_max' _ _).trans_lt (max_lt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A root of unity of order prime to `p` congruent to `1` is `1`. -/
theorem eq_one_of_pow_eq_one {u : Kbar p} {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (hu : u ^ N = 1)
    (h1 : ‖u - 1‖ < 1) : u = 1 := by
  by_contra hne
  have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hgeom : (∑ i ∈ Finset.range N, u ^ i) * (u - 1) = u ^ N - 1 := geom_sum_mul u N
  rw [hu, sub_self] at hgeom
  have hsum : ∑ i ∈ Finset.range N, u ^ i = 0 := (mul_eq_zero.mp hgeom).resolve_right hu1
  have hule : ‖u‖ ≤ 1 := by
    have : u = (u - 1) + 1 := by ring
    rw [this]
    exact (norm_add_le_max' _ _).trans (max_le h1.le (by rw [norm_one]))
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
      rw [this]
      refine (norm_add_le_max' _ _).trans_lt (max_lt ?_ h1)
      rw [norm_mul]
      calc ‖u‖ * ‖u ^ i - 1‖ ≤ 1 * ‖u ^ i - 1‖ :=
            mul_le_mul_of_nonneg_right hule (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact ih
  have hN1 : ‖(N : Kbar p)‖ = 1 := norm_natCast_eq_one hpN
  have : (N : Kbar p) = -∑ i ∈ Finset.range N, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  rw [this, norm_neg] at hN1
  exact absurd hN1 (norm_sum_lt_one _ _ fun i _ => hpow i).ne

/-- **Metric inertia fixes the roots of unity of order prime to `p`.** -/
theorem fix_of_mem_inertiaSet_of_pow_eq_one {σ : GQp p} (hσ : σ ∈ inertiaSet) {x : Kbar p}
    {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (hx : x ^ N = 1) : σ x = x := by
  have hxn : ‖x‖ = 1 := by
    have h := congrArg norm hx
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN.ne').mp h
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxn
  have hy : (σ x) ^ N = 1 := by rw [← map_pow, hx, map_one]
  have hclose : ‖σ x - x‖ < 1 := hσ x hxn.le
  set u := σ x * x⁻¹ with hu
  have huN : u ^ N = 1 := by rw [hu, mul_pow, inv_pow, hy, hx, inv_one, mul_one]
  have hu1 : ‖u - 1‖ < 1 := by
    have : u - 1 = (σ x - x) * x⁻¹ := by rw [hu]; field_simp
    rw [this, norm_mul, norm_inv, hxn, inv_one, mul_one]
    exact hclose
  have := eq_one_of_pow_eq_one hN hpN huN hu1
  rw [hu] at this
  exact (mul_inv_eq_one₀ hx0).mp this

/-- Metric inertia fixes the roots of `X^M − X` when `p ∣ M`, `M > 1`. -/
theorem fix_of_mem_inertiaSet_of_pow_eq_self {σ : GQp p} (hσ : σ ∈ inertiaSet) {x : Kbar p}
    {M : ℕ} (hM : 1 < M) (hpM : p ∣ M) (hx : x ^ M = x) : σ x = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact map_zero σ
  have h1 : x ^ (M - 1) = 1 := by
    have : x ^ (M - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hM.le, one_mul, hx]
    exact mul_right_cancel₀ hx0 this
  refine fix_of_mem_inertiaSet_of_pow_eq_one hσ (by omega) ?_ h1
  intro hd
  have hp1 : p ∣ M - (M - 1) := Nat.dvd_sub hpM hd
  rw [Nat.sub_sub_self hM.le] at hp1
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hp1)

/-! ### The residue field of `ℚ̄_p` -/

/-- The unit ball of `ℚ̄_p` as a valuation subring. -/
abbrev OO (p : ℕ) [Fact p.Prime] : ValuationSubring (Kbar p) :=
  (PadicAlgCl.valued p).v.valuationSubring

theorem mem_OO {x : Kbar p} : x ∈ OO p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff]
  change ‖x‖₊ ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

theorem residue_eq_zero_iff (a : OO p) :
    IsLocalRing.residue (OO p) a = 0 ↔ ‖(a : Kbar p)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change ‖(a : Kbar p)‖₊ < 1 ↔ _
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

/-- `ℤ_p → 𝒪_{ℚ̄_p}`. -/
def zpToOO (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* OO p :=
  ((algebraMap ℚ_[p] (Kbar p)).comp PadicInt.Coe.ringHom).codRestrict (OO p) (fun c => by
    rw [mem_OO]
    change ‖((c : ℚ_[p]) : Kbar p)‖ ≤ 1
    rw [PadicAlgCl.norm_extends]
    exact c.2)

theorem coe_zpToOO (c : ℤ_[p]) : ((zpToOO p c : OO p) : Kbar p) = algebraMap ℚ_[p] _ c := rfl

/-- **Every `x` with `‖x‖ ≤ 1` satisfies `‖x^{p^m} − x‖ < 1` for some `m ≥ 1`.** -/
theorem exists_pow_sub_lt_one {x : Kbar p} (hx : ‖x‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ‖x ^ p ^ m - x‖ < 1 := by
  set k := IsLocalRing.ResidueField (OO p)
  set r := IsLocalRing.residue (OO p)
  have hp : p.Prime := Fact.out
  -- `k` has characteristic `p`
  have hpk : ((p : ℕ) : k) = 0 := by
    rw [← map_natCast r p, residue_eq_zero_iff]
    change ‖((p : OO p) : Kbar p)‖ < 1
    rw [show ((p : OO p) : Kbar p) = ((p : ℚ_[p]) : Kbar p) by simp, PadicAlgCl.norm_extends,
      Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 hpk
  -- the minimal polynomial of `x` has integral coefficients
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  set g := minpoly ℚ_[p] x with hg
  have hgm : g.Monic := minpoly.monic hint
  have hcoeff : ∀ n, ‖g.coeff n‖ ≤ 1 := by
    have : spectralValue g ≤ 1 := by
      have e : spectralNorm ℚ_[p] (Kbar p) x = spectralValue g := rfl
      rw [← e, PadicAlgCl.spectralNorm_eq]; exact hx
    exact (spectralValue_le_one_iff hgm).1 this
  have hlifts : g ∈ Polynomial.lifts (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨g.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨gZ, hgZ, -, hgZm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hgm
  set ψ : ℤ_[p] →+* k := r.comp (zpToOO p)
  set gk : k[X] := gZ.map ψ
  have hgk0 : gk ≠ 0 := (hgZm.map ψ).ne_zero
  set x' : OO p := ⟨x, mem_OO.mpr hx⟩
  set y : k := r x'
  -- `y` is a root of `gk`
  have hroot : gk.eval y = 0 := by
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ (r.comp (zpToOO p)) (r x') gZ = 0
    rw [← Polynomial.hom_eval₂]
    have : Polynomial.eval₂ (zpToOO p) x' gZ = 0 := by
      apply Subtype.ext
      change (OO p).subtype (Polynomial.eval₂ (zpToOO p) x' gZ) = 0
      rw [Polynomial.hom_eval₂]
      have e : (OO p).subtype.comp (zpToOO p) =
          (algebraMap ℚ_[p] (Kbar p)).comp PadicInt.Coe.ringHom := RingHom.ext fun _ => rfl
      rw [e, ← Polynomial.eval₂_map, hgZ]
      exact minpoly.aeval ℚ_[p] x
    rw [this, map_zero]
  -- the coefficients of `gk` are fixed by Frobenius
  have hψ : ∀ c : ℤ_[p], (ψ c) ^ p = ψ c := by
    intro c
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range c
    have h0 : ψ (c - n) = 0 := by
      change r (zpToOO p (c - n)) = 0
      rw [residue_eq_zero_iff, coe_zpToOO, PadicAlgCl.norm_extends]
      exact (PadicInt.mem_nonunits.mp hn :)
    have hc : ψ c = (n : k) := by
      rw [map_sub, sub_eq_zero, map_natCast] at h0; exact h0
    rw [hc, ← frobenius_def, map_natCast]
  have hfrob : ∀ z : k, gk.eval z = 0 → gk.eval (z ^ p) = 0 := by
    intro z hz
    have e : gk.map (frobenius k p) = gk := by
      ext n
      rw [Polynomial.coeff_map, frobenius_def, Polynomial.coeff_map, hψ]
    calc gk.eval (z ^ p) = (gk.map (frobenius k p)).eval (frobenius k p z) := by
          rw [e, frobenius_def]
      _ = frobenius k p (gk.eval z) := by
          rw [Polynomial.eval_map, Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id]
      _ = 0 := by rw [hz, map_zero]
  have hall : ∀ i : ℕ, y ^ p ^ i ∈ {z : k | IsRoot gk z} := by
    intro i
    induction i with
    | zero => simpa using hroot
    | succ i ih =>
      rw [pow_succ, pow_mul]
      exact hfrob _ ih
  obtain ⟨i, j, hij, hyij⟩ := (Polynomial.finite_setOfPred_isRoot hgk0).exists_lt_map_eq_of_forall_mem hall
  refine ⟨j - i, by omega, ?_⟩
  have hy : y ^ p ^ (j - i) = y := by
    have hinj := (iterateFrobenius k p i).injective
    apply hinj
    rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
    exact hyij.symm
  have : r (x' ^ p ^ (j - i) - x') = 0 := by rw [map_sub, map_pow, hy, sub_self]
  rw [residue_eq_zero_iff] at this
  simpa using this

theorem norm_le_one_of_pow_eq_self {t : Kbar p} {M : ℕ} (hM : 1 < M) (ht : t ^ M = t) :
    ‖t‖ ≤ 1 := by
  by_contra h
  push Not at h
  have h1 : ‖t‖ ^ 1 < ‖t‖ ^ M := pow_lt_pow_right₀ h hM
  rw [pow_one, ← norm_pow, ht] at h1
  exact lt_irrefl _ h1

/-- If `‖x^M − x‖ < 1` then `x` is congruent to a root of `X^M − X`. -/
theorem exists_root_close {x : Kbar p} (hx : ‖x‖ ≤ 1) {M : ℕ} (hM : 1 < M)
    (hlt : ‖x ^ M - x‖ < 1) : ∃ t : Kbar p, t ^ M = t ∧ ‖x - t‖ < 1 := by
  set P : (Kbar p)[X] := X ^ M - X with hP
  have hPm : P.Monic := monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hM)
  have hprod : (P.roots.map fun a => X - C a).prod = P :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm IsAlgClosed.card_roots_eq_natDegree
  have heval : P.eval x = (P.roots.map fun a => x - a).prod := by
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    simp
  by_contra hne
  push Not at hne
  have hroot : ∀ a ∈ P.roots, ‖x - a‖ = 1 := by
    intro a ha
    have ha' : a ^ M = a := by
      have := (mem_roots hPm.ne_zero).1 ha
      simpa [P, sub_eq_zero] using this
    exact le_antisymm ((norm_sub_le_max' _ _).trans (max_le hx
      (norm_le_one_of_pow_eq_self hM ha'))) (hne a ha')
  have h1 : ‖P.eval x‖ = 1 := by
    rw [heval]
    change (normHom : Kbar p →*₀ ℝ) _ = 1
    rw [map_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_one
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hc
    exact hroot a ha
  have : P.eval x = x ^ M - x := by simp [P]
  rw [this] at h1
  exact absurd h1 hlt.ne

/-- **An element of `G_{ℚ_p}` fixing the roots of every `X^{p^m} − X` (`m ≥ 1`) lies in the metric
inertia group.** -/
theorem mem_inertiaSet_of_fix {σ : GQp p}
    (h : ∀ m : ℕ, 0 < m → ∀ t : Kbar p, t ^ p ^ m = t → σ t = t) : σ ∈ inertiaSet := by
  intro x hx
  obtain ⟨m, hm, hlt⟩ := exists_pow_sub_lt_one hx
  have hM : 1 < p ^ m := Nat.one_lt_pow hm.ne' (Fact.out : p.Prime).one_lt
  obtain ⟨t, ht, hxt⟩ := exists_root_close hx hM hlt
  have hσt := h m hm t ht
  have e : σ x - x = σ (x - t) - (x - t) := by rw [map_sub, hσt]; ring
  rw [e]
  refine (norm_sub_le_max' _ _).trans_lt ?_
  rw [norm_aut, max_self]
  exact hxt

end UnramRootsTask

noncomputable section

namespace UnramRootsTask

open PkgI4 (GQp)
open LadicCond Polynomial TauCeti IntermediateField ValuativeRel

variable {p : ℕ} [Fact p.Prime]

/-- Frobenius data of a finite `F/ℚ_p` (TC-free): `q > 1` a power of `p` (the residue cardinality),
a Frobenius lift `φ ∈ G_F` raising the roots of every `X^{q^f} − X` to the `q`-th power, and every
`σ ∈ G_F` acting on the roots of `X^{q^f} − X` as a power `x ↦ x^{q^k}`. -/
def FrobData (F : Fld p) (q : ℕ) (φ : GQp p) : Prop :=
  1 < q ∧ (∃ e : ℕ, q = p ^ e) ∧ φ ∈ fixSet F ∧
  (∀ (f : ℕ) (x : Kbar p), 0 < f → x ^ q ^ f = x → φ x = x ^ q) ∧
  (∀ σ ∈ fixSet F, ∀ f : ℕ, 0 < f → ∃ k : ℕ, ∀ x : Kbar p, x ^ q ^ f = x → σ x = x ^ q ^ k)

/-- `σ ∈ G_F` as an `F`-automorphism of `ℚ̄_p`. -/
def toF (F : Fld p) (σ : GQp p) (hσ : σ ∈ fixSet F) : Kbar p ≃ₐ[F] Kbar p :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun c => hσ (c : Kbar p) c.2)

theorem toF_apply (F : Fld p) (σ : GQp p) (hσ : σ ∈ fixSet F) (x : Kbar p) :
    toF F σ hσ x = σ x := rfl

theorem mem_rootSet_of_pow (F : Fld p) {q f : ℕ} (hq : 1 < q) (hf : 0 < f) {x : Kbar p}
    (hx : x ^ q ^ f = x) : x ∈ (X ^ q ^ f - X : F[X]).rootSet (Kbar p) := by
  have hdeg : 1 < q ^ f := Nat.one_lt_pow hf.ne' hq
  have hne : (X ^ q ^ f - X : F[X]) ≠ 0 :=
    (monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hdeg)).ne_zero
  rw [mem_rootSet_of_ne hne]
  simp [hx]

/-- **Frobenius data from Tau Ceti (proved).** -/
theorem frobData_exists (F : Fld p) [FiniteDimensional ℚ_[p] F] : ∃ q φ, FrobData F q φ := by
  letI := finiteIntermediateFieldValuativeRel ℚ_[p] (Kbar p) F
  letI := finiteIntermediateFieldTopology ℚ_[p] (Kbar p) F
  haveI := finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (Kbar p) F
  haveI := finiteIntermediateField_valuativeExtension ℚ_[p] (Kbar p) F
  set q := Nat.card 𝓀[F] with hqdef
  have hq1 : 1 < q := Finite.one_lt_card
  have hpq : ∃ e : ℕ, q = p ^ e := by
    have h2 : q = Nat.card 𝓀[ℚ_[p]] ^ inertiaDegree ℚ_[p] F := TauCeti.natCard_residueField ℚ_[p] F
    rw [Padic.natCard_residueField p] at h2
    exact ⟨_, h2⟩
  haveI : Algebra.IsIntegral F (Kbar p) := Algebra.IsIntegral.tower_top ℚ_[p]
  haveI : IsAlgClosure F (Kbar p) := ⟨inferInstance, inferInstance⟩
  haveI : Normal F (Kbar p) := IsAlgClosure.normal F (Kbar p)
  set E := maximalUnramifiedExtension F (Kbar p)
  set Φ := maximalUnramifiedFrobenius F (Kbar p)
  set φF : Kbar p ≃ₐ[F] Kbar p := Φ.liftNormal (Kbar p)
  refine ⟨q, φF.restrictScalars ℚ_[p], hq1, hpq, ?_, ?_, ?_⟩
  · intro x hx
    exact φF.commutes ⟨x, hx⟩
  · intro f x hf hx
    have hxL := rootSet_subset_unramifiedExtension F (Kbar p) f (mem_rootSet_of_pow F hq1 hf hx)
    have hxE : x ∈ E := unramifiedExtension_le_maximalUnramifiedExtension F (Kbar p) f hxL
    change φF x = x ^ q
    have h := AlgEquiv.liftNormal_commutes Φ (Kbar p) ⟨x, hxE⟩
    have hx' : (⟨x, hxE⟩ : E) ^ q ^ f = ⟨x, hxE⟩ := Subtype.ext (by simp [hx])
    rw [maximalUnramifiedFrobenius_apply_of_pow_natCard_pow_eq_self hf.ne' hx'] at h
    simpa using h
  · intro σ hσ f hf
    set L := unramifiedExtension F (Kbar p) f
    letI := finiteIntermediateFieldValuativeRel F (Kbar p) L
    letI := finiteIntermediateFieldTopology F (Kbar p) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField F (Kbar p) L
    haveI := finiteIntermediateField_valuativeExtension F (Kbar p) L
    haveI : IsUnramified F L := isUnramified_unramifiedExtension hf.ne'
    set σL : L ≃ₐ[F] L := (toF F σ hσ).restrictNormal L
    have hmem : σL ∈ Subgroup.zpowers (frobeniusAlgEquiv (K := F) (L := L)) := by
      rw [zpowers_frobeniusAlgEquiv]; trivial
    rw [← mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, fun x hx => ?_⟩
    have hxL : x ∈ L := rootSet_subset_unramifiedExtension F (Kbar p) f (mem_rootSet_of_pow F hq1 hf hx)
    have h1 : σ x = (σL ⟨x, hxL⟩ : Kbar p) :=
      (AlgEquiv.restrictNormal_commutes (toF F σ hσ) L ⟨x, hxL⟩).symm
    rw [h1, ← hk]
    have key : ∀ j : ℕ, ∀ y : L, y ^ q ^ f = y →
        (frobeniusAlgEquiv (K := F) (L := L) ^ j) y = y ^ q ^ j := by
      intro j
      induction j with
      | zero => intro y _; simp
      | succ j ih =>
        intro y hy
        have hyq : (y ^ q) ^ q ^ f = y ^ q := by rw [← pow_mul, mul_comm, pow_mul, hy]
        rw [pow_succ', AlgEquiv.mul_apply, ih y hy, map_pow,
          frobeniusAlgEquiv_apply_of_pow_natCard_pow_eq_self hf.ne' hy, ← pow_mul]
        show y ^ (q * q ^ j) = _
        rw [← pow_succ']
    have hy : (⟨x, hxL⟩ : L) ^ q ^ f = ⟨x, hxL⟩ := Subtype.ext (by simp [hx])
    rw [key k _ hy]
    simp

end UnramRootsTask

/-! ## `UnramProcyclic` from the Frobenius data (proved)

TC-free: Frobenius data (`FrobData`, from Tau Ceti in `frobData_exists`), the metric lemmas, and
Mathlib's finite and infinite Galois correspondence. -/

namespace UnramRootsTask

open PkgI4 (GQp)
open LadicCond Polynomial IntermediateField

variable {p : ℕ} [Fact p.Prime]

theorem pow_modEq_pow_mod (q n k : ℕ) (hq : 0 < q) : q ^ k ≡ q ^ (k % n) [MOD q ^ n - 1] := by
  have h1 : q ^ n ≡ 1 [MOD q ^ n - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hq)
  calc q ^ k = (q ^ n) ^ (k / n) * q ^ (k % n) := by rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (k / n) * q ^ (k % n) [MOD q ^ n - 1] := (h1.pow _).mul_right _
    _ = q ^ (k % n) := by rw [one_pow, one_mul]

theorem modEq_of_pow_modEq {q n k k' : ℕ} (hq : 1 < q) (hn : 0 < n)
    (h : q ^ k ≡ q ^ k' [MOD q ^ n - 1]) : k ≡ k' [MOD n] := by
  have h' : q ^ (k % n) ≡ q ^ (k' % n) [MOD q ^ n - 1] :=
    ((pow_modEq_pow_mod q n k (by omega)).symm.trans h).trans (pow_modEq_pow_mod q n k' (by omega))
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · have : n = 1 := by omega
    subst this
    exact Nat.modEq_one
  have hbound : ∀ r, r < n → q ^ r < q ^ n - 1 := by
    intro r hr
    have h1 : q ^ r ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : q ^ n = q * q ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    have h3 : q ≤ q ^ (n - 1) := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 2 * q ^ (n - 1) ≤ q ^ n := by rw [h2]; exact Nat.mul_le_mul_right _ hq
    omega
  have := Nat.ModEq.eq_of_lt_of_lt h' (hbound _ (Nat.mod_lt _ hn)) (hbound _ (Nat.mod_lt _ hn))
  exact Nat.pow_right_injective hq this

/-- The exponent by which `σ` acts on the roots of `X^{q^n} − X` is unique modulo `n`. -/
theorem modEq_of_act {q n k k' : ℕ} (hq : 1 < q) (hn : 0 < n)
    (h : ∀ x : Kbar p, x ^ q ^ n = x → x ^ q ^ k = x ^ q ^ k') : k ≡ k' [MOD n] := by
  set N := q ^ n - 1 with hNdef
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
  have hN : 0 < N := by omega
  haveI : NeZero (N : Kbar p) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (Kbar p) N
  have hζN : ζ ^ q ^ n = ζ := by
    rw [show q ^ n = N + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  have e := h ζ hζN
  rw [← pow_mod_of_pow_eq_one hζ.pow_eq_one (q ^ k),
    ← pow_mod_of_pow_eq_one hζ.pow_eq_one (q ^ k')] at e
  exact modEq_of_pow_modEq hq hn (hζ.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) e)

theorem pow_pow_of_dvd {q f N : ℕ} {x : Kbar p} (hx : x ^ q ^ f = x) (h : f ∣ N) :
    x ^ q ^ N = x := by
  obtain ⟨j, rfl⟩ := h
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hx]

theorem mem_rootSet_Qp {q f : ℕ} (hq : 1 < q) (hf : 0 < f) {x : Kbar p}
    (hx : x ^ q ^ f = x) : x ∈ (X ^ q ^ f - X : ℚ_[p][X]).rootSet (Kbar p) := by
  have hdeg : 1 < q ^ f := Nat.one_lt_pow hf.ne' hq
  have hne : (X ^ q ^ f - X : ℚ_[p][X]) ≠ 0 :=
    (monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hdeg)).ne_zero
  rw [mem_rootSet_of_ne hne]
  simp [hx]

theorem fix_adjoin {σ : GQp p} {S : Set (Kbar p)} (h : ∀ x ∈ S, σ x = x) :
    ∀ x ∈ adjoin ℚ_[p] S, σ x = x := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => exact σ.commutes r
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/-- (F2) from the Frobenius data. -/
theorem f2_of_frobData {F : Fld p} [FiniteDimensional ℚ_[p] F] {q : ℕ} {φ : GQp p}
    (hD : FrobData F q φ) (n : ℕ) (hn : 0 < n) : ∃ χ : GQp p → ZMod n,
        (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, χ (σ * τ) = χ σ + χ τ) ∧ χ φ = 1 ∧
        (∀ σ ∈ fixSet F ∩ inertiaSet, χ σ = 0) ∧
        ∃ K : Fld p, FiniteDimensional ℚ_[p] K ∧ ∀ σ ∈ fixSet K, χ σ = 0 := by
  obtain ⟨hq1, ⟨e, hqe⟩, hφF, hφ, hS3⟩ := hD
  have hpq : p ∣ q := by
    rcases e with _ | e
    · rw [pow_zero] at hqe; omega
    · rw [hqe]; exact dvd_pow_self p (Nat.succ_ne_zero e)
  classical
  let kk : GQp p → ℕ := fun σ => if h : σ ∈ fixSet F then Classical.choose (hS3 σ h n hn) else 0
  have hkk : ∀ σ (h : σ ∈ fixSet F), ∀ x : Kbar p, x ^ q ^ n = x → σ x = x ^ q ^ kk σ := by
    intro σ h
    simp only [kk, dif_pos h]
    exact Classical.choose_spec (hS3 σ h n hn)
  have hzero : ∀ σ (h : σ ∈ fixSet F), (∀ x : Kbar p, x ^ q ^ n = x → σ x = x) →
      ((kk σ : ℕ) : ZMod n) = 0 := by
    intro σ h hfix
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff]
    apply modEq_of_act (p := p) hq1 hn
    intro x hx
    rw [← hkk σ h x hx, pow_zero, pow_one]
    exact hfix x hx
  refine ⟨fun σ => (kk σ : ZMod n), ?_, ?_, ?_, ?_⟩
  · intro σ hσ τ hτ
    rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
    apply modEq_of_act (p := p) hq1 hn
    intro x hx
    rw [← hkk _ (mul_mem_fixSet hσ hτ) x hx, AlgEquiv.mul_apply, hkk τ hτ x hx, map_pow,
      hkk σ hσ x hx, ← pow_mul, ← pow_add]
  · show ((kk φ : ℕ) : ZMod n) = 1
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    apply modEq_of_act (p := p) hq1 hn
    intro x hx
    rw [← hkk φ hφF x hx, hφ n x hn hx, pow_one]
  · intro σ hσ
    exact hzero σ hσ.1 fun x hx => fix_of_mem_inertiaSet_of_pow_eq_self hσ.2
      (Nat.one_lt_pow hn.ne' hq1) (dvd_pow hpq hn.ne') hx
  · set A : Fld p := adjoin ℚ_[p] ((X ^ q ^ n - X : ℚ_[p][X]).rootSet (Kbar p))
    haveI : FiniteDimensional ℚ_[p] A :=
      finiteDimensional_adjoin fun _ hx => (isAlgebraic_of_mem_rootSet hx).isIntegral
    refine ⟨F ⊔ A, inferInstance, fun σ hσ => ?_⟩
    refine hzero σ (fixSet_anti le_sup_left hσ) fun x hx => ?_
    exact hσ x ((le_sup_right : A ≤ F ⊔ A) (subset_adjoin _ _ (mem_rootSet_Qp hq1 hn hx)))

/-- The roots of `X^{q^f} − X`, `f ≥ 1`. -/
def Rq (q : ℕ) : Set (Kbar p) := {x | ∃ f : ℕ, 0 < f ∧ x ^ q ^ f = x}

/-- `F(R_N)`, as a field over `ℚ_p`. -/
def EN (F : Fld p) (q N : ℕ) : Fld p := adjoin ℚ_[p] ((F : Set (Kbar p)) ∪ {x | x ^ q ^ N = x})

/-- Every element of `F^{ur} = F(R)` lies in some `F(R_N)`. -/
theorem exists_mem_EN {F : Fld p} {q : ℕ} {y : Kbar p}
    (hy : y ∈ adjoin ℚ_[p] ((F : Set (Kbar p)) ∪ Rq q)) : ∃ N : ℕ, 0 < N ∧ y ∈ EN F q N := by
  classical
  obtain ⟨T, hTS, hyT⟩ := exists_finset_of_mem_adjoin hy
  let ff : Kbar p → ℕ := fun t => if h : t ∈ Rq q then Classical.choose h else 1
  have hff : ∀ t, 0 < ff t := by
    intro t
    by_cases h : t ∈ Rq q
    · simp only [ff, dif_pos h]; exact (Classical.choose_spec h).1
    · simp only [ff, dif_neg h]; exact Nat.one_pos
  set N := ∏ t ∈ T, ff t
  have hN : 0 < N := Finset.prod_pos fun t _ => hff t
  refine ⟨N, hN, adjoin.mono _ _ _ ?_ hyT⟩
  intro t ht
  rcases hTS ht with htF | htR
  · exact Or.inl htF
  · right
    have hspec := (Classical.choose_spec htR).2
    have hdvd : ff t ∣ N := Finset.dvd_prod_of_mem ff ht
    simp only [ff, dif_pos htR] at hdvd
    exact pow_pow_of_dvd hspec hdvd

/-- (F1) from the Frobenius data. -/
theorem f1_of_frobData {F : Fld p} [FiniteDimensional ℚ_[p] F] {q : ℕ} {φ : GQp p}
    (hD : FrobData F q φ) (K : Fld p) (hK : FiniteDimensional ℚ_[p] K) (hFK : F ≤ K)
    (σ : GQp p) (hσ : σ ∈ fixSet F) :
    ∃ k : ℕ, ∃ τ ∈ fixSet F ∩ inertiaSet, ∃ g ∈ fixSet K, σ = φ ^ k * τ * g := by
  obtain ⟨hq1, ⟨e, hqe⟩, hφF, hφ, hS3⟩ := hD
  haveI : IsGalois ℚ_[p] (Kbar p) := IsAlgClosure.isGalois ℚ_[p] (Kbar p)
  set E : Fld p := adjoin ℚ_[p] ((F : Set (Kbar p)) ∪ Rq q) with hE
  set M : Fld p := normalClosure ℚ_[p] K (Kbar p) with hM
  have hKM : K ≤ M := IntermediateField.le_normalClosure K
  set H₀ : Subgroup (M ≃ₐ[ℚ_[p]] M) := E.fixingSubgroup.map (AlgEquiv.restrictNormalHom M)
  -- the fixed field of `H₀` is `M ∩ E`
  have hfix : ∀ y : M, y ∈ fixedField H₀ → (y : Kbar p) ∈ E := by
    intro y hy
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have h1 := (mem_fixedField_iff H₀ y).1 hy (AlgEquiv.restrictNormalHom M τ) ⟨τ, hτ, rfl⟩
    have h2 : (((τ.restrictNormal M) y : M) : Kbar p) = τ y := AlgEquiv.restrictNormal_commutes τ M y
    change τ (y : Kbar p) = y
    rw [← h2]
    exact congrArg Subtype.val h1
  -- a uniform level `N`
  obtain ⟨N, hN, hNfix⟩ : ∃ N : ℕ, 0 < N ∧ ∀ y : M, y ∈ fixedField H₀ → (y : Kbar p) ∈ EN F q N := by
    classical
    let b := Module.finBasis ℚ_[p] (fixedField H₀)
    have hb : ∀ i, ∃ N : ℕ, 0 < N ∧ (((b i : fixedField H₀) : M) : Kbar p) ∈ EN F q N :=
      fun i => exists_mem_EN (hfix _ (b i).2)
    choose Nf hNf0 hNf using hb
    refine ⟨∏ i, Nf i, Finset.prod_pos fun i _ => hNf0 i, fun y hy => ?_⟩
    have hmono : ∀ i, EN F q (Nf i) ≤ EN F q (∏ i, Nf i) := by
      intro i
      apply adjoin.mono
      rintro x (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (pow_pow_of_dvd hx (Finset.dvd_prod_of_mem Nf (Finset.mem_univ i)))
    have hrepr := b.sum_repr ⟨y, hy⟩
    let L : (fixedField H₀) →ₗ[ℚ_[p]] Kbar p := (M.val.comp (fixedField H₀).val).toLinearMap
    have hL := congrArg L hrepr
    rw [map_sum] at hL
    simp only [LinearMap.map_smul] at hL
    have : (y : Kbar p) = ∑ i, (b.repr ⟨y, hy⟩ i) • (((b i : fixedField H₀) : M) : Kbar p) :=
      hL.symm
    rw [this]
    exact sum_mem fun i _ => smul_mem _ (hmono i (hNf i))
  -- Frobenius exponent at level `N`
  obtain ⟨k, hk⟩ := hS3 σ hσ N hN
  have hφk : ∀ j : ℕ, ∀ x : Kbar p, x ^ q ^ N = x → (φ ^ j) x = x ^ q ^ j := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      have hxq : (x ^ q) ^ q ^ N = x ^ q := by rw [← pow_mul, mul_comm, pow_mul, hx]
      rw [pow_succ', AlgEquiv.mul_apply, ih x hx, map_pow, hφ N x hN hx, ← pow_mul, ← pow_succ']
  set σ' : GQp p := (φ ^ k)⁻¹ * σ with hσ'
  have hσ'F : σ' ∈ fixSet F := mul_mem_fixSet (inv_mem_fixSet (pow_mem_fixSet hφF k)) hσ
  have hσ'N : ∀ x ∈ EN F q N, σ' x = x := by
    apply fix_adjoin
    rintro x (hx | hx)
    · exact hσ'F x hx
    · change (φ ^ k)⁻¹ (σ x) = x
      rw [hk x hx, ← hφk k x hx, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  -- Galois correspondence in `M / ℚ_p`
  have hσM : AlgEquiv.restrictNormalHom M σ' ∈ H₀ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H₀, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply Subtype.ext
    have h2 : (((σ'.restrictNormal M) y : M) : Kbar p) = σ' y :=
      AlgEquiv.restrictNormal_commutes σ' M y
    change ((σ'.restrictNormal M) y : Kbar p) = y
    rw [h2]
    exact hσ'N _ (hNfix y hy)
  obtain ⟨τ, hτE, hτσ⟩ := Subgroup.mem_map.1 hσM
  have hτE' : ∀ x ∈ E, τ x = x := fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτE x hx
  have hτM : ∀ y ∈ M, τ y = σ' y := by
    intro y hy
    have h1 : (((τ.restrictNormal M) ⟨y, hy⟩ : M) : Kbar p) = τ y :=
      AlgEquiv.restrictNormal_commutes τ M ⟨y, hy⟩
    have h2 : (((σ'.restrictNormal M) ⟨y, hy⟩ : M) : Kbar p) = σ' y :=
      AlgEquiv.restrictNormal_commutes σ' M ⟨y, hy⟩
    have h3 := congrArg (fun χ : M ≃ₐ[ℚ_[p]] M => ((χ ⟨y, hy⟩ : M) : Kbar p)) hτσ
    rw [← h1, ← h2]
    exact h3
  have hFE : (F : Set (Kbar p)) ⊆ E := fun x hx => subset_adjoin _ _ (Or.inl hx)
  refine ⟨k, τ, ⟨fun x hx => hτE' x (hFE hx), ?_⟩, τ⁻¹ * σ', ?_, ?_⟩
  · apply mem_inertiaSet_of_fix
    intro m hm t ht
    apply hτE'
    apply subset_adjoin
    right
    refine ⟨m, hm, ?_⟩
    rw [hqe, ← pow_mul, mul_comm, pow_mul]
    clear hqe
    induction e with
    | zero => simp
    | succ e ih => rw [pow_succ, pow_mul, ih, ht]
  · intro x hx
    have hxM := hKM hx
    change τ⁻¹ (σ' x) = x
    rw [← hτM x hxM, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  · rw [hσ']; group

/-- **`UnramProcyclic` from the Frobenius data (proved).** -/
theorem unramProcyclic_of_frobData
    (h : ∀ F : Fld p, FiniteDimensional ℚ_[p] F → ∃ q φ, FrobData F q φ) :
    UnramProcyclic p := by
  intro F hF
  obtain ⟨q, φ, hD⟩ := h F hF
  exact ⟨φ, hD.2.2.1, fun K hK hFK σ hσ => f1_of_frobData hD K hK hFK σ hσ,
    fun n hn => f2_of_frobData hD n hn⟩

end UnramRootsTask

/-! ## The result -/

namespace UnramRootsTask

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`UnramRoots` (local-glue's textbook Prop, verbatim) is a theorem (proved)**, from Mathlib and
the vendored Tau Ceti (`ZInQKernel/Contrib/TauCeti/`). -/
theorem unramRoots : G15Ram.UnramRoots p ℓ :=
  unramRoots_of_unramProcyclic
    (unramProcyclic_of_frobData fun F hF => by haveI := hF; exact frobData_exists F)

/-- The form used by local-glue (`tail_glue.lean`, `part_pack.lean`): every `p`, `ℓ`. -/
theorem unramRoots_all : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ :=
  fun _ _ _ _ => unramRoots

/-- The form used at `p = 2` by local-glue (`hU2` in `tail_glue.lean`). -/
theorem unramRoots_two : ∀ (hp : Nat.Prime 2) (ℓ : ℕ) [Fact ℓ.Prime],
    @G15Ram.UnramRoots 2 ⟨hp⟩ ℓ _ :=
  fun hp _ _ => @unramRoots 2 ⟨hp⟩ _ _

end UnramRootsTask



/-! ## leaf-fold3: scratch/frob-pieces/FrobPiecesFull.lean, declarations already in the chain dropped -/


/-!
# g0-mod-field: glue steps G2, G4, G7 of the H decomposition (first range of `ModularConstituent`)

Task g0-mod-field (2026-11-13). `ModularConstituent` (scratch/g0-split/Split.lean, piece 10)
covers G2, G4, G7-G16 of docs/research/h-decomposition.md §3. This file takes the range
G2 (fibre field `K`), G4 (Hom field `L`, `[L:ℚ] ≤ D`), G7 (scalar descent to `L'`,
`[L':ℚ] ≤ Q·M`), for `S = S_mul`, `R = D` (the instance `SixContactMin`).

Outputs (`def … : Prop`): `G2Out Y Φ u P` (with `RationalFibre`), `G4Out u P`, `G7Out u P`, and the clause list `G7Data`
with `G7OutUnr u P` (G7 with the twist: `L'` unramified outside `T`), for a `ℚ̄`-object `P` of
`Y₃` over `J(u)` (`FibreCtx`). The descent datum of B1 on the actual `A` is `DescentDatum`
(maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`).

Proved (no `sorry`, standard axioms):
* `g2Out_of_cover`: G2's bookkeeping (a splitting field of a separable polynomial of degree
  `≤ 324` is Galois of degree `≤ 324!`).
* `descentDatum_of_conjugacy`: B1's normalization (N5 L645-663): conjugacy isogenies with
  rational discrepancy `c` give `a_σ = |ker m_σ|^{-1/4}` and the sign cocycle `ε = sgn c`.
* `g4Out_of_kernelField`: G4's bookkeeping (Hom field `L = E ⊔ K` Galois,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D` by Minkowski's bound, model by base change, B1).
* `g7Out_of_g4Out`, `g7OutUnr_of_g4Out`: G7 = B2-B3 on the actual descent datum
  (`b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf`, `b3_of_cochain`, `degree_le_QM`) and the
  model over `L'` (`isModelOver_baseChange`, transitivity of base change).
* `fieldDescent`, `fieldDescentUnr`: the composite G2 → G4 → G7.
* `modularConstituent_of_ranges`: `ModularConstituentG` (part_split's `ModularConstituent` over
  `PkgI3.AbVar`) from this range and the next ranges bundled as `AfterG7`.

Remaining (named Props): `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4:
Weil restriction, Galois image in `GL_r(ℤ)`, inertia on the Tate module, the conjugacy isogenies
`ConjugacyData`), `UnramifiedSup` (compositum of unramified fields; STANDARD), the four B2 leaves
of glue-descent (`LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit`, `LeafUnramified`), and `AfterG7`
(G8-G16, the other two tasks).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

/-! ## The outputs of G2, G4, G7 -/

/-! ## B1's normalization (proved): from conjugacy isogenies to the sign cocycle -/

/-! ## Sanity check: `DescentDatum` is satisfiable (an abelian variety over `ℚ`, `ε = 1`) -/

/-! ## Transitivity of base change -/

/-! ## G7 from G4 (proved) -/

/-! ## G7 with the twist: `L'` unramified outside `T` (proved) -/

/-! ## G2's bookkeeping (proved) -/

/-! ## G4's bookkeeping (proved) -/

/-! ## The remaining glue as Props, and the composite -/

/-! ## How G7's output feeds `ModularConstituent` -/

/-! ## Feeding g0-mod-galois' inputs (G8-G12): their `G2Out`, `G7Out` -/

namespace GaloisCopy
/-! Copied from scratch/g0-mod-galois/part_galois.lean (branch wip/g0-mod-galois at 20fa1287),
definitions `resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, verbatim (namespace renamed). -/

end GaloisCopy

end G0ModField

/-!
# unram-tate: `TateBridge` reduced to named glue pieces

Everything above `end G0ModField` is `scratch/g0-mod-field/ModField.lean` verbatim (lines 1-1036),
so `G0ModField.TateBridge` is the statement as written there. Below: the operators
`ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` (`opV`, a ring homomorphism, proved), the quaternion matrix units
(`matrixUnits_of_quat`, copied from scratch/unram-tate/QuatUnits.lean), five named glue Props, and
the assembly `tateBridge_of_pieces` (proved).
-/

namespace UnramTate

open G0ModField

/-! ## The Tate functor on additive maps of points -/

section Ops

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

end Ops

/-! ## Matrix units (copied from scratch/unram-tate/QuatUnits.lean, proved there) -/

section Quat

open GlueDescent

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

end Quat

/-! ## The order elements `i`, `j` of `𝒪` -/

/-! ## The named glue pieces -/

/-! ## The assembly -/

set_option maxHeartbeats 1000000 in
/-! ## Proofs of two pieces -/

set_option maxHeartbeats 1000000 in
/-! ## `EndBaseChange` (proof copied from scratch/bp-qmmoduli/QMAbVar.lean L533-557, `endBC`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
end BaseChangeEnd

/-! ## `TatePoints` (generic parts copied from scratch/unram-tate/BCPoints.lean) -/

section BCPoints

open scoped CategoryTheory.Obj

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

end Tr


end BCPoints

/-! ## `UnramifiedSup` in this context (proof copied from scratch/unram-tate/UnramSup.lean) -/

section Sup

open NumberField

end Sup

end UnramTate


/-!
# g14-trace, second file: the linked Tate bridge at `ℓ = 3, 5`

Appended to a verbatim copy of `scratch/g0-mod-field/ModField.lean` (g0-mod-field's `G7Data`,
`TateBridge`, `GaloisCopy.G7Out`). `TateBridge` gives the `ℓ`-adic data at each `ℓ` separately
(`∀ ℓ, ∃ Tm c ε' a β' uu, G7Out …`), which does not determine the traces of `r₃` against `r₅`
(g14-trace §1, `g7Out_twist`). `TateBridge35` is the linked form at `ℓ = 3, 5` that
`G14Trace.g12Spec_g14_of_galois` consumes: one pair `a, β : G_ℚ → ℚ̄` mapped to `ℚ̄₅`, `ℚ̄₃` by
embeddings `j₅`, `j₃` (TateBridge's own docstring: "mapped into `ℚ̄_ℓ` by one embedding of the
number field they generate"), and the operators `Tm_ℓ` (from one points-level `m_σ`) in the
Frobenius link at Frobenius elements. No `sorry`, no `axiom`.
-/

noncomputable section

namespace G14Bridge

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField
open GlueC10Link (FrobCompare)

end G14Bridge

end


/-!
# frob-trace: `TateBridge35` and `FrobTraceLink` (g14-trace)

Appended (by `build.sh`) to verbatim copies of `scratch/unram-tate/TateBridge.lean` (which is
`scratch/g0-mod-field/ModField.lean` L1-1036 plus unram-tate's section `UnramTate`) and of
`scratch/g14-trace/part_bridge.lean` (`G14Bridge.FrobTraceLink`, `G14Bridge.TateBridge35`).

Main result: `FrobTrace.tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree)
(hR : AlgFrobRed) : G14Bridge.TateBridge35`, through the chain of proved implications
`AlgFrobRed → AlgFrobOne → AlgFrobLink` and `tateBridge35_of_algFrobLink`. The operators are
unram-tate's `Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (one points-level `m`, one `Θ`,
one `h`), the scalars are `aQ g = βQ g / γQ(hgh⁻¹)` and `βQ` with `ιC ∘ βQ = β` in `ℚ̄` (proved,
`scalarsQbar`), and the conjunct `FrobTraceLink` for these operators is derived from the glue
Prop `AlgFrobRed` (one reduction homomorphism `A(ℚ̄) → Ā(k̄)` intertwining `f = F ∘ - ∘ Spec(σ)`
with an endomorphism of the reduction, bijective on prime-to-`p` torsion).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace FrobTrace

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-! ## The Tate functor on an additive equivalence -/

/-! ## The glue Prop: reduction of the algebraic maps `m_σ` modulo `p` -/

/-! ## `AlgFrobOne` from a reduction homomorphism on points -/

/-! ## From the points-level comparison to `FrobCompare` for `opV(Θ ∘ f ∘ Θ⁻¹)` -/

/-! ## Rescaling the scalars of `G7Out` -/

/-! ## The scalars in `ℚ̄` -/

/-! ## The assembly -/

set_option maxHeartbeats 4000000 in
end FrobTrace

end


/-!
# mul-rigidity: the textbook leaf `RigidityHom` proved from Mathlib

`RigidityHom` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4‴). The proof
follows Mathlib's proof that proper geometrically integral group schemes are commutative
(`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`, Stacks 0BFD),
with the commutator replaced by an arbitrary `c : G ⊗ G ⟶ Z` that is constant on `{e} × G` and on
`G × {e}` (the rigidity lemma, Mumford §4).
-/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {K : Type u} [Field K]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
end MulRigidity

/-! ## The leaf, copied verbatim, and its proof -/

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

end G0FibreSimple

/-!
# alg-frob-red: reducing `FrobTrace.AlgFrobRed`

Appended (by `build.sh`) to verbatim copies of frob-trace's three source parts
(`src_part_tate_src.lean`, `src_part_bridge_src.lean`, `src_part_frob.lean`, i.e.
`scratch/frob-trace/FrobTrace.lean` without its first import line, which `build.sh` re-adds).

Main results (namespace `AlgFrobRedRed`):
* `algFrobRed_of_at : AlgFrobRedAt → FrobTrace.AlgFrobRed` (proved): the place `g(v)` and the
  Frobenius `gτg⁻¹` are absorbed (`liesOver_smul`, `isArithFrob_conj`).
* `algFrobRedAt_of_good : GoodRedCofinite → AlgFrobRedGood → AlgFrobRedAt` (proved): the finite
  set `S` is the set of primes of bad reduction (leaf `GoodRedCofinite`); what remains is local
  at one place of good reduction (`AlgFrobRedGood`).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate
open scoped Pointwise

/-! ## 1. Conjugating the place -/

/-- Nonunits move with the place: `z ∈ v.nonunits → g z ∈ (g • v).nonunits`. -/
theorem smul_mem_nonunits (g : PkgI4.GQ) {v : ValuationSubring PkgI4.Qbar} {z : PkgI4.Qbar}
    (hz : z ∈ v.nonunits) : g z ∈ (g • v).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hz ⊢
  rcases hz with hz | hz
  · left; rw [hz, map_zero]
  · right
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    exact hz

/-- `g(v)` lies over `p` if `v` does. -/
theorem liesOver_smul (g : PkgI4.GQ) {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hv : PkgI4.LiesOver v p) : PkgI4.LiesOver (g • v) p := by
  have := smul_mem_nonunits g hv
  rwa [map_natCast] at this

/-- `gτg⁻¹` is an arithmetic Frobenius at `g(v)` if `τ` is one at `v`. -/
theorem isArithFrob_conj (g : PkgI4.GQ) {τ : PkgI4.GQ} {v : ValuationSubring PkgI4.Qbar}
    {p : ℕ} (hτ : PkgI4.IsArithFrob τ v p) : PkgI4.IsArithFrob (g * τ * g⁻¹) (g • v) p := by
  obtain ⟨hD, hF⟩ := hτ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff] at hD ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, hD]
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def] at hx
    have h := smul_mem_nonunits g (hF _ hx)
    have e1 : g (τ (g⁻¹ x)) = (g * τ * g⁻¹) x := rfl
    have e2 : g (g⁻¹ x) = x := by rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rwa [map_sub, map_pow, e1, e2] at h

/-- **`AlgFrobRedAt` (GLUE, AV side; Glazer N5 L777-786; the reduction map at the place of the
Frobenius).** `FrobTrace.AlgFrobRed` with the Frobenius `σ` at the place `v` itself (no
conjugating `g`): for `A/L`, `F : A → A` finite surjective there is a finite `S` such that for
`p ∉ S`, `v ∣ p`, `σ` an arithmetic Frobenius at `v` and `f(x) = F ∘ x ∘ Spec(σ)` additive, there
are `Ā/k` (`char k = p`), `α' ∈ End(Ā)`, `N ≠ 0` and `red : A(ℚ̄) → Ā(k̄)` with
`red ∘ (N·f) = α' ∘ red`, injective on `ℓⁿ`-torsion and onto `Ā(k̄)[ℓⁿ]` from `A(ℚ̄)[ℓⁿ]` for every
prime `ℓ ≠ p`. -/
def AlgFrobRedAt : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        ∀ (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobRed` from `AlgFrobRedAt` (proved):** apply `AlgFrobRedAt` at the place `g(v)` to
the arithmetic Frobenius `gτg⁻¹` there. -/
theorem algFrobRed_of_at (h : AlgFrobRedAt) : FrobTrace.AlgFrobRed := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := h L A F hF1 hF2
  exact ⟨S, fun p hp hpS v τ hv hτ g f hf =>
    hS p hp hpS (g • v) (g * τ * g⁻¹) (liesOver_smul g hv) (isArithFrob_conj g hτ) f hf⟩

/-! ## 2. Isolating the finite set: good reduction outside finitely many primes -/

/-- **`GoodRedCofinite` (LEAF candidate; good reduction almost everywhere).** An abelian variety
`A` over a number field `L ⊆ ℚ̄` has good reduction at every place of `L` above all but finitely
many primes `p`: there is a finite `S` with `A` having good reduction (I2's `HasGoodReduction`:
an abelian scheme over the valuation ring with generic fibre `≅ A`) at `v ∩ L` for every place
`v` of `ℚ̄` above `p ∉ S`. Source: spreading out, EGA IV₃ §8 (8.8.2, 8.10.5) and EGA IV₄ 17.7.8
for smoothness, with properness and geometric connectedness of fibres; in this form e.g.
Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), §1, and
Milne, *Abelian varieties* (in Cornell–Silverman, *Arithmetic Geometry*, 1986), §20
(all locators UNVERIFIED). -/
def GoodRedCofinite : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        PkgI2.HasGoodReduction (ObjBridge.toGrp A) (v.comap (algebraMap L PkgI4.Qbar))

/-- **`AlgFrobRedGood` (GLUE, AV side; Glazer N5 L777-786; the reduction map at one place of
good reduction).** `AlgFrobRedAt` at a single place `v ∣ p` at which `A` has good reduction
(`HasGoodReduction` at `v ∩ L`), with no finite set: for `σ` an arithmetic Frobenius at `v` and
`f(x) = F ∘ x ∘ Spec(σ)` additive (`F : A → A` finite surjective), there are `Ā/k`
(`char k = p`), `α' ∈ End(Ā)`, `N ≠ 0` and `red : A(ℚ̄) → Ā(k̄)` with `red ∘ (N·f) = α' ∘ red`,
injective on `ℓⁿ`-torsion and onto `Ā(k̄)[ℓⁿ]` from `A(ℚ̄)[ℓⁿ]` for every prime `ℓ ≠ p`.

Why it is true (SPECULATIVE in its Lean details; `N = 1`): `𝒜/O_w` (`w = v ∩ L`) the abelian
scheme, `Ā` its special fibre over `k = κ(w)`; `red` is `A(ℚ̄) = 𝒜(O_v) → Ā(κ(v)) ≅ Ā(k̄)`
(valuative criterion); `F` is an `L`-morphism `A → A^{(s)}`, `s = σ⁻¹|_L ∈ D(w)`, and `A^{(s)}`
has good reduction at `s(w) = w`, so `F` extends to `𝒜 → 𝒜^{(s)}` (leaf I2-NMP); `f` reduces to
`F̄ ∘ Fr_Ā`, a `k`-morphism fixing `0`, hence `α' ∈ End(Ā)` (rigidity); the torsion clauses are
leaf I2-Red. -/
def AlgFrobRedGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        PkgI2.HasGoodReduction (ObjBridge.toGrp A) (v.comap (algebraMap L PkgI4.Qbar)) →
        ∀ (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobRedAt` from the leaf `GoodRedCofinite` and the local glue `AlgFrobRedGood`
(proved):** `S` is the finite set of `GoodRedCofinite` for `A`. -/
theorem algFrobRedAt_of_good (hG : GoodRedCofinite) (hL : AlgFrobRedGood) : AlgFrobRedAt := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := hG L A
  exact ⟨S, fun p hp hpS v σ hv hσ f hf =>
    hL L A F hF1 hF2 p hp v σ hv hσ (hS p hp hpS v hv) f hf⟩

/-- **`AlgFrobRed` from `GoodRedCofinite` and `AlgFrobRedGood` (proved).** -/
theorem algFrobRed_of_good (hG : GoodRedCofinite) (hL : AlgFrobRedGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_at (algFrobRedAt_of_good hG hL)

/-- **`TateBridge35` from I3.M0, `GoodRedCofinite` and `AlgFrobRedGood` (proved).** -/
theorem tateBridge35_of_good (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hL : AlgFrobRedGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_good hG hL)

/-! ## 3. The local glue: special fibre, reduction relation, Frobenius -/

/-- `O_w = v ∩ L`, the valuation ring of `L` below the place `v` of `ℚ̄`. -/
abbrev Ow (L : IF) (v : ValuationSubring PkgI4.Qbar) : ValuationSubring L :=
  v.comap (algebraMap L PkgI4.Qbar)

/-- The residue field `k = κ(w)` of `O_w`. -/
abbrev kw (L : IF) (v : ValuationSubring PkgI4.Qbar) : Type :=
  IsLocalRing.ResidueField (Ow L v)

/-- The special fibre `𝒜 ×_{O} κ(O)` of a group object over a local ring `O`, as a group object
over `Spec κ(O)` (base change along `Spec κ(O) → Spec O`). -/
def sf {O : Type} [CommRing O] [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) :
    Grp (Over (Spec (.of (IsLocalRing.ResidueField O)))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))).mapGrp.obj 𝒜

/-- **`SmoothGeomConnIntegral` (LEAF candidate, textbook; Stacks Project / EGA IV₂).** A smooth,
quasi-compact, geometrically connected scheme over a field is geometrically integral (smooth ⇒
geometrically normal, EGA IV₂ 6.8.1 / 6.7.4 (UNVERIFIED); a connected, quasi-compact, locally
Noetherian normal scheme is integral, Stacks Tag 033M (UNVERIFIED); applied after every field
base change, which preserves smoothness and connectedness). -/
def SmoothGeomConnIntegral : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (.of k)),
    Smooth f → GeometricallyConnected f → QuasiCompact f → GeometricallyIntegral f

/-- The special fibre of an abelian scheme over a local ring is an abelian variety (I2's
`IsAbelianVariety`): properness, smoothness and geometric connectedness are stable under base
change (Mathlib), and geometric integrality is `SmoothGeomConnIntegral`. -/
theorem sf_isAbelianVariety (hS : SmoothGeomConnIntegral) {O : Type} [CommRing O]
    [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) [h : PkgI2.IsAbelianScheme 𝒜] :
    PkgI2.IsAbelianVariety (sf 𝒜) := by
  haveI := h.proper; haveI := h.smooth; haveI := h.geomConnected
  have hp : IsProper (sf 𝒜).X.hom := by
    show IsProper (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  have hs : Smooth (sf 𝒜).X.hom := by
    show Smooth (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  have hc : GeometricallyConnected (sf 𝒜).X.hom := by
    show GeometricallyConnected
      (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  exact ⟨hp, hs, hS _ _ _ hs hc inferInstance⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **The reduction relation.** For `A/L`, an abelian scheme `𝒜/O_w` with `e : 𝒜_L ≅ A`, and a
ring map `j : κ(v) → κ(w)‾`: the `κ(w)‾`-point `y` of the special fibre is the reduction of
`x ∈ A(ℚ̄)` (via `j`) if some `O_w`-morphism `x' : Spec O_v → 𝒜` restricts to `x` on the generic
point (through `e`; the clause of I2's `IsReductionOf`, copied) and `y` followed by the projection
to `𝒜` is `x'` on `Spec κ(v)`, read through `Spec j`. -/
def RedRel {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (x : PtQ L A) (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) : Prop :=
  ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
    ((Additive.toMul x) ≫ (e.inv.hom.hom : A.X ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) =
      Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left ∧
    y.left ≫ pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        x'.left

/-- `char κ(w) = p` for `w = v ∩ L`, `v ∣ p`. -/
theorem charP_kw {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ} (hp : p.Prime)
    (hv : PkgI4.LiesOver v p) : CharP (kw L v) p := by
  have h1 : ((p : Ow L v) : L) ∈ (Ow L v).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hin
    rw [ValuationSubring.mem_comap, map_inv₀] at hin
    have he : (algebraMap L PkgI4.Qbar ((p : Ow L v) : L)) = (p : PkgI4.Qbar) := by simp
    rw [he] at hin
    have hv' := hv
    unfold PkgI4.LiesOver at hv'
    rw [ValuationSubring.mem_nonunits_iff_or] at hv'
    rcases hv' with h0 | h0
    · exact (Nat.cast_ne_zero.mpr hp.ne_zero) h0
    · exact h0 hin
  have h2 : (p : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (ValuationSubring.coe_mem_nonunits_iff).mp h1
  have h3 : (p : kw L v) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (Ow L v)), IsLocalRing.residue_eq_zero_iff]
    exact h2
  exact (CharP.charP_iff_prime_eq_zero hp).mpr h3

/-- `ℓⁿ` is a unit of `O_w` for a prime `ℓ ≠ p`. -/
theorem isUnit_cast_of_ne {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ} (hp : p.Prime)
    (hv : PkgI4.LiesOver v p) {ℓ : ℕ} (hℓ : ℓ.Prime) (hne : ℓ ≠ p) (n : ℕ) :
    IsUnit (((ℓ ^ n : ℕ)) : Ow L v) := by
  by_contra hnu
  have hm : ((ℓ ^ n : ℕ) : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h0 : ((ℓ ^ n : ℕ) : kw L v) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (Ow L v)), IsLocalRing.residue_eq_zero_iff]
    exact hm
  haveI := charP_kw (L := L) hp hv
  rw [CharP.cast_eq_zero_iff (kw L v) p] at h0
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h0)).symm

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionMapGood` (GLUE; valuative criterion of properness, Stacks Tag 0BX5 / EGA II 7.3.8
(UNVERIFIED locators)).** At a place `v ∣ p` and an abelian scheme `𝒜/O_w` (`w = v ∩ L`) with
`e : 𝒜_L ≅ A`: there are a ring isomorphism `j : κ(v) ≅ κ(w)‾` compatible with the maps from
`O_w` (`κ(v)` is an algebraic closure of `κ(w)`) and a group homomorphism
`red : A(ℚ̄) → Ā(κ(w)‾)` (`Ā` the special fibre `sf 𝒜`) with `RedRel x (red x)` for every `x`
(existence of the lift `x' : Spec O_v → 𝒜`, valuative criterion: `𝒜` proper, `O_v` a valuation
ring with fraction field `ℚ̄`), and the reduction is unique (uniqueness of the lift, `𝒜`
separated, plus the universal property of the fibre product). `red` is a homomorphism since
restriction `𝒜(O_v) → 𝒜(ℚ̄)` is a bijective homomorphism and reduction `𝒜(O_v) → 𝒜(κ(v))` is
one. No Frobenius, no torsion. -/
def ReductionMapGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (p : ℕ), p.Prime →
    ∀ (v : ValuationSubring PkgI4.Qbar), PkgI4.LiesOver v p →
    ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
        ObjBridge.toGrp A),
    ∃ j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v), Function.Bijective j ∧
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) ∧
      ∃ red : PtQ L A →+ Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
        (∀ x, RedRel v 𝒜 e j x (Additive.toMul (red x))) ∧
        (∀ x y y', RedRel v 𝒜 e j x y → RedRel v 𝒜 e j x y' → y = y')

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedTorsionQbar` (GLUE: leaf I2-Red, `PkgI2.ReductionTorsionBijective` (Serre–Tate 1968,
§1), transported).** For `m ≥ 1` invertible in `O_w` and any ring isomorphism
`j : κ(v) ≅ κ(w)‾` compatible with the maps from `O_w`: reduction (`RedRel`) is a bijection
`A(ℚ̄)[m] → Ā(κ(w)‾)[m]`, in I2-Red's form (`∃!` both ways). This is I2-Red for the abelian scheme
`𝒜` over the DVR `O_w` (a valuation ring of the number field `L` with `p` a nonunit), read
through the `L`-isomorphism `ℚ̄ ≅ L‾` (`ℚ̄` is an algebraic closure of `L`), the universal
property of `sf 𝒜 = 𝒜 ×_{O_w} κ(w)` (points of `𝒜` over `κ(v)` = `κ(w)`-points of `sf 𝒜` over
`κ(v)`) and `j`. -/
def RedTorsionQbar : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (p : ℕ), p.Prime →
    ∀ (v : ValuationSubring PkgI4.Qbar), PkgI4.LiesOver v p →
    ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
        ObjBridge.toGrp A)
      (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)), Function.Bijective j →
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) →
      ∀ m : ℕ, 0 < m → IsUnit (m : Ow L v) →
        (∀ x : PtQ L A, m • x = 0 →
          ∃! y : Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
            m • y = 0 ∧ RedRel v 𝒜 e j x (Additive.toMul y)) ∧
        (∀ y : Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))), m • y = 0 →
          ∃! x : PtQ L A, m • x = 0 ∧ RedRel v 𝒜 e j x (Additive.toMul y))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionFrobGood` (GLUE, AV side; Glazer N5 L777-786; the Frobenius step).** At a place
`v ∣ p` with an abelian scheme `𝒜/O_w` and `e : 𝒜_L ≅ A`, `σ` an arithmetic Frobenius at `v`,
`F : A → A` finite surjective and `f(x) = F ∘ x ∘ Spec(σ)` additive: there is an endomorphism
`ᾱ` of the special fibre `Ā = sf 𝒜` (a morphism of group objects over `κ(w)`) such that for every
ring map `j : κ(v) → κ(w)‾`, if `y` is the reduction of `x` then `ᾱ ∘ y` is the reduction of
`f x`.

Why it is true (SPECULATIVE in its Lean details): `F` lies over `Spec(t)`, `t = σ⁻¹|_L ∈ D(w)`
(forced by `f(x)` being an `L`-point); `F` extends to `F̃ : 𝒜 → 𝒜` over `Spec(t|_{O_w})` (leaf
I2-NMP applied to `𝒜` and its base change along `t`); a lift of `f x` is
`Spec(σ|_{O_v}) ≫ x' ≫ F̃`; on `Spec κ(v)`, `σ` induces the `p`-power map (`IsArithFrob`), i.e.
the absolute Frobenius, which commutes with every morphism of schemes; so the reduction of
`f x` is `y ≫ Fr_Ā ≫ F̄` with `F̄` the base change of `F̃` (over `Spec(t̄) = Spec(Frob⁻¹)`), and
`ᾱ = Fr_Ā ≫ F̄` lies over `id_{κ(w)}` and fixes `0` (`f` is additive), hence is a homomorphism
(rigidity, Mumford, *Abelian varieties*, §4 Cor. 1, UNVERIFIED locator). -/
def ReductionFrobGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
          (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
            𝒜 ≅ ObjBridge.toGrp A)
          (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
            Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
              (Additive.toMul x).left ≫ F) →
        ∃ ab : sf 𝒜 ⟶ sf 𝒜,
          ∀ (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x : PtQ L A)
            (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
            RedRel v 𝒜 e j x y → RedRel v 𝒜 e j (f x) (y ≫ ab.hom.hom)

set_option synthInstance.maxHeartbeats 400000 in
/-- **`AlgFrobRedGood` from `SmoothGeomConnIntegral`, `ReductionMapGood`, `RedTorsionQbar` and
`ReductionFrobGood` (proved).** `k = κ(w)`, `Ā = sf 𝒜` (an abelian variety by
`sf_isAbelianVariety`), `α' = ᾱ`, `N = 1`, `red` from `ReductionMapGood`; the intertwining is the
uniqueness of reductions, the torsion clauses are `RedTorsionQbar` at `m = ℓⁿ` (a unit of `O_w`,
`isUnit_cast_of_ne`). -/
theorem algFrobRedGood_of (hS : SmoothGeomConnIntegral) (h1 : ReductionMapGood)
    (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) : AlgFrobRedGood := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ hgood f hf
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := hgood
  haveI := h𝒜
  haveI hAV := sf_isAbelianVariety hS 𝒜
  obtain ⟨j, hjb, hjc, red, hred, huniq⟩ := h1 L A p hp v hv 𝒜 e
  obtain ⟨ab, hab⟩ := h3 L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  refine ⟨kw L v, inferInstance, charP_kw hp hv, ObjBridge.ofGrp (sf 𝒜),
    ObjBridge.homOfGrp ab, 1, one_ne_zero, red, ?_, ?_⟩
  · intro x
    rw [one_smul]
    exact congrArg Additive.ofMul (huniq (f x) _ _ (hred (f x)) (hab j x _ (hred x)))
  · intro ℓ hℓ hne n
    have hu := isUnit_cast_of_ne (L := L) hp hv hℓ hne n
    obtain ⟨-, hB⟩ := h2 L A p hp v hv 𝒜 e j hjb hjc (ℓ ^ n) (pow_pos hℓ.pos n) hu
    refine ⟨fun x hx h0 => ?_, fun y hy => ?_⟩
    · have hx0 : RedRel v 𝒜 e j x (Additive.toMul 0) := h0 ▸ hred x
      have h00 : RedRel v 𝒜 e j 0 (Additive.toMul 0) := (map_zero red) ▸ hred 0
      exact (hB 0 (smul_zero _)).unique ⟨hx, hx0⟩ ⟨smul_zero _, h00⟩
    · obtain ⟨x, ⟨hx, hxr⟩, -⟩ := hB y hy
      exact ⟨x, hx, congrArg Additive.ofMul (huniq x _ _ (hred x) hxr)⟩

/-! ## 4. `ReductionMapGood` from the valuative criterion (Mathlib) and two smaller Props -/

set_option synthInstance.maxHeartbeats 400000 in
/-- `x ∈ A(ℚ̄)` as a `ℚ̄`-point of `𝒜_L` (through `e`). -/
def genPt {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X :=
  (Additive.toMul x) ≫ (e.inv.hom.hom : A.X ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X)

set_option synthInstance.maxHeartbeats 400000 in
/-- The generic point map `Spec ℚ̄ → 𝒜` of `x ∈ A(ℚ̄)` (through `e`), as in `RedRel`. -/
def genMap {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) : Spec (.of PkgI4.Qbar) ⟶ 𝒜.X.left :=
  (genPt v 𝒜 e x).left ≫
    pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))

set_option synthInstance.maxHeartbeats 400000 in
/-- The valuative square: `Spec ℚ̄ → 𝒜` over `Spec O_v → Spec O_w`. -/
theorem genMap_comm {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    genMap v 𝒜 e x ≫ 𝒜.X.hom = Spec.map (CommRingCat.ofHom (algebraMap v PkgI4.Qbar)) ≫
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
  have key : ∀ (T : Scheme) (u : T ⟶ pullback 𝒜.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))),
      (u ≫ pullback.fst _ _) ≫ 𝒜.X.hom = (u ≫ pullback.snd _ _) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) := fun T u => by
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hw : (genPt v 𝒜 e x).left ≫ pullback.snd 𝒜.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) =
      Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) := Over.w (genPt v 𝒜 e x)
  have h2 : ((genPt v 𝒜 e x).left ≫ pullback.snd _ _) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) =
      Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) :=
    congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) hw
  have h3 : Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) =
      Spec.map (CommRingCat.ofHom (algebraMap v PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact (key _ (genPt v 𝒜 e x).left).trans (h2.trans h3)

set_option synthInstance.maxHeartbeats 400000 in
/-- The valuative commutative square of `x`. -/
def vsq {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) : ValuativeCommSq 𝒜.X.hom where
  R := v
  K := PkgI4.Qbar
  i₁ := genMap v 𝒜 e x
  i₂ := Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))
  commSq := ⟨genMap_comm v 𝒜 e x⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Existence of the lift** `x' : Spec O_v → 𝒜` (proved: valuative criterion for the proper
`𝒜 → Spec O_w`, Mathlib `UniversallyClosed.eq_valuativeCriterion`). -/
theorem exists_lift {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
      genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left := by
  haveI := h𝒜.proper
  have h1 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) 𝒜.X.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨⟨l, hl1, hl2⟩⟩ := h1.1 (vsq v 𝒜 e x)
  exact ⟨Over.homMk l hl2, hl1.symm⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Uniqueness of the lift** (proved: valuative criterion of separatedness, Mathlib
`IsSeparated.valuativeCriterion`). -/
theorem lift_unique {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A)
    (x₁ x₂ : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X)
    (h₁ : genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x₁.left)
    (h₂ : genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x₂.left) : x₁ = x₂ := by
  haveI := h𝒜.proper
  have hU := IsSeparated.valuativeCriterion 𝒜.X.hom (vsq v 𝒜 e x)
  have e1 : (⟨x₁.left, h₁.symm, Over.w x₁⟩ : (vsq v 𝒜 e x).commSq.LiftStruct) =
      ⟨x₂.left, h₂.symm, Over.w x₂⟩ := Subsingleton.elim _ _
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l e1)

set_option synthInstance.maxHeartbeats 400000 in
/-- Every `x` has a reduction, for `j` compatible with the maps from `O_w` (proved). -/
theorem exists_redRel {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (x : PtQ L A) : ∃ y, RedRel v 𝒜 e j x y := by
  obtain ⟨x', hx'⟩ := exists_lift v 𝒜 e x
  have hw : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue v)) ≫ x'.left) ≫ 𝒜.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (kw L v) (AlgebraicClosure (kw L v)))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))) := by
    rw [Category.assoc, Category.assoc, Over.w x']
    simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact hjc a
  refine ⟨Over.homMk (pullback.lift _ _ hw) (pullback.lift_snd _ _ hw), x', hx', ?_⟩
  exact pullback.lift_fst _ _ hw

set_option synthInstance.maxHeartbeats 400000 in
/-- Reductions are unique (proved: uniqueness of the lift and of maps into a fibre product). -/
theorem redRel_unique {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x : PtQ L A)
    (y y' : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) :
    RedRel v 𝒜 e j x y → RedRel v 𝒜 e j x y' → y = y' := by
  rintro ⟨x₁, h₁, h₁'⟩ ⟨x₂, h₂, h₂'⟩
  obtain rfl := lift_unique v 𝒜 e x x₁ x₂ h₁ h₂
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h₁'.trans h₂'.symm
  · exact (Over.w y).trans (Over.w y').symm

/-- **`ResidueAlgClosure` (GLUE, standard commutative algebra).** For a place `v ∣ p` of `ℚ̄` and
`w = v ∩ L`, there is a ring isomorphism `j : κ(v) ≅ κ(w)‾` compatible with the maps from `O_w`:
`κ(v)` is algebraically closed (the residue field of a valuation ring of an algebraically closed
field) and algebraic over `κ(w)` (`ℚ̄/L` is algebraic), hence an algebraic closure of `κ(w)`
(Engler–Prestel, *Valued fields* (2005), Thm 3.2.11 and §3.2; Bourbaki, *Alg. Comm.* VI §8;
locators UNVERIFIED). -/
def ResidueAlgClosure : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar) (p : ℕ), p.Prime →
    PkgI4.LiesOver v p →
    ∃ j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v), Function.Bijective j ∧
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedRelMul` (GLUE; reduction respects the group law).** If `y₁, y₂` are the reductions of
`x₁, x₂` then `y₁ y₂` is the reduction of `x₁ + x₂`: the product `x'₁ x'₂` of the lifts (in the
group `𝒜(O_v)`) lifts `x₁ + x₂` (restriction to the generic point and `e` respect the group
laws), and base change to the special fibre respects them too (`sf 𝒜` carries the base-changed
group law). -/
def RedRelMul : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x₁ x₂ : PtQ L A)
    (y₁ y₂ : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
    RedRel v 𝒜 e j x₁ y₁ → RedRel v 𝒜 e j x₂ y₂ → RedRel v 𝒜 e j (x₁ + x₂) (y₁ * y₂)

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionMapGood` from `ResidueAlgClosure` and `RedRelMul` (proved)**, with the valuative
criterion (existence and uniqueness of lifts) from Mathlib. -/
theorem reductionMapGood_of (hR : ResidueAlgClosure) (hM : RedRelMul) : ReductionMapGood := by
  intro L _ A p hp v hv 𝒜 _ e
  obtain ⟨j, hjb, hjc⟩ := hR L v p hp hv
  choose r hr using exists_redRel v 𝒜 e j hjc
  have hun := redRel_unique v 𝒜 e j
  let red : PtQ L A →+ Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (r x)) (fun a b => by
      show Additive.ofMul (r (a + b)) = Additive.ofMul (r a * r b)
      exact congrArg Additive.ofMul (hun _ _ _ (hr (a + b)) (hM L A v 𝒜 e j a b _ _ (hr a) (hr b))))
  exact ⟨j, hjb, hjc, red, fun x => hr x, hun⟩

/-- **`AlgFrobRed` from the leaves `GoodRedCofinite`, `SmoothGeomConnIntegral` and the glue
`ReductionMapGood`, `RedTorsionQbar`, `ReductionFrobGood` (proved).** -/
theorem algFrobRed_of_pieces (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (h1 : ReductionMapGood) (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_good hG (algFrobRedGood_of hS h1 h2 h3)

/-- **`TateBridge35` from I3.M0 and the five pieces (proved).** -/
theorem tateBridge35_of_pieces (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (h1 : ReductionMapGood) (h2 : RedTorsionQbar)
    (h3 : ReductionFrobGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_pieces hG hS h1 h2 h3)

/-- **Main result: `AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `ResidueAlgClosure`, `RedRelMul`, `RedTorsionQbar`,
`ReductionFrobGood` (proved).** The valuative criterion (existence and uniqueness of the lift
`Spec O_v → 𝒜`), the special fibre being an abelian variety (up to `SmoothGeomConnIntegral`), the
residue characteristic, the units `ℓⁿ` and the conjugation of the place are proved here. -/
theorem algFrobRed_of_split (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hR : ResidueAlgClosure) (hM : RedRelMul) (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_pieces hG hS (reductionMapGood_of hR hM) h2 h3

/-- **`TateBridge35` from I3.M0 and the six pieces (proved).** -/
theorem tateBridge35_of_split (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hR : ResidueAlgClosure) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_split hG hS hR hM h2 h3)

/-! ## 5. `ReductionFrobGood` from the extension of `F` and the twisted Frobenius -/

/-- `σ` restricted to `O_v`, for `σ` in the decomposition group of `v`. -/
def sigV {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ) (hσ : σ ∈ v.decompositionSubgroup ℚ) :
    v →+* v where
  toFun y := ⟨σ y, by
    have h : σ • v = v := hσ
    have h2 := ValuationSubring.smul_mem_pointwise_smul σ (y : PkgI4.Qbar) v y.2
    rw [h, AlgEquiv.smul_def] at h2
    exact h2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ _ _)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ _ _)

/-- An arithmetic Frobenius acts on `κ(v)` as `z ↦ z^p` (proved from `IsArithFrob`). -/
theorem residue_sigV {v : ValuationSubring PkgI4.Qbar} {σ : PkgI4.GQ} {p : ℕ}
    (hσ : PkgI4.IsArithFrob σ v p) (y : v) :
    IsLocalRing.residue v (sigV σ hσ.1 y) = IsLocalRing.residue v y ^ p := by
  rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  have h := hσ.2 y y.2
  simpa [sigV] using h

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtend` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model).** At a place `v ∣ p` with an abelian scheme `𝒜/O_w`,
`e : 𝒜_L ≅ A`, `σ` an arithmetic Frobenius at `v`, `F : A → A` finite surjective and
`f(x) = F ∘ x ∘ Spec(σ)` additive: there are a ring endomorphism `t` of `O_w` (it is
`σ⁻¹|_{O_w}`) and a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` such that `t` induces
`Frob⁻¹` on `κ(w)` (`t(a)^p ≡ a`), `F̃` maps the unit section to itself (over `Spec t`), and
`F̃` extends `F`: whenever `x'` is the lift of `x`, `Spec(σ|_{O_v}) ≫ x' ≫ F̃` is a lift of `f x`.

Why it is true: `f(x) ∈ A(ℚ̄)` for all `x` forces `F` to lie over `Spec(σ⁻¹|_L)`, so `F` is an
`L`-morphism `A → A^{(t)}`; `A^{(t)}` is the generic fibre of the base change `𝒜^{(t)}` of `𝒜`
along `t|_{O_w}` (`σ ∈ D(v)`, so `t(O_w) = O_w`), and I2-NMP extends it to `𝒜 → 𝒜^{(t)}`, i.e.
`F̃`; the lift identity holds on the generic point, and `F̃` fixes `0` since `f(0) = 0` and `𝒜`
is separated over the integral `Spec O_w`. `t(a)^p ≡ a` since `σ` acts on `κ(v)` as `z ↦ z^p`. -/
def FExtend : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ) (_ : PkgI4.LiesOver v p)
        (hσ : PkgI4.IsArithFrob σ v p)
        (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
        (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜 ≅ ObjBridge.toGrp A)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (Ft : 𝒜.X.left ⟶ 𝒜.X.left) (t : Ow L v →+* Ow L v),
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom t) ∧
          (∀ a, IsLocalRing.residue (Ow L v) (t a) ^ p = IsLocalRing.residue (Ow L v) a) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom t) ≫ (η[𝒜.X]).left ∧
          ∀ (x : PtQ L A)
            (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
            genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
            ∃ x'' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
              genMap v 𝒜 e (f x) = Spec.map (CommRingCat.ofHom v.subtype) ≫ x''.left ∧
              x''.left = Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft

/-- **`FrobMorph` (GLUE; the absolute Frobenius of the special fibre twisted by `F̄`).** Let `O`
be a local ring with residue field `k` of characteristic `p`, `𝒜/O` an abelian scheme,
`t : O → O` a ring map inducing `Frob⁻¹` on `k` (`t(a)^p ≡ a`) and `F̃ : 𝒜 → 𝒜` a morphism over
`Spec(t)` fixing the unit section. Then there is a `k`-morphism `β` of the special fibre
`Ā = sf 𝒜` fixing `0` with `β ∘ y = F̃ ∘ y ∘ Spec(z ↦ z^p)` on `k̄`-points (after projecting to
`𝒜`).

Why it is true: `β = Fr_Ā ≫ F̄`, with `Fr_Ā` the absolute Frobenius of the `𝔽_p`-scheme `Ā`
(over `Fr_{Spec k} = Spec(z ↦ z^p)`) and `F̄ = F̃ ×_{Spec t} Spec(t̄)` the base change (over
`Spec t̄`, `t̄ = Frob⁻¹`); `β` lies over `Spec(t̄) ∘ Spec(Frob) = id`; on a point,
`y ≫ Fr_Ā = Fr_{Spec k̄} ≫ y` (naturality of the absolute Frobenius), and `Fr_Ā, F̄` fix `0`. The
absolute Frobenius of schemes is not in Mathlib 4.35. -/
def FrobMorph : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ), p.Prime →
    CharP (IsLocalRing.ResidueField O) p →
    ∀ (𝒜 : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme 𝒜]
      (Ft : 𝒜.X.left ⟶ 𝒜.X.left) (t : O →+* O),
      Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom t) →
      (∀ a, IsLocalRing.residue O (t a) ^ p = IsLocalRing.residue O a) →
      (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom t) ≫ (η[𝒜.X]).left →
      ∃ β : (sf 𝒜).X ⟶ (sf 𝒜).X, η[(sf 𝒜).X] ≫ β = η[(sf 𝒜).X] ∧
        ∀ (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (IsLocalRing.ResidueField O)))
          (φ : AlgebraicClosure (IsLocalRing.ResidueField O) →+*
            AlgebraicClosure (IsLocalRing.ResidueField O)),
          (∀ z, φ z = z ^ p) →
          (y ≫ β).left ≫
              pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) =
            Spec.map (CommRingCat.ofHom φ) ≫ y.left ≫
              pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) ≫ Ft

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionFrobGood` from `SmoothGeomConnIntegral`, `FExtend` and `FrobMorph` (proved)**,
with rigidity (`G0FibreSimple.rigidityHom`, proved from Mathlib by mul-rigidity, copied
verbatim): `ᾱ = β` is a homomorphism because it fixes `0`; the reduction of `f x` is computed
from the lift `Spec(σ|_{O_v}) ≫ x' ≫ F̃` and `residue_sigV` (`σ` is `z ↦ z^p` on `κ(v)`, and
`j` commutes with `z ↦ z^p`). -/
theorem reductionFrobGood_of (hS : SmoothGeomConnIntegral) (hE : FExtend) (hFr : FrobMorph) :
    ReductionFrobGood := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, t, hover, hres, hzero, hlift⟩ := hE L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  haveI := charP_kw (L := L) hp hv
  obtain ⟨β, hβ0, hβ⟩ := hFr (Ow L v) p hp inferInstance 𝒜 Ft t hover hres hzero
  haveI hAV := sf_isAbelianVariety hS 𝒜
  haveI hmon : IsMonHom β := G0FibreSimple.rigidityHom _ (ObjBridge.ofGrp (sf 𝒜))
    (ObjBridge.ofGrp (sf 𝒜)) β hβ0
  refine ⟨Grp.homMk β, fun j x y ⟨x', hx', hy⟩ => ?_⟩
  obtain ⟨x'', hx'', hx''eq⟩ := hlift x x' hx'
  refine ⟨x'', hx'', ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure (kw L v)) p :=
    charP_of_injective_algebraMap (algebraMap (kw L v) _).injective p
  have h1 := hβ y (frobenius _ p) (fun z => rfl)
  have hring : Spec.map (CommRingCat.ofHom (frobenius (AlgebraicClosure (kw L v)) p)) ≫
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    simp only [RingHom.comp_apply, residue_sigV hσ, map_pow, frobenius_def]
  have h3 := congrArg (fun m => Spec.map (CommRingCat.ofHom
    (frobenius (AlgebraicClosure (kw L v)) p)) ≫ m ≫ Ft) hy
  have h5 : Spec.map (CommRingCat.ofHom (frobenius (AlgebraicClosure (kw L v)) p)) ≫
      (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        x'.left) ≫ Ft =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft := by
    have h4 := congrArg (fun m => m ≫ x'.left ≫ Ft) hring
    simp only [Category.assoc] at h4 ⊢
    exact h4
  have h2 := (congrArg (fun m => Spec.map (CommRingCat.ofHom
    (frobenius (AlgebraicClosure (kw L v)) p)) ≫ m) (Category.assoc y.left _ Ft).symm).trans
    (h3.trans h5)
  rw [hx''eq]
  exact h1.trans h2

/-! ## 6. `ResidueAlgClosure` from two statements on residue fields -/

/-- `O_w → O_v` is a local homomorphism (proved). -/
instance isLocalHom_toW (L : IF) (v : ValuationSubring PkgI4.Qbar) :
    IsLocalHom (PkgI2.toW (Ow L v) v rfl) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : ((a : Ow L v) : L) ∈ (Ow L v).nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hna)
  have h2 : ((PkgI2.toW (Ow L v) v rfl a : v) : PkgI4.Qbar) ∈ v.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at h1 ⊢
    show algebraMap L PkgI4.Qbar (a : L) = 0 ∨ (algebraMap L PkgI4.Qbar (a : L))⁻¹ ∉ v
    rcases h1 with h | h
    · left; rw [h, map_zero]
    · right; rw [← map_inv₀]; exact h
  exact (IsLocalRing.mem_maximalIdeal _).mp (ValuationSubring.coe_mem_nonunits_iff.mp h2) ha

/-- **`ResidueAlgClosed` (GLUE, standard: the residue field of a valuation ring of an
algebraically closed field is algebraically closed; e.g. Engler–Prestel, *Valued fields* (2005),
Thm 3.2.11 (locator UNVERIFIED)).** Proof idea: lift a monic polynomial to `O_v`, take a root in
`ℚ̄`; it is integral over `O_v`, hence in `O_v`; reduce. -/
def ResidueAlgClosed : Prop :=
  ∀ v : ValuationSubring PkgI4.Qbar, IsAlgClosed (IsLocalRing.ResidueField v)

/-- **`ResidueAlgebraic` (GLUE, standard: the residue extension of an algebraic extension of
valued fields is algebraic; Bourbaki, *Alg. Comm.* VI §8.1, Engler–Prestel Cor. 3.2.3 (locators
UNVERIFIED)).** `κ(v)` is algebraic over `κ(w)`, `w = v ∩ L`, for the map induced by
`O_w → O_v`. -/
def ResidueAlgebraic : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar),
    @Algebra.IsAlgebraic (kw L v) (IsLocalRing.ResidueField v) _ _
      (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra

/-- **`ResidueAlgClosed` holds (proved from Mathlib):** lift a monic irreducible `q` over `κ(v)`
to a monic `Q` over `O_v`, take a root `z ∈ ℚ̄` of `Q`; `z` is integral over the integrally closed
`O_v`, so `z ∈ O_v`, and its residue is a root of `q`. -/
theorem residueAlgClosed : ResidueAlgClosed := by
  intro v
  refine IsAlgClosed.of_exists_root _ (fun q hq hirr => ?_)
  obtain ⟨Q, hQmap, hQdeg, hQmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective q) hq
  have hinj : Function.Injective (algebraMap v PkgI4.Qbar) := IsFractionRing.injective v PkgI4.Qbar
  have hdeg : (Q.map (algebraMap v PkgI4.Qbar)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    intro h
    have h1 : Q.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some h
    rw [hQdeg] at h1
    exact (Irreducible.natDegree_pos hirr).ne' h1
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz
  have hint : IsIntegral v z := ⟨Q, hQmon, hz⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [Polynomial.eval₂_hom] at hz
  have h0 : Q.eval y = 0 := hinj (hz.trans (map_zero _).symm)
  refine ⟨IsLocalRing.residue v y, ?_⟩
  rw [← hQmap, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]

/-- **`ResidueAlgebraic` holds (proved from Mathlib):** for `y ∈ O_v`, take `P ∈ L[X]`, `P ≠ 0`,
`P(y) = 0`, and divide by a coefficient of largest valuation for `O_w`: the result has
coefficients in `O_w` and a coefficient `1`, so its reduction is a nonzero polynomial over `κ(w)`
vanishing at the residue of `y`. -/
theorem residueAlgebraic : ResidueAlgebraic := by
  intro L _ v
  letI : Algebra (kw L v) (IsLocalRing.ResidueField v) :=
    (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra
  refine ⟨fun z => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  have hyalg : IsAlgebraic L (y : PkgI4.Qbar) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (y : PkgI4.Qbar)).tower_top L
  obtain ⟨P, hP0, hPy⟩ := hyalg
  obtain ⟨i, hi, hmax⟩ := P.support.exists_max_image (fun n => (Ow L v).valuation (P.coeff n))
    (Polynomial.support_nonempty.mpr hP0)
  have hci : P.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hlift : P * Polynomial.C (P.coeff i)⁻¹ ∈ Polynomial.lifts (algebraMap (Ow L v) L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_mul_C]
    have hmem : P.coeff n * (P.coeff i)⁻¹ ∈ Ow L v := by
      rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
      by_cases hn : n ∈ P.support
      · exact mul_inv_le_one_of_le₀ (hmax n hn) zero_le'
      · rw [Polynomial.notMem_support_iff.mp hn, map_zero, zero_mul]
        exact zero_le'
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts _).mp hlift
  have hinjO : Function.Injective (algebraMap (Ow L v) L) := IsFractionRing.injective (Ow L v) L
  have hQi : Q.coeff i = 1 := by
    apply hinjO
    rw [← Polynomial.coeff_map, hQ, Polynomial.coeff_mul_C, mul_inv_cancel₀ hci, map_one]
  refine ⟨Q.map (IsLocalRing.residue (Ow L v)), ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun r => r.coeff i) h0
    simp only [Polynomial.coeff_map, hQi, map_one, Polynomial.coeff_zero] at h1
    exact one_ne_zero h1
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap (kw L v) (IsLocalRing.ResidueField v)).comp
        (IsLocalRing.residue (Ow L v)) =
        (IsLocalRing.residue v).comp (PkgI2.toW (Ow L v) v rfl) := by
      ext a
      exact IsLocalRing.ResidueField.map_residue _ a
    rw [hcomp, ← Polynomial.hom_eval₂]
    have hzero : Q.eval₂ (PkgI2.toW (Ow L v) v rfl) y = 0 := by
      apply IsFractionRing.injective v PkgI4.Qbar
      rw [map_zero]
      have e1 := Polynomial.hom_eval₂ Q (PkgI2.toW (Ow L v) v rfl) (algebraMap v PkgI4.Qbar) y
      have e2 : (algebraMap v PkgI4.Qbar).comp (PkgI2.toW (Ow L v) v rfl) =
          (algebraMap L PkgI4.Qbar).comp (algebraMap (Ow L v) L) := rfl
      rw [e1, e2, ← Polynomial.eval₂_map, hQ, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      have e3 : P.eval₂ (algebraMap L PkgI4.Qbar) (algebraMap v PkgI4.Qbar y) = 0 := hPy
      rw [e3, zero_mul]
    rw [hzero, map_zero]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ResidueAlgClosure` from `ResidueAlgClosed` and `ResidueAlgebraic` (proved):** `κ(v)` is an
algebraic closure of `κ(w)`, so `IsAlgClosure.equiv` gives `j`. -/
theorem residueAlgClosure_of (h1 : ResidueAlgClosed) (h2 : ResidueAlgebraic) :
    ResidueAlgClosure := by
  intro L _ v p _ _
  letI : Algebra (kw L v) (IsLocalRing.ResidueField v) :=
    (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra
  haveI : IsAlgClosed (IsLocalRing.ResidueField v) := h1 v
  haveI : Algebra.IsAlgebraic (kw L v) (IsLocalRing.ResidueField v) := h2 L v
  haveI : IsAlgClosure (kw L v) (IsLocalRing.ResidueField v) := ⟨inferInstance, inferInstance⟩
  let e := IsAlgClosure.equiv (kw L v) (IsLocalRing.ResidueField v) (AlgebraicClosure (kw L v))
  refine ⟨e.toRingEquiv.toRingHom, e.bijective, fun a => ?_⟩
  have h3 : IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a) =
      algebraMap (kw L v) (IsLocalRing.ResidueField v) (IsLocalRing.residue (Ow L v) a) :=
    (IsLocalRing.ResidueField.map_residue _ a).symm
  show e (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) = _
  rw [h3, AlgEquiv.commutes]

/-! ## 7. `RedRelMul` from the adjunction `Over.map ⊣ Over.pullback` -/

section RedMul

open scoped CategoryTheory.Obj

/-- The adjunction bijection `Hom(T, g^* M) ≃ Hom(g_! T, M)` is multiplicative (as in
unram-tate's `homEquiv_mul`), here for the inverse map. -/
theorem pb_symm_mul {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S')
    (u w : T ⟶ (Over.pullback g).obj M) :
    ((Over.mapPullbackAdj g).homEquiv T M).symm (u * w) =
      ((Over.mapPullbackAdj g).homEquiv T M).symm u *
        ((Over.mapPullbackAdj g).homEquiv T M).symm w := by
  obtain ⟨p, rfl⟩ := ((Over.mapPullbackAdj g).homEquiv T M).surjective u
  obtain ⟨q, rfl⟩ := ((Over.mapPullbackAdj g).homEquiv T M).surjective w
  have hm : (Over.mapPullbackAdj g).homEquiv T M (p * q) =
      (Over.mapPullbackAdj g).homEquiv T M p * (Over.mapPullbackAdj g).homEquiv T M q := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_mul, MonObj.comp_mul]
  rw [← hm, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end RedMul

/-- `pb_symm_mul` for the group law of `(Over.pullback g).mapGrp.obj G` (the one of `sf 𝒜` and of
`𝒜_L`). -/
theorem pb_symm_mul' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (u w : T ⟶ ((Over.pullback g).mapGrp.obj G).X) :
    ((Over.mapPullbackAdj g).homEquiv T G.X).symm (u * w) =
      ((Over.mapPullbackAdj g).homEquiv T G.X).symm u *
        ((Over.mapPullbackAdj g).homEquiv T G.X).symm w :=
  pb_symm_mul g G.X T u w

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedRelMul` holds (proved):** the product of the lifts lifts the sum, and on both the
generic point and the special fibre the passage to `𝒜` is the adjunction bijection, which is
multiplicative (`pb_symm_mul'`); `e.inv` is a homomorphism. -/
theorem redRelMul : RedRelMul := by
  intro L _ A v 𝒜 _ e j x₁ x₂ y₁ y₂ ⟨x'₁, g₁, c₁⟩ ⟨x'₂, g₂, c₂⟩
  refine ⟨x'₁ * x'₂, ?_, ?_⟩
  · have hw : Spec.map (CommRingCat.ofHom v.subtype) ≫
        (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom =
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj
          (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar)).hom := by
      simp only [Over.mk_hom, Over.map_obj_hom, PkgI3.AbVar.ptObj]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    let ι0 : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj
        (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) :=
      Over.homMk (Spec.map (CommRingCat.ofHom v.subtype)) hw
    let u : PtQ L A → (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar ⟶
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜).X) := fun x => genPt v 𝒜 e x
    have hs : ∀ (x : PtQ L A)
        (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
        genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
        ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).homEquiv
          _ 𝒜.X).symm (u x) = ι0 ≫ x' := fun x x' h => Over.OverMorphism.ext h
    have hmul : u (x₁ + x₂) = u x₁ * u x₂ := by
      show (Additive.toMul x₁ * Additive.toMul x₂) ≫ e.inv.hom.hom =
        (Additive.toMul x₁ ≫ e.inv.hom.hom) * (Additive.toMul x₂ ≫ e.inv.hom.hom)
      exact MonObj.mul_comp _ _ _
    have key : ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
        (algebraMap (Ow L v) L)))).homEquiv _ 𝒜.X).symm (u (x₁ + x₂)) = ι0 ≫ (x'₁ * x'₂) :=
      (congrArg ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
        (algebraMap (Ow L v) L)))).homEquiv _ 𝒜.X).symm hmul).trans
        ((pb_symm_mul' _ 𝒜 _ (u x₁) (u x₂)).trans
          (by rw [hs x₁ x'₁ g₁, hs x₂ x'₂ g₂, MonObj.comp_mul]))
    exact congrArg Over.Hom.left key
  · have keyc : ∀ (T' : Scheme) (u : T' ⟶ pullback 𝒜.X.hom
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))),
        (u ≫ pullback.fst _ _) ≫ 𝒜.X.hom = (u ≫ pullback.snd _ _) ≫
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))) := fun T' u => by
      rw [Category.assoc, pullback.condition, Category.assoc]
    have h2 := (keyc _ y₁.left).trans (congrArg (· ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v)))) (Over.w y₁))
    have h1 := congrArg (· ≫ 𝒜.X.hom) c₁
    have h3 : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue v)) ≫ x'₁.left) ≫ 𝒜.X.hom =
        (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue v))) ≫
          (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
      rw [Category.assoc, Category.assoc, Category.assoc, Over.w x'₁]
    have hw' : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue v))) ≫
          (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom =
        ((Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
          (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v)))).hom :=
      h3.symm.trans (h1.symm.trans h2)
    let ι1 : (Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
        (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) :=
      Over.homMk (Spec.map (CommRingCat.ofHom j) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue v))) hw'
    have hs : ∀ (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)))
        (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
        y.left ≫ pullback.fst 𝒜.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
          Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
            x'.left →
        ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm y = ι1 ≫ x' :=
      fun y x' h => Over.OverMorphism.ext (h.trans (Category.assoc _ _ _).symm)
    have key : ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm (y₁ * y₂) =
        ι1 ≫ (x'₁ * x'₂) :=
      (pb_symm_mul' _ 𝒜 _ y₁ y₂).trans (by rw [hs y₁ x'₁ c₁, hs y₂ x'₂ c₂, MonObj.comp_mul])
    exact (congrArg Over.Hom.left key).trans (Category.assoc _ _ _)


/-! ## 8. `RedTorsionQbar` from the leaf I2-Red (transport along `L‾ ≅ ℚ̄`) -/

section RedMul2

open scoped CategoryTheory.Obj

/-- The adjunction bijection `Hom(g_! T, M) ≃ Hom(T, g^* M)` is multiplicative. -/
theorem pb_mul {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S')
    (p q : (Over.map g).obj T ⟶ M) :
    (Over.mapPullbackAdj g).homEquiv T M (p * q) =
      (Over.mapPullbackAdj g).homEquiv T M p * (Over.mapPullbackAdj g).homEquiv T M q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

set_option synthInstance.maxHeartbeats 400000 in
/-- The adjunction bijection sends `1` to `1`. -/
theorem pb_one {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S') :
    (Over.mapPullbackAdj g).homEquiv T M 1 = 1 := by
  rw [Adjunction.homEquiv_unit, Functor.map_one, MonObj.comp_one]

end RedMul2

/-- `pb_mul` at the group law of `(Over.pullback g).mapGrp.obj G`. -/
theorem pb_mul' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (p q : (Over.map g).obj T ⟶ G.X) (r u w : T ⟶ ((Over.pullback g).mapGrp.obj G).X)
    (hr : r = (Over.mapPullbackAdj g).homEquiv T G.X (p * q))
    (hu : u = (Over.mapPullbackAdj g).homEquiv T G.X p)
    (hw : w = (Over.mapPullbackAdj g).homEquiv T G.X q) : r = u * w := by
  subst hr hu hw
  exact pb_mul g G.X T p q

set_option synthInstance.maxHeartbeats 400000 in
/-- `pb_one` at the group law of `(Over.pullback g).mapGrp.obj G`. -/
theorem pb_one' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (r : T ⟶ ((Over.pullback g).mapGrp.obj G).X)
    (hr : r = (Over.mapPullbackAdj g).homEquiv T G.X 1) : r = 1 := by
  subst hr
  exact pb_one g G.X T

/-- **`OwDVR` (GLUE, standard: a valuation ring of a number field in which `p` is not a unit is
the localization of `𝓞_L` at a nonzero prime, a DVR; e.g. Neukirch, *Algebraic Number Theory*,
Ch. II (locator UNVERIFIED)).** Needed to apply I2-Red, whose base is a DVR. -/
def OwDVR : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar) (p : ℕ), p.Prime →
    PkgI4.LiesOver v p → IsDiscreteValuationRing (Ow L v)

/-- The place `w = ψ⁻¹(v)` of `L‾` for an `L`-isomorphism `ψ : L‾ ≅ ℚ̄`. -/
abbrev wOf {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar) :
    ValuationSubring (AlgebraicClosure L) :=
  v.comap (ψ : AlgebraicClosure L →+* PkgI4.Qbar)

theorem hw_of {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) :
    (wOf ψ v).comap (algebraMap L (AlgebraicClosure L)) = Ow L v := by
  ext x
  simp [ValuationSubring.mem_comap]

/-- `ψ` restricted to `O_w ≅ O_v`. -/
def psiW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar) :
    wOf ψ v ≃+* v where
  toFun y := ⟨ψ y, y.2⟩
  invFun z := ⟨ψ.symm z, by
    show ψ (ψ.symm z) ∈ v
    rw [AlgEquiv.apply_symm_apply]
    exact z.2⟩
  left_inv y := Subtype.ext (ψ.symm_apply_apply _)
  right_inv z := Subtype.ext (ψ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul ψ _ _)
  map_add' a b := Subtype.ext (map_add ψ _ _)

theorem psiW_toW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (a : Ow L v) :
    psiW ψ v (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v) a) = PkgI2.toW (Ow L v) v rfl a :=
  Subtype.ext (by
    show ψ (algebraMap L (AlgebraicClosure L) (a : L)) = algebraMap L PkgI4.Qbar (a : L)
    exact ψ.commutes _)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Spec(j ∘ κ(ψ)) : Spec κ(w)‾ → Spec κ(w')` over `Spec O_w`, where `w' = ψ⁻¹(v)` (an
isomorphism when `j` is bijective). -/
def iotaW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    (Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
        (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) (by
    simp only [Over.mk_hom, Over.map_obj_hom, PkgI2.specOver]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rw [psiW_toW ψ v a]
    exact hjc a)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Θ`: I2's `κ(w')`-points of `𝒜` to `κ(w)‾`-points of the special fibre (the adjunction
bijection applied to `ι ≫ y`, written out). -/
def thetaW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)) :=
  Over.homMk (pullback.lift (iotaW ψ v j hjc ≫ y).left
    (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))).hom (Over.w (iotaW ψ v j hjc ≫ y)))
    (pullback.lift_snd _ _ _)

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_left {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    (thetaW ψ v 𝒜 j hjc y).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
      Spec.map (CommRingCat.ofHom
        (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) ≫ y.left :=
  pullback.lift_fst _ _ _

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_symm {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm (thetaW ψ v 𝒜 j hjc y) =
      iotaW ψ v j hjc ≫ y :=
  Over.OverMorphism.ext (thetaW_left ψ v 𝒜 j hjc y)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Θ` as a monoid homomorphism. -/
def thetaHom {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) →*
      PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)) where
  toFun := thetaW ψ v 𝒜 j hjc
  map_one' := by
    apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
    rw [thetaW_symm, MonObj.comp_one]
    have h := pb_one' (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) 𝒜
      (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) _ rfl
    exact (((Over.mapPullbackAdj _).homEquiv _ 𝒜.X).symm_apply_eq.mpr h.symm).symm
  map_mul' y₁ y₂ := by
    apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
    rw [thetaW_symm, MonObj.comp_mul]
    exact ((pb_symm_mul' _ 𝒜 _ (thetaW ψ v 𝒜 j hjc y₁) (thetaW ψ v 𝒜 j hjc y₂)).trans
      (by rw [thetaW_symm, thetaW_symm])).symm

set_option synthInstance.maxHeartbeats 400000 in
theorem iotaW_isIso_left {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j) :
    IsIso (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) := by
  have hb : Function.Bijective (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom) :=
    hjb.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).bijective
  haveI : IsIso (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_injective {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j)
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    Function.Injective (thetaW ψ v 𝒜 j hjc) := by
  intro y₁ y₂ h
  haveI := iotaW_isIso_left ψ v j hjb
  have h1 := congrArg ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm h
  rw [thetaW_symm, thetaW_symm] at h1
  have h2 := congrArg Over.Hom.left h1
  apply Over.OverMorphism.ext
  exact (cancel_epi (Spec.map (CommRingCat.ofHom
    (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)))).mp h2

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_surjective {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j)
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    Function.Surjective (thetaW ψ v 𝒜 j hjc) := by
  intro yt
  haveI := iotaW_isIso_left ψ v j hjb
  let z := ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm yt
  have hz2 : z.left ≫ 𝒜.X.hom = (iotaW ψ v j hjc).left ≫ (Over.mk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v)))))).hom :=
    (Over.w z).trans (Over.w (iotaW ψ v j hjc)).symm
  have hw : (inv (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) ≫ z.left) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v)))))).hom :=
    (Category.assoc _ _ _).trans ((congrArg (inv (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) ≫ ·) hz2).trans
      (IsIso.inv_hom_id_assoc _ _))
  refine ⟨Over.homMk _ hw, ?_⟩
  apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
  rw [thetaW_symm]
  apply Over.OverMorphism.ext
  exact IsIso.hom_inv_id_assoc (Spec.map (CommRingCat.ofHom
    (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) z.left

set_option synthInstance.maxHeartbeats 400000 in
/-- **I2's reduction relation gives `RedRel`** (transport along `ψ`; proved). -/
theorem redRel_of_isReductionOf {L : IF} {A : PkgI3.AbVar L}
    (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (x : A.Pt (AlgebraicClosure L))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X)
    (h : PkgI2.IsReductionOf 𝒜 e (wOf ψ v) (hw_of ψ v) x y) :
    RedRel v 𝒜 e j (Additive.ofMul (UnramTate.trPt A ψ x)) (thetaW ψ v 𝒜 j hjc y) := by
  obtain ⟨xw, hg, hc⟩ := h
  have hov : (Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) ≫ xw.left) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
    rw [Category.assoc, Over.w xw]
    simp only [Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact congrArg Subtype.val (psiW_toW ψ v a)
  refine ⟨Over.homMk _ hov, ?_, ?_⟩
  · have hring : Spec.map (CommRingCat.ofHom (ψ : AlgebraicClosure L →+* PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (wOf ψ v).subtype) =
        Spec.map (CommRingCat.ofHom v.subtype) ≫
          Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    have h1 := congrArg (Spec.map (CommRingCat.ofHom
      (ψ : AlgebraicClosure L →+* PkgI4.Qbar)) ≫ ·) hg
    have h2 := congrArg (· ≫ xw.left) hring
    simp only [Category.assoc] at h2
    exact ((Category.assoc _ _ _).trans h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ xw.left) hring).trans (Category.assoc _ _ _)))
  · have hring : Spec.map (CommRingCat.ofHom
        (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (wOf ψ v))) =
        Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
          Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    refine (thetaW_left ψ v 𝒜 j hjc y).trans ?_
    rw [hc]
    have h3 := congrArg (· ≫ xw.left) hring
    simp only [Category.assoc] at h3
    exact h3

/-- `t = σ⁻¹|_{O_w}` (for `σ ∈ D(v)`, `L/ℚ` Galois). -/
def tSig {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ)
    (hσ : σ ∈ v.decompositionSubgroup ℚ) : Ow L v →+* Ow L v where
  toFun a := ⟨(σ⁻¹).restrictNormal L (a : L), by
    show algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L)) ∈ v
    rw [AlgEquiv.restrictNormal_commutes]
    exact (sigV σ⁻¹ (inv_mem hσ) ⟨_, a.2⟩).2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

/-- `t = σ⁻¹|_{O_w}` induces `Frob⁻¹` on `κ(w)` (proved from `IsArithFrob`). -/
theorem tSig_residue {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} {σ : PkgI4.GQ}
    {p : ℕ} (hσ : PkgI4.IsArithFrob σ v p) (a : Ow L v) :
    IsLocalRing.residue (Ow L v) (tSig σ hσ.1 a) ^ p = IsLocalRing.residue (Ow L v) a := by
  apply (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).injective
  rw [map_pow, IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
    ← residue_sigV hσ]
  congr 1
  apply Subtype.ext
  show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L))) =
    algebraMap L PkgI4.Qbar (a : L)
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendCore` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model).** `FExtend` with `t = σ⁻¹|_{O_w}` fixed (`tSig`): there is
a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` fixing the unit section and extending `F`
(whenever `x'` is the lift of `x`, `Spec(σ|_{O_v}) ≫ x' ≫ F̃` is a lift of `f x`). See `FExtend`
for why it is true. -/
def FExtendCore : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ) (_ : PkgI4.LiesOver v p)
        (hσ : PkgI4.IsArithFrob σ v p)
        (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
        (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜 ≅ ObjBridge.toGrp A)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ Ft : 𝒜.X.left ⟶ 𝒜.X.left,
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ≫ (η[𝒜.X]).left ∧
          ∀ (x : PtQ L A)
            (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
            genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
            ∃ x'' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
              genMap v 𝒜 e (f x) = Spec.map (CommRingCat.ofHom v.subtype) ≫ x''.left ∧
              x''.left = Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft

/-- **`FExtend` from `FExtendCore` (proved):** `t = tSig σ`, `t(a)^p ≡ a` by `tSig_residue`. -/
theorem fExtend_of_core (h : FExtendCore) : FExtend := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, h1, h2, h3⟩ := h L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  exact ⟨Ft, tSig σ hσ.1, h1, tSig_residue hσ, h2, h3⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendGen` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model `𝒜^{(t)}`).** For `F`, `σ`, `f` as in `FExtend` and
`t = σ⁻¹|_{O_w}`: there is a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` fixing the unit
section whose restriction to the generic fibre is `F` (through `e`):
`e⁻¹ ≫ pr₁ ≫ F̃ = F ≫ e⁻¹ ≫ pr₁` as maps `A → 𝒜`.

Why it is true: `f(x) ∈ A(ℚ̄)` for all `x` forces `F` to lie over `Spec(σ⁻¹|_L)`, so `F` is an
`L`-morphism `A → A^{(t)}`; I2-NMP for `𝒜` and its base change `𝒜^{(t)}` along `Spec t` extends
it; `F̃` fixes the unit section because both sides are sections of the separated `𝒜 → Spec O_w`
agreeing at the generic point (`f(0) = 0`). -/
def FExtendGen : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ) (_ : PkgI4.LiesOver v p)
        (hσ : PkgI4.IsArithFrob σ v p)
        (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
        (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜 ≅ ObjBridge.toGrp A)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ Ft : 𝒜.X.left ⟶ 𝒜.X.left,
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ≫ (η[𝒜.X]).left ∧
          (e.inv.hom.hom : A.X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap (Ow L v) L)))).obj 𝒜.X).left ≫
            pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) ≫ Ft =
          F ≫ (e.inv.hom.hom : A.X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap (Ow L v) L)))).obj 𝒜.X).left ≫
            pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendCore` from `FExtendGen` (proved):** the lift of `f x` is
`Spec(σ|_{O_v}) ≫ x' ≫ F̃`; it lies over `Spec(toW)` since `σ ∘ t = id` on `O_w`, and restricts to
`f x` by `hf`, the generic compatibility and `Spec σ ≫ Spec(O_v ⊂ ℚ̄) = Spec(O_v ⊂ ℚ̄) ≫ Spec σ_v`. -/
theorem fExtendCore_of_gen (h : FExtendGen) : FExtendCore := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, h1, h2, h3⟩ := h L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  refine ⟨Ft, h1, h2, fun x x' hx' => ?_⟩
  have hring1 : Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) ≫
        Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) =
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L))) =
      algebraMap L PkgI4.Qbar (a : L)
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hov : (Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
    rw [Category.assoc, Category.assoc, h1, ← Category.assoc x'.left, Over.w x']
    exact hring1
  refine ⟨Over.homMk _ hov, ?_, rfl⟩
  have hring2 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom v.subtype) =
      Spec.map (CommRingCat.ofHom v.subtype) ≫ Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hfx := hf x
  have hx'' := (Category.assoc _ _ _).symm.trans hx'
  have hx3 := ((congrArg ((Additive.toMul x).left ≫ ·) (Category.assoc _ _ Ft).symm).trans
    (Category.assoc _ _ Ft).symm).trans ((congrArg (· ≫ Ft) hx'').trans (Category.assoc _ _ _))
  exact (Category.assoc _ _ _).trans <|
    (congrArg (· ≫ _) hfx).trans <|
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans <|
    (congrArg (fun m => _ ≫ (Additive.toMul x).left ≫ m) h3.symm).trans <|
    (congrArg (_ ≫ ·) hx3).trans <|
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x'.left ≫ Ft) hring2).trans
      (Category.assoc _ _ _))

/-! ## 9. `FrobMorph` from the existence of the absolute Frobenius -/

/-- **`AbsFrob` (GLUE; the absolute Frobenius of an `𝔽_p`-scheme; standard, e.g. SGA 5 XIV,
Stacks Tag 0CC6 (locators UNVERIFIED); not in Mathlib 4.35).** For a scheme `X` over a field `k`
of characteristic `p` there is an endomorphism `Fr_X` (the identity on the space, `f ↦ f^p` on
sections) lying over `Fr_{Spec k} = Spec(z ↦ z^p)`, and natural for points: for every ring `R` of
characteristic `p` and `g : Spec R → X`, `Spec(r ↦ r^p) ≫ g = g ≫ Fr_X`. -/
def AbsFrob : Prop :=
  ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (X : Over (Spec (.of k))),
    ∃ Fr : X.left ⟶ X.left,
      Fr ≫ X.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (frobenius k p)) ∧
      ∀ (R : Type) [CommRing R] [CharP R p] (g : Spec (.of R) ⟶ X.left),
        Spec.map (CommRingCat.ofHom (frobenius R p)) ≫ g = g ≫ Fr

/-- A ring endomorphism inducing an inverse Frobenius on the residue field is local. -/
theorem isLocalHom_of_resPow {O : Type} [CommRing O] [IsLocalRing O] {p : ℕ} (hp : p.Prime)
    (t : O →+* O) (hres : ∀ a, IsLocalRing.residue O (t a) ^ p = IsLocalRing.residue O a) :
    IsLocalHom t := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : IsLocalRing.residue O a = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hna)
  rw [← hres a] at h1
  have h2 : IsLocalRing.residue O (t a) = 0 := pow_eq_zero_iff hp.ne_zero |>.mp h1
  exact ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h2)) ha

/-- The unit section of the special fibre, followed by the projection to `𝒜`, is the closed
point followed by the unit section of `𝒜` (proved). -/
theorem sf_eta_fst {O : Type} [CommRing O] [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) :
    (η[(sf 𝒜).X]).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ (η[𝒜.X]).left := by
  let g' := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  let F := Over.pullback g'
  have hε : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙 (Spec (.of O))) g' = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε F)
  have hε2 : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 (Spec (.of O))) g' = g' := by
    have hc : pullback.fst (𝟙 (Spec (.of O))) g' = pullback.snd (𝟙 (Spec (.of O))) g' ≫ g' := by
      rw [← pullback.condition, Category.comp_id]
    rw [hc, ← Category.assoc, hε, Category.id_comp]
  have hmap : (F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' =
      pullback.fst (𝟙 (Spec (.of O))) g' ≫ (η[𝒜.X]).left := pullback.lift_fst _ _ _
  show ((Functor.LaxMonoidal.ε F) ≫ F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε2]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FrobMorph` from `AbsFrob` (proved):** `β = Fr_Ā ≫ F̄`, with `F̄ = F̃ ×_{Spec t} Spec(t̄)`
(`pullback.map`) and `t̄` the map induced by `t` on `κ(O)` (`t̄ = Frob⁻¹`); `β` lies over
`Spec(Frob ∘ t̄) = id`; it fixes `0` (`sf_eta_fst`, point-naturality at the unit section); the
point formula is point-naturality at `y`. -/
theorem frobMorph_of (hA : AbsFrob) : FrobMorph := by
  intro O _ _ p hp hk 𝒜 _ Ft t hover hres hzero
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := isLocalHom_of_resPow hp t hres
  let tb := IsLocalRing.ResidueField.map t
  have htb : ∀ z, frobenius (IsLocalRing.ResidueField O) p (tb z) = z := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact hres a
  let g' := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  have heq2 : g' ≫ Spec.map (CommRingCat.ofHom t) = Spec.map (CommRingCat.ofHom tb) ≫ g' := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hid : Spec.map (CommRingCat.ofHom (frobenius (IsLocalRing.ResidueField O) p)) ≫
      Spec.map (CommRingCat.ofHom tb) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show (frobenius (IsLocalRing.ResidueField O) p).comp tb = RingHom.id _ from
      RingHom.ext htb, CommRingCat.ofHom_id, Spec.map_id]
  let Fb : pullback 𝒜.X.hom g' ⟶ pullback 𝒜.X.hom g' :=
    pullback.map 𝒜.X.hom g' 𝒜.X.hom g' Ft (Spec.map (CommRingCat.ofHom tb))
      (Spec.map (CommRingCat.ofHom t)) hover.symm heq2
  have hFb1 : Fb ≫ pullback.fst 𝒜.X.hom g' = pullback.fst 𝒜.X.hom g' ≫ Ft :=
    pullback.lift_fst _ _ _
  have hFb2 : Fb ≫ pullback.snd 𝒜.X.hom g' =
      pullback.snd 𝒜.X.hom g' ≫ Spec.map (CommRingCat.ofHom tb) := pullback.lift_snd _ _ _
  obtain ⟨Fr0, hFr1, hFr2⟩ := hA (IsLocalRing.ResidueField O) p
    (Over.mk (pullback.snd 𝒜.X.hom g'))
  let Fr : pullback 𝒜.X.hom g' ⟶ pullback 𝒜.X.hom g' := Fr0
  have hFr1' : Fr ≫ pullback.snd 𝒜.X.hom g' = pullback.snd 𝒜.X.hom g' ≫
      Spec.map (CommRingCat.ofHom (frobenius (IsLocalRing.ResidueField O) p)) := hFr1
  have hFr2' : ∀ (R : Type) [CommRing R] [CharP R p] (g : Spec (.of R) ⟶ pullback 𝒜.X.hom g'),
      Spec.map (CommRingCat.ofHom (frobenius R p)) ≫ g = g ≫ Fr := fun R _ _ g => hFr2 R g
  have hw : (Fr ≫ Fb) ≫ pullback.snd 𝒜.X.hom g' = pullback.snd 𝒜.X.hom g' := by
    rw [Category.assoc, hFb2, ← Category.assoc, hFr1', Category.assoc, hid, Category.comp_id]
  let e0 : Spec (.of (IsLocalRing.ResidueField O)) ⟶ pullback 𝒜.X.hom g' := (η[(sf 𝒜).X]).left
  have he0 : e0 ≫ pullback.fst 𝒜.X.hom g' = g' ≫ (η[𝒜.X]).left := sf_eta_fst 𝒜
  have he0s : e0 ≫ pullback.snd 𝒜.X.hom g' = 𝟙 _ := Over.w η[(sf 𝒜).X]
  refine ⟨Over.homMk (U := (sf 𝒜).X) (V := (sf 𝒜).X) (Fr ≫ Fb) hw, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    show e0 ≫ Fr ≫ Fb = e0
    have hn := hFr2' (IsLocalRing.ResidueField O) e0
    rw [← Category.assoc, ← hn, Category.assoc]
    have hη : e0 ≫ Fb = Spec.map (CommRingCat.ofHom tb) ≫ e0 := by
      apply pullback.hom_ext
      · rw [Category.assoc, hFb1, ← Category.assoc, he0, Category.assoc, Category.assoc, he0,
          hzero, ← Category.assoc, heq2, Category.assoc]
      · rw [Category.assoc, hFb2, ← Category.assoc, he0s, Category.id_comp, Category.assoc, he0s,
          Category.comp_id]
    rw [hη, ← Category.assoc, hid, Category.id_comp]
  · intro y φ hφ
    haveI : CharP (AlgebraicClosure (IsLocalRing.ResidueField O)) p :=
      charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) _).injective p
    have hφ' : φ = frobenius _ p := RingHom.ext hφ
    subst hφ'
    let yl : Spec (.of (AlgebraicClosure (IsLocalRing.ResidueField O))) ⟶ pullback 𝒜.X.hom g' :=
      y.left
    have hn := hFr2' (AlgebraicClosure (IsLocalRing.ResidueField O)) yl
    show (yl ≫ Fr ≫ Fb) ≫ pullback.fst 𝒜.X.hom g' = _ ≫ yl ≫ pullback.fst 𝒜.X.hom g' ≫ Ft
    rw [Category.assoc, Category.assoc, hFb1, ← Category.assoc, ← Category.assoc, ← hn,
      Category.assoc, Category.assoc]

/-- **Main result, finest form: `AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `ResidueAlgClosure`, `RedRelMul`, `RedTorsionQbar`,
`FExtend`, `FrobMorph` (proved).** -/
theorem algFrobRed_of_fine (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hR : ResidueAlgClosure) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_split hG hS hR hM h2 (reductionFrobGood_of hS hE hFr)

/-- **`TateBridge35` from I3.M0 and the seven pieces (proved).** -/
theorem tateBridge35_of_fine (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hR : ResidueAlgClosure) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_fine hG hS hR hM h2 hE hFr)

/-- **`AlgFrobRed` with `ResidueAlgClosure` split (proved).** Leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`; glue `ResidueAlgClosed`, `ResidueAlgebraic`,
`RedRelMul`, `RedTorsionQbar`, `FExtend`, `FrobMorph`. -/
theorem algFrobRed_of_finest (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hC : ResidueAlgClosed) (hA : ResidueAlgebraic) (hM : RedRelMul) (h2 : RedTorsionQbar)
    (hE : FExtend) (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_fine hG hS (residueAlgClosure_of hC hA) hM h2 hE hFr

/-- **`AlgFrobRed` with `ResidueAlgClosed` discharged (proved).** Leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`; glue `ResidueAlgebraic`, `RedRelMul`,
`RedTorsionQbar`, `FExtend`, `FrobMorph`. -/
theorem algFrobRed_of_final (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hA : ResidueAlgebraic) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_finest hG hS residueAlgClosed hA hM h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the seven remaining pieces (proved).** -/
theorem tateBridge35_of_final (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hA : ResidueAlgebraic) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_final hG hS hA hM h2 hE hFr)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `RedRelMul`, `RedTorsionQbar`, `FExtend`, `FrobMorph`
(proved).** Everything else (conjugating the place, isolating the finite set, the special fibre
as an abelian variety, the residue characteristic, the valuative criterion, `κ(v) ≅ κ(w)‾`,
`σ = Frob` on `κ(v)`, rigidity) is proved here or by Mathlib / mul-rigidity. -/
theorem algFrobRed_of_main (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_final hG hS residueAlgebraic hM h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the six remaining pieces (proved).** -/
theorem tateBridge35_of_main (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_main hG hS hM h2 hE hFr)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite` and
`SmoothGeomConnIntegral` and the glue `RedTorsionQbar`, `FExtend`, `FrobMorph` (proved).**
Proved here (or in Mathlib / mul-rigidity): conjugating the place, isolating the finite set, the
special fibre as an abelian variety (from `SmoothGeomConnIntegral`), the residue characteristic and
the units `ℓⁿ`, the valuative criterion (existence and uniqueness of lifts), `κ(v) ≅ κ(w)‾`
(`residueAlgClosed`, `residueAlgebraic`), the reduction map as a homomorphism (`redRelMul`),
`σ = Frob` on `κ(v)`, rigidity. -/
theorem algFrobRed_of_five (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_main hG hS redRelMul h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the five pieces (proved).** -/
theorem tateBridge35_of_five (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_five hG hS h2 hE hFr)

/-! ### `OwDVR` (proved; adapted from neron-lg's `dvrAt_center`) -/

section DVR

open NumberField

/-- The DVR `𝓞_{L,P}` of a nonzero prime `P` of `𝓞_L`, as a valuation subring of `L` (as in
neron-lg's `dvrAt`). -/
noncomputable def dvrAt' {K : Type} [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ValuationSubring K :=
  (P.valuation K).valuationSubring

instance {K : Type} [Field K] [NumberField K] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (dvrAt' P) := by
  unfold dvrAt'; infer_instance

theorem ringOfIntegers_mem' {K : Type} [Field K] [NumberField K] (O : ValuationSubring K)
    (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO' {K : Type} [Field K] [NumberField K] (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem' O)

/-- `p ∈ 𝔪_{O_w}` for `v ∣ p`. -/
theorem natCast_mem_maximalIdeal {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hp : p.Prime) (hv : PkgI4.LiesOver v p) :
    (p : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) := by
  have h1 : ((p : Ow L v) : L) ∈ (Ow L v).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hin
    rw [ValuationSubring.mem_comap, map_inv₀] at hin
    have he : (algebraMap L PkgI4.Qbar ((p : Ow L v) : L)) = (p : PkgI4.Qbar) := by simp
    rw [he] at hin
    have hv' := hv
    unfold PkgI4.LiesOver at hv'
    rw [ValuationSubring.mem_nonunits_iff_or] at hv'
    rcases hv' with h0 | h0
    · exact (Nat.cast_ne_zero.mpr hp.ne_zero) h0
    · exact h0 hin
  exact (ValuationSubring.coe_mem_nonunits_iff).mp h1

/-- **`OwDVR` holds (proved):** `O_w` contains `𝓞_L`; its center `P = 𝔪_{O_w} ∩ 𝓞_L` is a nonzero
prime (it contains `p`); `𝓞_{L,P} ⊆ O_w`, and a DVR is a maximal proper valuation subring
(`ValuationSubring.eq_of_le_of_ne_top`), so `O_w = 𝓞_{L,P}`. -/
theorem owDVR : OwDVR := by
  intro L _ v p hp hv
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hpm := natCast_mem_maximalIdeal (L := L) hp hv
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    { asIdeal := (IsLocalRing.maximalIdeal (Ow L v)).comap (toO' (Ow L v))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        have hmem : (p : 𝓞 L) ∈ (IsLocalRing.maximalIdeal (Ow L v)).comap (toO' (Ow L v)) := by
          rw [Ideal.mem_comap, map_natCast]; exact hpm
        rw [hbot, Ideal.mem_bot] at hmem
        exact hp.ne_zero (by exact_mod_cast hmem) }
  have hP : ∀ x : 𝓞 L, x ∈ P.asIdeal ↔ toO' (Ow L v) x ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    fun x => Iff.rfl
  have heq : dvrAt' P = Ow L v := by
    apply ValuationSubring.eq_of_le_of_ne_top
    · intro x hx
      obtain ⟨n, d, hnd⟩ :=
        IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P x hx
      have hd : IsUnit (toO' (Ow L v) d) := by
        by_contra h
        exact d.2 ((hP d).2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      have hvd : (Ow L v).valuation (algebraMap (𝓞 L) L d) = 1 :=
        ((Ow L v).valuation_eq_one_iff _).1 hd
      apply (Ow L v).mem_of_valuation_le_one
      have h2 := congrArg (Ow L v).valuation hnd
      rw [map_mul, hvd, _root_.mul_one] at h2
      rw [h2]
      exact (Ow L v).valuation_le_one (toO' (Ow L v) n)
    · intro htop
      have hall : ∀ y : L, y ∈ Ow L v := by
        intro y; rw [htop]; exact ValuationSubring.mem_top y
      have hp0 : ((p : Ow L v) : L) ≠ 0 := by
        simp only [ne_eq, map_natCast]
        push_cast
        exact_mod_cast hp.ne_zero
      have hu : IsUnit (p : Ow L v) := by
        refine isUnit_iff_exists_inv.2 ⟨⟨_, hall (((p : Ow L v) : L))⁻¹⟩, Subtype.ext ?_⟩
        rw [Subring.coe_mul]
        exact mul_inv_cancel₀ hp0
      exact (IsLocalRing.mem_maximalIdeal _).1 hpm hu
  have key : ∀ O' : ValuationSubring L, dvrAt' P = O' → IsDiscreteValuationRing O' := by
    rintro O' rfl; infer_instance
  exact key _ heq

end DVR

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedTorsionQbar` from the leaf I2-Red and `OwDVR` (proved).** Transport along an
`L`-isomorphism `ψ : L‾ ≅ ℚ̄` (`UnramTate.trPt`) and the bijective homomorphism `Θ` from I2's
`κ(w')`-points of `𝒜` to the `κ(w)‾`-points of `sf 𝒜`; I2's reductions are `RedRel`s
(`redRel_of_isReductionOf`), reductions are unique (`redRel_unique`) and additive
(`redRelMul`). -/
theorem redTorsionQbar_of (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR) :
    RedTorsionQbar := by
  intro L _ A p hp v hv 𝒜 _ e j hjb hjc m hm hmu
  haveI := hD L v p hp hv
  haveI : Algebra.IsAlgebraic L PkgI4.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI : IsAlgClosure L PkgI4.Qbar := ⟨inferInstance, inferInstance⟩
  let ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar :=
    IsAlgClosure.equiv L (AlgebraicClosure L) PkgI4.Qbar
  obtain ⟨hR1, hR2⟩ := hRed L (Ow L v) (wOf ψ v) (hw_of ψ v) (ObjBridge.toGrp A) 𝒜 e m hm hmu
  let Φ := UnramTate.trPt A ψ
  let Θ := thetaHom ψ v 𝒜 j hjc
  have hΘinj := thetaW_injective ψ v 𝒜 j hjb hjc
  have hΘsurj := thetaW_surjective ψ v 𝒜 j hjb hjc
  have hT3 := redRel_of_isReductionOf (A := A) ψ v 𝒜 e j hjc
  have hun := redRel_unique v 𝒜 e j
  have hex := exists_redRel v 𝒜 e j hjc
  have hmul := redRelMul L A v 𝒜 e j
  have h01 : RedRel v 𝒜 e j 0 1 := by
    obtain ⟨z, hz⟩ := hex 0
    have h2 := hmul 0 0 z z hz hz
    rw [add_zero] at h2
    have h3 : z * z = z := hun 0 _ _ h2 hz
    have hz1 : z = 1 := mul_eq_right.mp h3
    rw [hz1] at hz
    exact hz
  have hΘ1 : ∀ y, thetaW ψ v 𝒜 j hjc y = 1 → y = 1 := fun y h =>
    hΘinj (h.trans (map_one Θ).symm)
  have htors : ∀ x : PtQ L A, m • x = 0 →
      Φ.symm (Additive.toMul x) ∈ PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) m := by
    intro x hx
    show (Φ.symm (Additive.toMul x)) ^ m = 1
    rw [← map_pow, ← toMul_nsmul, hx, toMul_zero, map_one]
  have hT3' : ∀ (x : PtQ L A) yw, PkgI2.IsReductionOf 𝒜 e (wOf ψ v) (hw_of ψ v)
      (Φ.symm (Additive.toMul x)) yw → RedRel v 𝒜 e j x (thetaW ψ v 𝒜 j hjc yw) := by
    intro x yw h
    have hr := hT3 _ yw h
    rw [show UnramTate.trPt A ψ (Φ.symm (Additive.toMul x)) = Additive.toMul x from
      Φ.apply_symm_apply _, ofMul_toMul] at hr
    exact hr
  constructor
  · intro x hx
    obtain ⟨yw, ⟨hyw1, hyw2⟩, -⟩ := hR1 _ (htors x hx)
    have hr := hT3' x yw hyw2
    refine ⟨Additive.ofMul (thetaW ψ v 𝒜 j hjc yw), ⟨?_, hr⟩, ?_⟩
    · rw [← ofMul_pow]
      show Additive.ofMul (Θ yw ^ m) = 0
      rw [← map_pow, hyw1, map_one]
      rfl
    · rintro y' ⟨-, hy'⟩
      exact Additive.toMul.injective (hun x _ _ hy' hr)
  · intro yt hyt
    obtain ⟨yw, hyw⟩ := hΘsurj (Additive.toMul yt)
    have hywt : yw ^ m = 1 := by
      apply hΘinj
      show Θ (yw ^ m) = Θ 1
      rw [map_pow, map_one]
      show (thetaW ψ v 𝒜 j hjc yw) ^ m = 1
      rw [hyw, ← toMul_nsmul, hyt, toMul_zero]
    obtain ⟨xw0, ⟨hxw1, hxw2⟩, -⟩ := hR2 yw hywt
    let xw : A.Pt (AlgebraicClosure L) := xw0
    have hr := hT3 xw yw hxw2
    rw [hyw] at hr
    have hx2t : m • Additive.ofMul (Φ xw) = 0 := by
      rw [← ofMul_pow, ← map_pow]
      have : xw ^ m = 1 := hxw1
      rw [this, map_one]
      rfl
    refine ⟨Additive.ofMul (Φ xw), ⟨hx2t, hr⟩, ?_⟩
    rintro x1 ⟨hx1t, hx1r⟩
    have hd : RedRel v 𝒜 e j (x1 - Additive.ofMul (Φ xw)) 1 := by
      obtain ⟨yd, hyd⟩ := hex (x1 - Additive.ofMul (Φ xw))
      have h3 := hmul _ _ yd (Additive.toMul yt) hyd hr
      rw [sub_add_cancel] at h3
      have h4 : yd * Additive.toMul yt = Additive.toMul yt := hun x1 _ _ h3 hx1r
      rw [mul_eq_right.mp h4] at hyd
      exact hyd
    have hdt : m • (x1 - Additive.ofMul (Φ xw)) = 0 := by
      rw [smul_sub, hx1t, hx2t, sub_zero]
    obtain ⟨yd', ⟨hyd'1, hyd'2⟩, -⟩ := hR1 _ (htors _ hdt)
    have hyd'eq : yd' = 1 := hΘ1 yd' (hun _ _ _ (hT3' _ yd' hyd'2) hd)
    have h1t : (1 : PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure L)) ∈
        PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) m := one_pow m
    obtain ⟨y0, ⟨hy01, hy02⟩, -⟩ := hR1 1 h1t
    have hy0eq : y0 = 1 := by
      have hr0 := hT3 1 y0 hy02
      rw [map_one, ofMul_one] at hr0
      exact hΘ1 y0 (hun 0 _ _ hr0 h01)
    have hxd1 := (hR2 1 (one_pow m)).unique ⟨htors _ hdt, hyd'eq ▸ hyd'2⟩ ⟨h1t, hy0eq ▸ hy02⟩
    have h5 : Additive.toMul (x1 - Additive.ofMul (Φ xw)) = 1 := by
      have h6 := congrArg Φ hxd1
      rw [MulEquiv.apply_symm_apply] at h6
      exact h6.trans (map_one Φ)
    exact sub_eq_zero.mp (Additive.toMul.injective (h5.trans toMul_zero.symm))

/-- **`AlgFrobRed` from the leaves `GoodRedCofinite`, `SmoothGeomConnIntegral`, I2-Red (kernel
leaf `PkgI2.ReductionTorsionBijective`) and the glue `OwDVR`, `FExtend`, `FrobMorph` (proved).** -/
theorem algFrobRed_of_I2 (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_five hG hS (redTorsionQbar_of hRed hD) hE hFr

/-- **`TateBridge35` from I3.M0, I2-Red and the five other pieces (proved).** -/
theorem tateBridge35_of_I2 (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR)
    (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_I2 hG hS hRed hD hE hFr)

/-- **Main result, final form: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`
and `SmoothGeomConnIntegral`, the kernel leaf I2-Red (`PkgI2.ReductionTorsionBijective`), and the
glue `FExtend` and `FrobMorph` (proved).** -/
theorem algFrobRed_of_leaves (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_I2 hG hS hRed owDVR hE hFr

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`, `FExtend`,
`FrobMorph` (proved).** -/
theorem tateBridge35_of_leaves (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtend)
    (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_leaves hG hS hRed hE hFr)

/-- **Main result, finest form: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendCore`
and `FrobMorph` (proved).** -/
theorem algFrobRed_of_core (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendCore) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_leaves hG hS hRed (fExtend_of_core hE) hFr

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendCore`, `FrobMorph` (proved).** -/
theorem tateBridge35_of_core (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendCore) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_core hG hS hRed hE hFr)

/-- **Main result with `FrobMorph` reduced: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendCore` and
`AbsFrob` (proved).** -/
theorem algFrobRed_of_absFrob (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendCore) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_core hG hS hRed hE (frobMorph_of hA)

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendCore`, `AbsFrob` (proved).** -/
theorem tateBridge35_of_absFrob (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendCore) (hA : AbsFrob) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_absFrob hG hS hRed hE hA)

/-- **Main result, finest form: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendGen` and
`AbsFrob` (proved).** -/
theorem algFrobRed_of_gen (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_absFrob hG hS hRed (fExtendCore_of_gen hE) hA

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendGen`, `AbsFrob` (proved).** -/
theorem tateBridge35_of_gen (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendGen) (hA : AbsFrob) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_gen hG hS hRed hE hA)

end AlgFrobRedRed

end


/-!
# afr-absfrob: the absolute Frobenius of a scheme of characteristic `p`

Construction (not in Mathlib 4.35): for a scheme `X` with `(p : Γ(X, ⊤)) = 0`, `fr p X` is the
identity on the underlying space and `s ↦ s ^ p` on every ring of sections.
-/

noncomputable section

namespace AbsFrobDef

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable (p : ℕ) [hp : Fact p.Prime]

/-- `x ↦ x ^ p` as a ring endomorphism of a commutative ring in which `p = 0` (the ring may be
trivial, so no `CharP` instance is assumed). -/
def powHom (R : Type*) [CommRing R] (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow _
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.out.ne_zero
  map_add' x y := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    · have := (CharP.charP_iff_prime_eq_zero hp.out).2 h
      exact add_pow_char x y p

@[simp] theorem powHom_apply (R : Type*) [CommRing R] (h : (p : R) = 0) (x : R) :
    powHom p R h x = x ^ p := rfl

omit hp in
/-- `p = 0` in every ring of sections of `X` if it is `0` in the global sections. -/
theorem natCast_sections {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (p : Γ(X, U)) = 0 := by
  have := congrArg (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom hX
  rwa [map_natCast, map_zero] at this

/-- The Frobenius on the structure presheaf. -/
def frobC (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat (𝟙 (X : TopCat))).obj X.presheaf where
  app U := CommRingCat.ofHom (powHom p _ (natCast_sections p hX U.unop))
  naturality U V i := by
    ext x
    exact (map_pow (X.presheaf.map i).hom x p).symm

/-- The absolute Frobenius as a morphism of presheafed spaces. -/
def frobPSh (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 _
  c := frobC p X hX

/-- The stalk map of the absolute Frobenius is `a ↦ a ^ p`. -/
theorem frob_stalkMap (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (x : X)
    (a : X.presheaf.stalk x) :
    ((frobPSh p X hX).stalkMap x).hom a = a ^ p := by
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have := PresheafedSpace.stalkMap_germ_apply (frobPSh p X hX) U x hxU s
  erw [this]
  show X.presheaf.germ U x hxU (s ^ p) = _
  rw [map_pow]

/-- **The absolute Frobenius** `Fr_X : X ⟶ X` of a scheme with `p = 0` on `X`: the identity on
the underlying space, `s ↦ s ^ p` on sections (local on stalks since `a ^ p` a unit forces `a` a
unit). -/
def fr (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) : X ⟶ X :=
  Scheme.Hom.mk
    { toHom := frobPSh p X hX
      prop := fun x => ⟨fun a ha => by
        rw [frob_stalkMap p X hX x a] at ha
        exact (isUnit_pow_iff hp.out.ne_zero).mp ha⟩ }

@[simp] theorem fr_base (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    (fr p X hX).base = 𝟙 _ := rfl

theorem fr_app (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (fr p X hX).app U = CommRingCat.ofHom (powHom p _ (natCast_sections p hX U)) := rfl

/-- **Naturality of the absolute Frobenius:** `f ≫ Fr_X = Fr_Y ≫ f` for every morphism
`f : Y ⟶ X` of schemes on which `p = 0`. -/
theorem fr_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) : f ≫ fr p X hX = fr p Y hY ≫ f := by
  have hb : (f ≫ fr p X hX).base = (fr p Y hY ≫ f).base := by
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, fr_base, fr_base, Category.comp_id,
      Category.id_comp]
  refine Scheme.Hom.ext hb fun U => ?_
  rw [show (eqToHom (congr((Opens.map $hb.symm).obj U))).op =
      𝟙 (op ((Opens.map (f ≫ fr p X hX).base).obj U)) from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app, fr_app, fr_app]
  ext s
  exact map_pow (f.app U).hom s p

omit hp in
theorem natCast_Spec (R : CommRingCat.{u}) (h : (p : R) = 0) : (p : Γ(Spec R, ⊤)) = 0 := by
  have := congrArg (Scheme.ΓSpecIso R).inv.hom h
  rwa [map_natCast, map_zero] at this

omit hp in
theorem natCast_of_hom {R : CommRingCat.{u}} (h : (p : R) = 0) {X : Scheme.{u}}
    (f : X ⟶ Spec R) : (p : Γ(X, ⊤)) = 0 := by
  have := congrArg f.appTop.hom (natCast_Spec p R h)
  rwa [map_natCast, map_zero] at this

/-- **The absolute Frobenius of an affine scheme** is `Spec` of `r ↦ r ^ p`. -/
theorem fr_Spec (R : CommRingCat.{u}) (h : (p : R) = 0) :
    fr p (Spec R) (natCast_Spec p R h) = Spec.map (CommRingCat.ofHom (powHom p R h)) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso R).hom, Scheme.ΓSpecIso_naturality]
  ext s
  exact map_pow (Scheme.ΓSpecIso R).hom.hom s p

end AbsFrobDef

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry


/-- `frobenius R p` is `AbsFrobDef.powHom`. -/
theorem frobenius_eq_powHom (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    frobenius R p = AbsFrobDef.powHom p R (CharP.cast_eq_zero R p) :=
  RingHom.ext fun _ => rfl

/-- **`AbsFrob` (proved):** `Fr_X = AbsFrobDef.fr`. -/
theorem absFrob : AbsFrob := by
  intro k _ p _ _ X
  have hk : ((p : ℕ) : CommRingCat.of k) = 0 := CharP.cast_eq_zero k p
  have hX := AbsFrobDef.natCast_of_hom p hk X.hom
  refine ⟨AbsFrobDef.fr p X.left hX, ?_, fun R _ _ g => ?_⟩
  · rw [frobenius_eq_powHom, ← AbsFrobDef.fr_Spec p (.of k) hk,
      AbsFrobDef.fr_naturality p X.hom]
  · have hR : ((p : ℕ) : CommRingCat.of R) = 0 := CharP.cast_eq_zero R p
    rw [frobenius_eq_powHom, ← AbsFrobDef.fr_Spec p (.of R) hR, AbsFrobDef.fr_naturality p g]

end AlgFrobRedRed


/-! # afr-absfrob, part 2: `FExtendGen` from the Néron mapping property (leaf I2-NMP)

Appended by `build.sh` after alg-frob-red's `AlgFrobRed.lean` (verbatim copy) and the
absolute-Frobenius part. -/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry Limits
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-- **Galois rigidity of embeddings (proved).** For a normal extension `L/ℚ`, a domain `R` and two
ring maps `ψ₁, ψ₂ : L → R` which agree after some ring map `χ : R → Q` to a nontrivial ring,
`ψ₁ = ψ₂`. (`ψ₂ ℓ` is a root of the minimal polynomial of `ℓ`, which splits in `L`; so
`ψ₂ ℓ = ψ₁ r` for a conjugate `r`, and `χ ∘ ψ₁` is injective.) -/
theorem ringHom_eq_of_normal {L R Q : Type*} [Field L] [Algebra ℚ L] [Normal ℚ L]
    [CommRing R] [IsDomain R] [CommRing Q] [Nontrivial Q]
    (ψ₁ ψ₂ : L →+* R) (χ : R →+* Q) (h : χ.comp ψ₁ = χ.comp ψ₂) : ψ₁ = ψ₂ := by
  ext ℓ
  have hint : IsIntegral ℚ ℓ := Normal.isIntegral inferInstance ℓ
  have hsp := Normal.splits (inferInstance : Normal ℚ L) ℓ
  have hc : ψ₁.comp (algebraMap ℚ L) = ψ₂.comp (algebraMap ℚ L) := RingHom.ext_rat _ _
  have hne : ((minpoly ℚ ℓ).map (algebraMap ℚ L)).map ψ₁ ≠ 0 :=
    Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hint))
  have hroot : ψ₂ ℓ ∈ (((minpoly ℚ ℓ).map (algebraMap ℚ L)).map ψ₁).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.map_map, hc,
      ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  rw [hsp.roots_map ψ₁, Multiset.mem_map] at hroot
  obtain ⟨r, -, hr⟩ := hroot
  have hrl : r = ℓ := (χ.comp ψ₁).injective (by
    show χ (ψ₁ r) = χ (ψ₁ ℓ)
    rw [hr]
    exact (RingHom.congr_fun h ℓ).symm)
  rw [← hr, hrl]

/-- **Morphisms from an integral scheme to `Spec L`, `L/ℚ` normal, agreeing at one field-valued
point, are equal (proved).** Via `Γ(X, ⊤)` (a domain) and `ringHom_eq_of_normal`. -/
theorem hom_spec_eq_of_point {L : Type} [Field L] [Algebra ℚ L] [Normal ℚ L] {X : Scheme.{0}}
    [IsIntegral X] {K : Type} [Field K] (g₁ g₂ : X ⟶ Spec (.of L)) (x : Spec (.of K) ⟶ X)
    (h : x ≫ g₁ = x ≫ g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  have key := ringHom_eq_of_normal ((Scheme.ΓSpecIso (.of L)).inv ≫ g₁.appTop).hom
    ((Scheme.ΓSpecIso (.of L)).inv ≫ g₂.appTop).hom (x.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
    (by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
      congr 1
      simp only [Category.assoc]
      rw [reassoc_of% h'])
  rw [← cancel_epi (Scheme.ΓSpecIso (.of L)).inv]
  exact CommRingCat.hom_ext key

/-- `Spec` of an injective ring map is dominant (proved; the kernel is `0 ≤ nilradical`). -/
theorem isDominant_Spec_map_of_injective {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (h : Function.Injective φ.hom) : IsDominant (Spec.map φ) := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap φ.hom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [h (hx.trans (map_zero _).symm)]
  exact zero_mem _

/-- Cancelling `Spec(s)` for an automorphism `s` of `ℚ̄` (proved). -/
theorem spec_aut_cancel (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {X : Scheme.{0}}
    {a b : Spec (.of (AlgebraicClosure ℚ)) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ a =
      Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ b) :
    a = b := by
  have hi : Spec.map (CommRingCat.ofHom (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
      Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
          (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) = RingHom.id _ from
        RingHom.ext fun x => s.symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  calc a = (Spec.map (CommRingCat.ofHom (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) ≫ a := by
          rw [hi, Category.id_comp]
    _ = b := by rw [Category.assoc, h, ← Category.assoc, hi, Category.id_comp]

set_option synthInstance.maxHeartbeats 400000 in
/-- The unit section of a base change `(Over.pullback g').mapGrp.obj 𝒜`, followed by the first
projection, is `g'` followed by the unit section of `𝒜` (proved; `sf_eta_fst` for any `g'`). -/
theorem pb_eta_fst {S S' : Scheme.{0}} (g' : S' ⟶ S) (𝒜 : Grp (Over S)) :
    (η[((Over.pullback g').mapGrp.obj 𝒜).X]).left ≫ pullback.fst 𝒜.X.hom g' =
      g' ≫ (η[𝒜.X]).left := by
  let F := Over.pullback g'
  have hε : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙 S) g' = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε F)
  have hε2 : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 S) g' = g' := by
    have hc : pullback.fst (𝟙 S) g' = pullback.snd (𝟙 S) g' ≫ g' := by
      rw [← pullback.condition, Category.comp_id]
    rw [hc, ← Category.assoc, hε, Category.id_comp]
  have hmap : (F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' =
      pullback.fst (𝟙 S) g' ≫ (η[𝒜.X]).left := pullback.lift_fst _ _ _
  show ((Functor.LaxMonoidal.ε F) ≫ F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε2]

/-- `Spec(O_w → L)`. -/
abbrev jSpec (L : IF) (v : ValuationSubring PkgI4.Qbar) :
    Spec (.of L) ⟶ Spec (.of (Ow L v)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))

/-- `Spec(t)`, `t = σ⁻¹|_{O_w}`. -/
abbrev tSpec {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ)
    (hσ : σ ∈ v.decompositionSubgroup ℚ) : Spec (.of (Ow L v)) ⟶ Spec (.of (Ow L v)) :=
  Spec.map (CommRingCat.ofHom (tSig σ hσ))

/-- `τ = σ⁻¹|_L`. -/
abbrev tauL (L : IF) [IsGalois ℚ L] (σ : PkgI4.GQ) : L →+* L :=
  (((σ⁻¹).restrictNormal L : L ≃ₐ[ℚ] L) : L →+* L)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **`FExtendGen` from the leaf I2-NMP (proved).**
1. `F` lies over `Spec τ`, `τ = σ⁻¹|_L`: both `F ≫ A → Spec L` and `A → Spec L → Spec L` agree at
   the `ℚ̄`-point `0` (from `f 0 = 0`), and `A` is integral (`hom_spec_eq_of_point`).
2. `ℬ = 𝒜 ×_{Spec t} Spec O_w` (the conjugate model) is an abelian scheme (base change).
3. `φ = (e ≫ F ≫ e⁻¹ ≫ pr₁, pr₂) : 𝒜_L → ℬ_L` is an `L`-morphism; I2-NMP gives `G : 𝒜 → ℬ`
   over `O_w` with `G_L = φ`; `F̃ = G ≫ pr₁` lies over `Spec t` and restricts to `F`.
4. `F̃` fixes the unit section: both sides agree on `Spec L` (because `F(0) = 0` twisted, by
   separatedness of `A` and dominance of `Spec ℚ̄ → Spec L`), hence on `Spec O_w`
   (separatedness of `𝒜`, dominance of `Spec L → Spec O_w`). -/
theorem fExtendGen_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendGen := by
  intro L _ _ A F _ _ p hp v σ hv hσ 𝒜 h𝒜 e f hf
  generalize hσ.1 = hσ1
  haveI : IsDiscreteValuationRing (Ow L v) := owDVR L v p hp hv
  haveI : IsProper 𝒜.X.hom := h𝒜.proper
  haveI : Smooth 𝒜.X.hom := h𝒜.smooth
  haveI : GeometricallyConnected 𝒜.X.hom := h𝒜.geomConnected
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  -- ring identities
  have hR1 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ Spec.map (CommRingCat.ofHom (tauL L σ)) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L a)) = algebraMap L PkgI4.Qbar a
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hR2 : jSpec L v ≫ tSpec σ hσ1 = Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ jSpec L v := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  -- the zero point
  let x0 : Spec (.of Qbar) ⟶ A.X.left := (Additive.toMul (0 : PtQ L A)).left
  have hu : (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)).left =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    (Category.comp_id _).symm.trans
      (Over.w (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)))
  have hx0 : x0 = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ (η[A.X]).left := by
    show (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)).left ≫
      (η[A.X]).left = _
    rw [hu]
    rfl
  have hx0w : x0 ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    Over.w (Additive.toMul (0 : PtQ L A))
  have hηw : (η[A.X]).left ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
  have hf0 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      x0 ≫ F = x0 := by
    have := hf 0
    rw [map_zero] at this
    exact this.symm
  have hpt : x0 ≫ F = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫
      Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ (η[A.X]).left := by
    apply spec_aut_cancel (act σ)
    rw [hf0, reassoc_of% hR1]
    exact hx0
  -- Step 1: `F` lies over `Spec τ`
  have hFover : F ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (tauL L σ)) := by
    apply hom_spec_eq_of_point _ _ x0
    rw [reassoc_of% hpt, hηw, reassoc_of% hx0w]
    erw [Category.comp_id]
  -- `F(0) = 0`, twisted
  have hF0 : (η[A.X]).left ≫ F = Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ (η[A.X]).left := by
    haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap L Qbar))
      (algebraMap L Qbar).injective
    refine ext_of_isDominant_of_isSeparated (X := Spec (.of L)) A.X.hom ?_
      (Spec.map (CommRingCat.ofHom (algebraMap L Qbar))) ?_
    · simp only [Category.assoc]
      rw [hFover, reassoc_of% hηw, hηw]
      erw [Category.comp_id]
    · calc _ = x0 ≫ F := by rw [hx0, Category.assoc]
        _ = _ := hpt
  -- Step 2: the conjugate model
  let ℬ := (Over.pullback (tSpec σ hσ1)).mapGrp.obj 𝒜
  haveI hℬ : PkgI2.IsAbelianScheme ℬ :=
    ⟨show IsProper (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance,
      show Smooth (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance,
      show GeometricallyConnected (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance⟩
  -- Step 3: the generic morphism and I2-NMP
  let E : pullback 𝒜.X.hom (jSpec L v) ⟶ A.X.left := e.hom.hom.hom.left
  let Ei : A.X.left ⟶ pullback 𝒜.X.hom (jSpec L v) := e.inv.hom.hom.left
  have hEi : Ei ≫ E = 𝟙 _ := congrArg (fun m => m.hom.hom.left) e.inv_hom_id
  have hEw : E ≫ A.X.hom = pullback.snd 𝒜.X.hom (jSpec L v) := Over.w e.hom.hom.hom
  have hEiw : Ei ≫ pullback.snd 𝒜.X.hom (jSpec L v) = A.X.hom := Over.w e.inv.hom.hom
  have c1 : (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v)) ≫ 𝒜.X.hom =
      (pullback.snd 𝒜.X.hom (jSpec L v) ≫ jSpec L v) ≫ tSpec σ hσ1 := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% hEiw, reassoc_of% hFover, reassoc_of% hEw, hR2]
  let inner : pullback 𝒜.X.hom (jSpec L v) ⟶ pullback 𝒜.X.hom (tSpec σ hσ1) :=
    pullback.lift (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v))
      (pullback.snd 𝒜.X.hom (jSpec L v) ≫ jSpec L v) c1
  let φl : pullback 𝒜.X.hom (jSpec L v) ⟶
      pullback (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) :=
    pullback.lift inner (pullback.snd 𝒜.X.hom (jSpec L v)) (pullback.lift_snd _ _ _)
  let φ : (Over.pullback (jSpec L v)).obj 𝒜.X ⟶ (Over.pullback (jSpec L v)).obj ℬ.X :=
    Over.homMk φl (pullback.lift_snd _ _ _)
  obtain ⟨G, hG⟩ := (hN L (Ow L v) 𝒜 ℬ).2 φ
  have hG' : (Over.pullback (jSpec L v)).map G = φ := hG
  let Gl : 𝒜.X.left ⟶ pullback 𝒜.X.hom (tSpec σ hσ1) := G.left
  let Ft : 𝒜.X.left ⟶ 𝒜.X.left := Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1)
  have hGl : pullback.fst 𝒜.X.hom (jSpec L v) ≫ Gl =
      φl ≫ pullback.fst (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) := by
    have h1 : ((Over.pullback (jSpec L v)).map G).left ≫
        pullback.fst (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) =
        pullback.fst 𝒜.X.hom (jSpec L v) ≫ G.left := pullback.lift_fst _ _ _
    have h2 : ((Over.pullback (jSpec L v)).map G).left = φl := congrArg (fun m => m.left) hG'
    rw [← h2]
    exact h1.symm
  have hfst : pullback.fst 𝒜.X.hom (jSpec L v) ≫ Ft =
      E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    show pullback.fst 𝒜.X.hom (jSpec L v) ≫ Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1) = _
    rw [← Category.assoc (pullback.fst 𝒜.X.hom (jSpec L v)), hGl, Category.assoc φl]
    simp only [φl, inner, pullback.lift_fst_assoc, pullback.lift_fst]
  have hC3 : Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) ≫ Ft =
      F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    rw [hfst, ← Category.assoc Ei E, hEi, Category.id_comp]
  have hGw : Gl ≫ pullback.snd 𝒜.X.hom (tSpec σ hσ1) = 𝒜.X.hom := Over.w G
  have hC1 : Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ tSpec σ hσ1 := by
    show (Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1)) ≫ 𝒜.X.hom = _
    rw [Category.assoc, pullback.condition, reassoc_of% hGw]
  refine ⟨Ft, hC1, ?_, hC3⟩
  -- Step 4: the unit section
  have hηO : (η[𝒜.X]).left ≫ 𝒜.X.hom = 𝟙 _ := Over.w η[𝒜.X]
  have hηL : jSpec L v ≫ (η[𝒜.X]).left =
      (η[A.X]).left ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    rw [← pb_eta_fst (jSpec L v) 𝒜, ← Category.assoc]
    congr 1
    have h1 : η[A.X] ≫ e.inv.hom.hom = η[((Over.pullback (jSpec L v)).mapGrp.obj 𝒜).X] :=
      IsMonHom.one_hom _
    exact (congrArg (fun m => m.left) h1).symm
  haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap (Ow L v) L))
    (Subtype.val_injective)
  refine ext_of_isDominant_of_isSeparated (X := Spec (.of (Ow L v))) 𝒜.X.hom ?_ (jSpec L v) ?_
  · simp only [Category.assoc]
    rw [hC1, reassoc_of% hηO, hηO]
    erw [Category.comp_id]
  · rw [reassoc_of% hηL, hC3, reassoc_of% hF0, reassoc_of% hR2, hηL]

/-- **`FExtendCore` from I2-NMP (proved).** -/
theorem fExtendCore_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendCore :=
  fExtendCore_of_gen (fExtendGen_of_nmp hN)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the kernel leaves I2-Red, I2-NMP (proved).** alg-frob-red's two glue
Props are discharged: `AbsFrob` (`absFrob`, Mathlib only) and `FExtendGen` (`fExtendGen_of_nmp`). -/
theorem algFrobRed_of_nmp (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen hG hS hRed (fExtendGen_of_nmp hN) absFrob

/-- **`TateBridge35` from I3.M0, the two leaf candidates and I2-Red, I2-NMP (proved).** -/
theorem tateBridge35_of_nmp (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) : G14Bridge.TateBridge35 :=
  tateBridge35_of_gen hT hG hS hRed (fExtendGen_of_nmp hN) absFrob

end AlgFrobRedRed


/-! # frob-pieces: `GoodRedCofinite` from spreading out (task frob-pieces)

Appended (by `scratch/frob-pieces/build.sh`) to a verbatim copy of
`scratch/alg-frob-red/AlgFrobRed.lean`. -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

set_option synthInstance.maxHeartbeats 400000 in
/-- **`AbSchemeSpreadsOut` (LEAF candidate, published: spreading out an abelian variety to an
abelian scheme).** An abelian variety `A` over a number field `L ⊆ ℚ̄` extends to an abelian
scheme (I2's `IsAbelianScheme`: a group object, proper, smooth, geometrically connected) over a
finitely generated subring `R = ℤ[s] ⊆ L`, with generic fibre isomorphic to `A` as a group object.
Source: `L = colim R` over finitely generated subrings; the scheme, group law and axioms descend to
some `R` (EGA IV₃ 8.8.2), as do properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8);
geometric connectedness of the fibres holds after shrinking `R` to a normal ring with fraction
field `L`, e.g. `𝓞_L[1/N]` (finitely generated: an integral basis and `1/N`), by Zariski's
connectedness theorem (EGA III₁ 4.3; this is `FrobPiecesNeron.ProperSmoothGenConnected`), or
over a nonempty open of `Spec R` (EGA IV₃ 9.7.7, with a generic-point argument). Locators UNVERIFIED. Same input as
neron-lg's glue N1-g1 `AbVarSpreadsOut`, plus geometric connectedness of the fibres. -/
def AbSchemeSpreadsOut : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ (s : Finset L) (𝒜 : Grp (Over (Spec (.of (Subring.closure (s : Set L)))))),
      PkgI2.IsAbelianScheme 𝒜 ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (Subring.closure (s : Set L)) L)))).mapGrp.obj 𝒜 ≅ ObjBridge.toGrp A)

/-- A nonzero integer prime to `p` is a unit in `O_w` for `w ∣ p`. -/
theorem isUnit_intCast_of_coprime {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hp : p.Prime) (hv : PkgI4.LiesOver v p) {y : ℤ}
    (hpy : ¬ p ∣ y.natAbs) : IsUnit (y : Ow L v) := by
  by_contra hnu
  have hym : (y : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  have hpm := natCast_mem_maximalIdeal (L := L) hp hv
  have hcop : IsCoprime (p : ℤ) y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hp).2 hpy
    simpa [Int.gcd] using this
  obtain ⟨u, w, huw⟩ := hcop
  have h1 : ((u * p + w * y : ℤ) : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hym)
  rw [huw, Int.cast_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

set_option synthInstance.maxHeartbeats 400000 in
/-- Base change of a group object along equal morphisms. -/
theorem pullbackGrp_congr {X Y : Scheme} {f f' : X ⟶ Y} (h : f = f') (𝒜 : Grp (Over Y)) :
    Nonempty ((Over.pullback f).mapGrp.obj 𝒜 ≅ (Over.pullback f').mapGrp.obj 𝒜) := by
  subst h; exact ⟨Iso.refl _⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`GoodRedCofinite` from `AbSchemeSpreadsOut` (proved).** Let `𝒜/ℤ[s]` spread out `A`, and
`y ≠ 0` an integer with `y·a` integral for every `a ∈ s` (`exists_integral_multiples`). For a prime
`p ∤ y` and `w ∣ p`, `y` is a unit and integral elements lie in the valuation ring `O_w`, so
`ℤ[s] ⊆ O_w`; the base change of `𝒜` to `O_w` is an abelian scheme (base-change stability) whose
generic fibre is that of `𝒜` (`Over.pullbackComp`, `Functor.mapGrpNatIso`). -/
theorem goodRedCofinite_of (h : AbSchemeSpreadsOut) : GoodRedCofinite := by
  intro L _ A
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  obtain ⟨s, 𝒜, h𝒜, ⟨e⟩⟩ := h L A
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs.primeFactors, fun p hp hpS v hv => ?_⟩
  have hpy : ¬ p ∣ y.natAbs := fun hd =>
    hpS (Nat.mem_primeFactors.2 ⟨hp, hd, Int.natAbs_ne_zero.2 hy0⟩)
  obtain ⟨u, hu⟩ := isUnit_intCast_of_coprime (L := L) hp hv hpy
  have hinv : (y : L)⁻¹ ∈ Ow L v := by
    have h2 : ((u⁻¹ : (Ow L v)ˣ) : Ow L v) * (y : Ow L v) = 1 := by rw [← hu]; exact u.inv_mul
    have h3 : (((u⁻¹ : (Ow L v)ˣ) : Ow L v) : L) * (y : L) = 1 := by
      have := congrArg (fun z : Ow L v => (z : L)) h2
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left h3]
    exact ((u⁻¹ : (Ow L v)ˣ) : Ow L v).2
  have hmem : ∀ a ∈ s, a ∈ Ow L v := by
    intro a ha
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (show IsIntegral (Ow L v) (y • a) from (hyint a ha).tower_top)
    have hyL : (y : L) ≠ 0 := by exact_mod_cast hy0
    have ha' : a = (y : L)⁻¹ * (y • a) := by
      rw [zsmul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ hyL, _root_.one_mul]
    rw [ha', ← hb]
    exact mul_mem hinv b.2
  have hle : Subring.closure (s : Set L) ≤ (Ow L v).toSubring :=
    Subring.closure_le.2 (fun a ha => hmem a ha)
  let φ : Subring.closure (s : Set L) →+* Ow L v := Subring.inclusion hle
  let g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨(Over.pullback g).mapGrp.obj 𝒜, ?_, ?_⟩
  · have := h𝒜.proper; have := h𝒜.smooth; have := h𝒜.geomConnected
    refine ⟨?_, ?_, ?_⟩
    · show IsProper (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show Smooth (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show GeometricallyConnected (Limits.pullback.snd 𝒜.X.hom g); infer_instance
  · have hcomp : Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap (Subring.closure (s : Set L)) L)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    refine ⟨(Functor.mapGrpCompIso.app 𝒜).symm ≪≫
      (Functor.mapGrpNatIso (Over.pullbackComp _ _).symm).app 𝒜 ≪≫ ?_⟩
    exact (pullbackGrp_congr hcomp 𝒜).some ≪≫ e

end FrobPiecesGood

end

/-! # frob-pieces: `GoodRedCofinite` from neron-lg's glue N1-g1 `AbVarSpreadsOut` and Zariski's
connectedness theorem (task frob-pieces)

`HasAbelianSchemeAway` and `AbVarSpreadsOut` below are verbatim copies (docstring and `def`) of
the declarations of the same names in `scratch/neron-lg/NeronLG.lean` (namespace
`ZInQ.NeronLG`), under the same `open`s (checked by `scratch/frob-pieces/py/verbatim_check.py`). -/

noncomputable section

namespace FrobPiecesNeron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI3 (AbVar)
open scoped Obj

/-- `B` extends to an abelian scheme over `𝓞_L[1/f]`: a smooth proper group scheme whose generic
fibre is identified with `B` as a group scheme (over every presentation of `𝓞_L[1/f]`). -/
def HasAbelianSchemeAway (L : Type) [Field L] [NumberField L] (B : AbVar L) (f : 𝓞 L) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L],
    ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
      letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
        Functor.grpObjObj
      IsMonHom gen.hom

/-- **Glue N1-g1 (spreading out an abelian variety).** An abelian variety `B` over a number field
`L` extends to an abelian scheme over `𝓞_L[1/f]` for some nonzero `f ∈ 𝓞_L`. Textbook (a
candidate for a textbook leaf): `L = colim 𝓞_L[1/f]`, so `B`, its group law, unit and inverse
and the group axioms (equalities of morphisms) descend to some `𝓞_L[1/f]` (EGA IV₃ 8.8.2), as do
properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8 (ii)); all locators UNVERIFIED.
Mathlib v4.35 has the descent of morphisms for affine transition maps
(`AlgebraicGeometry/.../AffineTransitionLimit.lean`, EGA IV 8.8.2) but not the descent of schemes
or of properness and smoothness. -/
def AbVarSpreadsOut : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L), ∃ f : 𝓞 L, f ≠ 0 ∧ HasAbelianSchemeAway L B f

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ProperSmoothGenConnected` (LEAF candidate, published: Zariski's connectedness theorem).**
A smooth proper scheme `X` over `R = 𝓞_L[1/f]` (any presentation) whose generic fibre is
geometrically connected is geometrically connected over `R`. Proof (STANDARD): `R ≅ 𝓞_L[1/f]`
is normal with fraction field `L` (the case `f = 0` is vacuous: no ring map from the zero ring to
`L`), and `X_L` is geometrically reduced (smooth) and geometrically connected and proper, so
`H⁰(X_L, 𝒪) = L`; `f_*𝒪_X` is a finite `R`-algebra, torsion-free since `X` is flat (smooth), so
it lies inside `H⁰(X_L, 𝒪) = L` and is integral over the normal `R`, hence
`f_*𝒪_X = 𝒪_{Spec R}`; then all fibres of the proper `f` are geometrically connected (Zariski's
connectedness theorem, EGA III₁ 4.3.1–4.3.4; locators UNVERIFIED). The fibres are nonempty since
`X → Spec R` is open (smooth), closed (proper), `X ≠ ∅` and `Spec R` is connected. Not in Mathlib
v4.35 (no Stein factorization). -/
def ProperSmoothGenConnected : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (f : 𝓞 L) (R : Type) [CommRing R] [Algebra (𝓞 L) R]
    [IsLocalization.Away f R] [Algebra R L] [IsScalarTower (𝓞 L) R L]
    (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProper X.hom →
    GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj X).hom →
    GeometricallyConnected X.hom

/-- Geometrically integral implies geometrically connected. -/
theorem geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{0}} (g : X ⟶ Y)
    [GeometricallyIntegral g] : GeometricallyConnected g := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  infer_instance

/-- `A` has good reduction at `O` if an abelian scheme over a ring `R` mapping to `O` (compatibly
with the maps to `K`) has generic fibre `≅ A`: base change along `Spec O → Spec R`. -/
theorem hasGoodReduction_of_base {K : Type} [Field K] (O : ValuationSubring K) {R : Type}
    [CommRing R] (ιR : R →+* K) (φ : R →+* O) (hφ : (algebraMap O K).comp φ = ιR)
    (A : Grp (Over (Spec (.of K)))) (𝒜 : Grp (Over (Spec (.of R))))
    (h𝒜 : PkgI2.IsAbelianScheme 𝒜)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom ιR))).mapGrp.obj 𝒜 ≅ A) :
    PkgI2.HasGoodReduction A O := by
  let g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨(Over.pullback g).mapGrp.obj 𝒜, ?_, ?_⟩
  · have := h𝒜.proper; have := h𝒜.smooth; have := h𝒜.geomConnected
    refine ⟨?_, ?_, ?_⟩
    · show IsProper (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show Smooth (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show GeometricallyConnected (Limits.pullback.snd 𝒜.X.hom g); infer_instance
  · have hcomp : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ g =
        Spec.map (CommRingCat.ofHom ιR) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hφ]
    exact ⟨(Functor.mapGrpCompIso.app 𝒜).symm ≪≫
      (Functor.mapGrpNatIso (Over.pullbackComp _ _).symm).app 𝒜 ≪≫
      (FrobPiecesGood.pullbackGrp_congr hcomp 𝒜).some ≪≫ e⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`GoodRedCofinite` from neron-lg's N1-g1 `AbVarSpreadsOut` and `ProperSmoothGenConnected`
(proved).** Spread `A` out to `G/𝓞_L[1/f]` (presentation `Localization.Away f`); `G` is
geometrically connected by `ProperSmoothGenConnected` (its generic fibre is `≅ A`, geometrically
integral). `S` is the set of prime factors of `N = |N_{L/ℚ}(f)|`: for `p ∉ S` and `w ∣ p`, `N` is a
unit of `O_w` and `N ∈ (f)`, so `f` is a unit of `O_w`, and `𝓞_L[1/f] → L` factors through `O_w`
(`IsLocalization.Away.lift`); conclude by base change (`hasGoodReduction_of_base`). -/
theorem goodRedCofinite_of_neron (hsp : AbVarSpreadsOut) (hc : ProperSmoothGenConnected) :
    AlgFrobRedRed.GoodRedCofinite := by
  intro L _ A
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  obtain ⟨f, hf0, hf⟩ := hsp L A
  have hfL : IsUnit (algebraMap (𝓞 L) L f) :=
    isUnit_iff_ne_zero.2 (by simpa using hf0)
  let R := Localization.Away f
  letI : Algebra R L := (IsLocalization.Away.lift f hfL).toAlgebra
  haveI : IsScalarTower (𝓞 L) R L := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.Away.lift_eq f hfL x).symm)
  obtain ⟨G, hG, hGs, hGp, gen, hgen⟩ := hf R
  have hgc : GeometricallyConnected G.hom := by
    refine hc L f R G hGs hGp ?_
    have h1 : GeometricallyConnected A.X.hom := geometricallyConnected_of_geometricallyIntegral _
    have h2 : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G).hom =
        gen.hom.left ≫ A.X.hom := (Over.w gen.hom).symm
    rw [h2]
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0})
      gen.hom.left A.X.hom).2 h1
  let N : ℕ := Ideal.absNorm (Ideal.span {f})
  have hN0 : N ≠ 0 := by
    simp only [N, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hf0
  refine ⟨N.primeFactors, fun p hp hpS v hv => ?_⟩
  have hpN : ¬ p ∣ (N : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    exact fun hd => hpS (Nat.mem_primeFactors.2 ⟨hp, hd, hN0⟩)
  have hNu : IsUnit ((N : ℤ) : AlgFrobRedRed.Ow L v) :=
    FrobPiecesGood.isUnit_intCast_of_coprime (L := L) hp hv hpN
  have hfu : IsUnit (AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v) f) := by
    by_contra hnu
    have hfm : AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v) f ∈
        IsLocalRing.maximalIdeal (AlgFrobRedRed.Ow L v) := (IsLocalRing.mem_maximalIdeal _).2 hnu
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {f}))
    have : ((N : ℤ) : AlgFrobRedRed.Ow L v) ∈ IsLocalRing.maximalIdeal (AlgFrobRedRed.Ow L v) := by
      have := congrArg (AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v)) hc'
      rw [map_mul, map_natCast] at this
      rw [Int.cast_natCast, ← this]
      exact Ideal.mul_mem_left _ _ hfm
    exact (IsLocalRing.mem_maximalIdeal _).1 this hNu
  let φ : R →+* AlgFrobRedRed.Ow L v := IsLocalization.Away.lift f hfu
  have hφ : (algebraMap (AlgFrobRedRed.Ow L v) L).comp φ = algebraMap R L := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, φ, IsLocalization.Away.lift_eq]
    exact (IsLocalization.Away.lift_eq f hfL x).symm
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
    Functor.grpObjObj
  exact hasGoodReduction_of_base _ (algebraMap R L) φ hφ _ (Grp.mk G) ⟨hGp, hGs, hgc⟩
    (Grp.mkIso' gen)

end FrobPiecesNeron

end

/-! # frob-pieces: `AlgFrobRed` with `SmoothGeomConnIntegral` discharged and `GoodRedCofinite`
replaced by `AbSchemeSpreadsOut` -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **alg-frob-red's `SmoothGeomConnIntegral`, proved** (it is definitionally the verbatim copy
`FrobPieces.SmoothGeomConnIntegral` of `ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean`,
proved there from the vendored Tau Ceti theorem `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`). -/
theorem smoothGeomConnIntegral : AlgFrobRedRed.SmoothGeomConnIntegral :=
  FrobPieces.smoothGeomConnIntegral

/-- **`AlgFrobRed` from `AbSchemeSpreadsOut`, I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_spread (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen (goodRedCofinite_of hG) smoothGeomConnIntegral hRed hE hA

/-- **`AlgFrobRed` from `GoodRedCofinite`, I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_four (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen hG smoothGeomConnIntegral hRed hE hA

/-- **`TateBridge35` from I3.M0, `AbSchemeSpreadsOut`, I2-Red, `FExtendGen`, `AbsFrob`
(proved).** -/
theorem tateBridge35_of_spread (hT : PkgI3.TateModuleFree) (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_spread hG hRed hE hA)

/-- **`AlgFrobRed` from neron-lg's glue N1-g1 `AbVarSpreadsOut`, `ProperSmoothGenConnected`,
I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_neron (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen (FrobPiecesNeron.goodRedCofinite_of_neron hsp hc) smoothGeomConnIntegral hRed
    hE hA

/-- **`TateBridge35` from I3.M0, N1-g1, `ProperSmoothGenConnected`, I2-Red, `FExtendGen`,
`AbsFrob` (proved).** -/
theorem tateBridge35_of_neron (hT : PkgI3.TateModuleFree) (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_neron hsp hc hRed hE hA)

end FrobPiecesGood

end


/-! # frob-pieces: the combined form with afr-absfrob's `AbsFrob` and `FExtendGen`

Appended by `build_full.sh` after afr-absfrob's assembled `AfrAbsFrob.lean` (verbatim copy, which
begins with alg-frob-red's `AlgFrobRed.lean`) and this task's parts. -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **`FrobTrace.AlgFrobRed` from neron-lg's glue N1-g1 `AbVarSpreadsOut`, the leaf candidate
`ProperSmoothGenConnected` and the kernel leaves I2-Red, I2-NMP (proved).** -/
theorem algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp (FrobPiecesNeron.goodRedCofinite_of_neron hsp hc) smoothGeomConnIntegral
    hRed hN

/-- **`FrobTrace.AlgFrobRed` from `AbSchemeSpreadsOut` and the kernel leaves I2-Red, I2-NMP
(proved).** -/
theorem algFrobRed_of_spread_nmp (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp (goodRedCofinite_of hG) smoothGeomConnIntegral hRed hN

/-- **`FrobTrace.AlgFrobRed` from `GoodRedCofinite` and the kernel leaves I2-Red, I2-NMP
(proved).** -/
theorem algFrobRed_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp hG smoothGeomConnIntegral hRed hN

/-- **`G14Bridge.TateBridge35` from I3.M0, N1-g1, `ProperSmoothGenConnected`, I2-Red, I2-NMP
(proved).** -/
theorem tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_neron_nmp hsp hc hRed hN)

/-- **`G14Bridge.TateBridge35` from I3.M0, `AbSchemeSpreadsOut`, I2-Red, I2-NMP (proved).** -/
theorem tateBridge35_of_spread_nmp (hT : PkgI3.TateModuleFree) (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_spread_nmp hG hRed hN)

end FrobPiecesGood

end



import ZInQKernel.OneProof.H.TailH
import ZInQKernel.Contrib.OneProof.SZRaynaud

/-!
# d2a6-reroute (`Contrib/OneProof/D2WildNF.lean`): D2 on the manuscript's route (diophantine_zq.tex L814-818)

The kernel's D2 ("wild inertia of `F = L_v(A[3])` fixes `A[ℓⁿ]`") went through TailH's `raynaudPlace_of_R6`
(r6 = `PkgI2.RaynaudCriterionNF`: `(σ - 1)² = 0` on `A[ℓⁿ]` for every inertia `σ`, i.e. SGA 7 IX 3.5's unipotence
through the bundle field `sga7_IX_3_5_ForwardGeom_Def34`) followed by the `p`-power period of wild elements
(`wildIter`) and the algebraic core `fixed_of_unipSq_of_iterate'`. The manuscript says instead: Raynaud's criterion
(Silverberg–Zarhin Thm 3.5) gives semistable reduction over `F`, and wild inertia of `F` acts trivially on `V_ℓ(A)`
(an uncited sentence, ELLIOT). sz-raynaud stated both as leaves and proved `SZRaynaud.RaynaudWildNF` from them. This
file reroutes D2 through `RaynaudWildNF`:

* `isWildInertia_of_wild_gen` (proved): an element over a wild `σ ∈ G_{ℚ_p}` is wild inertia (`IsWildInertia`) at
  the valuation ring `normVS f` (the analogue of TailH's `isInertia_of_wild_gen`);
* `RaynaudPlaceFix A m` (the manuscript's form of TailH's `RaynaudPlace`: a wild `σ'` fixing `A[m]` *fixes*
  `A[ℓⁿ]`), `raynaudPlaceFix_of_wildNF` (proved: TailH's `raynaudPlace_of_R6` with `RaynaudWildNF` in place of r6),
  `raynaudPlace_of_fix` (fixing gives `(σ' - 1)² = 0`, for TailH's consumers stated with `RaynaudPlace`);
* `torsFix_of_wildNF` (proved: TailH's `torsFix_of_descent` with no unipotence and no `wildIter` step) and the
  consumers `torsFixWildOdd_of_wildNF`, `torsFixWildE_of_twist_wildNF`, `tateWildKE_of_wildNF`, `tateWildK_of_wildNF`,
  `localGlue_of_leaves_wildNF`, `localGlue_of_descent_wildNF`: TailH's statements with r6 replaced by
  `RaynaudWildNF`.

No `sorry`, no `axiom`; never imports `ZInQKernel.OneProof.Main`. Report: docs/research/d2a6-reroute.md.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

noncomputable section

namespace G15Ram

open _root_.PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj
open scoped Pointwise

section D2WildSec

variable {p : ℕ} [Fact p.Prime]

/-- **Wild elements are wild inertia (general form, proved).** If `f ∘ τ = σ ∘ f` with `σ` wild
(`‖σ z - z‖ < ‖z‖` for `z ≠ 0`), then `τ` is wild inertia at `normVS f` in sz-raynaud's sense
(`v(τ x - x) < v(x)` for `x ≠ 0`, `SZRaynaud.IsWildInertia`): `a = (τ x - x)/x` has `‖f a‖ < 1`, so it lies in the
maximal ideal of `normVS f`, and `v(τ x - x) = v(a) v(x) < v(x)`. -/
theorem isWildInertia_of_wild_gen {K₀ Ω : Type} [Field K₀] [Field Ω] [Algebra K₀ Ω]
    (f : Ω →+* Kbar p) {σ : GQp p} (hσ : σ ∈ wildSet) (τ : Ω ≃ₐ[K₀] Ω)
    (hf : ∀ y, f (τ y) = σ (f y)) : _root_.SZRaynaud.IsWildInertia (normVS f) τ := by
  intro x hx
  have hfx : f x ≠ 0 := (map_ne_zero f).mpr hx
  have hlt : ‖f (τ x - x)‖ < ‖f x‖ := by
    rw [map_sub, hf]
    exact hσ _ hfx
  have hfxpos : 0 < ‖f x‖ := norm_pos_iff.mpr hfx
  set a : Ω := (τ x - x) / x with ha
  have hfa : ‖f a‖ < 1 := by
    rw [ha, map_div₀, norm_div, div_lt_one hfxpos]
    exact hlt
  have haw : a ∈ normVS f := by
    rw [mem_normVS]
    exact hfa.le
  have hmax : (⟨a, haw⟩ : normVS f) ∈ IsLocalRing.maximalIdeal (normVS f) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
    have hc' : f a * f (c : Ω) = 1 := by
      rw [← map_mul]
      have := congrArg Subtype.val hc
      simp only [OneMemClass.coe_one] at this
      rw [show ((⟨a, haw⟩ * c : normVS f) : Ω) = a * c from rfl] at this
      rw [this, map_one]
    have hcn : ‖f (c : Ω)‖ ≤ 1 := c.2
    have := congrArg norm hc'
    rw [norm_mul, norm_one] at this
    have h0 : 0 ≤ ‖f a‖ := norm_nonneg _
    nlinarith
  have hva : (normVS f).valuation a < 1 :=
    ((normVS f).valuation_lt_one_iff ⟨a, haw⟩).mp hmax
  have hvx : 0 < (normVS f).valuation x := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hx
  have hdecomp : τ x - x = a * x := by
    rw [ha, div_mul_cancel₀ _ hx]
  rw [hdecomp, Valuation.map_mul]
  exact mul_lt_of_lt_one_left hvx hva

variable {K : Type} [Field K] [NumberField K]

/-- **`RaynaudPlace` in the manuscript's form** (diophantine_zq.tex L817-818, at the place of `embP`): a wild
`σ' ∈ G_K` (over `decomp σ`, `σ ∈ wildSet`) that fixes `A(K̄)[m]` fixes `A(K̄)[ℓⁿ]` for every prime `ℓ ≠ p`
(TailH's `RaynaudPlace` asks only `(σ' - 1)² = 0`). -/
def RaynaudPlaceFix (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ (n : ℕ) (x : A.Pt (AlgebraicClosure K)), x ^ (ℓ ^ n) = 1 →
      A.galAct σ' x = x

/-- **Fixing gives `(σ' - 1)² = 0` (proved)**: `RaynaudPlaceFix` implies TailH's `RaynaudPlace`. -/
theorem raynaudPlace_of_fix {A : PkgI3.AbVar K} {m : ℕ} (h : RaynaudPlaceFix (p := p) A m) :
    RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' hfix ℓ hℓ hℓp n x hx
  rw [h σ hσ σ' hσ' hfix ℓ hℓ hℓp n x hx, h σ hσ σ' hσ' hfix ℓ hℓ hℓp n x hx]
  group

/-- **`RaynaudPlaceFix` from `RaynaudWildNF` and I2-Tors (proved), for `dim A = 2`, `3 ≤ m`, `p ∤ m`**: the proof
of TailH's `raynaudPlace_of_R6` (the field `F = K(A[m])`, the base change `A_F`, the valuation rings at the place of
`embP` transported along `K̄ ≅ F̄`), with `RaynaudWildNF` applied over `F` in place of r6, and the wild element
`σ₁` shown wild inertia by `isWildInertia_of_wild_gen`. -/
theorem raynaudPlaceFix_of_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF)
    (hTors : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) : RaynaudPlaceFix (p := p) A m := by
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
  have hU := hW F O₁ w₁ hw₁ (ObjBridge.toGrp A₁) m hm3 (isUnit_natCast_normVS _ hpm) hrat σ₁
    (isInertia_of_wild_gen f₁ hσ σ₁ hf₁) (isWildInertia_of_wild_gen f₁ hσ σ₁ hf₁) ℓ hℓ
    (isUnit_natCast_normVS _ hℓp') n (Φ.symm x) hxm
  have hU' : A₁.galAct σ₁ (Φ.symm x) = Φ.symm x := hU
  have hcomm : ∀ z, Φ (A₁.galAct σ₁ z) = A.galAct σg (Φ z) :=
    hΦ σ₁ σg (fun y => (hσ₁ y).symm)
  have h2 := congrArg Φ hU'
  rw [hcomm, MulEquiv.apply_symm_apply] at h2
  exact h2

/-- **`RaynaudPlace` from `RaynaudWildNF` (proved)**: `raynaudPlaceFix_of_wildNF` and `raynaudPlace_of_fix`; a
drop-in replacement for TailH's `raynaudPlace_of_R6`. -/
theorem raynaudPlace_of_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF)
    (hTors : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) : RaynaudPlace (p := p) A m :=
  raynaudPlace_of_fix (raynaudPlaceFix_of_wildNF hW hTors A hdim hm3 hpm)

/-- **`TorsFixWild` at `p ≥ 7`, `p ≠ ℓ` (proved)** from `WildIter`, I2-Tors and `RaynaudPlaceFix`: as TailH's
`torsFixWild_of_raynaud` (the wild `σ'` fixes `A[m]` by `fix_torsion_of_coprime`), then `RaynaudPlaceFix` directly,
with no unipotence step. -/
theorem torsFixWild_of_raynaudFix {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hI : WildIter (p := p) A) (hT3 : TorsGL A 3) (hT7 : TorsGL A 7)
    (hR3 : p ≠ 13 → RaynaudPlaceFix (p := p) A 3) (hR7 : p = 13 → RaynaudPlaceFix (p := p) A 7) :
    TorsFixWild (p := p) A ℓ := by
  intro σ hσ σ' hσ' n x hx
  have hpp : p.Prime := Fact.out
  by_cases h13 : p = 13
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    refine hR7 h13 σ hσ σ' hσ' (fix_torsion_of_coprime hI 7 hT7 ?_ hσ hσ') ℓ Fact.out hℓp n x hx
    rw [card_GL4_seven, h13]; exact coprime_card_GL4_seven
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    refine hR3 h13 σ hσ σ' hσ' (fix_torsion_of_coprime hI 3 hT3 ?_ hσ hσ') ℓ Fact.out hℓp n x hx
    rw [card_GL4_three]; exact coprime_card_GL4_three hpp h7 h13

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from `RaynaudWildNF` and I2-Tors (proved)**: TailH's `tateWildK_of_R6` with
`raynaudPlaceFix_of_wildNF` (`m = 3` for `p ≠ 13`, `m = 7` for `p = 13`) and `torsFixWild_of_raynaudFix`. -/
theorem tateWildK_of_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF) (hTors : ObjBridge.TorsionStructure)
    {A : PkgI3.AbVar K} (hdim : A.dim = 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p) :
    TateWildK (p := p) A ℓ := by
  have hp : p.Prime := Fact.out
  refine tateWildK_of_torsFixWild (torsFixWild_of_raynaudFix hℓp h7 (wildIter A)
    (torsGL_of_leaf hTors A hdim 3 (by norm_num)) (torsGL_of_leaf hTors A hdim 7 (by norm_num))
    (fun _ => raynaudPlaceFix_of_wildNF hW hTors A hdim (by norm_num) ?_)
    (fun h13 => raynaudPlaceFix_of_wildNF hW hTors A hdim (by norm_num) ?_))
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · intro h
    rw [h13] at h
    norm_num at h

/-- **`LocalGlue` on G7's data from `RaynaudWildNF` and I2-Tors (proved)**: TailH's `localGlue_of_leaves` with
`tateWildK_of_wildNF`. -/
theorem localGlue_of_leaves_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_g7_twist h7 hC hK (fun h => tateWildK_of_wildNF hW hTors h7.1 (Ne.symm hpℓ) h) hE hB

end D2WildSec

section D2DescentSec

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] RQ.numberField_of_fd

variable {K : Type} [Field K] [NumberField K]

/-- **The torsion field of the model over `L` on the manuscript's route (proved)** from `RaynaudWildNF`, I2-Tors and
the glue `DescentPts`: TailH's `torsFix_of_descent` (same statement, same field `E`, same degree bound), where for
wild `σ ∈ G_E` the element `σ₀ ∈ G_L` over `decomp σ` fixes `A₀[q]`, so `RaynaudPlaceFix A₀ q` gives directly that
`σ₀` fixes `A₀[ℓⁿ]` (L817-818); no unipotence and no `p`-power period. -/
theorem torsFix_of_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF)
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
    have hR := raynaudPlaceFix_of_wildNF (p := p) hW hTors A₀ hdim₀ hq3 hpq'
    set Q := φ.symm P with hQdef
    have hQ : Q ^ (ℓ ^ n) = 1 := by rw [hQdef, ← map_pow, hP, map_one]
    have hfix := hR σ hσ.2 σ₀ hσ₀' (fun R hR' => hσ₀S R hR') ℓ Fact.out hℓp n Q hQ
    have h1 := hφ σ₀ σ' (hσ₀'.trans hσ'.symm) Q
    rw [hfix, hQdef, MulEquiv.apply_symm_apply] at h1
    exact h1.symm

/-- **`TorsFixWildOdd` at every `p ≠ ℓ` (proved)** from `RaynaudWildNF`, I2-Tors and `DescentPts`: TailH's
`torsFixWildOdd_of_descent` with `torsFix_of_wildNF`. -/
theorem torsFixWildOdd_of_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF)
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
    torsFix_of_wildNF hW hTors hD hℓp q hq3 hqp (Lv (p := p) L) le_rfl
  exact ⟨E, hEfd, hLvE, hdeg.trans (Nat.mul_le_mul_right _ hqN), hfix⟩

/-- **`TorsFixWildE` from `BetaTwist2` (proved; used at `p = 2`)**: TailH's `torsFixWildE_of_twist` with
`torsFix_of_wildNF`. -/
theorem torsFixWildE_of_twist_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hp3 : p ≠ 3) {β : GQ → PadicAlgCl ℓ}
    (hB : BetaTwist2 (p := p) β L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨M, hMfd, hLvM, hMdeg, hMβ⟩ := hB
  haveI := hMfd
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨E, hEfd, hME, hdeg, hfix⟩ :=
    torsFix_of_wildNF hW hTors hD hℓp 3 le_rfl (Ne.symm hp3) M hLvM
  refine ⟨E, hEfd, hLvM.trans hME, ?_, fun σ hσ =>
    ⟨hMβ σ ⟨fun x hx => hσ.1 x (hME hx), hσ.2⟩, hfix σ hσ⟩⟩
  rw [card_GL4_three] at hdeg
  calc Module.finrank ℚ_[p] E ≤ 24261120 * Module.finrank ℚ_[p] M := hdeg
    _ ≤ 24261120 * (4 * Module.finrank ℚ_[p] (Lv (p := p) L)) := Nat.mul_le_mul_left _ hMdeg
    _ = 97044480 * Module.finrank ℚ_[p] (Lv (p := p) L) := by ring
    _ ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) :=
        Nat.mul_le_mul_right _ (by unfold ZInQ.heightG0; norm_num)

/-- **`TateWildKE` at every `p ≠ ℓ` (proved)** from `RaynaudWildNF`, I2-Tors, `DescentPts`, G7's clauses and, at
`p = 2`, `BetaTwist2`: TailH's `tateWildKE_of_descent`. -/
theorem tateWildKE_of_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]
    {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hC : G7Clauses β ε L)
    (hD : DescentPts A L) (hℓp : ℓ ≠ p) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    TateWildKE (p := p) A ℓ β L := by
  by_cases h2 : p = 2
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_twist_wildNF hW hTors hD hℓp (by omega) (hB h2))
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_odd h2 hC (torsFixWildOdd_of_wildNF hW hTors hD hℓp))

/-- **`LocalGlue p Tm a β L` on G7's data (proved)** from `RaynaudWildNF`, I2-Tors and the glue `KerWild`,
`DescentPts` (`p ≤ 5`), `BetaTwist2` (`p = 2`): TailH's `localGlue_of_descent`. -/
theorem localGlue_of_descent_wildNF (hW : _root_.SZRaynaud.RaynaudWildNF)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L] (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hD : p ≤ 5 → DescentPts A L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_leaves_wildNF hW hTors hpℓ h7 hC hK
    (fun h5 => tateWildKE_of_wildNF hW hTors hC (hD h5) (Ne.symm hpℓ) hB) hB

end D2DescentSec

end G15Ram

end

end HDec

#print axioms HDec.G15Ram.isWildInertia_of_wild_gen
#print axioms HDec.G15Ram.raynaudPlaceFix_of_wildNF
#print axioms HDec.G15Ram.torsFix_of_wildNF
#print axioms HDec.G15Ram.localGlue_of_descent_wildNF

import ZInQKernel.OneProof.H.TailH
import ZInQKernel.Contrib.OneProof.SGA7IX35Unip

/-!
# sga735-finish: the readers of r6, re-proved from the nilpotent r6

Task sga735-finish (docs/research/sga735-finish.md). The live readers of r6's conclusion `(σ - 1)² = 0` are
* `HDec.G15Ram.raynaudPlace_of_R6` (wild `σ'` at a place over `p`, for `TateWildK` / `TorsFix…`), and
* `HDec.PkgI2.goodReduction_of_QM_rational3_of_alg` (the `ℓ = 3` quaternion consumer, glue A6).
Both are re-proved here with the same conclusion from `SGA735Nil.RaynaudCriterionNFNil` (σ - 1 nilpotent with
one exponent on all `A[ℓⁿ]`):
* `raynaudPlace_of_R6Nil`: a wild `σ'` has a `p`-power period on each point (`G15Ram.wildIter`), and a unipotent
  automorphism of an `ℓ`-group with a period prime to `ℓ` is trivial (`SGA735Nil.fixed_of_nil_of_iterate`), so
  `σ'` fixes `A[ℓⁿ]` and `(σ' - 1)² = 0` holds trivially. The statement `RaynaudPlace` is unchanged.
* `goodReduction_of_QM_rational3_of_alg_nil`: `(S - 1)^{2^{i+1}} = 0` on every `G[3^k]` gives
  `(S - 1)^{2^i} = 0` on every `G[3^k]` by `PkgI2.quatUnipotentTrivial` applied to `1 + (S - 1)^{2^i}`
  (`SGA735Nil.nilQuat_trivial`).

No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SGA735Nil

/-- **The `ℓ = 3` quaternion core for nilpotent `S - 1`.** `G` a commutative group with endomorphisms
`I² = 2`, `J² = -3`, `IJ = -JI`, each `G[3^{2k}]` free of rank 4 over `ℤ/3^{2k}`, `S` commuting with `I, J`, and
`(S - 1)^N = 0` on every `G[3^M]` (one `N`). Then `S` is the identity on every `G[3^k]`. -/
theorem nilQuat_trivial (hQ : HDec.PkgI2.QuatUnipotentTrivial.{u}) (G : Type u) [CommGroup G]
    (I J S : G →* G)
    (hI : ∀ x, I (I x) = x ^ 2) (hJ : ∀ x, J (J x) * x ^ 3 = 1) (hIJ : ∀ x, J (I x) * I (J x) = 1)
    (hSI : ∀ x, S (I x) = I (S x)) (hSJ : ∀ x, S (J x) = J (S x))
    (hE : ∀ k : ℕ, 1 ≤ k → ∃ e : {x : G | x ^ (3 ^ (2 * k)) = 1} ≃ (Fin (2 * 2) → ZMod (3 ^ (2 * k))),
      ∀ x y : {x : G | x ^ (3 ^ (2 * k)) = 1},
        ∀ h : x.1 * y.1 ∈ {x : G | x ^ (3 ^ (2 * k)) = 1}, e ⟨x.1 * y.1, h⟩ = e x + e y)
    (hN : ∃ N : ℕ, ∀ M : ℕ, ∀ x : G, x ^ (3 ^ M) = 1 → (diffHom S)^[N] x = 1) :
    ∀ k : ℕ, 1 ≤ k → ∀ x, x ^ (3 ^ k) = 1 → S x = x := by
  obtain ⟨N, hN⟩ := hN
  -- commutation of `(S - 1)^j` with `I`, `J`
  have hDI : ∀ (f : G →* G), (∀ x, S (f x) = f (S x)) → ∀ j x,
      (diffHom S)^[j] (f x) = f ((diffHom S)^[j] x) := by
    intro f hf j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, diffHom_apply, diffHom_apply, hf,
        map_mul, map_inv]
  let Q : ℕ → Prop := fun i => ∀ k : ℕ, 1 ≤ k → ∀ x : G, x ^ (3 ^ k) = 1 → (diffHom S)^[2 ^ i] x = 1
  have hQN : Q N := fun k _ x hx =>
    diffHom_iterate_of_le S (Nat.lt_two_pow_self).le x (hN k x hx)
  have hstep : ∀ i, Q (i + 1) → Q i := by
    intro i hQi k hk x hx
    let T : G →* G := diffPow S (2 ^ i)
    have hT : ∀ y, T y = (diffHom S)^[2 ^ i] y := diffPow_apply S _
    have hTf : ∀ (f : G →* G), (∀ x, S (f x) = f (S x)) → ∀ y, onePlus T (f y) = f (onePlus T y) := by
      intro f hf y
      show f y * T (f y) = f (y * T y)
      rw [hT, hT, hDI f hf, map_mul]
    have key := hQ G k hk I J (onePlus T) hI hJ hIJ (hTf I hSI) (hTf J hSJ) (hE k hk)
      (by
        intro y hy
        show y * T y * T (y * T y) * (y * T y)⁻¹ * (y * T y)⁻¹ * y = 1
        have hTT : T (T y) = 1 := by
          rw [hT, hT, ← Function.iterate_add_apply, ← two_mul, ← pow_succ']
          exact hQi (2 * k) (by omega) y hy
        rw [map_mul, hTT, _root_.mul_one]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel) x hx
    have : x * T x = x := key
    rw [← hT]
    exact mul_eq_left.mp this
  have hQ0 : ∀ i, Q (N - i) := by
    intro i
    induction i with
    | zero => simpa using hQN
    | succ i ih =>
      by_cases h : i < N
      · have := hstep (N - (i + 1)) (by rw [show N - (i + 1) + 1 = N - i by omega]; exact ih)
        exact this
      · rw [show N - (i + 1) = N - i by omega]; exact ih
  intro k hk x hx
  have h1 := hQ0 N k hk x hx
  simp only [Nat.sub_self, pow_zero, Function.iterate_one, diffHom_apply] at h1
  exact mul_inv_eq_one.mp h1

end SGA735Nil

namespace HDec

namespace G15Ram

open _root_.PkgI4 (GQp GQ decomp)
open _root_.LadicCond
open CategoryTheory MonObj
open scoped Pointwise

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]

theorem raynaudPlace_of_R6Nil (hR6 : SGA735Nil.RaynaudCriterionNFNil)
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
  obtain ⟨N, hN⟩ := hR6 F O₁ w₁ hw₁ (ObjBridge.toGrp A₁) m hm3 (isUnit_natCast_normVS _ hpm) hrat σ₁
    (isInertia_of_wild_gen f₁ hσ σ₁ hf₁) ℓ hℓ (isUnit_natCast_normVS _ hℓp')
  have hU : (fun y => A₁.galAct σ₁ y * y⁻¹)^[N] (Φ.symm x) = 1 := hN n (Φ.symm x) hxm
  have hcomm : ∀ z, Φ (A₁.galAct σ₁ z) = A.galAct σg (Φ z) :=
    hΦ σ₁ σg (fun y => (hσ₁ y).symm)
  have htr : ∀ (j : ℕ) (z : A₁.Pt Ω), Φ ((fun y => A₁.galAct σ₁ y * y⁻¹)^[j] z) =
      (SGA735Nil.diffHom (A.galAct σg))^[j] (Φ z) := by
    intro j
    induction j with
    | zero => intro z; rfl
    | succ j ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, SGA735Nil.diffHom_apply,
        map_mul, map_inv, hcomm]
  have hD : (SGA735Nil.diffHom (A.galAct σg))^[N] x = 1 := by
    have h1 := htr N (Φ.symm x)
    rw [MulEquiv.apply_symm_apply, hU, map_one] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := wildIter (p := p) A σ hσ σ' hσ' x
  have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
    Nat.Coprime.pow a n ((Nat.coprime_primes Fact.out hℓ).mpr (fun h => hℓp h.symm))
  have hfix : A.galAct σg x = x :=
    SGA735Nil.fixed_of_nil_of_iterate (A.galAct σg) x (ℓ ^ n) (p ^ a) N hcop hx hD ha
  rw [hfix, hfix, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

end G15Ram

namespace PkgI2

open _root_.PkgI2 (IsAbelianVariety IsInertia HasGoodReduction Pts torsion galAct NeronOggShafarevich
  TorsionStructure InertiaTrivialOn)

variable {K : Type} [Field K]

/-- **Glue A6 from the nilpotent r6** (`goodReduction_of_QM_rational3_of_alg` with
`hRay : SGA735Nil.RaynaudCriterionNFNil`; the algebraic step is `SGA735Nil.nilQuat_trivial`). -/
theorem goodReduction_of_QM_rational3_of_alg_nil [NumberField K] (hNOS : NeronOggShafarevich.{0})
    (hRay : SGA735Nil.RaynaudCriterionNFNil) (hTors : TorsionStructure.{0})
    (hAlg : QuatUnipotentTrivial.{0})
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
    obtain ⟨N, hN⟩ := hRay K O w hw A 3 le_rfl h3' hrat σ hσ 3 Nat.prime_three h3'
    exact SGA735Nil.nilQuat_trivial hAlg (Pts A (AlgebraicClosure K)) (endPts A I) (endPts A J)
      (galHomPts A σ) hI hJ hIJ
      (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      (fun k _ => hTors K A 2 (3 ^ (2 * k)) hdim (by positivity)
        (by rw [Nat.cast_pow]; exact pow_ne_zero _ h3K))
      ⟨N, fun M y hy => hN M y hy⟩ k hk x hx
  -- Néron–Ogg–Shafarevich (c) ⇒ (a)
  refine (hNOS K O w hw A).2.mpr ?_
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 ^ (k + 1)) ?_ ?_
  · intro a b hab
    simpa using (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hab)
  · intro k
    refine ⟨by positivity, ?_, key (k + 1) (by omega)⟩
    rw [Nat.cast_pow]; exact h3'.pow _

end PkgI2

end HDec

end

#print axioms SGA735Nil.nilQuat_trivial
#print axioms HDec.G15Ram.raynaudPlace_of_R6Nil
#print axioms HDec.PkgI2.goodReduction_of_QM_rational3_of_alg_nil

import ZInQKernel.OneProof.H.TailZ24
import ZInQKernel.Contrib.OneProof.UnipotentForward

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
open ReductSplit ReductGlue

set_option linter.style.haveILetI false

namespace SGA7Orth

open HDec.WeilPairing (tors Pairing galTors galMu Mu Gal galP)

/-! ## §1. Roots of unity of order prime to the residue characteristic lie in `K` (strictly henselian `O`) -/

section RootsOfUnity

variable {K : Type} [Field K]

/-- **A primitive `N`-th root of unity in `O`** for a strictly henselian discrete valuation ring `O` with `N` a unit
of `O`: lift a primitive root of the separably closed residue field by Hensel's lemma. -/
theorem exists_isPrimitiveRoot_O (O : ValuationSubring K) (hO : IsStrictlyHenselianDVR O) (N : ℕ)
    (hN : IsUnit (N : O)) (hN0 : 0 < N) : ∃ a : O, IsPrimitiveRoot a N := by
  obtain ⟨-, hH, hk⟩ := hO
  haveI := hH
  haveI := hk
  set k := IsLocalRing.ResidueField O
  have hNk : (N : k) ≠ 0 := by
    have := hN.map (IsLocalRing.residue O)
    rw [map_natCast] at this
    exact this.ne_zero
  haveI : NeZero (N : k) := ⟨hNk⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective ζ₀
  let f : Polynomial O := Polynomial.X ^ N - 1
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C 1 hN0.ne'
  have hres : ∀ b : O, IsLocalRing.residue O (f.eval b) = (IsLocalRing.residue O b) ^ N - 1 := by
    intro b
    simp [f]
  have h1 : f.eval a₀ ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, hres, ha₀, hζ₀.pow_eq_one, sub_self]
  have h2 : IsUnit (f.derivative.eval a₀) := by
    have hd : f.derivative.eval a₀ = (N : O) * a₀ ^ (N - 1) := by
      simp [f, Polynomial.derivative_X_pow]
    rw [hd]
    refine hN.mul (IsUnit.pow _ ?_)
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ha₀]
    exact hζ₀.ne_zero hN0.ne'
  obtain ⟨a, ha, haa₀⟩ := HenselianLocalRing.is_henselian f hf a₀ h1 h2
  have hra : IsLocalRing.residue O a = ζ₀ := by
    rw [← ha₀, ← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr haa₀
  have haN : a ^ N = 1 := by
    have : f.eval a = 0 := ha
    simpa [f, sub_eq_zero] using this
  refine ⟨a, haN, fun l hl => ?_⟩
  apply hζ₀.dvd_of_pow_eq_one
  rw [← hra, ← map_pow, hl, map_one]

/-- **`μ_N(K̄) ⊆ K`, so every `σ ∈ G_K` fixes `μ_N`**, for `O` strictly henselian and `N` a unit of `O`. -/
theorem gal_fixes_rootsOfUnity (O : ValuationSubring K) (hO : IsStrictlyHenselianDVR O) (N : ℕ)
    (hN : IsUnit (N : O)) (hN0 : 0 < N) (σ : Gal K) (ζ : AlgebraicClosure K) (hζ : ζ ^ N = 1) :
    σ ζ = ζ := by
  obtain ⟨a, ha⟩ := exists_isPrimitiveRoot_O O hO N hN hN0
  let emb : O →+* AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)).comp O.subtype
  have hemb : Function.Injective emb :=
    (algebraMap K (AlgebraicClosure K)).injective.comp Subtype.val_injective
  have hb : IsPrimitiveRoot (emb a) N := ha.map_of_injective hemb
  haveI : NeZero N := ⟨hN0.ne'⟩
  obtain ⟨i, -, hi⟩ := hb.eq_pow_of_pow_eq_one hζ
  rw [← hi, map_pow]
  congr 1
  exact σ.commutes (a : K)

/-- `σ ∈ G_K` acts trivially on `μ_N` (as `galMu`), under the same hypotheses. -/
theorem galMu_eq_self (O : ValuationSubring K) (hO : IsStrictlyHenselianDVR O) (N : ℕ)
    (hN : IsUnit (N : O)) (hN0 : 0 < N) (σ : Gal K) (z : Mu K N) : galMu N σ z = z := by
  apply Mu.val_injective
  apply Units.ext
  rw [HDec.WeilPairing.galMu_val]
  exact gal_fixes_rootsOfUnity O hO N hN hN0 σ _ (by
    rw [← Units.val_pow_eq_pow_val, Mu.val_pow, Units.val_one])

end RootsOfUnity

/-! ## §2. The new leaf: Grothendieck's orthogonality, semistable case, at finite level -/

open T09Pic in
/-- **LEAF (consequence) `GrothendieckOrthogonalitySS`**: Grothendieck's orthogonality theorem in the semistable
case, read at finite level (SGA 7 I, Exp. IX, Thm 2.4 with the rank count of the proof of Prop. 3.5; numbers
UNVERIFIED, recalled without network). `O` is a strictly henselian discrete valuation ring with fraction field `K`,
`ℓ` a prime invertible in `O`, `A` an abelian variety over `K` with semistable reduction at `O`
(`HasSemistableReduction`), `B = Pic⁰_{A/K}` its dual (`IsPicZero`, any representation of the Picard functor) and
`e` Mumford's Weil pairing `A[ℓⁿ] × B[ℓⁿ] → μ_{ℓⁿ}` (pinned by its values `weilScalar`). Then a point `x ∈ A[ℓⁿ]`
orthogonal to every `G_K`-invariant point of `B[ℓⁿ]` is `G_K`-invariant. Over a strictly henselian base the
inertia group is all of `G_K = Gal(K̄/K)`.

Derivation from the print (SPECULATIVE in its locators, standard in content): with `T = T_ℓ A`, `T' = T_ℓ B` and the
perfect pairing `T × T' → ℤ_ℓ(1)`, the orthogonality theorem says that the toric part `T_t` is the kernel of the
pairing restricted to `T_f × T'_f`, where `T_f = T^I` is the fixed part (`T_f ≅ T_ℓ(N⁰_s)`). For semistable reduction
`rank T_f = 2a + t = 2g - t`, and the same for `B` (same abelian and toric ranks), so `(T'_f)^⊥` has rank `t` and
contains `T_t` (rank `t`, saturated), hence `(T'_f)^⊥ = T_t ⊆ T_f`. Finite level: `T'_f` is a direct summand of
`T'`, so an `x` orthogonal to `B[ℓⁿ]^I ⊇ T'_f / ℓⁿ` lifts to an element of `(T'_f)^⊥ + ℓⁿ T ⊆ T_f + ℓⁿ T`. The sign
and normalization of the pairing (Mumford's `ē_n` against SGA 7's biextension pairing) do not matter. -/
def GrothendieckOrthogonalitySS : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
    ∀ (Pc : Over (Spec (CommRingCat.of K))) (rep : (picardFunctor A.X.hom).obj.RepresentableBy Pc)
      (B : PkgI3.AbVar K) (j : B.X ⟶ Pc), IsPicZero rep B j →
    ∀ (n : ℕ) (e : Pairing A B (ℓ ^ n)),
      (∀ x y, constK A ((e x y).val : AlgebraicClosure K) =
        weilScalar rep j (ℓ ^ n) (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B))) →
    ∀ x : tors A (ℓ ^ n), (∀ y : tors B (ℓ ^ n), (∀ σ : Gal K, galTors B (ℓ ^ n) σ y = y) → e x y = 0) →
      ∀ σ : Gal K, galTors A (ℓ ^ n) σ x = x

/-! ## §3. The finite-level glue: `(σ - 1)² = 0` on `A[ℓⁿ]` -/

/-- **`(σ - 1)² = 0` on `A(K̄)[ℓⁿ]`** for every `σ ∈ G_K`, from the new leaf and the three bundle leaves
`PicRepresentableAbVar`, `PicZeroAbVar`, `WeilPairingMumford`. For `x ∈ A[ℓⁿ]` and `y ∈ B[ℓⁿ]^{G_K}`,
`e(σx - x, y) = e(σx, σy) - e(x, y) = σ(e(x, y)) - e(x, y) = 0` (Galois equivariance, and `μ_{ℓⁿ} ⊆ K`), so
`σx - x` is `G_K`-invariant by the leaf. -/
theorem unipSq_tors (hOrth : GrothendieckOrthogonalitySS) (h1 : T09Pic.PicRepresentableAbVar)
    (h2 : T09Pic.PicZeroAbVar) (h4 : T09Pic.WeilPairingMumford) (K : Type) [Field K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (hO : IsStrictlyHenselianDVR O) (A : PkgI3.AbVar K)
    (hA : HasSemistableReduction A O) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n : ℕ) (σ : Gal K)
    (x : HDec.WeilPairing.P A) (hx : (ℓ ^ n) • x = 0) :
    galP A σ (galP A σ x) - 2 • galP A σ x + x = 0 := by
  obtain ⟨Pc, ⟨rep⟩⟩ := h1 K A
  obtain ⟨B, j, hj⟩ := h2 K A Pc rep
  obtain ⟨e, -, hgal, -, -, -, hval⟩ := h4 K A Pc rep B j hj
  have hN0 : 0 < ℓ ^ n := pow_pos hℓ.pos n
  have hNO : IsUnit ((ℓ ^ n : ℕ) : O) := by rw [Nat.cast_pow]; exact hℓO.pow n
  have hNK : ((ℓ ^ n : ℕ) : K) ≠ 0 := natCast_ne_zero_of_isUnit O hNO
  let xt : tors A (ℓ ^ n) := ⟨x, hx⟩
  let z : tors A (ℓ ^ n) := galTors A (ℓ ^ n) σ xt - xt
  have hz := hOrth K O hO A hA ℓ hℓ hℓO Pc rep B j hj n (e (ℓ ^ n)) (hval (ℓ ^ n) hN0 hNK) z
    (fun y hy => by
      change e (ℓ ^ n) (galTors A (ℓ ^ n) σ xt - xt) y = 0
      rw [map_sub, AddMonoidHom.sub_apply]
      have hy' : e (ℓ ^ n) (galTors A (ℓ ^ n) σ xt) y =
          e (ℓ ^ n) (galTors A (ℓ ^ n) σ xt) (galTors B (ℓ ^ n) σ y) := by rw [hy σ]
      rw [hy', hgal (ℓ ^ n) hN0 hNK σ xt y, galMu_eq_self O hO (ℓ ^ n) hNO hN0, sub_self])
    σ
  have hz' := congrArg Subtype.val hz
  change galP A σ (galP A σ x - x) = galP A σ x - x at hz'
  rw [map_sub] at hz'
  rw [two_nsmul]
  calc galP A σ (galP A σ x) - (galP A σ x + galP A σ x) + x
      = (galP A σ (galP A σ x) - galP A σ x) - (galP A σ x - x) := by abel
    _ = 0 := by rw [hz', sub_self]

/-! ## §4. The field -/

open ZInQ.Contrib.AbVarBC in
/-- **The field `sga7_IX_3_5_ForwardGeom` (statement unchanged)** from the new leaf `GrothendieckOrthogonalitySS`
and the bundle leaves `PicRepresentableAbVar`, `PicZeroAbVar`, `WeilPairingMumford`. `Ω` (a separable closure of
`K`) embeds into `K̄` over `K`, `σ` lifts to `σ' ∈ G_K` (`K̄/K` normal), `A(Ω) → A(K̄)` is injective and
equivariant, and the finite-level statement `unipSq_tors` gives the claim on each component of `T_ℓ`. The inertia
hypothesis is not used: over a strictly henselian base every `σ` is inertial. -/
theorem sga7_IX_3_5_ForwardGeom_of_orth (hOrth : GrothendieckOrthogonalitySS)
    (h1 : T09Pic.PicRepresentableAbVar) (h2 : T09Pic.PicZeroAbVar) (h4 : T09Pic.WeilPairingMumford) :
    UnipotentForward.SGA7_IX_3_5_ForwardGeom := by
  intro K _ O _ hO Ω _ _ _ w hw A ℓ _ hℓO hA σ hσ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsSeparable.isAlgebraic K Ω
  let κ : Ω →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra Ω (AlgebraicClosure K) := κ.toRingHom.toAlgebra
  haveI : IsScalarTower K Ω (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (κ.commutes x).symm)
  haveI : Normal K (AlgebraicClosure K) := IsAlgClosure.normal K _
  let σ' : Gal K := σ.liftNormal (AlgebraicClosure K)
  have hcomm : ∀ x, κ (σ x) = σ' (κ x) := fun x =>
    (AlgEquiv.liftNormal_commutes σ (AlgebraicClosure K) x).symm
  let E : Additive (A.Pt Ω) →+ HDec.WeilPairing.P A := MonoidHom.toAdditive (extPt A κ)
  have hEinj : Function.Injective E := extPt_injective A κ
  have hE : ∀ v, E (MonoidHom.toAdditive (A.galAct σ) v) = galP A σ' (E v) := fun v =>
    congrArg Additive.ofMul (extPt_galAct A κ σ σ' hcomm (Additive.toMul v))
  set f := galTΩ A ℓ σ with hf
  suffices key : ∀ t, f (f t) - 2 • f t + t = 0 by
    refine LinearMap.ext fun t => ?_
    have := key t
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
      LinearMap.zero_apply]
    rw [← this, two_nsmul]
    abel
  intro t
  set φ : Additive (A.Pt Ω) →+ Additive (A.Pt Ω) := MonoidHom.toAdditive (A.galAct σ) with hφ
  have e1 : ∀ (s : TΩ A Ω ℓ) (n : ℕ), (f s).1 n = φ (s.1 n) := fun s n => rfl
  apply Subtype.ext
  funext n
  have hc : (f (f t) - 2 • f t + t).1 n = (f (f t)).1 n - 2 • (f t).1 n + t.1 n := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub, AddSubgroup.coe_nsmul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply]
  rw [hc, e1, e1, e1]
  sorry

end SGA7Orth

#print axioms SGA7Orth.sga7_IX_3_5_ForwardGeom_of_orth

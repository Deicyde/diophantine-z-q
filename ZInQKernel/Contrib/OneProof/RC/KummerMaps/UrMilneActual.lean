import ZInQKernel.Contrib.OneProof.RC.KummerMaps.UrMilneUr
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerMilne

/-!
# Lane RC29, round 3 (item 2): Milne's form of the coefficient pairing

Manuscript `diophantine_zq.tex`, tex 3465–3467 ("A top-coefficient functional used to test a finite
Frobenius ring's perfection is not used as a coefficient-reduction-compatible arithmetic trace")
and the support comparisons, tex 3483–3498. Milne's Theorem I.2.6 (`MilneADT_I_2_6`) is about the
`ℤ`-linear dual `M^D = Hom(M, K^{s×})`; the lane's coefficient pairings `β₀ : M₀ × M₀' → T₀` are
`R`-bilinear and perfect over `R`. The hypothesis predicate `UrMDualForm` (`UrMilneUr.lean`) is the
passage between the two. This file derives it.

* `urM_hom_finite_card` (PROVED, Dedekind's independence of characters,
  `linearIndependent_monoidHom`): `Hom(X, F̄^×)` is finite with at most `|X|` elements for a finite
  abelian group `X`.
* **`urMDualForm_of_generating`** (PROVED): `UrMDualForm` holds for any equivariant
  `λ : T₀ → F̄_w^×` whose kernel contains no nonzero `R`-line (`λ(r t) = 0` for all `r` forces
  `t = 0`, a *generating character* of `T₀`) and any `β₀` with both partial maps injective: the
  two maps `M₀' → Hom(M₀, F̄^×)`, `M₀ → Hom(M₀', F̄^×)` are injective, so the cardinalities
  `|M₀'| ≤ |Hom(M₀, F̄^×)| ≤ |M₀| ≤ |Hom(M₀', F̄^×)| ≤ |M₀'|` agree.
* `urMTop`: **the top coefficient `A_i → ℤ/2^i`** (the coefficient of `t^{i−1}`, tex 3465–3467);
  `urMTop_generating` (PROVED): it is a generating character of `A_i` (for `x = ∑ c_j t^j`, the top
  coefficient of `t^{i−1−j} x` is `c_j`).
* `urMLam` (Definition): `λ : A_i(1) → F̄_w^×`, `t ↦ ℓ_w^{-1}(top(t))`, with `ℓ_w` the equivariant
  discrete logarithm `μ_{2^i}(K̄_w) ≃ ℤ/2^i(1)` of round 2 (`kmilneF`); `urMLam_smul`,
  `urMLam_generating` (PROVED).
* **`urMDualForm_actual`** (PROVED, under lane RC28's GLUE `FullTorsion`): `UrMDualForm` for the
  actual pair `M_i(α) × M_i(α⁻¹) → A_i(1)` (`weilPairingM`) at every place `w ∈ S`.
* **`urM_quasiIso_actual`** (PROVED from `MilneADT_I_2_6`, `NekovarProp524`, `FullTorsion` and the
  standing setting of the actual data): the per-place quasi-isomorphism of (unramified,
  unramified) at `w ∈ S − S₀` for the actual modules, with no remaining hypothesis on the
  coefficient pairing.

The top coefficient is used only inside the annihilator test (as tex 3465–3467 prescribes); the
per-place maps keep the coefficient-valued trace `tr_w`.

Kinds: definitions and PROVED (from the hypotheses named in each statement).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain Polynomial
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### Dedekind's bound for `Hom(X, F̄^×)` -/

section Dedekind

variable (F : Type) [Field F] (X : Type) [AddCommGroup X]

/-- Definition. An additive map `X → F̄^×` as a monoid homomorphism `Multiplicative X → F̄`. -/
def urMToMonoidHom (φ : X →+ UrMUnits F) : Multiplicative X →* AlgebraicClosure F where
  toFun m := urMUnitsVal F (φ (Multiplicative.toAdd m))
  map_one' := by
    change urMUnitsVal F (φ 0) = 1
    rw [map_zero]
    exact urMUnitsVal_zero
  map_mul' a b := by
    change urMUnitsVal F (φ (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [map_add, urMUnitsVal_add]

/-- PROVED. `urMToMonoidHom` is injective. -/
theorem urMToMonoidHom_injective : Function.Injective (urMToMonoidHom F X) := by
  intro φ ψ h
  exact AddMonoidHom.ext fun x => urMUnits_ext (DFunLike.congr_fun h (Multiplicative.ofAdd x))

/-- PROVED (Dedekind's linear independence of characters, `linearIndependent_monoidHom`).
**`Hom(X, F̄^×)` is finite with at most `|X|` elements** for a finite abelian group `X`. -/
theorem urM_hom_finite_card [Finite X] :
    Finite (X →+ UrMUnits F) ∧ Nat.card (X →+ UrMUnits F) ≤ Nat.card X := by
  classical
  have hli := (linearIndependent_monoidHom (Multiplicative X) (AlgebraicClosure F)).comp
    (urMToMonoidHom F X) (urMToMonoidHom_injective F X)
  have : Finite (Multiplicative X) := inferInstanceAs (Finite X)
  have : Fintype (Multiplicative X) := Fintype.ofFinite _
  have hfin : Finite (X →+ UrMUnits F) := hli.finite
  refine ⟨hfin, ?_⟩
  have : Fintype (X →+ UrMUnits F) := Fintype.ofFinite _
  calc Nat.card (X →+ UrMUnits F) = Fintype.card (X →+ UrMUnits F) := Nat.card_eq_fintype_card
    _ ≤ Module.finrank (AlgebraicClosure F) (Multiplicative X → AlgebraicClosure F) :=
        hli.fintype_card_le_finrank
    _ = Fintype.card (Multiplicative X) := Module.finrank_fintype_fun_eq_card (AlgebraicClosure F)
    _ = Nat.card X := by
        rw [← Nat.card_eq_fintype_card]
        rfl

end Dedekind

/-! ### `UrMDualForm` from a generating character -/

section Generating

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  {R : Type} [CommRing R] {M₀ M₀' T₀ : Type}
  [AddCommGroup M₀] [Module R M₀] [Finite M₀] [AddCommGroup M₀'] [Module R M₀'] [Finite M₀']
  [AddCommGroup T₀] [Module R T₀] [DistribMulAction (GKS K S₀) T₀]
  (β₀ : M₀ →ₗ[R] M₀' →ₗ[R] T₀)

/-- PROVED. **`UrMDualForm` from a generating character**: an equivariant `λ : T₀ → F̄_w^×` such
that `λ(r t) = 0` for all `r ∈ R` forces `t = 0`, for a pairing `β₀` with both partial maps
injective (e.g. perfect). The maps `m' ↦ λ ∘ β₀(·, m')` and `m ↦ λ ∘ β₀(m, ·)` are injective
(`λ(β₀(r m, m')) = λ(r β₀(m, m'))`), so by Dedekind's bound `urM_hom_finite_card` the first is a
bijection onto `Hom(M₀, F̄_w^×)`. -/
theorem urMDualForm_of_generating (w : Places K S) (lam : T₀ →+ UrMUnits (w.1.adicCompletion K))
    (hlam : ∀ (g : Gloc K w.1) (t : T₀), lam (inflMap K hS (locMap K S w.1 g) • t) = g • lam t)
    (hgen : ∀ t : T₀, (∀ r : R, lam (r • t) = 0) → t = 0)
    (hinj : Function.Injective β₀) (hinj' : Function.Injective β₀.flip) :
    UrMDualForm hS β₀ w := by
  refine ⟨lam, hlam, ?_⟩
  have hψ : Function.Injective fun m' : M₀' => lam.comp (β₀.flip m').toAddMonoidHom := by
    intro a b hab
    have h0 : ∀ m : M₀, lam (β₀ m (a - b)) = 0 := by
      intro m
      have e := DFunLike.congr_fun hab m
      change lam (β₀ m a) = lam (β₀ m b) at e
      rw [map_sub, map_sub, e, sub_self]
    have h1 : β₀.flip (a - b) = β₀.flip 0 := by
      refine LinearMap.ext fun m => ?_
      rw [map_zero, LinearMap.zero_apply, LinearMap.flip_apply]
      refine hgen _ fun r => ?_
      rw [← LinearMap.map_smul₂]
      exact h0 (r • m)
    exact sub_eq_zero.1 (hinj' h1)
  have hψ' : Function.Injective fun m : M₀ => lam.comp (β₀ m).toAddMonoidHom := by
    intro a b hab
    have h0 : ∀ m' : M₀', lam (β₀ (a - b) m') = 0 := by
      intro m'
      have e := DFunLike.congr_fun hab m'
      change lam (β₀ a m') = lam (β₀ b m') at e
      rw [map_sub, LinearMap.sub_apply, map_sub, e, sub_self]
    have h1 : β₀ (a - b) = β₀ 0 := by
      refine LinearMap.ext fun m' => ?_
      rw [map_zero, LinearMap.zero_apply]
      refine hgen _ fun r => ?_
      rw [← map_smul]
      exact h0 (r • m')
    exact sub_eq_zero.1 (hinj h1)
  obtain ⟨hfin, hcard⟩ := urM_hom_finite_card (w.1.adicCompletion K) M₀
  obtain ⟨hfin', hcard'⟩ := urM_hom_finite_card (w.1.adicCompletion K) M₀'
  have c2 := Nat.card_le_card_of_injective _ hψ'
  exact hψ.bijective_of_nat_card_le (hcard.trans (c2.trans hcard'))

end Generating

/-! ### The top coefficient of `A_i` -/

section Top

variable (i : ℕ)

/-- Definition (tex 2724–2725, 3465–3467). **The top coefficient `A_i → ℤ/2^i`**: the coefficient
of `t^{i−1}` of the reduced representative (Mathlib's `AdjoinRoot.modByMonicHom` for the monic
`t^i`). -/
def urMTop : Acoef i →ₗ[ZMod (2 ^ i)] ZMod (2 ^ i) :=
  (Polynomial.lcoeff (ZMod (2 ^ i)) (i - 1)).comp
    (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow i))

/-- PROVED. The top coefficient of the class of `q` is the coefficient of `t^{i−1}` in `q`. -/
theorem urMTop_mk [NeZero i] (q : (ZMod (2 ^ i))[X]) :
    urMTop i (Ideal.Quotient.mk _ q) = q.coeff (i - 1) := by
  have hi := NeZero.ne i
  change ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow i))
    (AdjoinRoot.mk (X ^ i) q)).coeff (i - 1) = _
  rw [AdjoinRoot.modByMonicHom_mk, Polynomial.modByMonic_eq_sub_mul_div q (X ^ i),
    Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), sub_zero]

/-- PROVED. **The top coefficient is a generating character of `A_i`**: if the top coefficient
of `r x` vanishes for every `r`, then `x = 0` (the top coefficient of `t^{i−1−j} x` is the
coefficient `c_j` of `x`). -/
theorem urMTop_generating [NeZero i] (x : Acoef i) (h : ∀ r : Acoef i, urMTop i (r * x) = 0) :
    x = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  intro d hd
  have e := h (Ideal.Quotient.mk _ (X ^ (i - 1 - d)))
  rw [← map_mul, urMTop_mk, Polynomial.coeff_X_pow_mul', ite_eq_left (by omega)] at e
  rwa [show i - 1 - (i - 1 - d) = d by omega] at e

end Top

/-! ### The generating character `λ : A_i(1) → F̄_w^×` -/

section Lam

variable (F : Type) [Field F] (m : ℕ)

/-- Definition. The inclusion `μ_m(F̄) ⊆ F̄^×`. -/
def urMMuIncl : MuAlg F m →+ UrMUnits F where
  toFun ζ := urMUnitsMk F ((Additive.toMul ζ : rootsOfUnity m (AlgebraicClosure F)) :
    (AlgebraicClosure F)ˣ)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- PROVED. The inclusion `μ_m(F̄) ⊆ F̄^×` is injective. -/
theorem urMMuIncl_injective : Function.Injective (urMMuIncl F m) := fun _ _ h =>
  muAlg_ext F m (congrArg (urMUnitsVal F) h)

/-- PROVED. The inclusion `μ_m(F̄) ⊆ F̄^×` is Galois-equivariant. -/
theorem urMMuIncl_smul (σ : Field.absoluteGaloisGroup F) (ζ : MuAlg F m) :
    urMMuIncl F m (σ • ζ) = σ • urMMuIncl F m ζ :=
  urMUnits_ext ((coe_smul_muAlg F m σ ζ).trans (urMUnitsVal_smul σ (urMMuIncl F m ζ)).symm)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (i : ℕ) [NeZero i] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i)) (w : Places K S)

/-- Definition. The top coefficient `A_i(1) → ℤ/2^i(1)`, into the local module at `w`. -/
def urMTopTate : Tate1 (Acoef i) hμ₀ →+
    ResMod (locMap K S w.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀)) where
  toFun t := urMTop i (CharMod.equiv (Acoef i) (cycA (Acoef i) hμ₀) t)
  map_zero' := by
    rw [map_zero, map_zero]
    rfl
  map_add' a b := by
    rw [map_add, map_add]
    rfl

/-- Definition (tex 3465–3467). **The generating character `λ : A_i(1) → F̄_w^×`**: the top
coefficient, then the inverse of round 2's equivariant discrete logarithm
`ℓ_w : μ_{2^i}(K̄_w) ≃ ℤ/2^i(1)` (`kmilneF`), then `μ_{2^i} ⊆ F̄_w^×`. -/
def urMLam : Tate1 (Acoef i) hμ₀ →+ UrMUnits (w.1.adicCompletion K) :=
  (urMMuIncl (w.1.adicCompletion K) (2 ^ i)).comp
    ((kmilneF hS i w hμ₀).symm.toAddMonoidHom.comp (urMTopTate hS i hμ₀ w))

omit [NeZero i] in
/-- PROVED. **`λ` is `G_{K_w}`-equivariant**: the top coefficient is `ℤ/2^i`-linear (the Galois
action on `A_i(1)` and on `ℤ/2^i(1)` is multiplication by the cyclotomic character), and
`ℓ_w`, `μ_{2^i} ⊆ F̄_w^×` are equivariant (`kmilneF_smul`, `urMMuIncl_smul`). -/
theorem urMLam_smul (g : Gloc K w.1) (t : Tate1 (Acoef i) hμ₀) :
    urMLam hS i hμ₀ w (inflMap K hS (locMap K S w.1 g) • t) = g • urMLam hS i hμ₀ w t := by
  have htop : urMTopTate hS i hμ₀ w (inflMap K hS (locMap K S w.1 g) • t) =
      g • urMTopTate hS i hμ₀ w t := by
    change urMTop i (((cycA (Acoef i) hμ₀ (inflMap K hS (locMap K S w.1 g)) : (Acoef i)ˣ) :
        Acoef i) * (show Acoef i from t)) =
      ((cycA (ZMod (2 ^ i)) hμ₀ (inflMap K hS (locMap K S w.1 g)) : (ZMod (2 ^ i))ˣ) :
        ZMod (2 ^ i)) * urMTop i (show Acoef i from t)
    change urMTop i (algebraMap (ZMod (2 ^ i)) (Acoef i)
        ((cycS hμ₀ (inflMap K hS (locMap K S w.1 g)) : (ZMod (2 ^ i))ˣ) : ZMod (2 ^ i)) *
          (show Acoef i from t)) =
      algebraMap (ZMod (2 ^ i)) (ZMod (2 ^ i))
        ((cycS hμ₀ (inflMap K hS (locMap K S w.1 g)) : (ZMod (2 ^ i))ˣ) : ZMod (2 ^ i)) *
          urMTop i (show Acoef i from t)
    rw [← Algebra.smul_def, map_smul, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]
  have hk : (kmilneF hS i w hμ₀).symm (g • urMTopTate hS i hμ₀ w t) =
      g • (kmilneF hS i w hμ₀).symm (urMTopTate hS i hμ₀ w t) := by
    apply (kmilneF hS i w hμ₀).injective
    rw [AddEquiv.apply_symm_apply, kmilneF_smul, AddEquiv.apply_symm_apply]
  change urMMuIncl (w.1.adicCompletion K) (2 ^ i) ((kmilneF hS i w hμ₀).symm
      (urMTopTate hS i hμ₀ w (inflMap K hS (locMap K S w.1 g) • t))) =
    g • urMMuIncl (w.1.adicCompletion K) (2 ^ i) ((kmilneF hS i w hμ₀).symm
      (urMTopTate hS i hμ₀ w t))
  rw [htop, hk, urMMuIncl_smul]

/-- PROVED. **`λ` is a generating character of `A_i(1)`** (`urMTop_generating`; `ℓ_w` and
`μ_{2^i} ⊆ F̄_w^×` are injective). -/
theorem urMLam_generating (t : Tate1 (Acoef i) hμ₀)
    (h : ∀ r : Acoef i, urMLam hS i hμ₀ w (r • t) = 0) : t = 0 := by
  have h' : ∀ r : Acoef i, urMTop i (r * (show Acoef i from t)) = 0 := by
    intro r
    have e := h r
    change urMMuIncl (w.1.adicCompletion K) (2 ^ i) ((kmilneF hS i w hμ₀).symm
      (urMTopTate hS i hμ₀ w (r • t))) = 0 at e
    have e1 := (injective_iff_map_eq_zero _).1 (urMMuIncl_injective (w.1.adicCompletion K) (2 ^ i))
      _ e
    have e2 := (injective_iff_map_eq_zero _).1 (kmilneF hS i w hμ₀).symm.injective _ e1
    exact e2
  exact urMTop_generating i (show Acoef i from t) h'

/-- PROVED (under lane RC28's GLUE `FullTorsion`, tex 2726, 2798–2804: `E[2^i]` is defined over
`K_{S₀}`). **`UrMDualForm` for the actual data** (tex 3465–3467): the Weil pairing
`M_i(α) × M_i(α⁻¹) → A_i(1)` (`weilPairingM`, tex 2798–2804) is in Milne's form at every place
`w ∈ S`, through the generating character `urMLam` (`urMDualForm_of_generating`, with the
perfectness `weilPairingM_bijective`, `weilPairingM_flip_bijective`). -/
theorem urMDualForm_actual (W : WeierstrassCurve K) [W.IsElliptic] (α : GKS K S₀ →* (Acoef i)ˣ)
    [IsOpenKer α] [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (hW : FullTorsion K S₀ W (2 ^ i)) :
    UrMDualForm hS (weilPairingM W hμ₀ (Acoef i) α) w :=
  urMDualForm_of_generating hS (weilPairingM W hμ₀ (Acoef i) α) w (urMLam hS i hμ₀ w)
    (urMLam_smul hS i hμ₀ w) (urMLam_generating hS i hμ₀ w)
    (weilPairingM_bijective W hμ₀ (Acoef i) α hW).1
    (weilPairingM_flip_bijective W hμ₀ (Acoef i) α hW).1

end Lam

/-! ### The per-place quasi-isomorphism for the actual data -/

section Actual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (i : ℕ) [NeZero i] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))

/-- PROVED from the PRINTs `MilneADT_I_2_6` (Milne ADT I.2.6; tex 3483–3498, 3815–3816) and lane
RC26's `NekovarProp524` (Nekovář 5.2.4; tex 3455–3456), under lane RC28's GLUE `FullTorsion`
(tex 2726, 2798–2804) and the standing setting of the actual data (`K` totally complex, `S₀ ⊆ S`
finite with the primes above `2` in `S₀`; Nekovář 5.1, tex 3455–3456). **The per-place
quasi-isomorphism of (unramified, unramified) at `w ∈ S − S₀` for the actual modules
`M_i(α)`, `M_i(α⁻¹)` and the Weil pairing** (tex 3483–3498, 3815–3816), for every isotropy homotopy
`J` and every trace `tr_w` killing coboundaries and inducing `H² ≅ A_i`; this replaces
`NekovarProp756` at these places (compare `orthUr_quasiIso_of_print`). -/
theorem urM_quasiIso_actual (hM : MilneADT_I_2_6) (h524 : NekovarProp524 K)
    (hK : IsTotallyComplex K) (hS₀fin : S₀.Finite) (hSfin : S.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (W : WeierstrassCurve K) [W.IsElliptic] (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (hW : FullTorsion K S₀ W (2 ^ i)) (w : Places K S) (hw : w.1 ∉ S₀)
    (J : LocalTruncIsotropy (urAt hS (Acoef i) (Mcoef K S₀ W i α) w hw).i
      (urAt hS (Acoef i) (Mcoef K S₀ W i (charInv α)) w hw).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) w))
    (trv : (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) w).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ z, trv ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) w).d 1 2 rfl z) = 0)
    (htrv2 : InducesIsoH2 trv) :
    QuasiIso (GHom.toCC (orthLocalMap (urAt hS (Acoef i) (Mcoef K S₀ W i α) w hw).i
      (urAt hS (Acoef i) (Mcoef K S₀ W i (charInv α)) w hw).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) w) J trv htrv)) :=
  urM_quasiIso_of_milne hS (weilPairingM W hμ₀ (Acoef i) α) (weilPairingM_smul W hμ₀ (Acoef i) α)
    hM h524 2 (nekovarFiniteSetting_acoef K hK S₀ hS₀fin h2₀ i) hSfin
    (weilPairingM_bijective W hμ₀ (Acoef i) α hW) (weilPairingM_flip_bijective W hμ₀ (Acoef i) α hW)
    (isCyclotomicTwist_tate1 (Acoef i) hμ₀) w hw (urMDualForm_actual hS i hμ₀ w W α hW) J trv htrv
    htrv2

end Actual

end ZInQ.Manuscript.RC.KummerMaps

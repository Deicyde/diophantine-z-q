import ZInQKernel.Contrib.OneProof.ShimuraSplit2

noncomputable section

set_option linter.unusedSectionVars false

namespace QMRecPrinted

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)
open scoped TensorProduct FiniteAdeleExtension MonObj

section Defs

variable {E : Type} [Field E] [NumberField E] {g : ℕ}

def cmVec (Φ : Fin g → E →+* ℂ) : E →+ (Fin g → ℂ) where
  toFun x i := Φ i x
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

def cmLat (Φ : Fin g → E →+* ℂ) (𝔞 : AddSubgroup E) : Submodule ℤ (Fin g → ℂ) :=
  (𝔞.map (cmVec Φ)).toIntSubmodule

def latHat (𝔞 : AddSubgroup E) : AddSubgroup (AQ ⊗[ℚ] E) :=
  AddSubgroup.closure {w | ∃ c ∈ ZhatQ, ∃ x ∈ 𝔞, w = c ⊗ₜ x}

def latAct (t : AQ ⊗[ℚ] E) (𝔞 : AddSubgroup E) : AddSubgroup E :=
  (latHat 𝔞).comap ((AddMonoidHom.mulLeft t).comp
    (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] AQ ⊗[ℚ] E).toRingHom.toAddMonoidHom)

variable {Er : Type} [Field Er] [NumberField Er] {n : ℕ}

def rhoA (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) :
    AQ ⊗[ℚ] Er →ₐ[AQ] Matrix (Fin n) (Fin n) (AQ ⊗[ℚ] E) :=
  AlgHom.liftEquiv ℚ AQ Er _
    (((Algebra.TensorProduct.includeRight : E →ₐ[ℚ] AQ ⊗[ℚ] E).mapMatrix).comp ρ)

def reflexNorm (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) :
    (FiniteAdeleRing (𝓞 Er) Er)ˣ →* (AQ ⊗[ℚ] E)ˣ :=
  Units.map (Matrix.detMonoidHom.comp ((rhoA ρ).toMonoidHom.comp
    ((finiteAdeleBaseChangeAlgEquiv ℚ Er).symm.toMonoidHom)))

def IsReflexModel (Φ : Fin g → E →+* ℂ) (κr : Er →+* ℂ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E)
    (j : (Fin n → E) →+ (Fin g → ℂ)) : Prop :=
  (∀ (e : E) (v : Fin n → E), j (e • v) = fun i => Φ i e * j v i) ∧
  (∀ (a : Er) (v : Fin n → E), j ((ρ a).mulVec v) = κr a • j v) ∧
  Submodule.span ℂ (Set.range j) = ⊤ ∧
  n * Module.finrank ℚ E = g * Module.finrank ℚ Er

def IsOfType (Φ : Fin g → E →+* ℂ) (𝔞 : AddSubgroup E) {A : PkgI3.AbVar ℂ}
    (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) : Prop :=
  ∀ e : E, (∀ x ∈ 𝔞, e * x ∈ 𝔞) →
    ∃ α : PkgI3.AbVar.End A, ∀ w, θ (fun i => Φ i e * w i) = θ w ≫ α.hom

end Defs

def MainTheoremCM : Prop :=
  ∃ ε : ℤˣ,
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-! ## §A The CM field `E = K(√2) = F ⊗ K` -/

section FieldE

open Polynomial

variable {K : Type} [Field K] [NumberField K]

theorem fE_ne_zero : (X ^ 2 - C (2 : K)) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) _

/-- `κ` is not real: some `κ(x)` is not fixed by complex conjugation. -/
theorem exists_not_real [IsTotallyComplex K] (κ : K →+* ℂ) : ∃ x : K, starRingEnd ℂ (κ x) ≠ κ x := by
  have h := (InfinitePlace.isComplex_mk_iff (φ := κ)).1 (IsTotallyComplex.isComplex _)
  rw [ComplexEmbedding.isReal_iff] at h
  by_contra hc
  simp only [not_exists, not_not] at hc
  exact h (RingHom.ext fun x => hc x)

/-- `2` is not a square in an imaginary quadratic field. -/
theorem no_sqrt_two [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (b : K) : b ^ 2 ≠ 2 := by
  intro hb
  have hnr : ∀ r : ℚ, b ≠ r := by
    intro r hr
    rw [hr] at hb
    have h2 : (r : ℚ) ^ 2 = 2 := by exact_mod_cast hb
    have : IsSquare (2 : ℚ) := ⟨r, by rw [← h2]; ring⟩
    rw [Rat.isSquare_iff] at this; norm_num at this
  obtain ⟨κ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hκb : starRingEnd ℂ (κ b) = κ b := by
    have h2 : κ b ^ 2 = 2 := by rw [← map_pow, hb, map_ofNat]
    have hs : κ b = (√2 : ℝ) ∨ κ b = -((√2 : ℝ) : ℂ) := by
      have : (κ b - (√2 : ℝ)) * (κ b + (√2 : ℝ)) = 0 := by
        have e : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
          rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
        linear_combination h2 - e
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases hs with h | h <;> rw [h] <;> simp [Complex.conj_ofReal]
  obtain ⟨x, hx⟩ := exists_not_real κ
  obtain ⟨r, s, rfl⟩ := exists_rat_repr hK hnr x
  apply hx
  simp [map_add, map_mul, map_ratCast, hκb]

theorem irr_fE [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) : Irreducible (X ^ 2 - C (2 : K)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (no_sqrt_two hK)

variable [Fact (Irreducible (X ^ 2 - C (2 : K)))]

/-- `E = K(√2)`. -/
abbrev EK (K : Type) [Field K] := AdjoinRoot (X ^ 2 - C (2 : K))

instance : CharZero (EK K) := charZero_of_injective_algebraMap (algebraMap K (EK K)).injective

instance : FiniteDimensional K (EK K) := (AdjoinRoot.powerBasis (fE_ne_zero (K := K))).finite

instance : NumberField (EK K) where
  to_finiteDimensional := Module.Finite.trans K (EK K)

theorem finrank_EK_K : Module.finrank K (EK K) = 2 := by
  rw [(AdjoinRoot.powerBasis (fE_ne_zero (K := K))).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

theorem finrank_EK (hK : Module.finrank ℚ K = 2) : Module.finrank ℚ (EK K) = 4 := by
  rw [← Module.finrank_mul_finrank ℚ K (EK K), hK, finrank_EK_K]

/-- The `K`-basis `1, √2` of `E`. -/
def bK : Module.Basis (Fin 2) K (EK K) :=
  (AdjoinRoot.powerBasis (fE_ne_zero (K := K))).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]))

theorem bK_apply (i : Fin 2) : (bK : Module.Basis (Fin 2) K (EK K)) i = AdjoinRoot.root _ ^ (i : ℕ) := by
  simp [bK, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]

theorem decomp (e : EK K) : e = algebraMap K (EK K) (bK.repr e 0) +
    algebraMap K (EK K) (bK.repr e 1) * AdjoinRoot.root _ := by
  conv_lhs => rw [← bK.sum_repr e]
  rw [Fin.sum_univ_two, bK_apply, bK_apply, Algebra.smul_def, Algebra.smul_def]
  simp

theorem sqrt2_sq : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The two embeddings of `E` extending `κ`: `√2 ↦ ±√2`. -/
def phi (κ : K →+* ℂ) (c : ℂ) (hc : c ^ 2 = 2) : EK K →+* ℂ :=
  AdjoinRoot.lift κ c (by rw [eval₂_sub, eval₂_X_pow, eval₂_C, hc, map_ofNat, sub_self])

theorem phi_of (κ : K →+* ℂ) (c : ℂ) (hc : c ^ 2 = 2) (x : K) :
    phi κ c hc (algebraMap K (EK K) x) = κ x := AdjoinRoot.lift_of _

theorem phi_root (κ : K →+* ℂ) (c : ℂ) (hc : c ^ 2 = 2) :
    phi κ c hc (AdjoinRoot.root _) = c := AdjoinRoot.lift_root _

theorem negsqrt2_sq : (-((√2 : ℝ) : ℂ)) ^ 2 = 2 := by rw [neg_sq, sqrt2_sq]

/-- `Φ = (φ₁, φ₂)`, the CM type of `E` lifted from `(K, κ)`. -/
def PhiE (κ : K →+* ℂ) : Fin 2 → EK K →+* ℂ :=
  ![phi κ _ sqrt2_sq, phi κ _ negsqrt2_sq]

theorem phi_apply (κ : K →+* ℂ) (c : ℂ) (hc : c ^ 2 = 2) (e : EK K) :
    phi κ c hc e = κ (bK.repr e 0) + κ (bK.repr e 1) * c := by
  conv_lhs => rw [decomp e]
  rw [map_add, map_mul, phi_of, phi_of, phi_root]

end FieldE

end QMRecPrinted

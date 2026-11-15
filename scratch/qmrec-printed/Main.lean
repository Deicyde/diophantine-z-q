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

/-! ## §B The CM type, its reflex field and the reflex norm -/

section TypeE

open Polynomial

variable {K : Type} [Field K] [NumberField K] [Fact (Irreducible (X ^ 2 - C (2 : K)))]

theorem phiE_of (κ : K →+* ℂ) (i : Fin 2) (x : K) : PhiE κ i (algebraMap K (EK K) x) = κ x := by
  fin_cases i
  · exact phi_of κ _ sqrt2_sq x
  · exact phi_of κ _ negsqrt2_sq x

@[simp] theorem phiE_of' (κ : K →+* ℂ) (i : Fin 2) (x : K) : PhiE κ i (AdjoinRoot.of _ x) = κ x :=
  phiE_of κ i x

theorem phiE0_root (κ : K →+* ℂ) : PhiE κ 0 (AdjoinRoot.root _) = ((√2 : ℝ) : ℂ) :=
  phi_root κ _ sqrt2_sq
theorem phiE1_root (κ : K →+* ℂ) : PhiE κ 1 (AdjoinRoot.root _) = -((√2 : ℝ) : ℂ) :=
  phi_root κ _ negsqrt2_sq

/-- **The reflex field of `(E, Φ)` is `κ(K)`.** -/
theorem reflex_eq (κ : K →+* ℂ) :
    κ.fieldRange = Subfield.closure (Set.range fun e : EK K => ∑ i, PhiE κ i e) := by
  have h : Set.range (fun e : EK K => ∑ i, PhiE κ i e) = (κ.fieldRange : Set ℂ) := by
    ext w
    constructor
    · rintro ⟨e, rfl⟩
      show (∑ i, PhiE κ i e) ∈ (κ.fieldRange : Set ℂ)
      rw [Fin.sum_univ_two]
      simp only [PhiE, Matrix.cons_val_zero, Matrix.cons_val_one, phi_apply]
      exact ⟨2 * bK.repr e 0, by rw [map_mul, map_ofNat]; ring⟩
    · rintro ⟨x, rfl⟩
      refine ⟨algebraMap K (EK K) (x / 2), ?_⟩
      simp only [Fin.sum_univ_two, phiE_of, map_div₀, map_ofNat]
      ring
  rw [h, Subfield.closure_eq]

theorem sqrt2_ne_zero : ((√2 : ℝ) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]; positivity

/-- **`Φ` is a CM type**: `φ₁, φ₂, φ̄₁, φ̄₂` are the four distinct embeddings. -/
theorem type_inj [IsTotallyComplex K] (κ : K →+* ℂ) :
    Function.Injective (Sum.elim (PhiE κ) fun i => (starRingEnd ℂ).comp (PhiE κ i)) := by
  obtain ⟨x0, hx0⟩ := exists_not_real κ
  have hs := sqrt2_ne_zero
  intro a b hab
  have hr := RingHom.congr_fun hab (AdjoinRoot.root _)
  have hx := RingHom.congr_fun hab (algebraMap K (EK K) x0)
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp only [Sum.elim_inl, Sum.elim_inr, RingHom.coe_comp, Function.comp_apply, phiE_of,
      Fin.zero_eta, Fin.mk_one, phiE0_root, phiE1_root, Complex.conj_ofReal, map_neg] at hr hx ⊢
  all_goals first
    | rfl
    | exact absurd (by linear_combination hr / 2 : ((√2 : ℝ) : ℂ) = 0) hs
    | exact absurd (by linear_combination -hr / 2 : ((√2 : ℝ) : ℂ) = 0) hs
    | exact absurd hx.symm hx0
    | exact absurd hx hx0

/-- The model `V = E` of `ℂ^Φ` over the reflex field `K`: `ρ(a)` is multiplication by `a`. -/
def rhoK : K →ₐ[ℚ] Matrix (Fin 1) (Fin 1) (EK K) :=
  (Algebra.ofId K (Matrix (Fin 1) (Fin 1) (EK K))).restrictScalars ℚ

/-- `j(v) = Φ(v₀)`. -/
def jK (κ : K →+* ℂ) : (Fin 1 → EK K) →+ (Fin 2 → ℂ) :=
  (cmVec (PhiE κ)).comp (Pi.evalAddMonoidHom (fun _ => EK K) 0)

theorem jK_apply (κ : K →+* ℂ) (v : Fin 1 → EK K) (i : Fin 2) : jK κ v i = PhiE κ i (v 0) := rfl

theorem rhoK_mulVec (a : K) (v : Fin 1 → EK K) :
    (rhoK a).mulVec v = fun i => algebraMap K (EK K) a * v i := by
  funext i
  simp [rhoK, Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

theorem model [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (κ : K →+* ℂ) :
    IsReflexModel (PhiE κ) κ rhoK (jK κ) := by
  refine ⟨fun e v => ?_, fun a v => ?_, ?_, ?_⟩
  · funext i; simp [jK_apply, map_mul]
  · funext i; simp [jK_apply, rhoK_mulVec, map_mul]
  · rw [eq_top_iff]
    intro w _
    have h1 : jK κ (fun _ => 1) = ![1, 1] := by
      funext i; fin_cases i <;> simp [jK_apply]
    have h2 : jK κ (fun _ => AdjoinRoot.root _) = ![((√2 : ℝ) : ℂ), -((√2 : ℝ) : ℂ)] := by
      funext i; fin_cases i <;> simp [jK_apply, phiE0_root, phiE1_root]
    have hw : w = ((w 0 + w 1) / 2) • jK κ (fun _ => 1) +
        ((w 0 - w 1) / (2 * ((√2 : ℝ) : ℂ))) • jK κ (fun _ => AdjoinRoot.root _) := by
      rw [h1, h2]
      funext i
      fin_cases i <;> simp <;> field_simp [sqrt2_ne_zero] <;> ring
    rw [hw]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  · rw [finrank_EK hK, hK]

/-- `𝔸_f ⊗ K → 𝔸_f ⊗ E`. -/
def inclA : AQ ⊗[ℚ] K →ₐ[AQ] AQ ⊗[ℚ] EK K :=
  Algebra.TensorProduct.map (AlgHom.id AQ AQ) ((Algebra.ofId K (EK K)).restrictScalars ℚ)

theorem rhoA_rhoK (w : AQ ⊗[ℚ] K) : rhoA rhoK w 0 0 = inclA w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a k =>
    rw [rhoA, AlgHom.liftEquiv_tmul]
    simp [rhoK, inclA, Matrix.algebraMap_eq_diagonal, Algebra.TensorProduct.includeRight_apply,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, map_add, Matrix.add_apply, hx, hy]

/-- **The reflex norm of `(E, Φ)` is the inclusion `𝔸_{K,f} → 𝔸_f ⊗ E`.** -/
theorem reflexNorm_rhoK (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (reflexNorm rhoK u : AQ ⊗[ℚ] EK K) = inclA ((finiteAdeleBaseChangeAlgEquiv ℚ K).symm u) := by
  simp only [reflexNorm, Units.coe_map, MonoidHom.coe_comp, Function.comp_apply,
    Matrix.coe_detMonoidHom, Matrix.det_unique]
  exact rhoA_rhoK _

end TypeE

/-! ## §C `E` acting on `B`: `β(a + b√2) = q(a) + i q(b)`, so `ι(β(e))(z, 1)ᵀ = (z φ₁(e), φ₂(e))` -/

section Beta

open Polynomial ShimuraSplit2

variable {K : Type} [Field K] [NumberField K] [Fact (Irreducible (X ^ 2 - C (2 : K)))]

/-- `i ∈ B` (`i² = 2`). -/
def iB : LeafQM.B := ⟨0, 1, 0, 0⟩

theorem iotaC_iB : iotaC iB = !![((√2 : ℝ) : ℂ), 0; 0, -((√2 : ℝ) : ℂ)] := RayClassCFT.qmMat_oI

/-- The `K`-coordinates of `E` in the basis `1, √2`, as `ℚ`-linear maps. -/
def crd (i : Fin 2) : EK K →ₗ[ℚ] K :=
  ((Finsupp.lapply i).comp (bK : Module.Basis (Fin 2) K (EK K)).repr.toLinearMap).restrictScalars ℚ

theorem crd_apply (i : Fin 2) (e : EK K) : crd i e = bK.repr e i := rfl

/-- `β : E → B`, `β(a + b√2) = q(a) + i q(b)` (`E` acts on `B` by `√2 ↦ i·` on the left and `K` through `q` on the
right; `β(e) = e · 1`). -/
def beta (q : K →ₐ[ℚ] LeafQM.B) : EK K →ₗ[ℚ] LeafQM.B :=
  q.toLinearMap ∘ₗ crd 0 + (LinearMap.mulLeft ℚ iB) ∘ₗ q.toLinearMap ∘ₗ crd 1

theorem beta_apply (q : K →ₐ[ℚ] LeafQM.B) (e : EK K) :
    beta q e = q (bK.repr e 0) + iB * q (bK.repr e 1) := rfl

/-- `β(k e) = β(e) q(k)`. -/
theorem beta_algebraMap_mul (q : K →ₐ[ℚ] LeafQM.B) (k : K) (e : EK K) :
    beta q (algebraMap K (EK K) k * e) = beta q e * q k := by
  have h : ∀ i, bK.repr (algebraMap K (EK K) k * e) i = k * bK.repr e i := fun i => by
    rw [← Algebra.smul_def, map_smul]; rfl
  rw [beta_apply, beta_apply, h, h, add_mul, mul_assoc, mul_comm k, mul_comm k, map_mul, map_mul]

theorem phi0_apply (κ : K →+* ℂ) (e : EK K) :
    PhiE κ 0 e = κ (bK.repr e 0) + κ (bK.repr e 1) * ((√2 : ℝ) : ℂ) := phi_apply κ _ sqrt2_sq e

theorem phi1_apply (κ : K →+* ℂ) (e : EK K) :
    PhiE κ 1 e = κ (bK.repr e 0) + κ (bK.repr e 1) * -((√2 : ℝ) : ℂ) := phi_apply κ _ negsqrt2_sq e

/-- **The period identity**: `ι(β(e))(z, 1)ᵀ = (z φ₁(e), φ₂(e))`. -/
theorem vec_beta {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} (hz : IsCMPoint q κ z)
    (e : EK K) : (iotaC (beta q e)).mulVec ![(z : ℂ), 1] = ![(z : ℂ) * PhiE κ 0 e, PhiE κ 1 e] := by
  have h0 : (iotaC (q (bK.repr e 0))).mulVec ![(z : ℂ), 1] = κ (bK.repr e 0) • ![(z : ℂ), 1] := hz _
  have h1 : (iotaC (q (bK.repr e 1))).mulVec ![(z : ℂ), 1] = κ (bK.repr e 1) • ![(z : ℂ), 1] := hz _
  rw [beta_apply, map_add, map_mul, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h0, h1, iotaC_iB,
    phi0_apply, phi1_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem beta_injective {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} (hz : IsCMPoint q κ z) :
    Function.Injective (beta q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro e he
  have h := congrFun (vec_beta hz e) 1
  rw [he, map_zero, Matrix.zero_mulVec] at h
  simp only [Pi.zero_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at h
  exact (map_eq_zero _).1 h.symm

theorem finrank_B : Module.finrank ℚ LeafQM.B = 4 := QuaternionAlgebra.finrank_eq_four _ _ _

/-- `β` as a `ℚ`-linear isomorphism `E ≅ B`. -/
def betaE {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (hz : IsCMPoint q κ z) : EK K ≃ₗ[ℚ] LeafQM.B :=
  LinearMap.linearEquivOfInjective (beta q) (beta_injective hz) (by rw [finrank_EK hK, finrank_B])

theorem betaE_apply {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (hz : IsCMPoint q κ z) (e : EK K) : betaE hK hz e = beta q e := rfl

/-- `z ≠ 0`, and the diagonal map `D_z = diag(z, 1)`. -/
def Dz (z : UpperHalfPlane) : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun w := ![(z : ℂ) * w 0, w 1]
  invFun w := ![(z : ℂ)⁻¹ * w 0, w 1]
  map_add' v w := by funext i; fin_cases i <;> simp [mul_add]
  map_smul' c w := by funext i; fin_cases i <;> simp <;> ring
  left_inv w := by
    funext i; fin_cases i <;> simp [← mul_assoc, inv_mul_cancel₀ (UpperHalfPlane.ne_zero z)]
  right_inv w := by
    funext i; fin_cases i <;> simp [← mul_assoc, mul_inv_cancel₀ (UpperHalfPlane.ne_zero z)]

theorem Dz_apply (z : UpperHalfPlane) (w : Fin 2 → ℂ) : Dz z w = ![(z : ℂ) * w 0, w 1] := rfl

theorem vec_beta' {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} (hz : IsCMPoint q κ z)
    (e : EK K) : (iotaC (beta q e)).mulVec ![(z : ℂ), 1] = Dz z (cmVec (PhiE κ) e) := by
  rw [vec_beta hz, Dz_apply]; rfl

/-- **The lattice of `T(z, h)` in the coordinates of `E`**: if `𝔟 = β⁻¹(L_h)` then `D_z Φ(𝔟) = ι(L_h)(z, 1)ᵀ`. -/
theorem cmLat_map_Dz {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (hz : IsCMPoint q κ z) (𝔟 : AddSubgroup (EK K)) (h : BAQˣ)
    (h𝔟 : ∀ e, e ∈ 𝔟 ↔ beta q e ∈ latB h) :
    (cmLat (PhiE κ) 𝔟).map ((Dz z).toLinearMap.restrictScalars ℤ) = vecLat (z : ℂ) h := by
  ext v
  rw [Submodule.mem_map, mem_vecLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨e, he, rfl⟩ := AddSubgroup.mem_map.1 hw
    exact ⟨beta q e, (h𝔟 e).1 he, vec_beta' hz e⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨e, rfl⟩ := (betaE hK hz).surjective x
    rw [betaE_apply] at hx ⊢
    exact ⟨cmVec (PhiE κ) e, AddSubgroup.mem_map.2 ⟨e, (h𝔟 e).2 hx, rfl⟩, (vec_beta' hz e).symm⟩

end Beta

/-! ## §D Lattices in `B ⊗ 𝔸_f`: `ℤ̂ L_h = 𝒪̂ h⁻¹`, approximation, and the transport `β̂ : 𝔸_f ⊗ E ≅ B ⊗ 𝔸_f` -/

section LatticeB

open ShimuraSplit2

theorem algebraMap_mul_ofQ (c : AQ) (v : Fin 4 → AQ) :
    algebraMap AQ BAQ c * ShimuraGlue.ofQ v = ShimuraGlue.ofQ (fun i => c * v i) := by
  ext <;> simp [ShimuraGlue.ofQ, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem natCast_comm (N : ℕ) (x : BAQ) : (N : BAQ) * x = x * N := (Nat.cast_commute N x)

/-- `w = β(y) + N·ofQ(b)` with `b ∈ ℤ̂⁴`, for `D w ∈ 𝒪̂` (approximation of `ℤ̂` by `ℤ` modulo `DN`). -/
theorem decompose (w : BAQ) {D : ℕ} (hD : 0 < D) (hDw : (D : BAQ) * w ∈ OhatQ) (N : ℕ) (hN : 0 < N) :
    ∃ (y : LeafQM.B) (b : Fin 4 → AQ), (∀ i, b i ∈ ZhatQ) ∧ w = bEmb y + (N : BAQ) * ShimuraGlue.ofQ b := by
  obtain ⟨n, hn, hw⟩ := hDw
  choose m b hb hmb using fun i => exists_int_approx (hn i) (D * N) (by positivity)
  refine ⟨((D : ℚ)⁻¹) • LeafQM.ofInt m, b, hb, ?_⟩
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hD' : (D : BAQ) * bEmb (((D : ℚ)⁻¹) • LeafQM.ofInt m) = bEmb (LeafQM.ofInt m) := by
    rw [← bEmb_natSmul, smul_smul, mul_inv_cancel₀ hD0, one_smul]
  have key : (D : BAQ) * w = (D : BAQ) * (bEmb (((D : ℚ)⁻¹) • LeafQM.ofInt m) +
      (N : BAQ) * ShimuraGlue.ofQ b) := by
    rw [hw, mul_add, hD', bEmb_ofInt, ← mul_assoc, ← Nat.cast_mul, natCast_mul_ofQ, ShimuraGlue.ofQ_add]
    congr 1
    funext i
    rw [hmb i]
    simp only [Pi.add_apply]
    try (push_cast; ring)
  have hu : algebraMap ℚ BAQ (D : ℚ)⁻¹ * (D : BAQ) = 1 := by
    rw [← map_natCast (algebraMap ℚ BAQ), ← map_mul, inv_mul_cancel₀ hD0, map_one]
  calc w = algebraMap ℚ BAQ (D : ℚ)⁻¹ * ((D : BAQ) * w) := by rw [← mul_assoc, hu, one_mul]
    _ = _ := by rw [key, ← mul_assoc, hu, one_mul]

/-- The generators `c β(y)` (`c ∈ ℤ̂`, `y ∈ L_h`) of `ℤ̂ L_h`. -/
def genSet (h : BAQˣ) : Set BAQ := {x | ∃ c ∈ ZhatQ, ∃ y ∈ latB h, x = algebraMap AQ BAQ c * bEmb y}

theorem ofQ_mem_closure (h : BAQˣ) {N : ℕ} (hNh : (N : BAQ) * h ∈ OhatQ) (b : Fin 4 → AQ)
    (hb : ∀ i, b i ∈ ZhatQ) : (N : BAQ) * ShimuraGlue.ofQ b ∈ AddSubgroup.closure (genSet h) := by
  have hgen : ∀ (k : Fin 4) (m : Fin 4 → ℤ), m = Pi.single k 1 →
      (N : BAQ) * ShimuraGlue.ofQ (fun i => b k * ((m i : ℤ) : AQ)) ∈ AddSubgroup.closure (genSet h) := by
    intro k m _
    apply AddSubgroup.subset_closure
    refine ⟨b k, hb k, (N : ℚ) • LeafQM.ofInt m, ?_, ?_⟩
    · show bEmb _ * (h : BAQ) ∈ OhatQ
      rw [bEmb_natSmul, natCast_comm, mul_assoc]
      exact OhatQ_mul (bEmb_mem_of_inO ⟨m, rfl⟩) hNh
    · rw [bEmb_natSmul, bEmb_ofInt, ← algebraMap_mul_ofQ, ← mul_assoc, ← mul_assoc, natCast_comm]
  have hsplit : ShimuraGlue.ofQ b =
      ShimuraGlue.ofQ (fun i => b 0 * (((Pi.single 0 1 : Fin 4 → ℤ) i : ℤ) : AQ)) +
      ShimuraGlue.ofQ (fun i => b 1 * (((Pi.single 1 1 : Fin 4 → ℤ) i : ℤ) : AQ)) +
      ShimuraGlue.ofQ (fun i => b 2 * (((Pi.single 2 1 : Fin 4 → ℤ) i : ℤ) : AQ)) +
      ShimuraGlue.ofQ (fun i => b 3 * (((Pi.single 3 1 : Fin 4 → ℤ) i : ℤ) : AQ)) := by
    rw [ShimuraGlue.ofQ_add, ShimuraGlue.ofQ_add, ShimuraGlue.ofQ_add]
    congr 1
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  rw [hsplit, mul_add, mul_add, mul_add]
  exact add_mem (add_mem (add_mem (hgen 0 _ rfl) (hgen 1 _ rfl)) (hgen 2 _ rfl)) (hgen 3 _ rfl)

/-- **`𝒪̂ h⁻¹ ⊆ ℤ̂ L_h`** (with the easy converse, `𝒪̂ h⁻¹ = ℤ̂ (B ∩ 𝒪̂ h⁻¹)`). -/
theorem lg (h : BAQˣ) (w : BAQ) (hw : w * h ∈ OhatQ) : w ∈ AddSubgroup.closure (genSet h) := by
  obtain ⟨N, hN, hNh⟩ := exists_den_B (h : BAQ)
  obtain ⟨M, hM, hMh⟩ := exists_den_B ((h⁻¹ : BAQˣ) : BAQ)
  have hMw : (M : BAQ) * w ∈ OhatQ := by
    have e : (M : BAQ) * w = (w * h) * ((M : BAQ) * ((h⁻¹ : BAQˣ) : BAQ)) := by
      rw [mul_assoc w, ← mul_assoc (h : BAQ), ← natCast_comm M (h : BAQ), mul_assoc (M : BAQ),
        Units.mul_inv, mul_one, natCast_comm]
    rw [e]; exact OhatQ_mul hw hMh
  obtain ⟨y, b, hb, hwy⟩ := decompose w hM hMw N hN
  have hy : y ∈ latB h := by
    show bEmb y * (h : BAQ) ∈ OhatQ
    have e : bEmb y * (h : BAQ) = w * h + -(ShimuraGlue.ofQ b * ((N : BAQ) * h)) := by
      rw [hwy, add_mul, natCast_comm N (ShimuraGlue.ofQ b), mul_assoc (ShimuraGlue.ofQ b)]; abel
    rw [e]
    exact OhatQ_add hw (OhatQ_neg (OhatQ_mul ⟨b, hb, rfl⟩ hNh))
  rw [hwy]
  exact add_mem (AddSubgroup.subset_closure ⟨1, ZhatS.one_mem, y, hy, by rw [map_one, one_mul]⟩)
    (ofQ_mem_closure h hNh b hb)

/-- **Approximation**: `B` is dense in `B ⊗ 𝔸_f`: for all `w, v` some `y ∈ B` has `(y − w) v ∈ 𝒪̂`. -/
theorem exists_approx (w v : BAQ) : ∃ y : LeafQM.B, (bEmb y - w) * v ∈ OhatQ := by
  obtain ⟨D, hD, hDw⟩ := exists_den_B w
  obtain ⟨N, hN, hNv⟩ := exists_den_B v
  obtain ⟨y, b, hb, hwy⟩ := decompose w hD hDw N hN
  refine ⟨y, ?_⟩
  have e : (bEmb y - w) * v = -(ShimuraGlue.ofQ b * ((N : BAQ) * v)) := by
    rw [hwy, natCast_comm, ← mul_assoc, ← natCast_comm]; noncomm_ring
  rw [e]
  exact OhatQ_neg (OhatQ_mul ⟨b, hb, rfl⟩ hNv)

end LatticeB

section Transport

open Polynomial ShimuraSplit2

variable {K : Type} [Field K] [NumberField K] [Fact (Irreducible (X ^ 2 - C (2 : K)))]

/-- `β̂ : 𝔸_f ⊗ E → B ⊗ 𝔸_f`, `a ⊗ e ↦ a β(e)`. -/
def betaHat (q : K →ₐ[ℚ] LeafQM.B) : AQ ⊗[ℚ] EK K →ₗ[ℚ] BAQ :=
  TensorProduct.lift (((LinearMap.mul ℚ BAQ).compl₂ (bEmb.toLinearMap ∘ₗ beta q)).comp
    ((Algebra.linearMap AQ BAQ).restrictScalars ℚ))

theorem betaHat_tmul (q : K →ₐ[ℚ] LeafQM.B) (a : AQ) (e : EK K) :
    betaHat q (a ⊗ₜ e) = algebraMap AQ BAQ a * bEmb (beta q e) := by
  simp [betaHat]

theorem betaHat_one_tmul (q : K →ₐ[ℚ] LeafQM.B) (e : EK K) : betaHat q (1 ⊗ₜ e) = bEmb (beta q e) := by
  rw [betaHat_tmul, map_one, one_mul]

theorem inclA_tmul (a : AQ) (k : K) : inclA (a ⊗ₜ[ℚ] k) = a ⊗ₜ[ℚ] algebraMap K (EK K) k := by
  simp [inclA]

theorem qT_tmul (q : K →ₐ[ℚ] LeafQM.B) (a : AQ) (k : K) :
    qT q (a ⊗ₜ[ℚ] k) = algebraMap AQ BAQ a * bEmb (q k) := by
  simp [qT]

/-- **`β̂` intertwines the reflex norm with `q̂`**: `β̂(u w) = β̂(w) q̂(u)`. -/
theorem betaHat_inclA_mul (q : K →ₐ[ℚ] LeafQM.B) (u : AQ ⊗[ℚ] K) (w : AQ ⊗[ℚ] EK K) :
    betaHat q (inclA u * w) = betaHat q w * qT q u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, add_mul, map_add, h₁, h₂, map_add, mul_add]
  | tmul a k =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, add_mul]
    | tmul c e =>
      rw [inclA_tmul, Algebra.TensorProduct.tmul_mul_tmul, betaHat_tmul, betaHat_tmul,
        beta_algebraMap_mul, qT_tmul, map_mul, map_mul]
      have h1 : algebraMap AQ BAQ a * algebraMap AQ BAQ c = algebraMap AQ BAQ c * algebraMap AQ BAQ a := by
        rw [← map_mul, mul_comm, map_mul]
      rw [h1]
      simp only [mul_assoc]
      rw [← mul_assoc (algebraMap AQ BAQ a), Algebra.commutes a (bEmb (beta q e)), mul_assoc]

/-- The standard basis `1, i, j, k` of `B`. -/
def stdB : Fin 4 → LeafQM.B := ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem quat_decomp (y : LeafQM.B) :
    y = y.re • stdB 0 + y.imI • stdB 1 + y.imJ • stdB 2 + y.imK • stdB 3 := by
  ext <;> simp [stdB]

/-- A left inverse of `β̂`. -/
def Linv (eb : Fin 4 → EK K) : BAQ →+ AQ ⊗[ℚ] EK K where
  toFun x := x.re ⊗ₜ eb 0 + x.imI ⊗ₜ eb 1 + x.imJ ⊗ₜ eb 2 + x.imK ⊗ₜ eb 3
  map_zero' := by simp
  map_add' x y := by simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add,
    QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add, TensorProduct.add_tmul]; abel

theorem mul_algebraMap_tmul (a : AQ) (r : ℚ) (e : EK K) :
    (a * algebraMap ℚ AQ r) ⊗ₜ[ℚ] e = a ⊗ₜ[ℚ] (r • e) := by
  rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]

theorem Linv_betaHat {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (hz : IsCMPoint q κ z) (w : AQ ⊗[ℚ] EK K) :
    Linv (fun k => (betaE hK hz).symm (stdB k)) (betaHat q w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul a e =>
    rw [betaHat_tmul]
    have hre : ∀ y : LeafQM.B, (algebraMap AQ BAQ a * bEmb y).re = a * algebraMap ℚ AQ y.re := fun y => by
      simp [QuaternionAlgebra.algebraMap_eq, bEmb]
    have hI : ∀ y : LeafQM.B, (algebraMap AQ BAQ a * bEmb y).imI = a * algebraMap ℚ AQ y.imI := fun y => by
      simp [QuaternionAlgebra.algebraMap_eq, bEmb]
    have hJ : ∀ y : LeafQM.B, (algebraMap AQ BAQ a * bEmb y).imJ = a * algebraMap ℚ AQ y.imJ := fun y => by
      simp [QuaternionAlgebra.algebraMap_eq, bEmb]
    have hK' : ∀ y : LeafQM.B, (algebraMap AQ BAQ a * bEmb y).imK = a * algebraMap ℚ AQ y.imK := fun y => by
      simp [QuaternionAlgebra.algebraMap_eq, bEmb]
    show (algebraMap AQ BAQ a * bEmb (beta q e)).re ⊗ₜ _ + _ + _ + _ = _
    rw [hre, hI, hJ, hK', mul_algebraMap_tmul, mul_algebraMap_tmul, mul_algebraMap_tmul,
      mul_algebraMap_tmul, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add,
      ← map_smul, ← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add, ← map_add,
      ← quat_decomp, ← betaE_apply hK hz, LinearEquiv.symm_apply_apply]

theorem betaHat_injective {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (hz : IsCMPoint q κ z) : Function.Injective (betaHat q) :=
  Function.LeftInverse.injective (Linv_betaHat hK hz)

/-- **`𝔞̂ = β̂⁻¹(𝒪̂ h⁻¹)`** for `𝔞 = β⁻¹(L_h)`: `w ∈ 𝔞̂ ↔ β̂(w) h ∈ 𝒪̂`. -/
theorem mem_latHat_iff {q : K →ₐ[ℚ] LeafQM.B} {κ : K →+* ℂ} {z : UpperHalfPlane} [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (hz : IsCMPoint q κ z) (h : BAQˣ) (w : AQ ⊗[ℚ] EK K) :
    w ∈ latHat ((latB h).comap (beta q).toAddMonoidHom) ↔ betaHat q w * h ∈ OhatQ := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hc, e, he, rfl⟩ := hx
      rw [betaHat_tmul, mul_assoc]
      exact algebraMap_mul_mem hc he
    | zero => rw [map_zero, zero_mul]; exact OhatQ_zero
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact OhatQ_add hx hy
    | neg x _ hx => rw [map_neg, neg_mul]; exact OhatQ_neg hx
  · intro hw
    have hle : AddSubgroup.closure (genSet h) ≤
        (latHat ((latB h).comap (beta q).toAddMonoidHom)).map (betaHat q).toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨c, hc, y, hy, rfl⟩
      refine ⟨c ⊗ₜ (betaE hK hz).symm y, AddSubgroup.subset_closure ⟨c, hc, _, ?_, rfl⟩, ?_⟩
      · show beta q ((betaE hK hz).symm y) ∈ latB h
        rw [← betaE_apply hK hz, LinearEquiv.apply_symm_apply]; exact hy
      · rw [LinearMap.toAddMonoidHom_coe, betaHat_tmul, ← betaE_apply hK hz, LinearEquiv.apply_symm_apply]
    obtain ⟨w₀, hw₀, he⟩ := hle (lg h _ hw)
    rwa [betaHat_injective hK hz he] at hw₀

end Transport

end QMRecPrinted

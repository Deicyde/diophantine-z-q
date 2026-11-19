import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.TateLambda
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.TateBasis
import ZInQKernel.Contrib.OneProof.RC.CoefModules.CoefModule
import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity

/-!
# The finite levels `M_i` of `𝕋 = T_2E ⊗ Λ(α)`

Lane RC28 (coefficient modules), round 2. Manuscript `diophantine_zq.tex`: the finite
coefficients `A_i`, `M_i` at tex 2723–2727; `Λ = ℤ₂[[t]]` at tex 2747; `T = T₂E` at tex
2836–2838; the finite characters `Ψ_i = (1+t)^{ξ_i}` and `α_i = χ_h Ψ_i` at tex 2780–2791. The
maps below are the finite levels of the conditional fixed-character construction
`(T_2E ⊗ Λ)(α)` described in the paragraph below, not of a global moving-character module
asserted at tex 2780–2785.

* F1. `lamToAcoef i : Λ → A_i = (ℤ/2^i)[t]/(t^i)`, surjective, with kernel `(2^i, t^i)`.
* F2. `lamToAcoef_onePlusTPow`: `(1+t)^a ↦ (1+t)^(a mod 2^(2i))`; `units_map_lambdaChar`:
  `α = χ_h Ψ` reduces to `α_i = χ_h Ψ_i` with `ξ_i = ξ mod 2^(2i)`.
* F3. `finLev i : 𝕋 → M_i`, `λ ⊗ P ↦ λ̄ ⊗ P_i`, `Λ`-semilinear and Galois-equivariant, killing
  `(2^i, t^i)𝕋`; when `T_2E → E[2^i]` is onto, it is onto with kernel `(2^i, t^i)𝕋`
  (`finLevEquiv`).
* F4. Non-vacuity.

Kinds: definitions and PROVED.
-/

/-!
This is a conditional construction for one supplied continuous Λ-valued character on a fixed
G_{K,S}. Its finite levels are the compatible reductions of that character. The manuscript's
moving characters have conductor primes varying with precision and need not be reductions of
one character (tex 2737–2741, 4269–4277). No identification with the retained inner-limit Selmer
diagrams is proved here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain TensorProduct Filter Topology
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef tA tA_pow two_pow_A unitPowHom_apply)
open ZInQ.Manuscript.RC.CoefModules (Mcoef CoefMod onePlusT onePlusT_pow movingCharS alphaChar
  charMul_apply intUnitsTo TorsS curveEll isElliptic_curveEll)
open scoped PowerSeries.WithPiTopology

attribute [local instance] lambda_isTopologicalRing

/-! ## F1. Truncation and `Λ → A_i` -/

/-- **Truncation `R⟦t⟧ → R[t]/(t^n)`**, a ring map. Kind: definition. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
def truncQuot (R : Type*) [CommRing R] (n : ℕ) :
    PowerSeries R →+* Polynomial R ⧸ Ideal.span {(Polynomial.X : Polynomial R) ^ n} where
  toFun f := Ideal.Quotient.mk _ (PowerSeries.trunc n f)
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial R) ^ n})),
      Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
    intro d hd
    simp only [Polynomial.coeff_sub, PowerSeries.coeff_trunc, hd, ↓reduceIte]
    rw [← Polynomial.coe_one, Polynomial.coeff_coe, sub_self]
  map_mul' f g := by
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
    intro d hd
    have h := congrArg (fun p => Polynomial.coeff p d)
      (PowerSeries.trunc_trunc_mul_trunc (n := n) f g)
    simp only [PowerSeries.coeff_trunc, hd, ↓reduceIte] at h
    simp only [Polynomial.coeff_sub, PowerSeries.coeff_trunc, hd, ↓reduceIte]
    rw [← h, ← Polynomial.coeff_coe, Polynomial.coe_mul, sub_self]
  map_zero' := by simp
  map_add' f g := by simp

/-- Truncation of a polynomial is its class. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem truncQuot_coe (R : Type*) [CommRing R] (n : ℕ) (p : Polynomial R) :
    truncQuot R n (p : PowerSeries R) = Ideal.Quotient.mk _ p := by
  show Ideal.Quotient.mk _ (PowerSeries.trunc n (p : PowerSeries R)) = _
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  intro d hd
  simp only [Polynomial.coeff_sub, PowerSeries.coeff_trunc, hd, ↓reduceIte]
  rw [Polynomial.coeff_coe, sub_self]

/-- **F1: `Λ → A_i`**: coefficients mod `2^i`, then mod `t^i`. Kind: definition. Locator:
`diophantine_zq.tex`, tex 2723–2727 (`A_i`), 2747 (`Λ`). -/
def lamToAcoef (i : ℕ) : Lambda →+* Acoef i :=
  (truncQuot (ZMod (2 ^ i)) i).comp (PowerSeries.map (PadicInt.toZModPow i))

/-- **F1: `t ↦ t`.** Kind: PROVED. Locator: `diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem lamToAcoef_X (i : ℕ) : lamToAcoef i PowerSeries.X = tA i := by
  rw [lamToAcoef, RingHom.comp_apply, PowerSeries.map_X, ← Polynomial.coe_X, truncQuot_coe]
  rfl

/-- Constants: `a ↦ a mod 2^i`. Kind: PROVED. Locator: `diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem lamToAcoef_C (i : ℕ) (a : ℤ_[2]) :
    lamToAcoef i (PowerSeries.C a) =
      Ideal.Quotient.mk _ (Polynomial.C (PadicInt.toZModPow i a)) := by
  rw [lamToAcoef, RingHom.comp_apply, PowerSeries.map_C, ← Polynomial.coe_C, truncQuot_coe]

/-- Constants as natural numbers `resN i a = a mod 2^i`. Kind: PROVED. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem lamToAcoef_algebraMap (i : ℕ) (a : ℤ_[2]) :
    lamToAcoef i (algebraMap ℤ_[2] Lambda a) = ((resN i a : ℕ) : Acoef i) := by
  rw [show algebraMap ℤ_[2] Lambda a = PowerSeries.C a from rfl, lamToAcoef_C,
    ← ZMod.natCast_zmod_val (PadicInt.toZModPow i a), map_natCast, map_natCast]
  rfl

/-- **F1: `Λ → A_i` is surjective.** Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem lamToAcoef_surjective (i : ℕ) : Function.Surjective (lamToAcoef i) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨PowerSeries.mk fun k => ((p.coeff k).val : ℤ_[2]), ?_⟩
  have hmap : PowerSeries.map (PadicInt.toZModPow i)
      (PowerSeries.mk fun k => ((p.coeff k).val : ℤ_[2])) = (p : PowerSeries (ZMod (2 ^ i))) := by
    ext k
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_natCast, ZMod.natCast_zmod_val,
      Polynomial.coeff_coe]
  rw [lamToAcoef, RingHom.comp_apply, hmap, truncQuot_coe]

/-- **F1: the kernel of `Λ → A_i` is `(2^i, t^i)`.** Kind: PROVED. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem ker_lamToAcoef (i : ℕ) : RingHom.ker (lamToAcoef i) = lamIdeal i := by
  apply le_antisymm
  · intro f hf
    change Ideal.Quotient.mk _ (PowerSeries.trunc i (PowerSeries.map (PadicInt.toZModPow i) f))
      = 0 at hf
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at hf
    refine mem_lamIdeal_of_coeff i f fun k hk => ?_
    have h := hf k hk
    simp only [PowerSeries.coeff_trunc, hk, ↓reduceIte, PowerSeries.coeff_map] at h
    have h' : PowerSeries.coeff k f ∈ RingHom.ker (PadicInt.toZModPow (p := 2) i) := h
    rw [PadicInt.ker_toZModPow] at h'
    exact_mod_cast h'
  · rw [lamIdeal, Ideal.span_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, map_ofNat, two_pow_A]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, lamToAcoef_X, tA_pow]

/-! ## F2. The character comparison -/

/-- An additive map with open kernel into a discrete group is continuous. Kind: PROVED.
Locator: `diophantine_zq.tex`, tex 2780–2791. -/
theorem continuous_of_ker_mem_nhds {G H : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [AddGroup H] [TopologicalSpace H] [DiscreteTopology H] (f : G →+ H)
    (hf : ((f.ker : AddSubgroup G) : Set G) ∈ 𝓝 (0 : G)) : Continuous f := by
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hc : Tendsto (fun y : G => y - x) (𝓝 x) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (sub_self x)
  filter_upwards [hc hf] with y hy
  simp only [Set.mem_preimage, SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub,
    sub_eq_zero] at hy
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [hy, hx]

/-- `1 + t` as an element. Kind: PROVED. Locator: `diophantine_zq.tex`, tex 2786–2791. -/
theorem coe_onePlusT (i : ℕ) : ((onePlusT i : (Acoef i)ˣ) : Acoef i) = 1 + tA i :=
  IsUnit.unit_spec _

/-- **F2: `(1+t)^a ↦ (1+t)^(a mod 2^(2i))` in `A_i`**: both sides are continuous in `a` (discrete
target) and agree on the dense `ℕ ⊂ ℤ₂`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2786–2791. -/
theorem lamToAcoef_onePlusTPow (i : ℕ) (a : ℤ_[2]) :
    lamToAcoef i (onePlusTPow a) =
      ((onePlusT i ^ (PadicInt.toZModPow (2 * i) a).val : (Acoef i)ˣ) : Acoef i) := by
  let _ : TopologicalSpace (Acoef i) := ⊥
  have : DiscreteTopology (Acoef i) := ⟨rfl⟩
  let _ : TopologicalSpace (ZMod (2 ^ (2 * i))) := ⊥
  have : DiscreteTopology (ZMod (2 ^ (2 * i))) := ⟨rfl⟩
  have hL : Continuous (lamToAcoef i : Lambda → Acoef i) := by
    refine continuous_of_ker_mem_nhds (lamToAcoef i).toAddMonoidHom
      (Filter.mem_of_superset (lamIdeal_mem_nhds i) fun f hf => ?_)
    change lamToAcoef i f = 0
    rw [← RingHom.mem_ker, ker_lamToAcoef]
    exact hf
  have hZ : Continuous (PadicInt.toZModPow (p := 2) (2 * i) : ℤ_[2] → ZMod (2 ^ (2 * i))) := by
    refine continuous_of_ker_mem_nhds (PadicInt.toZModPow (p := 2) (2 * i)).toAddMonoidHom
      (Filter.mem_of_superset ((isOpen_span_two_pow (2 * i)).mem_nhds (Submodule.zero_mem _))
        fun b hb => ?_)
    change PadicInt.toZModPow (2 * i) b = 0
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact_mod_cast hb
  have key := PadicInt.denseRange_natCast.equalizer (hL.comp continuous_onePlusTPow)
    ((continuous_of_discreteTopology (f := fun z : ZMod (2 ^ (2 * i)) =>
      ((onePlusT i ^ z.val : (Acoef i)ˣ) : Acoef i))).comp hZ) (funext fun n => ?_)
  · exact congrFun key a
  · simp only [Function.comp_apply, onePlusTPow_natCast, map_pow, map_add, map_one,
      lamToAcoef_X, map_natCast, ZMod.val_natCast]
    rw [← pow_eq_pow_mod n (onePlusT_pow i), Units.val_pow_eq_pow_val, coe_onePlusT]

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **`ξ_i = ξ mod 2^n`** for a `ℤ₂`-character `ξ`. Kind: definition. Locator:
`diophantine_zq.tex`, tex 2786–2791. -/
def redZ2 (n : ℕ) (ξ : GKS K S →* Multiplicative ℤ_[2]) :
    GKS K S →* Multiplicative (ZMod (2 ^ n)) :=
  (AddMonoidHom.toMultiplicative
    (PadicInt.toZModPow n : ℤ_[2] →+* ZMod (2 ^ n)).toAddMonoidHom).comp ξ

/-- **F2: `α = χ_h Ψ` mod `(2^i, t^i)` is `α_i = χ_h Ψ_i`** with `ξ_i = ξ mod 2^(2i)`. Kind:
PROVED. Locator: `diophantine_zq.tex`, tex 2780–2791. -/
theorem units_map_lambdaChar (i : ℕ) (χ : GKS K S →* ℤˣ) (ξ : GKS K S →* Multiplicative ℤ_[2]) :
    (Units.map (lamToAcoef i).toMonoidHom).comp (lambdaChar χ ξ) =
      alphaChar i χ (redZ2 (2 * i) ξ) := by
  ext σ
  rw [MonoidHom.comp_apply, Units.coe_map]
  change lamToAcoef i ((lambdaChar χ ξ σ : Lambdaˣ) : Lambda) = _
  rw [coe_lambdaChar, map_mul, map_intCast, lamToAcoef_onePlusTPow, alphaChar, charMul_apply,
    Units.val_mul]
  rfl

/-! ## F3. The finite levels -/

variable {W : WeierstrassCurve K}

/-- **`α_i = α mod (2^i, t^i)`.** Kind: definition. Locator: `diophantine_zq.tex`,
tex 2780–2791. -/
def alphaLev (i : ℕ) (α : GKS K S →* Lambdaˣ) : GKS K S →* (Acoef i)ˣ :=
  (Units.map (lamToAcoef i).toMonoidHom).comp α

omit [NumberField K] in
/-- Values of `α_i`. Kind: PROVED. Locator: `diophantine_zq.tex`, tex 2780–2791. -/
theorem coe_alphaLev (i : ℕ) (α : GKS K S →* Lambdaˣ) (σ : GKS K S) :
    ((alphaLev i α σ : (Acoef i)ˣ) : Acoef i) = lamToAcoef i ((α σ : Lambdaˣ) : Lambda) := rfl

/-- `α_i` for `α = χ_h Ψ` is round 1's `alphaChar`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2780–2791. -/
theorem alphaLev_lambdaChar (i : ℕ) (χ : GKS K S →* ℤˣ) (ξ : GKS K S →* Multiplicative ℤ_[2]) :
    alphaLev i (lambdaChar χ ξ) = alphaChar i χ (redZ2 (2 * i) ξ) :=
  units_map_lambdaChar i χ ξ

variable (K S W) in
/-- The biadditive map `(λ, P) ↦ λ̄ ⊗ P_i`. Kind: definition. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
def finLevBil (i : ℕ) : Lambda →+ TateS K S W →+ Acoef i ⊗[ℤ] Lev K S W i :=
  AddMonoidHom.mk' (fun l => AddMonoidHom.mk' (fun P => lamToAcoef i l ⊗ₜ[ℤ] projLev i P)
    (fun P Q => by simp only [map_add, TensorProduct.tmul_add]))
    (fun l l' => AddMonoidHom.ext fun P => by
      simp only [map_add, TensorProduct.add_tmul, AddMonoidHom.mk'_apply,
        AddMonoidHom.add_apply])

/-- `finLevBil` is `ℤ₂`-balanced (`a • P` has level-`i` coordinate `(a mod 2^i) • P_i`). Kind:
PROVED. Locator: `diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem finLevBil_balanced (i : ℕ) (a : ℤ_[2]) (l : Lambda) (P : TateS K S W) :
    finLevBil K S W i (a • l) P = finLevBil K S W i l (a • P) := by
  show lamToAcoef i (a • l) ⊗ₜ[ℤ] projLev i P = lamToAcoef i l ⊗ₜ[ℤ] projLev i (a • P)
  rw [Algebra.smul_def, map_mul, lamToAcoef_algebraMap, ← nsmul_eq_mul, TensorProduct.smul_tmul]
  rfl

variable (α : GKS K S →* Lambdaˣ)

/-- **The pure tensor `λ ⊗ P` of `𝕋`.** Kind: definition. Locator: `diophantine_zq.tex`,
tex 2747, 2836–2838. -/
def tl (l : Lambda) (P : TateS K S W) : TLam K S W α := (TLam.equiv α).symm (l ⊗ₜ P)

/-- Additivity of `tl` in `λ`. Kind: PROVED. Locator: `diophantine_zq.tex`, tex 2747, 2836–2838. -/
theorem tl_add_left (l l' : Lambda) (P : TateS K S W) :
    tl α (l + l') P = tl α l P + tl α l' P := by
  rw [tl, tl, tl, TensorProduct.add_tmul, map_add]

/-- Additivity of `tl` in `P`. Kind: PROVED. Locator: `diophantine_zq.tex`, tex 2747, 2836–2838. -/
theorem tl_add_right (l : Lambda) (P Q : TateS K S W) :
    tl α l (P + Q) = tl α l P + tl α l Q := by
  rw [tl, tl, tl, TensorProduct.tmul_add, map_add]

/-- `tl` and subtraction in `λ`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2747, 2836–2838. -/
theorem tl_sub_left (l l' : Lambda) (P : TateS K S W) :
    tl α (l - l') P = tl α l P - tl α l' P := by
  rw [tl, tl, tl, TensorProduct.sub_tmul, map_sub]

/-- `tl` and subtraction in `P`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2747, 2836–2838. -/
theorem tl_sub_right (l : Lambda) (P Q : TateS K S W) :
    tl α l (P - Q) = tl α l P - tl α l Q := by
  rw [tl, tl, tl, TensorProduct.tmul_sub, map_sub]

/-- `λ • (λ' ⊗ P) = (λ λ') ⊗ P`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2747, 2836–2838. -/
theorem lam_smul_tl (l l' : Lambda) (P : TateS K S W) : l • tl α l' P = tl α (l * l') P := by
  rw [tl, tl, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul]

/-- The Galois action on pure tensors. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2747, 2836–2838. -/
theorem smul_tl (σ : GKS K S) (l : Lambda) (P : TateS K S W) :
    σ • tl α l P = tl α (((α σ : Lambdaˣ) : Lambda) * l) (σ • P) :=
  TLam.smul_tmul σ l P

/-- Induction on `𝕋` through `tl`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2747, 2836–2838. -/
theorem tl_induction {motive : TLam K S W α → Prop} (x : TLam K S W α) (zero : motive 0)
    (tmul : ∀ (l : Lambda) (P : TateS K S W), motive (tl α l P))
    (add : ∀ x y : TLam K S W α, motive x → motive y → motive (x + y)) : motive x :=
  TLam.induction (α := α) (motive := motive) x zero tmul add

/-- The additive map `𝕋 → M_i`. Kind: definition. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
def finLevAdd (i : ℕ) : TLam K S W α →+ Mcoef K S W i (alphaLev i α) :=
  TensorProduct.liftAddHom (finLevBil K S W i) (finLevBil_balanced i)

/-- `finLevAdd (λ ⊗ P) = λ̄ ⊗ P_i`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem finLevAdd_tmul (i : ℕ) (l : Lambda) (P : TateS K S W) :
    finLevAdd α i (tl α l P) =
      CoefMod.equiv (Acoef i) (alphaLev i α) (TorsS K S W ((2 ^ i : ℕ) : ℤ))
        (lamToAcoef i l ⊗ₜ projLev i P) :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- `Λ`-semilinearity of `finLevAdd`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem finLevAdd_lam_smul (i : ℕ) (l : Lambda) (x : TLam K S W α) :
    finLevAdd α i (l • x) = lamToAcoef i l • finLevAdd α i x := by
  refine tl_induction α
    (motive := fun x => finLevAdd α i (l • x) = lamToAcoef i l • finLevAdd α i x) x ?_
    (fun l' P => ?_) (fun x y hx hy => ?_)
  · rw [smul_zero, map_zero, smul_zero]
  · rw [lam_smul_tl, finLevAdd_tmul, finLevAdd_tmul, map_mul, ← map_smul,
      TensorProduct.smul_tmul', smul_eq_mul]
  · rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **F3: the finite-level map `𝕋 → M_i`, `λ ⊗ P ↦ λ̄ ⊗ P_i`**, semilinear over
`lamToAcoef i`. Kind: definition. Locator: `diophantine_zq.tex`, tex 2723–2727, 2747. -/
def finLev (i : ℕ) : TLam K S W α →ₛₗ[lamToAcoef i] Mcoef K S W i (alphaLev i α) where
  toFun := finLevAdd α i
  map_add' := map_add _
  map_smul' := finLevAdd_lam_smul α i

/-- `finLev (λ ⊗ P) = λ̄ ⊗ P_i`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem finLev_tmul (i : ℕ) (l : Lambda) (P : TateS K S W) :
    finLev α i (tl α l P) =
      CoefMod.equiv (Acoef i) (alphaLev i α) (TorsS K S W ((2 ^ i : ℕ) : ℤ))
        (lamToAcoef i l ⊗ₜ projLev i P) :=
  finLevAdd_tmul α i l P

/-- **F3: `finLev` is Galois-equivariant.** Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem finLev_smul (i : ℕ) (σ : GKS K S) (x : TLam K S W α) :
    finLev α i (σ • x) = σ • finLev α i x := by
  refine tl_induction α (motive := fun x => finLev α i (σ • x) = σ • finLev α i x)
    x ?_ (fun l P => ?_) (fun x y hx hy => ?_)
  · rw [smul_zero, map_zero, smul_zero]
  · rw [smul_tl, finLev_tmul, finLev_tmul, CoefMod.smul_tmul, map_mul, coe_alphaLev,
      projLev_smul]
  · rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **F3 for `α = χ_h Ψ`**: equivariance into round 1's `M_i` with `α_i = χ_h Ψ_i` (use
`alphaLev_lambdaChar`). Kind: PROVED. Locator: `diophantine_zq.tex`, tex 2780–2791. -/
theorem finLev_smul_of_eq (i : ℕ) {α' : GKS K S →* (Acoef i)ˣ} (h : alphaLev i α = α')
    (σ : GKS K S) (x : TLam K S W α) :
    (show Mcoef K S W i α' from finLev α i (σ • x)) =
      σ • (show Mcoef K S W i α' from finLev α i x) := by
  subst h
  exact finLev_smul α i σ x

/-- **F3: `(2^i, t^i)𝕋 ⊆ ker finLev`.** Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem tlamNbhd_le_ker_finLev (i : ℕ) : tlamNbhd K S W α i ≤ LinearMap.ker (finLev α i) := by
  rw [tlamNbhd, Submodule.smul_le]
  intro r hr n _
  rw [LinearMap.mem_ker, LinearMap.map_smulₛₗ]
  have h0 : lamToAcoef i r = 0 := by rw [← RingHom.mem_ker, ker_lamToAcoef]; exact hr
  rw [h0]
  exact zero_smul (Acoef i) (finLev α i n)

/-- `λ ⊗ P ∈ (2^i, t^i)𝕋` for `λ ∈ (2^i, t^i)`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem tl_mem_tlamNbhd_of_mem {i : ℕ} {l : Lambda} (hl : l ∈ lamIdeal i) (P : TateS K S W) :
    tl α l P ∈ tlamNbhd K S W α i := by
  rw [show tl α l P = l • tl α 1 P by rw [lam_smul_tl, mul_one]]
  exact Submodule.smul_mem_smul hl Submodule.mem_top

/-- `λ ⊗ P ∈ (2^i, t^i)𝕋` for `P_i = 0` (`P ∈ 2^i T`, `mem_ker_projLev_iff`). Kind: PROVED.
Locator: `diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem tl_mem_tlamNbhd_of_projLev {i : ℕ} (l : Lambda) {P : TateS K S W}
    (hP : projLev i P = 0) : tl α l P ∈ tlamNbhd K S W α i := by
  obtain ⟨Q, rfl⟩ := (mem_ker_projLev_iff i P).mp (congrArg Subtype.val hP)
  have e : tl α l ((2 : ℤ_[2]) ^ i • Q) = ((2 : Lambda) ^ i) • tl α l Q := by
    rw [tl, tl, ← map_smul]
    congr 1
    rw [TensorProduct.tmul_smul, ← algebraMap_smul Lambda ((2 : ℤ_[2]) ^ i), map_pow, map_ofNat]
  rw [e]
  exact Submodule.smul_mem_smul (two_pow_mem_lamIdeal i) Submodule.mem_top

/-- Classes of `λ ⊗ P` only depend on `P_i`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem mk_tl_eq_of_projLev {i : ℕ} (l : Lambda) {P P' : TateS K S W}
    (h : projLev i P = projLev i P') :
    (Submodule.Quotient.mk (tl α l P) : TLam K S W α ⧸ tlamNbhd K S W α i) =
      Submodule.Quotient.mk (tl α l P') := by
  rw [Submodule.Quotient.eq, ← tl_sub_right]
  exact tl_mem_tlamNbhd_of_projLev α l (by rw [map_sub, h, sub_self])

/-- Classes of `λ ⊗ P` only depend on `λ̄`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem mk_tl_eq_of_lamToAcoef {i : ℕ} {l l' : Lambda} (h : lamToAcoef i l = lamToAcoef i l')
    (P : TateS K S W) :
    (Submodule.Quotient.mk (tl α l P) : TLam K S W α ⧸ tlamNbhd K S W α i) =
      Submodule.Quotient.mk (tl α l' P) := by
  rw [Submodule.Quotient.eq, ← tl_sub_left]
  refine tl_mem_tlamNbhd_of_mem α ?_ P
  rw [← ker_lamToAcoef, RingHom.mem_ker, map_sub, h, sub_self]

section Surj

variable {i : ℕ} (hsurj : Function.Surjective (projLev (K := K) (S := S) (W := W) i))

/-- The inverse on pure tensors, through chosen lifts. Kind: definition. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
def finLevInvBil : Acoef i →+ Lev K S W i →+ (TLam K S W α ⧸ tlamNbhd K S W α i) :=
  AddMonoidHom.mk' (fun c => AddMonoidHom.mk' (fun Q => Submodule.Quotient.mk
      (tl α (Function.surjInv (lamToAcoef_surjective i) c) (Function.surjInv hsurj Q)))
      (fun Q Q' => by
        rw [mk_tl_eq_of_projLev α _ (P' := Function.surjInv hsurj Q + Function.surjInv hsurj Q')
          (by rw [map_add, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj,
            Function.surjInv_eq hsurj]), tl_add_right, Submodule.Quotient.mk_add]))
    (fun c c' => AddMonoidHom.ext fun Q => by
      simp only [AddMonoidHom.add_apply, AddMonoidHom.mk'_apply]
      rw [mk_tl_eq_of_lamToAcoef α (l' := Function.surjInv (lamToAcoef_surjective i) c +
          Function.surjInv (lamToAcoef_surjective i) c')
          (by rw [map_add, Function.surjInv_eq (lamToAcoef_surjective i),
            Function.surjInv_eq (lamToAcoef_surjective i),
            Function.surjInv_eq (lamToAcoef_surjective i)]),
        tl_add_left, Submodule.Quotient.mk_add])

/-- **The inverse `M_i → 𝕋/(2^i, t^i)𝕋`.** Kind: definition. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
def finLevInv : Mcoef K S W i (alphaLev i α) →+ (TLam K S W α ⧸ tlamNbhd K S W α i) :=
  TensorProduct.liftAddHom (finLevInvBil α hsurj) (fun r c Q => by
    rw [map_zsmul (finLevInvBil α hsurj) r c, map_zsmul (finLevInvBil α hsurj c) r Q]
    rfl)

/-- `finLevInv ∘ finLev` is the quotient map. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem finLevInv_finLev (x : TLam K S W α) :
    finLevInv α hsurj (finLev α i x) = Submodule.Quotient.mk x := by
  refine tl_induction α (motive := fun x => finLevInv α hsurj (finLev α i x) =
    Submodule.Quotient.mk x) x ?_ (fun l P => ?_) (fun x y hx hy => ?_)
  · rw [map_zero, map_zero, Submodule.Quotient.mk_zero]
  · rw [finLev_tmul]
    refine (TensorProduct.liftAddHom_tmul _ _ _ _).trans ?_
    refine (mk_tl_eq_of_lamToAcoef α (Function.surjInv_eq (lamToAcoef_surjective i) _) _).trans ?_
    exact mk_tl_eq_of_projLev α l (Function.surjInv_eq hsurj _)
  · rw [map_add, map_add, hx, hy, Submodule.Quotient.mk_add]

include hsurj in
/-- **F3: `finLev` is surjective** when `T_2E → E[2^i]` is. Kind: PROVED. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem finLev_surjective : Function.Surjective (finLev (W := W) α i) := by
  intro y
  obtain ⟨y, rfl⟩ := (CoefMod.equiv (Acoef i) (alphaLev i α)
    (TorsS K S W ((2 ^ i : ℕ) : ℤ))).surjective y
  induction y using TensorProduct.inductionOn with
  | tmul c Q =>
    obtain ⟨l, rfl⟩ := lamToAcoef_surjective i c
    obtain ⟨P, rfl⟩ := hsurj Q
    exact ⟨tl α l P, finLev_tmul α i l P⟩
  | add y z hy hz =>
    obtain ⟨x, hx⟩ := hy
    obtain ⟨x', hx'⟩ := hz
    exact ⟨x + x', by rw [map_add, hx, hx', map_add]⟩

include hsurj in
/-- **F3: `ker finLev = (2^i, t^i)𝕋`** when `T_2E → E[2^i]` is onto. Kind: PROVED. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem ker_finLev : LinearMap.ker (finLev α i) = tlamNbhd K S W α i := by
  refine le_antisymm (fun x hx => ?_) (tlamNbhd_le_ker_finLev α i)
  rw [LinearMap.mem_ker] at hx
  rw [← Submodule.Quotient.mk_eq_zero, ← finLevInv_finLev α hsurj x, hx, map_zero]

/-- **F3: `𝕋/(2^i, t^i)𝕋 ≃ M_i`** when `T_2E → E[2^i]` is onto. Kind: definition. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
def finLevEquiv : (TLam K S W α ⧸ tlamNbhd K S W α i) ≃+ Mcoef K S W i (alphaLev i α) where
  toFun := (tlamNbhd K S W α i).liftQ (finLev α i) (tlamNbhd_le_ker_finLev α i)
  invFun := finLevInv α hsurj
  left_inv q := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.liftQ_apply, finLevInv_finLev]
  right_inv y := by
    obtain ⟨x, rfl⟩ := finLev_surjective α hsurj y
    rw [finLevInv_finLev, Submodule.liftQ_apply]
  map_add' := map_add _

/-- `finLevEquiv` on classes. Kind: PROVED. Locator: `diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem finLevEquiv_mk (x : TLam K S W α) :
    finLevEquiv α hsurj (Submodule.Quotient.mk x) = finLev α i x := rfl

/-- **F3: `finLevEquiv` is Galois-equivariant** (on classes). Kind: PROVED. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
theorem finLevEquiv_smul (σ : GKS K S) (x : TLam K S W α) :
    finLevEquiv α hsurj (Submodule.Quotient.mk (σ • x)) =
      σ • finLevEquiv α hsurj (Submodule.Quotient.mk x) := by
  rw [finLevEquiv_mk, finLevEquiv_mk, finLev_smul]

/-- **F3: `finLevEquiv` is `Λ`-semilinear.** Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
theorem finLevEquiv_lam_smul (l : Lambda) (y : TLam K S W α ⧸ tlamNbhd K S W α i) :
    finLevEquiv α hsurj (l • y) = lamToAcoef i l • finLevEquiv α hsurj y :=
  LinearMap.map_smulₛₗ ((tlamNbhd K S W α i).liftQ (finLev α i) (tlamNbhd_le_ker_finLev α i)) l y

end Surj

/-- **F3 under full `2`-power torsion** (`projLev_surjective`). Kind: definition. Locator:
`diophantine_zq.tex`, tex 2723–2727, 2747. -/
def finLevEquivFull [W.IsElliptic] [HasFullTwoTorsion K S W] (i : ℕ) :
    (TLam K S W α ⧸ tlamNbhd K S W α i) ≃+ Mcoef K S W i (alphaLev i α) :=
  finLevEquiv α (projLev_surjective i)

/-! ## F4. Non-vacuity -/

/-- Non-vacuity of F1 at `i = 1`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2723–2727, 2747. -/
example : Function.Surjective (lamToAcoef 1) ∧ RingHom.ker (lamToAcoef 1) = lamIdeal 1 :=
  ⟨lamToAcoef_surjective 1, ker_lamToAcoef 1⟩

/-- Non-vacuity of F2 at `i = 1`, `χ = 1`, `ξ = 1`. Kind: PROVED. Locator: `diophantine_zq.tex`,
tex 2780–2791. -/
example : (Units.map (lamToAcoef 1).toMonoidHom).comp
    (lambdaChar (1 : GKS ℚ Set.univ →* ℤˣ) 1) = alphaChar 1 1 (redZ2 (2 * 1) 1) :=
  units_map_lambdaChar 1 1 1

/-- Non-vacuity of F3 at `i = 1`, `α = 1`, for `E_1 : y² = x(x - 1)(x + 3)` over `ℚ` with `S` all
primes (full `2`-power torsion holds there): the equivalence `𝕋/(2, t)𝕋 ≃ M_1` exists. Kind:
PROVED. Locator: `diophantine_zq.tex`, tex 2723–2727, 2747. -/
example : Nonempty ((TLam ℚ Set.univ (curveEll (1 : ℚ)) 1 ⧸
    tlamNbhd ℚ Set.univ (curveEll (1 : ℚ)) 1 1) ≃+
      Mcoef ℚ Set.univ (curveEll (1 : ℚ)) 1 (alphaLev 1 1)) := by
  have := isElliptic_curveEll (K := ℚ) (one_ne_zero : (1 : ℚ) ≠ 0)
  exact ⟨finLevEquivFull 1 1⟩

end ZInQ.Manuscript.RC.LambdaCoef

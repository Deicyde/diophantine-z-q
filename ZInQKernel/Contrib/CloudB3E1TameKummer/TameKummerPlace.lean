import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalPlace
import ZInQKernel.Contrib.OneProof.RC.Local.TameH2Cup
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LocalCounts
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Decomp

/-!
# The tame comparison at a place of a number field, from the literature alone

Manuscript `diophantine_zq.tex`, tex 3470–3481 (the tame local free model (4.4) at augmentation,
the unramified condition), with the tame coordinates of tex 5026–5037.

`tameLocalModelPrintField_of_prints` reduces the field form `TameLocalModelPrintField` of (4.4) to
two statements: `TameCochainQuasiIso` and the PRINT `IwasawaGenerators`. Here the instance of
`TameCochainQuasiIso` that it consumes (at the completion `K_w` of a number field at a finite place
`w ∤ 2`, field coefficients, inflated from `Gal(K_w^ur/K_w)`, so that inertia acts trivially) is
PROVED from the tree PRINT `MilneADT_I_2_8` alone, and hence `TameLocalModelPrintField` rests on
the two literature statements `MilneADT_I_2_8` and `IwasawaGenerators`:

* `algQp`, `finiteDimensional_qp`: `K_w` is a finite-dimensional `ℚ_p`-algebra for the residue
  characteristic `p = resChar w` of `w`. The prime `w` lies over `p` (`liesOver_resChar`), and the
  degree is `e(w|p) f(w|p)` (the tree's `qpAlg`, `finrank_qp`).
* `kummer_primitive_of_generators`: over a nonarchimedean local field `F`, if `σ ∈ I_F` and a
  pro-`p` subgroup `P ≤ I_F` topologically generate inertia, then for every `n` prime to `p` there
  are `a ∈ F` and an `n`-th root `β` of `a` whose Kummer value `σ(β)/β` is a primitive `n`-th root
  of unity. Take `a` a uniformizer. The tame character `I_F → μ_n` is onto (the tree's
  `tameChar_surjective`). It kills `P`, since a pro-`p` group has `p`-group images under maps with
  open kernel and `n` is prime to `p`. The Kummer value is locally constant, and on `⟨σ⟩ P` it takes
  values in `⟨κ(σ)⟩`, so the same holds on its closure `I_F`. Hence `κ(σ)` generates `μ_n`.
* `quasiIso_inflation_of_milne`: the comparison `tameCochainMap` is a quasi-isomorphism at `w`
  for inflated field coefficients and any Iwasawa triple. This is the tree's
  `quasiIso_tameCochainMap_kummer` at `K_w` with `n = 2^(e+1)`, `2^e` the exponent of `M`.
* `tameLocalModelPrintField_of_milne`: `MilneADT_I_2_8` and `IwasawaGenerators` imply
  `TameLocalModelPrintField` (the proof of `tameLocalModelPrintField_of_prints`, with the
  quasi-isomorphism above in place of `TameCochainQuasiIso`).

No new hypothesis is introduced. Kinds: PROVED (from the PRINTs `MilneADT_I_2_8` and
`IwasawaGenerators`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local.TameKummerPlace

open CategoryTheory NumberField IsDedekindDomain TauCeti ValuativeRel IntermediateField
open ZInQ.Manuscript.RC.Local
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Limits (MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Contrib.RC53Assist.TameBijective
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (urCx eUr resUr frob frobCx frobElt)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr vP qpAlg finrank_qp vP_asIdeal
  one_le_ramificationIdx_mul_inertiaDeg)

/-! ### `K_w` as a finite extension of `ℚ_p` -/

section Instances

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The residue characteristic of `K_w`, as a prime (tex 3470–3480). Kind: definition. -/
def resChar : Nat.Primes := ⟨ringChar 𝓀[w.adicCompletion K], CharP.prime_ringChar _⟩

/-- The residue characteristic lies in `w` (tex 3470–3480). Kind: PROVED. -/
theorem resChar_mem : (((resChar w : ℕ) : ℤ) : 𝓞 K) ∈ w.asIdeal := by
  have h : ringChar 𝓀[w.adicCompletion K] ∣ (resChar w : ℕ) := dvd_rfl
  rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff] at h
  exact_mod_cast h

/-- `w` lies over the residue characteristic (tex 3470–3480). Kind: PROVED. -/
theorem liesOver_resChar : w.asIdeal.LiesOver (vP (resChar w)).asIdeal := by
  rw [vP_asIdeal]
  have : w.asIdeal.IsPrime := w.isPrime
  exact ZInQ.Contrib.CloudB3RC53.GenusOdd.Decomp.liesOver_of_mem (resChar w).2 (resChar_mem w)

/-- `K_w` as an algebra over `ℚ_p`, `p` the residue characteristic, through `ℚ_p ≃ ℚ_(p) → K_w`
(tex 3470–3480). Kind: definition. -/
@[instance_reducible] def algQp : Algebra ℚ_[(resChar w : ℕ)] (w.adicCompletion K) :=
  haveI := liesOver_resChar w
  qpAlg K (resChar w) w

/-- `K_w` is finite-dimensional over `ℚ_p`, of degree `e(w|p) f(w|p)` (tex 3470–3480).
Kind: PROVED. -/
theorem finiteDimensional_qp :
    letI := algQp w
    FiniteDimensional ℚ_[(resChar w : ℕ)] (w.adicCompletion K) := by
  have := liesOver_resChar w
  let _ := algQp w
  have : w.asIdeal.IsPrime := w.isPrime
  have : Module.Free ℚ_[(resChar w : ℕ)] (w.adicCompletion K) := Module.Free.of_divisionRing _ _
  apply Module.finite_of_finrank_pos
  exact lt_of_lt_of_le zero_lt_one
    ((one_le_ramificationIdx_mul_inertiaDeg w.asIdeal).trans (finrank_qp K (resChar w) w).ge)

end Instances

/-! ### Kummer data for a tame inertia generator -/

section Kummer

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The Kummer value `g ↦ g(β)/β` is locally constant: it is constant on the cosets of the open
fixing subgroup of `F(β)` (tex 3470–3487). Kind: PROVED. -/
theorem isLocallyConstant_kummerVal (β : AlgebraicClosure F) :
    IsLocallyConstant (fun g : Field.absoluteGaloisGroup F => kummerVal β (algebraicGaloisEquiv F g)) := by
  have : FiniteDimensional F F⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  have hopen := (IntermediateField.fixingSubgroup_isOpen F⟮β⟯).preimage
    (algebraicGaloisEquiv F).continuous
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun s => x * s) '' ((algebraicGaloisEquiv F) ⁻¹'
    ((F⟮β⟯).fixingSubgroup : Set Gal(AlgebraicClosure F/F))),
    isOpenMap_mul_left x _ hopen, ⟨1, by
      change algebraicGaloisEquiv F 1 ∈ (F⟮β⟯).fixingSubgroup
      rw [map_one]
      exact (F⟮β⟯).fixingSubgroup.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hsβ : algebraicGaloisEquiv F s β = β :=
    hs ⟨β, IntermediateField.mem_adjoin_simple_self F β⟩
  simp only [kummerVal, map_mul, AlgEquiv.mul_apply, hsβ]

/-- **Kummer data for a tame inertia generator** (tex 3470–3487, 5026–5037). Let `σ ∈ I_F` and
let `P ≤ I_F` be a pro-`p` subgroup, `p` the residue characteristic, such that `⟨σ⟩ P` is dense in
`I_F`. Then for `n` prime to `p` there are `a ∈ F` and `β` with `βⁿ = a`, `β ≠ 0`, and
`κ(σ) = σ(β)/β` a primitive `n`-th root of unity (`a` a uniformizer). Kind: PROVED. -/
theorem kummer_primitive_of_generators {n : ℕ} [NeZero n] (hn : n.Coprime (ringChar 𝓀[F]))
    {σ : Field.absoluteGaloisGroup F} {P : Subgroup (Field.absoluteGaloisGroup F)}
    (hσI : σ ∈ inertiaSubgroup F) (hPI : P ≤ inertiaSubgroup F)
    (hPp : TauCeti.IsProP (ringChar 𝓀[F]) P)
    (hcl : (Subgroup.zpowers σ ⊔ P).topologicalClosure = inertiaSubgroup F) :
    ∃ (a : F) (β : AlgebraicClosure F), β ^ n = algebraMap F (AlgebraicClosure F) a ∧ β ≠ 0 ∧
      IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv F σ)) n := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer F
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap F (AlgebraicClosure F) (ϖ : F)) (Nat.pos_of_ne_zero (NeZero.ne n))
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne n)] at hβ
    exact ϖ.ne_zero ((map_eq_zero _).mp hβ.symm)
  have hv : (normalizedValuation F (Units.mk0 (ϖ : F) ϖ.ne_zero)).toAdd = 1 := by
    rw [show Units.mk0 (ϖ : F) ϖ.ne_zero = ϖ from Units.ext rfl,
      (isUniformizer_def ϖ).mp hϖ, toAdd_ofAdd]
  refine ⟨ϖ, β, hβ, hβ0, ?_⟩
  let κ : Field.absoluteGaloisGroup F → AlgebraicClosure F :=
    fun g => kummerVal β (algebraicGaloisEquiv F g)
  have hκ : ∀ g, κ g = kummerVal β (algebraicGaloisEquiv F g) := fun _ => rfl
  have hmul : ∀ g ∈ inertiaSubgroup F, ∀ h, κ (g * h) = κ g * κ h := fun g hg h => by
    rw [hκ, hκ, hκ, map_mul]
    exact kummerVal_mul_of_mem hn hβ hβ0 hg _
  have hpow : ∀ g, κ g ^ n = 1 := fun g => kummerVal_pow hβ hβ0 _
  have hne : ∀ g, κ g ≠ 0 := fun g => kummerVal_ne_zero hβ0 _
  have hκ1 : κ 1 = 1 := by
    rw [hκ, map_one, kummerVal, AlgEquiv.one_apply, div_self hβ0]
  -- `κ` is trivial on the pro-`p` subgroup `P`
  have hP1 : ∀ x ∈ P, κ x = 1 := by
    intro x hx
    let f : P →* rootsOfUnity n (AlgebraicClosure F) :=
      (tameChar hn hβ hβ0).comp (Subgroup.inclusion hPI)
    have hfκ : ∀ y : P, ((f y : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) = κ y.1 :=
      fun y => coe_tameChar hn hβ hβ0 _
    have hker : (f.ker : Set P) = Subtype.val ⁻¹' (κ ⁻¹' {1}) := by
      ext y
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
      rw [← hfκ y]
      constructor
      · intro h
        rw [h]
        rfl
      · intro h
        apply Subtype.ext
        apply Units.ext
        exact h
    have hopen : IsOpen (f.ker : Set P) := by
      rw [hker]
      exact ((isLocallyConstant_kummerVal β) {1}).preimage continuous_subtype_val
    have hpg := hPp.isPGroup_range f hopen
    obtain ⟨k, hk⟩ := hpg ⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩
    have hk' : κ x ^ (ringChar 𝓀[F]) ^ k = 1 := by
      have := congrArg (fun z : f.range =>
        (((z : rootsOfUnity n (AlgebraicClosure F)) : (AlgebraicClosure F)ˣ) :
          AlgebraicClosure F)) hk
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val,
        OneMemClass.coe_one, Units.val_one] at this
      rw [hfκ] at this
      exact this
    have hcop : ((ringChar 𝓀[F]) ^ k).Coprime n := Nat.Coprime.pow_left k hn.symm
    have h1 := pow_gcd_eq_one.mpr ⟨hk', hpow x⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  -- the subgroup of inertia on which `κ` takes values in `⟨κ(σ)⟩`
  set ζ₀ := κ σ with hζ₀
  let T : Subgroup (Field.absoluteGaloisGroup F) :=
    { carrier := {g | g ∈ inertiaSubgroup F ∧ ∃ k : ℕ, κ g = ζ₀ ^ k}
      mul_mem' := by
        rintro a b ⟨ha, i, hi⟩ ⟨hb, j, hj⟩
        exact ⟨mul_mem ha hb, i + j, by rw [hmul a ha, hi, hj, pow_add]⟩
      one_mem' := ⟨one_mem _, 0, by rw [hκ1, pow_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, i, hi⟩
        refine ⟨inv_mem ha, i * (n - 1), ?_⟩
        have h1 : κ a⁻¹ * κ a = 1 := by rw [← hmul _ (inv_mem ha), inv_mul_cancel, hκ1]
        have hn1 : κ a ^ (n - 1) * κ a = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)), hpow]
        have h2 : κ a⁻¹ = κ a ^ (n - 1) := mul_right_cancel₀ (hne a) (h1.trans hn1.symm)
        rw [h2, hi, ← pow_mul] }
  have hle : Subgroup.zpowers σ ⊔ P ≤ T := sup_le
    (Subgroup.zpowers_le.mpr ⟨hσI, 1, (pow_one _).symm⟩)
    (fun x hx => ⟨hPI hx, 0, by rw [hP1 x hx, pow_zero]⟩)
  have hC : IsClosed (κ ⁻¹' Set.range (fun k : ℕ => ζ₀ ^ k)) := by
    rw [← isOpen_compl_iff, ← Set.preimage_compl]
    exact (isLocallyConstant_kummerVal β) _
  have hall : ∀ τ ∈ inertiaSubgroup F, ∃ k : ℕ, κ τ = ζ₀ ^ k := by
    intro τ hτ
    rw [← hcl] at hτ
    have hsub : (((Subgroup.zpowers σ ⊔ P).topologicalClosure : Subgroup _) : Set _) ⊆
        κ ⁻¹' Set.range (fun k : ℕ => ζ₀ ^ k) := by
      rw [Subgroup.topologicalClosure_coe]
      refine closure_minimal (fun g hg => ?_) hC
      obtain ⟨-, k, hk⟩ := hle hg
      exact ⟨k, hk.symm⟩
    obtain ⟨k, hk⟩ := hsub hτ
    exact ⟨k, hk.symm⟩
  -- surjectivity of the tame character
  have : NeZero (n : F) := ⟨natCast_ne_zero_of_coprime_ringChar hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure F) n
  obtain ⟨τ, hτ⟩ := tameChar_surjective hn hβ hβ0 ϖ.ne_zero hv
    ⟨hζ.isUnit (NeZero.ne n) |>.unit, by
      rw [mem_rootsOfUnity]; ext; simp [hζ.pow_eq_one]⟩
  have hτζ : κ τ.1 = ζ := by
    have := congrArg (fun x : rootsOfUnity n (AlgebraicClosure F) =>
      ((x : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)) hτ
    simp only [coe_tameChar, IsUnit.unit_spec] at this
    exact this
  obtain ⟨k, hk⟩ := hall τ.1 τ.2
  rw [hτζ] at hk
  have hord : orderOf ζ₀ = n := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hpow σ)) ?_
    rw [hζ.eq_orderOf, hk]
    exact orderOf_pow_dvd k
  exact hord ▸ IsPrimitiveRoot.orderOf ζ₀

end Kummer

/-! ### The comparison at a finite place, and the tame local model -/

section Place

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The tame comparison at `w ∤ 2` for inflated field coefficients, from Milne**
(tex 3470–3481). For a field `k`, a finite discrete `Gal(K_w^ur/K_w)`-representation `X`, a
surjection `f : X → M` onto a `G_{K_w}`-module with `f (resUr g • x) = g • f x`, `M` of
`2`-power exponent, and an Iwasawa triple `(φ, σ, P)` at `w`, the comparison `tameCochainMap`
(with `Φ = (φ • ·)`, `g = id`) is a quasi-isomorphism, given the PRINT `MilneADT_I_2_8` only. This
is the instance of `TameCochainQuasiIso` consumed by `tameLocalModelPrintField_of_prints`.
Kind: PROVED (from the PRINT). -/
theorem quasiIso_inflation_of_milne (h28 : MilneADT_I_2_8) (h2 : (2 : 𝓞 K) ∉ w.asIdeal)
    (k : Type) [Field k] [TopologicalSpace k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (Gloc K w) M] [SMulCommClass (Gloc K w) k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Gloc K w) M]
    (X : TopRep.{0} k (GUr K w)) [ContinuousSMul (GUr K w) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w) (x : X.V), f (resUr K w g • x) = g • f x)
    (hsurj : Function.Surjective f) {φ σ : Gloc K w} {P : Subgroup (Gloc K w)}
    (hI : IsIwasawaTriple K w φ σ P) (he : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    QuasiIso (GHom.toCC (tameCochainMap (DistribSMul.toLinearMap k M φ) LinearMap.id φ σ
      (Nat.card 𝓀[w.adicCompletion K]) (odd_natCard_residueField h2) (fun _ => rfl)
      (fun m => (smul_eq_self_of_mem_inertia_of_inflation f hf hsurj hI.mem_inertia m).symm)
      (LinearMap.id_comp _) ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm)
      hI.rel)) := by
  obtain ⟨e, he'⟩ := he
  let _ := algQp w
  have := finiteDimensional_qp w
  have hodd : ringChar 𝓀[w.adicCompletion K] ≠ 2 := ringChar_residueField_ne_two h2
  have hpr : (ringChar 𝓀[w.adicCompletion K]).Prime := (resChar w).2
  have : NeZero (2 ^ (e + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : Fact (1 < 2 ^ (e + 1)) := ⟨Nat.one_lt_two_pow (Nat.succ_ne_zero e)⟩
  have hncop : (2 ^ (e + 1)).Coprime (ringChar 𝓀[w.adicCompletion K]) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hpr).mpr (Ne.symm hodd))
  obtain ⟨a, β, hβ, hβ0, hζ⟩ :=
    kummer_primitive_of_generators hncop hI.mem_inertia hI.le_inertia hI.proP hI.closure_eq
  have hItriv : ∀ g ∈ inertiaSubgroup (w.adicCompletion K), ∀ m : M, g • m = m :=
    fun g hg m => smul_eq_self_of_mem_inertia_of_inflation f hf hsurj hg m
  have hnM : ∀ m : M, (2 ^ (e + 1)) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, he' m, smul_zero]
  exact quasiIso_tameCochainMap_kummer (p := (resChar w : ℕ)) h28 hodd X f hf hsurj hncop
    ⟨2 ^ e, by rw [pow_succ', mul_comm]⟩ hβ hβ0 hI.frob hI.mem_inertia hζ hItriv hnM
    (odd_natCard_residueField h2) _ (fun _ => rfl) _ _ _ hI.rel ⟨e, he'⟩

/-- **The tame local model at a place, over a field, from two literature statements**
(tex 3470–3481): the PRINTs `MilneADT_I_2_8` (Milne, *Arithmetic Duality Theorems*, I.2.8) and
`IwasawaGenerators` (Iwasawa 1955; Neukirch–Schmidt–Wingberg 7.5.1–7.5.3) imply
`TameLocalModelPrintField`. The proof is that of `tameLocalModelPrintField_of_prints`, with
`quasiIso_inflation_of_milne` in place of `TameCochainQuasiIso`. Kind: PROVED (from the PRINTs). -/
theorem tameLocalModelPrintField_of_milne (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators) :
    TameLocalModelPrintField := by
  intro K _ _ S k _ _ M _ _ _ _ _ _ _ _ w X _ _ _ f hf hbij hexp q hq hqcard
  have h2 : (2 : 𝓞 K) ∉ w.1.asIdeal := two_not_mem_of_odd_card (hqcard ▸ hq)
  obtain ⟨φ, σ, P, hIw⟩ := hI K w.1 h2
  have hq' := hqcard.trans (natCard_residueField_adicCompletion K w.1).symm
  subst hq'
  have : Finite (ResMod (locMap K S w.1) M) := inferInstanceAs (Finite M)
  have hexp' : ∃ e : ℕ, ∀ m : ResMod (locMap K S w.1) M, 2 ^ e • m = 0 := hexp
  let f' : X.V →ₗ[k] ResMod (locMap K S w.1) M := f
  have hbij' : Function.Bijective f' := hbij
  have hf' : ∀ (g : Gloc K w.1) (x : X.V), f' (resUr K w.1 g • x) = g • f' x := hf
  have hQ := quasiIso_inflation_of_milne h28 h2 k (ResMod (locMap K S w.1) M) X f' hf'
    hbij'.2 hIw hexp'
  obtain ⟨m, -, -⟩ := tameLocalModelAt_of_cochainQuasiIso (eUr K w.1) (resUr K w.1) X
    (G := Gloc K w.1) (M := ResMod (locMap K S w.1) M) f' hbij' hf' _ φ σ _ hq _
    (resUr_of_isArithFrobeniusLift hIw.frob) (resUr_of_mem_inertia hIw.mem_inertia) hIw.rel hQ
  exact ⟨m⟩

end Place

end ZInQ.Manuscript.RC.Local.TameKummerPlace

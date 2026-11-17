import ZInQKernel.Contrib.OneProof.DSCoeffExt

/-! Abstract glue: eigenvalues of operators preserving a spanning `F`-structure are algebraic of
bounded degree, jointly. -/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CoeffField

open Submodule

variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ι : Type*}

/-- `v` has all coordinates `c i v` in `F`. -/
def IsRat (c : ι → V →ₗ[K] K) (v : V) : Prop := ∀ i, c i v ∈ Set.range (algebraMap F K)

section Inner

variable [Module F V] [IsScalarTower F K V]

variable (F) in
/-- The `F`-structure `W = {v | c_i v ∈ F ∀ i}`. -/
def ratPart (c : ι → V →ₗ[K] K) : Submodule F V where
  carrier := {v | IsRat (F := F) c v}
  zero_mem' := fun i => ⟨0, by simp⟩
  add_mem' := by
    rintro a b ha hb i
    obtain ⟨x, hx⟩ := ha i
    obtain ⟨y, hy⟩ := hb i
    exact ⟨x + y, by simp [hx, hy]⟩
  smul_mem' := by
    rintro r a ha i
    obtain ⟨x, hx⟩ := ha i
    refine ⟨r * x, ?_⟩
    rw [← algebraMap_smul K r a, map_smul, map_mul, hx, smul_eq_mul]

theorem exists_finset (c : ι → V →ₗ[K] K) (hc : ∀ v, (∀ i, c i v = 0) → v = 0) :
    ∃ s : Finset (Module.Dual K V), (↑s ⊆ Set.range c) ∧ ∀ v, (∀ φ ∈ s, φ v = 0) → v = 0 := by
  have hfg : (span K (Set.range c)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (fg_span_iff_fg_span_finset_subset _).1 hfg
  refine ⟨s, hs, fun v hv => hc v fun i => ?_⟩
  have hi : c i ∈ span K (s : Set (Module.Dual K V)) := hspan ▸ subset_span ⟨i, rfl⟩
  refine span_induction (p := fun φ _ => φ v = 0) (fun φ hφ => hv φ hφ) (by simp)
    (fun φ ψ _ _ h1 h2 => by simp [h1, h2]) (fun a φ _ h => by simp [h]) hi

theorem finiteDimensional_ratPart (c : ι → V →ₗ[K] K) (hc : ∀ v, (∀ i, c i v = 0) → v = 0) :
    FiniteDimensional F (ratPart F c) := by
  obtain ⟨s, hs, hinj⟩ := exists_finset c hc
  let P : (s → F) →ₗ[F] (s → K) := LinearMap.pi fun φ => (Algebra.linearMap F K).comp (LinearMap.proj φ)
  let E : ratPart F c →ₗ[F] (s → K) :=
    { toFun := fun w φ => (φ : Module.Dual K V) (w : V)
      map_add' := fun a b => by funext φ; simp
      map_smul' := fun r a => by
        funext φ
        simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
        rw [← algebraMap_smul K r (a : V), map_smul, smul_eq_mul, Algebra.smul_def] }
  have hE : ∀ w, E w ∈ LinearMap.range P := by
    intro w
    have h : ∀ φ : s, ∃ x : F, algebraMap F K x = (φ : Module.Dual K V) (w : V) := by
      intro φ
      obtain ⟨i, hi⟩ := hs φ.2
      rw [← hi]
      exact w.2 i
    choose x hx using h
    exact ⟨x, by funext φ; simp [P, E, hx]⟩
  let E' : ratPart F c →ₗ[F] LinearMap.range P := E.codRestrict _ hE
  have hinj' : Function.Injective E' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ∀ φ ∈ s, φ (w : V) = 0 := fun φ hφ => by
      have := congrArg (fun z : LinearMap.range P => (z : s → K) ⟨φ, hφ⟩) hw
      simpa [E', E] using this
    exact Subtype.ext (hinj _ h0)
  exact Module.Finite.of_injective E' hinj'

/-- The stabilizer algebra: operators preserving `W` and having `f` as an eigenvector. -/
def stab (c : ι → V →ₗ[K] K) (f : V) : Subalgebra F (Module.End K V) where
  carrier := {T | (∀ w ∈ ratPart F c, T w ∈ ratPart F c) ∧ ∃ μ : K, T f = μ • f}
  mul_mem' := by
    rintro S T ⟨hS, μ, hμ⟩ ⟨hT, ν, hν⟩
    refine ⟨fun w hw => hS _ (hT w hw), μ * ν, ?_⟩
    rw [Module.End.mul_apply, hν, map_smul, hμ, smul_smul, mul_comm]
  add_mem' := by
    rintro S T ⟨hS, μ, hμ⟩ ⟨hT, ν, hν⟩
    exact ⟨fun w hw => add_mem (hS w hw) (hT w hw), μ + ν, by
      rw [LinearMap.add_apply, hμ, hν, add_smul]⟩
  algebraMap_mem' := by
    intro r
    refine ⟨fun w hw => ?_, algebraMap F K r, ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact (ratPart F c).smul_mem r hw
    · rw [Module.algebraMap_end_apply, algebraMap_smul]

variable (c : ι → V →ₗ[K] K) {f : V}

theorem eigen_exists (T : stab (F := F) c f) : ∃ μ : K, (T : Module.End K V) f = μ • f := T.2.2

/-- The eigenvalue. -/
def lamFun (T : stab (F := F) c f) : K := (eigen_exists c T).choose

theorem lamFun_spec (T : stab (F := F) c f) : (T : Module.End K V) f = lamFun c T • f :=
  (eigen_exists c T).choose_spec

theorem lamFun_eq (hf : f ≠ 0) {T : stab (F := F) c f} {μ : K} (h : (T : Module.End K V) f = μ • f) :
    lamFun c T = μ :=
  smul_left_injective K hf ((lamFun_spec c T).symm.trans h)

/-- The eigencharacter `stab → K`. -/
def lam (hf : f ≠ 0) : stab (F := F) c f →ₐ[F] K where
  toFun := lamFun c
  map_one' := lamFun_eq c hf (by simp)
  map_mul' S T := lamFun_eq c hf (by
    change (S : Module.End K V) ((T : Module.End K V) f) = _
    rw [lamFun_spec c T, map_smul, lamFun_spec c S, smul_smul, mul_comm])
  map_zero' := lamFun_eq c hf (by simp)
  map_add' S T := lamFun_eq c hf (by
    change (S : Module.End K V) f + (T : Module.End K V) f = _
    rw [lamFun_spec c S, lamFun_spec c T, add_smul])
  commutes' r := lamFun_eq c hf (by
    change (algebraMap F (Module.End K V) r) f = _
    rw [Module.algebraMap_end_apply, algebraMap_smul])

theorem finiteDimensional_stab (hc : ∀ v, (∀ i, c i v = 0) → v = 0)
    (hspan : span K (ratPart F c : Set V) = ⊤) : FiniteDimensional F (stab (F := F) c f) := by
  haveI := finiteDimensional_ratPart (F := F) c hc
  let R : stab (F := F) c f →ₗ[F] Module.End F (ratPart F c) :=
    { toFun := fun T => ((T : Module.End K V).restrictScalars F).restrict T.2.1
      map_add' := fun S T => by ext w; rfl
      map_smul' := fun r T => by ext w; rfl }
  refine Module.Finite.of_injective R ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro T hT
  have hT0 : (T : Module.End K V) = 0 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ span K (ratPart F c : Set V) := hspan ▸ mem_top
    refine span_induction (p := fun v _ => (T : Module.End K V) v = (0 : Module.End K V) v)
      (fun w hw => ?_) (by simp) (fun a b _ _ h1 h2 => by simp_all) (fun a b _ h => by simp_all) hv
    have := LinearMap.congr_fun hT ⟨w, hw⟩
    exact congrArg Subtype.val this
  exact Subtype.ext (by simpa using hT0)

theorem finiteDimensional_range_lam (hf : f ≠ 0) (hc : ∀ v, (∀ i, c i v = 0) → v = 0)
    (hspan : span K (ratPart F c : Set V) = ⊤) : FiniteDimensional F (lam (F := F) c hf).range := by
  haveI := finiteDimensional_stab (F := F) (f := f) c hc hspan
  exact Module.Finite.of_surjective (lam (F := F) c hf).rangeRestrict.toLinearMap
    (AlgHom.rangeRestrict_surjective _)

end Inner

/-- **Main abstract glue.** -/
theorem finiteDimensional_adjoin_eigenvalues (c : ι → V →ₗ[K] K)
    (hc : ∀ v, (∀ i, c i v = 0) → v = 0)
    (hspan : span K {v | IsRat (F := F) c v} = ⊤) {f : V} (hf : f ≠ 0) (s : Set K)
    (hs : ∀ μ ∈ s, ∃ T : Module.End K V,
      (∀ v, IsRat (F := F) c v → IsRat (F := F) c (T v)) ∧ T f = μ • f) :
    FiniteDimensional F (Algebra.adjoin F s) := by
  letI : Module F V := Module.compHom V (algebraMap F K)
  haveI : IsScalarTower F K V := ⟨fun a b v => by
    change (a • b) • v = algebraMap F K a • b • v
    rw [Algebra.smul_def, mul_smul]⟩
  have hle : Algebra.adjoin F s ≤ (lam (F := F) c hf).range := by
    rw [Algebra.adjoin_le_iff]
    intro μ hμ
    obtain ⟨T, hT, hTf⟩ := hs μ hμ
    exact ⟨⟨T, fun w hw => hT w hw, μ, hTf⟩, lamFun_eq c hf hTf⟩
  haveI := finiteDimensional_range_lam (F := F) c hf hc hspan
  exact Submodule.finiteDimensional_of_le (show Subalgebra.toSubmodule (Algebra.adjoin F s) ≤
    Subalgebra.toSubmodule (lam (F := F) c hf).range from hle)

end CoeffField

/-! ## Specialization to `S_k(N, χ)` -/

namespace CoeffField

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The `n`-th `q`-expansion coefficient as a linear functional on `S_k(N, χ)`. -/
def coeffL (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) : cuspFormCharSpace k χ →ₗ[ℂ] ℂ where
  toFun F := (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n
  map_add' F G := by
    rw [Submodule.coe_add, FunLike.coe_add,
      ModularForm.qExpansion_add one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N), map_add]
  map_smul' a F := by
    rw [Submodule.coe_smul, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
      PowerSeries.coeff_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]

theorem coeffL_apply (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) (F : cuspFormCharSpace k χ) :
    coeffL χ n F = (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n := rfl

theorem eq_zero_of_coeffL (χ : (ZMod N)ˣ →* ℂˣ) (F : cuspFormCharSpace k χ)
    (h : ∀ n, coeffL χ n F = 0) : F = 0 := by
  have hq : qExpansion 1 ((F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 :=
    PowerSeries.ext fun n ↦ by simpa [coeffL_apply] using h n
  have h0 : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := by
    refine CuspForm.toModularFormₗ_injective ?_
    rw [CuspForm.toModularFormₗ_eq_coe, map_zero]
    exact (ModularForm.qExpansion_eq_zero_iff one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _) _).mp hq
  exact Subtype.ext h0

/-- `ℚ(χ)`: the field generated over `ℚ` by the values of `χ`. -/
def charField (χ : (ZMod N)ˣ →* ℂˣ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range fun u => ((χ u : ℂˣ) : ℂ))

theorem charField_finiteDimensional (χ : (ZMod N)ˣ →* ℂˣ) : FiniteDimensional ℚ (charField χ) := by
  unfold charField
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro _ ⟨u, rfl⟩
  refine (IsIntegral.of_pow (Nat.pos_of_ne_zero (orderOf_pos u).ne') ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  exact isIntegral_one

theorem ofUnitHom_mem_charField (χ : (ZMod N)ˣ →* ℂˣ) (d : ℕ) :
    (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) d ∈ charField χ := by
  by_cases h : IsUnit (d : ZMod N)
  · rw [← h.unit_spec, MulChar.ofUnitHom_coe]
    exact IntermediateField.subset_adjoin ℚ _ ⟨h.unit, rfl⟩
  · rw [MulChar.map_nonunit _ h]
    exact zero_mem _

/-- The Hecke operators `T_n` preserve `ℚ(χ)`-rationality of `q`-expansions on `S_k(N, χ)`. -/
theorem hecke_coeff_mem (χ : (ZMod N)ˣ →* ℂˣ) {n : ℕ} (hn : n ≠ 0) (F : cuspFormCharSpace k χ)
    (hF : ∀ m, coeffL χ m F ∈ charField χ) (m : ℕ) :
    coeffL χ m (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) F) ∈ charField χ := by
  rw [coeffL_apply, qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 hn]
  refine sum_mem fun d _ => mul_mem (mul_mem (ofUnitHom_mem_charField χ d)
    (zpow_mem (natCast_mem _ d) _)) (hF _)

/-- **LEAF (rational structure of `S_k(N, χ)`).** For `k ≥ 2`, the space `S_k(Γ₁(N), χ)` of cusp forms of
weight `k` on `Γ₁(N)` with nebentypus `χ` (Tau Ceti's `cuspFormCharSpace k χ`, the joint eigenspace of the
diamond operators) is spanned over `ℂ` by forms whose `q`-expansion coefficients at `∞` all lie in
`ℚ(χ)`. -/
def CharSpaceRationalSpan : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ), 2 ≤ k →
    Submodule.span ℂ {F : cuspFormCharSpace k χ | ∀ n : ℕ,
      (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n ∈ charField χ} = ⊤

theorem isRat_iff (χ : (ZMod N)ˣ →* ℂˣ) (F : cuspFormCharSpace k χ) :
    IsRat (F := charField χ) (coeffL χ) F ↔ ∀ n, coeffL χ n F ∈ charField χ := by
  refine forall_congr' fun n => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

/-- For a full eigenform `F` with `a₁ = 1` in `S_k(N, χ)`, the coefficients generate a finite-dimensional
`ℚ(χ)`-algebra. -/
theorem finiteDimensional_adjoin_coeff (hR : CharSpaceRationalSpan) (F : Eigenform N k) (hk : 2 ≤ k) :
    FiniteDimensional (charField F.χ)
      (Algebra.adjoin (charField F.χ) (Set.range fun n : ℕ+ => F.eigenvalue n)) := by
  set χ := F.χ
  have hspan : Submodule.span ℂ {v | IsRat (F := charField χ) (coeffL (k := k) χ) v} = ⊤ := by
    have := hR N k χ hk
    convert this using 3
    ext v
    rw [isRat_iff]
    rfl
  have hf : (⟨F.toCuspForm, F.mem_charSpace⟩ : cuspFormCharSpace k χ) ≠ 0 := fun h =>
    F.ne_zero (congrArg Subtype.val h)
  refine finiteDimensional_adjoin_eigenvalues (coeffL χ) (eq_zero_of_coeffL χ) hspan hf _ ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n), fun v hv => ?_, F.isEigen n⟩
  rw [isRat_iff] at hv ⊢
  exact hecke_coeff_mem χ n.ne_zero v hv

/-- **`EigenformCoeffFieldFinite` from the rational structure of `S_k(N, χ)`.** -/
theorem eigenformCoeffFieldFinite_of (hR : CharSpaceRationalSpan) :
    DSCoeffExt.EigenformCoeffFieldFinite := by
  intro N _ k χ f hk hf
  obtain ⟨F, rfl, -, h1⟩ := hf
  set L := charField F.χ
  haveI : FiniteDimensional ℚ L := charField_finiteDimensional F.χ
  set A := Algebra.adjoin L (Set.range fun n : ℕ+ => F.eigenvalue n) with hAdef
  haveI hA : FiniteDimensional L A := finiteDimensional_adjoin_coeff hR F hk
  have hmem : ∀ n, ZInQ.Contrib.G9.PkgI4.coeff F.toCuspForm n ∈ A := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : ZInQ.Contrib.G9.PkgI4.coeff F.toCuspForm 0 = 0 := T25.coeff_zero _
      rw [this]
      exact zero_mem A
    · have e : ZInQ.Contrib.G9.PkgI4.coeff F.toCuspForm n = F.eigenvalue ⟨n, hn⟩ :=
        F.qExpansion_coeff_eq_eigenvalue h1 ⟨n, hn⟩
      rw [e]
      exact Algebra.subset_adjoin ⟨⟨n, hn⟩, rfl⟩
  haveI : Module.Finite ℚ A := Module.Finite.trans L A
  have hint : ∀ n, IsIntegral ℚ (ZInQ.Contrib.G9.PkgI4.coeff F.toCuspForm n) := by
    intro n
    have hL : IsIntegral L (ZInQ.Contrib.G9.PkgI4.coeff F.toCuspForm n) :=
      (Algebra.IsIntegral.isIntegral (R := L) (⟨_, hmem n⟩ : A)).map A.val
    exact isIntegral_trans _ hL
  set B := Algebra.adjoin ℚ (Set.range (ZInQ.Contrib.G9.PkgI4.coeff F.toCuspForm))
  have hBA : ∀ x ∈ B, x ∈ A := by
    intro x hx
    refine Algebra.adjoin_induction (fun y hy => ?_) (fun r => ?_) (fun a b _ _ ha hb => add_mem ha hb)
      (fun a b _ _ ha hb => mul_mem ha hb) hx
    · obtain ⟨n, rfl⟩ := hy
      exact hmem n
    · rw [IsScalarTower.algebraMap_apply ℚ L ℂ]
      exact A.algebraMap_mem _
  let iB : B →ₗ[ℚ] A :=
    { toFun := fun x => ⟨x, hBA x x.2⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp) }
  haveI : Module.Finite ℚ B := Module.Finite.of_injective iB (fun x y h => Subtype.ext
    (congrArg (fun z : A => (z : ℂ)) h))
  have hKB : (DSCoeffExt.coeffField F.toCuspForm).toSubalgebra = B :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x ⟨n, hn⟩ => hn ▸ (hint n).isAlgebraic)
  let iK : DSCoeffExt.coeffField F.toCuspForm →ₗ[ℚ] B :=
    { toFun := fun x => ⟨x, by rw [← hKB]; exact x.2⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp) }
  exact Module.Finite.of_injective iK (fun x y h => Subtype.ext (congrArg (fun z : B => (z : ℂ)) h))

/-! ## The rational structure of `S_k(N, χ)` from the `Γ₁(N)`-level statements -/

/-- The `n`-th coefficient on `S_k(Γ₁(N))` as a linear functional. -/
def coeffG (n : ℕ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ℂ where
  toFun g := (qExpansion 1 g).coeff n
  map_add' F G := by
    rw [FunLike.coe_add,
      ModularForm.qExpansion_add one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N), map_add]
  map_smul' a F := by
    rw [FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
      PowerSeries.coeff_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]

theorem coeffG_apply (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    coeffG n g = (qExpansion 1 g).coeff n := rfl

/-- **LEAF (Shimura's rational basis of `S_k(Γ₁(N))`).** For `k ≥ 2`, `S_k(Γ₁(N))` is spanned over `ℂ` by
cusp forms whose `q`-expansion coefficients at `∞` are all rational. -/
def Gamma1RationalSpan : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ), 2 ≤ k →
    Submodule.span ℂ {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = q} = ⊤

/-- **LEAF (the diamond operators are defined over `ℚ`).** For `k ≥ 2` and `d ∈ (ℤ/Nℤ)ˣ`, the diamond
operator `⟨d⟩` (slash by any `γ ∈ Γ₀(N)` with lower-right entry `≡ d`, Tau Ceti's `diamondOpCusp`) maps a cusp
form on `Γ₁(N)` with rational `q`-expansion to one with rational `q`-expansion. -/
def DiamondPreservesRational : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), 2 ≤ k →
    (∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = q) →
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 (diamondOpCusp k d g)).coeff n = q

/-- The (unnormalized) projector `Σ_d χ(d)⁻¹ ⟨d⟩` onto `S_k(N, χ)`. -/
def proj (χ : (ZMod N)ˣ →* ℂˣ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  ∑ d : (ZMod N)ˣ, ((χ d⁻¹ : ℂˣ) : ℂ) • diamondOpCusp k d

theorem proj_apply (χ : (ZMod N)ˣ →* ℂˣ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    proj χ g = ∑ d : (ZMod N)ˣ, ((χ d⁻¹ : ℂˣ) : ℂ) • diamondOpCusp k d g := by
  simp [proj, LinearMap.sum_apply]

theorem proj_mem (χ : (ZMod N)ˣ →* ℂˣ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    proj χ g ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff]
  intro e
  rw [proj_apply, map_sum, Finset.smul_sum]
  simp only [map_smul, diamondOpCuspHom_apply]
  refine Fintype.sum_equiv (Equiv.mulLeft e) _ _ (fun d => ?_)
  rw [Equiv.coe_mulLeft, diamondOpCusp_mul, LinearMap.comp_apply, smul_smul, ← Units.val_mul,
    ← map_mul]
  congr 3
  group
  simp only [zpow_neg_one]
  rw [mul_comm e, mul_inv_cancel_right]

theorem proj_of_mem (χ : (ZMod N)ˣ →* ℂˣ) {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ cuspFormCharSpace k χ) :
    proj χ F = (Fintype.card (ZMod N)ˣ : ℂ) • F := by
  rw [mem_cuspFormCharSpace_iff] at hF
  rw [proj_apply]
  have : ∀ d : (ZMod N)ˣ, ((χ d⁻¹ : ℂˣ) : ℂ) • diamondOpCusp k d F = F := by
    intro d
    rw [← diamondOpCuspHom_apply, hF d, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel,
      map_one, Units.val_one, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

theorem proj_coeff_mem (hB : DiamondPreservesRational) (χ : (ZMod N)ˣ →* ℂˣ) (hk : 2 ≤ k)
    {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hg : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = q)
    (n : ℕ) : (qExpansion 1 (proj χ g)).coeff n ∈ charField χ := by
  rw [← coeffG_apply, proj_apply, map_sum]
  refine sum_mem fun d _ => ?_
  rw [map_smul, smul_eq_mul]
  refine mul_mem (IntermediateField.subset_adjoin ℚ _ ⟨d⁻¹, rfl⟩) ?_
  obtain ⟨q, hq⟩ := hB N k d g hk hg n
  rw [coeffG_apply, hq]
  exact SubfieldClass.ratCast_mem _ q

/-- **`CharSpaceRationalSpan` from the two `Γ₁(N)`-level leaves.** -/
theorem charSpaceRationalSpan_of (hA : Gamma1RationalSpan) (hB : DiamondPreservesRational) :
    CharSpaceRationalSpan := by
  intro N _ k χ hk
  rw [eq_top_iff]
  rintro F -
  set R := {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k | ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = q}
  set X := {F : cuspFormCharSpace k χ | ∀ n : ℕ,
      (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n ∈ charField χ}
  let P' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] cuspFormCharSpace k χ :=
    (proj χ).codRestrict _ (proj_mem χ)
  have hR : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ Submodule.span ℂ R := by
    rw [hA N k hk]; exact Submodule.mem_top
  have hPX : P' '' R ⊆ X := by
    rintro _ ⟨g, hg, rfl⟩ n
    exact proj_coeff_mem hB χ hk hg n
  have h1 : P' F ∈ Submodule.span ℂ X := by
    have hmap := Submodule.mem_map_of_mem (f := P') hR
    rw [Submodule.map_span] at hmap
    exact Submodule.span_mono hPX hmap
  have h2 : P' F = (Fintype.card (ZMod N)ˣ : ℂ) • F := Subtype.ext (proj_of_mem χ F.2)
  have hc : (Fintype.card (ZMod N)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have : F = ((Fintype.card (ZMod N)ˣ : ℂ))⁻¹ • P' F := by
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ h1

/-- **`EigenformCoeffFieldFinite` from the two `Γ₁(N)`-level leaves.** -/
theorem eigenformCoeffFieldFinite_of_gamma1 (hA : Gamma1RationalSpan) (hB : DiamondPreservesRational) :
    DSCoeffExt.EigenformCoeffFieldFinite :=
  eigenformCoeffFieldFinite_of (charSpaceRationalSpan_of hA hB)

end CoeffField

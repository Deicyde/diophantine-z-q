import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.SmoothDescent
/-!
# Descent of the vanishing of `H1Cotangent` along etale faithfully flat maps

Target: `H1CotangentDescentFiniteEtale` (defined in `Y3SmoothDescent`).

Printed proof. For `R -> S -> T` with `S -> T` etale and faithfully flat:
More on Algebra, Lemma 15.34.6 (Stacks Tag 07D4) gives injectivity of
`T ⊗[S] H1(L_{S/R}) -> H1(L_{T/R})` (flatness of `S -> T` identifies `H1(NL_{S/R} ⊗ T)` with
`T ⊗[S] H1(L_{S/R})`, Stacks Tag 00S2); so `H1(T/R) = 0` forces `T ⊗[S] H1(S/R) = 0`, hence
`H1(S/R) = 0` by faithful flatness (Stacks Tag 00HP). Finiteness of `S -> T` is not used.

What is proved here.
* `h1CotangentDescentFiniteEtale_of_standardEtale`: the target follows from the standard etale
  case `H1DescentStandardEtale` of the vanishing statement. The reduction is complete:
  - etale implies locally standard etale on `T` (`Algebra.IsEtaleAt.exists_isStandardEtale`,
    Stacks Tag 00UE);
  - `H1(T_s/R) = T_s ⊗[T] H1(T/R)` (`Algebra.tensorH1CotangentOfIsLocalization`), so it vanishes;
  - the standard etale case gives `T_s ⊗[S] H1(S/R) = 0`, that is
    `T_s ⊗[T] (T ⊗[S] H1(S/R)) = 0` (`cancelBaseChange`);
  - a `T`-module whose base change to some `T_s` with `s ∉ Q` vanishes, for every prime `Q`,
    is zero (`h1Descent_subsingleton_of_local`);
  - faithful flatness (`Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right`).
* The standard etale case follows from either of two stronger statements, the injectivity form
  `H1TensorInjectiveStandardEtale` (the standard etale case of Tag 07D4) or the existence of a
  linear equivalence `H1TensorEquivStandardEtale`; no naturality of the equivalence is needed.
* `h1Descent_liftBaseChange_injective_of_isLocalization`: the injectivity holds for
  localizations (this is in Mathlib).

What is not proved: the standard etale case `H1DescentStandardEtale` itself. Mathlib has the
three term flat Jacobi-Zariski sequence `T ⊗[S] H1(S/R) -> H1(T/R) -> H1(T/S)`, exact in the
middle (`Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`), but no injectivity on the left
for etale `S -> T`; the extension level comparison
`Algebra.Extension.tensorH1CotangentOfFormallyEtale` needs an etale lift `P -> Q` of `S -> T`
to a presentation `P` of `S`, with `J ≃ Q ⊗[P] I`, which Mathlib does not construct.
-/

set_option autoImplicit false

noncomputable section

namespace Y3Buzzard.SourceDescent

/-! ## The remaining gap and its stronger forms -/

/-- **Remaining gap.** Vanishing of `H1Cotangent` descends in tensor form along a standard etale
map: if `S -> T` is standard etale and `H1(L_{T/R}) = 0` then `T ⊗[S] H1(L_{S/R}) = 0`.

Printed source: the standard etale case of More on Algebra, Lemma 15.34.6 (Stacks Tag 07D4),
together with Stacks Tag 00S2 for flat base change of `H1` of the naive cotangent complex. -/
def H1DescentStandardEtale : Prop :=
  ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T],
    Algebra.IsStandardEtale S T → Subsingleton (Algebra.H1Cotangent R T) →
      Subsingleton (TensorProduct S T (Algebra.H1Cotangent R S))

/-- Injectivity form of the gap: for `S -> T` standard etale, the comparison map
`T ⊗[S] H1(L_{S/R}) -> H1(L_{T/R})` is injective (standard etale case of Stacks Tag 07D4). -/
def H1TensorInjectiveStandardEtale : Prop :=
  ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T],
    Algebra.IsStandardEtale S T →
      Function.Injective (LinearMap.liftBaseChange T (Algebra.H1Cotangent.map R R S T))

/-- Equivalence form of the gap: for `S -> T` standard etale, `T ⊗[S] H1(L_{S/R})` and
`H1(L_{T/R})` are linearly equivalent (any equivalence suffices). -/
def H1TensorEquivStandardEtale : Prop :=
  ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T],
    Algebra.IsStandardEtale S T →
      Nonempty (TensorProduct S T (Algebra.H1Cotangent R S) ≃ₗ[T] Algebra.H1Cotangent R T)

theorem h1DescentStandardEtale_of_injective (h : H1TensorInjectiveStandardEtale) :
    H1DescentStandardEtale := by
  intro R S T _ _ _ _ _ _ _ hstd hT
  haveI : Subsingleton (Algebra.H1Cotangent R T) := hT
  exact (h R S T hstd).subsingleton

theorem h1DescentStandardEtale_of_equiv (h : H1TensorEquivStandardEtale) :
    H1DescentStandardEtale := by
  intro R S T _ _ _ _ _ _ _ hstd hT
  haveI : Subsingleton (Algebra.H1Cotangent R T) := hT
  obtain ⟨e⟩ := h R S T hstd
  exact e.injective.subsingleton

/-! ## Auxiliary lemmas -/

/-- A tensor product with a trivial right factor is trivial. -/
theorem h1Descent_subsingleton_tensorProduct_right (A M N : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Subsingleton N] :
    Subsingleton (TensorProduct A M N) := by
  have hz : ∀ z : TensorProduct A M N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Scalar tower `R -> S -> U` from the towers `R -> S -> T`, `R -> T -> U`, `S -> T -> U`.
Used for `U = Localization.Away s` with its canonical algebra structures. -/
theorem h1Descent_isScalarTower {R S T U : Type} [CommRing R] [CommRing S] [CommRing T]
    [CommRing U] [Algebra R S] [Algebra R T] [Algebra S T] [Algebra T U] [Algebra R U]
    [Algebra S U] [IsScalarTower R S T] [IsScalarTower R T U] [IsScalarTower S T U] :
    IsScalarTower R S U :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r =>
    (IsScalarTower.algebraMap_apply R T U r).trans
      ((congrArg (algebraMap T U) (IsScalarTower.algebraMap_apply R S T r)).trans
        (IsScalarTower.algebraMap_apply S T U (algebraMap R S r)).symm))

/-- Local to global for triviality: if for every prime `Q` of `T` there is `s ∉ Q` such that
`T_s ⊗[T] M` is trivial, then `M` is trivial. -/
theorem h1Descent_subsingleton_of_local (T M : Type) [CommRing T] [AddCommGroup M] [Module T M]
    (h : ∀ Q : Ideal T, Q.IsPrime → ∃ s : T, s ∉ Q ∧
      Subsingleton (TensorProduct T (Localization.Away s) M)) :
    Subsingleton M := by
  have hz : ∀ m : M, m = 0 := by
    intro m
    by_contra hm
    -- the annihilator of `m` is a proper ideal
    have hne : LinearMap.ker (LinearMap.toSpanSingleton T M m) ≠ ⊤ := by
      intro htop
      apply hm
      have h1 : (1 : T) ∈ LinearMap.ker (LinearMap.toSpanSingleton T M m) := by
        rw [htop]
        exact Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
      exact h1
    obtain ⟨Q, hQmax, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsQ, hsub⟩ := h Q hQmax.isPrime
    -- `M -> T_s ⊗[T] M` is a localization of modules at the powers of `s`
    haveI hloc : IsLocalizedModule (Submonoid.powers s)
        (TensorProduct.mk T (Localization.Away s) M 1) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers s) (Localization.Away s)
        (TensorProduct.mk T (Localization.Away s) M 1)).mpr
        (TensorProduct.isBaseChange T M (Localization.Away s))
    have heq : TensorProduct.mk T (Localization.Away s) M 1 m =
        TensorProduct.mk T (Localization.Away s) M 1 0 :=
      @Subsingleton.elim _ hsub _ _
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers s)
      (f := TensorProduct.mk T (Localization.Away s) M 1) heq
    have hc' : (c : T) • m = (c : T) • (0 : M) := hc
    have hcm : (c : T) • m = 0 := hc'.trans (smul_zero (c : T))
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : T) s).mp c.2
    have hpow : s ^ n ∈ LinearMap.ker (LinearMap.toSpanSingleton T M m) := by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, hn]
      exact hcm
    exact hsQ (hQmax.isPrime.mem_of_pow_mem n (hle hpow))
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The localization case of the injectivity (Mathlib). -/
theorem h1Descent_liftBaseChange_injective_of_isLocalization (R S T : Type) [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid S) [IsLocalization M T] :
    Function.Injective (LinearMap.liftBaseChange T (Algebra.H1Cotangent.map R R S T)) := by
  rw [← Algebra.tensorH1CotangentOfIsLocalization_toLinearMap R T M]
  exact (Algebra.tensorH1CotangentOfIsLocalization R T M).injective

/-! ## The reduction -/

/-- **Main reduction.** The target `H1CotangentDescentFiniteEtale` follows from the standard
etale case `H1DescentStandardEtale`. -/
theorem h1CotangentDescentFiniteEtale_of_standardEtale (hstd : H1DescentStandardEtale) :
    H1CotangentDescentFiniteEtale := by
  intro R S T _ _ _ _ _ _ _ hEt _ hFF hT
  haveI : Algebra.Etale S T := hEt
  haveI : Module.FaithfullyFlat S T := hFF
  haveI : Subsingleton (Algebra.H1Cotangent R T) := hT
  -- Step 1: `T ⊗[S] H1(S/R)` is trivial, checked locally on `T`.
  have hM : Subsingleton (TensorProduct S T (Algebra.H1Cotangent R S)) := by
    refine h1Descent_subsingleton_of_local T (TensorProduct S T (Algebra.H1Cotangent R S)) ?_
    intro Q hQ
    haveI : Q.IsPrime := hQ
    haveI : Algebra.FormallyEtale T (Localization.AtPrime Q) :=
      Algebra.FormallyEtale.of_isLocalization Q.primeCompl
    haveI : Algebra.FormallyEtale S (Localization.AtPrime Q) :=
      Algebra.FormallyEtale.comp S T (Localization.AtPrime Q)
    haveI : Algebra.IsEtaleAt S Q := ‹Algebra.FormallyEtale S (Localization.AtPrime Q)›
    haveI : Algebra.FinitePresentation S T := inferInstance
    -- a standard etale neighbourhood `T_s` of `Q`
    obtain ⟨s, hsQ, hstdS⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
    refine ⟨s, hsQ, ?_⟩
    haveI : Algebra.IsStandardEtale S (Localization.Away s) := hstdS
    haveI : IsScalarTower R S (Localization.Away s) := h1Descent_isScalarTower (T := T)
    -- `H1(T_s/R) = T_s ⊗[T] H1(T/R) = 0`
    haveI : Subsingleton (TensorProduct T (Localization.Away s) (Algebra.H1Cotangent R T)) :=
      h1Descent_subsingleton_tensorProduct_right T (Localization.Away s)
        (Algebra.H1Cotangent R T)
    haveI : Subsingleton (Algebra.H1Cotangent R (Localization.Away s)) :=
      (Algebra.tensorH1CotangentOfIsLocalization R (Localization.Away s)
        (Submonoid.powers s)).symm.injective.subsingleton
    -- the standard etale case: `T_s ⊗[S] H1(S/R) = 0`
    haveI : Subsingleton (TensorProduct S (Localization.Away s) (Algebra.H1Cotangent R S)) :=
      hstd R S (Localization.Away s) hstdS inferInstance
    -- `T_s ⊗[T] (T ⊗[S] H1(S/R)) ≃ T_s ⊗[S] H1(S/R)`
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange S T (Localization.Away s)
      (Localization.Away s) (Algebra.H1Cotangent R S)).injective.subsingleton
  -- Step 2: faithful flatness.
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right S T).mp hM

/-- The target from the injectivity form of the gap (standard etale case of Tag 07D4). -/
theorem h1CotangentDescentFiniteEtale_of_injective (h : H1TensorInjectiveStandardEtale) :
    H1CotangentDescentFiniteEtale :=
  h1CotangentDescentFiniteEtale_of_standardEtale (h1DescentStandardEtale_of_injective h)

/-- The target from the equivalence form of the gap. -/
theorem h1CotangentDescentFiniteEtale_of_equiv (h : H1TensorEquivStandardEtale) :
    H1CotangentDescentFiniteEtale :=
  h1CotangentDescentFiniteEtale_of_standardEtale (h1DescentStandardEtale_of_equiv h)

end Y3Buzzard.SourceDescent

end

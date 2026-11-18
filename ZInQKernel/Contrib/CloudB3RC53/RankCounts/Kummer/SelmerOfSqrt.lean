import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.Statements
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.Radical

/-!
# `kummer`, stage `⊆`: a square root in `K_S` gives a Selmer class (tex 4482–4492)

`selmerOfSqrtMem_proof : SelmerOfSqrtMem`: if `x ∈ K_S = unramifiedOutside K S` and `x² = a ∈ K^×`,
then the class of `a` lies in the Selmer group `K(S,2)` (`v(a)` even for every `v ∉ S`).

Proof: `x` lies in a finite join `J` of finite normal subextensions `L_i` unramified outside `S`;
`J` is a finite Galois number field; inside `J` the restrictions `E_i` of the `L_i` are unramified
outside `S` (`isUnramifiedIn_of_isUnramifiedOutside`: the `𝒪_K`-algebra isomorphism
`𝒪_{E_i} ≅ integralClosure 𝒪_K L_i` preserves ramification indices); by Tau Ceti's
`Ideal.isUnramifiedIn_iSup_iff` (inertia groups in the Galois extension `J/K`) their join
`⨆ E_i = ⊤` is unramified outside `S`; then Tau Ceti's `selmerGroup.mk_mem_of_pow_eq` (at a prime
of ramification index one, `v(a) = w(x)²`) gives `a ∈ K(S,2)`. Kinds: PROVED.
-/

open NumberField IsDedekindDomain
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS
variable (K : Type) [Field K] [NumberField K]

/-- A finite extension of a number field is a number field. -/
theorem numberField_of_finite (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] :
    NumberField L :=
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  { to_charZero := inferInstance
    to_finiteDimensional := Module.Finite.trans K L }

variable {K}

/-- Transport of unramifiedness from `integralClosure (𝓞 K) L` to `𝓞 E` for `L ≃ₐ[K] E`: the
`𝓞 K`-algebra isomorphism of the integral closures preserves ramification indices. PROVED. -/
theorem isUnramifiedIn_of_isUnramifiedOutside {S : Set (HeightOneSpectrum (𝓞 K))}
    {L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K L]
    (hL : IsUnramifiedOutside K S L) (E : Type) [Field E] [Algebra K E] [NumberField E]
    (f : L ≃ₐ[K] E) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := by
  let φ1 : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] integralClosure (𝓞 K) E :=
    (f.restrictScalars (𝓞 K)).mapIntegralClosure
  let φ2 : integralClosure (𝓞 K) E ≃ₐ[𝓞 K] 𝓞 E :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) E) E (𝓞 E)
  let φ : 𝓞 E ≃ₐ[𝓞 K] integralClosure (𝓞 K) L := (φ1.trans φ2).symm
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P hP hPv
  have hDed : IsDedekindDomain (integralClosure (𝓞 K) L) :=
    integralClosure.isDedekindDomain (𝓞 K) K L
  set Q : Ideal (integralClosure (𝓞 K) L) := P.map φ with hQdef
  have hQ : Q.IsPrime := Ideal.map_isPrime_of_equiv φ
  have hQv : Q.LiesOver v.asIdeal := by
    constructor
    rw [hQdef, Ideal.under, hPv.over]
    ext a
    simp only [Ideal.mem_comap]
    constructor
    · intro ha
      have : φ (algebraMap (𝓞 K) (𝓞 E) a) ∈ Ideal.map φ P := Ideal.mem_map_of_mem _ ha
      rwa [AlgEquiv.commutes] at this
    · intro ha
      have h2 : φ.symm (algebraMap (𝓞 K) (integralClosure (𝓞 K) L) a) ∈
          Ideal.map φ.symm (Ideal.map φ P) := Ideal.mem_map_of_mem _ ha
      rw [AlgEquiv.commutes] at h2
      have h3 : Ideal.map φ.symm (Ideal.map φ P) = P :=
        Ideal.map_of_equiv (I := P) (φ : 𝓞 E ≃+* integralClosure (𝓞 K) L)
      rwa [h3] at h2
  have h1 := hL v hv Q hQ hQv
  have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
  have hmapE : v.asIdeal.map (algebraMap (𝓞 K) (𝓞 E)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hv0
  have hmapL : v.asIdeal.map (algebraMap (𝓞 K) (integralClosure (𝓞 K) L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hv0
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx' (p := v.asIdeal) (q := P) hmapE,
    ← Ideal.ramificationIdx'_map_eq v.asIdeal P φ,
    Ideal.ramificationIdx'_eq_ramificationIdx' (p := v.asIdeal) (q := Q) hmapL]
  exact h1

/-- **`kummer`, stage `⊆`** (tex 4482–4492): a square root of `a` in `K_S` makes the class of `a`
a Selmer class. PROVED. -/
theorem selmerOfSqrtMem_proof : SelmerOfSqrtMem := by
  intro K _ _ S a x hx hxS
  rw [unramifiedOutside_eq_iSup_subtype] at hxS
  obtain ⟨s, hs⟩ := IntermediateField.exists_finset_of_mem_iSup hxS
  rw [iSup_subtype'] at hs
  set ι := {i // i ∈ s}
  let t : ι → IntermediateField K (AlgebraicClosure K) := fun i => (i.1 : IntermediateField K _)
  set J : IntermediateField K (AlgebraicClosure K) := ⨆ i, t i with hJ
  have hfd : ∀ i, FiniteDimensional K (t i) := fun i => i.1.2.1
  have hnorm : ∀ i, Normal K (t i) := fun i => i.1.2.2.1
  have : FiniteDimensional K J := IntermediateField.finiteDimensional_iSup_of_finite
  have : Normal K J := IntermediateField.normal_iSup K _ _
  let _ : NumberField J := numberField_of_finite K J
  have : IsGalois K J := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  let E : ι → IntermediateField K J := fun i => IntermediateField.restrict (le_iSup t i)
  have htop : (⨆ i, E i) = ⊤ := by
    apply IntermediateField.lift_injective J
    rw [IntermediateField.lift_top, IntermediateField.lift, IntermediateField.map_iSup]
    exact iSup_congr fun i => IntermediateField.lift_restrict (le_iSup t i)
  set F := ⨆ i, E i with hF
  have hxF : (⟨x, hs⟩ : J) ∈ F := by rw [htop]; trivial
  let α : F := ⟨⟨x, hs⟩, hxF⟩
  have hα : α ^ 2 = algebraMap K F (a : K) := by
    apply Subtype.ext; apply Subtype.ext
    simpa using hx
  have hun : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 F) v.asIdeal := by
    intro v hv
    rw [hF, Ideal.isUnramifiedIn_iSup_iff]
    intro i
    have := hfd i
    exact isUnramifiedIn_of_isUnramifiedOutside i.1.2.2.2 (E i)
      (IntermediateField.restrictAlgEquiv (le_iSup t i)) hv
  refine IsDedekindDomain.selmerGroup.mk_mem_of_pow_eq (B := 𝓞 F) hα fun v hv => ?_
  obtain ⟨⟨w, hwp, hwo⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 F)))
  have hw0 : w ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot w
  refine ⟨⟨w, hwp, hw0⟩, hwo, ?_⟩
  exact (hun v hv).ramificationIdx_eq_one hwo

end ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS

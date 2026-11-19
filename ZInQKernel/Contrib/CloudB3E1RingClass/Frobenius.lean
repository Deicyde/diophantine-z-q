import ZInQKernel.Contrib.CloudB3E1RingClass.Realization
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Frobenius
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Compatibility
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified

/-!
# Stage 2 of the ring-class realization: local Frobenius lifts restrict to Artin classes

Manuscript `diophantine_zq.tex`, tex 3575–3576 ("the Artin map sends `𝔭_j` to the class of
`𝔭_j ∩ (ℤ + r𝒪_K)`", [Cox, (9.1)]) and tex 3681–3682.

For a place `v` of `K` not over `f` and the ideal `J = v` of `𝒪_K`, some arithmetic Frobenius lift
`φ ∈ G_{K_v}` restricts, through the localization `p_v : G_{K_v} → G_{K,S}` and restriction to the
ring class field `H_f`, to the Artin class of `J` (`exists_frobeniusLift_locGal`). Proof:
* take a uniformizer `π` of `K_v` and a lift `τ ∈ G_{K_v}` of its local Artin symbol; `τ` is an
  arithmetic Frobenius lift (Tau Ceti, local class field theory);
* the restriction of `τ` to `H_f` is the local Artin symbol of `π` at `v` (`localArtinAt`), read
  through the embedding of `H_f` into `K̄_v` that defines `p_v`;
* by local–global compatibility this is the global Artin symbol of the idele `π` at `v`. Since `H_f`
  is unramified at `v`, that symbol is the class of the Artin element of `J` (the splitting law
  `isArithFrobAt_ringClassArtinEquiv_picClass`). `Gal(H_f/K)` is commutative, so the two agree.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules (KS)

variable {K : Type} [Field K] [NumberField K]

/-- The embedding of algebraic closures `K̄ → K̄_v` defining the decomposition map `G_{K_v} → G_K`.
Kind: definition. -/
def closureEmb (v : HeightOneSpectrum (𝓞 K)) :
    AlgebraicClosure K →+* AlgebraicClosure (v.adicCompletion K) :=
  letI : Algebra K (v.adicCompletion K) := (algebraMap K (v.adicCompletion K)).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K)).toRingHom

/-- The decomposition map is compatible with the embedding of algebraic closures.
Kind: PROVED. -/
theorem closureEmb_decompMap (v : HeightOneSpectrum (𝓞 K)) (τ : Gloc K v)
    (x : AlgebraicClosure K) :
    closureEmb v (DFunLike.coe (F := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (decompMap K v τ) x) =
      DFunLike.coe (F := AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        AlgebraicClosure (v.adicCompletion K)) τ (closureEmb v x) := by
  let _ : Algebra K (v.adicCompletion K) := (algebraMap K (v.adicCompletion K)).toAlgebra
  let _ : Algebra (AlgebraicClosure K) (AlgebraicClosure (v.adicCompletion K)) :=
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K)).toAlgebra
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K τ) (AlgebraicClosure K) x

variable (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- On `H_f ⊆ K_S ⊆ K̄`, the localization acts through the decomposition map. Kind: PROVED. -/
theorem locGal_apply_coe (v : HeightOneSpectrum (𝓞 K)) (τ : Gloc K v)
    (h : ringClassFieldOf f hf S hS) :
    (((locGal f hf S hS v τ h : ringClassFieldOf f hf S hS) : KS K S) : AlgebraicClosure K) =
      DFunLike.coe (F := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K v τ)
        ((h : KS K S) : AlgebraicClosure K) := by
  have h1 := AlgEquiv.restrictNormal_commutes
    (show KS K S ≃ₐ[K] KS K S from locMap K S v τ) (ringClassFieldOf f hf S hS) h
  have h2 := ZInQ.Contrib.CloudB3RC53.RankCounts.resAbs_apply_coe K S (decompMap K v τ) (h : KS K S)
  change ((((show KS K S ≃ₐ[K] KS K S from locMap K S v τ).restrictNormal
    (ringClassFieldOf f hf S hS) h : ringClassFieldOf f hf S hS) : KS K S) : AlgebraicClosure K) = _
  rw [show (((show KS K S ≃ₐ[K] KS K S from locMap K S v τ).restrictNormal
    (ringClassFieldOf f hf S hS) h : ringClassFieldOf f hf S hS) : KS K S) =
      algebraMap (ringClassFieldOf f hf S hS) (KS K S)
        ((show KS K S ≃ₐ[K] KS K S from locMap K S v τ).restrictNormal
          (ringClassFieldOf f hf S hS) h) from rfl, h1]
  exact h2

/-- **The embedding of Tau Ceti's ring class field into `K̄_v`** that defines the localization:
`H_f ≅ H_f ⊆ K_S ⊆ K̄ → K̄_v`. Kind: definition. -/
def ringClassEmb (v : HeightOneSpectrum (𝓞 K)) :
    ringClassField (ringClassOrder (K := K) f hf) →ₐ[K] AlgebraicClosure (v.adicCompletion K) where
  toRingHom := (closureEmb v).comp ((algebraMap (KS K S) (AlgebraicClosure K)).comp
    ((algebraMap (ringClassFieldOf f hf S hS) (KS K S)).comp
      (ringClassFieldOfEquiv f hf S hS).symm.toRingEquiv.toRingHom))
  commutes' c := by
    let _ : Algebra K (v.adicCompletion K) := (algebraMap K (v.adicCompletion K)).toAlgebra
    have h := (IsAlgClosed.lift :
      AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K)).commutes c
    exact h

theorem ringClassEmb_apply (v : HeightOneSpectrum (𝓞 K))
    (y : ringClassField (ringClassOrder (K := K) f hf)) :
    ringClassEmb f hf S hS v y = closureEmb v
      ((((ringClassFieldOfEquiv f hf S hS).symm y : ringClassFieldOf f hf S hS) : KS K S) :
        AlgebraicClosure K) := rfl

/-- **The restriction of `τ ∈ G_{K_v}` to Tau Ceti's ring class field**, through the identification
with `H_f ⊆ K_S`, is the automorphism `σ` with `j ∘ σ = τ ∘ j` for the embedding `j` above.
Kind: PROVED. -/
theorem ringClassEmb_locGal (v : HeightOneSpectrum (𝓞 K)) (τ : Gloc K v)
    (y : ringClassField (ringClassOrder (K := K) f hf)) :
    ringClassEmb f hf S hS v
        (AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS) (locGal f hf S hS v τ) y) =
      (show AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        AlgebraicClosure (v.adicCompletion K) from τ).toRingEquiv (ringClassEmb f hf S hS v y) := by
  rw [ringClassEmb_apply, ringClassEmb_apply, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [locGal_apply_coe, closureEmb_decompMap]
  rfl

/-- **Local Frobenius lifts restrict to Artin classes** (tex 3575–3576, 3681–3682; [Cox, (9.1)]):
at a place `v` not over `f`, with ideal `J = v`, some arithmetic Frobenius lift `φ ∈ G_{K_v}`
restricts to the Artin class of `J` in `Gal(H_f/K)`. Kind: PROVED. -/
theorem exists_frobeniusLift_locGal (v : HeightOneSpectrum (𝓞 K)) (hvf : (f : 𝓞 K) ∉ v.asIdeal)
    (J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus)
    (hJ : (J : Ideal (𝓞 K)) = v.asIdeal) :
    ∃ φ : Gloc K v, TauCeti.IsArithFrobeniusLift (v.adicCompletion K) φ ∧
      locGal f hf S hS v φ = artinClass f hf S hS J := by
  classical
  obtain ⟨π, hπ⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap (v.adicCompletion K) π)
  have hτF : TauCeti.IsArithFrobeniusLift (v.adicCompletion K) τ :=
    isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer (K := v.adicCompletion K) hπ τ hτ
  refine ⟨τ, hτF, ?_⟩
  have h1 : localArtinAt K (ringClassField (ringClassOrder (K := K) f hf)) v π =
      Abelianization.of (AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS)
        (locGal f hf S hS v τ)) :=
    localArtinAt_eq_of_mk_eq_artinMap v τ hτ (ringClassEmb f hf S hS v) _
      (ringClassEmb_locGal f hf S hS v τ)
  have hvc : ¬ v.asIdeal ∣ (ringClassOrder (K := K) f hf).conductor := fun hd =>
    hvf (mem_of_dvd_conductor_ringClassOrder f hf v hd)
  obtain ⟨Q, _, _⟩ := (inferInstance :
    Nonempty (v.asIdeal.primesOver (𝓞 (ringClassField (ringClassOrder (K := K) f hf)))))
  have : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    isUnramifiedAt_ringClassField (ringClassOrder (K := K) f hf) hvc Q
  obtain ⟨J, hJmem⟩ := J
  change J = v.asIdeal at hJ
  subst hJ
  have hfrob := isArithFrobAt_ringClassArtinEquiv_picClass (ringClassOrder (K := K) f hf)
    ⟨v.asIdeal, hJmem⟩ Q
  have h2 := globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt
    (ringClassField (ringClassOrder (K := K) f hf))
    (ringClassField (ringClassOrder (K := K) f hf)).val v Q hfrob π
  rw [(TauCeti.isUniformizer_def π).1 hπ, toAdd_ofAdd, zpow_one,
    IdeleClassGroup.ofAdicCompletion_apply, globalArtinMap_local, h1] at h2
  have h3 := Abelianization.of_injective (Additive.ofMul.injective h2)
  change locGal f hf S hS v τ = (AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS)).symm
    (ringClassArtinEquiv (ringClassOrder (K := K) f hf)
      ((ringClassOrder (K := K) f hf).picClass ⟨v.asIdeal, hJmem⟩))
  rw [← h3, MulEquiv.symm_apply_apply]

/-- **`FrobeniusCompat` holds** for the ring class field of `ℤ + f𝒪_K`. Kind: PROVED. -/
theorem frobeniusCompat : FrobeniusCompat f hf S hS :=
  fun v hvf J hJ => exists_frobeniusLift_locGal f hf S hS v hvf J hJ

open ZInQ.Manuscript.RC.Moving ZInQ.Contrib.CloudB3E1Moving in
/-- **`MovingRealization` from the genuine ring class field, unconditionally** (tex 3565–3595,
3679–3684): for every interface whose ring-class data at `r` are the genuine objects of `H_r`
(`RingClassIdentification`). Kind: PROVED. -/
def movingRealization_genuine {T : TateImage} {n : ℕ} {M : MovingSetting T n} {r : ℕ}
    {hr : r ≠ 0} {S : Set (HeightOneSpectrum (𝓞 K))}
    {hS : ∀ v : HeightOneSpectrum (𝓞 K), (r : 𝓞 K) ∈ v.asIdeal → v ∈ S}
    {P : Set (HeightOneSpectrum (𝓞 K))} (I : RingClassIdentification M r hr S hS P) :
    MovingRealization M r (K := K) (S₀ := S) P :=
  movingRealization_of_identification I (frobeniusCompat r hr S hS)

open ZInQ.Manuscript.RC.Moving ZInQ.Contrib.CloudB3E1Moving in
/-- **`PsiTrivialAt2N` from the genuine ring class field, unconditionally** (tex 2729, 3431,
3500–3506): the moving character `Ψ_i = Ψ ∘ res`, `res` the genuine restriction to
`Gal(H_r/K)`, satisfies the norm-cochain chain's `PsiTrivialAt2N` for every interface identified
with the genuine objects. Kind: PROVED. -/
theorem psiTrivialAt2N_genuine {T : TateImage} {n : ℕ} {M : MovingSetting T n} {r : ℕ}
    {hr : r ≠ 0} {S : Set (HeightOneSpectrum (𝓞 K))}
    {hS : ∀ v : HeightOneSpectrum (𝓞 K), (r : 𝓞 K) ∈ v.asIdeal → v ∈ S}
    {P : Set (HeightOneSpectrum (𝓞 K))} {i : ℕ} [NeZero i]
    [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (Ψ : M.P r →+ Additive (Acoef i)ˣ) (I : RingClassIdentification M r hr S hS P)
    (hΨ : ∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, Ψ z = 0) :
    ZInQ.Contrib.CloudB3E2.NormCochain.PsiTrivialAt2N i
      (ZInQ.Contrib.CloudB3E2.NormCochain.movingPi i (movingPsiAt Ψ (movingRealization_genuine I)))
      (ZInQ.Contrib.CloudB3E2.NormCochain.movingPsi i
        (movingPsiAt Ψ (movingRealization_genuine I))) P :=
  psiTrivialAt2N_of_realization Ψ _ hΨ

end ZInQ.Contrib.CloudB3E1RingClass

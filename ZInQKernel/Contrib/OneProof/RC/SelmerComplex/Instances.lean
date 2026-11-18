import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.SelmerLink
import ZInQKernel.Contrib.CloudB3RC53.Torsion.KummerIdentification
import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Naturality

/-!
# Lane RC26: the genuine Selmer data in the other group's identification interfaces

The identification inputs written against the `SelData` interface take the genuine Selmer data
of this lane directly:

* `selmerIdentificationOfGenuine`: `ClearingComplex.SelmerIdentification` (tex 5509–5517) with
  `sel` the genuine Selmer data `galoisSelData K S 𝒪[G] M Δ` over `𝒪[G]` (coefficient ring
  `MonoidAlgebra OO (SignGroup b)`); the remaining content is the comparison `φ` from the clearing
  complex `D` to the genuine Selmer complex and its quasi-isomorphy;
* `GenuineKummerModelIdentification`: `Torsion.KummerModelIdentification` (tex 4051–4064) over the
  genuine Selmer data;
* `genuineRetainedPairing`: `CommonCoordinate.RetainedPairing` (tex 4163–4166) with the genuine
  global and local cup products of continuous cochains and the genuine restriction of the target
  (compatibility PROVED); the two isotropy homotopies and their retention along the condition
  maps are the inputs;
* `localConditionsOfCC`: genuine local conditions from Mathlib `ℤ`-indexed complexes and cochain
  maps (e.g. the unramified complex `[W --(Φ−1)--> W]`).

These are instantiations of the interfaces (the fields `φ`, `qis` remain the inputs: they compare
the text's finite models with the genuine complexes and are not proved here).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open NumberField IsDedekindDomain CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Manuscript.RC.Determinant (OO SignGroup)

/-! ### Mathlib `ℤ`-indexed complexes as local conditions -/

section OfCC

universe u

variable {k : Type u} [CommRing k]

/-- A Mathlib `ℤ`-indexed cochain complex of `k`-modules as a relation-indexed complex `GCx`
(same terms and differentials). -/
def ofCC (C : CochainComplex (ModuleCat.{u} k) ℤ) : GCx k where
  X := C.X
  d i j _ := (C.d i j).hom
  d_d i j l _ _ x := congrArg (fun f => f.hom x) (C.d_comp_d i j l)

/-- A Mathlib cochain map `C ⟶ B.toCC` as a relation-indexed chain map `ofCC C → B`. -/
def ofCCHom {C : CochainComplex (ModuleCat.{u} k) ℤ} {B : GCx k} (f : C ⟶ B.toCC) :
    GHom (ofCC C) B where
  f i j h := by subst h; exact (f.f i).hom
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    have e : (B.toCC.d i i₁).hom ((f.f i).hom x) = (f.f i₁).hom ((C.d i i₁).hom x) :=
      congrArg (fun g => g.hom x) (f.comm i i₁)
    exact e.symm.trans (GCx.toCC_d_hom B i i₁ h₂ ((f.f i).hom x))

/-- **Local conditions from Mathlib data**: `ℤ`-indexed complexes `U_v` (for instance the
unramified complex `[W --(Φ−1)--> W]` in degrees `0, 1`) with Mathlib cochain maps
`U_v ⟶ C^•_cont(G_v, M)` (into the `ℤ`-indexed form `(localCx …).toCC` of the genuine local
complex) give genuine local conditions. -/
def localConditionsOfCC {GS : Type u} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
    {ι : Type u} {Gv : ι → Type u} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
    [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
    {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
    (U : ι → CochainComplex (ModuleCat.{u} k) ℤ) (i : ∀ v, U v ⟶ (localCx k GS Gv loc M v).toCC) :
    LocalConditions k GS Gv loc M :=
  ⟨fun v => ofCC (U v), fun v => ofCCHom (i v)⟩

end OfCC

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **`SelmerIdentification` with the genuine Selmer data** over `𝒪[G]`: an `Identification`,
genuine local conditions for a topological `𝒪[G][G_{K,S}]`-module `M`, and a quasi-isomorphism
from the clearing complex `D` to the genuine Selmer complex give the structure. -/
def selmerIdentificationOfGenuine {b dK hK cE tK : ℕ} (I : Identification b dK hK cE tK)
    (M : Type) [AddCommGroup M] [Module (MonoidAlgebra OO (SignGroup b)) M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (MonoidAlgebra OO (SignGroup b)) M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul (MonoidAlgebra OO (SignGroup b)) M]
    [ContinuousSMul (GKS K S) M]
    (Δ : GaloisLocalConditions K S (MonoidAlgebra OO (SignGroup b)) M)
    (φ : I.D.toGCx.toCC ⟶ (selCx (galoisSelData K S _ M Δ)).toCC) (qis : QuasiIso φ) :
    SelmerIdentification b dK hK cE tK where
  toIdentification := I
  sel := galoisSelData K S _ M Δ
  φ := φ
  qis := qis

/-- **`KummerModelIdentification` over the genuine Selmer data.** -/
abbrev GenuineKummerModelIdentification (R : Type) [CommRing R] [IsDomain R] (M : Type)
    [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul (GKS K S) M]
    (Δ : GaloisLocalConditions K S R M) : Type :=
  ZInQ.Contrib.CloudB3RC53.Torsion.KummerModelIdentification (galoisSelData K S R M Δ)

section Retained

open ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.CommonCoordinate

variable {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- **The retained pairing data with the genuine cup products** (tex 4163–4166): for genuine
primitive-orthogonal data `ΔPp` (coefficients `M`) and relaxed data `ΔR` (coefficients `M'`), the
genuine global and local cup products for `β`, the genuine restriction of the target and the
PROVED compatibility `res(a ∪ b) = res a ∪ res b`, together with the given isotropy homotopies
`h_R`, `h_P` and their retention. -/
def genuineRetainedPairing (ΔR : GaloisLocalConditions K S R M') (ΔPp : GaloisLocalConditions K S R M)
    {UP US : GCx R} (fP : GHom UP (galoisSelData K S R M' ΔR).U)
    (fS : GHom US (galoisSelData K S R M ΔPp).U)
    (hR : ∀ i j l : ℤ, i + j = l + 1 →
      US.X i →ₗ[R] (galoisSelData K S R M' ΔR).U.X j →ₗ[R] (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T).X l)
    (isoR : ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
      (hl : l + 1 = l₁) (u : US.X i) (v : (galoisSelData K S R M' ΔR).U.X j),
      (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T).d
          l l₁ hl (hR i j l h u v) + hR i₁ j l₁ (by omega) (US.d i i₁ hi u) v +
          sgn i • hR i j₁ l₁ (by omega) u ((galoisSelData K S R M' ΔR).U.d j j₁ hj v) =
        (localSumPair R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
          (continuous_pairing β)).P i j l₁ (by omega)
          ((ghomComp fS (galoisSelData K S R M ΔPp).ι).f i i rfl u)
          ((galoisSelData K S R M' ΔR).ι.f j j rfl v))
    (hP : ∀ i j l : ℤ, i + j = l + 1 →
      (galoisSelData K S R M ΔPp).U.X i →ₗ[R] UP.X j →ₗ[R] (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T).X l)
    (isoP : ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
      (hl : l + 1 = l₁) (u : (galoisSelData K S R M ΔPp).U.X i) (v : UP.X j),
      (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T).d
          l l₁ hl (hP i j l h u v) +
          hP i₁ j l₁ (by omega) ((galoisSelData K S R M ΔPp).U.d i i₁ hi u) v +
          sgn i • hP i j₁ l₁ (by omega) u (UP.d j j₁ hj v) =
        (localSumPair R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
          (continuous_pairing β)).P i j l₁ (by omega)
          ((galoisSelData K S R M ΔPp).ι.f i i rfl u)
          ((ghomComp fP (galoisSelData K S R M' ΔR).ι).f j j rfl v))
    (retained : ∀ (i j l : ℤ) (h : i + j = l + 1) (u : US.X i) (v : UP.X j),
      hR i j l h u (fP.f j j rfl v) = hP i j l h (fS.f i i rfl u) v) :
    RetainedPairing (galoisSelData K S R M' ΔR) (galoisSelData K S R M ΔPp) fP fS where
  E := globalCx R (GKS K S) T
  EL := localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
  resE := resS R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
  cupG := globalPair R (GKS K S) β hβ (continuous_pairing β)
  cupL := localSumPair R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
    (continuous_pairing β)
  compat := (galoisPairData K S R β hβ (strictConditions R _ _ _ M) (strictConditions R _ _ _ M')
    (strictIsotropy R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
      (continuous_pairing β))).compat
  hR := hR
  isoR := isoR
  hP := hP
  isoP := isoP
  retained := retained

end Retained

end ZInQ.Manuscript.RC.SelmerComplex

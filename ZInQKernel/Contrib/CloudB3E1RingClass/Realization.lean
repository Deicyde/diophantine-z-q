import ZInQKernel.Contrib.CloudB3E1RingClass.Order
import ZInQKernel.Contrib.CloudB3E1Moving.MovingRealization

/-!
# Stage 1 of the ring-class realization: `MovingRealization` from the genuine ring class field

Manuscript `diophantine_zq.tex`, tex 3565–3595 and 3679–3684 (the ring class fields `H_r`, their
decomposition and inertia groups and Frobenius classes), tex 2720 and 3528–3531 (`K` split at `2N`,
one chosen prime over each prime dividing `2N`).

The moving-character interface `MovingSetting` (lane RC4) carries abstract ring-class data: a group
`P r` standing for `Gal(H_r/K)`, its decomposition groups `decomp r j`, `decompBar r j` at the
chosen primes `𝔭_j`, `𝔭̄_j`, its inertia group `inertia r` at `r`, and the Frobenius classes
`q r j`. This file defines the genuine objects for the ring class field `H_r` of `ℤ + r𝒪_K` inside
`K_S` (`Order.lean`). It proves `MovingRealization`, the GLUE behind `PsiTrivialAt2N`, for every
interface whose ring-class data are these genuine objects.

* `locGal v : G_{K_v} → Gal(H_r/K)`: localization followed by restriction.
* `decompGal v`: the genuine decomposition group of `H_r/K` at `v`, the image of `G_{K_v}`.
* `inertiaGal v`: the genuine inertia group at `v`, the image of the inertia subgroup `I_{K_v}`.
* `artinClass J`: the Artin class of an ideal `J` prime to `r`, the image of the Picard class of
  `J ∩ (ℤ + r𝒪_K)` under `Pic(ℤ + r𝒪_K) ≃ Gal(H_r/K)` (tex 3575–3576, [Cox, (9.1)]).
* `FrobeniusCompat` (a Prop, PROVED in `Frobenius.lean`): at a place `v` not over `r`, some
  arithmetic Frobenius lift of `G_{K_v}` restricts to the Artin class of `v`.
* `RingClassIdentification M r P`: the interface's ring-class data are the genuine ones. That is:
  - an additive isomorphism `P r ≃ Gal(H_r/K)`;
  - `decomp`, `decompBar` and `inertia` are the genuine decomposition and inertia groups at
    chosen places `𝔭_j`, `𝔭̄_j` and a place over `r`;
  - `q r j` is the Artin class of `𝔭_j` at active `j`;
  - the places of `P` are among the `𝔭_j`, `𝔭̄_j` over `2N`.
  For a genuine construction of the interface (`P r := Gal(H_r/K)` with these subgroups and
  classes) the fields `e`, `inertia_eq`, `decomp_eq`, `decompBar_eq` and `q_eq` hold by definition.
  The fields `placeR`, `P_sub`, `ideal` and `place_not_over` are true facts about the chosen places
  (a place over `r` exists for `r > 1`; `K` is split at `2N`; the active primes are good).
* **`movingRealization_of_identification`** (PROVED): `RingClassIdentification` and
  `FrobeniusCompat` give `MovingRealization M r P`. The restriction is onto
  (`ringClassRes_surjective`), and the three compatibilities follow from the definitions and
  Frobenius compatibility.
* **`psiTrivialAt2N_of_identification`** (PROVED): the moving character's `PsiTrivialAt2N` for the
  norm-cochain chain, from the same inputs.

Kinds: definitions and PROVED. `FrobeniusCompat` is a hypothesis of the two theorems here; it is
PROVED in `Frobenius.lean`, which states the unconditional forms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Moving
open ZInQ.Contrib.CloudB3E1Moving

variable {K : Type} [Field K] [NumberField K]
variable (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-! ### The genuine decomposition and inertia groups and Artin classes -/

/-- **The localization `G_{K_v} → Gal(H_f/K)`**: `p_v` followed by restriction to `H_f`.
Kind: definition. -/
def locGal (v : HeightOneSpectrum (𝓞 K)) : Gloc K v →* ringClassGal f hf S hS :=
  (ringClassRes f hf S hS).comp (locMap K S v).toMonoidHom

/-- **The decomposition group of `H_f/K` at `v`**: the image of `G_{K_v}`. Kind: definition. -/
def decompGal (v : HeightOneSpectrum (𝓞 K)) : Subgroup (ringClassGal f hf S hS) :=
  (locGal f hf S hS v).range

/-- **The inertia group of `H_f/K` at `v`**: the image of the inertia subgroup of `G_{K_v}`.
Kind: definition. -/
def inertiaGal (v : HeightOneSpectrum (𝓞 K)) : Subgroup (ringClassGal f hf S hS) :=
  (TauCeti.inertiaSubgroup (v.adicCompletion K)).map (locGal f hf S hS v)

/-- **The Artin class** of an ideal `J` of `𝒪_K` prime to `f`: the image of the Picard class of
`J ∩ (ℤ + f𝒪_K)` (tex 3575–3576, [Cox, (9.1)]). Kind: definition. -/
def artinClass (J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus) :
    ringClassGal f hf S hS :=
  ringClassPicEquiv f hf S hS ((ringClassOrder (K := K) f hf).picClass J)

/-- **Local–global Frobenius compatibility** (tex 3575–3576 and 3681–3682): at a place `v` not
over `f`, whose ideal is `J`, some arithmetic Frobenius lift of `G_{K_v}` restricts to the Artin
class of `J` in `Gal(H_f/K)`. PROVED in `Frobenius.lean` (`frobeniusCompat`).
Kind: definition (of the Prop). -/
def FrobeniusCompat : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 K)), (f : 𝓞 K) ∉ v.asIdeal →
    ∀ J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus,
      (J : Ideal (𝓞 K)) = v.asIdeal →
        ∃ φ : Gloc K v, TauCeti.IsArithFrobeniusLift (v.adicCompletion K) φ ∧
          locGal f hf S hS v φ = artinClass f hf S hS J

/-! ### The identification of the interface with the genuine objects -/

variable {T : TateImage} {n : ℕ}

attribute [instance] MovingSetting.pGrp

/-- **The interface's ring-class data are the genuine ones at `r`** (tex 3565–3595, 3679–3684,
2720, 3528–3531). For a genuine construction of the interface, with `P r := Gal(H_r/K)` and these
subgroups and classes, the identification fields hold by definition. The place fields are true
facts about the chosen places. Kind: definition (of the structure). -/
structure RingClassIdentification (M : MovingSetting T n) (r : ℕ) (hr : r ≠ 0)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (r : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (P : Set (HeightOneSpectrum (𝓞 K))) where
  /-- `P r = Gal(H_r/K)`, written additively -/
  e : M.P r ≃+ Additive (ringClassGal r hr S hS)
  /-- a place of `K` over `r` -/
  placeR : HeightOneSpectrum (𝓞 K)
  placeR_over : ((r : ℤ) : 𝓞 K) ∈ placeR.asIdeal
  /-- `inertia r` is the genuine inertia group at `placeR` -/
  inertia_eq : ∀ z, z ∈ M.inertia r ↔ Additive.toMul (e z) ∈ inertiaGal r hr S hS placeR
  /-- the chosen primes `𝔭_j` and their conjugates `𝔭̄_j`, as places of `K` -/
  place : Fin M.s → HeightOneSpectrum (𝓞 K)
  placeBar : Fin M.s → HeightOneSpectrum (𝓞 K)
  /-- `decomp r j`, `decompBar r j` are the genuine decomposition groups at `𝔭_j`, `𝔭̄_j` -/
  decomp_eq : ∀ j z, z ∈ M.decomp r j ↔ Additive.toMul (e z) ∈ decompGal r hr S hS (place j)
  decompBar_eq : ∀ j z,
    z ∈ M.decompBar r j ↔ Additive.toMul (e z) ∈ decompGal r hr S hS (placeBar j)
  /-- the places of `P` (above `2N`) are among the chosen `𝔭_j`, `𝔭̄_j` over `2N` (`K` split at
  `2N`, one chosen prime over each prime dividing `2N`) -/
  P_sub : ∀ v ∈ P, ∃ j, M.over2N j ∧ (v = place j ∨ v = placeBar j)
  /-- at an active orientation, the ideal of `𝔭_j`, prime to `r` -/
  ideal : ∀ j, M.act j → integralIdealsPrimeTo (ringClassOrder (K := K) r hr).conductorModulus
  ideal_eq : ∀ j (hj : M.act j), ((ideal j hj : Ideal (𝓞 K))) = (place j).asIdeal
  /-- the active primes are prime to `r` (`r` is good) -/
  place_not_over : ∀ j, M.act j → (r : 𝓞 K) ∉ (place j).asIdeal
  /-- `q r j` is the Artin class of `𝔭_j` -/
  q_eq : ∀ j (hj : M.act j), Additive.toMul (e (M.q r j)) = artinClass r hr S hS (ideal j hj)

variable {M : MovingSetting T n} {r : ℕ} {hr : r ≠ 0} {S}
  {hS : ∀ v : HeightOneSpectrum (𝓞 K), (r : 𝓞 K) ∈ v.asIdeal → v ∈ S}
  {P : Set (HeightOneSpectrum (𝓞 K))}

/-- The restriction `G_{K,S} → Gal(H_r/K) = P r`, through the identification.
Kind: definition. -/
def RingClassIdentification.res (I : RingClassIdentification M r hr S hS P) :
    GKS K S →* Multiplicative (M.P r) where
  toFun g := Multiplicative.ofAdd (I.e.symm (Additive.ofMul (ringClassRes r hr S hS g)))
  map_one' := by simp
  map_mul' a b := by simp [map_mul]

theorem RingClassIdentification.e_res (I : RingClassIdentification M r hr S hS P) (g : GKS K S) :
    Additive.toMul (I.e (Multiplicative.toAdd (I.res g))) = ringClassRes r hr S hS g := by
  simp [RingClassIdentification.res]

/-- **`MovingRealization` from the genuine ring class field** (tex 3565–3595, 3679–3684). Given
the identification of the interface's ring-class data with `Gal(H_r/K)` and its genuine
decomposition groups, inertia group and Artin classes, and local–global Frobenius compatibility
(stage 2), the realization holds, with `res` the genuine restriction `G_{K,S} → Gal(H_r/K)`.
Kind: PROVED. -/
def movingRealization_of_identification (I : RingClassIdentification M r hr S hS P)
    (hF : FrobeniusCompat r hr S hS) : MovingRealization M r (K := K) (S₀ := S) P where
  res := I.res
  res_surj := by
    intro x
    obtain ⟨g, hg⟩ := ringClassRes_surjective r hr S hS
      (Additive.toMul (I.e (Multiplicative.toAdd x)))
    refine ⟨g, ?_⟩
    change Multiplicative.ofAdd (I.e.symm (Additive.ofMul (ringClassRes r hr S hS g))) = x
    rw [hg]
    simp
  decomp_at v hv := by
    obtain ⟨j, hj, hvj⟩ := I.P_sub v hv
    refine ⟨j, hj, ?_⟩
    rcases hvj with rfl | rfl
    · intro σ
      refine AddSubgroup.mem_sup_left ((I.decomp_eq j _).mpr ?_)
      rw [I.e_res]
      exact ⟨σ, rfl⟩
    · intro σ
      refine AddSubgroup.mem_sup_right ((I.decompBar_eq j _).mpr ?_)
      rw [I.e_res]
      exact ⟨σ, rfl⟩
  placeR := I.placeR
  placeR_over := I.placeR_over
  inertia_into σ hσ := by
    refine (I.inertia_eq _).mpr ?_
    rw [I.e_res]
    exact ⟨σ, hσ, rfl⟩
  inertia_onto z hz := by
    obtain ⟨σ, hσ, hσz⟩ := (I.inertia_eq z).mp hz
    refine ⟨σ, hσ, ?_⟩
    apply I.e.injective
    apply Additive.toMul.injective
    rw [I.e_res]
    exact hσz
  place := I.place
  frob_act j hj := by
    obtain ⟨φ, hφ, hφq⟩ :=
      hF (I.place j) (I.place_not_over j hj) (I.ideal j hj) (I.ideal_eq j hj)
    refine ⟨φ, hφ, ?_⟩
    apply I.e.injective
    apply Additive.toMul.injective
    rw [I.e_res, I.q_eq j hj]
    exact hφq

/-- **`PsiTrivialAt2N` for the genuine ring class field** (tex 2729, 3431, 3500–3506): the moving
character `Ψ_i = Ψ ∘ res`, with `res` the genuine restriction to `Gal(H_r/K)`, satisfies the
norm-cochain chain's `PsiTrivialAt2N`, from the identification and Frobenius compatibility.
Kind: PROVED. -/
theorem psiTrivialAt2N_of_identification {i : ℕ} [NeZero i]
    [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (Ψ : M.P r →+ Additive (Acoef i)ˣ) (I : RingClassIdentification M r hr S hS P)
    (hF : FrobeniusCompat r hr S hS)
    (hΨ : ∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, Ψ z = 0) :
    ZInQ.Contrib.CloudB3E2.NormCochain.PsiTrivialAt2N i
      (ZInQ.Contrib.CloudB3E2.NormCochain.movingPi i
        (movingPsiAt Ψ (movingRealization_of_identification I hF)))
      (ZInQ.Contrib.CloudB3E2.NormCochain.movingPsi i
        (movingPsiAt Ψ (movingRealization_of_identification I hF))) P :=
  psiTrivialAt2N_of_realization Ψ _ hΨ

end ZInQ.Contrib.CloudB3E1RingClass

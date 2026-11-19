import ZInQKernel.Contrib.CloudB3E1RingClass.Relations

/-!
# A genuine `MovingDataK` with the ring-class fields built from the ring class fields `H_r`

Manuscript `diophantine_zq.tex`, tex 3530–3595, 3662–3693 (the moving-character construction) and
tex 3500–3506 (Proposition `ex:arith-moving-character`).

Lane RC17/RC27's interface `MovingDataK E n` (`RC/GlueSweep/TateKummer.lean`) keeps the ring-class
data abstract: a group `P r` for `Gal(H_r/K)`, maps `π`, `δ`, classes `q`, `qbar`, and subgroups
`inertia`, `decomp`, `decompBar`, with GLUE fields relating them. This file builds a `MovingDataK`
whose ring-class data are the genuine objects of the ring class field `H_r` of `ℤ + r𝒪_K` inside
`K_{S_r}`, for a number field `K`:

* `P r := Gal(H_r/K)` (additively); `π r : Gal(H_r/K) → Cl(K)` (`galToClassGroup`);
  `Cl := Cl(K)`, `cls j := [𝔭_j]`;
* `q r j`, `qbar r j`: the Artin classes of the chosen primes `𝔭_j`, `𝔭̄_j`;
* `decomp r j`, `decompBar r j`: the genuine decomposition groups at `𝔭_j`, `𝔭̄_j`;
  `inertia r`: the genuine inertia group at a chosen place over `r`.

For these the interface fields `π_q`, `qbar_eq`, `decomp_eq` and `decompBar_eq` are PROVED here (stages
3–4). The remaining fields of `MovingDataK` are inputs (`GenuineMovingInputs`), stated over the genuine
objects:
* the Kummer data: `kd`, `KR_val`;
* `cls_gen`, `m`, `m_span`;
* `δ`, `δ_inj`, `exact`, `x`, `rel`, `κ`, `κ_surj`;
* `inertia_eq`, `frob_kummer`.

**`movingRealization_genuineData`** (PROVED): for this `MovingDataK`, the moving-character GLUE
`MovingRealization` holds at every good `r`, with no further hypothesis. **`exists_psiTrivialAt2N_genuineData`**
(PROVED): the norm-cochain chain's `PsiTrivialAt2N` for the moving character of this `MovingDataK`,
over the genuine Tate image of `E_ℓ`.

Kinds: definitions and PROVED. The inputs of `GenuineMovingInputs` keep the kinds of the
corresponding `MovingDataK` fields (GLUE/ELLIOT, see `TateKummer.lean`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Moving ZInQ.Manuscript.RC.TateWiring ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.GlueSweep.Tate
open ZInQ.Contrib.CloudB3E1Moving
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-! ### The places and support sets -/

/-- **The chosen primes and the support sets** (tex 3528–3531, 3683–3684): the chosen primes
`𝔭_j` and their conjugates `𝔭̄_j`, with `𝔭_j 𝔭̄_j = (p_j)`; support sets `S_r` containing the
primes over `r`; a place over each `r`. Kind: definition (of the structure). -/
structure RingClassSetup (K : Type) [Field K] [NumberField K] (s : ℕ) where
  𝔭 : Fin s → HeightOneSpectrum (𝓞 K)
  𝔭bar : Fin s → HeightOneSpectrum (𝓞 K)
  p : Fin s → ℕ
  p_prime : ∀ j, (p j).Prime
  𝔭_mul : ∀ j, (𝔭 j).asIdeal * (𝔭bar j).asIdeal = Ideal.span {(((p j : ℤ)) : 𝓞 K)}
  Sr : ℕ → Set (HeightOneSpectrum (𝓞 K))
  hSr : ∀ r (v : HeightOneSpectrum (𝓞 K)), ((max r 1 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ Sr r
  placeR : ℕ → HeightOneSpectrum (𝓞 K)

variable {s : ℕ} (C : RingClassSetup K s)

theorem max_one_ne_zero (r : ℕ) : max r 1 ≠ 0 := by omega

/-- `Gal(H_r/K)` for the setup (the conductor is `max r 1`, equal to `r` for `r ≥ 1`).
Kind: definition. -/
abbrev setupGal (r : ℕ) : Type :=
  ringClassGal (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)

/-- A maximal ideal not containing `f` is prime to the conductor of `ℤ + f𝒪_K`. Kind: PROVED. -/
theorem mem_primeTo_of_not_mem (f : ℕ) (hf : f ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (hv : (f : 𝓞 K) ∉ v.asIdeal) :
    v.asIdeal ∈ integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  refine ⟨v.ne_bot, ?_⟩
  have h1 : v.asIdeal ⊔ Ideal.span {(f : 𝓞 K)} = ⊤ := by
    by_contra h
    have h2 := v.isMaximal.eq_of_le h le_sup_left
    exact hv (by rw [h2]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine eq_top_iff.mpr ?_
  rw [← h1]
  exact sup_le_sup_left (span_le_conductor_ringClassOrder f hf) _

/-- The ideal of a place not over `f`, as an ideal prime to the conductor. Kind: definition. -/
def primeToIdeal (f : ℕ) (hf : f ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (hv : (f : 𝓞 K) ∉ v.asIdeal) :
    integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus :=
  ⟨v.asIdeal, mem_primeTo_of_not_mem f hf v hv⟩

/-! ### The genuine ring-class data -/

/-- **`q r j`**: the Artin class of `𝔭_j` in `Gal(H_r/K)` (`0` when `𝔭_j` lies over `r`, never for
good `r`). Kind: definition. -/
def setupQ (r : ℕ) (j : Fin s) : Additive (setupGal C r) := by
  classical
  exact if h : ((max r 1 : ℕ) : 𝓞 K) ∉ (C.𝔭 j).asIdeal then
    Additive.ofMul (artinClass (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
      (primeToIdeal (max r 1) (max_one_ne_zero r) (C.𝔭 j) h))
  else 0

/-- **`qbar r j`**: the Artin class of `𝔭̄_j` (`0` when `𝔭̄_j` lies over `r`, never for good `r`).
Kind: definition. -/
def setupQbar (r : ℕ) (j : Fin s) : Additive (setupGal C r) := by
  classical
  exact if h : ((max r 1 : ℕ) : 𝓞 K) ∉ (C.𝔭bar j).asIdeal then
    Additive.ofMul (artinClass (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
      (primeToIdeal (max r 1) (max_one_ne_zero r) (C.𝔭bar j) h))
  else 0

/-- **`π r : Gal(H_r/K) → Cl(K)`**. Kind: definition. -/
def setupPi (r : ℕ) : Additive (setupGal C r) →+ Additive (ClassGroup (𝓞 K)) :=
  (galToClassGroup (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)).toAdditive

/-- **`decomp r j`**, **`decompBar r j`**: the genuine decomposition groups at `𝔭_j`, `𝔭̄_j`.
Kind: definition. -/
def setupDecomp (r : ℕ) (j : Fin s) : AddSubgroup (Additive (setupGal C r)) :=
  Subgroup.toAddSubgroup (decompGal (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭 j))

def setupDecompBar (r : ℕ) (j : Fin s) : AddSubgroup (Additive (setupGal C r)) :=
  Subgroup.toAddSubgroup (decompGal (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭bar j))

/-- **`inertia r`**: the genuine inertia group at the chosen place over `r`. Kind: definition. -/
def setupInertia (r : ℕ) : AddSubgroup (Additive (setupGal C r)) :=
  Subgroup.toAddSubgroup (inertiaGal (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.placeR r))

/-- **`cls j = [𝔭_j]`** in `Cl(K)`. Kind: definition. -/
def setupCls (j : Fin s) : Additive (ClassGroup (𝓞 K)) :=
  Additive.ofMul (ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩)

/-! ### Facts at good primes -/

/-- A prime `r` different from `p_j` does not lie under `𝔭_j` or `𝔭̄_j`. Kind: PROVED. -/
theorem not_mem_of_ne (j : Fin s) (r : ℕ) (hr : r.Prime) (hrp : r ≠ C.p j) :
    ((max r 1 : ℕ) : 𝓞 K) ∉ (C.𝔭 j).asIdeal ∧ ((max r 1 : ℕ) : 𝓞 K) ∉ (C.𝔭bar j).asIdeal := by
  have hmax : max r 1 = r := max_eq_left hr.one_lt.le
  rw [hmax]
  have hcop : Nat.Coprime r (C.p j) := (Nat.coprime_primes hr (C.p_prime j)).mpr hrp
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * r + b * (C.p j) = 1 := by
    obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨a, b, h⟩
  have hp : ((C.p j : ℕ) : 𝓞 K) ∈ (C.𝔭 j).asIdeal * (C.𝔭bar j).asIdeal := by
    have := C.𝔭_mul j
    rw [Int.cast_natCast] at this
    rw [this]
    exact Ideal.mem_span_singleton_self _
  have key : ∀ (Q : Ideal (𝓞 K)), Q ≠ ⊤ → ((C.p j : ℕ) : 𝓞 K) ∈ Q → ((r : ℕ) : 𝓞 K) ∉ Q := by
    intro Q hQ hpQ hrQ
    apply hQ
    rw [Ideal.eq_top_iff_one]
    have h1 : (a : 𝓞 K) * (r : 𝓞 K) + (b : 𝓞 K) * ((C.p j : ℕ) : 𝓞 K) = 1 := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) hab
      push_cast at this
      exact this
    rw [← h1]
    exact Q.add_mem (Q.mul_mem_left _ hrQ) (Q.mul_mem_left _ hpQ)
  have h1 : ((C.p j : ℕ) : 𝓞 K) ∈ (C.𝔭 j).asIdeal :=
    Ideal.mul_le_left (I := (C.𝔭 j).asIdeal) (J := (C.𝔭bar j).asIdeal) hp
  have h2 : ((C.p j : ℕ) : 𝓞 K) ∈ (C.𝔭bar j).asIdeal :=
    Ideal.mul_le_right (I := (C.𝔭 j).asIdeal) (J := (C.𝔭bar j).asIdeal) hp
  exact ⟨key (C.𝔭 j).asIdeal (Ideal.IsPrime.ne_top (C.𝔭 j).isPrime) h1,
    key (C.𝔭bar j).asIdeal (Ideal.IsPrime.ne_top (C.𝔭bar j).isPrime) h2⟩

theorem toAddSubgroup_zpowers {G : Type*} [Group G] (g : G) :
    Subgroup.toAddSubgroup (Subgroup.zpowers g) = AddSubgroup.zmultiples (Additive.ofMul g) := by
  ext z
  change Additive.toMul z ∈ Subgroup.zpowers g ↔ z ∈ AddSubgroup.zmultiples (Additive.ofMul g)
  rw [Subgroup.mem_zpowers_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← ofMul_toMul z, ← hk, ofMul_zpow]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [toMul_zsmul, toMul_ofMul]⟩

/-- The ideal class of an ideal prime to a modulus is its class in `Cl(𝒪_K)`. Kind: PROVED. -/
theorem classOfIdeal_eq_mk0 {m : Modulus K} (J : integralIdealsPrimeTo m)
    (hJ : (J : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) :
    classOfIdeal J = ClassGroup.mk0 ⟨(J : Ideal (𝓞 K)), hJ⟩ := by
  rw [classOfIdeal, idealClass_apply, rayClassToClassGroup_rayClassMk, ← ClassGroup.mk_mk0 K]
  congr 1

/-! ### The inputs and the genuine `MovingDataK` -/

/-- **The remaining inputs of a genuine `MovingDataK`** (tex 3530–3595, 3662–3693). These are the
fields of `MovingDataK` that are not built here, stated over the genuine ring-class objects of
`C`, with the kinds of the corresponding `MovingDataK` fields; plus `p_mem` (the rational primes
under the chosen primes are excluded, tex 3566, 3676) and `placeR_over`.
Kind: definition (of the structure). -/
structure GenuineMovingInputs (E : WeierstrassCurve ℚ) (n : ℕ) {s : ℕ} (C : RingClassSetup K s) where
  D : ℚ
  sqrtD : Qbar
  sqrtD_sq : sqrtD ^ 2 = algebraMap ℚ Qbar D
  t : ℕ
  kd : KummerData sqrtD n t
  act : Fin s → Prop
  [decAct : DecidablePred act]
  over2N : Fin s → Prop
  act_not_over2N : ∀ j, act j → ¬ over2N j
  /-- `GLUE` (tex 3532–3534) -/
  cls_gen : ∀ c : Additive (ClassGroup (𝓞 K)), ∃ v : Fin s → ℤ, ∑ j, v j • setupCls C j = c
  m : Fin t → Fin s → ℤ
  m_span : ∀ v : Fin s → ℤ, ∑ j, v j • setupCls C j = 0 → ∃ b : Fin t → ℤ, v = ∑ a, b a • m a
  /-- `ELLIOT/GLUE` (tex 3551–3557) -/
  KR_val : ∀ b ∈ kd.KR, ∀ j, act j → (2 : ℤ) ^ n ∣ ∑ a, b a * m a j
  Sexc : Finset ℕ
  p_mem : ∀ j, C.p j ∈ Sexc
  placeR_over : ∀ r, GoodPrime E sqrtD Sexc r → ((r : ℤ) : 𝓞 K) ∈ (C.placeR r).asIdeal
  Pl : ℕ → Type
  δ : ∀ r, Pl r → (Additive (ZMod r)ˣ →+ Additive (setupGal C r))
  /-- `GLUE` (tex 3566–3575) -/
  δ_inj : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v, Function.Injective (δ r v)
  exact : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v, ∀ p : Additive (setupGal C r),
    setupPi C r p = 0 ↔ ∃ y, δ r v y = p
  x : ∀ r, Pl r → Fin t → Additive (ZMod r)ˣ
  /-- `GLUE` (tex 3576–3579) -/
  rel : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v a, ∑ j, m a j • setupQ C r j + δ r v (x r v a) = 0
  κ : ∀ r, Pl r → (Additive (ZMod r)ˣ →+ ZMod (2 ^ n))
  /-- `GLUE` (tex 3585–3586) -/
  κ_surj : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v, (2 : ℤ) ^ n ∣ (r : ℤ) - 1 →
    Function.Surjective (κ r v)
  /-- `GLUE` (tex 3679–3681): the genuine inertia group at `r` is the range of `δ` -/
  inertia_eq : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v, setupInertia C r = (δ r v).range
  /-- `GLUE` (tex 3676–3677): the power-residue formula -/
  frob_kummer : ∀ (r : ℕ) (h : GalQ), GoodPrime E sqrtD Sexc r →
    ZInQ.Contrib.ChebFD.C10.IsFrobAt h r → h sqrtD = sqrtD → (2 : ℤ) ^ n ∣ (r : ℤ) - 1 →
      ∃ v : Pl r, ∀ a, h (kd.γ a) = kd.ζ ^ (κ r v (x r v a)).val * kd.γ a

attribute [instance] GenuineMovingInputs.decAct

variable {C} {E : WeierstrassCurve ℚ} {n ℓ : ℕ}

theorem GenuineMovingInputs.not_mem (I : GenuineMovingInputs E n C) {r : ℕ}
    (hr : GoodPrime E I.sqrtD I.Sexc r) (j : Fin s) :
    ((max r 1 : ℕ) : 𝓞 K) ∉ (C.𝔭 j).asIdeal ∧ ((max r 1 : ℕ) : 𝓞 K) ∉ (C.𝔭bar j).asIdeal :=
  not_mem_of_ne C j r hr.1 (fun h => hr.2.2.2.1 (h ▸ I.p_mem j))

theorem setupQ_eq {r : ℕ} {j : Fin s} (h : ((max r 1 : ℕ) : 𝓞 K) ∉ (C.𝔭 j).asIdeal) :
    setupQ C r j = Additive.ofMul (artinClass (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
      (primeToIdeal (max r 1) (max_one_ne_zero r) (C.𝔭 j) h)) := by
  classical
  simp [setupQ, h]

theorem setupQbar_eq {r : ℕ} {j : Fin s} (h : ((max r 1 : ℕ) : 𝓞 K) ∉ (C.𝔭bar j).asIdeal) :
    setupQbar C r j = Additive.ofMul (artinClass (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
      (primeToIdeal (max r 1) (max_one_ne_zero r) (C.𝔭bar j) h)) := by
  classical
  simp [setupQbar, h]

/-- **The genuine `MovingDataK`**: the interface with `P r = Gal(H_r/K)` and the genuine
ring-class data; `π_q`, `qbar_eq`, `decomp_eq`, `decompBar_eq` PROVED. Kind: definition. -/
def GenuineMovingInputs.toMovingDataK (I : GenuineMovingInputs E n C) : MovingDataK E n where
  D := I.D
  sqrtD := I.sqrtD
  sqrtD_sq := I.sqrtD_sq
  s := s
  t := I.t
  kd := I.kd
  act := I.act
  over2N := I.over2N
  act_not_over2N := I.act_not_over2N
  Cl := Additive (ClassGroup (𝓞 K))
  cls := setupCls C
  cls_gen := I.cls_gen
  m := I.m
  m_span := I.m_span
  KR_val := I.KR_val
  Sexc := I.Sexc
  P r := Additive (setupGal C r)
  Pl := I.Pl
  δ := I.δ
  π := setupPi C
  δ_inj := I.δ_inj
  exact := I.exact
  q := setupQ C
  qbar := setupQbar C
  π_q r hr j := by
    rw [setupQ_eq (I.not_mem hr j).1, setupPi, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
      galToClassGroup_artinClass, classOfIdeal_eq_mk0 _
        (mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot)]
    rfl
  qbar_eq r hr j := by
    rw [setupQ_eq (I.not_mem hr j).1, setupQbar_eq (I.not_mem hr j).2, eq_neg_iff_add_eq_zero,
      ← ofMul_mul, artinClass_mul_eq_one _ _ _ _ _ _ (C.p j : ℤ) ?_, ofMul_one]
    · rw [mul_comm]
      exact C.𝔭_mul j
  x := I.x
  rel := I.rel
  κ := I.κ
  κ_surj := I.κ_surj
  inertia := setupInertia C
  inertia_eq := I.inertia_eq
  decomp := setupDecomp C
  decompBar := setupDecompBar C
  decomp_eq r hr j := by
    rw [setupQ_eq (I.not_mem hr j).1, setupDecomp, decompGal_eq_zpowers _ _ _ _ _
      (I.not_mem hr j).1 (primeToIdeal _ _ (C.𝔭 j) (I.not_mem hr j).1) rfl,
      toAddSubgroup_zpowers]
  decompBar_eq r hr j := by
    rw [setupQbar_eq (I.not_mem hr j).2, setupDecompBar, decompGal_eq_zpowers _ _ _ _ _
      (I.not_mem hr j).2 (primeToIdeal _ _ (C.𝔭bar j) (I.not_mem hr j).2) rfl,
      toAddSubgroup_zpowers]
  frob_kummer := I.frob_kummer

/-! ### `MovingRealization` and `PsiTrivialAt2N` for the genuine `MovingDataK` -/

/-- **`MovingRealization` for the genuine `MovingDataK`, unconditionally** (tex 3565–3595,
3679–3684, 2720, 3528–3531): at every good `r`, for places `P` among the chosen `𝔭_j`, `𝔭̄_j` over
`2N`, with `res` the genuine restriction `G_{K,S_r} → Gal(H_r/K)`. Kind: PROVED. -/
def movingRealization_genuineData (I : GenuineMovingInputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n C)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) {r : ℕ}
    (hr : (movingSettingEcurveS hS hcm hℓ hT I.toMovingDataK).good r)
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) :
    MovingRealization (movingSettingEcurveS hS hcm hℓ hT I.toMovingDataK) r (K := K)
      (S₀ := C.Sr r) P where
  res :=
    { toFun := fun g => Multiplicative.ofAdd (Additive.ofMul
        (ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) g))
      map_one' := by
        change Multiplicative.ofAdd (Additive.ofMul
          (ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) 1)) = 1
        rw [map_one]; rfl
      map_mul' := fun a b => by
        change Multiplicative.ofAdd (Additive.ofMul
          (ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (a * b))) = _
        rw [map_mul]; rfl }
  res_surj := by
    intro x
    obtain ⟨g, hg⟩ := ringClassRes_surjective (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
      (Additive.toMul (Multiplicative.toAdd x))
    refine ⟨g, ?_⟩
    change Multiplicative.ofAdd (Additive.ofMul _) = x
    rw [hg]; rfl
  decomp_at v hv := by
    obtain ⟨j, hj, hvj⟩ := hP v hv
    refine ⟨j, hj, ?_⟩
    rcases hvj with rfl | rfl
    · intro σ
      exact AddSubgroup.mem_sup_left (show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, rfl⟩)
    · intro σ
      exact AddSubgroup.mem_sup_right (show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, rfl⟩)
  placeR := C.placeR r
  placeR_over := I.placeR_over r hr
  inertia_into σ hσ := show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, hσ, rfl⟩
  inertia_onto z hz := by
    obtain ⟨σ, hσ, hσz⟩ := (show Additive.toMul z ∈ inertiaGal (max r 1) (max_one_ne_zero r)
      (C.Sr r) (C.hSr r) (C.placeR r) from hz)
    exact ⟨σ, hσ, by
      change Additive.ofMul (locGal (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
        (C.placeR r) σ) = z
      rw [hσz]; rfl⟩
  place := C.𝔭
  frob_act j hj := by
    have hnm := (I.not_mem hr j).1
    obtain ⟨φ, hφ, hφq⟩ := exists_frobeniusLift_locGal (max r 1) (max_one_ne_zero r) (C.Sr r)
      (C.hSr r) (C.𝔭 j) hnm (primeToIdeal _ _ (C.𝔭 j) hnm) rfl
    refine ⟨φ, hφ, ?_⟩
    change Additive.ofMul (locGal (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭 j) φ) =
      setupQ C r j
    rw [setupQ_eq hnm, hφq]

/-- **`PsiTrivialAt2N` for the genuine moving character** (tex 2720–2735, 3431, 3500–3506,
3694–3701): over the genuine Tate image of `E_ℓ` and the genuine `MovingDataK`, for every finite
avoidance set there is a good prime `r ∉ S` and a moving character `Ψ_i = Ψ ∘ res` of
`G_{K,S_r}`, with `Ψ` from `moving_character_Psi` and `res` the genuine restriction to `Gal(H_r/K)`,
satisfying the norm-cochain chain's `PsiTrivialAt2N` at the chosen places over `2N`.
Kind: PROVED. -/
theorem exists_psiTrivialAt2N_genuineData {i : ℕ} [NeZero i]
    [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (I : GenuineMovingInputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n C)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) (hn : 2 * i ≤ n)
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (S : Finset ℕ) :
    ∃ (r : ℕ) (hr : (movingSettingEcurveS hS hcm hℓ hT I.toMovingDataK).good r), r ∉ S ∧
      r.Prime ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ Ψ : (movingSettingEcurveS hS hcm hℓ hT I.toMovingDataK).P r →+ Additive (Acoef i)ˣ,
        ZInQ.Contrib.CloudB3E2.NormCochain.PsiTrivialAt2N i
          (ZInQ.Contrib.CloudB3E2.NormCochain.movingPi i
            (movingPsiAt Ψ (movingRealization_genuineData I hS hcm hℓ hT hr P hP)))
          (ZInQ.Contrib.CloudB3E2.NormCochain.movingPsi i
            (movingPsiAt Ψ (movingRealization_genuineData I hS hcm hℓ hT hr P hP))) P :=
  exists_psiTrivialAt2N_ecurve hS hcm hℓ hT I.toMovingDataK hn P C.Sr
    (fun _ hr => movingRealization_genuineData I hS hcm hℓ hT hr P hP) B S

end ZInQ.Contrib.CloudB3E1RingClass

import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.GaloisModel
import ZInQKernel.Contrib.Chebotarev.Exists
import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists

/-!
# Theorem 5.3, Lane RC24: the field `chebotarev` from Chebotarev's density theorem

Manuscript `diophantine_zq.tex`, App F: "Chebotarev and continuity make scalar trace and
determinant operators limits of good Hecke and diamond operations" (tex 9663–9669: the trace
action on the finite module is continuous; tex 9666–9668: Chebotarev's theorem in the finite
quotient), the level exponents at the added primes (tex 9524–9548), and the choice of fresh
primes representing given classes "in one sufficiently precise joint quotient" (tex 9919–9921).

The field `chebotarev` of `GaloisTraceModel` (a PRINT input there) is derived here from the
density theorem proved in this repository, `ZInQ.Contrib.ChebFD.C10.frobDense
ZInQ.Contrib.chebotarevExists` (for every finite subextension `E ⊆ ℚ̄`, every `g ∈ G_ℚ` and every
finite set `S`, a Frobenius element at a prime `p ∉ S` agrees with `g` on `E`; from Tau Ceti's
Chebotarev density theorem), and two GLUE hypotheses on the genuine subgroups `N_U = galN …`:

* (a) **openness** (`GalNOpen`, tex 9663–9669): for good `U`, `N_U` contains the fixing subgroup
  of a finite subextension `E ⊆ ℚ̄`; equivalently `N_U` is open in the Krull topology
  (`galN_isOpen_iff`);
* (b) **unramifiedness** (`GalNUnramified`, tex 9524–9548): for good `U` there is a finite set
  `S` (depending on `U`) such that at every good prime `q ∉ U ∪ S` and every maximal ideal `Q` of
  `ℤ̄` containing `q` (these are the primes of `ℤ̄` above `q`), the inertia group
  `I_Q = {σ | ∀ x ∈ ℤ̄, σ x − x ∈ Q}` (Mathlib's `Ideal.inertia`) lies in `N_U`.

Main results (all PROVED):

* `isFrobAt_iff_c10`: the Frobenius notion of this lane (`IsFrobAt`: an arithmetic Frobenius at a
  maximal ideal of `ℤ̄` containing `q`) agrees with the one of the density theorem
  (`ZInQ.Contrib.ChebFD.C10.IsFrobAt`: a congruence modulo a prime of `ℤ̄` over `qℤ`);
* `exists_smul_eq_of_isMaximal`: the maximal ideals of `ℤ̄` above `q` are conjugate under `G_ℚ`
  (Mathlib's transitivity for profinite groups);
* `IsFrobAt.exists_mul_inv_mem_inertia`: two Frobenius elements at `q` (possibly at different
  primes above `q`) differ, up to conjugation, by an inertia element;
* `exists_frob_eq_conj_mul` and `chebotarev_of_density`: under (a) and (b), the statement of the
  field `chebotarev` holds for every choice of Frobenius elements at the good primes;
* `finiteIndex_of_galNOpen`: (a) implies the field `finiteIndex` (`G_ℚ/N_U` finite);
* `GaloisDensityModel`, `GaloisDensityModel.toGaloisTraceModel`: the data of `GaloisTraceModel`
  with (a), (b) in place of the fields `chebotarev` and `finiteIndex`, and the model built from it;
  `GaloisTraceModel.chebotarev_holds_of_density`: in every model, (a) and (b) imply the statement of
  the field `chebotarev`;
* reductions: the character part of (b) holds for every type character reading the types
  (`chars_eq_one_of_mem_inertia`, `galNUnramified_of_trace`), the character part of (a) holds for
  continuous type characters (`galNOpen_of_continuous`; `typChar m` and `stageChar m₁ ℓ₀` are
  continuous), so (a), (b) reduce to the continuity and the unramifiedness of the trace action;
* non-vacuity: `GaloisDensityModel.zero`, `galoisDensityModel_typeData_nonempty`,
  `galoisDensityModel_stage_nonempty` (the zero model over the genuine type data satisfies (a)
  and (b)).

This supplies what the DEPARTURE note of the Galois model module records as missing for deriving
`chebotarev` from the finite form of Čebotarev's theorem: the openness of `N_U` (hypothesis (a))
and the conjugacy modulo `N_U` of the Frobenius elements at a prime unramified in the fixed field
of `N_U` (PROVED here from hypothesis (b)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped Pointwise

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-! ## The two notions of Frobenius element -/

/-- **The Frobenius notion of this lane agrees with the one of the density theorem** (tex
9666–9668, 9936–9942): for a prime `q`, `σ ∈ G_ℚ` is an arithmetic Frobenius element at a maximal
ideal of `ℤ̄` containing `q` (`IsFrobAt`) iff there is a prime `P` of `ℤ̄` with `P ∩ ℤ = qℤ` and
`σ x − x^q ∈ P` for every `x ∈ ℤ̄` (`ZInQ.Contrib.ChebFD.C10.IsFrobAt`). Kind: PROVED (GLUE:
`|ℤ/(Q ∩ ℤ)| = q`; a prime of `ℤ̄` over the maximal ideal `qℤ` is maximal, `ℤ̄/ℤ` being
integral). -/
theorem isFrobAt_iff_c10 {σ : GalQ} {q : ℕ} (hq : q.Prime) :
    IsFrobAt σ q ↔ ZInQ.Contrib.ChebFD.C10.IsFrobAt σ q := by
  constructor
  · rintro ⟨Q, hQ, hqQ, hF⟩
    refine ⟨Q, hQ.isPrime, under_eq_span_of_isMaximal hQ hq hqQ, fun x y hy => ?_⟩
    have hx := hF x
    rw [card_quot_under_of_isMaximal hQ hq hqQ] at hx
    have e : y = σ • x - x ^ q := Subtype.ext (by rw [hy]; push_cast; rfl)
    rw [e]
    exact hx
  · rintro ⟨P, hP, hPq, hh⟩
    have := Fact.mk hq
    have hPmax : P.IsMaximal := by
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ) (S := Zbar) P
      rw [hPq]
      exact Int.ideal_span_isMaximal_of_prime q
    have hqP : ((q : ℤ) : Zbar) ∈ P := by
      have : (q : ℤ) ∈ P.under ℤ := by rw [hPq]; exact Ideal.mem_span_singleton_self _
      rwa [Ideal.under_def, Ideal.mem_comap, eq_intCast] at this
    refine ⟨P, hPmax, hqP, fun x => ?_⟩
    rw [card_quot_under_of_isMaximal hPmax hq hqP]
    exact hh x _ (by push_cast; rfl)

/-! ## Conjugacy of the primes above `q` and of the Frobenius elements -/

/-- **The maximal ideals of `ℤ̄` above a prime `q` are conjugate under `G_ℚ`** (tex 9666–9668:
the Frobenius class at `q` is well defined). Kind: PROVED (Mathlib's
`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`, for the profinite group `G_ℚ` acting
on `ℤ̄` with invariants `ℤ`, `instIsInvariantZbar`; `ℤ̄` discrete, stabilizers open in the Krull
topology). -/
theorem exists_smul_eq_of_isMaximal {Q₁ Q₂ : Ideal Zbar} (h₁ : Q₁.IsMaximal) (h₂ : Q₂.IsMaximal)
    {q : ℕ} (hq : q.Prime) (hq₁ : ((q : ℤ) : Zbar) ∈ Q₁) (hq₂ : ((q : ℤ) : Zbar) ∈ Q₂) :
    ∃ τ : GalQ, Q₂ = τ • Q₁ := by
  have := h₁.isPrime
  have := h₂.isPrime
  let _ : TopologicalSpace Zbar := ⊥
  have : DiscreteTopology Zbar := ⟨rfl⟩
  have : ContinuousSMul GalQ Zbar := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) (x : Qbar) using 1
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ) (G := GalQ) Q₁ Q₂
    (by rw [under_eq_span_of_isMaximal h₁ hq hq₁, under_eq_span_of_isMaximal h₂ hq hq₂])

/-- **Two Frobenius elements at `q` differ, up to conjugation, by an inertia element** (tex
9666–9668): if `σ` and `σ'` are Frobenius elements at `q` (possibly at different maximal ideals
of `ℤ̄` above `q`), there are `τ ∈ G_ℚ` and a maximal ideal `Q` above `q` with
`σ (τ σ' τ⁻¹)⁻¹ ∈ I_Q`. Kind: PROVED (`exists_smul_eq_of_isMaximal`; Mathlib's
`IsArithFrobAt.conj` and `IsArithFrobAt.mul_inv_mem_inertia`). -/
theorem IsFrobAt.exists_mul_inv_mem_inertia {σ σ' : GalQ} {q : ℕ} (hq : q.Prime)
    (hσ : IsFrobAt σ q) (hσ' : IsFrobAt σ' q) :
    ∃ τ : GalQ, ∃ Q : Ideal Zbar, Q.IsMaximal ∧ ((q : ℤ) : Zbar) ∈ Q ∧
      σ * (τ * σ' * τ⁻¹)⁻¹ ∈ Q.inertia GalQ := by
  obtain ⟨Q₁, hQ₁, hq₁, hF₁⟩ := hσ
  obtain ⟨Q₂, hQ₂, hq₂, hF₂⟩ := hσ'
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isMaximal hQ₂ hQ₁ hq hq₂ hq₁
  refine ⟨τ, Q₁, hQ₁, hq₁, ?_⟩
  have h := hF₂.conj τ
  rw [← hτ] at h
  exact hF₁.mul_inv_mem_inertia h

/-! ## The two GLUE hypotheses -/

section Hypotheses

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- **(a) Openness of `N_U`** (tex 9663–9669: the characters are continuous and `g ↦ t(g)F_{U'}`
is continuous on the finite module): for every set `U` of good primes, `N_U = galN chiType t F U`
contains the fixing subgroup of a finite subextension `E ⊆ ℚ̄`, i.e. `N_U` is open in the Krull
topology (`galN_isOpen_iff`). Kind: definition (the GLUE hypothesis (a)). -/
def GalNOpen (T : TypeData L ε) (chiType : GalQ →* Multiplicative L)
    (t : GalQ → M →ₗ[ZMod 2] M) (F : Finset ℕ → M) : Prop :=
  ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) →
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ E.fixingSubgroup ≤ galN chiType t F U

/-- **(b) Unramifiedness of `N_U`** (tex 9524–9548: the forms have level supported on the bad
primes and on `U`; the type fields and the fields `ℚ(√s*)`, `s ∈ U`, are unramified outside the
level and `U`): for every set `U` of good primes there is a finite exceptional set `S` such that at
every good prime `q ∉ U ∪ S` and every maximal ideal `Q` of `ℤ̄` above `q`, every element of the
inertia group `I_Q = {σ | ∀ x ∈ ℤ̄, σ x − x ∈ Q}` lies in `N_U`. Kind: definition (the GLUE
hypothesis (b)). -/
def GalNUnramified (T : TypeData L ε) (chiType : GalQ →* Multiplicative L)
    (t : GalQ → M →ₗ[ZMod 2] M) (F : Finset ℕ → M) : Prop :=
  ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → ∃ S : Finset ℕ, ∀ q : ℕ, T.Good q → q ∉ U → q ∉ S →
    ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q → Q.inertia GalQ ≤ galN chiType t F U

/-- **Hypothesis (a) is openness in the Krull topology**: a subgroup of `G_ℚ` is open iff it
contains the fixing subgroup of a finite subextension of `ℚ̄` (tex 9663–9669). Kind: PROVED
(Mathlib's `krullTopology_mem_nhds_one_iff`, `IntermediateField.fixingSubgroup_isOpen`,
`Subgroup.isOpen_mono`). -/
theorem subgroup_isOpen_iff (H : Subgroup GalQ) :
    IsOpen (H : Set GalQ) ↔
      ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ E.fixingSubgroup ≤ H := by
  constructor
  · intro hH
    obtain ⟨E, hE, hEH⟩ :=
      (krullTopology_mem_nhds_one_iff ℚ Qbar (H : Set GalQ)).1 (hH.mem_nhds H.one_mem)
    exact ⟨E, hE, hEH⟩
  · rintro ⟨E, hE, hEH⟩
    exact Subgroup.isOpen_mono hEH E.fixingSubgroup_isOpen

/-- **(a) for `U` says that `N_U` is open** in the Krull topology (tex 9663–9669). Kind: PROVED
(`subgroup_isOpen_iff`). -/
theorem galN_isOpen_iff (chiType : GalQ →* Multiplicative L) (t : GalQ → M →ₗ[ZMod 2] M)
    (F : Finset ℕ → M) (U : Finset ℕ) :
    IsOpen (galN chiType t F U : Set GalQ) ↔
      ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
        E.fixingSubgroup ≤ galN chiType t F U :=
  subgroup_isOpen_iff _

/-- **An open subgroup of `G_ℚ` has finite index** (tex 9663–9669: the quotient `G_ℚ/N_U` is
finite): if `H` contains the fixing subgroup of a finite subextension `E ⊆ ℚ̄`, then `H` contains
the kernel of the restriction to the Galois closure `K` of `E`, whose image `Gal(K/ℚ)` is finite.
Kind: PROVED (Mathlib's `IntermediateField.restrictNormalHom_ker`, `Subgroup.finiteIndex_ker`). -/
theorem finiteIndex_of_fixingSubgroup_le (H : Subgroup GalQ) (E : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ E] (hEH : E.fixingSubgroup ≤ H) : H.FiniteIndex := by
  set K : IntermediateField ℚ Qbar := IntermediateField.normalClosure ℚ E Qbar with hK
  have : FiniteDimensional ℚ K := normalClosure.is_finiteDimensional ℚ E Qbar
  have : Normal ℚ K := normalClosure.normal ℚ E Qbar
  have hKH : K.fixingSubgroup ≤ H := (E.fixingSubgroup_antitone E.le_normalClosure).trans hEH
  have h := Subgroup.finiteIndex_ker (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) K)
  rw [IntermediateField.restrictNormalHom_ker K] at h
  exact Subgroup.finiteIndex_of_le hKH

/-- **(a) implies the finiteness of `G_ℚ/N_U`** for good `U` (the field `finiteIndex` of
`GaloisTraceModel`, tex 9663–9669). Kind: PROVED (`finiteIndex_of_fixingSubgroup_le`). -/
theorem finiteIndex_of_galNOpen (T : TypeData L ε) {chiType : GalQ →* Multiplicative L}
    {t : GalQ → M →ₗ[ZMod 2] M} {F : Finset ℕ → M} (hopen : GalNOpen T chiType t F)
    (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) : (galN chiType t F U).FiniteIndex := by
  obtain ⟨E, hE, hEN⟩ := hopen U hU
  exact finiteIndex_of_fixingSubgroup_le _ E hEN

end Hypotheses

/-! ## Chebotarev in `G_ℚ/N_U` from the density theorem -/

/-- **Chebotarev in `G_ℚ/H` for an open subgroup `H` unramified outside a finite set** (tex
9666–9668, 9919–9921), the core of `chebotarev_of_density`: let `H ≤ G_ℚ` contain the fixing
subgroup of a finite subextension `E ⊆ ℚ̄` and the inertia groups at the primes above every good
prime `q ∉ U ∪ S`. Then for every `g ∈ G_ℚ` and every finite set `avoid`, for every choice of
Frobenius elements `frob q` at the good primes, there is a good prime `q ∉ avoid` (also `q ∉ U ∪ S`)
with `frob q = h g h⁻¹ n` for some `h ∈ G_ℚ` and `n ∈ H`. Kind: PROVED (the density theorem
`ZInQ.Contrib.ChebFD.C10.frobDense ZInQ.Contrib.chebotarevExists`, applied to the Galois closure
`K` of `E` and to `avoid ∪ S ∪ U` and the primes of the modulus; `isFrobAt_iff_c10`;
`IsFrobAt.exists_mul_inv_mem_inertia`; the fixing subgroup of `K` is normal,
`InfiniteGalois.normal_iff_isGalois`). -/
theorem exists_frob_eq_conj_mul (T : TypeData L ε) {frob : ℕ → GalQ}
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) (H : Subgroup GalQ) (U S : Finset ℕ)
    (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E] (hEH : E.fixingSubgroup ≤ H)
    (hunr : ∀ q : ℕ, T.Good q → q ∉ U → q ∉ S →
      ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q → Q.inertia GalQ ≤ H)
    (g : GalQ) (avoid : Finset ℕ) :
    ∃ q h, ∃ n ∈ H, T.Good q ∧ q ∉ avoid ∧ q ∉ U ∧ q ∉ S ∧ frob q = h * g * h⁻¹ * n := by
  -- the Galois closure `K` of `E`; its fixing subgroup is normal and lies in `H`
  set K : IntermediateField ℚ Qbar := IntermediateField.normalClosure ℚ E Qbar with hK
  have : FiniteDimensional ℚ K := normalClosure.is_finiteDimensional ℚ E Qbar
  have : Normal ℚ K := normalClosure.normal ℚ E Qbar
  have : IsGalois ℚ K := ⟨⟩
  have hKn : K.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois K).mpr inferInstance
  have hKH : K.fixingSubgroup ≤ H := (E.fixingSubgroup_antitone E.le_normalClosure).trans hEH
  -- the density theorem: a Frobenius element `h'` at a prime `p` outside the bad set, `h' = g`
  -- on `K`
  obtain ⟨h', p, hp, hpbad, hh', hh'K⟩ := ZInQ.Contrib.ChebFD.C10.frobDense
    ZInQ.Contrib.chebotarevExists (avoid ∪ S ∪ U ∪ T.m.primeFactors) K inferInstance g
  simp only [Finset.mem_union, not_or] at hpbad
  obtain ⟨⟨⟨hpa, hpS⟩, hpU⟩, hpm⟩ := hpbad
  have hgood : T.Good p := ⟨hp, (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd =>
    hpm (Nat.mem_primeFactors.mpr ⟨hp, hd, T.m_pos.ne'⟩)⟩
  -- compare `frob p` with `h'`: `frob p = ι (τ h' τ⁻¹)` with `ι` in an inertia group above `p`
  obtain ⟨τ, Q, hQ, hpQ, hι⟩ := IsFrobAt.exists_mul_inv_mem_inertia hp (hfrob p hgood)
    ((isFrobAt_iff_c10 hp).mpr hh')
  have hιH : frob p * (τ * h' * τ⁻¹)⁻¹ ∈ H := hunr p hgood hpU hpS Q hQ hpQ hι
  -- `h' = g m` with `m` fixing `K`, and `τ m τ⁻¹` fixes `K` (normality)
  have hm : g⁻¹ * h' ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [AlgEquiv.mul_apply, hh'K x hx, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hm' : τ * (g⁻¹ * h') * τ⁻¹ ∈ H := hKH (hKn.conj_mem _ hm τ)
  refine ⟨p, frob p * (τ * h' * τ⁻¹)⁻¹ * τ,
    frob p * (τ * h' * τ⁻¹)⁻¹ * (τ * (g⁻¹ * h') * τ⁻¹), H.mul_mem hιH hm', hgood, hpa, hpU, hpS,
    by group⟩

/-- **The field `chebotarev` of `GaloisTraceModel` from Chebotarev's density theorem** (tex
9663–9669, 9666–9668, 9919–9921, 9524–9548): under (a) openness (`GalNOpen`) and (b)
unramifiedness (`GalNUnramified`) of the subgroups `N_U`, for every choice of Frobenius elements
`frob q` at the good primes, every class of `G_ℚ/N_U` (`U` good) is the Frobenius class of a good
prime outside any finite set — verbatim the statement of the field `chebotarev`. Kind: PROVED
(`exists_frob_eq_conj_mul`: the density theorem `ZInQ.Contrib.ChebFD.C10.frobDense
ZInQ.Contrib.chebotarevExists`, proved in this repository from the Chebotarev density theorem of
Tau Ceti). -/
theorem chebotarev_of_density (T : TypeData L ε) {chiType : GalQ →* Multiplicative L}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {t : GalQ → M →ₗ[ZMod 2] M}
    {F : Finset ℕ → M} {frob : ℕ → GalQ} (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hopen : GalNOpen T chiType t F) (hunr : GalNUnramified T chiType t F) :
    ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : GalQ) (avoid : Finset ℕ),
      ∃ q h, ∃ n ∈ galN chiType t F U, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n := by
  intro U hU g avoid
  obtain ⟨E, hE, hEN⟩ := hopen U hU
  obtain ⟨S, hS⟩ := hunr U hU
  obtain ⟨q, h, n, hn, hq, hqa, -, -, hf⟩ :=
    exists_frob_eq_conj_mul T hfrob (galN chiType t F U) U S E hEN hS g avoid
  exact ⟨q, h, n, hn, hq, hqa, hf⟩

/-! ## The model with (a), (b) in place of `chebotarev` -/

/-- **The genuine Galois trace model with openness and unramifiedness in place of Chebotarev**
(tex 9641–9771, 9905–9953): the data and fields of `GaloisTraceModel`, verbatim, except that the
PRINT field `chebotarev` and the GLUE field `finiteIndex` are replaced by the GLUE hypotheses (a)
`isOpen` (`GalNOpen`, tex 9663–9669) and (b) `unramified` (`GalNUnramified`, tex 9524–9548);
`chebotarev` and `finiteIndex` are then PROVED (`chebotarev_of_density`, `finiteIndex_of_galNOpen`,
`GaloisDensityModel.toGaloisTraceModel`). Kinds of the other fields as in `GaloisTraceModel`:
`frob_spec` definition; `trace_mul`, `det_orbit`, `two_fresh`, `trace_one`, `t_class` ELLIOT (tex
9705–9745, 9762–9771); `kummer` GLUE (tex 9745–9750); `reading` ELLIOT (tex 9671–9704); `o12`
ELLIOT (tex 9905–9918). -/
structure GaloisDensityModel (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) where
  /-- the reduced integral trace module (characteristic two, tex 9663–9669, 9893–9899) -/
  M : Type
  [instM : AddCommGroup M]
  [instMod : Module (ZMod 2) M]
  /-- the scalar trace operators `t(g)` (tex 9762–9771) -/
  t : GalQ → M →ₗ[ZMod 2] M
  /-- the determinant (diamond) operators `d(g)` (tex 9762–9771) -/
  d : GalQ → M →ₗ[ZMod 2] M
  /-- the reduced forms `F_U = θ H_U` (tex 9672) -/
  F : Finset ℕ → M
  /-- the coefficient-one functional on the `U`-forms (tex 9688–9695) -/
  read : Finset ℕ → M →ₗ[ZMod 2] ZMod 2
  /-- the Frobenius elements in `G_ℚ` -/
  frob : ℕ → GalQ
  /-- definition: `frob q` is a genuine arithmetic Frobenius element at every good prime `q` -/
  frob_spec : ∀ q, T.Good q → IsFrobAt (frob q) q
  /-- ELLIOT (RC12, tex 9729–9737): `t(g)t(h) = t(gh) + d(h)t(gh⁻¹)` -/
  trace_mul : ∀ g h (x : M), t g (t h x) = t (g * h) x + d h (t (g * h⁻¹) x)
  /-- ELLIOT (RC12, tex 9719–9733): `d` acts trivially on the trace orbit of `F_U` -/
  det_orbit : ∀ U u v, d u (t v (F U)) = t v (F U)
  /-- ELLIOT (RC12, tex 9741–9745): two fresh traces vanish -/
  two_fresh : ∀ U g h, t g (t h (F U)) = 0
  /-- ELLIOT (RC12, tex 9739): `t(1) = 2` -/
  trace_one : ∀ x, t 1 x = (2 : ZMod 2) • x
  /-- ELLIOT (tex 9762–9771; tex 9666–9668): `t` is a class function -/
  t_class : ∀ g h, t (h * g * h⁻¹) = t g
  /-- GLUE (Kummer theory for the several radicals, tex 9745–9750) -/
  kummer : ∀ U g, chiType g = 1 → (∀ s ∈ U, bitChar s g = 1) →
    g ∈ Subgroup.closure (sqSet GalQ) ⊔ galN chiType t F U
  /-- GLUE (a) (continuity, tex 9663–9669): `N_U` is open, `U` good -/
  isOpen : GalNOpen T chiType t F
  /-- GLUE (b) (level and unramifiedness, tex 9524–9548): `N_U` contains the inertia groups
  above the good primes outside `U` and a finite set, `U` good -/
  unramified : GalNUnramified T chiType t F
  /-- ELLIOT (tex 9671–9704): the reading of a fresh vertex -/
  reading : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
    (insert q U).card ≤ B → R (insert q U) = read U (t (frob q) (F U))
  /-- ELLIOT ((O.12) at coefficient one, tex 9905–9918) -/
  o12 : ∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : GalQ,
    ∃ (τ φ : GalQ) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
      chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s τ = 1) ∧
      bitChar p τ = Multiplicative.ofAdd 1 ∧
      chiType φ = Multiplicative.ofAdd (T.typ p) ∧
      (∀ s ∈ U, s ≠ p → bitChar s φ = Multiplicative.ofAdd (legBit p s)) ∧
      ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) * read (U.erase p) (t (g * τ * φ) (F (U.erase p))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) * read (U.erase p) (t (g * φ) (F (U.erase p))) =
        read U (t (g * τ) (F U)) - read U (t g (F U))

attribute [instance] GaloisDensityModel.instM GaloisDensityModel.instMod

/-- **The genuine Galois trace model from (a), (b) and the density theorem** (tex 9663–9669,
9666–9668): the field `chebotarev` is `chebotarev_of_density`, the field `finiteIndex` is
`finiteIndex_of_galNOpen`, all other fields are copied. Kind: PROVED (definition). -/
def GaloisDensityModel.toGaloisTraceModel {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {B : ℕ} {chiType : GalQ →* Multiplicative L}
    (X : GaloisDensityModel T R ap B chiType) : GaloisTraceModel T R ap B chiType where
  M := X.M
  t := X.t
  d := X.d
  F := X.F
  read := X.read
  frob := X.frob
  frob_spec := X.frob_spec
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit
  two_fresh := X.two_fresh
  trace_one := X.trace_one
  t_class := X.t_class
  kummer := X.kummer
  finiteIndex := finiteIndex_of_galNOpen T X.isOpen
  chebotarev := chebotarev_of_density T X.frob_spec X.isOpen X.unramified
  reading := X.reading
  o12 := X.o12

/-- **In every genuine Galois trace model, the field `chebotarev` is implied by (a) and (b)**
(tex 9663–9669, 9666–9668, 9524–9548): if the subgroups `N_U` of `X` are open and unramified
outside `U` and a finite set, the statement of the field `chebotarev` follows from the density
form of Chebotarev's theorem (so the PRINT input `chebotarev` may be replaced by the GLUE
hypotheses (a), (b)). Kind: PROVED (`chebotarev_of_density`). -/
theorem GaloisTraceModel.chebotarev_holds_of_density {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {B : ℕ} {chiType : GalQ →* Multiplicative L}
    (X : GaloisTraceModel T R ap B chiType) (hopen : GalNOpen T chiType X.t X.F)
    (hunr : GalNUnramified T chiType X.t X.F) :
    ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : GalQ) (avoid : Finset ℕ),
      ∃ q h, ∃ n ∈ X.N U, T.Good q ∧ q ∉ avoid ∧ X.frob q = h * g * h⁻¹ * n :=
  chebotarev_of_density T X.frob_spec hopen hunr

/-- **The model built from (a), (b) keeps the data**: `toGaloisTraceModel` has the same module,
operators, forms, readings and Frobenius elements (no tex line). Kind: PROVED (definition). -/
theorem GaloisDensityModel.toGaloisTraceModel_frob {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {B : ℕ} {chiType : GalQ →* Multiplicative L}
    (X : GaloisDensityModel T R ap B chiType) : X.toGaloisTraceModel.frob = X.frob := rfl

/-! ## Reductions of (a) and (b) to the trace action, and non-vacuity -/

/-- **A Frobenius element times an inertia element is a Frobenius element** at the same maximal
ideal (tex 9666–9668: the Frobenius class at an unramified prime is a coset of inertia). Kind:
PROVED (`σ` maps `Q` into `Q`, Mathlib's `AlgHom.IsArithFrobAt.le_comap`). -/
theorem isArithFrobAt_mul_of_mem_inertia {σ ι : GalQ} {Q : Ideal Zbar}
    (hσ : IsArithFrobAt ℤ σ Q) (hι : ι ∈ Q.inertia GalQ) : IsArithFrobAt ℤ (σ * ι) Q := by
  intro x
  have h1 : σ • x - x ^ Nat.card (ℤ ⧸ Q.under ℤ) ∈ Q := hσ x
  have h2 : σ • (ι • x - x) ∈ Q := Ideal.mem_comap.mp (hσ.le_comap (Ideal.mem_inertia.mp hι x))
  have e : (σ * ι) • x - x ^ Nat.card (ℤ ⧸ Q.under ℤ) =
      σ • (ι • x - x) + (σ • x - x ^ Nat.card (ℤ ⧸ Q.under ℤ)) := by
    rw [smul_sub, mul_smul]
    abel
  change (σ * ι) • x - x ^ Nat.card (ℤ ⧸ Q.under ℤ) ∈ Q
  rw [e]
  exact Q.add_mem h2 h1

/-- **The characters are unramified at the good primes outside `U`** (tex 9524–9548, 9745–9750):
for a type character reading the types (`IsTypeChar`), a good prime `q ∉ U`, `U` a set of good
primes, and `ι` in the inertia group of a maximal ideal `Q` of `ℤ̄` above `q`, `χ_type(ι) = 1` and
`χ_s(ι) = 1` for `s ∈ U`. Kind: PROVED (with `φ` a Frobenius element at `Q`, `φι` is one too,
`isArithFrobAt_mul_of_mem_inertia`; both read the type of `q` and the bits `(q/s)`). -/
theorem chars_eq_one_of_mem_inertia (T : TypeData L ε) {chiType : GalQ →* Multiplicative L}
    (htyp : IsTypeChar T chiType) {U : Finset ℕ} (hU : ∀ s ∈ U, T.Good s) {q : ℕ}
    (hq : T.Good q) (hqU : q ∉ U) {Q : Ideal Zbar} (hQ : Q.IsMaximal)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) {ι : GalQ} (hι : ι ∈ Q.inertia GalQ) :
    chiType ι = 1 ∧ ∀ s ∈ U, bitChar s ι = 1 := by
  obtain ⟨φ, hφ⟩ := exists_isArithFrobAt hQ hq.1 hqQ
  have h1 : IsFrobAt φ q := ⟨Q, hQ, hqQ, hφ⟩
  have h2 : IsFrobAt (φ * ι) q := ⟨Q, hQ, hqQ, isArithFrobAt_mul_of_mem_inertia hφ hι⟩
  refine ⟨?_, fun s hs => ?_⟩
  · have e := htyp q _ hq h2
    rw [map_mul, htyp q _ hq h1] at e
    exact mul_left_cancel (e.trans (mul_one _).symm)
  · have hqs : q ≠ s := fun h => hqU (h ▸ hs)
    have e := bitChar_of_good T hq (hU s hs) hqs h2
    rw [map_mul, bitChar_of_good T hq (hU s hs) hqs h1] at e
    exact mul_left_cancel (e.trans (mul_one _).symm)

/-- **(b) reduces to the trace action**: for a type character reading the types, the hypothesis
`GalNUnramified` follows from the unramifiedness of the trace action alone (inertia at the good
primes outside `U` and a finite set does not move `t(·)F_{U'}`, `U' ⊆ U`, tex 9524–9548); the
character part of `N_U` is unramified there (`chars_eq_one_of_mem_inertia`). Kind: PROVED. -/
theorem galNUnramified_of_trace (T : TypeData L ε) {chiType : GalQ →* Multiplicative L}
    (htyp : IsTypeChar T chiType) {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {t : GalQ → M →ₗ[ZMod 2] M} {F : Finset ℕ → M}
    (htr : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → ∃ S : Finset ℕ, ∀ q : ℕ, T.Good q → q ∉ U →
      q ∉ S → ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q → ∀ ι ∈ Q.inertia GalQ,
        ∀ g : GalQ, ∀ U' ⊆ U, t (g * ι) (F U') = t g (F U')) :
    GalNUnramified T chiType t F := by
  intro U hU
  obtain ⟨S, hS⟩ := htr U hU
  refine ⟨S, fun q hq hqU hqS Q hQ hqQ ι hι => ?_⟩
  obtain ⟨h1, h2⟩ := chars_eq_one_of_mem_inertia T htyp hU hq hqU hQ hqQ hι
  exact mem_galN.mpr ⟨h1, h2, hS q hq hqU hqS Q hQ hqQ ι hι⟩

/-- **The characters `χ_s`, `s ∈ U`, are continuous**: they are trivial on the fixing subgroup of
`ℚ(√s* : s ∈ U)`, a finite subextension of `ℚ̄` (tex 9745–9750). Kind: PROVED. -/
theorem exists_fixingSubgroup_le_ker_bitChar (U : Finset ℕ) :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ ∈ E.fixingSubgroup, ∀ s ∈ U, bitChar s σ = 1 := by
  refine ⟨IntermediateField.adjoin ℚ (↑(U.image fun s => sqrtQbar (sstar s)) : Set Qbar),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x,
    fun σ hσ s hs => ?_⟩
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ (sqrtQbar (sstar s))
    (IntermediateField.subset_adjoin _ _ (by
      rw [Finset.coe_image]
      exact Set.mem_image_of_mem _ hs))
  rw [bitChar_apply, sqrtChar_apply, ite_eq_left hfix]

/-- **(a) reduces to the continuity of the type character and of the trace action** (tex
9663–9669): if `χ_type` is trivial on the fixing subgroup of a finite subextension `E₀ ⊆ ℚ̄`, and
for every set `U` of good primes the elements fixing some finite subextension `E₁` do not move
`t(·)F_{U'}`, `U' ⊆ U`, then `GalNOpen` holds (with `E = E₀ E₁ ℚ(√s* : s ∈ U)`). Kind: PROVED
(`exists_fixingSubgroup_le_ker_bitChar`). -/
theorem galNOpen_of_continuous (T : TypeData L ε) {chiType : GalQ →* Multiplicative L}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {t : GalQ → M →ₗ[ZMod 2] M}
    {F : Finset ℕ → M}
    (hchi : ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ ∈ E.fixingSubgroup, chiType σ = 1)
    (htr : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → ∃ E : IntermediateField ℚ Qbar,
      FiniteDimensional ℚ E ∧ ∀ σ ∈ E.fixingSubgroup, ∀ g : GalQ, ∀ U' ⊆ U,
        t (g * σ) (F U') = t g (F U')) :
    GalNOpen T chiType t F := by
  intro U hU
  obtain ⟨E₀, hE₀, h₀⟩ := hchi
  obtain ⟨E₁, hE₁, h₁⟩ := htr U hU
  obtain ⟨E₂, hE₂, h₂⟩ := exists_fixingSubgroup_le_ker_bitChar U
  refine ⟨E₀ ⊔ E₁ ⊔ E₂, inferInstance, fun σ hσ => mem_galN.mpr ⟨?_, ?_, ?_⟩⟩
  · exact h₀ σ (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans le_sup_left) hσ)
  · exact h₂ σ (IntermediateField.fixingSubgroup_antitone le_sup_right hσ)
  · exact h₁ σ (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans le_sup_left) hσ)

/-- **The type character `typChar m` is continuous**: it is trivial on the fixing subgroup of
`ℚ(ζ_m)` (tex 2015–2025, 9663–9669). Kind: PROVED (`cycChar_spec`: an element fixing a
primitive `m`-th root of unity has cyclotomic character `1`). -/
theorem exists_fixingSubgroup_le_ker_typChar (m : ℕ) [NeZero m] :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ ∈ E.fixingSubgroup, typChar m σ = 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar m
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨IntermediateField.adjoin ℚ {ζ},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ),
    fun σ hσ => ?_⟩
  have hfix : σ ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ ζ
    (IntermediateField.mem_adjoin_simple_self ℚ ζ)
  set c : ZMod m := ((cycChar m σ : (ZMod m)ˣ) : ZMod m) with hc
  have h1 : ζ ^ c.val = ζ ^ (1 % m) := by
    rw [← cycChar_spec m σ ζ hζ.pow_eq_one, hfix, hζ.eq_orderOf, pow_mod_orderOf, pow_one]
  have h2 : c.val = 1 % m := hζ.pow_inj (ZMod.val_lt c) (Nat.mod_lt _ hm0) h1
  have h3 : cycChar m σ = 1 := by
    apply Units.ext
    rw [← hc, ← ZMod.natCast_zmod_val c, h2, ZMod.natCast_mod, Nat.cast_one, Units.val_one]
  rw [typChar_apply, h3]
  rfl

/-- **The stage type character is continuous**: `stageChar m₁ ℓ₀ = (typChar m₁, χ_{ℓ₀})` is trivial
on the fixing subgroup of `ℚ(ζ_{m₁}, √ℓ₀*)` (tex 2015–2025, 9663–9669). Kind: PROVED
(`exists_fixingSubgroup_le_ker_typChar`, `exists_fixingSubgroup_le_ker_bitChar`). -/
theorem exists_fixingSubgroup_le_ker_stageChar (m₁ ℓ₀ : ℕ) [NeZero m₁] :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ ∈ E.fixingSubgroup, stageChar m₁ ℓ₀ σ = 1 := by
  obtain ⟨E₁, hE₁, h₁⟩ := exists_fixingSubgroup_le_ker_typChar m₁
  obtain ⟨E₂, hE₂, h₂⟩ := exists_fixingSubgroup_le_ker_bitChar {ℓ₀}
  refine ⟨E₁ ⊔ E₂, inferInstance, fun σ hσ => ?_⟩
  have e1 := h₁ σ (IntermediateField.fixingSubgroup_antitone le_sup_left hσ)
  have e2 := h₂ σ (IntermediateField.fixingSubgroup_antitone le_sup_right hσ) ℓ₀
    (Finset.mem_singleton_self ℓ₀)
  rw [stageChar_apply, e1, e2]
  rfl

/-- **Non-vacuity of (a) and (b)**: for every type data and every continuous type character
reading the types, the zero model (zero module, as in `GaloisTraceModel.zero`) has open and
unramified subgroups `N_U`, so it is a `GaloisDensityModel` (the other fields as in
`GaloisTraceModel.zero`; `N_U` is the common kernel of the characters). Kind: PROVED
(`galNOpen_of_continuous`, `galNUnramified_of_trace`, `frobeniusExists`). -/
def GaloisDensityModel.zero (T : TypeData L ε) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType)
    (hchi : ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ ∈ E.fixingSubgroup, chiType σ = 1) :
    GaloisDensityModel T (fun _ => 0) ap B chiType where
  M := PUnit
  t _ := 0
  d _ := 0
  F _ := PUnit.unit
  read _ := 0
  frob := chooseFrob frobeniusExists
  frob_spec _ hq := chooseFrob_spec frobeniusExists hq.1
  trace_mul _ _ _ := Subsingleton.elim _ _
  det_orbit _ _ _ := Subsingleton.elim _ _
  two_fresh _ _ _ := Subsingleton.elim _ _
  trace_one _ := Subsingleton.elim _ _
  t_class _ _ := rfl
  kummer _ _ h1 h2 := Subgroup.mem_sup_right (mem_galN_of_subsingleton.mpr ⟨h1, h2⟩)
  isOpen := galNOpen_of_continuous T hchi
    fun _ _ => ⟨⊥, inferInstance, fun _ _ _ _ _ => Subsingleton.elim _ _⟩
  unramified := galNUnramified_of_trace T htyp
    fun _ _ => ⟨∅, fun _ _ _ _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _⟩
  reading := (GaloisTraceModel.zero frobeniusExists T ap B chiType htyp).reading
  o12 := (GaloisTraceModel.zero frobeniusExists T ap B chiType htyp).o12

/-- **The zero `GaloisDensityModel` over the genuine residue-class type data** `typeData m`, with
the genuine type character `typChar m` (tex 2015–2025). Kind: PROVED (`GaloisDensityModel.zero`,
`isTypeChar_typeData`, `exists_fixingSubgroup_le_ker_typChar`). -/
def GaloisDensityModel.zeroTypeData (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ)
    (B : ℕ) : GaloisDensityModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  GaloisDensityModel.zero _ ap B _ (isTypeChar_typeData m hm h4)
    (exists_fixingSubgroup_le_ker_typChar m)

/-- **`GaloisDensityModel` is inhabited over `typeData m`** (no tex line); its
`toGaloisTraceModel` is a genuine Galois trace model whose field `chebotarev` comes from the
density theorem. Kind: PROVED (`GaloisDensityModel.zeroTypeData`). -/
theorem galoisDensityModel_typeData_nonempty (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m)
    (ap : ℕ → ℤ) (B : ℕ) :
    Nonempty (GaloisDensityModel (typeData m hm h4) (fun _ => 0) ap B (typChar m)) :=
  ⟨GaloisDensityModel.zeroTypeData m hm h4 ap B⟩

/-- **The zero `GaloisDensityModel` over stage type data** (types `(sqClassOf m₁ p, legBit p ℓ₀)`
at the modulus `m₁ ℓ₀`, `ℓ₀` an odd prime), with the stage type character (tex 2015–2025). Kind:
PROVED (`GaloisDensityModel.zero`, `isTypeChar_stage`, `exists_fixingSubgroup_le_ker_stageChar`). -/
def GaloisDensityModel.zeroStage {m₁ ℓ₀ : ℕ} [NeZero m₁] {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2}
    (T : TypeData (SqClass m₁ × ZMod 2) ε₁) (hTm : T.m = m₁ * ℓ₀)
    (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀)) (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2)
    (ap : ℕ → ℤ) (B : ℕ) : GaloisDensityModel T (fun _ => 0) ap B (stageChar m₁ ℓ₀) :=
  GaloisDensityModel.zero T ap B _ (isTypeChar_stage T hTm hTtyp hℓ₀ hℓ₀2)
    (exists_fixingSubgroup_le_ker_stageChar m₁ ℓ₀)

/-- **`GaloisDensityModel` is inhabited over stage type data** (no tex line). Kind: PROVED
(`GaloisDensityModel.zeroStage`). -/
theorem galoisDensityModel_stage_nonempty {m₁ ℓ₀ : ℕ} [NeZero m₁]
    {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2} (T : TypeData (SqClass m₁ × ZMod 2) ε₁)
    (hTm : T.m = m₁ * ℓ₀) (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀))
    (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2) (ap : ℕ → ℤ) (B : ℕ) :
    Nonempty (GaloisDensityModel T (fun _ => 0) ap B (stageChar m₁ ℓ₀)) :=
  ⟨GaloisDensityModel.zeroStage T hTm hTtyp hℓ₀ hℓ₀2 ap B⟩

end ZInQ.Manuscript.RC.AddressGenuine

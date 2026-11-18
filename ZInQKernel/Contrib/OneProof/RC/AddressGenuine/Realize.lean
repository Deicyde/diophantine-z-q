import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Types
import ZInQKernel.Contrib.OneProof.RC.Wiring.Address
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Realize

/-!
# Lane RC24: the genuine prime realization of the address construction

Manuscript `diophantine_zq.tex`: Definition `ex:sec7-typed-graph` (tex 2015–2066), Lemma
`ex:sec7-realization` and its proof (tex 2151–2174), and Proposition `ex:app-final-family` with
its proof (App G, tex 10792–10861; in particular 10785–10788 and 10825–10828: "Realize its
prescribed forward residue bits by distinct primes using CRT and Dirichlet; quadratic reciprocity
supplies the reverse bits").

The common alphabet of the address construction is `CommonL m k hk`: the `K`-split squareclasses
modulo the fixed modulus `m` (`4|k| ∣ m`, `K = ℚ(√k)`), together with the residue bit at the moving
theta prime `ℓ₀` (a coefficient prime and exclusion of the stage, tex 10845–10848). Its sign
coordinate `commonSign` is `ε = (p − 1)/2 mod 2`, read on the squareclass.

`RealizesAt m k hk ℓ₀ avoid Δ D` says that `D = ∏ q^*` over a prime realization of the typed graph
`Δ`: distinct primes prime to `m`, different from `ℓ₀` and outside `avoid`, with the prescribed
squareclasses, bits at `ℓ₀` and mutual residue bits.

Main results (all PROVED):
* `exists_family_realizesAt` — conjunct 15 of lane RC0's `AddressPackage`: a compatible typed
  graph with nonzero activations is realized, at every nonzero address, by one admissible family
  (CRT and Dirichlet through lane RC2's `finite_realization_nat`, reciprocity for the reverse bits);
* `realizesAt_omega` — `ω(D) = |V(Δ)|`;
* `realizesAt_squarefree_coprime`, `realizesAt_not_dvd_ell` — `D` squarefree, prime to the prime
  members of the avoidance set, a unit modulo `m`, prime to `ℓ₀`;
* `realizesAt_total_zero`, `realizesAt_total_zero_iff` — total type zero is exactly the filter
  `D > 0`, `D` a square modulo `m` and modulo `ℓ₀`;
* `RealizesWith.isReal_odd`, `RealizesWith.isReal_even`, `RealizesWith.jacobiSym_eq_one` — the
  odd and even readings of one realization, for batch 3's `TypeData`/`IsReal`;
* `realizesAt_of_primes` — conversely, a finite set of admissible primes realizes its own
  configuration `primeCommonConfig` (used for seeds).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open Finset

/-! ### The common alphabet and realizations -/

/-- **The common alphabet** (Definition `ex:sec7-typed-graph`, tex 2015–2030, 2060–2065; App G
tex 10525–10532; kind: definition): the `K`-split squareclasses modulo `m`, and the Legendre bit
at the moving theta prime. -/
abbrev CommonL (m : ℕ) (k : ℤ) (hk : 4 * k.natAbs ∣ m) : Type := KSplitClass m k hk × ZMod 2

/-- **The sign coordinate of the common alphabet** `ε_v = (p_v − 1)/2 mod 2` (tex 2037–2039;
kind: definition), read on the squareclass. -/
def commonSign (m : ℕ) (h4 : 4 ∣ m) (k : ℤ) (hk : 4 * k.natAbs ∣ m) : CommonL m k hk →+ ZMod 2 :=
  (signChar m h4).comp ((kSplitSub m k hk).subtype.comp (AddMonoidHom.fst _ _))

/-- **A prime realization of a typed graph, with product `D = ∏ q^*`** (Lemma
`ex:sec7-realization`, tex 2151–2174; Definition `ex:sec7-typed-graph`, tex 2031–2047; App G tex
10795–10828; kind: definition): distinct primes `f v`, prime to `m`, different from the theta
prime `ℓ₀` and outside `avoid`, with the prescribed squareclass and bit at `ℓ₀`, the residue bits
`z_{vw} = 0/1 ⟺ (f v / f w) = ±1`, and `D = ∏_v (f v)^*`. -/
def RealizesAt (m : ℕ) (k : ℤ) (hk : 4 * k.natAbs ∣ m) (ℓ₀ : ℕ) (avoid : Finset ℕ)
    (Δ : Config (CommonL m k hk)) (D : ℤ) : Prop :=
  ∃ f : ℕ → ℕ, Set.InjOn f Δ.V ∧
    (∀ v ∈ Δ.V, (f v).Prime ∧ Nat.Coprime (f v) m ∧ f v ≠ ℓ₀ ∧ f v ∉ avoid ∧
      sqClassOf m (f v) = ((Δ.t v).1 : SqClass m) ∧ legBit (f v) ℓ₀ = (Δ.t v).2) ∧
    (∀ v ∈ Δ.V, ∀ w ∈ Δ.V, v ≠ w → legBit (f v) (f w) = Δ.z v w) ∧
    D = ∏ v ∈ Δ.V, qstar (f v)

/-- The body of `RealizesAt` for a given witness `f` (kind: definition). -/
def RealizesWith (m : ℕ) (k : ℤ) (hk : 4 * k.natAbs ∣ m) (ℓ₀ : ℕ) (avoid : Finset ℕ)
    (Δ : Config (CommonL m k hk)) (D : ℤ) (f : ℕ → ℕ) : Prop :=
  Set.InjOn f Δ.V ∧
    (∀ v ∈ Δ.V, (f v).Prime ∧ Nat.Coprime (f v) m ∧ f v ≠ ℓ₀ ∧ f v ∉ avoid ∧
      sqClassOf m (f v) = ((Δ.t v).1 : SqClass m) ∧ legBit (f v) ℓ₀ = (Δ.t v).2) ∧
    (∀ v ∈ Δ.V, ∀ w ∈ Δ.V, v ≠ w → legBit (f v) (f w) = Δ.z v w) ∧
    D = ∏ v ∈ Δ.V, qstar (f v)

/-- `RealizesAt` is the existence of a witness (kind: PROVED, by definition). -/
theorem realizesAt_iff {m : ℕ} {k : ℤ} {hk : 4 * k.natAbs ∣ m} {ℓ₀ : ℕ} {avoid : Finset ℕ}
    {Δ : Config (CommonL m k hk)} {D : ℤ} :
    RealizesAt m k hk ℓ₀ avoid Δ D ↔ ∃ f, RealizesWith m k hk ℓ₀ avoid Δ D f := Iff.rfl

/-- The sign coordinate of a type is the sign character of its squareclass (kind: PROVED). -/
theorem commonSign_apply {m : ℕ} (h4 : 4 ∣ m) {k : ℤ} {hk : 4 * k.natAbs ∣ m}
    (x : CommonL m k hk) : commonSign m h4 k hk x = signChar m h4 (x.1 : SqClass m) := rfl

/-! ### Auxiliary arithmetic -/

namespace RealizeAux

/-- An element of `ZMod 2` is `0` or `1` (kind: PROVED). -/
theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A prime prime to `m`, `4 ∣ m`, is odd (kind: PROVED). -/
theorem ne_two_of_coprime_four {m p : ℕ} (h4 : 4 ∣ m) (hp : Nat.Coprime p m) : p ≠ 2 :=
  ne_two_of_coprime_even (dvd_trans ⟨2, by norm_num⟩ h4) hp

/-- A natural number prime to `m` is a unit modulo `m` (kind: PROVED). -/
theorem isUnit_natCast_of_coprime {m p : ℕ} (h : Nat.Coprime p m) :
    IsUnit (((p : ℕ) : ℤ) : ZMod m) := by
  rw [Int.cast_natCast]
  exact (ZMod.isUnit_iff_coprime p m).mpr h

/-- The squareclass of a natural number in the class of a unit (kind: PROVED). -/
theorem sqClassOf_natCast_eq {m p : ℕ} {u : (ZMod m)ˣ} (h : ((p : ℕ) : ZMod m) = u) :
    sqClassOf m (p : ℤ) = sqMk u := by
  have hu : IsUnit (((p : ℕ) : ℤ) : ZMod m) := by rw [Int.cast_natCast, h]; exact u.isUnit
  rw [sqClassOf_of_isUnit hu]
  congr 1
  ext
  rw [IsUnit.unit_spec, Int.cast_natCast, h]

/-- The squareclass of `1` is zero (kind: PROVED). -/
theorem sqClassOf_one (m : ℕ) : sqClassOf m 1 = 0 := by
  have hu : IsUnit ((1 : ℤ) : ZMod m) := by rw [Int.cast_one]; exact isUnit_one
  have h := sqClassOf_mul hu hu
  rw [mul_one] at h
  rw [h, sqClass_add_self]

/-- Squareclasses of products of units (kind: PROVED). -/
theorem sqClassOf_prod {m : ℕ} (s : Finset ℕ) (g : ℕ → ℕ) (hg : ∀ v ∈ s, Nat.Coprime (g v) m) :
    sqClassOf m (∏ v ∈ s, (g v : ℤ)) = ∑ v ∈ s, sqClassOf m (g v) ∧
      IsUnit (((∏ v ∈ s, (g v : ℤ) : ℤ)) : ZMod m) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, Int.cast_one]
    exact ⟨RealizeAux.sqClassOf_one m, isUnit_one⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun v hv => hg v (mem_insert_of_mem hv)
    have hua := RealizeAux.isUnit_natCast_of_coprime (hg a (mem_insert_self a s))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, sqClassOf_mul hua ih2, ih1, Int.cast_mul]
    exact ⟨rfl, hua.mul ih2⟩

/-- **Multiplicativity of the residue bit** at a prime (kind: PROVED, Legendre symbol). -/
theorem legBit_mul {p : ℕ} (hp : p.Prime) {a b : ℤ} (ha : (a : ZMod p) ≠ 0)
    (hb : (b : ZMod p) ≠ 0) : legBit (a * b) p = legBit a p + legBit b p := by
  have := Fact.mk hp
  have hab : ((a * b : ℤ) : ZMod p) ≠ 0 := by rw [Int.cast_mul]; exact mul_ne_zero ha hb
  have hmul := legendreSym.mul p a b
  by_cases hsa : IsSquare (a : ZMod p) <;> by_cases hsb : IsSquare (b : ZMod p)
  · rw [legBit_of_isSquare hsa, legBit_of_isSquare hsb,
      legBit_of_isSquare (by rw [Int.cast_mul]; exact hsa.mul hsb)]
    decide
  · have h1 := (legendreSym.eq_one_iff p ha).mpr hsa
    have h2 := (legendreSym.eq_neg_one_iff p).mpr hsb
    have h3 : legendreSym p (a * b) = -1 := by rw [hmul, h1, h2, one_mul]
    rw [legBit_of_isSquare hsa, legBit_of_not_isSquare hsb,
      legBit_of_not_isSquare ((legendreSym.eq_neg_one_iff p).mp h3)]
    decide
  · have h1 := (legendreSym.eq_neg_one_iff p).mpr hsa
    have h2 := (legendreSym.eq_one_iff p hb).mpr hsb
    have h3 : legendreSym p (a * b) = -1 := by rw [hmul, h1, h2, mul_one]
    rw [legBit_of_not_isSquare hsa, legBit_of_isSquare hsb,
      legBit_of_not_isSquare ((legendreSym.eq_neg_one_iff p).mp h3)]
    decide
  · have h1 := (legendreSym.eq_neg_one_iff p).mpr hsa
    have h2 := (legendreSym.eq_neg_one_iff p).mpr hsb
    have h3 : legendreSym p (a * b) = 1 := by rw [hmul, h1, h2]; norm_num
    rw [legBit_of_not_isSquare hsa, legBit_of_not_isSquare hsb,
      legBit_of_isSquare ((legendreSym.eq_one_iff p hab).mp h3)]
    decide

/-- The residue bit of a product is the sum of the residue bits (kind: PROVED). -/
theorem legBit_prod {p : ℕ} (hp : p.Prime) (s : Finset ℕ) (g : ℕ → ℕ)
    (hg : ∀ v ∈ s, ((g v : ℤ) : ZMod p) ≠ 0) :
    legBit (∏ v ∈ s, (g v : ℤ)) p = ∑ v ∈ s, legBit (g v) p := by
  have := Fact.mk hp
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact legBit_of_isSquare ⟨1, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      RealizeAux.legBit_mul hp (hg a (mem_insert_self a s)) ?_,
      ih fun v hv => hg v (mem_insert_of_mem hv)]
    rw [Int.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun v hv => hg v (mem_insert_of_mem hv)

/-- `|q^*| = q` (kind: PROVED). -/
theorem qstar_natAbs (q : ℕ) : (qstar q).natAbs = q := by
  simp [qstar, Int.natAbs_mul, Int.natAbs_pow]

/-- `|∏ q^*| = ∏ q` (kind: PROVED). -/
theorem natAbs_prod_qstar (s : Finset ℕ) (g : ℕ → ℕ) :
    (∏ v ∈ s, qstar (g v)).natAbs = ∏ v ∈ s, g v := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.natAbs_mul, ih, RealizeAux.qstar_natAbs]

/-- `∏ q^* = (−1)^{∑ (q − 1)/2} ∏ q` (kind: PROVED). -/
theorem prod_qstar_eq (s : Finset ℕ) (g : ℕ → ℕ) :
    ∏ v ∈ s, qstar (g v) = (-1) ^ (∑ v ∈ s, (g v - 1) / 2) * ∏ v ∈ s, (g v : ℤ) := by
  unfold qstar
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- `q^*` is a unit modulo `m` for `q` prime to `m` (kind: PROVED). -/
theorem isUnit_qstar {m q : ℕ} (h : Nat.Coprime q m) : IsUnit ((qstar q : ℤ) : ZMod m) := by
  unfold qstar
  push_cast
  exact (isUnit_neg_one.pow _).mul ((ZMod.isUnit_iff_coprime q m).mpr h)

/-- A product of distinct primes is squarefree (kind: PROVED). -/
theorem squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.squarefree_mul_iff]
    have hpa := hs a (mem_insert_self a s)
    refine ⟨Nat.Coprime.prod_right fun p hp => ?_, hpa.prime.squarefree,
      ih fun p hp => hs p (mem_insert_of_mem hp)⟩
    exact (Nat.coprime_primes hpa (hs p (mem_insert_of_mem hp))).mpr fun h => ha (h ▸ hp)

/-- A prime dividing `∏ q^*` over primes is one of them (kind: PROVED). -/
theorem prime_dvd_prod_qstar {p : ℕ} (hp : p.Prime) (s : Finset ℕ) (g : ℕ → ℕ)
    (hg : ∀ v ∈ s, (g v).Prime) (hd : (p : ℤ) ∣ ∏ v ∈ s, qstar (g v)) : ∃ v ∈ s, g v = p := by
  obtain ⟨v, hv, hdv⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp) _).mp hd
  unfold qstar at hdv
  have h2 : (p : ℤ) ∣ (g v : ℤ) := ((isUnit_neg_one (α := ℤ)).pow _).dvd_mul_left.mp hdv
  have h3 : p ∣ g v := Int.natCast_dvd_natCast.mp h2
  exact ⟨v, hv, ((Nat.prime_dvd_prime_iff_eq hp (hg v hv)).mp h3).symm⟩

/-- `(q − 1)/2 = q/2` for odd `q` (kind: PROVED). -/
theorem half_eq {q : ℕ} (hq : q % 2 = 1) : (q - 1) / 2 = q / 2 := by omega

/-- The linear form `x ↦ ∑ᵢ wᵢ xᵢ` of an activation vector (tex 2209–2220; kind: definition). -/
def linForm {b : ℕ} (w : Fin b → ZMod 2) : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, w i * x i
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Evaluation of the linear form of an activation (kind: PROVED, by definition). -/
theorem linForm_apply {b : ℕ} (w x : Fin b → ZMod 2) :
    RealizeAux.linForm w x = ∑ i, w i * x i := rfl

/-- A nonzero activation vector gives a nonzero linear form (kind: PROVED). -/
theorem linForm_ne_zero {b : ℕ} {w : Fin b → ZMod 2} (hw : w ≠ 0) : RealizeAux.linForm w ≠ 0 := by
  intro h
  apply hw
  funext i
  have := LinearMap.congr_fun h (Pi.single i 1)
  rw [RealizeAux.linForm_apply, LinearMap.zero_apply, Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    simp [hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

open Classical in
/-- **The binary family of a realization** (the family (3.9), tex 2674–2694, 10801–10804; kind:
definition): primes `Q = f(V)` and, for `q = f u`, the linear form of the activation of `u`. -/
def familyOf (b : ℕ) (V : Finset ℕ) (f : ℕ → ℕ) (act' : ℕ → Option (Fin b → ZMod 2)) :
    Family where
  b := b
  Q := V.image f
  lam := fun q => if h : ∃ u ∈ V, f u = q then RealizeAux.linForm ((act' h.choose).getD 0) else 0

/-- The linear form `λ_{f u}` of the family is the form of the activation of `u` (tex 2209–2220,
10801–10804; kind: PROVED). -/
theorem familyOf_lam {b : ℕ} {V : Finset ℕ} {f : ℕ → ℕ} {act' : ℕ → Option (Fin b → ZMod 2)}
    (hinj : Set.InjOn f V) {u : ℕ} (hu : u ∈ V) :
    (RealizeAux.familyOf b V f act').lam (f u) = RealizeAux.linForm ((act' u).getD 0) := by
  classical
  have h : ∃ u' ∈ V, f u' = f u := ⟨u, hu, rfl⟩
  unfold RealizeAux.familyOf
  dsimp only
  rw [dite_eq_left h]
  have hc := h.choose_spec
  rw [hinj (Finset.mem_coe.mpr hc.1) (Finset.mem_coe.mpr hu) hc.2]

open Classical in
/-- The member `h_x` of the family is the product of `q^*` over the present vertices (tex 2209–2220,
10801–10804; kind: PROVED). -/
theorem familyOf_h {b : ℕ} {V : Finset ℕ} {f : ℕ → ℕ} {act' : ℕ → Option (Fin b → ZMod 2)}
    (hinj : Set.InjOn f V) (hact : ∀ u ∈ V, ∃ w, w ≠ 0 ∧ act' u = some w)
    (x : Fin b → ZMod 2) :
    (RealizeAux.familyOf b V f act').h x = ∏ u ∈ V.filter (present act' x), qstar (f u) := by
  unfold Family.h
  rw [show (RealizeAux.familyOf b V f act').Q = V.image f from rfl, Finset.prod_image hinj,
    Finset.prod_filter]
  refine Finset.prod_congr rfl fun u hu => ?_
  rw [RealizeAux.familyOf_lam hinj hu]
  obtain ⟨w, -, hw⟩ := hact u hu
  have hp : present act' x u ↔ (∑ i, w i * x i) = 1 := by unfold present; rw [hw]
  rw [hw, Option.getD_some]
  change qstar (f u) ^ (∑ i, w i * x i).val = _
  rcases RealizeAux.zmod2_cases (∑ i, w i * x i) with h0 | h1
  · rw [ite_eq_right (by rw [hp, h0]; decide), h0, ZMod.val_zero, pow_zero]
  · rw [ite_eq_left (hp.mpr h1), h1]
    exact pow_one _

end RealizeAux


variable {m : ℕ} {k : ℤ} {hk : 4 * k.natAbs ∣ m} {ℓ₀ : ℕ} {avoid : Finset ℕ}

/-! ### Basic properties of a realization -/

namespace RealizesWith

variable {Δ : Config (CommonL m k hk)} {D : ℤ} {f : ℕ → ℕ}

/-- A realization restricts to the active configuration at an address (tex 2209–2220; kind:
PROVED). -/
theorem at' {b : ℕ} (hf : RealizesWith m k hk ℓ₀ avoid Δ D f)
    (act' : ℕ → Option (Fin b → ZMod 2)) (x : Fin b → ZMod 2) :
    RealizesWith m k hk ℓ₀ avoid (Δ.at act' x) (∏ v ∈ (Δ.at act' x).V, qstar (f v)) f := by
  classical
  have hsub : (Δ.at act' x).V ⊆ Δ.V := Finset.filter_subset _ _
  exact ⟨hf.1.mono (Finset.coe_subset.mpr hsub), fun v hv => hf.2.1 v (hsub hv),
    fun v hv w hw hvw => hf.2.2.1 v (hsub hv) w (hsub hw) hvw, rfl⟩

/-- **A realized typed graph is compatible** (tex 2031–2041, reciprocity; kind: PROVED). -/
theorem compatible (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) (h4 : 4 ∣ m) :
    Δ.Compatible (commonSign m h4 k hk) := by
  intro v hv w hw hvw
  obtain ⟨hpv, hcv, -, -, hsv, -⟩ := hf.2.1 v hv
  obtain ⟨hpw, hcw, -, -, hsw, -⟩ := hf.2.1 w hw
  rw [← hf.2.2.1 v hv w hw hvw, ← hf.2.2.1 w hw v hv (Ne.symm hvw), commonSign_apply,
    commonSign_apply, ← hsv, ← hsw, signChar_sqClassOf h4 hpv hcv, signChar_sqClassOf h4 hpw hcw]
  exact legBit_reciprocity hpv hpw (RealizeAux.ne_two_of_coprime_four h4 hcv)
    (RealizeAux.ne_two_of_coprime_four h4 hcw) fun h => hvw (hf.1 hv hw h)

/-- **Every vertex prime is split in `K`**: `(k/q) = 1` (tex 2678–2680, 4234–4237; kind: PROVED
from the Kronecker character `kChar`). -/
theorem jacobiSym_eq_one (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) :
    ∀ v ∈ Δ.V, jacobiSym k (f v) = 1 := by
  intro v hv
  obtain ⟨hp, hc, -, -, hs, -⟩ := hf.2.1 v hv
  exact (kChar_sqClassOf_eq_zero_iff hk hp hc).mp (by rw [hs]; exact (Δ.t v).1.2)

/-- `D` is the product of `q^*` over the realized primes (kind: PROVED). -/
theorem prod_image (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) :
    D = ∏ q ∈ Δ.V.image f, qstar q := by
  rw [hf.2.2.2, Finset.prod_image hf.1]

/-- The realized primes are as many as the vertices (kind: PROVED). -/
theorem card_image (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) :
    (Δ.V.image f).card = Δ.V.card :=
  Finset.card_image_of_injOn hf.1

/-- The prime divisors of `D` are exactly the realized primes (kind: PROVED). -/
theorem prime_dvd_iff (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ D ↔ p ∈ Δ.V.image f := by
  constructor
  · intro hd
    rw [hf.2.2.2] at hd
    obtain ⟨v, hv, rfl⟩ := RealizeAux.prime_dvd_prod_qstar hp Δ.V f (fun v hv => (hf.2.1 v hv).1) hd
    exact Finset.mem_image_of_mem f hv
  · intro hmem
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hmem
    rw [hf.2.2.2]
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun v => qstar (f v)) hv)
    unfold qstar
    exact Dvd.intro_left _ rfl

/-- `ω(D) = |V(Δ)|` (tex 2678–2686, 10795–10804; kind: PROVED). -/
theorem omega_eq (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) :
    ZInQ.Contrib.CloudB3RC53.AppGEndpoints.omega D = Δ.V.card := by
  have hprime : ∀ p ∈ Δ.V.image f, p.Prime := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact (hf.2.1 v hv).1
  have hP : ∏ v ∈ Δ.V, f v = ∏ q ∈ Δ.V.image f, q := by rw [Finset.prod_image hf.1]
  unfold ZInQ.Contrib.CloudB3RC53.AppGEndpoints.omega
  rw [hf.2.2.2, RealizeAux.natAbs_prod_qstar, hP,
    ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  change (Nat.primeFactors _).card = _
  rw [Nat.primeFactors_prod hprime, Finset.card_image_of_injOn hf.1]

/-- `D` is squarefree (tex 2678–2686, 10801–10804; kind: PROVED). -/
theorem squarefree (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) : Squarefree D := by
  have hprime : ∀ p ∈ Δ.V.image f, p.Prime := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact (hf.2.1 v hv).1
  have hP : ∏ v ∈ Δ.V, f v = ∏ q ∈ Δ.V.image f, q := by rw [Finset.prod_image hf.1]
  rw [← Int.squarefree_natAbs, hf.2.2.2, RealizeAux.natAbs_prod_qstar, hP]
  exact RealizeAux.squarefree_prod_primes _ hprime

/-- `D` is a unit modulo `m` (tex 2042–2047; kind: PROVED). -/
theorem isUnit (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) : IsUnit (D : ZMod m) := by
  rw [hf.2.2.2, Int.cast_prod]
  exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    fun v hv => RealizeAux.isUnit_qstar (hf.2.1 v hv).2.1

/-! ### The total type -/

/-- The squareclass of the product of the realized primes is the squareclass coordinate of the
total type, and it is a unit (tex 2042–2047; kind: PROVED). -/
theorem sqClassOf_prod_eq (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) :
    sqClassOf m (∏ v ∈ Δ.V, (f v : ℤ)) = ((Δ.total).1 : SqClass m) ∧
      IsUnit (((∏ v ∈ Δ.V, (f v : ℤ) : ℤ)) : ZMod m) := by
  obtain ⟨h1, h2⟩ := RealizeAux.sqClassOf_prod (m := m) Δ.V f fun v hv => (hf.2.1 v hv).2.1
  refine ⟨?_, h2⟩
  rw [h1]
  have hφ := map_sum ((kSplitSub m k hk).subtype.comp (AddMonoidHom.fst _ _)) Δ.t Δ.V
  refine Eq.trans ?_ hφ.symm
  exact Finset.sum_congr rfl fun v hv => (hf.2.1 v hv).2.2.2.2.1

/-- The residue bit of the product of the realized primes at `ℓ₀` is the bit coordinate of the
total type (Legendre multiplicativity; kind: PROVED). -/
theorem legBit_prod_eq (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) (hℓ₀ : ℓ₀.Prime) :
    legBit (∏ v ∈ Δ.V, (f v : ℤ)) ℓ₀ = (Δ.total).2 := by
  rw [RealizeAux.legBit_prod hℓ₀ Δ.V f ?_]
  · have hφ := map_sum (AddMonoidHom.snd (KSplitClass m k hk) (ZMod 2)) Δ.t Δ.V
    refine Eq.trans ?_ hφ.symm
    exact Finset.sum_congr rfl fun v hv => (hf.2.1 v hv).2.2.2.2.2
  · intro v hv h0
    obtain ⟨hp, -, hne, -⟩ := hf.2.1 v hv
    rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h0
    exact hne ((Nat.prime_dvd_prime_iff_eq hℓ₀ hp).mp h0).symm

/-- The sign of `D`: `D = (−1)^e ∏ q` with `e mod 2` the sign coordinate of the total type
(tex 2042–2047; kind: PROVED). -/
theorem sign_eq (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) (h4 : 4 ∣ m) :
    D = (-1) ^ (∑ v ∈ Δ.V, (f v - 1) / 2) * ∏ v ∈ Δ.V, (f v : ℤ) ∧
      ((∑ v ∈ Δ.V, (f v - 1) / 2 : ℕ) : ZMod 2) = commonSign m h4 k hk Δ.total := by
  refine ⟨by rw [hf.2.2.2, RealizeAux.prod_qstar_eq], ?_⟩
  rw [Nat.cast_sum, commonSign_apply]
  have hφ := map_sum ((kSplitSub m k hk).subtype.comp (AddMonoidHom.fst _ _)) Δ.t Δ.V
  have hT : ((Δ.total).1 : SqClass m) = ∑ v ∈ Δ.V, ((Δ.t v).1 : SqClass m) := hφ
  rw [hT, map_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨hp, hc, -, -, hs, -⟩ := hf.2.1 v hv
  rw [← hs, signChar_sqClassOf h4 hp hc,
    RealizeAux.half_eq (hp.eq_two_or_odd.resolve_left (RealizeAux.ne_two_of_coprime_four h4 hc))]

/-- The product of the realized primes is positive (kind: PROVED). -/
theorem prod_pos (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) : 0 < ∏ v ∈ Δ.V, (f v : ℤ) :=
  Finset.prod_pos fun v hv => by exact_mod_cast (hf.2.1 v hv).1.pos

/-- **Total type zero is the positive square filter** (tex 2042–2047, 2686, 10589–10596,
10804; kind: PROVED): for a realization, `Δ.total = 0` iff `D > 0`, `D` is a square modulo `m`
and `D` is a square modulo `ℓ₀`. -/
theorem total_zero_iff (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) (h4 : 4 ∣ m)
    (hℓ₀ : ℓ₀.Prime) :
    Δ.total = 0 ↔ 0 < D ∧ IsSquare (D : ZMod m) ∧ IsSquare (D : ZMod ℓ₀) := by
  obtain ⟨hD, hsign⟩ := hf.sign_eq h4
  obtain ⟨hcl, hunit⟩ := hf.sqClassOf_prod_eq
  have hbit := hf.legBit_prod_eq hℓ₀
  have hpos := hf.prod_pos
  set P := ∏ v ∈ Δ.V, (f v : ℤ) with hPdef
  set e := ∑ v ∈ Δ.V, (f v - 1) / 2 with hedef
  constructor
  · intro htot
    have he : ((e : ℕ) : ZMod 2) = 0 := by rw [hsign, htot, map_zero]
    have hDP : D = P := by
      rw [hD, ((ZMod.natCast_eq_zero_iff_even).mp he).neg_one_pow, one_mul]
    have h1 : ((Δ.total).1 : SqClass m) = 0 := by rw [htot]; rfl
    have h2 : (Δ.total).2 = 0 := by rw [htot]; rfl
    refine ⟨hDP ▸ hpos, ?_, ?_⟩
    · rw [hDP]
      exact (sqClassOf_eq_zero_iff hunit).mp (hcl.trans h1)
    · rw [hDP]
      by_contra hns
      have := legBit_of_not_isSquare hns
      rw [hbit, h2] at this
      exact absurd this (by decide)
  · rintro ⟨hDpos, hsqm, hsql⟩
    have hDP : D = P := by
      rcases neg_one_pow_eq_or ℤ e with h | h
      · rw [hD, h, one_mul]
      · rw [hD, h, neg_one_mul] at hDpos
        exact absurd hDpos (not_lt.mpr (neg_nonpos.mpr hpos.le))
    rw [hDP] at hsqm hsql
    have h1 : ((Δ.total).1 : SqClass m) = 0 :=
      hcl.symm.trans ((sqClassOf_eq_zero_iff hunit).mpr hsqm)
    have h2 : (Δ.total).2 = 0 := hbit.symm.trans (legBit_of_isSquare hsql)
    exact Prod.ext (Subtype.ext h1) h2

/-! ### The odd and even readings -/

end RealizesWith

/-- **The odd projection** of the common alphabet to the stage alphabet at `m₁ ∣ m` (squareclass
modulo `m₁`, bit at the theta prime) (tex 2060–2065, 10519–10521; kind: definition). -/
def oddProj {m₁ m : ℕ} {k : ℤ} {hk : 4 * k.natAbs ∣ m} (h : m₁ ∣ m) :
    CommonL m k hk →+ SqClass m₁ × ZMod 2 :=
  ((sqProj h).comp ((kSplitSub m k hk).subtype.comp (AddMonoidHom.fst _ _))).prod
    (AddMonoidHom.snd _ _)

/-- Evaluation of the odd projection (kind: PROVED, by definition). -/
theorem oddProj_apply {m₁ : ℕ} (h : m₁ ∣ m) (x : CommonL m k hk) :
    oddProj h x = (sqProj h (x.1 : SqClass m), x.2) := rfl

/-- The odd projection carries the sign coordinate (tex 2060–2065; kind: PROVED). -/
theorem oddSign_oddProj {m₁ : ℕ} (h : m₁ ∣ m) (h4₁ : 4 ∣ m₁) (h4 : 4 ∣ m)
    (x : CommonL m k hk) :
    ((signChar m₁ h4₁).comp (AddMonoidHom.fst _ _)) (oddProj h x) = commonSign m h4 k hk x := by
  change signChar m₁ h4₁ (sqProj h (x.1 : SqClass m)) = _
  rw [signChar_sqProj h h4₁, commonSign_apply]

/-- An even projection `x ↦ sqProj x.1` carries the sign coordinate (tex 2060–2065, 2656–2658;
kind: PROVED). -/
theorem evenSign_proj {m₂ : ℕ} (h : m₂ ∣ m) (h4₂ : 4 ∣ m₂) (h4 : 4 ∣ m)
    (π₂ : CommonL m k hk →+ SqClass m₂) (hπ₂ : ∀ x, π₂ x = sqProj h (x.1 : SqClass m))
    (x : CommonL m k hk) : signChar m₂ h4₂ (π₂ x) = commonSign m h4 k hk x := by
  rw [hπ₂, signChar_sqProj h h4₂, commonSign_apply]

namespace RealizesWith

variable {Δ : Config (CommonL m k hk)} {D : ℤ} {f : ℕ → ℕ}

/-- **The odd reading of a realization** (tex 2093–2096, 10236–10249, 10825–10850; kind: PROVED):
the witness `f` is a prime realization, in batch 3's sense, of the odd projection of `Δ` for any
stage type data whose conductor is `m₁ ℓ₀` and whose type is the squareclass modulo `m₁` with the
bit at `ℓ₀`. -/
theorem isReal_odd (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) (hℓ₀ : ℓ₀.Prime) {m₁ : ℕ}
    (h : m₁ ∣ m) {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2} (T : TypeData (SqClass m₁ × ZMod 2) ε₁)
    (hTm : T.m = m₁ * ℓ₀) (hTt : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀)) :
    IsReal T (Δ.mapType (oddProj h)) f := by
  refine ⟨hf.1, fun v hv => ?_, fun v hv w hw hvw => hf.2.2.1 v hv w hw hvw⟩
  obtain ⟨hp, hc, hne, -, hs, hl⟩ := hf.2.1 v hv
  refine ⟨⟨hp, ?_⟩, ?_⟩
  · rw [hTm]
    exact Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right h hc)
      ((Nat.coprime_primes hp hℓ₀).mpr hne)
  · rw [hTt]
    change _ = oddProj h (Δ.t v)
    rw [oddProj_apply, ← hs, sqProj_sqClassOf h (RealizeAux.isUnit_natCast_of_coprime hc), hl]

/-- **The even reading of a realization** (tex 2093–2096, 10288–10322, 10854–10855; kind:
PROVED): the witness `f` is a prime realization of the even projection of `Δ` for any even type
data whose conductor is `m₂ ∣ m` and whose type is the squareclass modulo `m₂`. -/
theorem isReal_even (hf : RealizesWith m k hk ℓ₀ avoid Δ D f) {m₂ : ℕ} (h : m₂ ∣ m)
    {ε₂ : SqClass m₂ →+ ZMod 2} (T₂ : TypeData (SqClass m₂) ε₂) (hTm : T₂.m = m₂)
    (hTt : T₂.typ = fun p : ℕ => sqClassOf m₂ (p : ℤ)) (π₂ : CommonL m k hk →+ SqClass m₂)
    (hπ₂ : ∀ x, π₂ x = sqProj h (x.1 : SqClass m)) : IsReal T₂ (Δ.mapType π₂) f := by
  refine ⟨hf.1, fun v hv => ?_, fun v hv w hw hvw => hf.2.2.1 v hv w hw hvw⟩
  obtain ⟨hp, hc, -, -, hs, -⟩ := hf.2.1 v hv
  refine ⟨⟨hp, ?_⟩, ?_⟩
  · rw [hTm]
    exact Nat.Coprime.coprime_dvd_right h hc
  · rw [hTt]
    change _ = π₂ (Δ.t v)
    rw [hπ₂, ← hs, sqProj_sqClassOf h (RealizeAux.isUnit_natCast_of_coprime hc)]

end RealizesWith

/-! ### The realization of the address construction -/

/-- **Realization of a compatible typed graph by primes** (Lemma `ex:sec7-realization`, tex
2151–2174; kind: PROVED): CRT and Dirichlet (lane RC2's `finite_realization_nat`, with the old
prime `ℓ₀` carrying the bit coordinate and reduced classes representing the squareclasses) give
the forward bits; quadratic reciprocity and compatibility give the reverse bits. -/
theorem exists_realizesWith (hm : 0 < m) (h4 : 4 ∣ m) (hℓ₀ : ℓ₀.Prime)
    (hℓ₀m : Nat.Coprime ℓ₀ m) (avoid : Finset ℕ) (Γ : Config (CommonL m k hk))
    (hΓ : Γ.Compatible (commonSign m h4 k hk)) :
    ∃ f : ℕ → ℕ, RealizesWith m k hk ℓ₀ avoid Γ (∏ v ∈ Γ.V, qstar (f v)) f := by
  classical
  have h2 : 2 ∣ m := dvd_trans ⟨2, by norm_num⟩ h4
  choose u hu using fun v : ℕ => sqMk_surjective m ((Γ.t v).1 : SqClass m)
  have hold : ∀ p ∈ ({ℓ₀} : Finset ℕ), p.Prime ∧ Nat.Coprime p m := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨hℓ₀, hℓ₀m⟩
  obtain ⟨q, hinj, hq, hqold, hqnew⟩ := finite_realization_nat m hm h2 {ℓ₀} hold avoid
    (fun i => (u (enumV Γ.V i) : ZMod m)) (fun i => (u (enumV Γ.V i)).isUnit)
    (fun i _ => (Γ.t (enumV Γ.V i)).2) (fun i j => Γ.z (enumV Γ.V i) (enumV Γ.V j)) Γ.V.card
  have key : ∀ v ∈ Γ.V, (q (idxV Γ.V v)).Prime ∧ Nat.Coprime (q (idxV Γ.V v)) m ∧
      q (idxV Γ.V v) ≠ ℓ₀ ∧ q (idxV Γ.V v) ∉ avoid ∧
      sqClassOf m (q (idxV Γ.V v)) = ((Γ.t v).1 : SqClass m) ∧
      legBit (q (idxV Γ.V v)) ℓ₀ = (Γ.t v).2 := by
    intro v hv
    obtain ⟨hi, hiv⟩ := idxV_spec hv
    obtain ⟨hp, hno, hav, hc⟩ := hq _ hi
    have hc' : ((q (idxV Γ.V v) : ℕ) : ZMod m) = u v := by
      simp only [hiv] at hc
      exact hc
    refine ⟨hp, (ZMod.isUnit_iff_coprime _ m).mp (by rw [hc']; exact (u v).isUnit),
      fun h => hno (by rw [h]; exact Finset.mem_singleton_self _), hav, ?_, ?_⟩
    · rw [RealizeAux.sqClassOf_natCast_eq hc', hu v]
    · have := hqold _ hi ℓ₀ (Finset.mem_singleton_self _)
      simp only [hiv] at this
      exact this
  refine ⟨fun v => q (idxV Γ.V v), ?_, key, ?_, rfl⟩
  · intro v hv w hw h
    have h1 := idxV_spec (Finset.mem_coe.mp hv)
    have h2 := idxV_spec (Finset.mem_coe.mp hw)
    rw [← h1.2, ← h2.2, hinj _ h1.1 _ h2.1 h]
  · intro v hv w hw hvw
    obtain ⟨hi, hiv⟩ := idxV_spec hv
    obtain ⟨hj, hjw⟩ := idxV_spec hw
    have hij : idxV Γ.V v ≠ idxV Γ.V w := fun h => hvw (by rw [← hiv, ← hjw, h])
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · -- the reverse bit, by reciprocity and compatibility
      have hqne : q (idxV Γ.V v) ≠ q (idxV Γ.V w) := fun h => hij (hinj _ hi _ hj h)
      obtain ⟨hpv, hcv, -, -, hsv, -⟩ := key v hv
      obtain ⟨hpw, hcw, -, -, hsw, -⟩ := key w hw
      have hrec := legBit_reciprocity hpv hpw (RealizeAux.ne_two_of_coprime_four h4 hcv)
        (RealizeAux.ne_two_of_coprime_four h4 hcw) hqne
      have hback : legBit (q (idxV Γ.V w)) (q (idxV Γ.V v)) = Γ.z w v := by
        have := hqnew _ hj _ hlt
        simp only [hiv, hjw] at this
        exact this
      have hcomp := hΓ v hv w hw hvw
      rw [commonSign_apply, commonSign_apply, ← hsv, ← hsw, signChar_sqClassOf h4 hpv hcv,
        signChar_sqClassOf h4 hpw hcw] at hcomp
      rw [hback] at hrec
      exact add_right_cancel (hrec.trans hcomp.symm)
    · -- the forward bit
      have := hqnew _ hi _ hgt
      simp only [hiv, hjw] at this
      exact this

/-- **Prime realization of the address construction by one admissible family** (conjunct 15 of
lane RC0's `AddressPackage`; Lemma `ex:sec7-realization`, tex 2151–2174; Proposition
`ex:app-final-family`, App G tex 10795–10828, in particular 10825–10828: "Realize its prescribed
forward residue bits by distinct primes using CRT and Dirichlet; quadratic reciprocity supplies
the reverse bits"; kind: PROVED). For every `b`, every compatible typed graph `Γ` over the common
alphabet with nonzero activations is realized by distinct primes `f v` (prime to `m`, different
from `ℓ₀`, outside `avoid`, split in `K`); the family has `Q = f(V)` and `λ_{f u}` the linear form
of the activation of `u`, so that at every nonzero address `x` the member `h_x` is `∏ q^*` over the
present vertices, a realization of the active configuration `Γ.at act' x`. -/
theorem exists_family_realizesAt (hm : 0 < m) (h4 : 4 ∣ m) (hℓ₀ : ℓ₀.Prime)
    (hℓ₀m : Nat.Coprime ℓ₀ m) (avoid : Finset ℕ) (b : ℕ) (Γ : Config (CommonL m k hk))
    (hΓ : Γ.Compatible (commonSign m h4 k hk)) (act' : ℕ → Option (Fin b → ZMod 2))
    (hact : ∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) :
    ∃ F : Family, ∃ hdim : F.b = b, Family.Admissible avoid k F ∧
      ∀ x : Fin b → ZMod 2, x ≠ 0 →
        RealizesAt m k hk ℓ₀ avoid (Γ.at act' x) (F.h (x ∘ Fin.cast hdim)) := by
  classical
  obtain ⟨f, hf⟩ := exists_realizesWith hm h4 hℓ₀ hℓ₀m avoid Γ hΓ
  refine ⟨RealizeAux.familyOf b Γ.V f act', rfl, ?_, fun x _ => ⟨f, ?_⟩⟩
  · intro q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp, hcop, -, hav, -, -⟩ := hf.2.1 u hu
    obtain ⟨w, hw0, hw⟩ := hact u hu
    refine ⟨hp, RealizeAux.ne_two_of_coprime_four h4 hcop, hav, hf.jacobiSym_eq_one u hu, ?_⟩
    rw [RealizeAux.familyOf_lam hf.1 hu, hw, Option.getD_some]
    exact RealizeAux.linForm_ne_zero hw0
  · have e : (RealizeAux.familyOf b Γ.V f act').h (x ∘ Fin.cast rfl) =
        ∏ v ∈ (Γ.at act' x).V, qstar (f v) := RealizeAux.familyOf_h hf.1 hact x
    change RealizesWith m k hk ℓ₀ avoid (Γ.at act' x) _ f
    rw [e]
    exact hf.at' act' x

/-! ### Consequences for `RealizesAt` -/

/-- **A realization has `ω(D) = |V(Δ)|`** (first half of conjunct 16₀ of lane RC0's
`AddressPackageZeroTotal`; tex 2678–2686, 10795–10804; kind: PROVED). -/
theorem realizesAt_omega {Δ : Config (CommonL m k hk)} {D : ℤ}
    (hR : RealizesAt m k hk ℓ₀ avoid Δ D) :
    ZInQ.Contrib.CloudB3RC53.AppGEndpoints.omega D = Δ.V.card := by
  obtain ⟨f, hf⟩ := hR
  exact RealizesWith.omega_eq hf

/-- **A realization is a realized compatible typed graph** (tex 2031–2041; kind: PROVED). -/
theorem realizesAt_compatible (h4 : 4 ∣ m) {Δ : Config (CommonL m k hk)} {D : ℤ}
    (hR : RealizesAt m k hk ℓ₀ avoid Δ D) : Δ.Compatible (commonSign m h4 k hk) := by
  obtain ⟨f, hf⟩ := hR
  exact RealizesWith.compatible hf h4

/-- **The product of a realization is squarefree, prime to the avoided primes and a unit modulo
`m`** (tex 2042–2047, 2678–2686, 10801–10804; kind: PROVED). DEPARTURE (statement): the avoidance
conclusion is stated for the *prime* members `p` of `avoid`, since `avoid` may contain `1`. -/
theorem realizesAt_squarefree_coprime {Δ : Config (CommonL m k hk)} {D : ℤ}
    (hR : RealizesAt m k hk ℓ₀ avoid Δ D) :
    Squarefree D ∧ (∀ p ∈ avoid, p.Prime → ¬ (p : ℤ) ∣ D) ∧ IsUnit (D : ZMod m) := by
  obtain ⟨f, hf⟩ := hR
  refine ⟨RealizesWith.squarefree hf, fun p hp hpp hd => ?_, RealizesWith.isUnit hf⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ((RealizesWith.prime_dvd_iff hf hpp).mp hd)
  exact (hf.2.1 v hv).2.2.2.1 hp

/-- **The product of a realization is prime to the theta prime** (tex 10845–10848: the theta
prime is an exclusion; kind: PROVED). -/
theorem realizesAt_not_dvd_ell (hℓ₀ : ℓ₀.Prime) {Δ : Config (CommonL m k hk)} {D : ℤ}
    (hR : RealizesAt m k hk ℓ₀ avoid Δ D) : ¬ (ℓ₀ : ℤ) ∣ D := by
  obtain ⟨f, hf⟩ := hR
  intro hd
  obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp ((RealizesWith.prime_dvd_iff hf hℓ₀).mp hd)
  exact (hf.2.1 v hv).2.2.1 hfv

/-- **Total type zero: the product lies in the positive square filter** (tex 2042–2047, 2686,
10589–10596, 10804; kind: PROVED): the class of the product is a square, hence `≡ 1 (mod 4)`, so
the signs of the `q^*` cancel and `D = ∏ q > 0`; Legendre multiplicativity at `ℓ₀`. -/
theorem realizesAt_total_zero (h4 : 4 ∣ m) (hℓ₀ : ℓ₀.Prime) {Δ : Config (CommonL m k hk)}
    {D : ℤ} (hR : RealizesAt m k hk ℓ₀ avoid Δ D) (htot : Δ.total = 0) :
    0 < D ∧ IsSquare (D : ZMod m) ∧ IsSquare (D : ZMod ℓ₀) := by
  obtain ⟨f, hf⟩ := hR
  exact (RealizesWith.total_zero_iff hf h4 hℓ₀).mp htot

/-- **The positive square filter is total type zero** (the converse of `realizesAt_total_zero`;
tex 2042–2047, 10589–10596; kind: PROVED). -/
theorem realizesAt_total_zero_iff (h4 : 4 ∣ m) (hℓ₀ : ℓ₀.Prime) {Δ : Config (CommonL m k hk)}
    {D : ℤ} (hR : RealizesAt m k hk ℓ₀ avoid Δ D) :
    Δ.total = 0 ↔ 0 < D ∧ IsSquare (D : ZMod m) ∧ IsSquare (D : ZMod ℓ₀) := by
  obtain ⟨f, hf⟩ := hR
  exact RealizesWith.total_zero_iff hf h4 hℓ₀

/-- **One witness for both readings** (tex 2060–2065, 2093–2096, 10825–10855; kind: PROVED): a
realization has a witness `f`, injective on `V`, with `D = ∏_{q ∈ f(V)} q^*`, `|f(V)| = |V|`,
every vertex prime split in `K`, which realizes the odd projection for every stage type data at
`m₁ ∣ m` with conductor `m₁ ℓ₀` and the even projection for every even type data at `m₂ ∣ m`. -/
theorem realizesAt_readings (hℓ₀ : ℓ₀.Prime) {Δ : Config (CommonL m k hk)} {D : ℤ}
    (hR : RealizesAt m k hk ℓ₀ avoid Δ D) :
    ∃ f : ℕ → ℕ, RealizesWith m k hk ℓ₀ avoid Δ D f ∧
      D = ∏ q ∈ Δ.V.image f, qstar q ∧ (Δ.V.image f).card = Δ.V.card ∧
      (∀ v ∈ Δ.V, jacobiSym k (f v) = 1) ∧
      (∀ (m₁ : ℕ) (h : m₁ ∣ m) (ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2)
        (T : TypeData (SqClass m₁ × ZMod 2) ε₁), T.m = m₁ * ℓ₀ →
        (∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀)) →
        IsReal T (Δ.mapType (oddProj h)) f) ∧
      (∀ (m₂ : ℕ) (h : m₂ ∣ m) (ε₂ : SqClass m₂ →+ ZMod 2) (T₂ : TypeData (SqClass m₂) ε₂),
        T₂.m = m₂ → T₂.typ = (fun p : ℕ => sqClassOf m₂ (p : ℤ)) →
        ∀ π₂ : CommonL m k hk →+ SqClass m₂, (∀ x, π₂ x = sqProj h (x.1 : SqClass m)) →
        IsReal T₂ (Δ.mapType π₂) f) := by
  obtain ⟨f, hf⟩ := hR
  exact ⟨f, hf, RealizesWith.prod_image hf, RealizesWith.card_image hf,
    RealizesWith.jacobiSym_eq_one hf,
    fun m₁ h _ T hTm hTt => RealizesWith.isReal_odd hf hℓ₀ h T hTm hTt,
    fun m₂ h _ T₂ hTm hTt π₂ hπ₂ => RealizesWith.isReal_even hf h T₂ hTm hTt π₂ hπ₂⟩

/-! ### Configurations read off prime sets (seeds) -/

open Classical in
/-- **The configuration of a finite set of primes** (Definition `ex:sec7-typed-graph`, tex
2031–2034; kind: definition): vertices the primes, types their squareclass modulo `m` (when
`K`-split) and their bit at `ℓ₀`, bits the residue bits. -/
def primeCommonConfig (m : ℕ) (k : ℤ) (hk : 4 * k.natAbs ∣ m) (ℓ₀ : ℕ) (U : Finset ℕ) :
    Config (CommonL m k hk) where
  V := U
  t := fun q => (if h : sqClassOf m q ∈ kSplitSub m k hk then ⟨sqClassOf m q, h⟩ else 0,
    legBit q ℓ₀)
  z := fun v w => legBit v w

/-- **Prime sets realize their own configuration** (the converse direction, used for seeds; tex
2031–2047, 2176–2180; kind: PROVED): a finite set `U` of primes prime to `m`, different from `ℓ₀`,
outside `avoid` and split in `K` realizes `primeCommonConfig m k hk ℓ₀ U` by the identity, with
`D = ∏_{q ∈ U} q^*`, and this configuration is compatible. -/
theorem realizesAt_of_primes (h4 : 4 ∣ m) {U : Finset ℕ}
    (hU : ∀ q ∈ U, q.Prime ∧ Nat.Coprime q m ∧ q ≠ ℓ₀ ∧ q ∉ avoid ∧ jacobiSym k q = 1) :
    RealizesWith m k hk ℓ₀ avoid (primeCommonConfig m k hk ℓ₀ U) (∏ q ∈ U, qstar q) id ∧
      RealizesAt m k hk ℓ₀ avoid (primeCommonConfig m k hk ℓ₀ U) (∏ q ∈ U, qstar q) ∧
      (primeCommonConfig m k hk ℓ₀ U).Compatible (commonSign m h4 k hk) := by
  have hW : RealizesWith m k hk ℓ₀ avoid (primeCommonConfig m k hk ℓ₀ U)
      (∏ q ∈ U, qstar q) id := by
    refine ⟨Set.injOn_id _, fun q hq => ?_, fun v _ w _ _ => rfl, rfl⟩
    obtain ⟨hp, hc, hne, hav, hj⟩ := hU q hq
    have hmem : sqClassOf m q ∈ kSplitSub m k hk := (kChar_sqClassOf_eq_zero_iff hk hp hc).mpr hj
    refine ⟨hp, hc, hne, hav, ?_, rfl⟩
    simp [primeCommonConfig, hmem]
  exact ⟨hW, ⟨id, hW⟩, hW.compatible h4⟩

end ZInQ.Manuscript.RC.AddressGenuine

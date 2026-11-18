import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Realize
import ZInQKernel.Contrib.OneProof.RC.Skeleton.Setup

/-!
# Lane RC24: the genuine residue-class type alphabets

Manuscript `diophantine_zq.tex`: Definition `ex:sec7-typed-graph` (tex 2015–2066), Lemma
`ex:sec7-realization` (tex 2151–2174, in particular tex 2162–2163), the final companion `k` and
`K = ℚ(√k)` (tex 2595–2615, 10279–10286), the moving theta prime (tex 2024–2025, 10527–10532)
and the signed factors `q^*` (tex 2045–2048, 2682–2684).

* `SqClass m`: the squareclass group `(ℤ/m)ˣ/((ℤ/m)ˣ)²` (additive); `sqClassOf m a` the type
  of an integer; `typeData m`: the genuine type data of lane RC2/the coefficient dictionary, with
  `classes` and `sign` PROVED.
* `signChar` (the sign coordinate `ε`), `kChar` (the splitting character of `K`), the projections
  `sqProj` and `kSplitProj` (surjective), and their compatibilities.
* `exists_kSplit_lift`: fresh ramification lifts every old class to a `K`-split class (Jacobi
  reciprocity).
* `stageTypeData`: the type data of an odd theta stage, with the residue bit at the moving prime.
* Multiplicativity of types and residue bits; the sign of `∏ q^*`.

Everything is PROVED; there are no hypotheses beyond those stated.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-! ### The squareclass group of `(ℤ/m)ˣ` -/

/-- The subgroup of squares of `(ℤ/m)ˣ` (definition; tex 2017–2021, "its unit squareclasses at
`S`"). -/
def sqSub (m : ℕ) : Subgroup (ZMod m)ˣ := (powMonoidHom 2 : (ZMod m)ˣ →* (ZMod m)ˣ).range

/-- **The squareclass group** `(ℤ/m)ˣ/((ℤ/m)ˣ)²`, written additively (definition; tex 2017–2021). -/
abbrev SqClass (m : ℕ) : Type := Additive ((ZMod m)ˣ ⧸ sqSub m)

/-- A square lies in `sqSub m` (PROVED, GLUE). -/
theorem sq_mem_sqSub {m : ℕ} (u : (ZMod m)ˣ) : u ^ 2 ∈ sqSub m :=
  MonoidHom.mem_range.2 ⟨u, powMonoidHom_apply 2 u⟩

/-- The squareclass group is an elementary two-group (PROVED; tex 2020–2021, "finite elementary
two-group"). -/
theorem sqClass_add_self {m : ℕ} (x : SqClass m) : x + x = 0 := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (s := sqSub m) (Additive.toMul x)
  have hx : x = Additive.ofMul (QuotientGroup.mk u : (ZMod m)ˣ ⧸ sqSub m) := by
    rw [hu]; rfl
  subst hx
  show Additive.ofMul ((QuotientGroup.mk (u * u)) : (ZMod m)ˣ ⧸ sqSub m) = Additive.ofMul 1
  congr 1
  rw [QuotientGroup.eq_one_iff, ← pow_two]
  exact sq_mem_sqSub u

instance (m : ℕ) [NeZero m] : Fintype (SqClass m) := Fintype.ofFinite _

instance (m : ℕ) : DecidableEq (SqClass m) := Classical.decEq _

/-- The class of a unit (definition). -/
def sqMk {m : ℕ} (u : (ZMod m)ˣ) : SqClass m := Additive.ofMul (QuotientGroup.mk u)

/-- `sqMk` is additive (PROVED). -/
theorem sqMk_mul {m : ℕ} (u v : (ZMod m)ˣ) : sqMk (u * v) = sqMk u + sqMk v := rfl

/-- Every squareclass is the class of a unit (PROVED). -/
theorem sqMk_surjective (m : ℕ) : Function.Surjective (sqMk (m := m)) := by
  intro x
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (s := sqSub m) (Additive.toMul x)
  refine ⟨u, ?_⟩
  show Additive.ofMul (QuotientGroup.mk u : (ZMod m)ˣ ⧸ sqSub m) = x
  rw [hu]; rfl

/-- The class of a unit vanishes iff the unit is a square (PROVED). -/
theorem sqMk_eq_zero_iff {m : ℕ} (u : (ZMod m)ˣ) : sqMk u = 0 ↔ u ∈ sqSub m := by
  show (QuotientGroup.mk u : (ZMod m)ˣ ⧸ sqSub m) = 1 ↔ _
  exact QuotientGroup.eq_one_iff u

/-- The class of `1` is `0` (PROVED). -/
theorem sqMk_one {m : ℕ} : sqMk (1 : (ZMod m)ˣ) = 0 :=
  (sqMk_eq_zero_iff 1).2 (one_mem _)

open Classical in
/-- **The type of an integer at the modulus `m`**: its squareclass in `(ℤ/m)ˣ` (`0` if it is not
a unit) (definition; tex 2017–2021). -/
def sqClassOf (m : ℕ) (a : ℤ) : SqClass m :=
  if h : IsUnit (a : ZMod m) then sqMk h.unit else 0

/-- The type of a unit is the class of that unit (PROVED). -/
theorem sqClassOf_of_isUnit {m : ℕ} {a : ℤ} (h : IsUnit (a : ZMod m)) :
    sqClassOf m a = sqMk h.unit := by
  rw [sqClassOf, dite_eq_left h]

/-- The type of an integer congruent to a unit `u` is the class of `u` (PROVED). -/
theorem sqClassOf_eq_sqMk {m : ℕ} {a : ℤ} (u : (ZMod m)ˣ) (h : (a : ZMod m) = (u : ZMod m)) :
    sqClassOf m a = sqMk u := by
  have hu : IsUnit (a : ZMod m) := by rw [h]; exact u.isUnit
  rw [sqClassOf_of_isUnit hu]
  congr 1
  exact Units.ext (by rw [IsUnit.unit_spec, h])

/-- The type of `1` is `0` (PROVED). -/
theorem sqClassOf_one {m : ℕ} : sqClassOf m 1 = 0 := by
  rw [sqClassOf_eq_sqMk 1 (by rw [Int.cast_one, Units.val_one]), sqMk_one]

/-- The type is multiplicative on units (PROVED). -/
theorem sqClassOf_mul {m : ℕ} {a b : ℤ} (ha : IsUnit (a : ZMod m)) (hb : IsUnit (b : ZMod m)) :
    sqClassOf m (a * b) = sqClassOf m a + sqClassOf m b := by
  rw [sqClassOf_of_isUnit ha, sqClassOf_of_isUnit hb, ← sqMk_mul]
  apply sqClassOf_eq_sqMk
  rw [Int.cast_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]

/-- A unit is a square iff its class is zero (PROVED). -/
theorem sqClassOf_eq_zero_iff {m : ℕ} {a : ℤ} (h : IsUnit (a : ZMod m)) :
    sqClassOf m a = 0 ↔ IsSquare (a : ZMod m) := by
  rw [sqClassOf_of_isUnit h, sqMk_eq_zero_iff]
  constructor
  · intro hmem
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 hmem
    refine ⟨(v : ZMod m), ?_⟩
    rw [← IsUnit.unit_spec h, ← hv, powMonoidHom_apply, pow_two, Units.val_mul]
  · rintro ⟨r, hr⟩
    have hr' : IsUnit r := isUnit_of_mul_isUnit_left (hr ▸ h)
    refine MonoidHom.mem_range.2 ⟨hr'.unit, ?_⟩
    apply Units.ext
    rw [powMonoidHom_apply, pow_two, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hr]

/-! ### Characters of the squareclass group -/

/-- A `ZMod 2`-valued additive function on `(ℤ/m)ˣ`, as a homomorphism to `Multiplicative (ZMod 2)`
(definition, GLUE). -/
def charHom {m : ℕ} (s : (ZMod m)ˣ → ZMod 2) (hs : ∀ u v, s (u * v) = s u + s v) :
    (ZMod m)ˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (s u)
  map_one' := by
    have h1 := hs 1 1
    rw [one_mul] at h1
    have h2 : s 1 + s 1 = 0 := zmod2_add_self' (s 1)
    rw [← h1] at h2
    rw [h2, ofAdd_zero]
  map_mul' u v := by
    show Multiplicative.ofAdd (s (u * v)) = Multiplicative.ofAdd (s u) * Multiplicative.ofAdd (s v)
    rw [hs, ofAdd_add]

/-- Squares are in the kernel of such a homomorphism (PROVED, GLUE). -/
theorem sqSub_le_ker {m : ℕ} (s : (ZMod m)ˣ → ZMod 2) (hs : ∀ u v, s (u * v) = s u + s v) :
    sqSub m ≤ (charHom s hs).ker := by
  intro x hx
  obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hx
  rw [MonoidHom.mem_ker]
  show Multiplicative.ofAdd (s ((powMonoidHom 2) v)) = 1
  rw [powMonoidHom_apply, pow_two, hs, zmod2_add_self', ofAdd_zero]

/-- The character of the squareclass group induced by an additive `s : (ℤ/m)ˣ → ZMod 2`
(definition, GLUE). -/
def liftChar {m : ℕ} (s : (ZMod m)ˣ → ZMod 2) (hs : ∀ u v, s (u * v) = s u + s v) :
    SqClass m →+ ZMod 2 :=
  MonoidHom.toAdditiveLeft (QuotientGroup.lift (sqSub m) (charHom s hs) (sqSub_le_ker s hs))

/-- `liftChar s` on the class of a unit `u` is `s u` (PROVED). -/
theorem liftChar_sqMk {m : ℕ} (s : (ZMod m)ˣ → ZMod 2) (hs : ∀ u v, s (u * v) = s u + s v)
    (u : (ZMod m)ˣ) : liftChar s hs (sqMk u) = s u := rfl

/-! ### The sign coordinate -/

/-- The units of `ℤ/4` are `1` and `3` (PROVED). -/
theorem zmod4_unit_cases (u : (ZMod 4)ˣ) : (u : ZMod 4) = 1 ∨ (u : ZMod 4) = 3 := by
  have key : ∀ a b : ZMod 4, a * b = 1 → a = 1 ∨ a = 3 := by decide
  exact key _ _ u.mul_inv

/-- The sign bit of a unit of `ℤ/4`: `0` at `1`, `1` at `3` (definition). -/
def sign4 (u : (ZMod 4)ˣ) : ZMod 2 := if (u : ZMod 4) = 1 then 0 else 1

/-- The sign bit is additive (PROVED). -/
theorem sign4_mul (u v : (ZMod 4)ˣ) : sign4 (u * v) = sign4 u + sign4 v := by
  have key : ∀ a b : ZMod 4, (a = 1 ∨ a = 3) → (b = 1 ∨ b = 3) →
      (if a * b = 1 then (0 : ZMod 2) else 1) = (if a = 1 then 0 else 1) + (if b = 1 then 0 else 1) := by
    decide
  unfold sign4
  rw [Units.val_mul]
  exact key _ _ (zmod4_unit_cases u) (zmod4_unit_cases v)

/-- **The sign coordinate** `ε = (p − 1)/2 mod 2`, the character `u ↦ [u ≡ 3 (mod 4)]` of the
squareclass group (`4 ∣ m`) (definition; tex 2037–2039). It is read through the reduction to
`(ℤ/4)ˣ`. -/
def signChar (m : ℕ) (h4 : 4 ∣ m) : SqClass m →+ ZMod 2 :=
  liftChar (fun u => sign4 (ZMod.unitsMap h4 u)) (fun u v => by rw [map_mul, sign4_mul])

/-- `signChar` on the class of a unit (PROVED). -/
theorem signChar_sqMk {m : ℕ} (h4 : 4 ∣ m) (u : (ZMod m)ˣ) :
    signChar m h4 (sqMk u) = sign4 (ZMod.unitsMap h4 u) := rfl

/-- An integer prime to `m` is a unit modulo `m` (PROVED, GLUE). -/
theorem isUnit_natCast_of_coprime {m p : ℕ} (hpm : Nat.Coprime p m) :
    IsUnit (((p : ℤ)) : ZMod m) := by
  rw [Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime p m).2 hpm

/-- A number prime to an even modulus is odd (PROVED, GLUE). -/
theorem odd_of_coprime_of_two_dvd {m p : ℕ} (h2 : 2 ∣ m) (hpm : Nat.Coprime p m) : Odd p :=
  Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right h2 hpm)

/-- **The sign coordinate of a type** (PROVED; tex 2037–2039): for an odd number `p` prime to
`m`, `ε(type p) = (p − 1)/2 mod 2`. -/
theorem signChar_sqClassOf_natCast {m : ℕ} (h4 : 4 ∣ m) {p : ℕ} (hpm : Nat.Coprime p m) :
    signChar m h4 (sqClassOf m p) = ((p / 2 : ℕ) : ZMod 2) := by
  have hpu := isUnit_natCast_of_coprime hpm
  have hodd : p % 2 = 1 :=
    Nat.odd_iff.mp (odd_of_coprime_of_two_dvd ((show (2 : ℕ) ∣ 4 by norm_num).trans h4) hpm)
  rw [sqClassOf_of_isUnit hpu, signChar_sqMk, sign4, ZMod.unitsMap_val, IsUnit.unit_spec,
    ZMod.cast_intCast h4, Int.cast_natCast, ← ZMod.natCast_mod p 4, ← ZMod.natCast_mod (p / 2) 2]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [h, (by omega : p / 2 % 2 = 0)]; decide
  · rw [h, (by omega : p / 2 % 2 = 1)]; decide

/-- **The sign coordinate of a prime** (PROVED; tex 2037–2039). -/
theorem signChar_sqClassOf {m : ℕ} (h4 : 4 ∣ m) {p : ℕ} (hp : p.Prime) (hpm : Nat.Coprime p m) :
    signChar m h4 (sqClassOf m p) = ((p / 2 : ℕ) : ZMod 2) := by
  have _hp2 := hp.two_le
  exact signChar_sqClassOf_natCast h4 hpm

/-! ### The type data -/

/-- **The genuine type data at the modulus `m`** (Definition `ex:sec7-typed-graph`, tex 2015–2025;
Lemma `ex:sec7-realization`, tex 2162–2163: "the fixed type is a reduced residue condition at a
modulus supported on `S_lab`, including eight"): the type of a prime is its squareclass in
`(ℤ/m)ˣ`; `classes` and `sign` are PROVED. -/
def typeData (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) : TypeData (SqClass m) (signChar m h4) where
  m := m
  m_pos := hm
  two_dvd := (show (2 : ℕ) ∣ 4 by norm_num).trans h4
  typ p := sqClassOf m p
  classes := by
    intro ℓ
    obtain ⟨u, rfl⟩ := sqMk_surjective m ℓ
    refine ⟨(u : ZMod m), u.isUnit, fun p _ hp => ?_⟩
    exact sqClassOf_eq_sqMk u (by rw [Int.cast_natCast, hp])
  sign := fun _ hp hpm => signChar_sqClassOf h4 hp hpm

/-- The type of `typeData` (PROVED, `rfl`). -/
theorem typeData_typ (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (p : ℕ) :
    (typeData m hm h4).typ p = sqClassOf m p := rfl

/-- The conductor of `typeData` (PROVED, `rfl`). -/
theorem typeData_m (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) : (typeData m hm h4).m = m := rfl

/-! ### Projections between moduli -/

/-- The projection of squareclasses for `m₁ ∣ m` (definition). -/
def sqProj {m₁ m : ℕ} (h : m₁ ∣ m) : SqClass m →+ SqClass m₁ :=
  MonoidHom.toAdditive (QuotientGroup.map (sqSub m) (sqSub m₁) (ZMod.unitsMap h) (by
    intro x hx
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hx
    refine Subgroup.mem_comap.2 (MonoidHom.mem_range.2 ⟨ZMod.unitsMap h v, ?_⟩)
    rw [powMonoidHom_apply, powMonoidHom_apply, map_pow]))

/-- `sqProj` on the class of a unit (PROVED). -/
theorem sqProj_sqMk {m₁ m : ℕ} (h : m₁ ∣ m) (u : (ZMod m)ˣ) :
    sqProj h (sqMk u) = sqMk (ZMod.unitsMap h u) := rfl

/-- Projections compose (PROVED). -/
theorem sqProj_comp {m₁ m₂ m : ℕ} (h₁ : m₁ ∣ m₂) (h₂ : m₂ ∣ m) (x : SqClass m) :
    sqProj h₁ (sqProj h₂ x) = sqProj (h₁.trans h₂) x := by
  obtain ⟨u, rfl⟩ := sqMk_surjective m x
  rw [sqProj_sqMk, sqProj_sqMk, sqProj_sqMk, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]

/-- The projection is surjective (PROVED). -/
theorem sqProj_surjective {m₁ m : ℕ} [NeZero m] (h : m₁ ∣ m) :
    Function.Surjective (sqProj h) := by
  intro y
  obtain ⟨u, rfl⟩ := sqMk_surjective m₁ y
  obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective h u
  exact ⟨sqMk v, sqProj_sqMk h v⟩

/-- The projection of the type of an integer is its type (PROVED). -/
theorem sqProj_sqClassOf {m₁ m : ℕ} (h : m₁ ∣ m) {a : ℤ} (ha : IsUnit (a : ZMod m)) :
    sqProj h (sqClassOf m a) = sqClassOf m₁ a := by
  rw [sqClassOf_of_isUnit ha, sqProj_sqMk]
  symm
  apply sqClassOf_eq_sqMk
  rw [ZMod.unitsMap_val, IsUnit.unit_spec, ZMod.cast_intCast h]

/-- The sign coordinate commutes with projections (PROVED). -/
theorem signChar_sqProj {m₁ m : ℕ} (h : m₁ ∣ m) (h4 : 4 ∣ m₁) (x : SqClass m) :
    signChar m₁ h4 (sqProj h x) = signChar m (h4.trans h) x := by
  obtain ⟨u, rfl⟩ := sqMk_surjective m x
  rw [sqProj_sqMk, signChar_sqMk, signChar_sqMk, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]

/-! ### The Kronecker character of `K = ℚ(√k)` -/

/-- For a unit `u` modulo `4|k|`, its least nonnegative representative is odd and `J(k | u) = ±1`
(PROVED). -/
theorem odd_and_jacobi_of_unit {k : ℤ} (u : (ZMod (4 * k.natAbs))ˣ) :
    Odd (u : ZMod (4 * k.natAbs)).val ∧ (jacobiSym k (u : ZMod (4 * k.natAbs)).val = 1 ∨
      jacobiSym k (u : ZMod (4 * k.natAbs)).val = -1) := by
  have hcop := ZMod.val_coe_unit_coprime u
  refine ⟨odd_of_coprime_of_two_dvd (Dvd.dvd.mul_right (by norm_num) _) hcop, ?_⟩
  apply jacobiSym.eq_one_or_neg_one
  rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
  exact Nat.Coprime.coprime_dvd_left (Dvd.intro_left 4 rfl) hcop.symm

/-- The splitting bit of a unit modulo `4|k|`: `1` iff `J(k | u) = −1` at its least nonnegative
representative (definition). -/
def kBit (k : ℤ) (u : (ZMod (4 * k.natAbs))ˣ) : ZMod 2 :=
  if jacobiSym k (u : ZMod (4 * k.natAbs)).val = -1 then 1 else 0

/-- The splitting bit is additive (PROVED: Jacobi multiplicativity and periodicity). -/
theorem kBit_mul (k : ℤ) (u v : (ZMod (4 * k.natAbs))ˣ) : kBit k (u * v) = kBit k u + kBit k v := by
  unfold kBit
  obtain ⟨hu_odd, hu⟩ := odd_and_jacobi_of_unit u
  obtain ⟨hv_odd, hv⟩ := odd_and_jacobi_of_unit v
  have hmul : jacobiSym k ((u * v : (ZMod (4 * k.natAbs))ˣ) : ZMod (4 * k.natAbs)).val =
      jacobiSym k (u : ZMod (4 * k.natAbs)).val * jacobiSym k (v : ZMod (4 * k.natAbs)).val := by
    rw [Units.val_mul, ZMod.val_mul, ← jacobiSym.mod_right k (hu_odd.mul hv_odd),
      jacobiSym.mul_right' k hu_odd.pos.ne' hv_odd.pos.ne']
  rw [hmul]
  rcases hu with h1 | h1 <;> rcases hv with h2 | h2 <;> rw [h1, h2] <;> decide

/-- **The splitting character of `K = ℚ(√k)`** on squareclasses modulo `m` (`4|k| ∣ m`):
`u ↦ [J(k | u) = −1]`, `J` the Jacobi symbol at the least nonnegative representative of the
reduction of `u` modulo `4|k|` (definition; tex 2017–2018, 2596–2601, 2679). -/
def kChar (m : ℕ) (k : ℤ) (hk : 4 * k.natAbs ∣ m) : SqClass m →+ ZMod 2 :=
  liftChar (fun u => kBit k (ZMod.unitsMap hk u)) (fun u v => by rw [map_mul, kBit_mul])

/-- `kChar` on the class of a unit (PROVED). -/
theorem kChar_sqMk {m : ℕ} {k : ℤ} (hk : 4 * k.natAbs ∣ m) (u : (ZMod m)ˣ) :
    kChar m k hk (sqMk u) = kBit k (ZMod.unitsMap hk u) := rfl

/-- **`χ_k` at the type of a number `w` prime to `m`** (PROVED, Jacobi periodicity):
`χ_k(type w) = [J(k | w) = −1]`. -/
theorem kChar_sqClassOf_natCast {m : ℕ} {k : ℤ} (hk : 4 * k.natAbs ∣ m) {w : ℕ}
    (hw : Nat.Coprime w m) :
    kChar m k hk (sqClassOf m w) = if jacobiSym k w = -1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hw1 : w = 1 := (Nat.coprime_zero_right w).1 hw
    subst hw1
    rw [Nat.cast_one, sqClassOf_one, map_zero, jacobiSym.one_right, ite_eq_right (by decide)]
  · have hwu := isUnit_natCast_of_coprime hw
    have hwN : Nat.Coprime w (4 * k.natAbs) := Nat.Coprime.coprime_dvd_right hk hw
    have hw_odd : Odd w := odd_of_coprime_of_two_dvd (Dvd.dvd.mul_right (by norm_num) _) hwN
    rw [sqClassOf_of_isUnit hwu, kChar_sqMk, kBit, ZMod.unitsMap_val, IsUnit.unit_spec,
      ZMod.cast_intCast hk, Int.cast_natCast, ZMod.val_natCast, ← jacobiSym.mod_right k hw_odd]

/-- **`χ_k` reads the splitting in `K`** (PROVED, Jacobi periodicity; tex 2679): for a prime
`p ∤ m`, `χ_k(type p) = 0 ↔ (k/p) = 1`. -/
theorem kChar_sqClassOf_eq_zero_iff {m : ℕ} {k : ℤ} (hk : 4 * k.natAbs ∣ m) {p : ℕ}
    (hp : p.Prime) (hpm : Nat.Coprime p m) :
    kChar m k hk (sqClassOf m p) = 0 ↔ jacobiSym k p = 1 := by
  have _hp2 := hp.two_le
  rw [kChar_sqClassOf_natCast hk hpm]
  have hgcd : k.gcd (p : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact Nat.Coprime.coprime_dvd_left ((Dvd.intro_left 4 rfl).trans hk) hpm.symm
  rcases jacobiSym.eq_one_or_neg_one hgcd with h | h
  · rw [h, ite_eq_right (by decide)]; exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [h, ite_eq_left rfl]; exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (by decide)⟩

/-- The `K`-split classes, as a subgroup (definition). -/
def kSplitSub (m : ℕ) (k : ℤ) (hk : 4 * k.natAbs ∣ m) : AddSubgroup (SqClass m) where
  carrier := {x | kChar m k hk x = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  neg_mem' := by intro a ha; simp_all

/-- The `K`-split classes (definition). -/
abbrev KSplitClass (m : ℕ) (k : ℤ) (hk : 4 * k.natAbs ∣ m) : Type := kSplitSub m k hk

/-! ### Lane RC24 additions: projections of `K`-split classes -/

/-- Membership in `kSplitSub` (PROVED, `Iff.rfl`). -/
theorem mem_kSplitSub {m : ℕ} {k : ℤ} {hk : 4 * k.natAbs ∣ m} {x : SqClass m} :
    x ∈ kSplitSub m k hk ↔ kChar m k hk x = 0 := Iff.rfl

/-- **`χ_k` commutes with the projections** (PROVED; tex 2600–2608): for `4|k| ∣ m₂ ∣ m`,
`χ_k` modulo `m₂` of the projection of `x` is `χ_k(x)` modulo `m`. -/
theorem kChar_sqProj {m₂ m : ℕ} (h : m₂ ∣ m) {k : ℤ} (hk₂ : 4 * k.natAbs ∣ m₂) (x : SqClass m) :
    kChar m₂ k hk₂ (sqProj h x) = kChar m k (hk₂.trans h) x := by
  obtain ⟨u, rfl⟩ := sqMk_surjective m x
  rw [sqProj_sqMk, kChar_sqMk, kChar_sqMk, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]

/-- **The projection of `K`-split classes** `KSplitClass m k → KSplitClass m₂ k` for
`4|k| ∣ m₂ ∣ m` (definition; tex 2600–2608, 10283–10286, "separate surjective projections"):
the restriction of `sqProj`. -/
def kSplitProj {m₂ m : ℕ} (h : m₂ ∣ m) {k : ℤ} (hk₂ : 4 * k.natAbs ∣ m₂) :
    KSplitClass m k (hk₂.trans h) →+ KSplitClass m₂ k hk₂ :=
  ((sqProj h).comp (kSplitSub m k (hk₂.trans h)).subtype).codRestrict (kSplitSub m₂ k hk₂)
    (fun x => by
      show kChar m₂ k hk₂ (sqProj h (x : SqClass m)) = 0
      rw [kChar_sqProj]
      exact x.2)

/-- `kSplitProj` is `sqProj` on the underlying classes (PROVED, `rfl`). -/
theorem kSplitProj_coe {m₂ m : ℕ} (h : m₂ ∣ m) {k : ℤ} (hk₂ : 4 * k.natAbs ∣ m₂)
    (x : KSplitClass m k (hk₂.trans h)) :
    ((kSplitProj h hk₂ x : SqClass m₂)) = sqProj h x := rfl

/-- **The projection of `K`-split classes is surjective** (PROVED; tex 10283–10286, "its separate
surjective projections"). -/
theorem kSplitProj_surjective {m₂ m : ℕ} [NeZero m] (h : m₂ ∣ m) {k : ℤ}
    (hk₂ : 4 * k.natAbs ∣ m₂) : Function.Surjective (kSplitProj h hk₂) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := sqProj_surjective h y
  refine ⟨⟨x, ?_⟩, Subtype.ext rfl⟩
  rw [mem_kSplitSub, ← kChar_sqProj h hk₂]
  exact hy

/-! ### Fresh ramification: lifts of old labels to `K`-split labels -/

/-- In `ZMod 2` a nonzero element is `1` (PROVED). -/
theorem zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a; decide

/-- **A `K`-nonsplit class trivial at the old modulus** (PROVED; tex 2600–2608, 10283–10286): if a
prime `q₀` of the odd squarefree `k` does not divide `m₁` (fresh ramification), there is a class
modulo `m` (`m₁ ∣ m`, `4 ∣ m₁`, `4|k| ∣ m`) which projects to `0` modulo `m₁` and has `χ_k = 1`.
It is the class of `w ≡ 1` modulo the prime-to-`q₀` part of `m` and `w ≡` a nonresidue modulo
the `q₀`-part; Jacobi reciprocity gives `J(k | w) = J(w | q₀) = −1`. -/
theorem exists_kChar_one_of_fresh {m₁ m : ℕ} [NeZero m] (h : m₁ ∣ m) (h4 : 4 ∣ m₁) {k : ℤ}
    (hk : 4 * k.natAbs ∣ m) (hk_odd : Odd k) (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime)
    (hq₀k : (q₀ : ℤ) ∣ k) (hq₀m₁ : ¬ q₀ ∣ m₁) :
    ∃ w : SqClass m, kChar m k hk w = 1 ∧ sqProj h w = 0 := by
  have hn_odd : Odd k.natAbs := Int.natAbs_odd.2 hk_odd
  have hn_sf : Squarefree k.natAbs := Int.squarefree_natAbs.2 hk_sf
  have hq₀n : q₀ ∣ k.natAbs := Int.natCast_dvd.1 hq₀k
  have hn0 : k.natAbs ≠ 0 := hn_odd.pos.ne'
  have hm0 : m ≠ 0 := NeZero.ne m
  have hnm : k.natAbs ∣ m := (Dvd.intro_left 4 rfl).trans hk
  have hq₀2 : q₀ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hn_odd) (even_iff_two_dvd.2 hq₀n)
  -- `m = q₀ ^ e * m'` with `q₀ ∤ m'`
  obtain ⟨e, m', hq₀m', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 q₀ hq₀.one_lt.ne'
  have hq₀m : q₀ ∣ m := hq₀n.trans hnm
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hmeq
    exact hq₀m' (hmeq ▸ hq₀m)
  have hcop_q₀ : Nat.Coprime (q₀ ^ e) m' :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq₀).2 hq₀m')
  have hm₁m' : m₁ ∣ m' := by
    have hc : Nat.Coprime m₁ (q₀ ^ e) :=
      (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq₀).2 hq₀m₁)).symm
    exact hc.dvd_of_dvd_mul_left (hmeq ▸ h)
  -- `|k| = q₀ * n'` with `q₀ ∤ n'` (squarefree) and `n' ∣ m'`
  obtain ⟨n', hn'⟩ := hq₀n
  have hq₀n' : ¬ q₀ ∣ n' := by
    rintro ⟨c, rfl⟩
    have hu := hn_sf q₀ ⟨c, by rw [hn']; ring⟩
    exact hq₀.one_lt.ne' (Nat.isUnit_iff.1 hu)
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hn'
    exact hn0 hn'
  have hn'm' : n' ∣ m' := by
    have hc : Nat.Coprime n' (q₀ ^ e) :=
      (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq₀).2 hq₀n')).symm
    have hn'm : n' ∣ m := (Dvd.intro_left q₀ hn'.symm).trans hnm
    exact hc.dvd_of_dvd_mul_left (hmeq ▸ hn'm)
  -- a nonresidue `g` modulo `q₀`
  obtain ⟨g, hg_ndvd, hg⟩ := exists_residue_bit hq₀ hq₀2 1
  have hg_ns : ¬ IsSquare (((g : ℤ)) : ZMod q₀) := by
    intro hsq
    rw [legBit_of_isSquare hsq] at hg
    exact absurd hg (by decide)
  -- CRT: `w ≡ g (mod q₀ ^ e)` and `w ≡ 1 (mod m')`
  obtain ⟨w, hwq, hw1⟩ := Nat.chineseRemainder hcop_q₀ g 1
  have hwq₀ : w ≡ g [MOD q₀] := Nat.ModEq.of_dvd (dvd_pow_self q₀ he) hwq
  have hw4 : w % 4 = 1 := by
    have h' := Nat.ModEq.of_dvd (h4.trans hm₁m') hw1
    unfold Nat.ModEq at h'
    omega
  have hw_odd : Odd w := Nat.odd_iff.2 (by omega)
  have hwq₀' : Nat.Coprime w q₀ :=
    ((Nat.Prime.coprime_iff_not_dvd hq₀).2
      (fun hd => hg_ndvd ((Nat.ModEq.dvd_iff hwq₀ dvd_rfl).1 hd))).symm
  have hwm' : Nat.Coprime w m' := by
    have hg1 := Nat.ModEq.gcd_eq hw1
    rw [Nat.gcd_one_left] at hg1
    exact hg1
  have hwm : Nat.Coprime w m := by
    rw [hmeq]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right e hwq₀') hwm'
  -- `J(k | w) = −1`
  have hJ : jacobiSym k w = -1 := by
    have hJn : jacobiSym k w = jacobiSym (k.natAbs : ℤ) w := by
      rcases Int.natAbs_eq k with hk' | hk'
      · exact congrArg (fun a => jacobiSym a w) hk'
      · rw [hk', jacobiSym.neg _ hw_odd, ZMod.χ₄_nat_one_mod_four hw4, one_mul, Int.natAbs_neg,
          Int.natAbs_natCast]
    have hJq : jacobiSym (w : ℤ) q₀ = -1 := by
      have := Fact.mk hq₀
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
      have hwg : (((w : ℤ)) : ZMod q₀) = (((g : ℤ)) : ZMod q₀) := by
        rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_eq_natCast_iff']
        exact hwq₀
      rw [hwg]
      exact hg_ns
    have hJn' : jacobiSym (w : ℤ) n' = 1 := by
      have hmod : (w : ℤ) % (n' : ℤ) = ((1 : ℕ) : ℤ) % (n' : ℤ) := by
        rw [← Int.natCast_mod, ← Int.natCast_mod]
        exact congrArg _ (Nat.ModEq.of_dvd hn'm' hw1)
      rw [jacobiSym.mod_left' hmod, Nat.cast_one, jacobiSym.one_left]
    rw [hJn, jacobiSym.quadratic_reciprocity_one_mod_four' hn_odd hw4, hn',
      jacobiSym.mul_right' _ hq₀.ne_zero hn'0, hJq, hJn', mul_one]
  refine ⟨sqClassOf m w, ?_, ?_⟩
  · rw [kChar_sqClassOf_natCast hk hwm, ite_eq_left hJ]
  · rw [sqProj_sqClassOf h (isUnit_natCast_of_coprime hwm)]
    have h1 : (((w : ℤ)) : ZMod m₁) = ((1 : (ZMod m₁)ˣ) : ZMod m₁) := by
      rw [Int.cast_natCast, Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
      exact Nat.ModEq.of_dvd hm₁m' hw1
    rw [sqClassOf_eq_sqMk 1 h1, sqMk_one]

/-- **Fresh-ramification lift** (PROVED; tex 2600–2608: "The fresh ramified prime of `K` lies
outside this set, so its intersection with `K` is `ℚ`. Thus each old odd label still has a lift
split in `K`"; tex 10283–10286: "Fresh ramification implies that every old odd label still lifts
to a `K`-split label"): if a prime `q₀ ∣ k` (`k` odd squarefree) does not divide the old modulus
`m₁`, every old class modulo `m₁` lifts to a `K`-split class modulo `m`. -/
theorem exists_kSplit_lift {m₁ m : ℕ} [NeZero m] (h : m₁ ∣ m) (h4 : 4 ∣ m₁) {k : ℤ}
    (hk : 4 * k.natAbs ∣ m) (hk_odd : Odd k) (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime)
    (hq₀k : (q₀ : ℤ) ∣ k) (hq₀m₁ : ¬ q₀ ∣ m₁) (y : SqClass m₁) :
    ∃ x : SqClass m, kChar m k hk x = 0 ∧ sqProj h x = y := by
  obtain ⟨x₀, hx₀⟩ := sqProj_surjective h y
  by_cases h0 : kChar m k hk x₀ = 0
  · exact ⟨x₀, h0, hx₀⟩
  · obtain ⟨w, hw1, hw0⟩ := exists_kChar_one_of_fresh h h4 hk hk_odd hk_sf hq₀ hq₀k hq₀m₁
    refine ⟨x₀ + w, ?_, ?_⟩
    · rw [map_add, zmod2_eq_one_of_ne_zero h0, hw1]
      decide
    · rw [map_add, hx₀, hw0]
      exact add_zero y

/-! ### Stage type data with the moving theta prime -/

/-- **The sign character of a stage alphabet** `SqClass m₁ × ZMod 2`: the sign coordinate of the
squareclass factor (definition; tex 2037–2039). -/
def stageSign (m₁ : ℕ) (h4 : 4 ∣ m₁) : SqClass m₁ × ZMod 2 →+ ZMod 2 :=
  (signChar m₁ h4).comp (AddMonoidHom.fst _ _)

/-- **Stage type data with the moving theta prime `ℓ₀`** (definition with PROVED fields;
tex 2024–2025: "For an odd theta stage, its reduction prime is part of this fixed support during
that stage"; tex 10527–10532: "The moving theta prime contributes only a bounded number of
quadratic label coordinates"): the type of a prime `p` is its squareclass modulo `m₁` together
with its residue bit at `ℓ₀`, read modulo `m₁ ℓ₀`. `classes` is PROVED by CRT and
`exists_residue_bit`; `sign` from `signChar_sqClassOf`. -/
def stageTypeData (m₁ : ℕ) (hm : 0 < m₁) (h4 : 4 ∣ m₁) (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime)
    (hcop : Nat.Coprime ℓ₀ m₁) : TypeData (SqClass m₁ × ZMod 2) (stageSign m₁ h4) where
  m := m₁ * ℓ₀
  m_pos := Nat.mul_pos hm hℓ₀.pos
  two_dvd := Dvd.dvd.mul_right ((show (2 : ℕ) ∣ 4 by norm_num).trans h4) ℓ₀
  typ p := (sqClassOf m₁ p, legBit p ℓ₀)
  classes := by
    rintro ⟨s, b⟩
    obtain ⟨u, rfl⟩ := sqMk_surjective m₁ s
    have hℓ₀2 : ℓ₀ ≠ 2 := ne_two_of_coprime_even ((show (2 : ℕ) ∣ 4 by norm_num).trans h4) hcop
    obtain ⟨a, ha, hab⟩ := exists_residue_bit hℓ₀ hℓ₀2 b
    have e : ZMod (m₁ * ℓ₀) ≃+* ZMod m₁ × ZMod ℓ₀ := ZMod.chineseRemainder hcop.symm
    have hau : IsUnit (a : ZMod ℓ₀) :=
      (ZMod.isUnit_iff_coprime a ℓ₀).2 ((Nat.Prime.coprime_iff_not_dvd hℓ₀).2 ha).symm
    refine ⟨e.symm ((u : ZMod m₁), (a : ZMod ℓ₀)),
      (MulEquiv.isUnit_map e.symm).2 (Prod.isUnit_iff.2 ⟨u.isUnit, hau⟩), fun p _ hp => ?_⟩
    have h1 : e (p : ZMod (m₁ * ℓ₀)) = ((u : ZMod m₁), (a : ZMod ℓ₀)) := by
      rw [hp, RingEquiv.apply_symm_apply]
    rw [map_natCast] at h1
    have hpu : (p : ZMod m₁) = u := by
      have h2 := congrArg Prod.fst h1
      rwa [Prod.fst_natCast] at h2
    have hpa : (p : ZMod ℓ₀) = a := by
      have h2 := congrArg Prod.snd h1
      rwa [Prod.snd_natCast] at h2
    show (sqClassOf m₁ p, legBit p ℓ₀) = (sqMk u, b)
    refine Prod.ext (sqClassOf_eq_sqMk u (by rw [Int.cast_natCast, hpu])) ?_
    show legBit p ℓ₀ = b
    rw [← hab]
    apply legBit_congr
    rw [Int.cast_natCast, Int.cast_natCast, hpa]
  sign := fun p hp hpm => by
    show signChar m₁ h4 (sqClassOf m₁ p) = _
    exact signChar_sqClassOf h4 hp (Nat.Coprime.coprime_mul_right_right hpm)

/-- The type of `stageTypeData` (PROVED, `rfl`). -/
theorem stageTypeData_typ (m₁ : ℕ) (hm : 0 < m₁) (h4 : 4 ∣ m₁) (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime)
    (hcop : Nat.Coprime ℓ₀ m₁) (p : ℕ) :
    (stageTypeData m₁ hm h4 ℓ₀ hℓ₀ hcop).typ p = (sqClassOf m₁ p, legBit p ℓ₀) := rfl

/-- The conductor of `stageTypeData` (PROVED, `rfl`). -/
theorem stageTypeData_m (m₁ : ℕ) (hm : 0 < m₁) (h4 : 4 ∣ m₁) (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime)
    (hcop : Nat.Coprime ℓ₀ m₁) : (stageTypeData m₁ hm h4 ℓ₀ hℓ₀ hcop).m = m₁ * ℓ₀ := rfl

/-! ### Multiplicativity of types and residue bits -/

/-- **The type of a product** is the sum of the types (PROVED; tex 2050–2053: a contracted vertex has the sum of the types and the product
template). -/
theorem sqClassOf_prod {m : ℕ} (s : Finset ℕ) (f : ℕ → ℤ)
    (h : ∀ i ∈ s, IsUnit ((f i : ℤ) : ZMod m)) :
    sqClassOf m (∏ i ∈ s, f i) = ∑ i ∈ s, sqClassOf m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, sqClassOf_one]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsUnit ((f i : ℤ) : ZMod m) :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hprod : IsUnit (((∏ i ∈ s, f i : ℤ)) : ZMod m) :=
      Finset.prod_induction f (fun x : ℤ => IsUnit (x : ZMod m))
        (fun x y hx hy => by rw [Int.cast_mul]; exact hx.mul hy)
        (by rw [Int.cast_one]; exact isUnit_one) hs
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      sqClassOf_mul (h a (Finset.mem_insert_self a s)) hprod, ih hs]

/-- `legBit a q = 0` iff `a` is a square modulo `q` (PROVED, from the definition). -/
theorem legBit_eq_zero_iff {a : ℤ} {q : ℕ} : legBit a q = 0 ↔ IsSquare (a : ZMod q) := by
  constructor
  · intro h
    by_contra hns
    rw [legBit_of_not_isSquare hns] at h
    exact absurd h (by decide)
  · exact legBit_of_isSquare

/-- `legBit` through the Legendre symbol (PROVED). -/
theorem legBit_eq_ite_legendreSym {a : ℤ} {q : ℕ} [Fact q.Prime] (ha : ¬ (q : ℤ) ∣ a) :
    legBit a q = if legendreSym q a = 1 then 0 else 1 := by
  have ha0 : (a : ZMod q) ≠ 0 := fun h0 => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).1 h0)
  by_cases hsq : IsSquare (a : ZMod q)
  · rw [legBit_of_isSquare hsq, ite_eq_left ((legendreSym.eq_one_iff q ha0).2 hsq)]
  · rw [legBit_of_not_isSquare hsq,
      ite_eq_right (fun h1 => hsq ((legendreSym.eq_one_iff q ha0).1 h1))]

/-- **Multiplicativity of residue bits** (PROVED: multiplicativity of the Legendre symbol;
tex 2050–2053, incidences of a product template add): `z(ab, q) = z(a, q) + z(b, q)` for `q ∤ ab`. -/
theorem legBit_mul {a b : ℤ} {q : ℕ} (hq : q.Prime) (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) :
    legBit (a * b) q = legBit a q + legBit b q := by
  have := Fact.mk hq
  have hq' : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hab : ¬ (q : ℤ) ∣ a * b := fun hd => (hq'.dvd_or_dvd hd).elim ha hb
  have ha0 : (a : ZMod q) ≠ 0 := fun h0 => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).1 h0)
  have hb0 : (b : ZMod q) ≠ 0 := fun h0 => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b q).1 h0)
  rw [legBit_eq_ite_legendreSym ha, legBit_eq_ite_legendreSym hb, legBit_eq_ite_legendreSym hab,
    legendreSym.mul]
  rcases legendreSym.eq_one_or_neg_one q ha0 with h1 | h1 <;>
    rcases legendreSym.eq_one_or_neg_one q hb0 with h2 | h2 <;> rw [h1, h2] <;> decide

/-- **Residue bit of a product** (PROVED; tex 2050–2053): the bit of `∏ f i` at `q` is the sum of
the bits, for `q` prime to every factor. -/
theorem legBit_prod {q : ℕ} (s : Finset ℕ) (f : ℕ → ℤ) (hq : q.Prime)
    (h : ∀ i ∈ s, ¬ (q : ℤ) ∣ f i) :
    legBit (∏ i ∈ s, f i) q = ∑ i ∈ s, legBit (f i) q := by
  classical
  have hq' : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact legBit_of_isSquare ⟨1, by rw [Int.cast_one, mul_one]⟩
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ¬ (q : ℤ) ∣ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hprod : ¬ (q : ℤ) ∣ ∏ i ∈ s, f i := by
      rw [Prime.dvd_finsetProd_iff hq']
      rintro ⟨i, hi, hd⟩
      exact hs i hi hd
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      legBit_mul hq (h a (Finset.mem_insert_self a s)) hprod, ih hs]

/-! ### The signed factors `q^*` -/

/-- The type of `(−1)^n` (PROVED). -/
theorem sqClassOf_neg_one_pow {m : ℕ} (n : ℕ) :
    sqClassOf m ((-1 : ℤ) ^ n) = n • sqClassOf m (-1) := by
  have hu : IsUnit (((-1 : ℤ)) : ZMod m) := by
    rw [Int.cast_neg, Int.cast_one]; exact isUnit_one.neg
  induction n with
  | zero => rw [pow_zero, zero_nsmul, sqClassOf_one]
  | succ n ih =>
    have hpow : IsUnit ((((-1 : ℤ) ^ n : ℤ)) : ZMod m) := by rw [Int.cast_pow]; exact hu.pow n
    rw [pow_succ, sqClassOf_mul hpow hu, ih, succ_nsmul]

/-- **The type of `q^* = (−1)^{(q−1)/2} q`** (PROVED; tex 2045–2048, 2682–2684): for `q` prime to
`m`, `type(q^*) = ((q − 1)/2) • type(−1) + type(q)`. -/
theorem sqClassOf_qstar {m : ℕ} {q : ℕ} (hqm : Nat.Coprime q m) :
    sqClassOf m (qstar q) = ((q - 1) / 2) • sqClassOf m (-1) + sqClassOf m q := by
  have hu : IsUnit (((-1 : ℤ)) : ZMod m) := by
    rw [Int.cast_neg, Int.cast_one]; exact isUnit_one.neg
  have hpow : IsUnit ((((-1 : ℤ) ^ ((q - 1) / 2) : ℤ)) : ZMod m) := by
    rw [Int.cast_pow]; exact hu.pow _
  rw [qstar, sqClassOf_mul hpow (isUnit_natCast_of_coprime hqm), sqClassOf_neg_one_pow]

/-- `∏ q^* = (−1)^{Σ (q−1)/2} ∏ q` (PROVED). -/
theorem prod_qstar (Q : Finset ℕ) :
    ∏ q ∈ Q, qstar q = (-1) ^ (∑ q ∈ Q, (q - 1) / 2) * ∏ q ∈ Q, (q : ℤ) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  rfl

/-- The total sign coordinate of numbers prime to `m` is the parity of `Σ (q − 1)/2` (PROVED;
tex 2037–2039). -/
theorem sum_signChar_sqClassOf {m : ℕ} (h4 : 4 ∣ m) {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, Nat.Coprime q m) :
    ∑ q ∈ Q, signChar m h4 (sqClassOf m q) = ((∑ q ∈ Q, (q - 1) / 2 : ℕ) : ZMod 2) := by
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [signChar_sqClassOf_natCast h4 (hQ q hq)]
  have hodd : q % 2 = 1 := Nat.odd_iff.mp
    (odd_of_coprime_of_two_dvd ((show (2 : ℕ) ∣ 4 by norm_num).trans h4) (hQ q hq))
  rw [(by omega : (q - 1) / 2 = q / 2)]

/-- **The sign of `∏ q^*` is the product of the signs** (PROVED; tex 2043–2048, 2682–2684): for numbers `q`
prime to `m` (`4 ∣ m`) whose sign coordinates sum to `0`, `∏ q^* = ∏ q`. -/
theorem prod_qstar_eq_prod_of_sign_zero {m : ℕ} (h4 : 4 ∣ m) {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, Nat.Coprime q m) (hsign : ∑ q ∈ Q, signChar m h4 (sqClassOf m q) = 0) :
    ∏ q ∈ Q, qstar q = ∏ q ∈ Q, (q : ℤ) := by
  rw [sum_signChar_sqClassOf h4 hQ, ZMod.natCast_eq_zero_iff_even] at hsign
  rw [prod_qstar, hsign.neg_one_pow, one_mul]

/-- **`∏ q^* > 0` iff the sign coordinates sum to `0`** (PROVED; tex 2043–2048, 2682–2684). -/
theorem prod_qstar_pos_iff {m : ℕ} (h4 : 4 ∣ m) {Q : Finset ℕ} (hQ : ∀ q ∈ Q, Nat.Coprime q m) :
    0 < ∏ q ∈ Q, qstar q ↔ ∑ q ∈ Q, signChar m h4 (sqClassOf m q) = 0 := by
  have hpos : 0 < ∏ q ∈ Q, (q : ℤ) := Finset.prod_pos (fun q hq => by
    have hq0 := (odd_of_coprime_of_two_dvd ((show (2 : ℕ) ∣ 4 by norm_num).trans h4) (hQ q hq)).pos
    exact_mod_cast hq0)
  rw [sum_signChar_sqClassOf h4 hQ, ZMod.natCast_eq_zero_iff_even, prod_qstar]
  rcases Nat.even_or_odd (∑ q ∈ Q, (q - 1) / 2) with he | ho
  · rw [he.neg_one_pow, one_mul]
    exact ⟨fun _ => he, fun _ => hpos⟩
  · rw [ho.neg_one_pow, neg_one_mul]
    constructor
    · intro h
      exact absurd h (not_lt.2 (neg_nonpos.2 hpos.le))
    · intro h
      exact absurd h (Nat.not_even_iff_odd.2 ho)

end ZInQ.Manuscript.RC.AddressGenuine

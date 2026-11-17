import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 7: the local diagrams at a derivative place

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
"The local diagrams underlying the coefficient push", tex lines 3297–3336.

* The two-generator tame resolution `[M → M ⊕ M → M]`, `u ↦ ((Φ_v - 1)u, 0)`,
  `(x, y) ↦ (Φ_v - q) y`, is a complex, and at the retained exponent (where `Φ_v` acts trivially
  and `q ≡ 1`) it has zero differential: the model `D⁰ ⊕ (F_v ⊕ S_v)[-1] ⊕ D²[-2]`
  (tex 3301–3309).  `PROVED`.
* With compatible generators, in the order `D⁰, F_v, S_v, D²`,
  `res = diag(1, f, e, ef)` and `cor = diag(ef, e, f, 1)`; these preserve each of the four
  conditions retaining `D⁰`, satisfy the cup-product adjunction `⟨res x, y⟩ = ⟨x, cor y⟩` entry by
  entry, and `cor ∘ res = ef` (tex 3318–3333).  `PROVED`.
* The possible transfer shear is divisible by `(q - 1)/2` and vanishes at retained precision
  (tex 3329–3330).  `PROVED`.

The exactness of the two-generator resolution for the tame quotient, local Tate duality and the
local Kummer theory behind the self-cup statement (tex 3310–3316) are `GLUE`.
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

/-! ## The tame resolution -/

section Tame

variable {M : Type*} [AddCommGroup M]

/-- `d⁰ u = ((Φ - 1) u, 0)` (tex 3303). -/
def tameD0 (Φ : M →+ M) (u : M) : M × M := (Φ u - u, 0)

/-- `d¹ (x, y) = (Φ - q) y` (tex 3304). -/
def tameD1 (Φ : M →+ M) (q : ℤ) (xy : M × M) : M := Φ xy.2 - q • xy.2

/-- tex 3302–3305, `PROVED`: the tame resolution is a complex. -/
theorem tame_d1_d0 (Φ : M →+ M) (q : ℤ) (u : M) : tameD1 Φ q (tameD0 Φ u) = 0 := by
  simp [tameD1, tameD0]

/-- tex 3307–3309, `PROVED`: if `Φ_v = ρ(φ_v)` acts trivially on `M` and `q ≡ 1` on `M` (both
from (H12) at the retained exponent `m ≤ a`, where `q = ℓ² ≡ 1 (mod 2^{a+2})`), both
differentials vanish: the zero-differential model `D⁰ ⊕ (F_v ⊕ S_v)[-1] ⊕ D²[-2]`. -/
theorem tame_zero_differential (Φ : M →+ M) (q : ℤ) (hΦ : ∀ u, Φ u = u) (hq : ∀ u : M, q • u = u) :
    (∀ u, tameD0 Φ u = 0) ∧ (∀ xy, tameD1 Φ q xy = 0) := by
  refine ⟨fun u => ?_, fun xy => ?_⟩
  · simp [tameD0, hΦ]
  · simp [tameD1, hΦ, hq]

/-- tex 3309, `PROVED`: on a module killed by `2^m`, an integer `q` with `2^m ∣ q - 1` acts as
the identity (this is how `q ≡ 1 (mod 2^{a+2})` is used, `m ≤ a`). -/
theorem q_acts_trivially (m : ℕ) (q : ℤ) (hq : (2 : ℤ) ^ m ∣ q - 1)
    (hM : ∀ u : M, ((2 : ℤ) ^ m) • u = 0) (u : M) : q • u = u := by
  obtain ⟨k, hk⟩ := hq
  have : q = 1 + 2 ^ m * k := by linarith
  rw [this, add_smul, one_smul, mul_comm, mul_smul, hM, smul_zero, add_zero]

end Tame

/-! ## Local restriction and corestriction in the zero-differential model -/

section ResCor

variable {M : Type*} [AddCommGroup M]

/-- The zero-differential local model, components in the order `D⁰, F_v, S_v, D²`. -/
abbrev Loc4 (M : Type*) := M × M × M × M

/-- A diagonal map `diag(c₀, c₁, c₂, c₃)` on `Loc4 M`. -/
def diag4 (c0 c1 c2 c3 : ℤ) (x : Loc4 M) : Loc4 M :=
  (c0 • x.1, c1 • x.2.1, c2 • x.2.2.1, c3 • x.2.2.2)

/-- `res = diag(1, f, e, ef)` (tex 3326). -/
def resLoc (e f : ℤ) : Loc4 M → Loc4 M := diag4 1 f e (e * f)

/-- `cor = diag(ef, e, f, 1)` (tex 3327). -/
def corLoc (e f : ℤ) : Loc4 M → Loc4 M := diag4 (e * f) e f 1

/-- The strict condition `U_str = D⁰`. -/
def Ustr : Set (Loc4 M) := {x | x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.2.2.2 = 0}
/-- The relaxed condition `U_rel = D⁰ ⊕ (F ⊕ S)[-1]`. -/
def Urel : Set (Loc4 M) := {x | x.2.2.2 = 0}
/-- The finite condition `U_F = D⁰ ⊕ F[-1]`. -/
def UF : Set (Loc4 M) := {x | x.2.2.1 = 0 ∧ x.2.2.2 = 0}
/-- The singular condition `U_S = D⁰ ⊕ S[-1]`. -/
def US : Set (Loc4 M) := {x | x.2.1 = 0 ∧ x.2.2.2 = 0}

/-- tex 3330–3331, `PROVED`: every diagonal map preserves each of the four conditions retaining
`D⁰`. -/
theorem diag4_preserves (c0 c1 c2 c3 : ℤ) (x : Loc4 M) :
    (x ∈ Ustr → diag4 c0 c1 c2 c3 x ∈ Ustr) ∧ (x ∈ Urel → diag4 c0 c1 c2 c3 x ∈ Urel) ∧
      (x ∈ UF → diag4 c0 c1 c2 c3 x ∈ UF) ∧ (x ∈ US → diag4 c0 c1 c2 c3 x ∈ US) := by
  simp only [Ustr, Urel, UF, US, diag4, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all

/-- The local cup pairing in the zero-differential model: `D⁰` pairs with `D²`, `F` with `S` and
`S` with `F`, through arbitrary biadditive forms (the transported mixed pairing and the
`D⁰, D²` pairing of tex 3315–3316). -/
def cupLoc {A : Type*} [AddCommGroup A] (β0 β1 β2 β3 : M →+ M →+ A) (x y : Loc4 M) : A :=
  β0 x.1 y.2.2.2 + β1 x.2.1 y.2.2.1 + β2 x.2.2.1 y.2.1 + β3 x.2.2.2 y.1

/-- tex 3331–3332, `PROVED`: the local cup-product adjunction `⟨res x, y⟩ = ⟨x, cor y⟩`, entry
by entry (with `x` on the lower and `y` on the upper field). -/
theorem cup_adjunction {A : Type*} [AddCommGroup A] (β0 β1 β2 β3 : M →+ M →+ A) (e f : ℤ)
    (x y : Loc4 M) :
    cupLoc β0 β1 β2 β3 (resLoc e f x) y = cupLoc β0 β1 β2 β3 x (corLoc e f y) := by
  simp only [cupLoc, resLoc, corLoc, diag4, map_zsmul, AddMonoidHom.zsmul_apply, one_smul]

/-- tex 3326–3327, `PROVED`: `cor ∘ res = ef`, the local degree. -/
theorem cor_res (e f : ℤ) (x : Loc4 M) : corLoc e f (resLoc e f x) = (e * f) • x := by
  simp only [corLoc, resLoc, diag4, smul_smul, one_smul]
  ext <;> simp [mul_comm]

/-- tex 3329–3330, `PROVED`: a transfer shear with coefficient divisible by `(q - 1)/2`, where
`2^{a+1} ∣ (q - 1)/2` (`half_q_cong`), vanishes on a module killed by `2^m`, `m ≤ a + 1`. -/
theorem shear_vanishes (a m : ℕ) (hm : m ≤ a + 1) (s k k' : ℤ) (hs : s = k * (2 ^ (a + 1) * k'))
    (hM : ∀ u : M, ((2 : ℤ) ^ m) • u = 0) (u : M) : s • u = 0 := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hm
  rw [hs, hj, pow_add, show k * (2 ^ m * 2 ^ j * k') = (k * 2 ^ j * k') * 2 ^ m by ring, mul_smul,
    hM, smul_zero]

/-- tex 3359–3362 ("the restricted zero pairing"), `PROVED`: on the zero-differential model the
local cup pairing vanishes on `U_F × U_F` and on `U_S × U_S` (the finite and singular planes are
self-orthogonal), and on `U_str × U_rel` (the strict condition `D⁰` is orthogonal to the relaxed
one); these are the restricted pairings for which the isotropy null-homotopies are taken. -/
theorem cup_isotropic {A : Type*} [AddCommGroup A] (β0 β1 β2 β3 : M →+ M →+ A) (x y : Loc4 M) :
    (x ∈ UF → y ∈ UF → cupLoc β0 β1 β2 β3 x y = 0) ∧
      (x ∈ US → y ∈ US → cupLoc β0 β1 β2 β3 x y = 0) ∧
      (x ∈ Ustr → y ∈ Urel → cupLoc β0 β1 β2 β3 x y = 0) := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [UF, US, Ustr, Urel, Set.mem_ofPred_eq, cupLoc]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩ ⟨rfl, rfl⟩; simp
  · rintro ⟨rfl, rfl⟩ ⟨rfl, rfl⟩; simp
  · rintro ⟨rfl, rfl, rfl⟩ rfl; simp

end ResCor

/-- tex 3359–3362, `PROVED` (the degree count): a map of negative degree `k < 0` from a complex
concentrated in degrees `0, 1, 2` (here `U_v ⊗ U'_v`) to a complex concentrated in degree `2`
(the trace target `A[-2]`) has no nonzero component, since `n + k = 2` forces `n > 2`. -/
theorem negative_degree_count (k n : ℤ) (hk : k < 0) (hn : 0 ≤ n ∧ n ≤ 2) : n + k ≠ 2 := by
  omega

end ZInQ.Manuscript.RC.HeegnerAlgebra

import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Annihilator
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Descent
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Precision
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Frobenius

/-!
# Lane RC10 (Heegner algebra), part 9: the cohomological inputs as interfaces, and assembly

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner`, tex 2834–3410.

Heegner points on `X₀(N)`, ring-class fields, continuous Galois cohomology of number fields and
their completions with coefficients `E[2^a]`, `(T₂E ⊗ A_i)(χ_h Ψ_i)` and `A_i[G]`, Kolyvagin
derivative classes and Selmer complexes are not available as genuine definitions here.  Following
the lane conventions, each input of Elliot's descent is recorded as the most faithful abstract
interface: a structure whose fields are exactly the properties the proof uses, over abstract
abelian groups standing for the named cohomology groups and points.  Each structure's docstring
names the input, its kind (`PRINT`, `GLUE`, `ELLIOT`) and the tex lines.  The `PROVED` algebra of
the other files consumes these fields; the assembly theorems at the end make the dependencies
explicit:

* `H7_assembled`: (H12) for every retained prime (gap B1-a) ⇒ the derivative class
  `c_{I,a} = δ_a(C_π D_I y_{f n_I})` is `Gal(M_I/H_f)`-invariant;
* `H11_assembled`: (H8)–(H9) and (H11): `b_{I,a}` restricts to `δ_a(L D_I y_{f n_I})`;
* `H19_assembled`: the singular coordinate relation `s_new = J f_old` at precision `2^m`.

Locators of printed sources are given as the manuscript gives them; those for Nekovář were checked
against the Astérisque 310 text (see the lane report); the others are `UNVERIFIED` here (lane RC9
states Cai–Chen–Liu, Elkik, Serre, Lang and Silverman as printed leaves).
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

/-! ## Interfaces -/

/-- `GLUE` (Kummer theory), used at tex 2995–3002, 3058–3062, 3080–3084, 3111–3113: the Kummer
map `δ_a : E(F) → H¹(F, E[2^a])` of the multiplication-by-`2^a` sequence, Galois-equivariant when
`F` varies in a Galois tower, with kernel `2^a E(F)`, followed by `H¹(F, E[2^a]) → H¹(F, E)`, exact
in the middle.  `P`, `HV`, `HE` stand for `E(F)`, `H¹(F, E[2^a])`, `H¹(F, E)`; `Γ` for the Galois
group acting. -/
structure KummerSequence (Γ P HV HE : Type*) [Group Γ] [AddCommGroup P] [AddCommGroup HV]
    [AddCommGroup HE] [DistribMulAction Γ P] [DistribMulAction Γ HV] (a : ℕ) where
  /-- the Kummer map `δ_a` -/
  δ : P →+ HV
  /-- `H¹(F, E[2^a]) → H¹(F, E)` -/
  j : HV →+ HE
  equivariant : ∀ γ : Γ, ∀ x, δ (γ • x) = γ • δ x
  ker_δ : ∀ x, δ x = 0 ↔ ∃ y, x = ((2 : ℤ) ^ a) • y
  exact : ∀ v, j v = 0 ↔ ∃ x, δ x = v

/-- `δ_a` kills `2^a`-multiples. -/
theorem KummerSequence.δ_two_pow {Γ P HV HE : Type*} [Group Γ] [AddCommGroup P] [AddCommGroup HV]
    [AddCommGroup HE] [DistribMulAction Γ P] [DistribMulAction Γ HV] {a : ℕ}
    (K : KummerSequence Γ P HV HE a) (x : P) : K.δ (((2 : ℤ) ^ a) • x) = 0 :=
  (K.ker_δ _).mpr ⟨x, rfl⟩

/-- `PRINT` (Nekovář, *Selmer complexes*, Astérisque 310, formula (4.1.4.1), p. 96; see the lane
report for the check of this locator), with `GLUE` (H2) input, tex 3004–3017: for the finite
Galois extension `M = M_I` of `B = H_f` with group `Γ` and `V_a = E[2^a]`, the five-term sequence
`0 → H¹(Γ, V_a^{G_M}) → H¹(B, V_a) → H¹(M, V_a)^Γ → H²(Γ, V_a^{G_M})`, and the vanishing of
multiplication by `2^e` on the outer groups, which follows from (H2) because `V_a^{G_M} =
E(M)[2^a]` is killed by `2^e` ("hence on every cochain and cohomology group of `Γ`"). -/
structure InfResInput (A B C D : Type*) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] (e : ℕ) where
  /-- the five-term sequence (H8) -/
  seq : FiveTerm A B C D
  killA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0
  killD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0

/-- `PRINT`/`GLUE` (H10), tex 3034–3062 (Lang 1956, Theorem 1 and its corollary; Silverman,
*The Arithmetic of Elliptic Curves*, IV.3.2(a), p. 124; both `UNVERIFIED` here, stated by lane
RC9): for an unramified extension `F'/F` of local fields at an old place, the Kummer sequences
over `F` and `F'`, restriction, inflation from `H¹(Gal(F'/F), B(F'))` onto the kernel of
restriction, and `c_B H¹(Gal(F'/F), B(F')) = 0`. -/
structure LocalDescentInput (Pt Pt' HV HV' HB HB' Hinf : Type*) [AddCommGroup Pt]
    [AddCommGroup Pt'] [AddCommGroup HV] [AddCommGroup HV'] [AddCommGroup HB] [AddCommGroup HB']
    [AddCommGroup Hinf] where
  κ : Pt →+ HV
  j : HV →+ HB
  exK : ∀ v, j v = 0 → ∃ x, κ x = v
  κ' : Pt' →+ HV'
  j' : HV' →+ HB'
  hκ' : ∀ x', j' (κ' x') = 0
  res : HV →+ HV'
  resB : HB →+ HB'
  hcomm : ∀ v, j' (res v) = resB (j v)
  infl : Hinf →+ HB
  exInf : ∀ w, resB w = 0 → ∃ z, infl z = w
  /-- the geometric component-group order `c_B` (or a common multiple `C_bad`) -/
  cB : ℤ
  hH10 : ∀ z : Hinf, cB • z = 0

/-- `LocalDescentInput` gives: a class that becomes Kummer over `F'` becomes Kummer over `F` after
multiplication by `m₀ c_B` (tex 3058–3062, 3080), `PROVED`. -/
theorem LocalDescentInput.kummer {Pt Pt' HV HV' HB HB' Hinf : Type*} [AddCommGroup Pt]
    [AddCommGroup Pt'] [AddCommGroup HV] [AddCommGroup HV'] [AddCommGroup HB] [AddCommGroup HB']
    [AddCommGroup Hinf] (D : LocalDescentInput Pt Pt' HV HV' HB HB' Hinf) (m0 : ℤ) (v : HV)
    (hv : ∃ x', D.res v = D.κ' x') : ∃ x, D.κ x = (m0 * D.cB) • v :=
  H11_kummer_at_old D.κ D.j D.exK D.κ' D.j' D.hκ' D.res D.resB D.hcomm D.infl D.exInf D.cB
    D.hH10 m0 v hv

/-- `PRINT` (Cai–Chen–Liu, Trans. AMS 370, Theorem 2.15, stated by lane RC9; `UNVERIFIED` here),
the inert norm relations (4.1), tex 2914–2936, together with the Artin identification (H5)
(`GLUE`, tex 2969–2985), in the form used by (H7): the points `y J = y_{f n_J}` (`J ⊆ I`) live in
the module `P = E(M_I)` over the commutative group ring `𝒜 = ℤ[Gal(M_I/H_f)]`; `σ i`, `D i`,
`Tr i ∈ 𝒜` are the generator, the derivative and the trace of the `i`-factor `C_{ℓ_i+1}` of (H5);
`γ i ∈ Γ = Gal(M_I/H_f)` is the same generator as a group element; the `γ i` (`i ∈ I`) generate
`Γ`; and `Tr_ℓ y_{f n_I} = a_ℓ y_{f n_I/ℓ}` for `ℓ ∈ I`.  -/
structure DerivativeInput (ι 𝒜 Γ P : Type*) [DecidableEq ι] [CommRing 𝒜] [AddCommGroup P]
    [Module 𝒜 P] [Group Γ] [DistribMulAction Γ P] (I : Finset ι) where
  σ : ι → 𝒜
  D : ι → 𝒜
  Tr : ι → 𝒜
  γ : ι → Γ
  /-- the rational prime `ℓ_i` -/
  ℓnum : ι → ℤ
  /-- the Hecke eigenvalue `a_{ℓ_i}` -/
  aℓ : ι → ℤ
  y : Finset ι → P
  /-- (H6) in `𝒜` (`PROVED` in `GroupRing.lean`: `H6_groupRing`) -/
  hH6 : ∀ i, (σ i - 1) * D i = ((ℓnum i + 1 : ℤ) : 𝒜) - Tr i
  /-- the group element `γ i` acts as `σ i ∈ 𝒜` -/
  hγσ : ∀ i (x : P), γ i • x = σ i • x
  /-- the `γ i`, `i ∈ I`, generate `Γ` (H5) -/
  generate : Subgroup.closure (γ '' (I : Set ι)) = ⊤
  /-- the inert norm relations (4.1) -/
  hnorm : ∀ i ∈ I, Tr i • y I = (aℓ i : 𝒜) • y (I.erase i)


/-- `PRINT` (Serre's open-image theorem for non-CM `E/ℚ` at `2`, stated by lane RC9) with `GLUE`
(class field theory of ring-class fields), tex 2881–2900: `G = G_ℚ` acts on `V = E[2^∞](ℚ̄)`;
some `g` acts as the scalar `u = 1 + 2^n`, `n ≥ 2` (since `1 + 2^n M₂(ℤ₂) ⊂ ρ_T(G_ℚ)`); `G_K` has
index two; `N = G_{H_d}` is normal, and complex conjugation `τ` inverts `G_K/N` (`Gal(H_d/ℚ)` is
generalized dihedral).  Consumed by `H2_assembled`. -/
structure OpenImageInput (G V : Type*) [Group G] [AddCommGroup V] [DistribMulAction G V] where
  n : ℕ
  two_le : 2 ≤ n
  g : G
  scalar : ∀ v : V, g • v = ((1 : ℤ) + 2 ^ n) • v
  τ : G
  GK : Subgroup G
  index_two : GK.index = 2

/-- (H2) assembled, tex 2881–2900, `PROVED` from `OpenImageInput`: for every ring-class field
`H_d` (any normal `N ≤ G_K` inverted by `τ`), every point of `E(H_d)[2^∞]` is killed by `2^e`,
`e = n + 2`; the same `e` works for every `d`, every allowed `K` and every compositum. -/
theorem H2_assembled {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]
    (O : OpenImageInput G V) (N : Subgroup G) [N.Normal]
    (hτ : ∀ x ∈ O.GK, O.τ * x * O.τ⁻¹ * x ∈ N) (P : V) (hP : ∀ x ∈ N, x • P = P)
    (htors : ∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) : ((2 : ℤ) ^ (O.n + 2)) • P = 0 :=
  H2_ringClass N O.GK O.index_two O.τ hτ O.n O.two_le O.g O.scalar P hP htors

/-- The inputs of the one-derivative-prime computation (H13)–(H19), tex 3097–3190.  `G =
G_{H_{f n_I}}` acts on `V = E(ℚ̄)`; `Hup = G_{H_{f n_I ℓ}}`; `σ` a local inertia lift of the
generator `σ_ℓ`; `red` the reduction at a place above `ℓ` with Frobenius `F`; `J = ρ_T(τ)`.
Kinds: `cocycle`, `tors`, `kummer_upper` are the choice of the adjusted representative of
`b_{I∪ℓ,a}` (`ELLIOT`, tex 3122–3128); `hZ`, `hQ` define the division points; `hY`, `hTr` are
(4.1) with `d = f n_I` (`PRINT`, CCL 2.15); `hXfix`, `hYfix` say `X, Y` are points of the
indicated fields; `hH2` is (H2) for the upper field (`H2_assembled`); `hu'`, `hv'` come from
(H12) (`H12_divisibility`); `hinert` (inertia acts trivially on reductions), `hYX` ((H4), the CM
congruence, `ELLIOT` tex 2948–2967), `hXF` (`(ℓ)` splits completely in `H_{f n_I}`),
`hchar` (`F² - a_ℓ F + ℓ = 0`) and `hJ` ((H12) through the equivariant identification of
`E[2^a]` with the reduced torsion) are `GLUE`. -/
structure DerivativePrimeInput (G V Vb : Type*) [Group G] [AddCommGroup V] [DistribMulAction G V]
    [AddCommGroup Vb] where
  Hup : Subgroup G
  normal : Hup.Normal
  σ : G
  ℓ : ℕ
  a : ℕ
  e : ℕ
  L : ℤ
  aℓ : ℤ
  u' : ℤ
  v' : ℤ
  X : V
  Y : V
  Z : V
  Q : V
  b : G → V
  cocycle : ∀ g k, b (g * k) = b g + g • b k
  tors : ((2 : ℤ) ^ a) • b σ = 0
  kummer_upper : ∀ h ∈ Hup, b h = h • Z - Z
  hZ : ((2 : ℤ) ^ a) • Z = L • Dact σ ℓ Y
  hQ : ((2 : ℤ) ^ a) • Q = L • X
  hY : σ ^ (ℓ + 1) • Y = Y
  hTr : Tract σ ℓ Y = aℓ • X
  hXfix : ∀ h ∈ Hup, h • X = X
  hYfix : ∀ h ∈ Hup, h • Y = Y
  hH2 : ∀ P : V, (∀ h ∈ Hup, h • P = P) → (∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) →
    ((2 : ℤ) ^ e) • P = 0
  hu' : (ℓ : ℤ) + 1 = 2 ^ a * u'
  hv' : aℓ = 2 ^ a * v'
  red : V →+ Vb
  F : Vb →+ Vb
  J : Vb →+ Vb
  hinert : red (σ • Z) = red Z
  hYX : red Y = F (red X)
  hXF : F (F (red X)) = red X
  hchar : ∀ w : Vb, F (F w) - aℓ • F w + (ℓ : ℤ) • w = 0
  hJ : ∀ w : Vb, ((2 : ℤ) ^ a) • w = 0 → F w - aℓ • w = J w

/-- (H16)–(H19) assembled, tex 3150–3190, `PROVED` from `DerivativePrimeInput`: at precision
`2^m` with `a - m ≥ e`, the singular coordinate of `b_{I∪ℓ,a}` at the derivative place is `J`
applied to the finite coordinate `f_old = (F² - 1) Q̄` of `b_{I,a}`. -/
theorem H19_assembled {G V Vb : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]
    [AddCommGroup Vb] (Dp : DerivativePrimeInput G V Vb) (m : ℕ) (hm : Dp.e ≤ Dp.a - m) :
    ((2 : ℤ) ^ (Dp.a - m)) • Dp.red (Dp.b Dp.σ) =
      Dp.J (((2 : ℤ) ^ (Dp.a - m)) • (Dp.F (Dp.F (Dp.red Dp.Q)) - Dp.red Dp.Q)) :=
  haveI := Dp.normal
  H19_singular Dp.Hup Dp.σ Dp.ℓ Dp.a m Dp.e Dp.L Dp.aℓ Dp.u' Dp.v' Dp.X Dp.Y Dp.Z Dp.Q Dp.b
    Dp.cocycle Dp.tors Dp.kummer_upper Dp.hZ Dp.hQ Dp.hY Dp.hTr Dp.hXfix Dp.hYfix Dp.hH2 Dp.hu'
    Dp.hv' Dp.red Dp.F Dp.J Dp.hinert Dp.hYX Dp.hXF Dp.hchar Dp.hJ hm

/-- `PRINT`/`GLUE` (formal groups: Silverman, IV.2.3 and IV.3.2, pp. 122–124, `UNVERIFIED` here),
tex 3173–3186, the input of (H19) `f_new = 0`: in the totally ramified upper local field the point
`L D_ℓ Y` has a `2^a`-division point `P` (Hensel lift from `𝔽_{ℓ²}`, `[2^a]` invertible on the
formal group since `ℓ` is odd), so the restricted class is the coboundary of `P`; and the chosen
Frobenius lift `φ` fixes `E[2^a]` by (H12). -/
structure UpperDivisionInput (G V : Type*) [Group G] [AddCommGroup V] [DistribMulAction G V] where
  b : G → V
  P : V
  coboundary : ∀ g, b g = g • P - P
  φ : G
  frob_fixes : φ • P = P

/-- (H19), finite coordinate, `PROVED` from `UpperDivisionInput`: `f_new = 0`. -/
theorem H19_finite_assembled {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]
    (U : UpperDivisionInput G V) : U.b U.φ = 0 :=
  H19_finite U.b U.P U.coboundary U.φ U.frob_fixes

/-! ## Assembly -/

/-- (H7) assembled with gap B1-a, tex 2992–3002 and 3089–3096, `PROVED` from the interfaces: if
every `ℓ ∈ I` satisfies (H12) at exponent `a` (`ρ_T(Fr_ℓ) ≡ J (mod 2^{a+1})`, giving
`2^{a+1} ∣ a_ℓ` and `2^{a+1} ∣ ℓ + 1` by `H12_divisibility`), then
`c_{I,a} = δ_a(C_π D_I y_{f n_I})` is `Gal(M_I/H_f)`-invariant.  The hypothesis is imposed on
*every* prime of `I`, as gap B1-a requires; the manuscript's statement (tex 2846, 2865) asserts
`P_{I,m}` for any finite inert `I`, and every use chooses `I` by Chebotarev with (H12). -/
theorem H7_assembled {ι 𝒜 Γ P HV HE : Type*} [DecidableEq ι] [CommRing 𝒜] [AddCommGroup P]
    [Module 𝒜 P] [Group Γ] [DistribMulAction Γ P] [AddCommGroup HV] [AddCommGroup HE]
    [DistribMulAction Γ HV] (I : Finset ι) (a : ℕ) (K : KummerSequence Γ P HV HE a)
    (Din : DerivativeInput ι 𝒜 Γ P I) (Cπ : ℤ)
    (hH12 : ∀ i ∈ I, (2 : ℤ) ^ (a + 1) ∣ Din.aℓ i ∧ (2 : ℤ) ^ (a + 1) ∣ Din.ℓnum i + 1) :
    ∀ g : Γ, g • K.δ (((Cπ : 𝒜) * ∏ j ∈ I, Din.D j) • Din.y I) =
      K.δ (((Cπ : 𝒜) * ∏ j ∈ I, Din.D j) • Din.y I) := by
  apply H7_invariant K.δ K.equivariant a K.δ_two_pow (Din.γ '' (I : Set ι)) Din.generate
  rintro _ ⟨i, hi, rfl⟩
  have hB1a := B1a_of_H12 a (Din.aℓ i) (Din.ℓnum i) (hH12 i hi)
  rw [Din.hγσ]
  exact H7_difference_divisible Din.σ Din.D Din.Tr Din.ℓnum Din.aℓ Din.hH6 Din.y I i hi
    (Din.hnorm i hi) Cπ a hB1a.2 hB1a.1

/-- (H8)–(H11) assembled, tex 3004–3086, `PROVED` from the interfaces: with
`c_{I,a} = δ_a(C_π D_I y_{f n_I})` and `b_{I,a} = m₀ C_bad d_a(c_{I,a})`, the restriction of
`b_{I,a}` to `M_I` is `δ_a(L D_I y_{f n_I})`, `L = m₀ C_π C_bad 2^{2e}`; for `I = ∅`
(restriction the identity) the class is the Kummer class of `L` times the point. -/
theorem H11_assembled {A B C D P : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup P] (e : ℕ) (Inp : InfResInput A B C D e) (δa : P →+ C)
    (m0 Cπ Cbad : ℕ) (x : P) :
    Inp.seq.res (((m0 * Cbad : ℕ) : ℤ) • Inp.seq.descend e Inp.killD (δa ((Cπ : ℤ) • x))) =
      δa (Lmult m0 Cπ Cbad e • x) :=
  H11_restriction Inp.seq e Inp.killD δa m0 Cπ Cbad x

/-- (H8)–(H9) for `I = ∅`, tex 3030–3032 and 3293–3295, `PROVED`: when the relative group is
trivial the descended class is `2^{2e}` times the class, so `b_{∅,a}` is the Kummer class of the
`L`-multiplied point. -/
theorem H11_empty {A B D P : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [AddCommGroup P] (e : ℕ) (Inp : InfResInput A B B D e) (hres : ∀ b, Inp.seq.res b = b)
    (δa : P →+ B) (m0 Cπ Cbad : ℕ) (x : P) :
    ((m0 * Cbad : ℕ) : ℤ) • Inp.seq.descend e Inp.killD (δa ((Cπ : ℤ) • x)) =
      δa (Lmult m0 Cπ Cbad e • x) := by
  have h := H11_restriction Inp.seq e Inp.killD δa m0 Cπ Cbad x
  rwa [hres] at h

end ZInQ.Manuscript.RC.HeegnerAlgebra

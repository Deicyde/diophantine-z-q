import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationRC19
import ZInQKernel.Contrib.OneProof.RC.Height.IndexTwo
import ZInQKernel.Contrib.PoleRC.MordellWeilM

/-!
**Theorem 5.3, Lane RC0 round 3: the free generators of (4.6) from the forward theorems**

`CalibrationModelR` (`Wiring/CalibrationRC19.lean`) still takes free generators `g_𝒜` of
`𝒜(ℚ) = E^{(h_x)}(K)` and `g_ℬ` of `ℬ(ℚ) = E^{(h_x)}(ℚ) × E^{(h_x k)}(ℚ)` as fields. The text
obtains them from the forward theorems: "At known simple zeros, Lemma `lem:forward-rank` gives rank
one and finite `Ш`" (tex 4020–4021; Lemma `lem:forward-rank`, tex 1086–1110: BCDT Theorem A and
Kolyvagin Theorem 1). This file proves their existence from

* `Prints.bcdt`, `Prints.kolyvagin` (the blueprint's BCDT print and its Kolyvagin statement,
  GLUE): `rank E^{(h_x)}(ℚ) = 1` from `ord_{s=1} L(E^{(h_x)},s) = 1`, and `rank E^{(h_x k)}(ℚ) = 0`
  from `L(E^{(h_x k)},1) ≠ 0`;
* Mordell's theorem for the curves `E_m` (`PoleRC.mordellWeil_curve`, PROVED in the tree);
* the structure theorem of finitely generated abelian groups (Mathlib): rank one and finite
  generation give a free generator `q` of `E^{(h_x)}(ℚ)`, and rank zero makes `E^{(h_x k)}(ℚ)`
  torsion, so `g_ℬ = (q, 0)`;
* lane RC19's descent for `K = ℚ(√k)` (`conj_sub_isOfFinAddOrder_of_twist_torsion`, `descend`):
  every `P ∈ E^{(h_x)}(K)` has `2P ≡ n q_K` modulo torsion, so `E^{(h_x)}(K)` modulo torsion is
  `ℤ q_K` or `ℤ P₁` with `2P₁ ≡ q_K` (the "index at most two" of tex 2433–2435, here at the
  calibration); this gives `g_𝒜`.

The Milne field is then stated for **every** pair of free generators (the regulator of a rank-one
lattice is the height of any of its free generators), and the generator fields disappear:

* `CalibrationModelP` (no `gA`, `gB`, `freeA`, `freeB`);
* `CalibrationModelP.nonempty_modelR : Prints → 0 < ℓ → h_x ≠ 0 → ord L(E^{(h_x)}) = 1 →
  L(E^{(h_x k)},1) ≠ 0 → CalibrationModelP … → Nonempty (CalibrationModelR …)` (PROVED);
* `calibrationInputs_of_P : Prints → 0 < ℓ → CalibrationInputsP D → CalibrationInputs D` (PROVED).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

attribute [local instance] Nat.fact_prime_two

/-! Free generators of rank-one groups -/

/-- If `n • x` is torsion for some `n ≠ 0`, then `x` is torsion (PROVED). -/
theorem isOfFinAddOrder_of_zsmul {G : Type*} [AddCommGroup G] {x : G} {n : ℤ} (hn : n ≠ 0)
    (h : IsOfFinAddOrder (n • x)) : IsOfFinAddOrder x := by
  obtain ⟨m, hm, hmx⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp h
  exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨m * n, mul_ne_zero hm hn, by rw [mul_smul, hmx]⟩

/-- **Rank zero means torsion**: if `rank_ℤ G = 0`, every element of `G` has finite order
(PROVED). -/
theorem isOfFinAddOrder_of_rank_eq_zero {G : Type*} [AddCommGroup G]
    (h : Module.rank ℤ G = 0) (x : G) : IsOfFinAddOrder x := by
  obtain ⟨a, ha, hax⟩ := rank_eq_zero_iff.mp h x
  exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, ha, hax⟩

/-- **A finitely generated abelian group of rank one has a free generator** (PROVED, from the
structure theorem `AddCommGroup.equiv_free_prod_directSum_zmod`). -/
theorem exists_isFreeGenerator_of_rank_eq_one {G : Type} [AddCommGroup G] [AddGroup.FG G]
    (h : Module.rank ℤ G = 1) : ∃ g : G, IsFreeGenerator g := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  set T := DirectSum ι fun i => ZMod (p i ^ e i) with hTdef
  -- the torsion summand has rank zero
  have hker : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin n →₀ ℤ) T)) = 0 := by
    refine (rank_eq_zero_iff (R := ℤ)
      (M := ↥(LinearMap.ker (LinearMap.fst ℤ (Fin n →₀ ℤ) T)))).mpr fun y =>
        ⟨(addOrderOf y.1.2 : ℤ), ?_, ?_⟩
    · exact_mod_cast (isOfFinAddOrder_of_finite y.1.2).addOrderOf_pos.ne'
    · have hy : y.1.1 = 0 := y.2
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · simp [hy]
      · change ((addOrderOf y.1.2 : ℤ) • y.1).2 = 0
        rw [Prod.smul_snd, natCast_zsmul, addOrderOf_nsmul_eq_zero]
  have hrank : Module.rank ℤ G = n := by
    rw [f.toIntLinearEquiv.rank_eq,
      LinearMap.rank_eq_of_surjective (f := LinearMap.fst ℤ (Fin n →₀ ℤ) T)
        (fun a => ⟨(a, 0), rfl⟩), hker, add_zero, rank_finsupp_self', Cardinal.mk_fin]
  have hn : n = 1 := by
    rw [h] at hrank
    exact_mod_cast hrank.symm
  subst hn
  set g : G := f.symm (Finsupp.single 0 1, 0) with hgdef
  refine ⟨g, fun hg => ?_, fun P => ⟨(f P).1 0, ?_⟩⟩
  · obtain ⟨m, hm, hmg⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hg
    have h1 : f (m • g) = 0 := by rw [hmg, map_zero]
    rw [map_nsmul, hgdef, AddEquiv.apply_symm_apply] at h1
    have h2 : (m • ((Finsupp.single 0 1, 0) : (Fin 1 →₀ ℤ) × T)).1 0 = 0 := by
      rw [h1, Prod.fst_zero, Finsupp.coe_zero, Pi.zero_apply]
    rw [Prod.smul_fst, Finsupp.smul_apply, Finsupp.single_eq_same, nsmul_eq_mul, mul_one] at h2
    exact hm.ne' (by exact_mod_cast h2)
  · have key : P - ((f P).1 0) • g = f.symm (0, (f P).2) := by
      apply f.injective
      rw [map_sub, map_zsmul, hgdef, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      refine Prod.ext (Finsupp.ext fun i => ?_) ?_
      · fin_cases i
        simp
      · simp
    rw [key]
    have ht : IsOfFinAddOrder ((0, (f P).2) : (Fin 1 →₀ ℤ) × T) :=
      (AddMonoidHom.inr (Fin 1 →₀ ℤ) T).isOfFinAddOrder (isOfFinAddOrder_of_finite (f P).2)
    exact f.symm.toAddMonoidHom.isOfFinAddOrder ht

/-- The rank of the point group is invariant under an equality of curves (PROVED). -/
theorem rank_points_congr {W W' : WeierstrassCurve ℚ} (h : W = W') :
    Module.rank ℤ W.toAffine.Point = Module.rank ℤ W'.toAffine.Point := by
  subst h
  rfl

/-- **A free generator of a product with a torsion factor**: if `q` is a free generator of `G` and
`H` is torsion, `(q, 0)` is a free generator of `G × H` (PROVED). -/
theorem isFreeGenerator_prod_zero {G H : Type*} [AddCommGroup G] [AddCommGroup H] {q : G}
    (hq : IsFreeGenerator q) (htors : ∀ y : H, IsOfFinAddOrder y) :
    IsFreeGenerator ((q, 0) : G × H) := by
  refine ⟨fun h => hq.1 ((AddMonoidHom.fst G H).isOfFinAddOrder h), fun P => ?_⟩
  obtain ⟨n, hn⟩ := hq.2 P.1
  refine ⟨n, ?_⟩
  have e : P - n • ((q, 0) : G × H) =
      AddMonoidHom.inl G H (P.1 - n • q) + AddMonoidHom.inr G H P.2 := by
    ext <;> simp
  rw [e]
  exact ((AddMonoidHom.inl G H).isOfFinAddOrder hn).add
    ((AddMonoidHom.inr G H).isOfFinAddOrder (htors _))

/-- **A free generator of `E^{(h)}(K)`** for `K = ℚ(√k)` (the index-two descent, as in lane
RC19's `IndexTwo.lean`): if `q` generates `E^{(h)}(ℚ)` modulo torsion and `E^{(hk)}(ℚ)` is torsion,
then every `P ∈ E^{(h)}(K)` has `2P ≡ n q_K` modulo torsion (`P − σP` is torsion and `P + σP` is
rational), so `E^{(h)}(K)` has a free generator: `q_K` if no `P₁` has `2P₁ ≡ q_K`, and such a `P₁`
otherwise (PROVED). -/
theorem exists_isFreeGenerator_baseChange {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    [Algebra.IsQuadraticExtension ℚ K] {k : ℚ} (Dq : QuadData K k) (E : WeierstrassCurve ℚ)
    (h : ℚ) (q : ((qtwist E h).baseChange ℚ).toAffine.Point) (hq : IsFreeGenerator q)
    (htors : ∀ R : ((qtwist E (h * k)).baseChange ℚ).toAffine.Point, IsOfFinAddOrder R) :
    ∃ g : ((qtwist E h).baseChange K).toAffine.Point, IsFreeGenerator g := by
  classical
  set qK := Point.baseChange ℚ K q with hqKdef
  have hnorm : ∀ P : ((qtwist E h).baseChange K).toAffine.Point,
      ∃ n : ℤ, IsOfFinAddOrder ((2 : ℤ) • P - n • qK) := by
    intro P
    have hfix := ZInQ.Manuscript.RC.Height.conj_add_conj E h k Dq P
    obtain ⟨n, hn⟩ := hq.2 (ZInQ.Manuscript.RC.Height.descend Dq _ hfix)
    refine ⟨n, ?_⟩
    have h1 := (Point.baseChange ℚ K).isOfFinAddOrder hn
    rw [map_sub, map_zsmul, ZInQ.Manuscript.RC.Height.baseChange_descend] at h1
    have h2 := ZInQ.Manuscript.RC.Height.conj_sub_isOfFinAddOrder_of_twist_torsion Dq E h htors P
    have e : (2 : ℤ) • P - n • qK =
        (P + ZInQ.Manuscript.RC.Height.conj Dq P - n • qK) -
          (ZInQ.Manuscript.RC.Height.conj Dq P - P) := by
      rw [two_zsmul]; abel
    rw [e]
    exact ZInQ.Manuscript.RC.Height.isOfFinAddOrder_sub' h1 h2
  have hqK : ¬IsOfFinAddOrder qK := fun ht =>
    hq.1 (ZInQ.Manuscript.RC.Height.isOfFinAddOrder_of_map_isOfFinAddOrder _
      (ZInQ.Manuscript.RC.Height.baseChange_injective _) ht)
  by_cases hhalf : ∃ P₁, IsOfFinAddOrder ((2 : ℤ) • P₁ - qK)
  · obtain ⟨P₁, hP₁⟩ := hhalf
    refine ⟨P₁, fun ht => hqK ?_, fun P => ?_⟩
    · have e : qK = (2 : ℤ) • P₁ - ((2 : ℤ) • P₁ - qK) := by abel
      rw [e]
      exact ZInQ.Manuscript.RC.Height.isOfFinAddOrder_sub' ht.zsmul hP₁
    · obtain ⟨n, hn⟩ := hnorm P
      refine ⟨n, isOfFinAddOrder_of_zsmul (n := 2) (by norm_num) ?_⟩
      have e : (2 : ℤ) • (P - n • P₁) = ((2 : ℤ) • P - n • qK) - n • ((2 : ℤ) • P₁ - qK) := by
        rw [smul_sub, smul_sub, smul_smul, smul_smul, mul_comm]
        abel
      rw [e]
      exact ZInQ.Manuscript.RC.Height.isOfFinAddOrder_sub' hn hP₁.zsmul
  · refine ⟨qK, hqK, fun P => ?_⟩
    obtain ⟨n, hn⟩ := hnorm P
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
    · refine ⟨m, isOfFinAddOrder_of_zsmul (n := 2) (by norm_num) ?_⟩
      have e : (2 : ℤ) • (P - m • qK) = (2 : ℤ) • P - (2 * m) • qK := by
        rw [smul_sub, smul_smul]
      rw [e]
      exact hn
    · exfalso
      refine hhalf ⟨P - m • qK, ?_⟩
      have e : (2 : ℤ) • (P - m • qK) - qK = (2 : ℤ) • P - (2 * m + 1) • qK := by
        rw [smul_sub, smul_smul, add_smul, one_smul]
        abel
      rw [e]
      exact hn

/-! The calibration model without generator fields -/

/-- **The remaining inputs of (4.6) at one address, with the free generators derived**
(Proposition `ex:arith-central-calibration`, tex 3987–4141). The fields are those of
`CalibrationModelR` (same names, tex lines, kinds and owners), without `gA`, `gB`, `freeA`,
`freeB`, and with the Milne field stated for every pair of free generators:

| field | content | tex | kind | owner |
|---|---|---|---|---|
| `hmilne` | Cassels' isogeny invariance in Milne's form, with the canonical regulators `Reg_𝒜 = ĥ_𝒜(g_𝒜)`, `Reg_ℬ = ĥ_ℬ(g_ℬ)` for any free generators `g_𝒜` of `𝒜(ℚ) = E^{(h_x)}(K)` and `g_ℬ` of `ℬ(ℚ) = E^{(h_x)}(ℚ) × E^{(h_x k)}(ℚ)`, and self-dual torsion counts; as a leaf field it constrains only free parameters (`shaA`, `tA`, `tB`, `C_𝒜`, `C_ℬ`, `Ω_𝒜`, `ρ_Ω`): with RC19's height relation it holds for every choice of the other data, and its effect is to define `v₂ shaA − 2v₂ tA` | 4027–4030, 4106–4113 | PRINT (Milne ADT I.7.3, (7.3.1)) + GLUE (RC19's pairings are the canonical height pairings of `𝒜`, `ℬ` for their principal polarizations) | RC15 / RC19 |

No longer fields: the free generators, from `Prints` (BCDT Thm A, Kolyvagin Thm 1), Mordell's
theorem for `E_m` and the index-two descent (`CalibrationModelP.nonempty_modelR`). -/
structure CalibrationModelP {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
  /-- `|Ш(𝒜)[2^∞]|` -/
  shaA : ℕ
  /-- `|Ш(ℬ)[2^∞]|` -/
  shaB : ℕ
  /-- `|𝒜(ℚ)_tors[2^∞]|` -/
  tA : ℕ
  /-- `|ℬ(ℚ)_tors[2^∞]|` -/
  tB : ℕ
  /-- finiteness of `Ш(𝒜)` -/
  shaA_ne : shaA ≠ 0
  /-- finiteness of `Ш(ℬ)` -/
  shaB_ne : shaB ≠ 0
  /-- `𝒜` has torsion -/
  tA_ne : tA ≠ 0
  /-- `ℬ` has torsion -/
  tB_ne : tB ≠ 0
  /-- the finite set of primes carrying the component numbers -/
  Scomp : Finset ℕ
  /-- the component numbers of `𝒜` -/
  cA : ℕ → ℕ
  /-- the component numbers of `ℬ` -/
  cB : ℕ → ℕ
  /-- `t_p = dim_{𝔽₂} E[2]^{Fr_p}` -/
  tp : ℕ → ℕ
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- Edixhoven at a companion prime -/
  hB : ∀ p ∈ D.kfin.natAbs.primeFactors, cB p = 2 ^ tp p
  /-- `t_p ≤ 2` -/
  htp : ∀ p ∈ D.kfin.natAbs.primeFactors, tp p ≤ 2
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : QuadData K (D.kfin : ℚ)
  /-- `φ^*ω_ℬ = a ω_𝒜` -/
  aPull : ℤ
  /-- `ψ^*ω_𝒜 = b ω_ℬ` -/
  bPull : ℤ
  /-- `ab = 4` -/
  hab : aPull * bPull = 4
  /-- `|coker φ_ℝ|` -/
  gam : ℕ
  /-- `|ker φ_ℝ|` -/
  kap : ℕ
  /-- both at most four -/
  hgam : 1 ≤ gam ∧ gam ≤ 4
  /-- both at most four -/
  hkap : 1 ≤ kap ∧ kap ≤ 4
  /-- the Néron period of `𝒜` -/
  OmA : ℝ
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators of any free
  generators of the two rank-one lattices -/
  hmilne : ∀ (gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point)
    (gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point),
    IsFreeGenerator gA → IsFreeGenerator gB →
    Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
      (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
      (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
      ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℤ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `m_i = a_{r_i} − 2χ ≠ 0` -/
  hmne : amov - 2 * chimov ≠ 0
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ rmov - 1
  /-- `v₂ m_i < B_i` (the manuscript's `v₂ m_i ≤ c_E < B_i`) -/
  hBexp : padicValInt 2 (amov - 2 * chimov) < Bexp
  /-- the primitive central value is regular at the centre with the computed valuation -/
  hvprim : v2 (central (D.uPrim Fam x)) =
    ((primValuation (D.jrc (Fam.h x) D.kfin) vL ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)
      ((padicValNat 2 tA : ℕ) : ℤ) ((padicValNat 2 shaA : ℕ) : ℤ)
      ((padicValInt 2 (rmov + 1 - chimov * amov) : ℕ) : ℤ) ((omega (Fam.h x) : ℕ) : ℤ) :
        ℤ) : WithTop ℤ)

attribute [instance] CalibrationModelP.fieldK CalibrationModelP.nfK CalibrationModelP.decK
  CalibrationModelP.quadK

/-- **The free generators from the forward theorems** (tex 4020–4021; Lemma `lem:forward-rank`,
tex 1086–1110): at an address with `ord_{s=1} L(E^{(h_x)},s) = 1` and `L(E^{(h_x k)},1) ≠ 0`,
BCDT and Kolyvagin (`Prints`) give `rank E^{(h_x)}(ℚ) = 1` and `rank E^{(h_x k)}(ℚ) = 0`;
Mordell's theorem for `E_{h_x ℓ}` and the structure theorem give a free generator `q` of
`E^{(h_x)}(ℚ)`; `g_ℬ = (q, 0)`; the index-two descent gives `g_𝒜`. The model of
`CalibrationRC19.lean` follows, with Milne's identity at these generators. PROVED. -/
theorem CalibrationModelP.nonempty_modelR {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family}
    {x : Addr Fam.b} (Pr : Prints) (hℓ : 0 < ℓ) (hx0 : Fam.h x ≠ 0)
    (h1 : AnalyticRank (Etw ℓ (Fam.h x)) 1) (h0 : AnalyticRank (Etw ℓ (Fam.h x * D.kfin)) 0)
    (M : CalibrationModelP D vL G₀ Fam x) : Nonempty (CalibrationModelR D vL G₀ Fam x) := by
  have hℓQ : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hk0 : (D.kfin : ℚ) ≠ 0 := QuadData.k_ne_zero M.quad
  have instA : (Etw ℓ (Fam.h x)).IsElliptic := ellA_of hℓ hx0
  have instB : (qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).IsElliptic :=
    ellB_of hℓ hx0 hk0
  have instB' : (Etw ℓ (Fam.h x * D.kfin)).IsElliptic := by
    simp only [Etw, Int.cast_mul]
    exact instB
  -- the forward theorems
  have hr1 : Module.rank ℤ (Etw ℓ (Fam.h x)).toAffine.Point = 1 := by
    have := (Pr.kolyvagin _ instA (Pr.bcdt _ instA) 1 le_rfl h1).1
    exact_mod_cast this
  have hr0 : Module.rank ℤ (Etw ℓ (Fam.h x * D.kfin)).toAffine.Point = 0 := by
    have := (Pr.kolyvagin _ instB' (Pr.bcdt _ instB') 0 (by norm_num) h0).1
    exact_mod_cast this
  have hr0' : Module.rank ℤ (qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).toAffine.Point =
      0 :=
    (rank_points_congr (by simp only [Etw, Int.cast_mul])).symm.trans hr0
  -- Mordell's theorem for `E^{(h_x)} = E_{h_x ℓ}`
  have hFG : AddGroup.FG (Etw ℓ (Fam.h x)).toAffine.Point := by
    rw [Etw_eq]
    exact PoleRC.mordellWeil_curve _ (mul_ne_zero (by exact_mod_cast hx0) hℓQ)
  obtain ⟨q, hq⟩ := exists_isFreeGenerator_of_rank_eq_one hr1
  have htors : ∀ R : ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange
      ℚ).toAffine.Point, IsOfFinAddOrder R :=
    fun R => isOfFinAddOrder_of_rank_eq_zero hr0' R
  have hq' : IsFreeGenerator
      (q : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point) := hq
  obtain ⟨gA, hgA⟩ := exists_isFreeGenerator_baseChange M.quad (Ecurve ℓ) (Fam.h x : ℚ) q hq'
    htors
  have hgB := isFreeGenerator_prod_zero hq' htors
  exact ⟨{
    shaA := M.shaA
    shaB := M.shaB
    tA := M.tA
    tB := M.tB
    shaA_ne := M.shaA_ne
    shaB_ne := M.shaB_ne
    tA_ne := M.tA_ne
    tB_ne := M.tB_ne
    Scomp := M.Scomp
    cA := M.cA
    cB := M.cB
    tp := M.tp
    hTS := M.hTS
    hcpos := M.hcpos
    hcancel := M.hcancel
    hA1 := M.hA1
    hB := M.hB
    htp := M.htp
    K := M.K
    quad := M.quad
    gA := gA
    gB := (q, 0)
    freeA := hgA
    freeB := hgB
    aPull := M.aPull
    bPull := M.bPull
    hab := M.hab
    gam := M.gam
    kap := M.kap
    hgam := M.hgam
    hkap := M.hkap
    OmA := M.OmA
    hOmA := M.hOmA
    rhoOm := M.rhoOm
    hcv := M.hcv
    hmilne := M.hmilne gA (q, 0) hgA hgB
    hsB := M.hsB
    hgB := M.hgB
    rmov := M.rmov
    amov := M.amov
    chimov := M.chimov
    Bexp := M.Bexp
    hchi := M.hchi
    hmne := M.hmne
    hrmov := M.hrmov
    hBexp := M.hBexp
    hvprim := M.hvprim }⟩

/-- **The remaining inputs of `RCSteps.calibration` with the free generators derived** ((4.6),
tex 3987–4141): as `CalibrationInputs`, with `CalibrationModelP` at every address. -/
def CalibrationInputsP {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelP D vL G₀ F x)

/-- `CalibrationInputsR` from `CalibrationInputsP` and the prints (PROVED). -/
theorem calibrationInputsR_of_P {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsP D) : CalibrationInputsR D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact M.nonempty_modelR Pr hℓ (Family.h_ne_zero hF.1 x) h1 h0

/-- `CalibrationInputs` from `CalibrationInputsP` and the prints (PROVED). -/
theorem calibrationInputs_of_P {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsP D) : CalibrationInputs D :=
  calibrationInputs_of_R hℓ (calibrationInputsR_of_P Pr hℓ h)

/-- **`RCSteps.calibration` from `CalibrationInputsP`** ((4.6), tex 3987–4141), with the uniform
error bound `C_cal = 2v₂L + 2G₀ + 5`. PROVED. -/
theorem calibrationTarget_of_P {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsP D) : CalibrationTarget D :=
  calibrationTarget_of_inputs (calibrationInputs_of_P Pr hℓ h)

end ZInQ.Manuscript.RC.Wiring

import ZInQKernel.Contrib.RC53Assist.InnerLimit.Objects
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Duality

/-!
# Lane RC31, round 2, part 1: the paired inner-limit diagram at a derivative label

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-derivative-switch` (tex 4834–4907): "At a
derivative prime use the actual split local model `L_v = D⁰ ⊕ (F_v ⊕ S_v)[−1] ⊕ D²[−2]` with zero
differential at the retained precision, and retain its pairing and isotropy homotopies. Here `D⁰`
and `D²` are dual, and `F_v, S_v` are the finite and singular isotropic planes. … Thus
`U_str^⊥ = U_rel`"; the transported cross pairing "`β(x, y) = ε e₂(x, J y)`, `ε ∈ k^×`" (tex 5037);
"The retained localization-duality diagrams give `U = U^⊥`" (tex 5065–5070); and Lemma
`ex:limits-inner-limit` (tex 4391–4451): the retained data "include the integral duality maps,
their homotopy inverses, and the homotopies expressing compatibility of duality with localization"
(tex 4385–4388).

For the realized limit diagram of the inner-limit objects (`limitRelaxed G res`, its strict datum
and the actual connecting map), this file builds the cup-product data `SelPairData` of the strict
and relaxed limit Selmer data from two retained pairings, and reduces the producer contract
`LimitPairingCertificate` to the global and local duality quasi-isomorphisms:

* `limitTraceTarget`, `limitLocalTarget`, `limitTraceRes`: the coefficient targets of the trace,
  `k` in every degree; the global one has differential `−1` from degree `2` to degree `3`, so that
  `H³(Cone(E → E_L)[−1]) ≅ k` (`limitTrace`, the sum of the two coordinates, kills boundaries).
* `SplitLocalPairing`: the retained local pairing of the split model, `D⁰ × D² → k`,
  `(F ⊕ S) × (F ⊕ S) → k` and `D² × D⁰ → k` (tex 4860–4868).
* `limitCupL`, `limitCupG`: the local and global cup products. The global one consists of the
  retained global trace pairing `B_G : G^a × G^{3−a} → k` in degree `3` and of the local pairing of
  the restrictions in degree `2`; its Leibniz rule is exactly the chain-level reciprocity identity
  `LimitReciprocity` (`B_G(da, b) + (−1)^a B_G(a, db) = −β(res a, res b)`), which in the realized
  diagram is the trace of the retained Leibniz rule and compatibility of the cup product.
* `limitPair`: the `SelPairData` of (strict, relaxed); the isotropy homotopy is zero (no pairing of
  `D⁰` with the relaxed condition lands in degree two).
* `limitPair_residue`: the residue formula of `LimitPairingCertificate`, from the transported
  pairing (`b₁₁(x, y) = −switchPairing ε σ J y x`).
* **`limitPairingCertificate_of_dualities`**: the certificate from the global duality
  quasi-isomorphism (`globalDualityMap`, Nekovář 5.4.3 for the retained diagram) and the local one
  (`localDualityMap`, Nekovář 5.2.4 / 6.3.4 for the split model), through lane RC26's
  `finiteSelmerDualityNode_proof` (Nekovář 6.3.4).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.Uniform (switchPairing)
open ZInQ.Manuscript.RC.SelmerComplex (cls1 cls1_eq_clsAt clsAt liftCycAt kerToCC iCycles_clsAt)

section Targets

variable (k : Type) [Field k]

/-- The scalar differentials of the global trace target: `−1` from degree `2` to degree `3`. -/
def limitTraceD (n : ℤ) : k := if n = 2 then -1 else 0

/-- The trace target is a complex: consecutive differentials compose to zero. Kind: PROVED. -/
theorem limitTraceD_mul (n : ℤ) : limitTraceD k (n + 1) * limitTraceD k n = 0 := by
  unfold limitTraceD
  by_cases h : n = 2
  · subst h
    simp
  · simp [h]

/-- **The global trace target** `E`: `k` in every degree, with differential `−1` from degree `2`
to degree `3` and `0` otherwise (tex 4385–4388: the retained trace data). Kind: definition. -/
def limitTraceTarget : GCx k where
  X _ := ModuleCat.of k k
  d i _ _ := limitTraceD k i • LinearMap.id
  d_d i j l hij hjl x := by
    subst hij hjl
    change limitTraceD k (i + 1) • (limitTraceD k i • x) = 0
    rw [smul_smul, limitTraceD_mul, zero_smul]

/-- **The local trace target** `E_L`: `k` in every degree, zero differentials. Kind: definition. -/
def limitLocalTarget : GCx k where
  X _ := ModuleCat.of k k
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- **The restriction of the trace targets**: the identity in degree `2`, zero otherwise. Kind:
definition. -/
def limitTraceRes : GHom (limitTraceTarget k) (limitLocalTarget k) where
  f i _ _ := if i = 2 then LinearMap.id else 0
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij h₁ hj
    change (if i + 1 = 2 then LinearMap.id else 0) (limitTraceD k i • x) = 0
    by_cases h : i + 1 = 2
    · have hi : i = 1 := by omega
      subst hi
      have h0 : limitTraceD k 1 = 0 := by simp [limitTraceD]
      rw [ite_eq_left_iff.mpr (fun hn => absurd h hn), h0, zero_smul]
      rfl
    · rw [ite_eq_right_iff.mpr (fun hn => absurd hn h)]
      rfl

/-- **The trace** `Cone(E → E_L)[−1]³ = k × k → k`, the sum of the coordinates. Kind:
definition. -/
def limitTrace : (coneCx (limitTraceRes k)).X 3 →ₗ[k] k :=
  LinearMap.coprod LinearMap.id LinearMap.id

/-- The trace is the sum of the two coordinates. Kind: PROVED (definitional). -/
theorem limitTrace_apply (e z : k) :
    limitTrace k (show (coneCx (limitTraceRes k)).X 3 from (e, z)) = e + z :=
  rfl

/-- **The trace kills boundaries**: `tr(d e, e) = −e + e = 0`. Kind: PROVED. -/
theorem limitTrace_d (z : (coneCx (limitTraceRes k)).X 2) :
    limitTrace k ((coneCx (limitTraceRes k)).d 2 3 rfl z) = 0 := by
  obtain ⟨e, w⟩ := z
  change limitTraceD k 2 • e + ((if (2 : ℤ) = 2 then LinearMap.id else 0) e - 0) = 0
  simp [limitTraceD]

end Targets

/-! ### The local pairing of the split model -/

section Local

variable {k : Type} [Field k]

/-- **The retained local pairing of the split model** `L = D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]`
(tex 4860–4868: "`D⁰` and `D²` are dual, and `F_v, S_v` are the finite and singular isotropic
planes"; tex 5037: the cross pairing `β(x, y) = ε e₂(x, J y)`): its three components of total
degree two. Kind: definition (data). -/
structure SplitLocalPairing (k : Type) [Field k] where
  /-- `D⁰ × D² → k`. -/
  b02 : Vec2 k →ₗ[k] Vec2 k →ₗ[k] k
  /-- `(F ⊕ S) × (F ⊕ S) → k`. -/
  b11 : Coords k →ₗ[k] Coords k →ₗ[k] k
  /-- `D² × D⁰ → k`. -/
  b20 : Vec2 k →ₗ[k] Vec2 k →ₗ[k] k

/-- The local pairing in total degree two, as a degree-indexed family. Kind: definition. -/
def SplitLocalPairing.bl (B : SplitLocalPairing k) :
    ∀ a b : ℤ, (splitLocalComplex k).X a →ₗ[k] (splitLocalComplex k).X b →ₗ[k] k
  | .ofNat 0, .ofNat 2 => B.b02
  | .ofNat 1, .ofNat 1 => B.b11
  | .ofNat 2, .ofNat 0 => B.b20
  | _, _ => 0

/-- The degree-`(0, 2)` component. Kind: PROVED (definitional). -/
theorem SplitLocalPairing.bl_02 (B : SplitLocalPairing k) : B.bl 0 2 = B.b02 := rfl

/-- The degree-`(1, 1)` component. Kind: PROVED (definitional). -/
theorem SplitLocalPairing.bl_11 (B : SplitLocalPairing k) : B.bl 1 1 = B.b11 := rfl

/-- The degree-`(2, 0)` component. Kind: PROVED (definitional). -/
theorem SplitLocalPairing.bl_20 (B : SplitLocalPairing k) : B.bl 2 0 = B.b20 := rfl

/-- The components of the local cup product: the local pairing in degree two, zero otherwise.
Kind: definition. -/
def limitCupLP (B : SplitLocalPairing k) (a b c : ℤ) :
    (splitLocalComplex k).X a →ₗ[k] (splitLocalComplex k).X b →ₗ[k] k :=
  if c = 2 then B.bl a b else 0

/-- In degree two the local cup product is the local pairing. Kind: PROVED. -/
theorem limitCupLP_apply_of_two (B : SplitLocalPairing k) {a b c : ℤ} (hc : c = 2)
    (x : (splitLocalComplex k).X a) (y : (splitLocalComplex k).X b) :
    limitCupLP B a b c x y = B.bl a b x y := by
  unfold limitCupLP
  rw [ite_eq_left hc]

/-- Outside degree two the local cup product vanishes. Kind: PROVED. -/
theorem limitCupLP_apply_of_ne (B : SplitLocalPairing k) {a b c : ℤ} (hc : c ≠ 2)
    (x : (splitLocalComplex k).X a) (y : (splitLocalComplex k).X b) :
    limitCupLP B a b c x y = 0 := by
  unfold limitCupLP
  rw [ite_eq_right hc, LinearMap.zero_apply, LinearMap.zero_apply]

/-- The Leibniz rule of the local cup product (zero differentials). Kind: PROVED. -/
theorem limitCupLP_leib (B : SplitLocalPairing k) (i i₁ j j₁ c₁ : ℤ)
    (x : (splitLocalComplex k).X i) (y : (splitLocalComplex k).X j) :
    (0 : k) = limitCupLP B i₁ j c₁ (0 : (splitLocalComplex k).X i₁) y +
      sgn i • limitCupLP B i j₁ c₁ x (0 : (splitLocalComplex k).X j₁) := by
  simp

/-- **The local cup product** `L × L → E_L`: the local pairing in degree two, zero otherwise; the
Leibniz rule holds since all differentials vanish (tex 4860: "with zero differential at the
retained precision"). Kind: definition. -/
def limitCupL (B : SplitLocalPairing k) :
    GPair (splitLocalComplex k) (splitLocalComplex k) (limitLocalTarget k) where
  P a b c _ := limitCupLP B a b c
  leib i i₁ j j₁ _ c₁ _ _ _ _ x y := limitCupLP_leib B i i₁ j j₁ c₁ x y

end Local

/-! ### The global cup product and the cup-product data -/

section Pairing

variable {k : Type} [Field k] (G : GCx k) (res : GHom G (splitLocalComplex k))

/-- **The retained global trace pairing** `B_G : G^a × G^{3−a} → k` (the trace of the global cup
product, tex 4385–4388). Kind: definition (data type). -/
abbrev GlobalTracePairing := ∀ a b : ℤ, a + b = 3 → G.X a →ₗ[k] G.X b →ₗ[k] k

variable {G}

/-- **Chain-level reciprocity** for the retained global trace pairing: for `a + b = 2`,
`B_G(da, b) + (−1)^a B_G(a, db) = −β(res a, res b)`. In the realized diagram this is the trace of
the Leibniz rule and of the compatibility `res_E(a ∪ b) = res a ∪ res b` of the retained cup product
(the trace kills boundaries of `Cone(E → E_L)[−1]`). Kind: hypothesis (definition). -/
def LimitReciprocity (BG : GlobalTracePairing G) (B : SplitLocalPairing k) : Prop :=
  ∀ (a b : ℤ) (h : a + b = 2) (x : G.X a) (y : G.X b),
    BG (a + 1) b (by omega) (G.d a (a + 1) rfl x) y +
        sgn a • BG a (b + 1) (by omega) x (G.d b (b + 1) rfl y) =
      -(B.bl a b (res.f a a rfl x) (res.f b b rfl y))

/-- The components of the global cup product: `B_G` in degree `3`, the local pairing of the
restrictions in degree `2`, zero otherwise. Kind: definition. -/
def limitCupGP (BG : GlobalTracePairing G) (B : SplitLocalPairing k) (a b c : ℤ) (h : a + b = c) :
    G.X a →ₗ[k] G.X b →ₗ[k] k :=
  if hc : c = 3 then BG a b (by omega)
  else if c = 2 then (B.bl a b).compl₁₂ (res.f a a rfl) (res.f b b rfl) else 0

/-- In degree three the global cup product is the global trace pairing. Kind: PROVED. -/
theorem limitCupGP_apply_of_three (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    {a b c : ℤ} (h : a + b = c) (hc : c = 3) (x : G.X a) (y : G.X b) :
    limitCupGP res BG B a b c h x y = BG a b (by omega) x y := by
  unfold limitCupGP
  rw [dite_eq_left hc]

/-- In degree two the global cup product is the local pairing of the restrictions. Kind: PROVED. -/
theorem limitCupGP_apply_of_two (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    {a b c : ℤ} (h : a + b = c) (hc : c = 2) (x : G.X a) (y : G.X b) :
    limitCupGP res BG B a b c h x y = B.bl a b (res.f a a rfl x) (res.f b b rfl y) := by
  unfold limitCupGP
  rw [dite_eq_right (by omega), ite_eq_left hc]
  rfl

/-- Outside degrees two and three the global cup product vanishes. Kind: PROVED. -/
theorem limitCupGP_apply_of_ne (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    {a b c : ℤ} (h : a + b = c) (hc3 : c ≠ 3) (hc2 : c ≠ 2) (x : G.X a) (y : G.X b) :
    limitCupGP res BG B a b c h x y = 0 := by
  unfold limitCupGP
  rw [dite_eq_right hc3, ite_eq_right hc2, LinearMap.zero_apply, LinearMap.zero_apply]

/-- The Leibniz rule of the global cup product, from `LimitReciprocity`. Kind: PROVED. -/
theorem limitCupGP_leib (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    (hrec : LimitReciprocity res BG B) (i j c : ℤ) (h : i + j = c) (x : G.X i) (y : G.X j) :
    limitTraceD k c • limitCupGP res BG B i j c h x y =
      limitCupGP res BG B (i + 1) j (c + 1) (by omega) (G.d i (i + 1) rfl x) y +
        sgn i • limitCupGP res BG B i (j + 1) (c + 1) (by omega) x (G.d j (j + 1) rfl y) := by
  by_cases h2 : c = 2
  · subst h2
    rw [limitCupGP_apply_of_two res BG B h rfl,
      limitCupGP_apply_of_three res BG B _ (by norm_num),
      limitCupGP_apply_of_three res BG B _ (by norm_num), hrec i j h x y]
    simp [limitTraceD]
  · by_cases h1 : c = 1
    · subst h1
      have r1 : res.f (i + 1) (i + 1) rfl (G.d i (i + 1) rfl x) = 0 :=
        res.comm i (i + 1) i (i + 1) rfl rfl rfl rfl x
      have r2 : res.f (j + 1) (j + 1) rfl (G.d j (j + 1) rfl y) = 0 :=
        res.comm j (j + 1) j (j + 1) rfl rfl rfl rfl y
      rw [limitCupGP_apply_of_ne res BG B h (by norm_num) (by norm_num),
        limitCupGP_apply_of_two res BG B _ (by norm_num),
        limitCupGP_apply_of_two res BG B _ (by norm_num), r1, r2]
      simp
    · have hc1 : c + 1 ≠ 3 := fun e => h2 (by omega)
      have hc2 : c + 1 ≠ 2 := fun e => h1 (by omega)
      rw [limitCupGP_apply_of_ne res BG B _ hc1 hc2, limitCupGP_apply_of_ne res BG B _ hc1 hc2]
      simp [limitTraceD, h2]

/-- **The global cup product** `G × G → E`: `B_G` in degree `3`, the local pairing of the
restrictions in degree `2`, zero otherwise; its Leibniz rule is `LimitReciprocity` in degree two
and the chain-map property of `res` in degree one. Kind: definition. -/
def limitCupG (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    (hrec : LimitReciprocity res BG B) : GPair G G (limitTraceTarget k) where
  P a b c h := limitCupGP res BG B a b c h
  leib i i₁ j j₁ c c₁ h hi hj hc x y := by
    subst hi hj hc
    exact limitCupGP_leib res BG B hrec i j c h x y

/-- Compatibility of the two cup products with restriction, in clean form. -/
theorem limitCup_compat (BG : GlobalTracePairing G) (B : SplitLocalPairing k) (i j c : ℤ)
    (h : i + j = c) (a : G.X i) (b : G.X j) :
    (if c = 2 then (LinearMap.id : k →ₗ[k] k) else 0) (limitCupGP res BG B i j c h a b) =
      limitCupLP B i j c (res.f i i rfl a) (res.f j j rfl b) := by
  by_cases h2 : c = 2
  · rw [ite_eq_left h2, limitCupLP_apply_of_two B h2, LinearMap.id_apply]
    exact limitCupGP_apply_of_two res BG B h h2 a b
  · rw [ite_eq_right h2, limitCupLP_apply_of_ne B h2, LinearMap.zero_apply]

/-- The strict local condition `D⁰` maps to zero outside degree zero. -/
theorem strictLimit_ι_eq_zero (i : ℤ) (hi : i ≠ 0)
    (u : (ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData (limitRelaxed G res).D
      (strictLimitMap G res)).U.X i) :
    (ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData (limitRelaxed G res).D
      (strictLimitMap G res)).ι.f i i rfl u = 0 := by
  rcases i with ((_ | _ | i) | i)
  · exact absurd rfl hi
  · change ((show ↥(⊥ : Submodule k (Coords k)) from u) : Coords k) = 0
    exact (Submodule.mem_bot k).mp (show ↥(⊥ : Submodule k (Coords k)) from u).2
  · rfl
  · rfl

/-- The relaxed local condition has no degree-two term. -/
theorem relaxedLimit_ι_two (v : (limitRelaxed G res).D.U.X 2) :
    (limitRelaxed G res).D.ι.f 2 2 rfl v = 0 :=
  rfl

/-- The local cup product vanishes outside degree two and on zero arguments. -/
theorem limitCupLP_eq_zero (B : SplitLocalPairing k) (i j c₁ : ℤ) (x : (splitLocalComplex k).X i)
    (y : (splitLocalComplex k).X j) (h : c₁ ≠ 2 ∨ x = 0 ∨ y = 0) :
    (0 : k) = limitCupLP B i j c₁ x y := by
  rcases h with h | h | h
  · rw [limitCupLP_apply_of_ne B h]
  · rw [h, map_zero, LinearMap.zero_apply]
  · rw [h, map_zero]

/-- The isotropy identity, in clean form: no pairing of the strict condition with the relaxed one
lands in degree two. -/
theorem limitCup_isotropy (B : SplitLocalPairing k) (i j c₁ : ℤ) (hij : i + j = c₁)
    (u : (ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData (limitRelaxed G res).D
      (strictLimitMap G res)).U.X i)
    (v : (limitRelaxed G res).D.U.X j) :
    (0 : k) = limitCupLP B i j c₁
      ((ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData (limitRelaxed G res).D
        (strictLimitMap G res)).ι.f i i rfl u)
      ((limitRelaxed G res).D.ι.f j j rfl v) := by
  by_cases h2 : c₁ = 2
  · by_cases hi0 : i = 0
    · subst hi0
      have hj2 : j = 2 := by omega
      subst hj2
      exact limitCupLP_eq_zero B 0 2 c₁ _ _ (Or.inr (Or.inr (relaxedLimit_ι_two res v)))
    · exact limitCupLP_eq_zero B i j c₁ _ _ (Or.inr (Or.inl (strictLimit_ι_eq_zero res i hi0 u)))
  · exact limitCupLP_eq_zero B i j c₁ _ _ (Or.inl h2)

/-- **The cup-product data of the strict and relaxed limit Selmer data** (Nekovář 6.2–6.3 in the
form of lane RC26's `SelPairData`): global cup product `limitCupG`, local cup product `limitCupL`,
the restriction `limitTraceRes`, and the zero isotropy homotopy. Kind: definition. -/
def limitPair (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    (hrec : LimitReciprocity res BG B) :
    SelPairData (ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData (limitRelaxed G res).D
        (strictLimitMap G res))
      (limitRelaxed G res).D where
  E := limitTraceTarget k
  EL := limitLocalTarget k
  resE := limitTraceRes k
  cupG := limitCupG res BG B hrec
  cupL := limitCupL B
  compat i j c i' j' c' h h' hi hj hc a b := by
    subst hi hj hc
    exact limitCup_compat res BG B i j c h a b
  hU _ _ _ _ := 0
  isotropy i i₁ j j₁ c c₁ h hi hj hc u v := by
    subst hi hj hc
    refine Eq.trans ?_ (limitCup_isotropy res B i j (c + 1) (by omega) u v)
    show (0 : k →ₗ[k] k) 0 + (0 : k) + sgn i • (0 : k) = 0
    simp

/-- The trace kills the boundaries of the trace target of `limitPair`. Kind: PROVED. -/
theorem limitPair_htr (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    (hrec : LimitReciprocity res BG B) (z : (coneCx (limitPair res BG B hrec).resE).X 2) :
    limitTrace k ((coneCx (limitPair res BG B hrec).resE).d 2 3 rfl z) = 0 :=
  limitTrace_d k z

end Pairing

/-! ### The residue formula and the certificate -/

section Certificate

variable {k : Type} [Field k] {G : GCx k} (res : GHom G (splitLocalComplex k))

omit [Field k] in
/-- `H¹(W) ≃ W¹` sends the class of a cocycle to the cocycle. Kind: PROVED. -/
theorem h1Equiv_cls1_aux {k : Type} [Field k] (W : GCx k) (hW : ConcDegOne W)
    (x : LinearMap.ker (W.d 1 2 rfl)) : h1Equiv W hW (cls1 W x) = x.1 := by
  rw [h1Equiv_apply, cls1_eq_clsAt]
  unfold clsAt
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have := congrArg (fun f => ModuleCat.Hom.hom f
    ((liftCycAt W.toCC 1 2 rfl).hom (kerToCC W 1 2 rfl x))) (homologyπ_h1Iso W hW)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  rw [this]
  exact iCycles_clsAt W 1 2 rfl x

/-- The residue computation in clean form. -/
theorem limitResidue_clean (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    (x y : (splitLocalComplex k).X 1) :
    limitCupGP res BG B 2 1 3 rfl 0 0 +
        (limitCupLP B 1 1 2 (-x) y + sgn 2 • limitCupLP B 2 0 2 (res.f 2 2 rfl 0) 0 + 0) =
      -(B.bl 1 1 x y) := by
  have hA : limitCupGP res BG B 2 1 3 rfl 0 0 = 0 := LinearMap.map_zero₂ _ _
  have hB1 : limitCupLP B 1 1 2 (-x) y = -(B.bl 1 1 x y) := by
    rw [LinearMap.map_neg₂, limitCupLP_apply_of_two B rfl]
  have hB2 : limitCupLP B 2 0 2 (res.f 2 2 rfl 0) 0 = 0 := map_zero _
  rw [hA, hB1, hB2]
  simp

/-- **The residue formula of the certificate** (lane RC26's `SwitchCoordinates` shape; tex
2816–2818 and 5037): for the transported local pairing `b₁₁(x, y) = −switchPairing ε σ J y x`, the
trace of the Selmer cup product of `(0, s, −ι u)` and `(0, t, 0)` is the switch pairing of the
coordinates of `t` and `u`. Kind: PROVED. -/
theorem limitPair_residue (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    (hrec : LimitReciprocity res BG B) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hb11 : ∀ x y, B.b11 x y = -(switchPairing ε σ J y x))
    (t u : (limitRelaxed G res).D.U.X 1)
    (s : (conditionComplex (⊥ : Submodule k (Coords k))).X 2)
    (ct cu : LinearMap.ker ((limitRelaxed G res).Wrel.d 1 2 rfl))
    (hct : ct.1 = (limitRelaxed G res).gR.f 1 1 rfl t)
    (hcu : cu.1 = (limitRelaxed G res).gR.f 1 1 rfl u) :
    limitTrace k (selCupFun (limitPair res BG B hrec) 2 1 3 rfl
        ((0 : (limitRelaxed G res).D.G.X 2), s,
          -((limitRelaxed G res).D.ι.f 1 (2 - 1) (by omega) u))
        ((0 : (limitRelaxed G res).D.G.X 1), t, (0 : (limitRelaxed G res).D.L.X (1 - 1)))) =
      switchPairing ε σ J ((limitRelaxed G res).eR (cls1 (limitRelaxed G res).Wrel ct))
        ((limitRelaxed G res).eR (cls1 (limitRelaxed G res).Wrel cu)) := by
  have et : (limitRelaxed G res).eR (cls1 (limitRelaxed G res).Wrel ct) =
      (limitRelaxed G res).D.ι.f 1 1 rfl t :=
    (h1Equiv_cls1_aux (literalLimitRelaxed G res).Wrel (literalLimitRelaxed G res).hWrel ct).trans
      hct
  have eu : (limitRelaxed G res).eR (cls1 (limitRelaxed G res).Wrel cu) =
      (limitRelaxed G res).D.ι.f 1 1 rfl u :=
    (h1Equiv_cls1_aux (literalLimitRelaxed G res).Wrel (literalLimitRelaxed G res).hWrel cu).trans
      hcu
  refine (limitResidue_clean res BG B ((limitRelaxed G res).D.ι.f 1 1 rfl u)
    ((limitRelaxed G res).D.ι.f 1 1 rfl t)).trans ?_
  have h3 := hb11 ((limitRelaxed G res).D.ι.f 1 1 rfl u) ((limitRelaxed G res).D.ι.f 1 1 rfl t)
  refine (congrArg Neg.neg h3).trans ((neg_neg _).trans ?_)
  exact congrArg₂ (fun a b => switchPairing ε σ J a b) et.symm eu.symm

/-- A perfect coefficient pairing over the field itself (`k × k → k`). -/
def limitPerfectSelf (k : Type) [Field k] : PerfectCoefficientPairing k :=
  ⟨ModuleCat.of k k, ModuleCat.of k k, LinearMap.mul k k,
    ⟨fun a b h => by simpa using LinearMap.congr_fun h 1, fun f => ⟨f 1, LinearMap.ext fun x => by
      rw [LinearMap.mul_apply', mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]⟩⟩,
    ⟨fun a b h => by simpa using LinearMap.congr_fun h 1, fun f => ⟨f 1, LinearMap.ext fun x => by
      rw [LinearMap.flip_apply, LinearMap.mul_apply', ← smul_eq_mul, ← map_smul, smul_eq_mul,
        mul_one]⟩⟩⟩

/-- **The producer contract from the two dualities** (Nekovář 6.3.4 in lane RC26's cochain form,
`finiteSelmerDualityNode_proof`): if the global duality map of the limit pairing data is a
quasi-isomorphism (`hglob`: the retained global duality of the limit diagram, Nekovář 5.4.3 at the
finite stages, transported by Lemma `ex:limits-inner-limit`) and so is the local duality map of the
split model (`hloc`: Nekovář 5.2.4 / 6.3.4 for the split model, see `LimitLocal.lean`), and the
local pairing in degree one is the transported switch pairing (`hb11`, tex 5037), then the
inner-limit producer contract `LimitPairingCertificate` holds. Kind: PROVED. -/
theorem limitPairingCertificate_of_dualities (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    (hrec : LimitReciprocity res BG B) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hb11 : ∀ x y, B.b11 x y = -(switchPairing ε σ J y x))
    (hglob : QuasiIso (GHom.toCC (globalDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec))))
    (hloc : QuasiIso (GHom.toCC (localDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec)))) :
    LimitPairingCertificate G res ε σ J :=
  ⟨limitPair res BG B hrec, limitTrace k, limitPair_htr res BG B hrec,
    finiteSelmerDualityNode_proof k _ _ (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec) (limitPerfectSelf k) (Or.inl (field_selfInjective k)) hglob
      hloc,
    fun t u s _ _ ct cu hct hcu => limitPair_residue res BG B hrec ε σ J hb11 t u s ct cu hct hcu⟩

end Certificate


end ZInQ.Manuscript.RC.FibreDuality

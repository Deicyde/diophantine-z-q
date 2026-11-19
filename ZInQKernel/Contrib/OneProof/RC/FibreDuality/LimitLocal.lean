import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitPairing

/-!
# Lane RC31, round 2, part 2: local duality for the split limit model

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-derivative-switch` (tex 4834–4907): "At a
derivative prime use the actual split local model `L_v = D⁰ ⊕ (F_v ⊕ S_v)[−1] ⊕ D²[−2]` with zero
differential at the retained precision, and retain its pairing and isotropy homotopies. … Thus
`U_str^⊥ = U_rel`"; local duality in the cochain form of Nekovář, *Selmer complexes*, 5.2.4 and
6.3.4.

For the strict limit datum (`U_str = D⁰`, the condition `⊥` in degree one) and the relaxed one
(`U_rel = D⁰ ⊕ (F ⊕ S)[−1]`), the complex `Cone(U_str → L)[−1]` has cohomology `F ⊕ S` in degree
two and `D²` in degree three, and the target `Hom(U_rel, k)[−3]` is `Hom(F ⊕ S, k)` in degree two
and `Hom(D⁰, k)` in degree three. The local duality map of the limit pairing data (`limitPair`,
trace `limitTrace`) is, in these two degrees, the adjoint of `b₁₁` and of `b₂₀`. This file proves:

* **`limitLocalDuality_quasiIso`**: if `b₁₁` and `b₂₀` have bijective adjoints, the local duality
  map is a quasi-isomorphism; it is the forward map of an explicit homotopy equivalence
  (`limitLocalHomotopyEquiv`), whose inverse uses the inverse adjoints and whose homotopy on the
  source contracts `D⁰ → L⁰`.
* **`switch_b11_bijective`**: the transported switch pairing `b₁₁(x, y) = −switchPairing ε σ J y x`
  (tex 5037) has bijective adjoint for `ε, σ ≠ 0`, `J² = 1`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.Uniform (switchPairing)

/-! ### Vanishing terms -/

section Terms

variable {k : Type} [Field k]

/-- A condition complex vanishes outside degrees zero and one (tex 4860: the local conditions
retain `D⁰` and a plane of `F ⊕ S`). Kind: PROVED. -/
theorem conditionTerms_subsingleton (P : Submodule k (Coords k)) (n : ℤ) (h0 : n ≠ 0)
    (h1 : n ≠ 1) : Subsingleton (conditionTerms P n) := by
  rcases n with ((_ | _ | n) | n)
  · exact absurd rfl h0
  · exact absurd rfl h1
  · change Subsingleton PUnit
    infer_instance
  · change Subsingleton PUnit
    infer_instance

/-- The split local model vanishes outside degrees zero, one and two (tex 4860). Kind: PROVED. -/
theorem splitLocalTerms_subsingleton (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton (splitLocalTerms k n) := by
  rcases n with ((_ | _ | _ | n) | n)
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · change Subsingleton PUnit
    infer_instance
  · change Subsingleton PUnit
    infer_instance

/-- An elementary identity in `D⁰ = k²`. Kind: PROVED. -/
theorem vec2_zero_eq (u : Vec2 k) : (0 : Vec2 k) = -u - 0 + u := by
  rw [sub_zero, neg_add_cancel]

end Terms

/-! ### The inverse adjoints -/

section Adjoints

variable {k : Type} [Field k] (B : SplitLocalPairing k)

/-- **The inverse adjoint of `b₁₁`**, read on the relaxed plane `⊤ ≅ F ⊕ S`: a linear form `φ` on
`⊤` goes to the unique `x` with `b₁₁(x, ·) = φ` (tex 4860–4868: `F_v ⊕ S_v` is self-dual). Kind:
definition. -/
def limitE11 (h11 : Function.Bijective B.b11) :
    Module.Dual k ↥(⊤ : Submodule k (Coords k)) →ₗ[k] Coords k :=
  (LinearEquiv.ofBijective B.b11 h11).symm.toLinearMap ∘ₗ
    (Submodule.topEquiv (R := k) (M := Coords k)).symm.toLinearMap.dualMap

/-- The inverse adjoint of `b₁₁` inverts the adjoint. Kind: PROVED. -/
theorem limitE11_eq (h11 : Function.Bijective B.b11)
    (φ : Module.Dual k ↥(⊤ : Submodule k (Coords k)))
    (x : Coords k) (h : ∀ v : ↥(⊤ : Submodule k (Coords k)), φ v = B.b11 x v) :
    limitE11 B h11 φ = x := by
  have hψ : (Submodule.topEquiv (R := k) (M := Coords k)).symm.toLinearMap.dualMap φ = B.b11 x :=
    LinearMap.ext fun y => h _
  show (LinearEquiv.ofBijective B.b11 h11).symm
    ((Submodule.topEquiv (R := k) (M := Coords k)).symm.toLinearMap.dualMap φ) = x
  rw [hψ]
  exact (LinearEquiv.ofBijective B.b11 h11).symm_apply_apply x

/-- The adjoint of `b₁₁` inverts the inverse adjoint. Kind: PROVED. -/
theorem limitE11_right (h11 : Function.Bijective B.b11)
    (φ : Module.Dual k ↥(⊤ : Submodule k (Coords k))) (v : ↥(⊤ : Submodule k (Coords k))) :
    B.b11 (limitE11 B h11 φ) v = φ v :=
  LinearMap.congr_fun ((LinearEquiv.ofBijective B.b11 h11).apply_symm_apply
    ((Submodule.topEquiv (R := k) (M := Coords k)).symm.toLinearMap.dualMap φ)) v

/-- **The inverse adjoint of `b₂₀`** `Hom(D⁰, k) → D²` (tex 4860: "`D⁰` and `D²` are dual"). Kind:
definition. -/
def limitE20 (h20 : Function.Bijective B.b20) : Module.Dual k (Vec2 k) →ₗ[k] Vec2 k :=
  (LinearEquiv.ofBijective B.b20 h20).symm.toLinearMap

/-- The inverse adjoint of `b₂₀` inverts the adjoint. Kind: PROVED. -/
theorem limitE20_eq (h20 : Function.Bijective B.b20) (φ : Module.Dual k (Vec2 k)) (x : Vec2 k)
    (h : ∀ v, φ v = B.b20 x v) : limitE20 B h20 φ = x := by
  have hψ : φ = B.b20 x := LinearMap.ext h
  rw [hψ]
  exact (LinearEquiv.ofBijective B.b20 h20).symm_apply_apply x

/-- The adjoint of `b₂₀` inverts the inverse adjoint. Kind: PROVED. -/
theorem limitE20_right (h20 : Function.Bijective B.b20) (φ : Module.Dual k (Vec2 k))
    (v : Vec2 k) : B.b20 (limitE20 B h20 φ) v = φ v :=
  LinearMap.congr_fun ((LinearEquiv.ofBijective B.b20 h20).apply_symm_apply φ) v

end Adjoints

/-! ### The local duality map and its homotopy inverse -/

section Local

variable {k : Type} [Field k] {G : GCx k} (res : GHom G (splitLocalComplex k))

/-- The strict limit Selmer datum `restrictData (limitRelaxed G res).D (strictLimitMap G res)`
(tex 4860–4870: the strict condition `D⁰`). Kind: definition. -/
abbrev limitStrictSel : SelData k :=
  ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData (limitRelaxed G res).D (strictLimitMap G res)

/-- **The local duality map, explicitly**: `(u, x) ↦ (v ↦ x ∪ ι v)` in total degree two
(Nekovář 5.2.4: `(u, x) ↦ (v ↦ tr(0, x ∪ ι' v + h(u, v)))`, with zero isotropy homotopy). Kind:
PROVED. -/
theorem limitLocal_apply (BG : GlobalTracePairing G) (B : SplitLocalPairing k)
    (hrec : LimitReciprocity res BG B) (i : ℤ) (u : (limitStrictSel res).U.X i)
    (x : (splitLocalComplex k).X (i - 1)) (v : (limitRelaxed G res).D.U.X (3 - i)) :
    asDual ((localDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec)).f i i rfl (u, x)) v =
      limitCupLP B (i - 1) (3 - i) 2 x ((limitRelaxed G res).D.ι.f (3 - i) (3 - i) rfl v) := by
  change limitCupGP res BG B i (3 - i) 3 (by omega) 0 0 +
      (limitCupLP B (i - 1) (3 - i) (3 - 1) x ((limitRelaxed G res).D.ι.f (3 - i) (3 - i) rfl v) +
        sgn i • limitCupLP B i (3 - i - 1) (3 - 1) (res.f i i rfl 0) 0 + 0) = _
  rw [LinearMap.map_zero₂, map_zero]
  simp only [smul_zero, add_zero, zero_add]
  rfl

/-- The target `Hom(U_rel, k)[−3]` has zero differentials (tex 4860). Kind: PROVED. -/
theorem limitDual_d (i j : ℤ) (h : i + 1 = j) (φ : (dualCx (limitRelaxed G res).D.U 3).X i) :
    (dualCx (limitRelaxed G res).D.U 3).d i j h φ = 0 := by
  refine dualCx_ext fun x => ?_
  have hx : (limitRelaxed G res).D.U.d (3 - j) (3 - i) (by omega) x = 0 := rfl
  rw [dualCx_d_apply, hx, map_zero, smul_zero]
  rfl

/-- The target `Hom(U_rel, k)[−3]` vanishes outside degrees two and three. Kind: PROVED. -/
theorem limitDual_subsingleton (n : ℤ) (h2 : n ≠ 2) (h3 : n ≠ 3) :
    Subsingleton ((dualCx (limitRelaxed G res).D.U 3).X n) := by
  have hs : Subsingleton ((limitRelaxed G res).D.U.X (3 - n)) :=
    conditionTerms_subsingleton ⊤ (3 - n) (by omega) (by omega)
  refine ⟨fun φ ψ => dualCx_ext fun v => ?_⟩
  rw [@Subsingleton.elim _ hs v 0, map_zero, map_zero]

/-- The source `Cone(U_str → L)[−1]` vanishes outside degrees zero to three. Kind: PROVED. -/
theorem limitLoc_subsingleton (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) (h3 : n ≠ 3) :
    Subsingleton ((locCx (limitStrictSel res)).X n) := by
  have := conditionTerms_subsingleton (⊥ : Submodule k (Coords k)) n h0 h1
  have := splitLocalTerms_subsingleton (k := k) (n - 1) (by omega) (by omega) (by omega)
  change Subsingleton
    (↑(conditionTerms (⊥ : Submodule k (Coords k)) n) × ↑(splitLocalTerms k (n - 1)))
  infer_instance

/-- The differential of `Cone(U_str → L)[−1]` vanishes on elements `(0, x)`. Kind: PROVED. -/
theorem limitLoc_d_zero_fst (i j : ℤ) (h : i + 1 = j) (x : (splitLocalComplex k).X (i - 1)) :
    (locCx (limitStrictSel res)).d i j h
      ((0, x) : (limitStrictSel res).U.X i × (splitLocalComplex k).X (i - 1)) = 0 := by
  refine Prod.ext (map_zero _) ?_
  change -((limitStrictSel res).ι.f i (j - 1) (by omega) 0) - 0 =
    (0 : (splitLocalComplex k).X (j - 1))
  rw [map_zero, neg_zero, sub_zero]
  rfl

variable (B : SplitLocalPairing k)

/-- The components of the homotopy inverse: the inverse adjoint of `b₁₁` in degree two and of `b₂₀`
in degree three, zero otherwise. Kind: definition. -/
def limitLocalInvAt (h11 : Function.Bijective B.b11) (h20 : Function.Bijective B.b20) :
    ∀ n : ℤ, (dualCx (limitRelaxed G res).D.U 3).X n →ₗ[k] (locCx (limitStrictSel res)).X n
  | .ofNat 2 => (LinearMap.inr k PUnit.{1} (Coords k)).comp (limitE11 B h11)
  | .ofNat 3 => (LinearMap.inr k PUnit.{1} (Vec2 k)).comp (limitE20 B h20)
  | _ => 0

/-- The homotopy inverse has zero first coordinate. Kind: PROVED. -/
theorem limitLocalInvAt_fst (h11 : Function.Bijective B.b11) (h20 : Function.Bijective B.b20)
    (n : ℤ) (φ : (dualCx (limitRelaxed G res).D.U 3).X n) :
    (limitLocalInvAt res B h11 h20 n φ).1 = 0 := by
  rcases n with ((_ | _ | _ | _ | n) | n) <;> rfl

/-- **The homotopy inverse of the local duality map** `Hom(U_rel, k)[−3] → Cone(U_str → L)[−1]`,
`φ ↦ (0, b₁₁⁻¹ φ)` in degree two and `φ ↦ (0, b₂₀⁻¹ φ)` in degree three. Kind: definition. -/
def limitLocalInv (h11 : Function.Bijective B.b11) (h20 : Function.Bijective B.b20) :
    GHom (dualCx (limitRelaxed G res).D.U 3) (locCx (limitStrictSel res)) where
  f a b hab := by subst hab; exact limitLocalInvAt res B h11 h20 a
  comm i i₁ j j₁ hij h₁ h₂ hj φ := by
    subst hij hj h₁
    change limitLocalInvAt res B h11 h20 (i + 1)
        ((dualCx (limitRelaxed G res).D.U 3).d i (i + 1) rfl φ) =
      (locCx (limitStrictSel res)).d i (i + 1) h₂ (limitLocalInvAt res B h11 h20 i φ)
    rw [limitDual_d, map_zero]
    have hp : limitLocalInvAt res B h11 h20 i φ =
        ((0, (limitLocalInvAt res B h11 h20 i φ).2) :
          (limitStrictSel res).U.X i × (splitLocalComplex k).X (i - 1)) :=
      Prod.ext (limitLocalInvAt_fst res B h11 h20 i φ) rfl
    rw [hp]
    exact (limitLoc_d_zero_fst res i (i + 1) h₂ _).symm

/-- The components of the homotopy on the source: `(w, y) ↦ (y, 0)` from degree one to degree
zero (it contracts `D⁰ = U_str⁰ → L⁰`), zero otherwise. Kind: definition. -/
def limitLocalHtpAt :
    ∀ b : ℤ, (locCx (limitStrictSel res)).X (b + 1) →ₗ[k] (locCx (limitStrictSel res)).X b
  | .ofNat 0 => (LinearMap.inl k (Vec2 k) PUnit.{1}).comp
      (LinearMap.snd k ↥(⊥ : Submodule k (Coords k)) (Vec2 k))
  | _ => 0

/-- The homotopy on the source, relation-indexed. Kind: definition. -/
def limitLocalHtp (a b : ℤ) (hab : b + 1 = a) :
    (locCx (limitStrictSel res)).X a →ₗ[k] (locCx (limitStrictSel res)).X b := by
  subst hab
  exact limitLocalHtpAt res b

variable (BG : GlobalTracePairing G) (hrec : LimitReciprocity res BG B)
  (h11 : Function.Bijective B.b11) (h20 : Function.Bijective B.b20)

/-- The homotopy identity on the source in degree zero. Kind: PROVED. -/
theorem limitLocal_homInv_zero (c : (locCx (limitStrictSel res)).X 0) :
    (limitLocalInv res B h11 h20).f 0 0 rfl ((localDualityMap (limitPair res BG B hrec)
      (limitTrace k) (limitPair_htr res BG B hrec)).f 0 0 rfl c) =
      limitLocalHtp res 1 0 rfl ((locCx (limitStrictSel res)).d 0 1 rfl c) +
        (locCx (limitStrictSel res)).d (0 - 1) 0 (by omega)
          (limitLocalHtp res 0 (0 - 1) (by omega) c) + c := by
  have e1 : (limitLocalInv res B h11 h20).f 0 0 rfl ((localDualityMap (limitPair res BG B hrec)
      (limitTrace k) (limitPair_htr res BG B hrec)).f 0 0 rfl c) = 0 := rfl
  have e2 : limitLocalHtp res 0 (0 - 1) (by omega) c = 0 := rfl
  rw [e1, e2, map_zero, add_zero]
  obtain ⟨u, x⟩ := c
  refine Prod.ext ?_ (Subsingleton.elim (α := PUnit) _ _)
  exact vec2_zero_eq u

/-- The homotopy identity on the source in degree one. Kind: PROVED. -/
theorem limitLocal_homInv_one (c : (locCx (limitStrictSel res)).X 1) :
    (limitLocalInv res B h11 h20).f 1 1 rfl ((localDualityMap (limitPair res BG B hrec)
      (limitTrace k) (limitPair_htr res BG B hrec)).f 1 1 rfl c) =
      limitLocalHtp res 2 1 rfl ((locCx (limitStrictSel res)).d 1 2 rfl c) +
        (locCx (limitStrictSel res)).d (1 - 1) 1 (by omega)
          (limitLocalHtp res 1 (1 - 1) (by omega) c) + c := by
  have e1 : (limitLocalInv res B h11 h20).f 1 1 rfl ((localDualityMap (limitPair res BG B hrec)
      (limitTrace k) (limitPair_htr res BG B hrec)).f 1 1 rfl c) = 0 := rfl
  have e2 : limitLocalHtp res 2 1 rfl ((locCx (limitStrictSel res)).d 1 2 rfl c) = 0 := rfl
  rw [e1, e2, zero_add]
  obtain ⟨w, y⟩ := c
  refine Prod.ext (Subsingleton.elim (α := ↥(⊥ : Submodule k (Coords k))) _ _) ?_
  exact vec2_zero_eq y

/-- The homotopy identity on the source in degree two: the composite is the identity, since
`b₁₁⁻¹` inverts the adjoint of `b₁₁`. Kind: PROVED. -/
theorem limitLocal_homInv_two (c : (locCx (limitStrictSel res)).X 2) :
    (limitLocalInv res B h11 h20).f 2 2 rfl ((localDualityMap (limitPair res BG B hrec)
      (limitTrace k) (limitPair_htr res BG B hrec)).f 2 2 rfl c) =
      limitLocalHtp res 3 2 rfl ((locCx (limitStrictSel res)).d 2 3 rfl c) +
        (locCx (limitStrictSel res)).d (2 - 1) 2 (by omega)
          (limitLocalHtp res 2 (2 - 1) (by omega) c) + c := by
  have e1 : limitLocalHtp res 3 2 rfl ((locCx (limitStrictSel res)).d 2 3 rfl c) = 0 := rfl
  have e2 : limitLocalHtp res 2 (2 - 1) (by omega) c = 0 := rfl
  rw [e1, e2, map_zero, zero_add, zero_add]
  obtain ⟨u, x⟩ := c
  refine Prod.ext (Subsingleton.elim (α := PUnit) _ _) ?_
  change limitE11 B h11 ((localDualityMap (limitPair res BG B hrec) (limitTrace k)
    (limitPair_htr res BG B hrec)).f 2 2 rfl (u, x)) = x
  exact limitE11_eq B h11 _ x fun v =>
    (limitLocal_apply res BG B hrec 2 u x v).trans (limitCupLP_apply_of_two B rfl _ _)

/-- The homotopy identity on the source in degree three: the composite is the identity, since
`b₂₀⁻¹` inverts the adjoint of `b₂₀`. Kind: PROVED. -/
theorem limitLocal_homInv_three (c : (locCx (limitStrictSel res)).X 3) :
    (limitLocalInv res B h11 h20).f 3 3 rfl ((localDualityMap (limitPair res BG B hrec)
      (limitTrace k) (limitPair_htr res BG B hrec)).f 3 3 rfl c) =
      limitLocalHtp res 4 3 rfl ((locCx (limitStrictSel res)).d 3 4 rfl c) +
        (locCx (limitStrictSel res)).d (3 - 1) 3 (by omega)
          (limitLocalHtp res 3 (3 - 1) (by omega) c) + c := by
  have e1 : limitLocalHtp res 4 3 rfl ((locCx (limitStrictSel res)).d 3 4 rfl c) = 0 := rfl
  have e2 : limitLocalHtp res 3 (3 - 1) (by omega) c = 0 := rfl
  rw [e1, e2, map_zero, zero_add, zero_add]
  obtain ⟨u, x⟩ := c
  refine Prod.ext (Subsingleton.elim (α := PUnit) _ _) ?_
  change limitE20 B h20 ((localDualityMap (limitPair res BG B hrec) (limitTrace k)
    (limitPair_htr res BG B hrec)).f 3 3 rfl (u, x)) = x
  exact limitE20_eq B h20 _ x fun v =>
    (limitLocal_apply res BG B hrec 3 u x v).trans (limitCupLP_apply_of_two B rfl _ _)

/-- The homotopy inverse is a right inverse on the nose, in degree two. Kind: PROVED. -/
theorem limitLocal_invHom_two (φ : (dualCx (limitRelaxed G res).D.U 3).X 2) :
    (localDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec)).f 2 2 rfl ((limitLocalInv res B h11 h20).f 2 2 rfl φ) = φ := by
  refine dualCx_ext fun v => ?_
  refine (limitLocal_apply res BG B hrec 2 0 (limitE11 B h11 φ) v).trans ?_
  refine (limitCupLP_apply_of_two B rfl _ _).trans ?_
  exact limitE11_right B h11 φ v

/-- The homotopy inverse is a right inverse on the nose, in degree three. Kind: PROVED. -/
theorem limitLocal_invHom_three (φ : (dualCx (limitRelaxed G res).D.U 3).X 3) :
    (localDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec)).f 3 3 rfl ((limitLocalInv res B h11 h20).f 3 3 rfl φ) = φ := by
  refine dualCx_ext fun v => ?_
  refine (limitLocal_apply res BG B hrec 3 0 (limitE20 B h20 φ) v).trans ?_
  refine (limitCupLP_apply_of_two B rfl _ _).trans ?_
  exact limitE20_right B h20 φ v

/-- The homotopy inverse is a right inverse on the nose. Kind: PROVED. -/
theorem limitLocal_invHom (n : ℤ) (φ : (dualCx (limitRelaxed G res).D.U 3).X n) :
    (localDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec)).f n n rfl ((limitLocalInv res B h11 h20).f n n rfl φ) = φ := by
  by_cases h2 : n = 2
  · subst h2
    exact limitLocal_invHom_two res B BG hrec h11 h20 φ
  by_cases h3 : n = 3
  · subst h3
    exact limitLocal_invHom_three res B BG hrec h11 h20 φ
  exact @Subsingleton.elim _ (limitDual_subsingleton res n h2 h3) _ _

/-- **The local duality map is a homotopy equivalence**
`Cone(U_str → L)[−1] ≃ Hom(U_rel, k)[−3]` (Nekovář 5.2.4 / 6.3.4 for the split model; tex
4834–4907: "Thus `U_str^⊥ = U_rel`"), when `b₁₁` and `b₂₀` have bijective adjoints. Kind:
definition. -/
def limitLocalHomotopyEquiv :
    HomotopyEquiv (locCx (limitStrictSel res)).toCC (dualCx (limitRelaxed G res).D.U 3).toCC where
  hom := GHom.toCC (localDualityMap (limitPair res BG B hrec) (limitTrace k)
    (limitPair_htr res BG B hrec))
  inv := GHom.toCC (limitLocalInv res B h11 h20)
  homotopyHomInvId := homotopyOfLinearIdentities _ _ (limitLocalHtp res) (by
    intro a
    erw [toCC_d_linear (locCx (limitStrictSel res)) a (a + 1) rfl,
      toCC_d_linear (locCx (limitStrictSel res)) (a - 1) a (by omega)]
    apply LinearMap.ext
    intro c
    by_cases h0 : a = 0
    · subst h0
      exact limitLocal_homInv_zero res B BG hrec h11 h20 c
    by_cases h1 : a = 1
    · subst h1
      exact limitLocal_homInv_one res B BG hrec h11 h20 c
    by_cases h2 : a = 2
    · subst h2
      exact limitLocal_homInv_two res B BG hrec h11 h20 c
    by_cases h3 : a = 3
    · subst h3
      exact limitLocal_homInv_three res B BG hrec h11 h20 c
    exact @Subsingleton.elim _ (limitLoc_subsingleton res a h0 h1 h2 h3) _ _)
  homotopyInvHomId := Homotopy.ofEq (by
    ext n φ
    exact limitLocal_invHom res B BG hrec h11 h20 n φ)

end Local

/-! ### The main theorem -/

/-- **Local duality for the split limit model** (Nekovář, *Selmer complexes*, 5.2.4 / 6.3.4, for
the split model `L = D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]` with zero differential; tex 4834–4907: "Thus
`U_str^⊥ = U_rel`"): if the local pairing has bijective adjoints in the bidegrees `(1, 1)` and
`(2, 0)`, the local duality map `Cone(U_str → L)[−1] → Hom(U_rel, k)[−3]` of the limit pairing data
is a quasi-isomorphism. Kind: PROVED. -/
theorem limitLocalDuality_quasiIso {k : Type} [Field k] {G : GCx k}
    (res : GHom G (splitLocalComplex k))
    (BG : GlobalTracePairing G) (B : SplitLocalPairing k) (hrec : LimitReciprocity res BG B)
    (h11 : Function.Bijective B.b11) (h20 : Function.Bijective B.b20) :
    QuasiIso (GHom.toCC (localDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec))) :=
  (limitLocalHomotopyEquiv res B BG hrec h11 h20).quasiIso_hom

/-- **The transported switch pairing has bijective adjoint** (tex 5037: `β(x, y) = ε e₂(x, J y)`,
`ε ∈ k^×`; tex 4860–4868): if `b₁₁(x, y) = −switchPairing ε σ J y x` with `ε, σ ≠ 0` and
`J² = 1`, then `x ↦ b₁₁(x, ·)` is bijective, by nondegeneracy of the switch pairing on the
four-dimensional space `F ⊕ S`. Kind: PROVED. -/
theorem switch_b11_bijective {k : Type} [Field k] (B : SplitLocalPairing k) (ε σ : k)
    (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (hb11 : ∀ x y, B.b11 x y = -(switchPairing ε σ J y x)) : Function.Bijective B.b11 := by
  have hnd := ZInQ.Manuscript.RC.Uniform.switchPairing_nondegenerate hε hσ hJ
  have hinj : Function.Injective B.b11 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine hnd.2 x fun y => ?_
    have := LinearMap.congr_fun hx y
    rw [hb11, LinearMap.zero_apply, neg_eq_zero] at this
    exact this
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := k) (V := Coords k)).symm).mp hinj

end ZInQ.Manuscript.RC.FibreDuality

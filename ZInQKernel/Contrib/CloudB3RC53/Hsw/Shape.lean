import ZInQKernel.Contrib.CloudB3RC53.Hsw.CupOneReverse

/-!
# RC53 `hsw`: the local-duality shape of the residue pairing

`hsw_of_residuePairing` (`Coordinates.lean`) needed the residue pairing `P` to have a fixed shape:
`F` and `S` isotropic, `σ`-symmetric, and `F × S` perfect. This file weakens that to intrinsic
local-duality properties of the cup product. The remaining properties are produced by a coordinate
change that fixes the finite plane.

## Results

* `exists_coord_switchPairing_shear`: `S` need not be isotropic. If `P|_S` is `σ`-split,
  `q(y, y') = h(y, y') + σ h(y', y)`, then after a shear `S → F` and an automorphism of `S`, `P` is
  the switch pairing.
* `split_of_two_ne_zero`: `P|_S` is `σ`-split when `2 ≠ 0` and `σ² = 1`.
* `split_of_alternating`: for `σ = 1` it is `σ`-split when `P|_S` is alternating. This holds in
  any characteristic, so it covers `𝔽₂`.
* `cross_isPerfPair_of_nondeg`: `F × S` is perfect when `P` is nondegenerate and `F` is isotropic.
* `exists_gClass`: when the strict condition vanishes in degree two, every coordinate vector is
  the class `eR[g t]` of a relaxed cocycle. So the descended `P` is determined by the residue form
  `resForm t u = tr((0, 0, −ι u) ∪ (0, t, 0))` on relaxed cocycles (`residuePairing_gClass`).
* `resForm_symm`: the residue form is `(−c)`-symmetric, from the cup-one datum. This gives
  `σ = −c`; for the Weil pairing, `c = −1` and `σ = 1`.
* `map_coordShear_finPlane`: the coordinate change `Φ = (id × A) ∘ shear` fixes the finite plane,
  so detection `F ≤ U` is unchanged.
* `hsw_of_localDuality`: `hsw` holds verbatim, with `σ = −c`, after a coordinate change `Φ` fixing
  `F`. It needs: the switch exactness data, a trace killing cone coboundaries, a strict condition
  vanishing in degree two, a cup-one datum, and the local-duality shape of the residue form. The
  shape means: `F` isotropic (unramified classes), nondegenerate (local Tate duality), and either
  `2 ≠ 0` or (`c = −1` and alternating on `S`).
* `genuine_switchCoordinates_of_localDuality`: the same for the genuine switch, with the genuine
  cup-one datum `genuineCupOne`.

## Remaining inputs

The three shape properties of the genuine residue form at the switch place are the content of
local duality:
* `F` isotropic: the cup of two unramified classes is a coboundary (`cd Ẑ = 1`). Proved in
  `ShapeUnramified.lean`, given the tie `hUrRep` of the finite plane to unramified classes.
* Nondegenerate: local Tate duality, i.e. `NekovarProp524` at `H¹`. This also needs the global
  trace restricted to the local summand at `v` to induce `H²(G_v, T) ≅ k`.
* Alternating on `S` in characteristic two: for the Weil pairing `x ∪ x` is a coboundary. Proved
  in `ShapeAlternating.lean` for polarized pairings.

Non-vacuity: `ShapeNonVacuity.lean`.

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k]

/-! ### Coordinates with a shear -/

/-- The shear `(x, y) ↦ (x + B y, y)` of `F ⊕ S`. -/
def shear (B : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    ((Fin 2 → k) × (Fin 2 → k)) →ₗ[k] ((Fin 2 → k) × (Fin 2 → k)) :=
  (LinearMap.fst k _ _ + B ∘ₗ LinearMap.snd k _ _).prod (LinearMap.snd k _ _)

@[simp] theorem shear_apply (B : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (a : (Fin 2 → k) × (Fin 2 → k)) :
    shear B a = (a.1 + B a.2, a.2) := rfl

/-- **Coordinates for a local-duality-shaped pairing, with a shear** (`PROVED`). Let `P` on
`F ⊕ S` have `F` isotropic, be `σ`-graded-symmetric, and have perfect cross pairing. Suppose its
restriction to `S` is `σ`-split, `P((0,y),(0,y')) = h(y,y') + σ h(y',y)`. Then after a shear
`B : S → F` and an automorphism `A` of `S`, `P` is the switch pairing. -/
theorem exists_coord_switchPairing_shear {ε : k} (hε : ε ≠ 0) (σ : k)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)))
    (hF : ∀ x x', P (x, 0) (x', 0) = 0) (hσ : ∀ a b, P b a = σ * P a b)
    (hperf : (P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)).IsPerfPair)
    (h : LinearMap.BilinForm k (Fin 2 → k))
    (hsplit : ∀ y y', P (0, y) (0, y') = h y y' + σ * h y' y) :
    ∃ (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) (B : (Fin 2 → k) →ₗ[k] (Fin 2 → k)), ∀ a b,
      P a b = switchPairing ε σ J ((shear B a).1, A (shear B a).2)
        ((shear B b).1, A (shear B b).2) := by
  set β' := P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _) with hβ'
  have hβ'apply : ∀ x y, β' x y = P (x, 0) (0, y) := fun _ _ => rfl
  -- `B₀ y` is the element of `F` with `β'(B₀ y, ·) = h(y, ·)`
  let e := LinearEquiv.ofBijective β' (LinearMap.IsPerfPair.bijective_left β')
  let B₀ : (Fin 2 → k) →ₗ[k] (Fin 2 → k) := e.symm.toLinearMap ∘ₗ h
  have hB₀ : ∀ y y', β' (B₀ y) y' = h y y' := by
    intro y y'
    have := congrArg (fun φ : Module.Dual k (Fin 2 → k) => φ y') (e.apply_symm_apply (h y))
    exact this
  -- the transformed form `P' = P ∘ (shear (−B₀) × shear (−B₀))`
  let P' := P.compl₁₂ (shear (-B₀)) (shear (-B₀))
  have hP'apply : ∀ a b, P' a b = P (a.1 - B₀ a.2, a.2) (b.1 - B₀ b.2, b.2) := by
    intro a b
    simp [P', shear_apply, sub_eq_add_neg]
  have split : ∀ x y : Fin 2 → k, ((x, y) : (Fin 2 → k) × (Fin 2 → k)) = (x, 0) + (0, y) := by
    intro x y; simp
  have hF' : ∀ x x', P' (x, 0) (x', 0) = 0 := by
    intro x x'; rw [hP'apply]; simpa using hF x x'
  have hS' : ∀ y y', P' (0, y) (0, y') = 0 := by
    intro y y'
    rw [hP'apply]
    simp only [zero_sub]
    rw [split (-B₀ y) y, split (-B₀ y') y']
    simp only [map_add, LinearMap.add_apply, hF, zero_add]
    rw [hσ (-B₀ y', 0) (0, y), ← hβ'apply, ← hβ'apply, hsplit]
    simp only [map_neg, LinearMap.neg_apply, hB₀]
    ring
  have hσ' : ∀ a b, P' b a = σ * P' a b := by
    intro a b; rw [hP'apply, hP'apply, hσ]
  have hcross : P'.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _) = β' := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    change P' (x, 0) (0, y) = P (x, 0) (0, y)
    rw [hP'apply]
    simp only [map_zero, sub_zero, zero_sub]
    rw [split (-B₀ y) y]
    simp only [map_add, hF, zero_add]
  obtain ⟨A, hA⟩ := exists_coord_switchPairing hε σ hJ2 P' hF' hS' hσ' (hcross ▸ hperf)
  refine ⟨A, B₀, fun a b => ?_⟩
  rw [← hA, hP'apply]
  simp

/-! ### The hypotheses of the shear theorem from intrinsic properties -/

/-- **The cross pairing is perfect** when `P` is nondegenerate and `F` is isotropic (`PROVED`;
`F` and `S` both have dimension two). -/
theorem cross_isPerfPair_of_nondeg (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)))
    (hF : ∀ x x', P (x, 0) (x', 0) = 0) (hnd : ∀ a, (∀ b, P a b = 0) → a = 0) :
    (P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)).IsPerfPair := by
  set β' := P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)
  have hinj : Function.Injective β' := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h0 : ((x, 0) : (Fin 2 → k) × (Fin 2 → k)) = 0 := by
      refine hnd _ fun b => ?_
      have hb : b = (b.1, 0) + (0, b.2) := by simp
      rw [hb, map_add, hF, zero_add]
      exact LinearMap.congr_fun hx b.2
    simpa using congrArg Prod.fst h0
  have hdim : Module.finrank k (Fin 2 → k) = Module.finrank k (Module.Dual k (Fin 2 → k)) :=
    (Subspace.dual_finrank_eq).symm
  have hsurj : Function.Surjective β' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  exact LinearMap.IsPerfPair.of_bijective β' ⟨hinj, hsurj⟩

/-- **`σ`-split when `2 ≠ 0`** (`PROVED`): take `h = q / 2`. -/
theorem split_of_two_ne_zero (h2 : (2 : k) ≠ 0) {σ : k} (hσ2 : σ * σ = 1)
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k))) (hσ : ∀ a b, P b a = σ * P a b) :
    ∃ h : LinearMap.BilinForm k (Fin 2 → k),
      ∀ y y', P (0, y) (0, y') = h y y' + σ * h y' y := by
  refine ⟨(2 : k)⁻¹ • P.compl₁₂ (LinearMap.inr k _ _) (LinearMap.inr k _ _), fun y y' => ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearMap.inr_apply, smul_eq_mul]
  rw [hσ (0, y) (0, y')]
  field_simp
  linear_combination (-(P (0, y) (0, y'))) * hσ2

/-- **`σ`-split for a symmetric form that is alternating on `S`** (`PROVED`, any characteristic):
with `σ = 1` and `P((0,y),(0,y)) = 0`, take `h(y, y') = q(e₀, e₁) y₀ y'₁`. -/
theorem split_of_alternating (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)))
    (hσ : ∀ a b, P b a = P a b) (halt : ∀ y, P (0, y) (0, y) = 0) :
    ∃ h : LinearMap.BilinForm k (Fin 2 → k),
      ∀ y y', P (0, y) (0, y') = h y y' + 1 * h y' y := by
  set q := P.compl₁₂ (LinearMap.inr k (Fin 2 → k) (Fin 2 → k))
    (LinearMap.inr k (Fin 2 → k) (Fin 2 → k)) with hq
  have hqa : ∀ y y', P (0, y) (0, y') = q y y' := fun _ _ => rfl
  let e : Fin 2 → (Fin 2 → k) := fun i => Pi.single i 1
  let c := q (e 0) (e 1)
  refine ⟨c • (LinearMap.mul k k).compl₁₂ (LinearMap.proj 0) (LinearMap.proj 1), fun y y' => ?_⟩
  have hy : ∀ z : Fin 2 → k, z = z 0 • e 0 + z 1 • e 1 := by
    intro z; ext i; fin_cases i <;> simp [e]
  have h00 : q (e 0) (e 0) = 0 := halt _
  have h11 : q (e 1) (e 1) = 0 := halt _
  have h10 : q (e 1) (e 0) = c := by
    change P (0, e 1) (0, e 0) = P (0, e 0) (0, e 1)
    exact hσ _ _
  rw [hqa, hy y, hy y']
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h00,
    h11, h10, LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.proj_apply]
  simp [e, c]
  ring

/-! ### The residue form on cocycles -/

section Residue

variable (R : QuasiRelaxedLocalization k) (Ustr : GCx k) (f : GHom Ustr R.D.U)
  (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)

/-- **The residue form** on relaxed `1`-cocycles: `tr((0, 0, −ι u) ∪ (0, t, 0))`, the left-hand
side of `hsw` with `s = 0`. -/
def resForm (t u : R.D.U.X 1) : k :=
  tr (selCupFun Q 2 1 3 rfl ((0 : R.D.G.X 2), (0 : Ustr.X 2), -(R.D.ι.f 1 (2 - 1) (by omega) u))
    ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1))))

/-- The class `eR[g t]` of a relaxed `1`-cocycle. -/
def gClass (t : R.D.U.X 1) (ht : R.D.U.d 1 2 rfl t = 0) : (Fin 2 → k) × (Fin 2 → k) :=
  R.eR (cls1 R.Wrel ⟨R.gR.f 1 1 rfl t, LinearMap.mem_ker.2
    ((R.gR.comm 1 2 1 2 rfl rfl rfl rfl t).symm.trans (by rw [ht, map_zero]))⟩)

/-- **Every coordinate vector is the class of a relaxed cocycle** when the strict condition
vanishes in degree two (`PROVED`). -/
theorem exists_gClass (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (h2 : ∀ x : Ustr.X 2, x = 0) (a : (Fin 2 → k) × (Fin 2 → k)) :
    ∃ (t : R.D.U.X 1) (ht : R.D.U.d 1 2 rfl t = 0), gClass R t ht = a := by
  obtain ⟨cw, hcw⟩ := clsAt_surjective R.Wrel 1 2 rfl (R.eR.symm a)
  obtain ⟨u, hu⟩ := hg 1 cw.1
  have hdu : R.gR.f 2 2 rfl (R.D.U.d 1 2 rfl u) = 0 := by
    rw [R.gR.comm 1 2 1 2 rfl rfl rfl rfl u, hu]
    exact cw.2
  obtain ⟨s, hs⟩ := hex 2 _ hdu
  have ht : R.D.U.d 1 2 rfl u = 0 := by rw [← hs, h2 s, map_zero]
  refine ⟨u, ht, ?_⟩
  have e : cls1 R.Wrel ⟨R.gR.f 1 1 rfl u, LinearMap.mem_ker.2
      ((R.gR.comm 1 2 1 2 rfl rfl rfl rfl u).symm.trans (by rw [ht, map_zero]))⟩ =
      cls1 R.Wrel cw := congrArg (cls1 R.Wrel) (Subtype.ext hu)
  unfold gClass
  rw [e, cls1_eq_clsAt, hcw, LinearEquiv.apply_symm_apply]

/-- The residue pairing evaluated on classes of cocycles is the residue form (`PROVED`). -/
theorem residuePairing_gClass {P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k))}
    (hP : ResiduePairing R Ustr f Q tr P) (t u : R.D.U.X 1) (ht : R.D.U.d 1 2 rfl t = 0)
    (hu : R.D.U.d 1 2 rfl u = 0) :
    P (gClass R t ht) (gClass R u hu) = resForm R Ustr f Q tr t u :=
  (hP t u 0 ht (by rw [hu, map_zero]) _ _ rfl rfl).symm

/-- **The residue form is `(−c)`-symmetric** (`PROVED`), from the cup-one datum: for relaxed
cocycles `t, u`, `resForm t u = −c • resForm u t`. -/
theorem resForm_symm (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) {c : k}
    (Cd : CupOneDatum R.D Ustr f Q c) (t u : R.D.U.X 1) (ht : R.D.U.d 1 2 rfl t = 0)
    (hu : R.D.U.d 1 2 rfl u = 0) :
    resForm R Ustr f Q tr t u = -c * resForm R Ustr f Q tr u t := by
  have l1 := lhs_eq R.D Ustr f Q tr t u 0
  have l2 := lhs_eq R.D Ustr f Q tr u t 0
  unfold resForm
  rw [l1, l2]
  have h0 : ∀ v : R.D.U.X 1, Q.hU 2 1 2 rfl (0 : Ustr.X 2) v = 0 := fun v =>
    LinearMap.map_zero₂ _ _
  rw [h0, h0, zero_sub, zero_sub, map_neg, map_neg, map_neg, map_neg]
  have hbt : R.D.L.d 1 2 rfl (R.D.ι.f 1 1 rfl t) = 0 := by
    rw [← R.D.ι.comm 1 2 1 2 rfl rfl rfl rfl, ht, map_zero]
  have hau : R.D.L.d 1 2 rfl (R.D.ι.f 1 1 rfl u) = 0 := by
    rw [← R.D.ι.comm 1 2 1 2 rfl rfl rfl rfl, hu, map_zero]
  have hform := Cd.formula (R.D.ι.f 1 1 rfl u) (R.D.ι.f 1 1 rfl t) hbt
  rw [hau, map_zero, LinearMap.zero_apply, add_zero] at hform
  have hz := tr_locT_d Q tr htr (Cd.C11 (R.D.ι.f 1 1 rfl u) (R.D.ι.f 1 1 rfl t))
  rw [hform, map_sub, map_neg, map_smul, map_sub, map_neg, map_smul, smul_eq_mul] at hz
  linear_combination hz

end Residue

/-! ### `hsw` from the local-duality shape -/

/-- The shear as a linear automorphism of `F ⊕ S`. -/
def shearEquiv (B : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)) :=
  { shear B with
    invFun := shear (-B)
    left_inv := fun a => by simp
    right_inv := fun a => by simp }

/-- The coordinate change `Φ = (id × A) ∘ shear B`. -/
def coordShear (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) (B : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)) :=
  (shearEquiv B).trans ((LinearEquiv.refl k (Fin 2 → k)).prodCongr A)

theorem coordShear_apply (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) (B : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (a : (Fin 2 → k) × (Fin 2 → k)) : coordShear A B a = ((shear B a).1, A (shear B a).2) := rfl

/-- `Φ = (id × A) ∘ shear B` maps the finite plane onto itself, so detection `F ≤ U` is unchanged
(`PROVED`). -/
theorem map_coordShear_finPlane (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k))
    (B : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    (finPlane k (Fin 2 → k) (Fin 2 → k)).map (coordShear A B).toLinearMap =
      finPlane k (Fin 2 → k) (Fin 2 → k) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, hb, he⟩
    have hb' : b = 0 := mem_finPlane.1 hb
    rw [mem_finPlane, ← he, hb']
    simp [coordShear_apply]
  · intro hy
    rw [mem_finPlane] at hy
    refine ⟨(x, 0), mem_finPlane.2 rfl, ?_⟩
    simp [coordShear_apply, show y = 0 from hy]

/-- A relaxed localization with coordinates changed by a linear automorphism `Φ` of `F ⊕ S`. -/
abbrev reCoordGen (R : QuasiRelaxedLocalization k)
    (Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k))) :
    QuasiRelaxedLocalization k :=
  { R with eR := R.eR.trans Φ }

/-- **`hsw` from the local-duality shape** (tex L2790–2818, L2816–2818; `PROVED` from the inputs).
The setting is a relaxed localization with the switch exactness data, a trace killing cone
coboundaries, a strict condition vanishing in degree two, and a cup-one datum with sign `c` (for
the genuine data: `genuineCupOne`). Assume the **local-duality shape** of the residue form on
relaxed cocycles:
* the classes in the finite plane `F` are mutually orthogonal (`F` isotropic: the unramified
  classes);
* the form is nondegenerate (local Tate duality);
* either `2 ≠ 0` and `c² = 1`, or `c = −1` and the form vanishes on the diagonal of `S`
  (alternating; characteristic two).

Then after a coordinate change `Φ` fixing the finite plane, `hsw` holds verbatim with `σ = −c`. -/
theorem hsw_of_localDuality (R : QuasiRelaxedLocalization k) (Ustr : GCx k) (f : GHom Ustr R.D.U)
    (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) (h2 : ∀ x : Ustr.X 2, x = 0) {c : k}
    (Cd : CupOneDatum R.D Ustr f Q c) {ε : k} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) k}
    (hJ2 : J * J = 1)
    (hFiso : ∀ t u (ht : R.D.U.d 1 2 rfl t = 0) (hu : R.D.U.d 1 2 rfl u = 0),
      gClass R t ht ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      gClass R u hu ∈ finPlane k (Fin 2 → k) (Fin 2 → k) → resForm R Ustr f Q tr t u = 0)
    (hnd : ∀ t (ht : R.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : R.D.U.d 1 2 rfl u = 0), resForm R Ustr f Q tr t u = 0) → gClass R t ht = 0)
    (hchar : ((2 : k) ≠ 0 ∧ c * c = 1) ∨
      (c = -1 ∧ ∀ t (ht : R.D.U.d 1 2 rfl t = 0),
        gClass R t ht ∈ singPlane k (Fin 2 → k) (Fin 2 → k) → resForm R Ustr f Q tr t t = 0)) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
        (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
        (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
        tr (selCupFun Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
            ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
          switchPairing ε (-c) J ((reCoordGen R Φ).eR (cls1 R.Wrel ct))
            ((reCoordGen R Φ).eR (cls1 R.Wrel cu)) := by
  obtain ⟨P, hP⟩ := exists_residuePairing R Ustr f Q tr hfg hf hg hex htr
    (strictOrth_of_reverseIsotropy R.D Ustr f Q tr htr
      (reverseIsotropy_of_cupOne R.D Ustr f Q c Cd h2))
  have cls := exists_gClass R Ustr f hg hex h2
  have hσ : ∀ a b, P b a = -c * P a b := by
    intro a b
    obtain ⟨t, ht, rfl⟩ := cls a
    obtain ⟨u, hu, rfl⟩ := cls b
    rw [residuePairing_gClass R Ustr f Q tr hP u t hu ht,
      residuePairing_gClass R Ustr f Q tr hP t u ht hu, resForm_symm R Ustr f Q tr htr Cd u t hu ht]
  have hF : ∀ x x', P (x, 0) (x', 0) = 0 := by
    intro x x'
    obtain ⟨t, ht, hte⟩ := cls (x, 0)
    obtain ⟨u, hu, hue⟩ := cls (x', 0)
    rw [← hte, ← hue, residuePairing_gClass R Ustr f Q tr hP t u ht hu]
    exact hFiso t u ht hu (hte ▸ mem_finPlane.2 rfl) (hue ▸ mem_finPlane.2 rfl)
  have hnd' : ∀ a, (∀ b, P a b = 0) → a = 0 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := cls a
    exact hnd t ht fun u hu => by
      rw [← residuePairing_gClass R Ustr f Q tr hP t u ht hu]; exact ha _
  have hperf := cross_isPerfPair_of_nondeg P hF hnd'
  have hsplit : ∃ h : LinearMap.BilinForm k (Fin 2 → k),
      ∀ y y', P (0, y) (0, y') = h y y' + -c * h y' y := by
    rcases hchar with ⟨h2k, hc2⟩ | ⟨hc, halt⟩
    · exact split_of_two_ne_zero h2k (by linear_combination hc2) P hσ
    · subst hc
      have hsym : ∀ a b, P b a = P a b := fun a b => by rw [hσ]; ring
      have halt' : ∀ y, P (0, y) (0, y) = 0 := by
        intro y
        obtain ⟨t, ht, hte⟩ := cls (0, y)
        rw [← hte, residuePairing_gClass R Ustr f Q tr hP t t ht ht]
        exact halt t ht (hte ▸ mem_singPlane.2 rfl)
      obtain ⟨h, hh⟩ := split_of_alternating P hsym halt'
      exact ⟨h, fun y y' => by rw [hh]; ring⟩
  obtain ⟨h, hh⟩ := hsplit
  obtain ⟨A, B, hAB⟩ := exists_coord_switchPairing_shear hε (-c) hJ2 P hF hσ hperf h hh
  refine ⟨coordShear A B, map_coordShear_finPlane A B,
    fun t u s ht hu ct cu hct hcu => (hP t u s ht hu ct cu hct hcu).trans (hAB _ _)⟩

/-! ### The genuine switch -/

section Genuine

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- **`SwitchCoordinates` for the genuine switch from the local-duality shape** (tex L2816–2818;
`PROVED` from the inputs). Let `β` be a `c`-symmetric equivariant self-pairing, `I` any isotropy
data, and suppose the strict condition complexes vanish in degree two. Suppose also that the
residue form has the local-duality shape: finite plane isotropic, nondegenerate, and the
characteristic condition. Then for coordinates `eR` changed by some `Φ` fixing the finite plane,
the genuine switch satisfies `SwitchCoordinates` with `σ = −c`. -/
theorem genuine_switchCoordinates_of_localDuality (X : GenuineSwitch K S k M)
    (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (c : k) (hc : ∀ x y, β x y = c • β y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (X.US v).X 2), x = 0) {ε : k} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (hFiso : ∀ t u (ht : X.toQuasi.D.U.d 1 2 rfl t = 0) (hu : X.toQuasi.D.U.d 1 2 rfl u = 0),
      gClass X.toQuasi t ht ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      gClass X.toQuasi u hu ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t u = 0)
    (hnd : ∀ t (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : X.toQuasi.D.U.d 1 2 rfl u = 0),
        resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t u =
          0) → gClass X.toQuasi t ht = 0)
    (hchar : ((2 : k) ≠ 0 ∧ c * c = 1) ∨
      (c = -1 ∧ ∀ t (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
        gClass X.toQuasi t ht ∈ singPlane k (Fin 2 → k) (Fin 2 → k) →
        resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t t =
          0)) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ({ X with eR := X.eR.trans Φ } : GenuineSwitch K S k M).SwitchCoordinates
        (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr ε (-c) J := by
  obtain ⟨Φ, hΦ, hsw⟩ := hsw_of_localDuality X.toQuasi (piCx X.US) (piMap X.φ) _ tr X.hfg
    X.φ_inj X.g_surj X.ex htr (fun x => funext fun v => hUS2 v (x v))
    (genuineCupOne X β hβ c hc I) hε hJ2 hFiso hnd hchar
  exact ⟨Φ, hΦ, hsw⟩

end Genuine

end ZInQ.Contrib.CloudB3RC53.Hsw

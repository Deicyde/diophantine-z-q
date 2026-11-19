import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericSides

/-!
# RC53 SwitchInputs: the switch families and coordinates over an arbitrary coefficient field

Manuscript `diophantine_zq.tex`, tex L5027–5086. Field-generic restatement of
`DerivativeCoords.lean` (whose genuine instances are specialised to the residue field `𝔽₂` and do
not apply at the height-one primes `𝔭 ≠ (2)` where switching runs,
`isEmpty_ringHom_zmod_two_heightOne`): over an arbitrary field `k`, the strict, side and relaxed
derivative subcomplexes of the genuine local complexes `C^•_cont(G_v, M_v)` over `k`
(`relSubK`, `strSubK`, `sideSubK`, `switchFamK`), the coordinates `eRAtK : H¹(W_rel) ≃ k² × k²` from
the named tame-coordinate input `TameCoordinatesTrivialK`, the plane equation `range_H1i_eRAtK`, the
finite/singular plane identifications (`finite_side_iffK`, `singular_side_iffK`), and the quasi
switch sides (`finQuasiSideK`, `singQuasiSideK`, `switchQuasiSideK`) over the side-independent
relaxed localization `relLocK`. The proofs are those of `DerivativeCoords.lean` with `ZMod 2`
replaced by `k`; they never use the characteristic. All PROVED (from `TameCoordinatesTrivialK`,
GLUE).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.GenuineInst ZInQ.Manuscript.RC.Uniform ValuativeRel

section Family

variable {k : Type} [Field k]

variable {ι : Type} [DecidableEq ι]
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module (k) (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) (k) (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, ContinuousAdd (Mv v)]
  [∀ v, ContinuousConstSMul k (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]

variable (k Gv Mv) in
/-- The genuine local complex `C^•_cont(G_v, M_v)` at `v` (extended by zero). -/
abbrev locCxK (v : ι) : GCx (k) := natCx (contCochains (k) (Gv v) (Mv v))

variable (k Gv Mv) in
/-- **The relaxed derivative condition** `τ_{≤1} C^• = [C⁰ → Z¹]` at `v` (tex L5060–5061). -/
def relSubK (v : ι) : SubFam (locCxK k Gv Mv v) :=
  degSub _ ⊤ (Z1K k (Gv v) (Mv v)) (fun x _ => (relaxedDK k (Gv v) (Mv v) x).2) (fun _ hx => hx)

variable (k Gv Mv) in
/-- **The strict derivative condition** `τ_{≤0} C^• = [Z⁰ → 0]` at `v` (tex L5060–5061). -/
def strSubK (v : ι) : SubFam (locCxK k Gv Mv v) :=
  degSub _ (Z0K k (Gv v) (Mv v)) ⊥ (fun _ hx => (Submodule.mem_bot _).mpr hx)
    (fun x hx => by rw [(Submodule.mem_bot _).mp hx, map_zero])

/-- **The side condition** `[A → B] ⊆ [C⁰ → Z¹]` of a `SideCond` at `v` (tex L5060–5082). -/
def sideSubK (v : ι) (c : SideCondK k (Gv v) (Mv v)) : SubFam (locCxK k Gv Mv v) :=
  degSub _ c.AF (c.BF.map (Z1K k (Gv v) (Mv v)).subtype)
    (fun x hx => ⟨relaxedDK k (Gv v) (Mv v) x, c.hd hx, rfl⟩)
    (fun _ hx => by obtain ⟨z, _, rfl⟩ := hx; exact z.2)

variable (k Gv Mv) in
/-- The strict conditions of the switch at `q`: `[Z⁰ → 0]` at `q`, the old conditions elsewhere. -/
def switchStrK (q : ι) (old : ∀ v, SubFam (locCxK k Gv Mv v)) (v : ι) : SubFam (locCxK k Gv Mv v) :=
  if v = q then strSubK k Gv Mv v else old v

variable (k Gv Mv) in
/-- The relaxed conditions of the switch at `q`: `[C⁰ → Z¹]` at `q`, the old conditions
elsewhere. -/
def switchRelK (q : ι) (old : ∀ v, SubFam (locCxK k Gv Mv v)) (v : ι) : SubFam (locCxK k Gv Mv v) :=
  if v = q then relSubK k Gv Mv v else old v

variable (k Gv Mv) in
/-- **The switch family** at the place `q` (tex L5060–5082): the strict, side (`sideOfSetK k (Mv q)
(T q)`:
the finite side for `T q = I`, the singular side for `T q = {φ}`) and relaxed derivative conditions
at `q`, and the old conditions `old v` elsewhere. -/
def switchFamK (q : ι) (old : ∀ v, SubFam (locCxK k Gv Mv v)) (T : ∀ v, Set (Gv v)) :
    DerivFamily (locCxK k Gv Mv) where
  str := switchStrK k Gv Mv q old
  side v := if v = q then sideSubK v (sideOfSetK k (Mv v) (T v)) else old v
  rel := switchRelK k Gv Mv q old
  hss v n := by
    dsimp only [switchStrK]
    split_ifs
    · exact degS_mono _ (sideOfSetK k (Mv v) (T v)).hZ0 bot_le n
    · exact le_rfl
  hsr v n := by
    dsimp only [switchRelK]
    split_ifs
    · exact degS_mono _ le_top (by
        rintro _ ⟨z, _, rfl⟩
        exact z.2) n
    · exact le_rfl
  hcobS v x hx hdx := by
    dsimp only [switchRelK] at hx
    split_ifs at hx hdx ⊢ with h
    · obtain ⟨z, hz, hzx⟩ := hdx
      have e : relaxedDK k (Gv v) (Mv v) x = z := Subtype.ext hzx.symm
      exact (sideOfSetK k (Mv v) (T v)).hcob x (e ▸ hz)
    · exact hx
  hcobStr v x hx hdx := by
    dsimp only [switchStrK] at hdx ⊢
    split_ifs at hx hdx ⊢ with h
    · exact (Submodule.mem_bot _).mp hdx
    · exact hx

variable (q : ι) (old : ∀ v, SubFam (locCxK k Gv Mv v)) (T : ∀ v, Set (Gv v))

theorem switchStr_qK : switchStrK k Gv Mv q old q = strSubK k Gv Mv q := by simp [switchStrK]

theorem switchRel_qK : switchRelK k Gv Mv q old q = relSubK k Gv Mv q := by simp [switchRelK]

theorem switchStr_neK {v : ι} (h : v ≠ q) : switchStrK k Gv Mv q old v = old v := by
  simp [switchStrK, h]

theorem switchRel_neK {v : ι} (h : v ≠ q) : switchRelK k Gv Mv q old v = old v := by
  simp [switchRelK, h]

/-- Strict below relaxed for the switch conditions (independent of the side sets). PROVED. -/
theorem switch_hsrK (v : ι) (n : ℤ) :
    (switchStrK k Gv Mv q old v).S n ≤ (switchRelK k Gv Mv q old v).S n := by
  by_cases h : v = q
  · subst h
    rw [switchStr_qK, switchRel_qK]
    exact degS_mono _ le_top bot_le n
  · rw [switchStr_neK q old h, switchRel_neK q old h]

theorem switchFam_side_qK (n : ℤ) :
    ((switchFamK k Gv Mv q old T).side q).S n = (sideSubK q (sideOfSetK k (Mv q) (T q))).S n := by
  simp [switchFamK]

end Family

section Coords

variable {k : Type} [Field k]

variable {ι : Type}
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module (k) (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) (k) (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, ContinuousAdd (Mv v)]
  [∀ v, ContinuousConstSMul k (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]

/-- **Relaxed and strict conditions switched at the place `q`**: at `q` the strict condition is
`[Z⁰ → 0]` (degree `1`: `0`), the relaxed one `[C⁰ → Z¹]`; away from `q` relaxed and strict agree in
degree `1`. -/
structure RelAtK (str rel : ∀ v, SubFam (locCxK k Gv Mv v)) (q : ι) : Prop where
  str1 : ∀ x : (locCxK k Gv Mv q).X 1, x ∈ (str q).S 1 → x = 0
  rel0 : ∀ x : (locCxK k Gv Mv q).X 0, x ∈ (rel q).S 0
  rel1 : ∀ x : (locCxK k Gv Mv q).X 1, x ∈ (rel q).S 1 ↔ x ∈ Z1K k (Gv q) (Mv q)
  rel_ne : ∀ v, v ≠ q → ∀ x : (locCxK k Gv Mv v).X 1, x ∈ (rel v).S 1 → x ∈ (str v).S 1

/-- **A family switched at the place `q` with side condition `c`**: its strict and relaxed
conditions are switched at `q` and the side condition at `q` is `[A → B]`. -/
structure SwitchedAtK (F : DerivFamily (locCxK k Gv Mv)) (q : ι) (c : SideCondK k (Gv q) (Mv q)) :
    Prop where
  rel : RelAtK F.str F.rel q
  side1 : ∀ x : (locCxK k Gv Mv q).X 1, x ∈ (F.side q).S 1 ↔
    ∃ z ∈ c.BF, (z : (contCochains (k) (Gv q) (Mv q)).X 1) = x

/-- **The switch conditions are switched at `q`**. PROVED. -/
theorem switch_relAtK [DecidableEq ι] (q : ι) (old : ∀ v, SubFam (locCxK k Gv Mv v)) :
    RelAtK (switchStrK k Gv Mv q old) (switchRelK k Gv Mv q old) q where
  str1 x hx := by
    rw [switchStr_qK] at hx
    exact (Submodule.mem_bot _).mp hx
  rel0 x := by
    rw [switchRel_qK]
    trivial
  rel1 x := by
    rw [switchRel_qK]
    exact Iff.rfl
  rel_ne v h x hx := by
    rw [switchRel_neK q old h] at hx
    rw [switchStr_neK q old h]
    exact hx

/-- **The switch family is switched at `q`** with the side condition `sideOfSetK k (Mv q) (T q)`.
PROVED. -/
theorem switchFam_switchedAtK [DecidableEq ι] (q : ι) (old : ∀ v, SubFam (locCxK k Gv Mv v))
    (T : ∀ v, Set (Gv v)) :
    SwitchedAtK (switchFamK k Gv Mv q old T) q (sideOfSetK k (Mv q) (T q)) where
  rel := switch_relAtK q old
  side1 x := by
    rw [switchFam_side_qK]
    exact Iff.rfl

/-- Strict below relaxed in a derivative family. -/
theorem derivHsrK (F : DerivFamily (locCxK k Gv Mv)) (v : ι) (n : ℤ) :
    (F.str v).S n ≤ (F.rel v).S n :=
  (F.hss v n).trans (F.hsr v n)

variable {str rel : ∀ v, SubFam (locCxK k Gv Mv v)} (hsr : ∀ v n, (str v).S n ≤ (rel v).S n)
  {q : ι} (hR : RelAtK str rel q) (φ σ : Gv q) (eM : Mv q ≃ₗ[k] (Fin 2 → k))

variable (rel) in
/-- The relaxed local-condition complex `∏_v U_v^{rel}`. -/
abbrev relUK : GCx (k) := piCx fun v => (rel v).cx

/-- `strict → relaxed`. -/
def strRelK : GHom (piCx fun v => (str v).cx) (relUK rel) :=
  piMap fun v => SubFam.inclLe (hsr v)

/-- `W_rel = relaxed / strict` (for a derivative family `F`, definitionally `F.Wrel`). -/
abbrev relWK : GCx (k) := quotCx (strRelK hsr)

variable (q) in
/-- The coordinates `x ↦ (eM x(φ), eM x(σ))` of a `1`-cochain at `q`. -/
def coordAtK : (contCochains (k) (Gv q) (Mv q)).X 1 →ₗ[k]
    (Fin 2 → k) × (Fin 2 → k) :=
  (eM.toLinearMap ∘ₗ ev1LK φ).prod (eM.toLinearMap ∘ₗ ev1LK σ)

theorem coordAt_applyK (x : (contCochains (k) (Gv q) (Mv q)).X 1) :
    coordAtK q φ σ eM x = (eM (ev1K x φ), eM (ev1K x σ)) :=
  rfl

theorem coordAt_relaxedDK (hφ : ∀ m : Mv q, φ • m = m) (hσ : ∀ m : Mv q, σ • m = m)
    (a : (contCochains (k) (Gv q) (Mv q)).X 0) :
    coordAtK q φ σ eM ((relaxedDK k (Gv q) (Mv q) a : Z1K k (Gv q) (Mv q)) :
      (contCochains (k) (Gv q) (Mv q)).X 1) = 0 := by
  have h := coordLK_relaxedD φ σ hφ hσ a
  have h1 : ev1K ((relaxedDK k (Gv q) (Mv q) a : Z1K k (Gv q) (Mv q)) :
      (contCochains (k) (Gv q) (Mv q)).X 1) φ = 0 := congrArg Prod.fst h
  have h2 : ev1K ((relaxedDK k (Gv q) (Mv q) a : Z1K k (Gv q) (Mv q)) :
      (contCochains (k) (Gv q) (Mv q)).X 1) σ = 0 := congrArg Prod.snd h
  rw [coordAt_applyK, h1, h2, map_zero]
  rfl

theorem coordAt_mkK (T : TameCoordinatesTrivialK k (Mv q) I φ σ) (z : Z1K k (Gv q) (Mv q)) :
    coordAtK q φ σ eM (z : (contCochains (k) (Gv q) (Mv q)).X 1) =
      coordEquivK T eM (Submodule.Quotient.mk z) :=
  rfl

variable (rel q) in
/-- The coordinates read at `q` on the relaxed condition in degree `1`. -/
def psiRawK : (relUK rel).X 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  coordAtK q φ σ eM ∘ₗ ((rel q).S 1).subtype ∘ₗ
    LinearMap.proj (R := k) (φ := fun v => ((rel v).S 1 : Type)) q

/-- The coordinates on `W_rel¹ = U_rel¹ / U_str¹` (they kill the strict condition at `q`). -/
def psi0K : (relWK hsr).X 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  (quotSub (strRelK hsr) 1).liftQ (psiRawK rel q φ σ eM) (by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change coordAtK q φ σ eM ((x q).1 : (locCxK k Gv Mv q).X 1) = 0
    rw [hR.str1 _ (x q).2]
    exact (coordAtK q φ σ eM).map_zero)

theorem psi0_dK (hφ : ∀ m : Mv q, φ • m = m) (hσ : ∀ m : Mv q, σ • m = m) (y : (relWK hsr).X 0) :
    psi0K hsr hR φ σ eM ((relWK hsr).d 0 1 rfl y) = 0 := by
  obtain ⟨r, rfl⟩ := (quotSub (strRelK hsr) 0).mkQ_surjective y
  exact coordAt_relaxedDK φ σ eM hφ hσ ((r q).1 : (locCxK k Gv Mv q).X 0)

/-- **The coordinate map** `C : H¹(W_rel) → k² × k²`, `[x] ↦ (eM x_q(φ), eM x_q(σ))`. -/
def coordCK (hφ : ∀ m : Mv q, φ • m = m) (hσ : ∀ m : Mv q, σ • m = m) :
    (relWK hsr).toCC.homology 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  descH1 (relWK hsr) (psi0K hsr hR φ σ eM) (psi0_dK hsr hR φ σ eM hφ hσ)

variable [DecidableEq ι]

/-- A `1`-cocycle at `q` as an element of the relaxed condition at `q`. -/
def relInK : Z1K k (Gv q) (Mv q) →ₗ[k] ((rel q).S 1) where
  toFun z := ⟨z.1, (hR.rel1 _).2 z.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A `1`-cocycle at `q` as a relaxed `1`-cochain supported at `q`. -/
def sAtK : Z1K k (Gv q) (Mv q) →ₗ[k] (relUK rel).X 1 :=
  LinearMap.single (k) (fun v => ((rel v).S 1 : Type)) q ∘ₗ relInK hR

/-- Its class in `W_rel¹` is a cocycle. -/
def zAtK : Z1K k (Gv q) (Mv q) →ₗ[k] LinearMap.ker ((relWK hsr).d 1 2 rfl) :=
  ((quotSub (strRelK hsr) 1).mkQ ∘ₗ sAtK hR).codRestrict _ fun z => by
    change Submodule.Quotient.mk ((relUK rel).d 1 2 rfl (Pi.single q (relInK hR z))) =
      (0 : (relWK hsr).X 2)
    have hz : (rel q).cx.d 1 2 rfl (relInK hR z) = 0 := Subtype.ext (LinearMap.mem_ker.mp z.2)
    exact (congrArg Submodule.Quotient.mk
      ((piCx_d_single (fun v => (rel v).cx) 1 2 rfl q (relInK hR z)).trans
        ((congrArg (fun y => (Pi.single q y : ∀ v, ((rel v).cx).X 2)) hz).trans
          (Pi.single_zero q)))).trans (Submodule.Quotient.mk_zero _)

/-- **The comparison map** `Z¹(G_q, M_q) / d⁰C⁰ → H¹(W_rel)`, `[z] ↦ [z at q]`. -/
def phiAtK : (H1WrelK k (Gv q) (Mv q)) →ₗ[k] (relWK hsr).toCC.homology 1 :=
  (LinearMap.range (relaxedDK k (Gv q) (Mv q))).liftQ (cls1 (relWK hsr) ∘ₗ zAtK hsr hR) (by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    have ha : (a : (locCxK k Gv Mv q).X 0) ∈ (rel q).S 0 := hR.rel0 a
    have e : zAtK hsr hR (relaxedDK k (Gv q) (Mv q) a) =
        ⟨(relWK hsr).d 0 1 rfl (Submodule.Quotient.mk (Pi.single q (⟨a, ha⟩ : (rel q).S 0))),
          LinearMap.mem_ker.mpr ((relWK hsr).d_d 0 1 2 rfl rfl _)⟩ := Subtype.ext
      (congrArg Submodule.Quotient.mk
        (piCx_d_single (fun v => (rel v).cx) 0 1 rfl q (⟨a, ha⟩ : (rel q).S 0)).symm)
    change cls1 (relWK hsr) (zAtK hsr hR (relaxedDK k (Gv q) (Mv q) a)) = 0
    rw [e]
    exact cls1_boundary _ _ _)

theorem coordC_phiAtK (hφ : ∀ m : Mv q, φ • m = m) (hσ : ∀ m : Mv q, σ • m = m)
    (z : Z1K k (Gv q) (Mv q)) :
    coordCK hsr hR φ σ eM hφ hσ (phiAtK hsr hR (Submodule.Quotient.mk z)) =
      coordAtK q φ σ eM (z : (contCochains (k) (Gv q) (Mv q)).X 1) := by
  change descH1 (relWK hsr) _ _ (cls1 (relWK hsr) (zAtK hsr hR z)) = _
  rw [descH1_cls1]
  have e : (Pi.single q (relInK hR z) : ∀ v, ((rel v).S 1 : Type)) q = relInK hR z :=
    Pi.single_eq_same _ _
  exact congrArg
    (fun w : ((rel q).S 1 : Type) => coordAtK q φ σ eM (w.1 : (locCxK k Gv Mv q).X 1)) e

/-- **Every class of `H¹(W_rel)` is supported at `q`**: `phiAtK` is surjective. PROVED. -/
theorem phiAt_surjectiveK : Function.Surjective (phiAtK hsr hR) := by
  intro w
  obtain ⟨⟨y, hy⟩, rfl⟩ := clsAt_surjective (relWK hsr) 1 2 rfl w
  obtain ⟨r, rfl⟩ := (quotSub (strRelK hsr) 1).mkQ_surjective y
  have hr : ((r q).1 : (contCochains (k) (Gv q) (Mv q)).X 1) ∈ Z1K k (Gv q) (Mv q) :=
    (hR.rel1 _).1 (r q).2
  refine ⟨Submodule.Quotient.mk ⟨(r q).1, hr⟩, ?_⟩
  change cls1 (relWK hsr) (zAtK hsr hR ⟨(r q).1, hr⟩) = clsAt (relWK hsr) 1 2 rfl ⟨_, hy⟩
  congr 1
  apply Subtype.ext
  change Submodule.Quotient.mk (Pi.single q (r q) : ∀ v, ((rel v).S 1 : Type)) =
    Submodule.Quotient.mk r
  refine ((Submodule.Quotient.eq _).mpr ?_).symm
  refine ⟨fun v => ⟨(r v).1 - ((Pi.single q (r q) : ∀ v, ((rel v).S 1 : Type)) v).1, ?_⟩, ?_⟩
  · by_cases hv : v = q
    · subst hv
      have e : (Pi.single v (r v) : ∀ w, ((rel w).S 1 : Type)) v = r v := Pi.single_eq_same _ _
      rw [e, sub_self]
      exact Submodule.zero_mem _
    · have e : (Pi.single q (r q) : ∀ w, ((rel w).S 1 : Type)) v = 0 := Pi.single_eq_of_ne hv _
      rw [e, Submodule.coe_zero, sub_zero]
      exact hR.rel_ne v hv _ (r v).2
  · funext v
    exact Subtype.ext rfl

theorem coordC_bijectiveK (T : TameCoordinatesTrivialK k (Mv q) I φ σ) :
    Function.Bijective (coordCK hsr hR φ σ eM (T.htriv φ) (T.htriv σ)) := by
  have key : ∀ u, coordCK hsr hR φ σ eM (T.htriv φ) (T.htriv σ) (phiAtK hsr hR u) =
      coordEquivK T eM u := by
    intro u
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    exact coordC_phiAtK hsr hR φ σ eM (T.htriv φ) (T.htriv σ) z
  refine ⟨fun a b h => ?_, fun x => ?_⟩
  · obtain ⟨a', rfl⟩ := phiAt_surjectiveK hsr hR a
    obtain ⟨b', rfl⟩ := phiAt_surjectiveK hsr hR b
    rw [key, key] at h
    rw [(coordEquivK T eM).injective h]
  · obtain ⟨u, rfl⟩ := (coordEquivK T eM).surjective x
    exact ⟨phiAtK hsr hR u, key u⟩

/-- **The coordinates** `eR : H¹(W_rel) ≃ k² × k²` (tex L5027–5037), `[x] ↦ (eM x_q(φ), eM x_q(σ))`.
Classification: PROVED (from the tame coordinates at `q`). -/
def eRAtK (T : TameCoordinatesTrivialK k (Mv q) I φ σ) :
    (relWK hsr).toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  LinearEquiv.ofBijective _ (coordC_bijectiveK hsr hR φ σ eM T)

variable {F : DerivFamily (locCxK k Gv Mv)} {c : SideCondK k (Gv q) (Mv q)}

theorem eRAt_H1iK (hsr' : ∀ v n, (F.str v).S n ≤ (F.rel v).S n) (hR' : RelAtK F.str F.rel q)
    (T : TameCoordinatesTrivialK k (Mv q) I φ σ) (s : F.Uside.X 1)
    (hs : (Submodule.Quotient.mk s : F.W₁.X 1) ∈ LinearMap.ker (F.W₁.d 1 2 rfl)) :
    eRAtK hsr' hR' φ σ eM T (H1 F.i (cls1 F.W₁ ⟨Submodule.Quotient.mk s, hs⟩)) =
      coordAtK q φ σ eM ((s q).1 : (locCxK k Gv Mv q).X 1) := by
  rw [H1_cls1]
  exact descH1_cls1 F.Wrel (psi0K hsr' hR' φ σ eM)
    (psi0_dK hsr' hR' φ σ eM (T.htriv φ) (T.htriv σ)) _

/-- **The plane equation from the side condition** (tex L5027–5037): if the side cocycles at `q` are
exactly those with coordinates in `P`, the image of `H¹(W₁)` in the coordinates `eRAtK` is `P`.
PROVED. -/
theorem range_H1i_eRAtK (hF : SwitchedAtK F q c) (hsr' : ∀ v n, (F.str v).S n ≤ (F.rel v).S n)
    (hR' : RelAtK F.str F.rel q)
    (T : TameCoordinatesTrivialK k (Mv q) I φ σ)
    (P : Submodule (k) ((Fin 2 → k) × (Fin 2 → k)))
    (hB : ∀ z : Z1K k (Gv q) (Mv q),
      z ∈ c.BF ↔ coordAtK q φ σ eM (z : (contCochains (k) (Gv q) (Mv q)).X 1) ∈ P) :
    (LinearMap.range (H1 F.i)).map (eRAtK hsr' hR' φ σ eM T).toLinearMap = P := by
  ext x
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := clsAt_surjective F.W₁ 1 2 rfl w
    obtain ⟨s, rfl⟩ := (quotSub F.fs 1).mkQ_surjective y
    obtain ⟨z, hz, hzs⟩ := (hF.side1 _).1 (s q).2
    have h2 : coordAtK q φ σ eM ((s q).1 : (locCxK k Gv Mv q).X 1) ∈ P := by
      rw [← hzs]
      exact (hB z).1 hz
    exact Eq.mpr (congrArg (· ∈ P) (eRAt_H1iK φ σ eM hsr' hR' T s hy)) h2
  · intro hx
    obtain ⟨u, rfl⟩ := (coordEquivK T eM).surjective x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have hz : z ∈ c.BF := (hB z).2 hx
    have hzs : ((z : (contCochains (k) (Gv q) (Mv q)).X 1) : (locCxK k Gv Mv q).X 1) ∈
        (F.side q).S 1 := (hF.side1 _).2 ⟨z, hz, rfl⟩
    have hs : (Submodule.Quotient.mk (Pi.single q (⟨_, hzs⟩ : (F.side q).S 1)) : F.W₁.X 1) ∈
        LinearMap.ker (F.W₁.d 1 2 rfl) := by
      change Submodule.Quotient.mk (F.Uside.d 1 2 rfl
        (Pi.single q (⟨_, hzs⟩ : (F.side q).S 1))) = (0 : F.W₁.X 2)
      have h : (F.side q).cx.d 1 2 rfl (⟨_, hzs⟩ : (F.side q).S 1) = 0 :=
        Subtype.ext (LinearMap.mem_ker.mp z.2)
      exact (congrArg Submodule.Quotient.mk
        ((piCx_d_single (fun v => (F.side v).cx) 1 2 rfl q (⟨_, hzs⟩ : (F.side q).S 1)).trans
          ((congrArg (fun y => (Pi.single q y : ∀ v, ((F.side v).cx).X 2)) h).trans
            (Pi.single_zero q)))).trans (Submodule.Quotient.mk_zero _)
    refine ⟨H1 F.i (cls1 F.W₁ ⟨_, hs⟩), ⟨_, rfl⟩, ?_⟩
    have e : (Pi.single q (⟨_, hzs⟩ : (F.side q).S 1) : ∀ v, ((F.side v).S 1 : Type)) q =
        ⟨_, hzs⟩ := Pi.single_eq_same _ _
    exact (eRAt_H1iK φ σ eM hsr' hR' T _ hs).trans (congrArg (fun w : ((F.side q).S 1 : Type) =>
      coordAtK q φ σ eM (w.1 : (locCxK k Gv Mv q).X 1)) e)

end Coords

section Planes

variable {k : Type} [Field k]

variable {ι : Type} [DecidableEq ι]
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module (k) (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) (k) (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, ContinuousAdd (Mv v)]
  [∀ v, ContinuousConstSMul k (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]
  {q : ι} (φ σ : Gv q) (eM : Mv q ≃ₗ[k] (Fin 2 → k))

omit [DecidableEq ι] in
/-- **The finite side cocycles are the finite plane** (tex L5027–5037): `z` vanishes on `I` iff
`z(σ) = 0`. PROVED (from the tame coordinates). -/
theorem finite_side_iffK {I : Subgroup (Gv q)} (T : TameCoordinatesTrivialK k (Mv q) I φ σ)
    (z : Z1K k (Gv q) (Mv q)) :
    z ∈ (sideOfSetK k (Mv q) (I : Set (Gv q))).BF ↔
      coordAtK q φ σ eM (z : (contCochains (k) (Gv q) (Mv q)).X 1) ∈
        finPlane (k) (Fin 2 → k) (Fin 2 → k) := by
  rw [mem_sideOfSetK_BF, mem_finPlane, coordAt_applyK]
  dsimp only
  rw [LinearEquiv.map_eq_zero_iff]
  exact ⟨fun h => h σ T.hσI, fun h g hg => T.hI z h g hg⟩

omit [DecidableEq ι] in
/-- **The singular side cocycles are the singular plane** (tex L5027–5037): `z(φ) = 0`. PROVED. -/
theorem singular_side_iffK (z : Z1K k (Gv q) (Mv q)) :
    z ∈ (sideOfSetK k (Mv q) ({φ} : Set (Gv q))).BF ↔
      coordAtK q φ σ eM (z : (contCochains (k) (Gv q) (Mv q)).X 1) ∈
        singPlane (k) (Fin 2 → k) (Fin 2 → k) := by
  rw [mem_sideOfSetK_BF, mem_singPlane, coordAt_applyK]
  dsimp only
  rw [LinearEquiv.map_eq_zero_iff]
  refine ⟨fun h => h φ (Set.mem_singleton φ), fun h g hg => ?_⟩
  rw [Set.mem_singleton_iff.mp hg]
  exact h

variable {F : DerivFamily (locCxK k Gv Mv)} (G : GCx (k)) (res : GHom G (piCx (locCxK k Gv Mv)))

/-- **The finite quasi side** of a family switched at `q` with the finite side (tex L5060–5086):
`toQuasiSide` with the coordinates `eRAtK` and the plane equation `range_H1i_eRAtK`. PROVED. -/
def finQuasiSideK {I : Subgroup (Gv q)}
    (hF : SwitchedAtK F q (sideOfSetK k (Mv q) (I : Set (Gv q))))
    (T : TameCoordinatesTrivialK k (Mv q) I φ σ) :
    QuasiSwitchSide (F.toQuasiRelaxed G res (eRAtK (derivHsrK F) hF.rel φ σ eM T))
      (finPlane (k) (Fin 2 → k) (Fin 2 → k)) :=
  F.toQuasiSide G res (eRAtK (derivHsrK F) hF.rel φ σ eM T) _
    (range_H1i_eRAtK φ σ eM hF (derivHsrK F) hF.rel T _ (finite_side_iffK φ σ eM T))

/-- **The singular quasi side** of a family switched at `q` with the singular side. PROVED. -/
def singQuasiSideK {I : Subgroup (Gv q)}
    (hF : SwitchedAtK F q (sideOfSetK k (Mv q) ({φ} : Set (Gv q))))
    (T : TameCoordinatesTrivialK k (Mv q) I φ σ) :
    QuasiSwitchSide (F.toQuasiRelaxed G res (eRAtK (derivHsrK F) hF.rel φ σ eM T))
      (singPlane (k) (Fin 2 → k) (Fin 2 → k)) :=
  F.toQuasiSide G res (eRAtK (derivHsrK F) hF.rel φ σ eM T) _
    (range_H1i_eRAtK φ σ eM hF (derivHsrK F) hF.rel T _ (singular_side_iffK φ σ eM))

variable (q) in
/-- **The relaxed localization of switch conditions** (tex L5060–5086): the quasi relaxed
localization `G → ∏_v L_v ← ∏_v U_v^{rel}`, `W_rel`, with coordinates `eR`; it involves only the
strict and relaxed conditions, not the side. -/
def relLocK (old : ∀ v, SubFam (locCxK k Gv Mv v))
    (eR : (relWK (switch_hsrK q old)).toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)) :
    QuasiRelaxedLocalization (k) :=
  ⟨⟨G, relUK (switchRelK k Gv Mv q old), piCx (locCxK k Gv Mv), res,
    piMap fun v => (switchRelK k Gv Mv q old v).incl⟩, relWK (switch_hsrK q old),
    quotMk (strRelK (switch_hsrK q old)), eR⟩

/-- **The switch families have the side-independent relaxed localization** `relLocK` (tex
L5060–5086): so the finite and singular quasi sides live over one quasi relaxed localization.
PROVED (definitional). -/
theorem switchFam_toQuasiRelaxedK (old : ∀ v, SubFam (locCxK k Gv Mv v)) (T' : ∀ v, Set (Gv v))
    {I : Subgroup (Gv q)} (T : TameCoordinatesTrivialK k (Mv q) I φ σ) :
    (switchFamK k Gv Mv q old T').toQuasiRelaxed G res
        (eRAtK (switch_hsrK q old) (switch_relAtK q old) φ σ eM T) =
      relLocK q G res old (eRAtK (switch_hsrK q old) (switch_relAtK q old) φ σ eM T) :=
  rfl

/-- **The quasi side of the switch family with side set `T' q`** (tex L5060–5086), over `relLocK`:
`toQuasiSide` with the coordinates `eRAtK` and the plane equation `range_H1i_eRAtK`. PROVED. -/
def switchQuasiSideK (old : ∀ v, SubFam (locCxK k Gv Mv v)) (T' : ∀ v, Set (Gv v))
    {I : Subgroup (Gv q)} (T : TameCoordinatesTrivialK k (Mv q) I φ σ)
    (P : Submodule (k) ((Fin 2 → k) × (Fin 2 → k)))
    (hB : ∀ z : Z1K k (Gv q) (Mv q), z ∈ (sideOfSetK k (Mv q) (T' q)).BF ↔
      coordAtK q φ σ eM (z : (contCochains (k) (Gv q) (Mv q)).X 1) ∈ P) :
    QuasiSwitchSide (relLocK q G res old (eRAtK (switch_hsrK q old) (switch_relAtK q old) φ σ eM
        T)) P :=
  (switchFamK k Gv Mv q old T').toQuasiSide G res
    (eRAtK (switch_hsrK q old) (switch_relAtK q old) φ σ eM T) P
    (range_H1i_eRAtK φ σ eM (switchFam_switchedAtK q old T') (switch_hsrK q old) (switch_relAtK q
        old)
      T P hB)

end Planes

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

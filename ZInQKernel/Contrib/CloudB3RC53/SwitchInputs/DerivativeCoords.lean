import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.DerivativeTransport
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.TameUnramified
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchAdjunction

/-!
# RC53 SwitchInputs: the coordinates of the derivative quotients and the genuine side families

Proposition `ex:limits-uniform-lower-bound`, the switch at a new inert derivative prime (tex
L5027–5037, L5060–5086). This file feeds `DerivFamily.toQuasiSide` with its two remaining inputs at
the genuine local complexes `C^•_cont(G_v, M_v)`.

Nodes:
* Scaffolding (generic, PROVED): `degSub` (a subcomplex of an extended `ℕ`-indexed complex given in
  degrees `0`, `1`), `descH1` (maps out of `H¹` by a cocycle formula killing coboundaries),
  `cls1_boundary`, `H1_cls1` (naturality of classes), `piCx_d_single`.
* The derivative subcomplexes at a place (PROVED): `strSub = [Z⁰ → 0]`, `relSub = [C⁰ → Z¹]`,
  `sideSub c = [A → B]` for a `SideCond` (the finite side `sideOfSet I`, the singular side
  `sideOfSet {φ}`), and the switch family `switchFam q old T` (switched at `q`, old conditions
  elsewhere), with `hcobS`, `hcobStr` from the side conditions (`switchFam_switchedAt`).
* (1) The coordinate comparison (PROVED from `TameCoordinates`): for strict/relaxed conditions
  switched at `q` (`RelAt`), `eRAt : H¹(W_rel) ≃ k² × k²`, `[x] ↦ (eM x_q(φ), eM x_q(σ))`; the
  comparison `phiAt : Z¹/d⁰C⁰ → H¹(W_rel)` is surjective and `eRAt ∘ phiAt = coordEquiv`.
  The plane equation `range_H1i_eRAt`: the image of `H¹(W₁)` is the plane cut out by the side
  cocycles; `finite_side_iff` (finite plane) and `singular_side_iff` (singular plane).
* (2) The quasi sides (PROVED): `finQuasiSide`, `singQuasiSide` for any switched family;
  `switchQuasiSide` over the side-independent relaxed localization `relLoc`
  (`switchFam_toQuasiRelaxed`).
* non-vacuity at the genuine setting (PROVED): `genuine_quasiSides` — for a nonarchimedean local
  field `K` with odd residue characteristic, both quasi switch sides (finite plane, singular plane)
  over one relaxed localization of `C^•_cont(G_K, 𝔽₂²)` (`genFinSide`, `genSingSide`);
  `TameCoordinates` from `tameCoordinatesTrivial_galois`, `SwitchedAt` from `switchFam_switchedAt`.

**Caveat (residue field `𝔽₂`).** The genuine instances in this file are specialised to the residue
field `𝔽₂`. They are not applicable at the height-one primes `𝔭 ≠ (2)` of `Λ` where the switching
runs (tex L4976: `R = Λ_𝔭`, residue field of characteristic `0`): there is no ring map
`Λ_𝔭 → ZMod 2` (`isEmpty_ringHom_zmod_two_heightOne`). See `GaloisWiringQuad.lean` for the
field-generic version.
-/
noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.GenuineInst ZInQ.Manuscript.RC.Uniform ValuativeRel

/-! ### Classes and maps out of `H¹` -/

section Cls

variable {k : Type} [Field k]

/-- **Maps out of `H¹`**: a linear map `ψ : W¹ → V` killing the coboundaries `d⁰(W⁰)` descends to
`H¹(W) → V`. -/
def descH1 (W : GCx k) {V : Type} [AddCommGroup V] [Module k V] (ψ : W.X 1 →ₗ[k] V)
    (hψ : ∀ y, ψ (W.d 0 1 rfl y) = 0) : W.toCC.homology 1 →ₗ[k] V :=
  (CokernelCofork.IsColimit.desc' (W.toCC.homologyIsCokernel 0 1 (by simp))
    (ModuleCat.ofHom (ψ ∘ₗ (W.toCC.iCycles 1).hom)) (by
      ext y
      have h := congrArg (fun f => ModuleCat.Hom.hom f y) (W.toCC.toCycles_i 0 1)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      change ψ ((W.toCC.iCycles 1).hom ((W.toCC.toCycles 0 1).hom y)) = 0
      rw [h]
      exact (congrArg ψ (GCx.toCC_d_hom W 0 1 rfl y)).trans (hψ y))).1.hom

theorem descH1_cls1 (W : GCx k) {V : Type} [AddCommGroup V] [Module k V] (ψ : W.X 1 →ₗ[k] V)
    (hψ : ∀ y, ψ (W.d 0 1 rfl y) = 0) (x : LinearMap.ker (W.d 1 2 rfl)) :
    descH1 W ψ hψ (cls1 W x) = ψ x.1 := by
  have hfac := (CokernelCofork.IsColimit.desc' (W.toCC.homologyIsCokernel 0 1 (by simp))
    (ModuleCat.ofHom (ψ ∘ₗ (W.toCC.iCycles 1).hom)) (by
      ext y
      have h := congrArg (fun f => ModuleCat.Hom.hom f y) (W.toCC.toCycles_i 0 1)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      change ψ ((W.toCC.iCycles 1).hom ((W.toCC.toCycles 0 1).hom y)) = 0
      rw [h]
      exact (congrArg ψ (GCx.toCC_d_hom W 0 1 rfl y)).trans (hψ y))).2
  have e := congrArg (fun f => ModuleCat.Hom.hom f
    ((liftCycAt W.toCC 1 2 rfl).hom (kerToCC W 1 2 rfl x))) hfac
  simp only [Cofork.π_ofπ, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  change descH1 W ψ hψ ((W.toCC.homologyπ 1).hom
    ((liftCycAt W.toCC 1 2 rfl).hom (kerToCC W 1 2 rfl x))) = _
  rw [descH1, e]
  exact congrArg ψ (iCycles_clsAt W 1 2 rfl x)

/-- **Coboundaries have zero class.** -/
theorem cls1_boundary (W : GCx k) (y : W.X 0) (hy : W.d 0 1 rfl y ∈ LinearMap.ker (W.d 1 2 rfl)) :
    cls1 W ⟨W.d 0 1 rfl y, hy⟩ = 0 := by
  change (W.toCC.homologyπ 1).hom
    ((liftCycAt W.toCC 1 2 rfl).hom (kerToCC W 1 2 rfl ⟨W.d 0 1 rfl y, hy⟩)) = 0
  have e : (liftCycAt W.toCC 1 2 rfl).hom (kerToCC W 1 2 rfl ⟨W.d 0 1 rfl y, hy⟩) =
      (W.toCC.toCycles 0 1).hom y := by
    apply iCycles_hom_injective
    refine (iCycles_clsAt W 1 2 rfl ⟨W.d 0 1 rfl y, hy⟩).trans ?_
    have h : (W.toCC.iCycles 1).hom ((W.toCC.toCycles 0 1).hom y) = (W.toCC.d 0 1).hom y :=
      congrArg (fun f => ModuleCat.Hom.hom f y) (W.toCC.toCycles_i 0 1)
    exact ((GCx.toCC_d_hom W 0 1 rfl y).symm.trans h.symm)
  rw [e]
  exact congrArg (fun f => ModuleCat.Hom.hom f y) (W.toCC.toCycles_comp_homologyπ 0 1)

/-- The image of a cocycle under a chain map is a cocycle. -/
theorem map_mem_ker1 {A B : GCx k} (f : GHom A B) (x : LinearMap.ker (A.d 1 2 rfl)) :
    f.f 1 1 rfl x.1 ∈ LinearMap.ker (B.d 1 2 rfl) := by
  rw [LinearMap.mem_ker, ← f.comm 1 2 1 2 rfl rfl rfl rfl, LinearMap.mem_ker.mp x.2, map_zero]

/-- **Naturality of classes**: `H¹(f)[x] = [f x]`. -/
theorem H1_cls1 {A B : GCx k} (f : GHom A B) (x : LinearMap.ker (A.d 1 2 rfl)) :
    H1 f (cls1 A x) = cls1 B ⟨f.f 1 1 rfl x.1, map_mem_ker1 f x⟩ := by
  change (HomologicalComplex.homologyMap (GHom.toCC f) 1).hom ((A.toCC.homologyπ 1).hom
    ((liftCycAt A.toCC 1 2 rfl).hom (kerToCC A 1 2 rfl x))) = (B.toCC.homologyπ 1).hom
    ((liftCycAt B.toCC 1 2 rfl).hom (kerToCC B 1 2 rfl ⟨f.f 1 1 rfl x.1, map_mem_ker1 f x⟩))
  have hn := congrArg (fun g => ModuleCat.Hom.hom g
    ((liftCycAt A.toCC 1 2 rfl).hom (kerToCC A 1 2 rfl x)))
    (HomologicalComplex.homologyπ_naturality (GHom.toCC f) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  rw [hn]
  congr 1
  apply iCycles_hom_injective
  have hi := congrArg (fun g => ModuleCat.Hom.hom g
    ((liftCycAt A.toCC 1 2 rfl).hom (kerToCC A 1 2 rfl x)))
    (HomologicalComplex.cyclesMap_i (GHom.toCC f) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi, iCycles_clsAt, iCycles_clsAt]
  rfl

end Cls

/-! ### Subcomplexes given in degrees `0` and `1` -/

section Deg

variable {k : Type} [Field k]

/-- The submodule family `S₀` in degree `0`, `S₁` in degree `1`, `0` elsewhere, of the extension by
zero of an `ℕ`-indexed complex. -/
def degS (K : CochainComplex (ModuleCat.{0} k) ℕ) (S0 : Submodule k (K.X 0))
    (S1 : Submodule k (K.X 1)) : ∀ n : ℤ, Submodule k ((natCx K).X n)
  | Int.ofNat 0 => S0
  | Int.ofNat 1 => S1
  | _ => ⊥

/-- **The subcomplex** with `S₀` in degree `0`, `S₁` in degree `1`, when `d(S₀) ⊆ S₁` and
`d(S₁) = 0`. -/
def degSub (K : CochainComplex (ModuleCat.{0} k) ℕ) (S0 : Submodule k (K.X 0))
    (S1 : Submodule k (K.X 1)) (h01 : ∀ x ∈ S0, (K.d 0 1).hom x ∈ S1)
    (h12 : ∀ x ∈ S1, (K.d 1 2).hom x = 0) : SubFam (natCx K) where
  S := degS K S0 S1
  hd i j h x hx := by
    subst h
    rcases i with (_ | _ | n) | m
    · exact h01 x hx
    · change (K.d 1 2).hom x ∈ (⊥ : Submodule k (K.X 2))
      rw [h12 x hx]
      exact Submodule.zero_mem _
    · have hx0 : x = 0 := (Submodule.mem_bot k).mp hx
      rw [hx0]
      exact Submodule.zero_mem _
    · have hx0 : x = 0 := (Submodule.mem_bot k).mp hx
      rw [hx0]
      exact Submodule.zero_mem _

theorem degS_mono (K : CochainComplex (ModuleCat.{0} k) ℕ) {S0 T0 : Submodule k (K.X 0)}
    {S1 T1 : Submodule k (K.X 1)} (h0 : S0 ≤ T0) (h1 : S1 ≤ T1) :
    ∀ n, degS K S0 S1 n ≤ degS K T0 T1 n
  | Int.ofNat 0 => h0
  | Int.ofNat 1 => h1
  | Int.ofNat (_ + 2) => le_rfl
  | Int.negSucc _ => le_rfl

end Deg

/-! ### The derivative subcomplexes at a place and the switch family -/

section Family

variable {ι : Type} [DecidableEq ι]
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module (ZMod 2) (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) (ZMod 2) (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, DiscreteTopology (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]

variable (Gv Mv) in
/-- The genuine local complex `C^•_cont(G_v, M_v)` at `v` (extended by zero). -/
abbrev locCx (v : ι) : GCx (ZMod 2) := natCx (contCochains (ZMod 2) (Gv v) (Mv v))

variable (Gv Mv) in
/-- **The relaxed derivative condition** `τ_{≤1} C^• = [C⁰ → Z¹]` at `v` (tex L5060–5061). -/
def relSub (v : ι) : SubFam (locCx Gv Mv v) :=
  degSub _ ⊤ (Z1 (Gv v) (Mv v)) (fun x _ => (relaxedD (Gv v) (Mv v) x).2) (fun _ hx => hx)

variable (Gv Mv) in
/-- **The strict derivative condition** `τ_{≤0} C^• = [Z⁰ → 0]` at `v` (tex L5060–5061). -/
def strSub (v : ι) : SubFam (locCx Gv Mv v) :=
  degSub _ (Z0 (Gv v) (Mv v)) ⊥ (fun _ hx => (Submodule.mem_bot _).mpr hx)
    (fun x hx => by rw [(Submodule.mem_bot _).mp hx, map_zero])

/-- **The side condition** `[A → B] ⊆ [C⁰ → Z¹]` of a `SideCond` at `v` (tex L5060–5082). -/
def sideSub (v : ι) (c : SideCond (Gv v) (Mv v)) : SubFam (locCx Gv Mv v) :=
  degSub _ c.AF (c.BF.map (Z1 (Gv v) (Mv v)).subtype)
    (fun x hx => ⟨relaxedD (Gv v) (Mv v) x, c.hd hx, rfl⟩)
    (fun _ hx => by obtain ⟨z, _, rfl⟩ := hx; exact z.2)

variable (Gv Mv) in
/-- The strict conditions of the switch at `q`: `[Z⁰ → 0]` at `q`, the old conditions elsewhere. -/
def switchStr (q : ι) (old : ∀ v, SubFam (locCx Gv Mv v)) (v : ι) : SubFam (locCx Gv Mv v) :=
  if v = q then strSub Gv Mv v else old v

variable (Gv Mv) in
/-- The relaxed conditions of the switch at `q`: `[C⁰ → Z¹]` at `q`, the old conditions elsewhere.
-/
def switchRel (q : ι) (old : ∀ v, SubFam (locCx Gv Mv v)) (v : ι) : SubFam (locCx Gv Mv v) :=
  if v = q then relSub Gv Mv v else old v

variable (Gv Mv) in
/-- **The switch family** at the place `q` (tex L5060–5082): the strict, side (`sideOfSet (T q)`:
the finite side for `T q = I`, the singular side for `T q = {φ}`) and relaxed derivative conditions
at `q`, and the old conditions `old v` elsewhere. -/
def switchFam (q : ι) (old : ∀ v, SubFam (locCx Gv Mv v)) (T : ∀ v, Set (Gv v)) :
    DerivFamily (locCx Gv Mv) where
  str := switchStr Gv Mv q old
  side v := if v = q then sideSub v (sideOfSet (T v)) else old v
  rel := switchRel Gv Mv q old
  hss v n := by
    dsimp only [switchStr]
    split_ifs
    · exact degS_mono _ (sideOfSet (M := Mv v) (T v)).hZ0 bot_le n
    · exact le_rfl
  hsr v n := by
    dsimp only [switchRel]
    split_ifs
    · exact degS_mono _ le_top (by
        rintro _ ⟨z, _, rfl⟩
        exact z.2) n
    · exact le_rfl
  hcobS v x hx hdx := by
    dsimp only [switchRel] at hx
    split_ifs at hx hdx ⊢ with h
    · obtain ⟨z, hz, hzx⟩ := hdx
      have e : relaxedD (Gv v) (Mv v) x = z := Subtype.ext hzx.symm
      exact (sideOfSet (M := Mv v) (T v)).hcob x (e ▸ hz)
    · exact hx
  hcobStr v x hx hdx := by
    dsimp only [switchStr] at hdx ⊢
    split_ifs at hx hdx ⊢ with h
    · exact (Submodule.mem_bot _).mp hdx
    · exact hx

variable (q : ι) (old : ∀ v, SubFam (locCx Gv Mv v)) (T : ∀ v, Set (Gv v))

theorem switchStr_q : switchStr Gv Mv q old q = strSub Gv Mv q := by simp [switchStr]

theorem switchRel_q : switchRel Gv Mv q old q = relSub Gv Mv q := by simp [switchRel]

theorem switchStr_ne {v : ι} (h : v ≠ q) : switchStr Gv Mv q old v = old v := by
  simp [switchStr, h]

theorem switchRel_ne {v : ι} (h : v ≠ q) : switchRel Gv Mv q old v = old v := by
  simp [switchRel, h]

/-- Strict below relaxed for the switch conditions (independent of the side sets). PROVED. -/
theorem switch_hsr (v : ι) (n : ℤ) : (switchStr Gv Mv q old v).S n ≤ (switchRel Gv Mv q old v).S n := by
  by_cases h : v = q
  · subst h
    rw [switchStr_q, switchRel_q]
    exact degS_mono _ le_top bot_le n
  · rw [switchStr_ne q old h, switchRel_ne q old h]

theorem switchFam_side_q (n : ℤ) :
    ((switchFam Gv Mv q old T).side q).S n = (sideSub q (sideOfSet (T q))).S n := by
  simp [switchFam]

end Family

/-! ### Products and single places -/

section Single

variable {k : Type} [CommRing k] {ι : Type} [DecidableEq ι]

theorem piCx_d_single (A : ι → GCx k) (i j : ℤ) (h : i + 1 = j) (q : ι) (x : (A q).X i) :
    (piCx A).d i j h (Pi.single q x) = Pi.single q ((A q).d i j h x) := by
  funext v
  by_cases hv : v = q
  · subst hv
    change (A v).d i j h ((Pi.single v x : ∀ w, (A w).X i) v) =
      (Pi.single v ((A v).d i j h x) : ∀ w, (A w).X j) v
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · change (A v).d i j h ((Pi.single q x : ∀ w, (A w).X i) v) =
      (Pi.single q ((A q).d i j h x) : ∀ w, (A w).X j) v
    rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, map_zero]

end Single

/-! ### The coordinates `H¹(W_rel) ≃ k² × k²` of a family switched at one place -/

section Coords

variable {ι : Type}
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module (ZMod 2) (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) (ZMod 2) (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, DiscreteTopology (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]

/-- **Relaxed and strict conditions switched at the place `q`**: at `q` the strict condition is
`[Z⁰ → 0]` (degree `1`: `0`), the relaxed one `[C⁰ → Z¹]`; away from `q` relaxed and strict agree in
degree `1`. -/
structure RelAt (str rel : ∀ v, SubFam (locCx Gv Mv v)) (q : ι) : Prop where
  str1 : ∀ x : (locCx Gv Mv q).X 1, x ∈ (str q).S 1 → x = 0
  rel0 : ∀ x : (locCx Gv Mv q).X 0, x ∈ (rel q).S 0
  rel1 : ∀ x : (locCx Gv Mv q).X 1, x ∈ (rel q).S 1 ↔ x ∈ Z1 (Gv q) (Mv q)
  rel_ne : ∀ v, v ≠ q → ∀ x : (locCx Gv Mv v).X 1, x ∈ (rel v).S 1 → x ∈ (str v).S 1

/-- **A family switched at the place `q` with side condition `c`**: its strict and relaxed
conditions are switched at `q` and the side condition at `q` is `[A → B]`. -/
structure SwitchedAt (F : DerivFamily (locCx Gv Mv)) (q : ι) (c : SideCond (Gv q) (Mv q)) :
    Prop where
  rel : RelAt F.str F.rel q
  side1 : ∀ x : (locCx Gv Mv q).X 1, x ∈ (F.side q).S 1 ↔
    ∃ z ∈ c.BF, (z : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) = x

/-- **The switch conditions are switched at `q`**. PROVED. -/
theorem switch_relAt [DecidableEq ι] (q : ι) (old : ∀ v, SubFam (locCx Gv Mv v)) :
    RelAt (switchStr Gv Mv q old) (switchRel Gv Mv q old) q where
  str1 x hx := by
    rw [switchStr_q] at hx
    exact (Submodule.mem_bot _).mp hx
  rel0 x := by
    rw [switchRel_q]
    trivial
  rel1 x := by
    rw [switchRel_q]
    exact Iff.rfl
  rel_ne v h x hx := by
    rw [switchRel_ne q old h] at hx
    rw [switchStr_ne q old h]
    exact hx

/-- **The switch family is switched at `q`** with the side condition `sideOfSet (T q)`. PROVED. -/
theorem switchFam_switchedAt [DecidableEq ι] (q : ι) (old : ∀ v, SubFam (locCx Gv Mv v))
    (T : ∀ v, Set (Gv v)) : SwitchedAt (switchFam Gv Mv q old T) q (sideOfSet (T q)) where
  rel := switch_relAt q old
  side1 x := by
    rw [switchFam_side_q]
    exact Iff.rfl

/-- Strict below relaxed in a derivative family. -/
theorem derivHsr (F : DerivFamily (locCx Gv Mv)) (v : ι) (n : ℤ) :
    (F.str v).S n ≤ (F.rel v).S n :=
  (F.hss v n).trans (F.hsr v n)

variable {str rel : ∀ v, SubFam (locCx Gv Mv v)} (hsr : ∀ v n, (str v).S n ≤ (rel v).S n)
  {q : ι} (hR : RelAt str rel q) (φ σ : Gv q) (eM : Mv q ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))

variable (rel) in
/-- The relaxed local-condition complex `∏_v U_v^{rel}`. -/
abbrev relU : GCx (ZMod 2) := piCx fun v => (rel v).cx

/-- `strict → relaxed`. -/
def strRel : GHom (piCx fun v => (str v).cx) (relU rel) :=
  piMap fun v => SubFam.inclLe (hsr v)

/-- `W_rel = relaxed / strict` (for a derivative family `F`, definitionally `F.Wrel`). -/
abbrev relW : GCx (ZMod 2) := quotCx (strRel hsr)

variable (q) in
/-- The coordinates `x ↦ (eM x(φ), eM x(σ))` of a `1`-cochain at `q`. -/
def coordAt : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1 →ₗ[ZMod 2]
    (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) :=
  (eM.toLinearMap ∘ₗ ev1L φ).prod (eM.toLinearMap ∘ₗ ev1L σ)

theorem coordAt_apply (x : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) :
    coordAt q φ σ eM x = (eM (ev1 x φ), eM (ev1 x σ)) :=
  rfl

theorem coordAt_relaxedD (hφ : ∀ m : Mv q, φ • m = m) (hσ : ∀ m : Mv q, σ • m = m)
    (a : (contCochains (ZMod 2) (Gv q) (Mv q)).X 0) :
    coordAt q φ σ eM ((relaxedD (Gv q) (Mv q) a : Z1 (Gv q) (Mv q)) :
      (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) = 0 := by
  have h := coordL_relaxedD φ σ hφ hσ a
  have h1 : ev1 ((relaxedD (Gv q) (Mv q) a : Z1 (Gv q) (Mv q)) :
      (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) φ = 0 := congrArg Prod.fst h
  have h2 : ev1 ((relaxedD (Gv q) (Mv q) a : Z1 (Gv q) (Mv q)) :
      (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) σ = 0 := congrArg Prod.snd h
  rw [coordAt_apply, h1, h2, map_zero]
  rfl

theorem coordAt_mk (T : TameCoordinates (M := Mv q) I φ σ) (z : Z1 (Gv q) (Mv q)) :
    coordAt q φ σ eM (z : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) =
      coordEquiv T eM (Submodule.Quotient.mk z) :=
  rfl

variable (rel q) in
/-- The coordinates read at `q` on the relaxed condition in degree `1`. -/
def psiRaw : (relU rel).X 1 →ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) :=
  coordAt q φ σ eM ∘ₗ ((rel q).S 1).subtype ∘ₗ
    LinearMap.proj (R := ZMod 2) (φ := fun v => ((rel v).S 1 : Type)) q

/-- The coordinates on `W_rel¹ = U_rel¹ / U_str¹` (they kill the strict condition at `q`). -/
def psi0 : (relW hsr).X 1 →ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) :=
  (quotSub (strRel hsr) 1).liftQ (psiRaw rel q φ σ eM) (by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change coordAt q φ σ eM ((x q).1 : (locCx Gv Mv q).X 1) = 0
    rw [hR.str1 _ (x q).2]
    exact (coordAt q φ σ eM).map_zero)

theorem psi0_d (hφ : ∀ m : Mv q, φ • m = m) (hσ : ∀ m : Mv q, σ • m = m) (y : (relW hsr).X 0) :
    psi0 hsr hR φ σ eM ((relW hsr).d 0 1 rfl y) = 0 := by
  obtain ⟨r, rfl⟩ := (quotSub (strRel hsr) 0).mkQ_surjective y
  exact coordAt_relaxedD φ σ eM hφ hσ ((r q).1 : (locCx Gv Mv q).X 0)

/-- **The coordinate map** `C : H¹(W_rel) → k² × k²`, `[x] ↦ (eM x_q(φ), eM x_q(σ))`. -/
def coordC (hφ : ∀ m : Mv q, φ • m = m) (hσ : ∀ m : Mv q, σ • m = m) :
    (relW hsr).toCC.homology 1 →ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) :=
  descH1 (relW hsr) (psi0 hsr hR φ σ eM) (psi0_d hsr hR φ σ eM hφ hσ)

variable [DecidableEq ι]

/-- A `1`-cocycle at `q` as an element of the relaxed condition at `q`. -/
def relIn : Z1 (Gv q) (Mv q) →ₗ[ZMod 2] ((rel q).S 1) where
  toFun z := ⟨z.1, (hR.rel1 _).2 z.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A `1`-cocycle at `q` as a relaxed `1`-cochain supported at `q`. -/
def sAt : Z1 (Gv q) (Mv q) →ₗ[ZMod 2] (relU rel).X 1 :=
  LinearMap.single (ZMod 2) (fun v => ((rel v).S 1 : Type)) q ∘ₗ relIn hR

/-- Its class in `W_rel¹` is a cocycle. -/
def zAt : Z1 (Gv q) (Mv q) →ₗ[ZMod 2] LinearMap.ker ((relW hsr).d 1 2 rfl) :=
  ((quotSub (strRel hsr) 1).mkQ ∘ₗ sAt hR).codRestrict _ fun z => by
    change Submodule.Quotient.mk ((relU rel).d 1 2 rfl (Pi.single q (relIn hR z))) = (0 : (relW hsr).X 2)
    have hz : (rel q).cx.d 1 2 rfl (relIn hR z) = 0 := Subtype.ext (LinearMap.mem_ker.mp z.2)
    exact (congrArg Submodule.Quotient.mk
      ((piCx_d_single (fun v => (rel v).cx) 1 2 rfl q (relIn hR z)).trans
        ((congrArg (fun y => (Pi.single q y : ∀ v, ((rel v).cx).X 2)) hz).trans
          (Pi.single_zero q)))).trans (Submodule.Quotient.mk_zero _)

/-- **The comparison map** `Z¹(G_q, M_q) / d⁰C⁰ → H¹(W_rel)`, `[z] ↦ [z at q]`. -/
def phiAt : (H1Wrel (G := Gv q) (M := Mv q)) →ₗ[ZMod 2] (relW hsr).toCC.homology 1 :=
  (LinearMap.range (relaxedD (Gv q) (Mv q))).liftQ (cls1 (relW hsr) ∘ₗ zAt hsr hR) (by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    have ha : (a : (locCx Gv Mv q).X 0) ∈ (rel q).S 0 := hR.rel0 a
    have e : zAt hsr hR (relaxedD (Gv q) (Mv q) a) =
        ⟨(relW hsr).d 0 1 rfl (Submodule.Quotient.mk (Pi.single q (⟨a, ha⟩ : (rel q).S 0))),
          LinearMap.mem_ker.mpr ((relW hsr).d_d 0 1 2 rfl rfl _)⟩ := Subtype.ext
      (congrArg Submodule.Quotient.mk
        (piCx_d_single (fun v => (rel v).cx) 0 1 rfl q (⟨a, ha⟩ : (rel q).S 0)).symm)
    change cls1 (relW hsr) (zAt hsr hR (relaxedD (Gv q) (Mv q) a)) = 0
    rw [e]
    exact cls1_boundary _ _ _)

theorem coordC_phiAt (hφ : ∀ m : Mv q, φ • m = m) (hσ : ∀ m : Mv q, σ • m = m)
    (z : Z1 (Gv q) (Mv q)) :
    coordC hsr hR φ σ eM hφ hσ (phiAt hsr hR (Submodule.Quotient.mk z)) =
      coordAt q φ σ eM (z : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) := by
  change descH1 (relW hsr) _ _ (cls1 (relW hsr) (zAt hsr hR z)) = _
  rw [descH1_cls1]
  have e : (Pi.single q (relIn hR z) : ∀ v, ((rel v).S 1 : Type)) q = relIn hR z :=
    Pi.single_eq_same _ _
  exact congrArg (fun w : ((rel q).S 1 : Type) => coordAt q φ σ eM (w.1 : (locCx Gv Mv q).X 1)) e

/-- **Every class of `H¹(W_rel)` is supported at `q`**: `phiAt` is surjective. PROVED. -/
theorem phiAt_surjective : Function.Surjective (phiAt hsr hR) := by
  intro w
  obtain ⟨⟨y, hy⟩, rfl⟩ := clsAt_surjective (relW hsr) 1 2 rfl w
  obtain ⟨r, rfl⟩ := (quotSub (strRel hsr) 1).mkQ_surjective y
  have hr : ((r q).1 : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) ∈ Z1 (Gv q) (Mv q) :=
    (hR.rel1 _).1 (r q).2
  refine ⟨Submodule.Quotient.mk ⟨(r q).1, hr⟩, ?_⟩
  change cls1 (relW hsr) (zAt hsr hR ⟨(r q).1, hr⟩) = clsAt (relW hsr) 1 2 rfl ⟨_, hy⟩
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

theorem coordC_bijective (T : TameCoordinates (M := Mv q) I φ σ) :
    Function.Bijective (coordC hsr hR φ σ eM T.hφ T.hσ) := by
  have key : ∀ u, coordC hsr hR φ σ eM T.hφ T.hσ (phiAt hsr hR u) = coordEquiv T eM u := by
    intro u
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    exact coordC_phiAt hsr hR φ σ eM T.hφ T.hσ z
  refine ⟨fun a b h => ?_, fun x => ?_⟩
  · obtain ⟨a', rfl⟩ := phiAt_surjective hsr hR a
    obtain ⟨b', rfl⟩ := phiAt_surjective hsr hR b
    rw [key, key] at h
    rw [(coordEquiv T eM).injective h]
  · obtain ⟨u, rfl⟩ := (coordEquiv T eM).surjective x
    exact ⟨phiAt hsr hR u, key u⟩

/-- **The coordinates** `eR : H¹(W_rel) ≃ k² × k²` (tex L5027–5037), `[x] ↦ (eM x_q(φ), eM x_q(σ))`.
Classification: PROVED (from the tame coordinates at `q`). -/
def eRAt (T : TameCoordinates (M := Mv q) I φ σ) :
    (relW hsr).toCC.homology 1 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) :=
  LinearEquiv.ofBijective _ (coordC_bijective hsr hR φ σ eM T)

variable {F : DerivFamily (locCx Gv Mv)} {c : SideCond (Gv q) (Mv q)}

theorem eRAt_H1i (hsr' : ∀ v n, (F.str v).S n ≤ (F.rel v).S n) (hR' : RelAt F.str F.rel q)
    (T : TameCoordinates (M := Mv q) I φ σ) (s : F.Uside.X 1)
    (hs : (Submodule.Quotient.mk s : F.W₁.X 1) ∈ LinearMap.ker (F.W₁.d 1 2 rfl)) :
    eRAt hsr' hR' φ σ eM T (H1 F.i (cls1 F.W₁ ⟨Submodule.Quotient.mk s, hs⟩)) =
      coordAt q φ σ eM ((s q).1 : (locCx Gv Mv q).X 1) := by
  rw [H1_cls1]
  exact descH1_cls1 F.Wrel (psi0 hsr' hR' φ σ eM)
    (psi0_d hsr' hR' φ σ eM T.hφ T.hσ) _

/-- **The plane equation from the side condition** (tex L5027–5037): if the side cocycles at `q` are
exactly those with coordinates in `P`, the image of `H¹(W₁)` in the coordinates `eRAt` is `P`.
PROVED. -/
theorem range_H1i_eRAt (hF : SwitchedAt F q c) (hsr' : ∀ v n, (F.str v).S n ≤ (F.rel v).S n) (hR' : RelAt F.str F.rel q)
    (T : TameCoordinates (M := Mv q) I φ σ)
    (P : Submodule (ZMod 2) ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)))
    (hB : ∀ z : Z1 (Gv q) (Mv q),
      z ∈ c.BF ↔ coordAt q φ σ eM (z : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) ∈ P) :
    (LinearMap.range (H1 F.i)).map (eRAt hsr' hR' φ σ eM T).toLinearMap = P := by
  ext x
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := clsAt_surjective F.W₁ 1 2 rfl w
    obtain ⟨s, rfl⟩ := (quotSub F.fs 1).mkQ_surjective y
    obtain ⟨z, hz, hzs⟩ := (hF.side1 _).1 (s q).2
    have h2 : coordAt q φ σ eM ((s q).1 : (locCx Gv Mv q).X 1) ∈ P := by
      rw [← hzs]
      exact (hB z).1 hz
    exact Eq.mpr (congrArg (· ∈ P) (eRAt_H1i φ σ eM hsr' hR' T s hy)) h2
  · intro hx
    obtain ⟨u, rfl⟩ := (coordEquiv T eM).surjective x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have hz : z ∈ c.BF := (hB z).2 hx
    have hzs : ((z : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) : (locCx Gv Mv q).X 1) ∈
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
    exact (eRAt_H1i φ σ eM hsr' hR' T _ hs).trans (congrArg (fun w : ((F.side q).S 1 : Type) =>
      coordAt q φ σ eM (w.1 : (locCx Gv Mv q).X 1)) e)

end Coords

/-! ### The finite and singular planes and the quasi sides -/

section Planes

variable {ι : Type} [DecidableEq ι]
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module (ZMod 2) (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) (ZMod 2) (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, DiscreteTopology (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]
  {q : ι} (φ σ : Gv q) (eM : Mv q ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))

omit [DecidableEq ι] in
/-- **The finite side cocycles are the finite plane** (tex L5027–5037): `z` vanishes on `I` iff
`z(σ) = 0`. PROVED (from the tame coordinates). -/
theorem finite_side_iff {I : Subgroup (Gv q)} (T : TameCoordinates (M := Mv q) I φ σ)
    (z : Z1 (Gv q) (Mv q)) :
    z ∈ (sideOfSet (M := Mv q) (I : Set (Gv q))).BF ↔
      coordAt q φ σ eM (z : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) ∈
        finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) := by
  rw [mem_sideOfSet_BF, mem_finPlane, coordAt_apply]
  dsimp only
  rw [LinearEquiv.map_eq_zero_iff]
  exact ⟨fun h => h σ T.hσI, fun h g hg => T.hI z h g hg⟩

omit [DecidableEq ι] in
/-- **The singular side cocycles are the singular plane** (tex L5027–5037): `z(φ) = 0`. PROVED. -/
theorem singular_side_iff (z : Z1 (Gv q) (Mv q)) :
    z ∈ (sideOfSet (M := Mv q) ({φ} : Set (Gv q))).BF ↔
      coordAt q φ σ eM (z : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) ∈
        singPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) := by
  rw [mem_sideOfSet_BF, mem_singPlane, coordAt_apply]
  dsimp only
  rw [LinearEquiv.map_eq_zero_iff]
  refine ⟨fun h => h φ (Set.mem_singleton φ), fun h g hg => ?_⟩
  rw [Set.mem_singleton_iff.mp hg]
  exact h

variable {F : DerivFamily (locCx Gv Mv)} (G : GCx (ZMod 2)) (res : GHom G (piCx (locCx Gv Mv)))

/-- **The finite quasi side** of a family switched at `q` with the finite side (tex L5060–5086):
`toQuasiSide` with the coordinates `eRAt` and the plane equation `range_H1i_eRAt`. PROVED. -/
def finQuasiSide {I : Subgroup (Gv q)} (hF : SwitchedAt F q (sideOfSet (I : Set (Gv q))))
    (T : TameCoordinates (M := Mv q) I φ σ) :
    QuasiSwitchSide (F.toQuasiRelaxed G res (eRAt (derivHsr F) hF.rel φ σ eM T))
      (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) :=
  F.toQuasiSide G res (eRAt (derivHsr F) hF.rel φ σ eM T) _
    (range_H1i_eRAt φ σ eM hF (derivHsr F) hF.rel T _ (finite_side_iff φ σ eM T))

/-- **The singular quasi side** of a family switched at `q` with the singular side. PROVED. -/
def singQuasiSide {I : Subgroup (Gv q)} (hF : SwitchedAt F q (sideOfSet ({φ} : Set (Gv q))))
    (T : TameCoordinates (M := Mv q) I φ σ) :
    QuasiSwitchSide (F.toQuasiRelaxed G res (eRAt (derivHsr F) hF.rel φ σ eM T))
      (singPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) :=
  F.toQuasiSide G res (eRAt (derivHsr F) hF.rel φ σ eM T) _
    (range_H1i_eRAt φ σ eM hF (derivHsr F) hF.rel T _ (singular_side_iff φ σ eM))

variable (q) in
/-- **The relaxed localization of switch conditions** (tex L5060–5086): the quasi relaxed
localization `G → ∏_v L_v ← ∏_v U_v^{rel}`, `W_rel`, with coordinates `eR`; it involves only the
strict and relaxed conditions, not the side. -/
def relLoc (old : ∀ v, SubFam (locCx Gv Mv v))
    (eR : (relW (switch_hsr q old)).toCC.homology 1 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    QuasiRelaxedLocalization (ZMod 2) :=
  ⟨⟨G, relU (switchRel Gv Mv q old), piCx (locCx Gv Mv), res,
    piMap fun v => (switchRel Gv Mv q old v).incl⟩, relW (switch_hsr q old),
    quotMk (strRel (switch_hsr q old)), eR⟩

/-- **The switch families have the side-independent relaxed localization** `relLoc` (tex
L5060–5086): so the finite and singular quasi sides live over one quasi relaxed localization.
PROVED (definitional). -/
theorem switchFam_toQuasiRelaxed (old : ∀ v, SubFam (locCx Gv Mv v)) (T' : ∀ v, Set (Gv v))
    {I : Subgroup (Gv q)} (T : TameCoordinates (M := Mv q) I φ σ) :
    (switchFam Gv Mv q old T').toQuasiRelaxed G res
        (eRAt (switch_hsr q old) (switch_relAt q old) φ σ eM T) =
      relLoc q G res old (eRAt (switch_hsr q old) (switch_relAt q old) φ σ eM T) :=
  rfl

/-- **The quasi side of the switch family with side set `T' q`** (tex L5060–5086), over `relLoc`:
`toQuasiSide` with the coordinates `eRAt` and the plane equation `range_H1i_eRAt`. PROVED. -/
def switchQuasiSide (old : ∀ v, SubFam (locCx Gv Mv v)) (T' : ∀ v, Set (Gv v))
    {I : Subgroup (Gv q)} (T : TameCoordinates (M := Mv q) I φ σ)
    (P : Submodule (ZMod 2) ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)))
    (hB : ∀ z : Z1 (Gv q) (Mv q), z ∈ (sideOfSet (M := Mv q) (T' q)).BF ↔
      coordAt q φ σ eM (z : (contCochains (ZMod 2) (Gv q) (Mv q)).X 1) ∈ P) :
    QuasiSwitchSide (relLoc q G res old (eRAt (switch_hsr q old) (switch_relAt q old) φ σ eM T)) P :=
  (switchFam Gv Mv q old T').toQuasiSide G res
    (eRAt (switch_hsr q old) (switch_relAt q old) φ σ eM T) P
    (range_H1i_eRAt φ σ eM (switchFam_switchedAt q old T') (switch_hsr q old) (switch_relAt q old)
      T P hB)

end Planes

/-! ### The genuine instance at a local Galois group (non-vacuity) -/

section Genuine

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- The one-place family of local groups `G_K`. -/
abbrev genG : Unit → Type := fun _ => Field.absoluteGaloisGroup K

variable (K) in
/-- The one-place family of coefficients `𝔽₂²` (trivial action). -/
abbrev genM : Unit → Type := fun _ => GalM K 2

variable (K) in
/-- The old conditions (irrelevant: the only place is the switch place). -/
abbrev genOld : ∀ v, SubFam (locCx (genG K) (genM K) v) := fun _ => SubFam.top _

/-- The genuine global term (the product of the local complexes, `res = id`). -/
abbrev genGlob : GCx (ZMod 2) := piCx (locCx (genG K) (genM K))

/-- **The genuine coordinates** `H¹(W_rel) ≃ k² × k²` for `C^•_cont(G_K, 𝔽₂²)` (tex L5027–5037). -/
def genER {φ σ : Field.absoluteGaloisGroup K}
    (T : TameCoordinates (M := GalM K 2) (TauCeti.inertiaSubgroup K) φ σ) :
    (relW (switch_hsr () (genOld K))).toCC.homology 1 ≃ₗ[ZMod 2]
      (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) :=
  eRAt (switch_hsr () (genOld K)) (switch_relAt () (genOld K)) φ σ (trivModEquiv _ _) T

/-- **The genuine quasi relaxed localization** of `C^•_cont(G_K, 𝔽₂²)`. -/
def genR {φ σ : Field.absoluteGaloisGroup K}
    (T : TameCoordinates (M := GalM K 2) (TauCeti.inertiaSubgroup K) φ σ) :
    QuasiRelaxedLocalization (ZMod 2) :=
  relLoc () (genGlob (K := K)) (idGHom _) (genOld K) (genER T)

/-- **The genuine finite quasi side** at `G_K` (tex L5060–5086): the switch family with the finite
side `sideOfSet I_K` (`finiteSide I_K`). PROVED. -/
def genFinSide {φ σ : Field.absoluteGaloisGroup K}
    (T : TameCoordinates (M := GalM K 2) (TauCeti.inertiaSubgroup K) φ σ) :
    QuasiSwitchSide (genR T) (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) :=
  switchQuasiSide (Gv := genG K) (Mv := genM K) (q := ()) φ σ (trivModEquiv _ _) genGlob
    (idGHom _) (genOld K)
    (fun _ => (TauCeti.inertiaSubgroup K : Set (Field.absoluteGaloisGroup K))) T _
    (finite_side_iff (Gv := genG K) (Mv := genM K) (q := ()) φ σ (trivModEquiv _ _) T)

/-- **The genuine singular quasi side** at `G_K` (side `sideOfSet {φ}`, `singularSide φ`), over the
same relaxed localization. PROVED. -/
def genSingSide {φ σ : Field.absoluteGaloisGroup K}
    (T : TameCoordinates (M := GalM K 2) (TauCeti.inertiaSubgroup K) φ σ) :
    QuasiSwitchSide (genR T) (singPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) :=
  switchQuasiSide (Gv := genG K) (Mv := genM K) (q := ()) φ σ (trivModEquiv _ _) genGlob
    (idGHom _) (genOld K) (fun _ => {φ}) T _
    (singular_side_iff (Gv := genG K) (Mv := genM K) (q := ()) φ σ (trivModEquiv _ _))

variable (K) in
/-- **non-vacuity at the genuine setting** (tex L5027–5037, L5060–5086): for a nonarchimedean local
field `K` with odd residue characteristic there are a Frobenius lift `φ`, a tame generator
`σ ∈ I_K` and tame coordinates for `𝔽₂²`, and over the genuine relaxed localization of
`C^•_cont(G_K, 𝔽₂²)` both quasi switch sides (finite plane and singular plane) exist. PROVED.
Residual-field (`𝔽₂`) instance only; not applicable at height-one primes `≠ (2)`, see
`isEmpty_ringHom_zmod_two_heightOne`; the characteristic-zero version is the field-generic chain. -/
theorem genuine_quasiSides (hp : ringChar 𝓀[K] ≠ 2) :
    ∃ φ σ : Field.absoluteGaloisGroup K, TauCeti.IsArithFrobeniusLift K φ ∧
      σ ∈ TauCeti.inertiaSubgroup K ∧
      ∃ T : TameCoordinates (M := GalM K 2) (TauCeti.inertiaSubgroup K) φ σ,
        Nonempty (QuasiSwitchSide (genR T) (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2))) ∧
        Nonempty (QuasiSwitchSide (genR T) (singPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2))) := by
  obtain ⟨φ, σ, hφ, hσ, hT⟩ := tameCoordinatesTrivial_galois K hp 2
  exact ⟨φ, σ, hφ, hσ, tameCoordinates_of_trivial hT, ⟨genFinSide _⟩, ⟨genSingSide _⟩⟩

end Genuine

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

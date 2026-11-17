import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Transfer
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

/-!
# HeegnerCohomology, part 11: each Mackey orbit term is a local corestriction

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3251–3256: "Localizing (H21) separates the cosets into decomposition-group orbits: this is the
local Mackey formula, a sum of the local corestrictions from the transported places."

`Transfer.lean` splits the restriction of (H21) to a subgroup `D ≤ G` (the decomposition group at
a place) into the terms `TO` over the `D`-orbits `O ⊆ Δ = G/H` (`T_eq_sum_TO`), each a cochain map
(`dTO_eq_TOd`).  Here each orbit term is identified with a corestriction (all `PROVED`):

Fix the orbit `O = D δ₀`, a lift `s ∈ G` of `δ₀`, the stabilizer `D₀ = {x ∈ D : x δ₀ = δ₀}` (the
decomposition group of the transported place; `s⁻¹ D₀ s ⊆ H`), a transversal `t` of `D/D₀`, and
the transported cocycle `b_s(x) = R(s) b(s⁻¹ x s)` on `D₀`.  The coefficients are `M(θ)` with `D`
acting through `R = θ ρ` (`TwM`).

* `orbitTerm_eq_cor`: if the global section is compatible with the orbit (`r(t_u δ₀) = t_u s`,
  "transport these choices"), the orbit term is *exactly* Tau Ceti's corestriction cochain
  `cochainsCor1 D (Tw …) D₀ t b_s` (`(cor¹_t f)(γ) = ∑_u t_u • f(t_u⁻¹ γ t_{γ⁻¹u})`), which induces
  `explicitCor1Transversal`, the genuine corestriction `H¹(D₀, M(θ)) → H¹(D, M(θ))`.
* `orbitTerm_change_section`: changing the section changes the orbit term by the coboundary of
  `w = ∑_{δ ∈ O} R(r_δ) b(r_δ⁻¹ r'_δ)` (the integral homotopy, degree one, restricted to an orbit).
* `orbitTerm_eq_cor_add_coboundary`: for an arbitrary section, the orbit term is the corestriction
  of the transported cocycle plus a coboundary; so on `H¹` every orbit term is the local
  corestriction from the transported place.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

namespace TwistedTransfer

open Finset

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
  {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ)

/-- `M` with `G` acting through `R = θ ρ`. -/
structure TwM (H : Subgroup G) [H.Normal] (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) where
  /-- the underlying element of `M` -/
  val : M

namespace TwM

variable {H ρ θ}

@[ext] theorem ext' {x y : TwM H ρ θ} (h : x.val = y.val) : x = y := by
  cases x; cases y; simp_all

/-- `TwM ≃ M`. -/
def equiv : TwM H ρ θ ≃ M := ⟨TwM.val, TwM.mk, fun _ => rfl, fun _ => rfl⟩

instance : AddCommGroup (TwM H ρ θ) := (equiv (H := H) (ρ := ρ) (θ := θ)).addCommGroup

@[simp] theorem val_add (x y : TwM H ρ θ) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_zero : (0 : TwM H ρ θ).val = 0 := rfl
@[simp] theorem val_sub (x y : TwM H ρ θ) : (x - y).val = x.val - y.val := rfl
@[simp] theorem val_neg (x : TwM H ρ θ) : (-x).val = -x.val := rfl

theorem val_sum {ι : Type*} (s : Finset ι) (f : ι → TwM H ρ θ) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val :=
  map_sum (⟨⟨TwM.val, rfl⟩, fun _ _ => rfl⟩ : TwM H ρ θ →+ M) f s

instance : DistribMulAction G (TwM H ρ θ) where
  smul g x := ⟨R H ρ θ g x.val⟩
  one_smul x := by
    ext; show R H ρ θ 1 x.val = x.val
    simp [R]
  mul_smul g k x := by
    ext; show R H ρ θ (g * k) x.val = R H ρ θ g (R H ρ θ k x.val)
    rw [R_mul, Module.End.mul_apply]
  smul_zero g := by ext; show R H ρ θ g 0 = 0; simp
  smul_add g x y := by ext; show R H ρ θ g (x.val + y.val) = _; simp; rfl

@[simp] theorem val_smul (g : G) (x : TwM H ρ θ) : (g • x).val = R H ρ θ g x.val := rfl

end TwM

variable (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)

/-- The degree-one orbit term `(𝒯_O b)(g) = ∑_{δ ∈ O} R(r_{gδ}) b(h(g,δ))`. -/
def orbitTerm (O : Finset (G ⧸ H)) (b : H → M) (g : G) : M :=
  ∑ δ ∈ O, R H ρ θ (r ((g : G ⧸ H) * δ)) (b ⟨hc H r g δ, hc_mem H r hr g δ⟩)

/-- In degree one, `TO` is the orbit term. -/
theorem TO_one (O : Finset (G ⧸ H)) (b : H → M) (g : G) :
    TO H r hr ρ θ O 1 (fun x => b (x 0)) (fun _ => g) = orbitTerm H ρ θ r hr O b g := by
  refine sum_congr rfl fun δ _ => ?_
  have h1 : ((tprod 1 (fun _ => g) : G) : G ⧸ H) * δ = (g : G ⧸ H) * δ := by simp [tprod_succ]
  have h2 : hTuple H r hr 1 δ (fun _ => g) 0 = ⟨hc H r g δ, hc_mem H r hr g δ⟩ :=
    Subtype.ext (by rw [hTuple_zero]; simp [tprod])
  rw [h1]
  show R H ρ θ _ (b (hTuple H r hr 1 δ (fun _ => g) 0)) = _
  rw [h2]

/-! ## The stabilizer and the transported cocycle -/

variable (D : Subgroup G) (δ₀ : G ⧸ H)

/-- The stabilizer `D₀ = {x ∈ D : x δ₀ = δ₀}` of `δ₀` in `D`. -/
def stab : Subgroup D where
  carrier := {x | ((x : G) : G ⧸ H) * δ₀ = δ₀}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, QuotientGroup.mk_mul, mul_assoc] at *
    rw [hy, hx]
  inv_mem' {x} hx := by
    simp only [Set.mem_setOf_eq, InvMemClass.coe_inv, QuotientGroup.mk_inv] at *
    conv_lhs => rw [← hx]
    group

variable {D δ₀}

theorem conj_mem_of_stab (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (x : stab H D δ₀) :
    s⁻¹ * ((x : D) : G) * s ∈ H := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    hs, mul_assoc, x.2]
  group

/-- The transported cocycle `b_s(x) = R(s) b(s⁻¹ x s)` on `D₀`. -/
def bTrans (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M) : stab H D δ₀ → TwM H ρ θ :=
  fun x => ⟨R H ρ θ s (b ⟨s⁻¹ * ((x : D) : G) * s, conj_mem_of_stab H s hs x⟩)⟩

variable [(stab H D δ₀).FiniteIndex] (t : D ⧸ stab H D δ₀ → D)
  (ht : ∀ u, (QuotientGroup.mk (t u) : D ⧸ stab H D δ₀) = u)

/-- The orbit point of a coset: `φ(u) = t_u δ₀`. -/
def phi (u : D ⧸ stab H D δ₀) : G ⧸ H := (((t u : D) : G) : G ⧸ H) * δ₀

omit [(stab H D δ₀).FiniteIndex] in
include ht in
theorem phi_smul (d : D) (u : D ⧸ stab H D δ₀) :
    phi H t (d • u) = (((d : D) : G) : G ⧸ H) * phi H t u := by
  have h1 : (QuotientGroup.mk (t (d • u)) : D ⧸ stab H D δ₀) = QuotientGroup.mk (d * t u) := by
    rw [ht]
    conv_lhs => rw [← ht u]
    rfl
  obtain ⟨k, hk⟩ : ∃ k : stab H D δ₀, t (d • u) = d * t u * k := by
    rw [QuotientGroup.eq] at h1
    exact ⟨(⟨_, h1⟩ : stab H D δ₀)⁻¹, by simp; group⟩
  have hk2 : ((((k : D) : G)) : G ⧸ H) * δ₀ = δ₀ := k.2
  simp only [phi, hk, Subgroup.coe_mul, QuotientGroup.mk_mul, mul_assoc]
  rw [hk2]

omit [(stab H D δ₀).FiniteIndex] in
include ht in
theorem phi_injective : Function.Injective (phi H t) := by
  intro u v h
  rw [← ht u, ← ht v, QuotientGroup.eq]
  show (((((t u)⁻¹ * t v : D) : G)) : G ⧸ H) * δ₀ = δ₀
  simp only [phi] at h
  rw [Subgroup.coe_mul, InvMemClass.coe_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_assoc,
    ← h, ← mul_assoc, inv_mul_cancel, one_mul]

/-! ## The identification -/

/-- **Each orbit term is a local corestriction** (tex 3251–3256), `PROVED`: with a global section
compatible with the orbit (`r(t_u δ₀) = t_u s`), the orbit term over `O = {t_u δ₀}` restricted to
`D` is exactly the corestriction cochain from `D₀` to `D` of the transported cocycle `b_s`. -/
theorem orbitTerm_eq_cor [DecidableEq (G ⧸ H)] (s : G) (hs : ((s : G) : G ⧸ H) = δ₀)
    (hcomp : ∀ u, r (phi H t u) = ((t u : D) : G) * s) (b : H → M) (d : D) :
    orbitTerm H ρ θ r hr (univ.image (phi H t)) b d =
      (TauCeti.ContCohomology.cochainsCor1 D (TwM H ρ θ) (stab H D δ₀) t ht
        (bTrans H ρ θ s hs b) d).val := by
  classical
  rw [orbitTerm, sum_image (fun u _ v _ h => phi_injective H t ht h),
    TauCeti.ContCohomology.cochainsCor1_apply, TwM.val_sum]
  refine Fintype.sum_equiv (MulAction.toPerm d) _ _ (fun u => ?_)
  simp only [MulAction.toPerm_apply]
  rw [Subgroup.smul_def, TwM.val_smul]
  simp only [bTrans]
  rw [← phi_smul H t ht, hcomp, R_mul, Module.End.mul_apply]
  congr 3
  apply Subtype.ext
  simp only [hc, ← phi_smul H t ht, hcomp, TauCeti.lWord_def, inv_smul_smul, Subgroup.coe_mul,
    InvMemClass.coe_inv]
  group

/-- **Changing the section on an orbit** (the integral homotopy of Nekovář 8.1.4 in degree one,
restricted to a `D`-stable set `O`), `PROVED`: for a cocycle `b` (`b(xy) = b(x) + x b(y)`), two
sections give orbit terms differing by the coboundary of `w = ∑_{δ ∈ O} R(r_δ) b(r_δ⁻¹ r'_δ)`. -/
theorem orbitTerm_change_section (r' : G ⧸ H → G) (hr' : ∀ δ, ((r' δ : G) : G ⧸ H) = δ)
    (O : Finset (G ⧸ H)) (hO : ∀ d ∈ D, ∀ δ ∈ O, ((d : G) : G ⧸ H) * δ ∈ O)
    (b : H → M) (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    ∃ w : M, ∀ d : D, orbitTerm H ρ θ r' hr' O b d =
      orbitTerm H ρ θ r hr O b d + (R H ρ θ d w - w) := by
  -- `u_δ = r_δ⁻¹ r'_δ ∈ H`
  have hu : ∀ δ, (r δ)⁻¹ * r' δ ∈ H := fun δ => by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hr, hr',
      inv_mul_cancel]
  let u : G ⧸ H → H := fun δ => ⟨_, hu δ⟩
  have hb1 : b 1 = 0 := by simpa using hb 1 1
  have hbinv : ∀ x : H, b x⁻¹ = -ρ (x⁻¹ : H) (b x) := fun x => by
    have := hb x⁻¹ x
    rw [inv_mul_cancel, hb1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  refine ⟨∑ δ ∈ O, R H ρ θ (r δ) (b (u δ)), fun d => ?_⟩
  have hρinv : ∀ (x : H) (m : M), ρ (x : G) (ρ ((x⁻¹ : H) : G) m) = m := fun x m => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have key : ∀ δ : G ⧸ H,
      R H ρ θ (r' ((((d : D) : G) : G ⧸ H) * δ)) (b ⟨hc H r' d δ, hc_mem H r' hr' d δ⟩) =
      R H ρ θ (r ((((d : D) : G) : G ⧸ H) * δ)) (b ⟨hc H r d δ, hc_mem H r hr d δ⟩)
        - R H ρ θ (r ((((d : D) : G) : G ⧸ H) * δ)) (b (u ((((d : D) : G) : G ⧸ H) * δ)))
        + R H ρ θ d (R H ρ θ (r δ) (b (u δ))) := by
    intro δ
    set x := u ((((d : D) : G) : G ⧸ H) * δ) with hx
    set hδ : H := ⟨hc H r d δ, hc_mem H r hr d δ⟩ with hhδ
    have e : (⟨hc H r' d δ, hc_mem H r' hr' d δ⟩ : H) = x⁻¹ * (hδ * u δ) := by
      apply Subtype.ext
      simp only [hx, hhδ, u, hc, Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    have hr'e : r' ((((d : D) : G) : G ⧸ H) * δ) = r ((((d : D) : G) : G ⧸ H) * δ) * (x : G) := by
      simp [hx, u]
    have hsub : ρ (x : G) (b (x⁻¹ * (hδ * u δ))) = b hδ - b x + ρ (hδ : G) (b (u δ)) := by
      rw [hb, hb, hbinv]
      simp only [map_add, map_neg, hρinv]
      abel
    rw [e, hr'e, R_mul, Module.End.mul_apply, R_of_mem H ρ θ x.2, hsub, map_add, map_sub,
      ← Module.End.mul_apply (R H ρ θ _) (ρ _), R_r_mul_hc H r hr ρ θ, Module.End.mul_apply]
  simp only [orbitTerm, key, sum_add_distrib, sum_sub_distrib, ← map_sum]
  have hre : ∑ δ ∈ O, R H ρ θ (r ((d : G) * δ)) (b (u ((d : G) * δ))) =
      ∑ δ ∈ O, R H ρ θ (r δ) (b (u δ)) := by
    refine sum_nbij' (fun δ => ((d : G) : G ⧸ H) * δ) (fun δ => ((d : G) : G ⧸ H)⁻¹ * δ)
      (fun δ hδ => hO _ d.2 δ hδ) (fun δ hδ => ?_) (fun δ _ => by simp) (fun δ _ => by simp)
      (fun δ _ => rfl)
    simpa using hO _ (D.inv_mem d.2) δ hδ
  rw [hre]
  abel

include ht in
/-- The orbit `{t_u δ₀}` is `D`-stable. -/
theorem image_phi_stable [DecidableEq (G ⧸ H)] :
    ∀ d ∈ D, ∀ δ ∈ univ.image (phi H t), ((d : G) : G ⧸ H) * δ ∈ univ.image (phi H t) := by
  intro d hd δ hδ
  obtain ⟨u, -, rfl⟩ := mem_image.mp hδ
  exact mem_image.mpr ⟨(⟨d, hd⟩ : D) • u, mem_univ _, phi_smul H t ht ⟨d, hd⟩ u⟩

/-- **On `H¹`, each orbit term is the local corestriction from the transported place**
(tex 3251–3256), `PROVED` for an arbitrary global section: for a cocycle `b` of `H`, the orbit term
restricted to `D` is the corestriction cochain of the transported cocycle `b_s` plus the coboundary
of some `w ∈ M` (for the action `R` of `D`). -/
theorem orbitTerm_eq_cor_add_coboundary [DecidableEq (G ⧸ H)] (s : G)
    (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M) (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    ∃ w : M, ∀ d : D, orbitTerm H ρ θ r hr (univ.image (phi H t)) b d =
      (TauCeti.ContCohomology.cochainsCor1 D (TwM H ρ θ) (stab H D δ₀) t ht
        (bTrans H ρ θ s hs b) d).val + (R H ρ θ d w - w) := by
  classical
  -- the compatible section
  let rc : G ⧸ H → G := fun δ =>
    if h : ∃ u, phi H t u = δ then ((t h.choose : D) : G) * s else r δ
  have hrc : ∀ δ, ((rc δ : G) : G ⧸ H) = δ := by
    intro δ
    by_cases h : ∃ u, phi H t u = δ
    · simp only [rc, dif_pos h, QuotientGroup.mk_mul, hs]
      exact h.choose_spec
    · simp only [rc, dif_neg h, hr]
  have hcomp : ∀ u, rc (phi H t u) = ((t u : D) : G) * s := by
    intro u
    have h : ∃ v, phi H t v = phi H t u := ⟨u, rfl⟩
    simp only [rc, dif_pos h, phi_injective H t ht h.choose_spec]
  obtain ⟨w, hw⟩ := orbitTerm_change_section H ρ θ rc hrc r hr (univ.image (phi H t))
    (image_phi_stable H t ht) b hb
  exact ⟨w, fun d => by rw [hw d, orbitTerm_eq_cor H ρ θ rc hrc t ht s hs hcomp b d]⟩

end TwistedTransfer

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Node: the Mackey orbit terms are local corestrictions**, tex 3251–3256, `PROVED`: for every
group `G`, normal subgroup `H`, section `r` of `G → G/H`, representation `ρ`, character `θ` of
`G/H`, subgroup `D` (decomposition group), point `δ₀ ∈ G/H` with finite `D`-orbit (finite-index
stabilizer `D₀`), lift `s` of `δ₀`, transversal `t` of `D/D₀`, and cocycle `b` of `H`: the orbit
term of the twisted transfer over `D δ₀` equals, up to a coboundary on `D`, the corestriction from
`D₀` to `D` of the transported cocycle `x ↦ θ(s)ρ(s) b(s⁻¹ x s)`, with coefficients `M(θ)`. -/
def MackeyCorNode : Prop :=
  ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] (r : G ⧸ H → G)
    (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (D : Subgroup G) (δ₀ : G ⧸ H)
    [(TwistedTransfer.stab H D δ₀).FiniteIndex] [DecidableEq (G ⧸ H)]
    (t : D ⧸ TwistedTransfer.stab H D δ₀ → D)
    (ht : ∀ u, (QuotientGroup.mk (t u) : D ⧸ TwistedTransfer.stab H D δ₀) = u)
    (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M)
    (_hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)),
    ∃ w : M, ∀ d : D,
      TwistedTransfer.orbitTerm H ρ θ r hr (Finset.univ.image (TwistedTransfer.phi H t)) b d =
        (TauCeti.ContCohomology.cochainsCor1 D (TwistedTransfer.TwM H ρ θ)
          (TwistedTransfer.stab H D δ₀) t ht (TwistedTransfer.bTrans H ρ θ s hs b) d).val +
        (TwistedTransfer.R H ρ θ d w - w)

theorem mackeyCorNode_proof : MackeyCorNode := by
  intro G _ H _ r hr A M _ _ _ ρ θ D δ₀ _ _ t ht s hs b hb
  exact TwistedTransfer.orbitTerm_eq_cor_add_coboundary H ρ θ r hr t ht s hs b hb

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

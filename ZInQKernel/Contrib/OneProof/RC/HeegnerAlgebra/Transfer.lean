import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 6: the coefficient push and the twisted transfer

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 7 "The actual coefficient push and its local conditions", tex lines 3202–3295.

* (H20), tex 3203–3217: Shapiro followed by the equivariant coefficient map
  `E[2^m] ⊗ A[Δ_f] → (E[2^m] ⊗ A)(θ)`, `v ⊗ [δ] ↦ θ(δ) v`, is equivariant (`PROVED`).
* (H21), tex 3219–3249: the explicit transferred cochains
  `(𝒯_θ c)(g₁,…,g_n) = ∑_δ R(r_{g₁⋯g_n δ}) c(h(g₁,δ₁),…,h(g_n,δ_n))`, `δ_i = g_{i+1}⋯g_n δ`,
  `R = θ ρ_T`, `g r_δ = r_{gδ} h(g,δ)`; the identity `h(gk,δ) = h(g,kδ) h(k,δ)` and
  `d 𝒯_θ = 𝒯_θ d` in degrees `0, 1, 2` (`PROVED`); no averaging factor occurs.  Changing the
  sections changes the degree-one transfer by an explicit coboundary (the integral homotopy of
  Nekovář 8.1.4 in degree one, `PROVED`).
* (4.2) in common coordinates, tex 3268–3277: the weights `ρ_T(r_δ)` turn the transported
  relations `s' = ρ(r_δ)⁻¹ J ρ(r_δ) f'` into `s = J f` (`PROVED`).
* Gap B1-b (`maps/mcheck-rc-deep.md`), tex 3281–3295: the twisted split norm relation
  `a_q - θ(σ_q) - θ(σ_q)⁻¹` needs `θ` to factor through `Δ_{f/q}`; with that hypothesis it is
  `PROVED` (`B1b_twisted_split_norm`), and a counterexample shows the hypothesis cannot be dropped
  (`B1b_hypothesis_needed`).

The identification of these explicit cochain maps with Nekovář's integral Shapiro and transfer
maps (Selmer complexes, Sections 8.1.1–8.1.6) is the `PRINT` input recorded in
`Interfaces.lean`.  Continuity (all cochains factor through finite quotients, tex 3389–3391) is
not needed for the algebra: the statements below hold for an arbitrary group `G` with a normal
subgroup `H` of finite index.
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open Finset

/-! ## (H20): the equivariant coefficient map -/

section H20

variable {G Δ A M : Type*} [Group G] [CommGroup Δ] [Fintype Δ] [CommRing A] [AddCommGroup M]
  [Module A M]

/-- The induced module `M ⊗ A[Δ]`, written as functions `Δ → M` (`f = ∑_δ f(δ) ⊗ [δ]`), with the
diagonal action `g (v ⊗ [δ]) = g v ⊗ [π(g) δ]`, i.e. `(g f)(δ') = ρ(g) f(π(g)⁻¹ δ')`. -/
def indAct (π : G →* Δ) (ρ : G →* Module.End A M) (g : G) (f : Δ → M) : Δ → M :=
  fun δ' => ρ g (f ((π g)⁻¹ * δ'))

/-- The coefficient map (H20): `v ⊗ [δ] ↦ θ(δ) v`. -/
def coeffMap (θ : Δ →* Aˣ) (f : Δ → M) : M := ∑ δ, (θ δ : A) • f δ

/-- (H20), tex 3207–3217, `PROVED`: the coefficient map is equivariant from the induced module
to the twist `M(θ)`: `Φ(g f) = θ(π g) ρ(g) Φ(f)`.  `A` is an arbitrary commutative ring, so the
statement holds verbatim over `A[G]` for a finite binary group (before evaluation at a sign
character). -/
theorem H20_equivariant (π : G →* Δ) (ρ : G →* Module.End A M) (θ : Δ →* Aˣ) (g : G)
    (f : Δ → M) :
    coeffMap θ (indAct π ρ g f) = (θ (π g) : A) • ρ g (coeffMap θ f) := by
  unfold coeffMap indAct
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (π g)⁻¹) _ _ (fun δ' => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [map_smul, smul_smul, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]

end H20

/-! ## (H21): the twisted transfer on explicit cochains -/

section H21

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The twisted action `R(g) = θ(g) ρ_T(g)` (tex 3235), for a character `θ` of `Δ = G/H`. -/
def Rtw (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (g : G) : Module.End A M :=
  (θ (QuotientGroup.mk g) : A) • ρ g

/-- `R` is multiplicative. -/
theorem Rtw_mul (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (g k : G) :
    Rtw H ρ θ (g * k) = Rtw H ρ θ g * Rtw H ρ θ k := by
  unfold Rtw
  rw [QuotientGroup.mk_mul, map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

/-- On `H`, `R = ρ_T` (`θ` factors through `Δ = G/H`). -/
theorem Rtw_of_mem (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (x : G) (hx : x ∈ H) :
    Rtw H ρ θ x = ρ x := by
  unfold Rtw
  rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one, Units.val_one, one_smul]

/-- The cocycle `h(g,δ) = r_{gδ}⁻¹ g r_δ` of a section `r` of `G → G/H` (tex 3222). -/
def hc (r : G ⧸ H → G) (g : G) (δ : G ⧸ H) : G := (r (QuotientGroup.mk g * δ))⁻¹ * g * r δ

/-- `h(g,δ) ∈ H`. -/
theorem hc_mem (r : G ⧸ H → G) (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ) (g : G)
    (δ : G ⧸ H) : hc H r g δ ∈ H := by
  unfold hc
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, hr, hr]
  group

/-- The identity `h(gk,δ) = h(g,kδ) h(k,δ)` (tex 3229–3230), `PROVED`. -/
theorem hc_mul (r : G ⧸ H → G) (g k : G) (δ : G ⧸ H) :
    hc H r (g * k) δ = hc H r g (QuotientGroup.mk k * δ) * hc H r k δ := by
  unfold hc
  have e : (QuotientGroup.mk (g * k) : G ⧸ H) * δ =
      QuotientGroup.mk g * (QuotientGroup.mk k * δ) := by
    rw [QuotientGroup.mk_mul, mul_assoc]
  rw [e]
  group

/-- `h(g,δ)` as an element of `H`. -/
def hH (r : G ⧸ H → G) (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ) (g : G) (δ : G ⧸ H) :
    H :=
  ⟨hc H r g δ, hc_mem H r hr g δ⟩

/-! Inhomogeneous differentials in degrees `0, 1, 2` for an action map `act`. -/

/-- `d⁰ Q (g) = g Q - Q`. -/
def d0 {Γ : Type*} (act : Γ → Module.End A M) (Q : M) : Γ → M := fun g => act g Q - Q

/-- `d¹ b (g,k) = g b(k) - b(gk) + b(g)`. -/
def d1 {Γ : Type*} [Mul Γ] (act : Γ → Module.End A M) (b : Γ → M) : Γ → Γ → M :=
  fun g k => act g (b k) - b (g * k) + b g

/-- `d² c (g,k,l) = g c(k,l) - c(gk,l) + c(g,kl) - c(g,k)`. -/
def d2 {Γ : Type*} [Mul Γ] (act : Γ → Module.End A M) (c : Γ → Γ → M) : Γ → Γ → Γ → M :=
  fun g k l => act g (c k l) - c (g * k) l + c g (k * l) - c g k

variable (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (r : G ⧸ H → G)
  (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ)

/-- The action of `H` on `M` by restriction of `ρ_T`. -/
def actH : H → Module.End A M := fun x => ρ x

/-- Degree-zero transfer: the weighted sum `∑_δ θ(r_δ) ρ_T(r_δ) Q` (tex 3232–3233). -/
def T0 (Q : M) : M := ∑ δ, Rtw H ρ θ (r δ) Q

/-- Degree-one transfer (H21), tex 3224–3227:
`(𝒯_θ b)(g) = ∑_δ θ(r_{gδ}) ρ_T(r_{gδ}) b(h(g,δ))`. -/
def T1 (b : H → M) : G → M :=
  fun g => ∑ δ, Rtw H ρ θ (r (QuotientGroup.mk g * δ)) (b (hH H r hr g δ))

/-- Degree-two transfer, tex 3237–3242 with `n = 2`: `δ₁ = g₂ δ`, `δ₂ = δ`. -/
def T2 (c : H → H → M) : G → G → M :=
  fun g k => ∑ δ, Rtw H ρ θ (r (QuotientGroup.mk (g * k) * δ))
    (c (hH H r hr g (QuotientGroup.mk k * δ)) (hH H r hr k δ))

/-- Degree-three transfer, tex 3237–3242 with `n = 3`: `δ₁ = g₂g₃δ`, `δ₂ = g₃δ`, `δ₃ = δ`. -/
def T3 (c : H → H → H → M) : G → G → G → M :=
  fun g k l => ∑ δ, Rtw H ρ θ (r (QuotientGroup.mk (g * k * l) * δ))
    (c (hH H r hr g (QuotientGroup.mk (k * l) * δ)) (hH H r hr k (QuotientGroup.mk l * δ))
      (hH H r hr l δ))

/-- The key identity `R(r_{gδ}) ρ_T(h(g,δ)) = R(g) R(r_δ)`, from `r_{gδ} h(g,δ) = g r_δ`. -/
private theorem Rtw_key (g : G) (δ : G ⧸ H) (x : M) :
    Rtw H ρ θ (r (QuotientGroup.mk g * δ)) (ρ (hH H r hr g δ) x) =
      Rtw H ρ θ g (Rtw H ρ θ (r δ) x) := by
  have e : r (QuotientGroup.mk g * δ) * (hH H r hr g δ : G) = g * r δ := by
    show r (QuotientGroup.mk g * δ) * hc H r g δ = g * r δ
    unfold hc
    group
  have hop : Rtw H ρ θ (r (QuotientGroup.mk g * δ)) * ρ (hH H r hr g δ) =
      Rtw H ρ θ g * Rtw H ρ θ (r δ) := by
    rw [← Rtw_of_mem H ρ θ _ (hH H r hr g δ).2, ← Rtw_mul, ← Rtw_mul, e]
  exact congrArg (fun F : Module.End A M => F x) hop

/-- `h(g,kδ) h(k,δ) = h(gk,δ)` as elements of `H`. -/
private theorem hH_mul (g k : G) (δ : G ⧸ H) :
    hH H r hr g (QuotientGroup.mk k * δ) * hH H r hr k δ = hH H r hr (g * k) δ :=
  Subtype.ext (hc_mul H r g k δ).symm

omit [Fintype (G ⧸ H)] in
/-- `(gk)δ = g(kδ)` in `G/H`. -/
private theorem mk_mul_smul (g k : G) (δ : G ⧸ H) :
    (QuotientGroup.mk (g * k) : G ⧸ H) * δ = QuotientGroup.mk g * (QuotientGroup.mk k * δ) := by
  rw [QuotientGroup.mk_mul, mul_assoc]

/-- tex 3232–3234, `PROVED`: in degree zero, applying the boundary to the weighted sum gives
(H21) applied to the boundary of `Q`: `d(𝒯_θ Q) = 𝒯_θ(d Q)`. -/
theorem T0_comm_d (Q : M) :
    d0 (Rtw H ρ θ) (T0 H ρ θ r Q) = T1 H ρ θ r hr (d0 (actH H ρ) Q) := by
  funext g
  simp only [d0, T0, T1, actH, map_sum, map_sub, Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl (fun δ _ => (Rtw_key H ρ θ r hr g δ Q).symm)
  · symm
    exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk g)) _ _ (fun δ => rfl)

/-- tex 3243–3244, `PROVED`: `d 𝒯_θ = 𝒯_θ d` from degree one to degree two. -/
theorem T1_comm_d (b : H → M) :
    d1 (Rtw H ρ θ) (T1 H ρ θ r hr b) = T2 H ρ θ r hr (d1 (actH H ρ) b) := by
  funext g k
  simp only [d1, T1, T2, actH, map_sum, map_add, map_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl (fun δ _ => ?_)
    rw [mk_mul_smul]
    exact (Rtw_key H ρ θ r hr g _ _).symm
  · refine Finset.sum_congr rfl (fun δ _ => ?_)
    rw [hH_mul]
  · simp only [mk_mul_smul]
    symm
    exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk k)) _ _ (fun δ => rfl)

/-- tex 3243–3244, `PROVED`: `d 𝒯_θ = 𝒯_θ d` from degree two to degree three. -/
theorem T2_comm_d (c : H → H → M) :
    d2 (Rtw H ρ θ) (T2 H ρ θ r hr c) = T3 H ρ θ r hr (d2 (actH H ρ) c) := by
  funext g k l
  simp only [d2, T2, T3, actH, map_sum, map_add, map_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have e1 : ∀ δ : G ⧸ H, (QuotientGroup.mk (g * k * l) : G ⧸ H) * δ =
      QuotientGroup.mk g * (QuotientGroup.mk (k * l) * δ) := fun δ => by
    rw [mul_assoc g k l, mk_mul_smul]
  have e3 : ∀ δ : G ⧸ H, (QuotientGroup.mk (g * k * l) : G ⧸ H) * δ =
      QuotientGroup.mk (g * k) * (QuotientGroup.mk l * δ) := fun δ => mk_mul_smul H (g * k) l δ
  congr 1
  congr 1
  congr 1
  · refine Finset.sum_congr rfl (fun δ _ => ?_)
    rw [e1]
    exact (Rtw_key H ρ θ r hr g _ _).symm
  · refine Finset.sum_congr rfl (fun δ _ => ?_)
    rw [mk_mul_smul H k l δ, hH_mul]
  · rw [← mul_assoc g k l]
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    rw [hH_mul]
  · simp only [e3, mk_mul_smul H k l]
    symm
    exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk l)) _ _ (fun δ => rfl)

/-- (H21), tex 3229–3231, `PROVED`: the transferred cochain of a cocycle is a cocycle for the
twisted action `θ ρ_T`: `(𝒯_θ b)(gk) = (𝒯_θ b)(g) + θ(g)ρ_T(g)(𝒯_θ b)(k)`. -/
theorem H21_cocycle (b : H → M) (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) (g k : G) :
    T1 H ρ θ r hr b (g * k) = T1 H ρ θ r hr b g + Rtw H ρ θ g (T1 H ρ θ r hr b k) := by
  have h := congrFun (congrFun (T1_comm_d H ρ θ r hr b) g) k
  have hz : d1 (actH H ρ) b = fun _ _ => 0 := by
    funext x y
    simp only [d1, actH, hb]
    abel
  rw [hz] at h
  simp only [d1, T2, map_zero, Finset.sum_const_zero] at h
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  abel

/-- tex 3247–3248 (the integral homotopy of Nekovář 8.1.4, in degree one), `PROVED`: for another
section `r'`, the two degree-one transfers of a cocycle differ by the coboundary of
`w = ∑_δ R(r_δ) b(r_δ⁻¹ r'_δ)`. -/
theorem T1_change_section (r' : G ⧸ H → G) (hr' : ∀ δ, (QuotientGroup.mk (r' δ) : G ⧸ H) = δ)
    (b : H → M) (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    ∃ w : M, ∀ g : G,
      T1 H ρ θ r' hr' b g = T1 H ρ θ r hr b g + (Rtw H ρ θ g w - w) := by
  have hk : ∀ δ, (r δ)⁻¹ * r' δ ∈ H := fun δ => by
    rw [← QuotientGroup.eq, hr, hr']
  let k : G ⧸ H → H := fun δ => ⟨(r δ)⁻¹ * r' δ, hk δ⟩
  have hkval : ∀ δ, (k δ : G) = (r δ)⁻¹ * r' δ := fun δ => rfl
  refine ⟨∑ δ, Rtw H ρ θ (r δ) (b (k δ)), fun g => ?_⟩
  have hb1 : b 1 = 0 := by simpa using hb 1 1
  have hbinv : ∀ x : H, ρ x (b x⁻¹) = - b x := fun x => by
    have h := hb x x⁻¹
    rw [mul_inv_cancel, hb1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hρinv : ∀ (x : H) (m : M), ρ x (ρ (x⁻¹ : H) m) = m := fun x m => by
    show (ρ x * ρ (x⁻¹ : H)) m = m
    rw [← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one]
    rfl
  have hr'k : ∀ δ, r' δ = r δ * (k δ : G) := fun δ => by
    rw [hkval, mul_inv_cancel_left]
  have hh' : ∀ δ, hH H r' hr' g δ = (k (QuotientGroup.mk g * δ))⁻¹ * (hH H r hr g δ * k δ) :=
    fun δ => by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hkval]
      show (r' (QuotientGroup.mk g * δ))⁻¹ * g * r' δ =
        ((r (QuotientGroup.mk g * δ))⁻¹ * r' (QuotientGroup.mk g * δ))⁻¹ *
          ((r (QuotientGroup.mk g * δ))⁻¹ * g * r δ * ((r δ)⁻¹ * r' δ))
      group
  have term : ∀ δ, Rtw H ρ θ (r' (QuotientGroup.mk g * δ)) (b (hH H r' hr' g δ)) =
      - Rtw H ρ θ (r (QuotientGroup.mk g * δ)) (b (k (QuotientGroup.mk g * δ)))
      + Rtw H ρ θ (r (QuotientGroup.mk g * δ)) (b (hH H r hr g δ))
      + Rtw H ρ θ g (Rtw H ρ θ (r δ) (b (k δ))) := fun δ => by
    rw [hh', hb, hb, hr'k (QuotientGroup.mk g * δ), Rtw_mul, Module.End.mul_apply,
      Rtw_of_mem H ρ θ _ (k _).2]
    simp only [map_add, map_neg, hρinv, hbinv]
    rw [Rtw_key H ρ θ r hr g δ]
    abel
  unfold T1
  rw [Finset.sum_congr rfl (fun δ _ => term δ), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← map_sum]
  rw [Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk g))
    (fun δ => Rtw H ρ θ (r (QuotientGroup.mk g * δ)) (b (k (QuotientGroup.mk g * δ))))
    (fun δ => Rtw H ρ θ (r δ) (b (k δ))) (fun δ => rfl)]
  abel

end H21

/-! ## (4.2) in common coordinates -/

/-- tex 3268–3277, `PROVED`: at the place `r_δ⁻¹ λ` the transported relation reads
`s'_δ = ρ(r_δ)⁻¹ J ρ(r_δ) f'_δ`; the weights `θ(δ) ρ_T(r_δ)` of (H21) turn the sum into
`s = J f` in the common target coordinates. -/
theorem weights_42 {Δ A M : Type*} [Fintype Δ] [CommRing A] [AddCommGroup M] [Module A M]
    (θ : Δ → A) (ρr : Δ → (M ≃ₗ[A] M)) (J : M →ₗ[A] M) (f' : Δ → M) :
    ∑ δ, θ δ • ρr δ ((ρr δ).symm (J (ρr δ (f' δ)))) = J (∑ δ, θ δ • ρr δ (f' δ)) := by
  simp only [LinearEquiv.apply_symm_apply, map_sum, map_smul]

/-! ## Gap B1-b: the twisted split norm relation -/

/-- If every left coset `δ N` meets `T` in exactly one point, then a sum over the group is the sum
over the cosets `t N`, `t ∈ T`. -/
private theorem B1b_sum_eq_sum_transversal {Δ M : Type*} [Group Δ] [Fintype Δ] [AddCommMonoid M]
    (N : Subgroup Δ) [DecidablePred (· ∈ N)] (T : Finset Δ)
    (hT : ∀ δ : Δ, ∃! t, t ∈ T ∧ t⁻¹ * δ ∈ N) (f : Δ → M) :
    ∑ δ, f δ = ∑ t ∈ T, ∑ n ∈ univ.filter (· ∈ N), f (t * n) := by
  have hT' : ∀ δ : Δ, ∃ t, (t ∈ T ∧ t⁻¹ * δ ∈ N) ∧ ∀ y, y ∈ T ∧ y⁻¹ * δ ∈ N → y = t := hT
  choose φ hφ huniq using hT'
  rw [← Finset.sum_product' T (univ.filter (· ∈ N)) (fun t n => f (t * n))]
  symm
  refine Finset.sum_nbij' (fun p => p.1 * p.2) (fun δ => (φ δ, (φ δ)⁻¹ * δ)) ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact Finset.mem_univ _
  · intro δ _
    rw [Finset.mem_product, Finset.mem_filter]
    exact ⟨(hφ δ).1, Finset.mem_univ _, (hφ δ).2⟩
  · rintro ⟨t, n⟩ hp
    rw [Finset.mem_product, Finset.mem_filter] at hp
    have ht : t = φ (t * n) :=
      huniq (t * n) t ⟨hp.1, by rw [inv_mul_cancel_left]; exact hp.2.2⟩
    simp only [← ht, inv_mul_cancel_left]
  · intro δ _
    exact mul_inv_cancel_left (φ δ) δ
  · intro p _
    rfl

/-- A function invariant under right translation by `N` has the same sum over a set `T` of
representatives of the cosets of `N` as over its translate `T σ`. -/
private theorem B1b_sum_transversal_mul_right {Δ M : Type*} [CommGroup Δ] [AddCommMonoid M]
    (N : Subgroup Δ) (T : Finset Δ) (hT : ∀ δ : Δ, ∃! t, t ∈ T ∧ t⁻¹ * δ ∈ N)
    (F : Δ → M) (hF : ∀ δ, ∀ n ∈ N, F (δ * n) = F δ) (σ : Δ) :
    ∑ t ∈ T, F (t * σ) = ∑ t ∈ T, F t := by
  have hT' : ∀ δ : Δ, ∃ t, (t ∈ T ∧ t⁻¹ * δ ∈ N) ∧ ∀ y, y ∈ T ∧ y⁻¹ * δ ∈ N → y = t := hT
  choose φ hφ huniq using hT'
  have key : ∀ δ, F δ = F (φ δ) := fun δ => by
    have h := hF (φ δ) _ (hφ δ).2
    rwa [mul_inv_cancel_left] at h
  have back : ∀ τ, ∀ t ∈ T, φ (φ (t * τ) * τ⁻¹) = t := by
    intro τ t ht
    refine (huniq _ t ⟨ht, ?_⟩).symm
    have h := N.inv_mem (hφ (t * τ)).2
    convert h using 1
    simp only [mul_inv_rev, inv_inv]
    ac_rfl
  calc ∑ t ∈ T, F (t * σ) = ∑ t ∈ T, F (φ (t * σ)) := Finset.sum_congr rfl fun t _ => key _
    _ = ∑ t ∈ T, F t := by
      refine Finset.sum_nbij' (fun t => φ (t * σ)) (fun t => φ (t * σ⁻¹)) ?_ ?_ ?_ ?_ ?_
      · intro t _
        exact (hφ _).1
      · intro t _
        exact (hφ _).1
      · intro t ht
        exact back σ t ht
      · intro t ht
        have h := back σ⁻¹ t ht
        rwa [inv_inv] at h
      · intro t _
        rfl

/-- Gap B1-b, tex 3281–3295, `PROVED` with the added hypothesis.  `Δ = Δ_f` (abelian) acts on the
points `P` (A-linearly, through `act`); `N = Gal(H_f/H_{f/q})`; `T` is a set of representatives of
`Δ/N` (so `T ≅ Δ_{f/q}`); `y_{f/q}` is `N`-fixed and the split norm relation (4.1) reads
`∑_{n ∈ N} n y_f = a_q y_{f/q} - σ_q y_{f/q} - σ_q⁻¹ y_{f/q}`.  If `θ` is trivial on `N` (i.e.
factors through `Δ_{f/q}`), then the twisted sums satisfy
`∑_{δ ∈ Δ} θ(δ) δ y_f = (a_q - θ(σ_q) - θ(σ_q)⁻¹) ∑_{t ∈ T} θ(t) t y_{f/q}`. -/
theorem B1b_twisted_split_norm {Δ A P : Type*} [CommGroup Δ] [Fintype Δ] [DecidableEq Δ]
    [CommRing A] [AddCommGroup P] [Module A P] (act : Δ →* Module.End A P)
    (N : Subgroup Δ) [DecidablePred (· ∈ N)] (T : Finset Δ)
    (hT : ∀ δ : Δ, ∃! t, t ∈ T ∧ t⁻¹ * δ ∈ N)
    (θ : Δ →* Aˣ) (hθN : ∀ n ∈ N, θ n = 1)
    (yf yq : P) (hyq : ∀ n ∈ N, act n yq = yq) (aq : ℤ) (σq : Δ)
    (hnorm : ∑ n ∈ univ.filter (· ∈ N), act n yf = aq • yq - act σq yq - act σq⁻¹ yq) :
    ∑ δ, (θ δ : A) • act δ yf =
      ((aq : A) - (θ σq : A) - ((θ σq)⁻¹ : Aˣ)) • ∑ t ∈ T, (θ t : A) • act t yq := by
  -- the summand `θ(δ) δ y_{f/q}` is invariant under right translation by `N`
  have hF : ∀ δ, ∀ n ∈ N, (θ (δ * n) : A) • act (δ * n) yq = (θ δ : A) • act δ yq := by
    intro δ n hn
    rw [map_mul θ δ n, hθN n hn, mul_one, map_mul act δ n, Module.End.mul_apply, hyq n hn]
  -- translating the representatives by `σ` multiplies the twisted sum by `θ(σ)⁻¹`
  have hshift : ∀ σ : Δ, ∑ t ∈ T, (θ t : A) • act (t * σ) yq =
      (((θ σ)⁻¹ : Aˣ) : A) • ∑ t ∈ T, (θ t : A) • act t yq := by
    intro σ
    have h := B1b_sum_transversal_mul_right N T hT (fun δ => (θ δ : A) • act δ yq) hF σ
    rw [← h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_smul, map_mul θ t σ, Units.val_mul, mul_comm (θ t : A), Units.inv_mul_cancel_left]
  -- decompose the sum over `Δ` along the cosets `t N` and apply the norm relation on each
  have hcoset : ∀ t ∈ T, ∑ n ∈ univ.filter (· ∈ N), (θ (t * n) : A) • act (t * n) yf =
      aq • ((θ t : A) • act t yq) - (θ t : A) • act (t * σq) yq -
        (θ t : A) • act (t * σq⁻¹) yq := by
    intro t _
    have h1 : ∀ n ∈ univ.filter (· ∈ N),
        (θ (t * n) : A) • act (t * n) yf = (θ t : A) • act t (act n yf) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [map_mul θ t n, hθN n hn.2, mul_one, map_mul act t n, Module.End.mul_apply]
    rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, ← map_sum, hnorm, map_sub, map_sub, map_zsmul,
      smul_sub, smul_sub, smul_comm (θ t : A) aq (act t yq), map_mul act t σq,
      map_mul act t σq⁻¹, Module.End.mul_apply, Module.End.mul_apply]
  rw [B1b_sum_eq_sum_transversal N T hT, Finset.sum_congr rfl hcoset, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum, hshift, hshift, map_inv, inv_inv, sub_smul,
    sub_smul, Int.cast_smul_eq_zsmul]
  abel

/-- The nontrivial character of `C₂ = Multiplicative (ZMod 2)` with values `±1`. -/
def signC2 : Multiplicative (ZMod 2) →* ℤˣ where
  toFun x := if x = 1 then 1 else -1
  map_one' := by simp
  map_mul' := by decide

open Classical in
/-- Gap B1-b, negative control, `PROVED`: without `θ` trivial on `N` the conclusion of
`B1b_twisted_split_norm` fails.  Take `Δ = N = C₂ = {1, s}`, `A = P = ℤ` with the trivial action,
`θ(s) = -1`, `y_f = y_{f/q} = 1`, `σ_q = 1`, `a_q = 4` and `T = {1}`.  Every other hypothesis holds
(the norm relation reads `1 + 1 = 4 - 1 - 1`), but the twisted sum is `1 - 1 = 0`, while the right
side is `(4 - 1 - 1)·1 = 2`. -/
theorem B1b_hypothesis_needed :
    let Δ := Multiplicative (ZMod 2)
    let act : Δ →* Module.End ℤ ℤ := 1
    (∀ δ : Δ, ∃! t, t ∈ ({1} : Finset Δ) ∧ t⁻¹ * δ ∈ (⊤ : Subgroup Δ)) ∧
    (∀ n ∈ (⊤ : Subgroup Δ), act n 1 = 1) ∧
    (∑ n ∈ univ.filter (· ∈ (⊤ : Subgroup Δ)), act n 1 = (4 : ℤ) • (1 : ℤ) - act 1 1 - act 1⁻¹ 1) ∧
    signC2 (Multiplicative.ofAdd 1) ≠ 1 ∧
    ∑ δ, (signC2 δ : ℤ) • act δ 1 ≠
      ((4 : ℤ) - (signC2 1 : ℤ) - ((signC2 1)⁻¹ : ℤˣ)) • ∑ t ∈ ({1} : Finset Δ),
        (signC2 t : ℤ) • act t 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro δ
    refine ⟨1, ⟨Finset.mem_singleton_self _, Subgroup.mem_top _⟩, ?_⟩
    rintro t ⟨ht, -⟩
    exact Finset.mem_singleton.mp ht
  · intro n _
    rfl
  · rw [Finset.filter_true_of_mem (fun x _ => Subgroup.mem_top x)]
    decide
  · decide
  · decide

end ZInQ.Manuscript.RC.HeegnerAlgebra

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

omit [Fintype (G ⧸ H)] in
/-- `R = θ ρ_T` is multiplicative (tex 3231, 3235), `PROVED`. -/
theorem Rtw_mul (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (g k : G) :
    Rtw H ρ θ (g * k) = Rtw H ρ θ g * Rtw H ρ θ k := by
  unfold Rtw
  rw [QuotientGroup.mk_mul, map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

omit [Fintype (G ⧸ H)] in
/-- On `H`, `R = ρ_T` (`θ` factors through `Δ = G/H`; tex 3204, 3231), `PROVED`. -/
theorem Rtw_of_mem (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (x : G) (hx : x ∈ H) :
    Rtw H ρ θ x = ρ x := by
  unfold Rtw
  rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one, Units.val_one, one_smul]

/-- The cocycle `h(g,δ) = r_{gδ}⁻¹ g r_δ` of a section `r` of `G → G/H` (tex 3222). -/
def hc (r : G ⧸ H → G) (g : G) (δ : G ⧸ H) : G := (r (QuotientGroup.mk g * δ))⁻¹ * g * r δ

omit [Fintype (G ⧸ H)] in
/-- `h(g,δ) ∈ H` (tex 3222), `PROVED`. -/
theorem hc_mem (r : G ⧸ H → G) (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ) (g : G)
    (δ : G ⧸ H) : hc H r g δ ∈ H := by
  unfold hc
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, hr, hr]
  group

omit [Fintype (G ⧸ H)] in
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

omit [Fintype (G ⧸ H)] in
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

omit [Fintype (G ⧸ H)] in
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

/-! ### Every degree: the transfer `𝒯_θ` and `d 𝒯_θ = 𝒯_θ d` (tex 3235–3244) -/

/-- The inhomogeneous differential in degree `n` for an action map `act` (tex 3235–3244), with
the formula of Mathlib's `inhomogeneousCochains.d`: for `g = (g₀,…,g_n)`,
`(dⁿ f)(g) = g₀ f(g₁,…,g_n) + ∑_{j=0}^{n} (-1)^{j+1} f(Fin.contractNth j (· * ·) g)`, where
`Fin.contractNth j (· * ·) g = (g₀,…,g_j g_{j+1},…,g_n)` for `j < n` and
`Fin.contractNth n (· * ·) g = (g₀,…,g_{n-1})`.  In degrees `0, 1, 2` it is `d0`, `d1`, `d2`
(`dn_eq_d0`, `dn_eq_d1`, `dn_eq_d2`). -/
def dn {Γ : Type*} [Mul Γ] {n : ℕ} (act : Γ → Module.End A M) (f : (Fin n → Γ) → M) :
    (Fin (n + 1) → Γ) → M :=
  fun g => act (g 0) (f (Fin.tail g)) +
    ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • f (Fin.contractNth j (· * ·) g)

/-- Degree-`n` transfer (H21), tex 3237–3242, for every `n` (tex 3235–3244):
`(𝒯_θ c)(g₁,…,g_n) = ∑_δ R(r_{g₁⋯g_n δ}) c(h(g₁,δ₁),…,h(g_n,δ_n))`, `δ_i = g_{i+1}⋯g_n δ`.
Here `g : Fin n → G` lists `g₁,…,g_n` as `g 0,…,g (n-1)`; the ordered product `g₁⋯g_n` is
`(List.ofFn g).prod`, and the coset paired with `g i` (that is, `δ_{i+1} = g_{i+2}⋯g_n δ`) is
`((List.ofFn g).drop (i + 1)).prod * δ`.  In degrees `0, 1, 2, 3` it is `T0`, `T1`, `T2`, `T3`
(`Tn_eq_T0`, `Tn_eq_T1`, `Tn_eq_T2`, `Tn_eq_T3`). -/
def Tn {n : ℕ} (c : (Fin n → H) → M) : (Fin n → G) → M :=
  fun g => ∑ δ, Rtw H ρ θ (r (QuotientGroup.mk (List.ofFn g).prod * δ))
    (c fun i => hH H r hr (g i) (QuotientGroup.mk ((List.ofFn g).drop (i.val + 1)).prod * δ))

/-- tex 3235–3244 (the cosets of tex 3237–3242), indexed from `0` and including the full
product: `sufCoset H g δ i = (g i ⋯ g (n-1)) δ`; thus `sufCoset H g δ 0 = (g 0 ⋯ g (n-1)) δ`, the
coset paired with `g i` in `Tn` is `sufCoset H g δ (i + 1)`, and `sufCoset H g δ n = δ`. -/
private def sufCoset {n : ℕ} (g : Fin n → G) (δ : G ⧸ H) (i : Fin (n + 1)) : G ⧸ H :=
  QuotientGroup.mk ((List.ofFn g).drop i.val).prod * δ

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: the empty suffix, `sufCoset H g δ n = δ`. -/
private theorem sufCoset_last {n : ℕ} (g : Fin n → G) (δ : G ⧸ H) :
    sufCoset H g δ (Fin.last n) = δ := by
  rw [sufCoset, Fin.val_last, List.drop_of_length_le List.length_ofFn.le, List.prod_nil,
    QuotientGroup.mk_one, one_mul]

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: the recursion `sufCoset H g δ i = (g i) (sufCoset H g δ (i + 1))`
(left multiplication in `G/H`). -/
private theorem sufCoset_castSucc {n : ℕ} (g : Fin n → G) (δ : G ⧸ H) (i : Fin n) :
    sufCoset H g δ i.castSucc = QuotientGroup.mk (g i) * sufCoset H g δ i.succ := by
  rw [sufCoset, sufCoset, Fin.val_castSucc, Fin.val_succ,
    List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn,
    List.prod_cons, QuotientGroup.mk_mul, mul_assoc]

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: `sufCoset H g δ` is the only sequence with last value `δ` that
satisfies the recursion of `sufCoset_castSucc`. -/
private theorem sufCoset_eq_of_rec {n : ℕ} (g : Fin n → G) (δ : G ⧸ H)
    (E : Fin (n + 1) → G ⧸ H) (hlast : E (Fin.last n) = δ)
    (hstep : ∀ i : Fin n, E i.castSucc = QuotientGroup.mk (g i) * E i.succ) :
    E = sufCoset H g δ := by
  funext i
  induction i using Fin.reverseInduction with
  | last => rw [hlast, sufCoset_last]
  | cast i ih => rw [hstep, sufCoset_castSucc, ih]

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: the cosets of `Fin.tail g` are those of `g`, shifted by one. -/
private theorem sufCoset_tail {n : ℕ} (g : Fin (n + 1) → G) (δ : G ⧸ H) (i : Fin (n + 1)) :
    sufCoset H (Fin.tail g) δ i = sufCoset H g δ i.succ := by
  rw [sufCoset, sufCoset, Fin.val_succ, List.ofFn_succ (f := g), List.drop_succ_cons]
  rfl

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: dropping the last entry `g n` of `g` and replacing `δ` by
`(g n) δ` does not change the cosets. -/
private theorem sufCoset_init {n : ℕ} (g : Fin (n + 1) → G) (δ : G ⧸ H) (i : Fin (n + 1)) :
    sufCoset H (Fin.init g) (QuotientGroup.mk (g (Fin.last n)) * δ) i =
      sufCoset H g δ i.castSucc := by
  refine congrFun (sufCoset_eq_of_rec H (Fin.init g) _ (fun i => sufCoset H g δ i.castSucc)
    ?_ ?_).symm i
  · show sufCoset H g δ (Fin.last n).castSucc = _
    rw [sufCoset_castSucc, Fin.succ_last, sufCoset_last]
  · intro k
    show sufCoset H g δ k.castSucc.castSucc = QuotientGroup.mk (g k.castSucc) *
      sufCoset H g δ k.succ.castSucc
    rw [sufCoset_castSucc H g δ k.castSucc, Fin.succ_castSucc]

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: merging `g j` and `g (j + 1)` (`j < n`) deletes the coset
`sufCoset H g δ (j + 1)`. -/
private theorem sufCoset_contractNth {n : ℕ} (g : Fin (n + 1) → G) (δ : G ⧸ H) (j : Fin n)
    (i : Fin (n + 1)) :
    sufCoset H (Fin.contractNth j.castSucc (· * ·) g) δ i =
      sufCoset H g δ (j.castSucc.succ.succAbove i) := by
  refine congrFun (sufCoset_eq_of_rec H _ δ
    (fun i => sufCoset H g δ (j.castSucc.succ.succAbove i)) ?_ ?_).symm i
  · show sufCoset H g δ (j.castSucc.succ.succAbove (Fin.last n)) = δ
    have hl : j.castSucc.succ ≤ (Fin.last n).castSucc := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last]; omega
    rw [Fin.succAbove_of_le_castSucc _ _ hl, Fin.succ_last, sufCoset_last]
  · intro k
    show sufCoset H g δ (j.castSucc.succ.succAbove k.castSucc) =
      QuotientGroup.mk (Fin.contractNth j.castSucc (· * ·) g k) *
        sufCoset H g δ (j.castSucc.succ.succAbove k.succ)
    rcases lt_trichotomy (k : ℕ) j with h | h | h
    · have h1 : (k : ℕ) < (j.castSucc : ℕ) := by simpa using h
      have h2 : k.castSucc.castSucc < j.castSucc.succ := by
        simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]; omega
      have h3 : k.succ.castSucc < j.castSucc.succ := by
        simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]; omega
      rw [Fin.contractNth_apply_of_lt _ _ _ _ h1, Fin.succAbove_of_castSucc_lt _ _ h2,
        Fin.succAbove_of_castSucc_lt _ _ h3, sufCoset_castSucc H g δ k.castSucc,
        Fin.succ_castSucc]
    · have h1 : (k : ℕ) = (j.castSucc : ℕ) := by simpa using h
      have h2 : k.castSucc.castSucc < j.castSucc.succ := by
        simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]; omega
      have h3 : j.castSucc.succ ≤ k.succ.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      rw [Fin.contractNth_apply_of_eq _ _ _ _ h1, Fin.succAbove_of_castSucc_lt _ _ h2,
        Fin.succAbove_of_le_castSucc _ _ h3, sufCoset_castSucc H g δ k.castSucc,
        Fin.succ_castSucc, sufCoset_castSucc H g δ k.succ, QuotientGroup.mk_mul, mul_assoc]
    · have h1 : (j.castSucc : ℕ) < (k : ℕ) := by simpa using h
      have h2 : j.castSucc.succ ≤ k.castSucc.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have h3 : j.castSucc.succ ≤ k.succ.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      rw [Fin.contractNth_apply_of_gt _ _ _ _ h1, Fin.succAbove_of_le_castSucc _ _ h2,
        Fin.succAbove_of_le_castSucc _ _ h3, Fin.succ_castSucc,
        sufCoset_castSucc H g δ k.succ]

/-- tex 3235–3244: the arguments `(h(g₁,δ₁),…,h(g_n,δ_n))` of `c` in `Tn` (tex 3237–3242),
`hArgs H r hr g δ i = h(g i, sufCoset H g δ (i + 1))`. -/
private def hArgs {n : ℕ} (g : Fin n → G) (δ : G ⧸ H) : Fin n → H :=
  fun i => hH H r hr (g i) (sufCoset H g δ i.succ)

/-- tex 3235–3244, `PROVED`: `Tn` written with `sufCoset` and `hArgs`. -/
private theorem Tn_eq_sum_hArgs {n : ℕ} (c : (Fin n → H) → M) (g : Fin n → G) :
    Tn H ρ θ r hr c g = ∑ δ, Rtw H ρ θ (r (sufCoset H g δ 0)) (c (hArgs H r hr g δ)) :=
  rfl

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: the face `0` of `hArgs`. -/
private theorem hArgs_tail {n : ℕ} (g : Fin (n + 1) → G) (δ : G ⧸ H) :
    Fin.tail (hArgs H r hr g δ) = hArgs H r hr (Fin.tail g) δ := by
  funext i
  show hH H r hr (g i.succ) (sufCoset H g δ i.succ.succ) =
    hH H r hr (g i.succ) (sufCoset H (Fin.tail g) δ i.succ)
  rw [sufCoset_tail]

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: the last face of `hArgs`. -/
private theorem hArgs_init {n : ℕ} (g : Fin (n + 1) → G) (δ : G ⧸ H) :
    Fin.init (hArgs H r hr g δ) =
      hArgs H r hr (Fin.init g) (QuotientGroup.mk (g (Fin.last n)) * δ) := by
  funext i
  show hH H r hr (g i.castSucc) (sufCoset H g δ i.castSucc.succ) =
    hH H r hr (g i.castSucc)
      (sufCoset H (Fin.init g) (QuotientGroup.mk (g (Fin.last n)) * δ) i.succ)
  rw [sufCoset_init, Fin.succ_castSucc]

omit [Fintype (G ⧸ H)] in
/-- tex 3235–3244, `PROVED`: the inner faces of `hArgs`, by `h(gk,δ) = h(g,kδ) h(k,δ)`
(tex 3229–3230). -/
private theorem hArgs_contractNth {n : ℕ} (g : Fin (n + 1) → G) (δ : G ⧸ H) (j : Fin n) :
    Fin.contractNth j.castSucc (· * ·) (hArgs H r hr g δ) =
      hArgs H r hr (Fin.contractNth j.castSucc (· * ·) g) δ := by
  funext k
  show Fin.contractNth j.castSucc (· * ·) (hArgs H r hr g δ) k =
    hH H r hr (Fin.contractNth j.castSucc (· * ·) g k)
      (sufCoset H (Fin.contractNth j.castSucc (· * ·) g) δ k.succ)
  rw [sufCoset_contractNth]
  rcases lt_trichotomy (k : ℕ) j with h | h | h
  · have h1 : (k : ℕ) < (j.castSucc : ℕ) := by simpa using h
    have h3 : k.succ.castSucc < j.castSucc.succ := by
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]; omega
    rw [Fin.contractNth_apply_of_lt _ _ _ _ h1, Fin.contractNth_apply_of_lt _ _ _ _ h1,
      Fin.succAbove_of_castSucc_lt _ _ h3]
    show hH H r hr (g k.castSucc) (sufCoset H g δ k.castSucc.succ) = _
    rw [Fin.succ_castSucc]
  · have h1 : (k : ℕ) = (j.castSucc : ℕ) := by simpa using h
    have h3 : j.castSucc.succ ≤ k.succ.castSucc := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
    rw [Fin.contractNth_apply_of_eq _ _ _ _ h1, Fin.contractNth_apply_of_eq _ _ _ _ h1,
      Fin.succAbove_of_le_castSucc _ _ h3]
    show hH H r hr (g k.castSucc) (sufCoset H g δ k.castSucc.succ) *
      hH H r hr (g k.succ) (sufCoset H g δ k.succ.succ) = _
    rw [Fin.succ_castSucc, sufCoset_castSucc, hH_mul]
  · have h1 : (j.castSucc : ℕ) < (k : ℕ) := by simpa using h
    have h3 : j.castSucc.succ ≤ k.succ.castSucc := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
    rw [Fin.contractNth_apply_of_gt _ _ _ _ h1, Fin.contractNth_apply_of_gt _ _ _ _ h1,
      Fin.succAbove_of_le_castSucc _ _ h3]
    rfl

/-- tex 3235–3244, `PROVED`: the last face `Fin.contractNth n` deletes the last entry. -/
private theorem contractNth_last_eq_init {α : Type*} {n : ℕ} (op : α → α → α)
    (g : Fin (n + 1) → α) : Fin.contractNth (Fin.last n) op g = Fin.init g := by
  funext k
  exact Fin.contractNth_apply_of_lt _ _ _ _ k.isLt

/-- (H21), tex 3243–3244 in every degree (tex 3235–3244), `PROVED`: `d 𝒯_θ = 𝒯_θ d` from
degree `n` to degree `n + 1`, for every `n`, where `d` is the inhomogeneous differential `dn` of
the twisted action `R = θ ρ_T` of `G` on the left and of `ρ_T` restricted to `H` on the right.
The face `0` uses `R(r_{gδ}) ρ_T(h(g,δ)) = R(g) R(r_δ)`, the inner faces use
`h(gk,δ) = h(g,kδ) h(k,δ)`, and the last face reindexes the sum over `δ` by left
multiplication with the last entry of `g`. -/
theorem Tn_comm_d {n : ℕ} (c : (Fin n → H) → M) :
    dn (Rtw H ρ θ) (Tn H ρ θ r hr c) = Tn H ρ θ r hr (dn (actH H ρ) c) := by
  funext g
  simp only [dn, Tn_eq_sum_hArgs, map_add, map_sum, map_zsmul, Finset.sum_add_distrib,
    Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun δ _ => ?_
    have h0 : sufCoset H g δ 0 =
        QuotientGroup.mk (g 0) * sufCoset H g δ (0 : Fin (n + 1)).succ :=
      sufCoset_castSucc H g δ 0
    rw [hArgs_tail, sufCoset_tail, h0]
    exact (Rtw_key H ρ θ r hr (g 0) _ _).symm
  · conv_rhs => rw [Finset.sum_comm]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun δ _ => ?_
      rw [hArgs_contractNth, sufCoset_contractNth, Fin.succ_succAbove_zero]
    · simp only [contractNth_last_eq_init, hArgs_init]
      symm
      refine Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk (g (Fin.last n)))) _ _
        fun δ => ?_
      simp only [Equiv.coe_mulLeft]
      rw [sufCoset_init, Fin.castSucc_zero]

/-- tex 3235–3244, `PROVED`: in degree `0`, `dn` is `d0`. -/
theorem dn_eq_d0 {Γ : Type*} [Mul Γ] (act : Γ → Module.End A M) (Q : M) (g : Fin 1 → Γ) :
    dn act (fun _ => Q) g = d0 act Q (g 0) := by
  simp [dn, d0, sub_eq_add_neg]

/-- tex 3235–3244, `PROVED`: in degree `1`, `dn` is `d1`. -/
theorem dn_eq_d1 {Γ : Type*} [Mul Γ] (act : Γ → Module.End A M) (b : Γ → M) (g : Fin 2 → Γ) :
    dn act (fun x => b (x 0)) g = d1 act b (g 0) (g 1) := by
  simp [dn, d1, Fin.sum_univ_two, Fin.contractNth, Fin.tail, sub_eq_add_neg, add_assoc]

/-- tex 3235–3244, `PROVED`: in degree `2`, `dn` is `d2`. -/
theorem dn_eq_d2 {Γ : Type*} [Mul Γ] (act : Γ → Module.End A M) (c : Γ → Γ → M)
    (g : Fin 3 → Γ) : dn act (fun x => c (x 0) (x 1)) g = d2 act c (g 0) (g 1) (g 2) := by
  simp [dn, d2, Fin.sum_univ_three, Fin.contractNth, Fin.tail, sub_eq_add_neg, add_assoc]

/-- tex 3235–3244, `PROVED`: in degree `0`, `Tn` is `T0`. -/
theorem Tn_eq_T0 (Q : M) (g : Fin 0 → G) : Tn H ρ θ r hr (fun _ => Q) g = T0 H ρ θ r Q := by
  simp [Tn, T0]

/-- tex 3235–3244, `PROVED`: in degree `1`, `Tn` is `T1`. -/
theorem Tn_eq_T1 (b : H → M) (g : Fin 1 → G) :
    Tn H ρ θ r hr (fun x => b (x 0)) g = T1 H ρ θ r hr b (g 0) := by
  simp [Tn, T1, List.ofFn_succ]

/-- tex 3235–3244, `PROVED`: in degree `2`, `Tn` is `T2`. -/
theorem Tn_eq_T2 (c : H → H → M) (g : Fin 2 → G) :
    Tn H ρ θ r hr (fun x => c (x 0) (x 1)) g = T2 H ρ θ r hr c (g 0) (g 1) := by
  simp [Tn, T2, List.ofFn_succ]

/-- tex 3235–3244, `PROVED`: in degree `3`, `Tn` is `T3`. -/
theorem Tn_eq_T3 (c : H → H → H → M) (g : Fin 3 → G) :
    Tn H ρ θ r hr (fun x => c (x 0) (x 1) (x 2)) g = T3 H ρ θ r hr c (g 0) (g 1) (g 2) := by
  simp [Tn, T3, List.ofFn_succ, mul_assoc]

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
/-- Gap B1-b, negative control, tex 3289–3295, `PROVED`: without `θ` trivial on `N` the conclusion of
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

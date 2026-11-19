import ZInQKernel.Contrib.CloudB3E2Norm.H20Actual

/-!
# The bridge from `Δ_f` to `im Ψ_i`: transitivity of the twisted transfer of Kummer classes

Manuscript `diophantine_zq.tex`, tex 3203–3250 (the class `P_{I,m}` over `K` is Shapiro from
`H_f` followed by the coefficient map (H20); its degree-one cochain is the twisted transfer
`𝒯_θ` over `G_K/G_{H_f}`, tex 3237–3242) and tex 3257–3262 (the twisted norm `∑_δ χ(δ) δ Q` is a
point over the lower field).

The manuscript's class is the transfer over `Δ_f = G/G_{H_f}` with coefficients `ℤ[Δ_f]` (or
`A[Δ_f]`). `H20Actual.lean` works with the smaller group `im Ψ_i = G/ker π` (`π` the corestriction of
`Ψ_i`, `ker π = G_L` for the field `L ⊆ H_f` cut out by `Ψ_i`). This file proves that nothing is lost
in the passage, at the level of cochains:

* **`transfer_kummer_bridge`** (PROVED): for `H_R ≤ H_P` normal of finite index and characters
  with `θ_R = θ_P` on `G` (the character factors through `G/H_P`), the transfer over `G/H_R` of the
  Kummer cocycle of `Q_R` (`k Q_R = y_R`, `y_R` fixed by `H_R`) equals the transfer over `G/H_P` of the
  Kummer cocycle of any `Q_P` with `k Q_P = ∑_τ ρ(t_τ) y_R` (the norm of `y_R` from `H_R` to `H_P`, i.e.
  from `H_f` to `L`), up to the coboundary of the explicit `k`-torsion element
  `b = ∑_δ R(r_δ) Q_R − ∑_δ R(r'_δ) Q_P`.
* **`bridge_coeff`** (PROVED): the same after a semilinear equivariant coefficient change
  `c : D₁ → D₂` along `φ : k₁ → k₂` (for the text, `ℤ[Δ_f] → ℤ[im Ψ_i]`, `[δ] ↦ [Ψ_i(δ)]`,
  `h20RingHom`), when the pushed character factors through `G/H_P`.
* **`bridge_class`** (PROVED): for genuine coefficient modules, a class over `k₁` carried to the
  `Δ_f`-transfer of `κ(Q_f)` is pushed to a class carried to the `im Ψ_i`-transfer of `κ(Q_L)` plus
  `d⁰` of a genuine element: the input `hz` of `LocalIdentity.lean` / `H20Actual.lean` at `H = ker π`
  is satisfied by the pushed class up to a coboundary.
* **`term_fixed_of_mem`**, **`locMap_mem_ker_movingPi`** (PROVED): at `v ∈ P` (where `Ψ_i` is
  trivial, ELLIOT) the decomposition group lies in `ker π = G_L`, so the orbit (local-norm)
  conditions of `LocalIdentity.lean` at the `im Ψ_i` level are trivial orbits: every term is
  invariant under the twisted action of `G_{K_v}` (that it is a point of the local twist over `K_v`,
  in RC29's plain Kummer image, is `LocalTwistIdentification` with `hreal`).
* Non-vacuity: `nonVacuity_bridge`.

**How the conditions compare, and which the text uses.** At the `Δ_f` level (Shapiro from `H_f`)
the local condition at `v ∈ P` is the induced one: a sum over the places of `H_f` above `v` (the
`G_{K_v}`-orbits on `Δ_f`) of corestricted Kummer images of points over the completions of `H_f`
(the local Mackey formula, tex 3251–3256). After the push `[δ] ↦ [Ψ_i(δ)]` the orbits are those of
`G_{K_v}` on `im Ψ_i`, which are singletons because `Ψ_i` is trivial on `G_{K_v}` (tex 2729, 3431):
the orbit sums become twisted norms `∑_{δ ∈ O} χ(δ) δ Q`, points of the twist `B = E^{(h)}` over `K_v`
(tex 3257–3262, `KummerPush.old_kummer_survives`), and the condition is the plain Kummer condition of
`B` over `K_v`. The text's stage Selmer complex uses the latter, the actual Kummer condition of
paragraph 5 extended to `A_i` ("Thus the old Kummer conditions proved in paragraph 5 survive (H20)",
tex 3262–3270), i.e. RC29's `actualKummerAtS`/`actLCondA`. The bridge above works at the cochain
level (transitivity of the transfer), so no `Δ_f`-level local condition has to be formalized.

So the remaining inputs at the `im Ψ_i` level are the ones already named (`LocalTwistIdentification`,
the realization `hreal` at `H = ker π`, now of the norms `N_{H_f/L}` of the Heegner points); no
`Δ_f`-level local conditions are needed. Not packaged here: the specialization to the actual
quotient and coefficient maps, and the construction of the `selCx` classes and the Shapiro-level
identity `h₁` required by `hzR_stage_actual` (the next step).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer

set_option linter.unusedSectionVars false

section Bridge

variable {G : Type*} [Group G] {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M)
  (HP HR : Subgroup G) [HP.Normal] [HR.Normal] [Fintype (G ⧸ HP)] [Fintype (G ⧸ HR)]
  (rP : G ⧸ HP → G) (hrP : ∀ δ, ((rP δ : G) : G ⧸ HP) = δ)
  (rR : G ⧸ HR → G) (hrR : ∀ δ, ((rR δ : G) : G ⧸ HR) = δ)
  (θP : G ⧸ HP →* Aˣ) (θR : G ⧸ HR →* Aˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : G) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

/-- **The bridge boundary** `b = ∑_δ R(r_δ) Q_R − ∑_δ R(r'_δ) Q_P`. Kind: definition. -/
def bridgeBoundary (QR QP : M) : M := wsum ρ HR rR θR QR - wsum ρ HP rP θP QP

include hrP hrR hU ht in
/-- **Transitivity of the twisted transfer of Kummer classes** (PROVED; tex 3237–3262): with
`θ_R = θ_P` on `G`, `k Q_R = y_R` (`y_R` fixed by `H_R`) and `k Q_P = ∑_τ ρ(t_τ) y_R`,
`𝒯^{H_R}(κ(Q_R)) = 𝒯^{H_P}(κ(Q_P)) + (R(g) b − b)` with `k b = 0`. -/
theorem transfer_kummer_bridge (hle : HR ≤ HP)
    (hθ : ∀ x : G, ((θR (x : G ⧸ HR) : Aˣ) : A) = θP (x : G ⧸ HP))
    (k : ℤ) {yR QR QP : M} (hQR : k • QR = yR) (hQP : k • QP = ∑ τ : HP ⧸ U, ρ (t τ : G) yR)
    (hfixR : ∀ h ∈ HR, ρ h yR = yR) :
    (∀ g : Fin 1 → G, T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g =
        T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g +
          (R HR ρ θR (g 0) (bridgeBoundary ρ HP HR rP rR θP θR QR QP) -
            bridgeBoundary ρ HP HR rP rR θP θR QR QP)) ∧
      k • bridgeBoundary ρ HP HR rP rR θP θR QR QP = 0 := by
  have hRR : ∀ x : G, R HR ρ θR x = R HP ρ θP x := fun x => by simp only [R, hθ]
  obtain ⟨hkR, hTR⟩ := kummer_weighted_sum HR rR hrR ρ θR k yR QR hQR
  obtain ⟨hkP, hTP⟩ := kummer_weighted_sum HP rP hrP ρ θP k _ QP hQP
  refine ⟨fun g => ?_, ?_⟩
  · have e1 : kummerCochain ρ HR QR = fun x => ρ (x 0 : G) QR - QR := rfl
    have e2 : kummerCochain ρ HP QP = fun x => ρ (x 0 : G) QP - QP := rfl
    rw [e1, e2, hTR g, hTP g, bridgeBoundary, map_sub, hRR (g 0), wsum, wsum]
    abel
  · have hR' : k • wsum ρ HR rR θR QR = wsum ρ HR rR θR yR := hkR
    have hP' : k • wsum ρ HP rP θP QP = wsum ρ HP rP θP (∑ τ : HP ⧸ U, ρ (t τ : G) yR) := hkP
    rw [bridgeBoundary, smul_sub, hR', hP',
      wsum_inflation ρ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ hfixR, sub_self]

end Bridge

section Coeff

variable {G : Type*} [Group G] {k₁ k₂ : Type*} [CommRing k₁] [CommRing k₂] (φ : k₁ →+* k₂)
  {D₁ D₂ : Type*} [AddCommGroup D₁] [Module k₁ D₁] [AddCommGroup D₂] [Module k₂ D₂]
  (ρ₁ : G →* Module.End k₁ D₁) (ρ₂ : G →* Module.End k₂ D₂) (c : D₁ →ₛₗ[φ] D₂)
  (HP HR : Subgroup G) [HP.Normal] [HR.Normal] [Fintype (G ⧸ HP)] [Fintype (G ⧸ HR)]
  (rP : G ⧸ HP → G) (hrP : ∀ δ, ((rP δ : G) : G ⧸ HP) = δ)
  (rR : G ⧸ HR → G) (hrR : ∀ δ, ((rR δ : G) : G ⧸ HR) = δ)
  (θ₁ : G ⧸ HR →* k₁ˣ) (θR : G ⧸ HR →* k₂ˣ) (θP : G ⧸ HP →* k₂ˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : G) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

include hrP hrR hU ht in
/-- **The bridge after the coefficient change** (PROVED; tex 3203–3262): for `φ ∘ θ₁ = θ_R` and
`θ_R = θ_P` on `G` (the pushed character factors through `G/H_P`), and an equivariant semilinear
`c`, `c(𝒯^{H_R}_{θ₁}(κ(Q_f))) = 𝒯^{H_P}_{θ_P}(κ(Q_L)) + (R(g) b − b)` with `k b = 0`, for any
`Q_L` with `k Q_L = ∑_τ ρ₂(t_τ) c(y_f)`. -/
theorem bridge_coeff (hle : HR ≤ HP) (hφ : ∀ x, φ (θ₁ x : k₁) = θR x)
    (hθ : ∀ x : G, ((θR (x : G ⧸ HR) : k₂ˣ) : k₂) = θP (x : G ⧸ HP))
    (hc : ∀ g x, c (ρ₁ g x) = ρ₂ g (c x)) (k : ℤ) {yf Qf : D₁} {QL : D₂}
    (hQf : k • Qf = yf) (hfix : ∀ h ∈ HR, ρ₁ h yf = yf)
    (hQL : k • QL = ∑ τ : HP ⧸ U, ρ₂ (t τ : G) (c yf)) :
    (∀ g : Fin 1 → G, c (T HR rR hrR ρ₁ θ₁ 1 (kummerCochain ρ₁ HR Qf) g) =
        T HP rP hrP ρ₂ θP 1 (kummerCochain ρ₂ HP QL) g +
          (R HR ρ₂ θR (g 0) (bridgeBoundary ρ₂ HP HR rP rR θP θR (c Qf) QL) -
            bridgeBoundary ρ₂ HP HR rP rR θP θR (c Qf) QL)) ∧
      k • bridgeBoundary ρ₂ HP HR rP rR θP θR (c Qf) QL = 0 := by
  have hcQ : k • c Qf = c yf := by rw [← hQf, map_zsmul]
  have hcfix : ∀ h ∈ HR, ρ₂ h (c yf) = c yf := fun h hh => by rw [← hc, hfix h hh]
  obtain ⟨h1, h2⟩ := transfer_kummer_bridge ρ₂ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ k hcQ
    hQL hcfix
  exact ⟨fun g => by rw [transfer_kummer_coeff HR rR hrR φ ρ₁ ρ₂ θ₁ θR c hφ hc]; exact h1 g, h2⟩

include hrP hrR hU ht in
/-- **The pushed class satisfies the `im Ψ_i`-level input up to a coboundary** (PROVED): if `ι₁`
carries `z` to the `Δ_f`-transfer of `κ(Q_f)`, then for a coefficient map `f : M₁ → M₂` with
`ι₂ ∘ f = c ∘ ι₁`, `ι₂` equivariant for `R_{θ_P}` and every `k`-torsion element of `D₂` in `ι₂(M₂)`,
there is `m₀ ∈ M₂` with `ι₂(f(z(g)) − (g m₀ − m₀)) = 𝒯^{H_P}_{θ_P}(κ(Q_L))(g)`. -/
theorem bridge_class (hle : HR ≤ HP) (hφ : ∀ x, φ (θ₁ x : k₁) = θR x)
    (hθ : ∀ x : G, ((θR (x : G ⧸ HR) : k₂ˣ) : k₂) = θP (x : G ⧸ HP))
    (hc : ∀ g x, c (ρ₁ g x) = ρ₂ g (c x)) (k : ℤ) {yf Qf : D₁} {QL : D₂}
    (hQf : k • Qf = yf) (hfix : ∀ h ∈ HR, ρ₁ h yf = yf)
    (hQL : k • QL = ∑ τ : HP ⧸ U, ρ₂ (t τ : G) (c yf))
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k₁ M₁] [AddCommGroup M₂] [Module k₂ M₂]
    [DistribMulAction G M₂] (f : M₁ →ₛₗ[φ] M₂) (ι₁ : M₁ →ₗ[k₁] D₁) (ι₂ : M₂ →ₗ[k₂] D₂)
    (hιc : ∀ x, ι₂ (f x) = c (ι₁ x)) (hι₂ : ∀ (g : G) (m : M₂), ι₂ (g • m) = R HP ρ₂ θP g (ι₂ m))
    (htors : ∀ x : D₂, k • x = 0 → ∃ m : M₂, ι₂ m = x)
    (z : (Fin 1 → G) → M₁)
    (hz : ∀ g, ι₁ (z g) = T HR rR hrR ρ₁ θ₁ 1 (kummerCochain ρ₁ HR Qf) g) :
    ∃ m₀ : M₂, ∀ g : Fin 1 → G,
      ι₂ (f (z g) - (g 0 • m₀ - m₀)) = T HP rP hrP ρ₂ θP 1 (kummerCochain ρ₂ HP QL) g := by
  obtain ⟨h1, h2⟩ := bridge_coeff φ ρ₁ ρ₂ c HP HR rP hrP rR hrR θ₁ θR θP U hU t ht hle hφ hθ hc k
    hQf hfix hQL
  obtain ⟨m₀, hm₀⟩ := htors _ h2
  refine ⟨m₀, fun g => ?_⟩
  have hRR : R HR ρ₂ θR (g 0) = R HP ρ₂ θP (g 0) := by simp only [R, hθ]
  rw [map_sub, map_sub, hι₂, hm₀, hιc, hz, h1 g, hRR]
  abel

end Coeff

/-! ### At the places of `P` the orbit conditions are the plain Kummer conditions -/

section Orbits

variable {G : Type*} [Group G] {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (H : Subgroup G) [H.Normal] (r : G ⧸ H → G)
  (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (θ : G ⧸ H →* Aˣ)

include hr in
/-- **When the decomposition group lies in `H`, every orbit is a singleton and every term of the
weighted sum is a local point** (PROVED): for `g ∈ H` and `y` fixed by `H`,
`R(g)(R(r_δ) y) = R(r_δ) y`. With `H = ker π = G_L` and `g` in the image of `G_{K_v}`, `v ∈ P`
(`locMap_mem_ker_movingPi`), the orbit (local-norm) decomposition of `LocalIdentity.lean` at `v`
is trivial: each term is invariant under the twisted action of `G_{K_v}`. That such an invariant
term is the image of a point of the local twist over `K_v`, lying in RC29's Kummer image, is the
content of `LocalTwistIdentification` and the realization `hreal` (not proved here). -/
theorem term_fixed_of_mem {g : G} (hg : g ∈ H) (δ : G ⧸ H) {y : M}
    (hy : ∀ h ∈ H, ρ h y = y) : R H ρ θ g (R H ρ θ (r δ) y) = R H ρ θ (r δ) y := by
  have h1 : ((g : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff g).2 hg
  have := orbitSum_fixed ρ H r hr θ g {δ} (fun δ' hδ' => by simp_all)
    (fun δ' hδ' => by simp_all) hy
  simpa [orbitSum] using this

end Orbits

/-- **The decomposition groups at `P` lie in `ker Ψ_i`** (PROVED from the ELLIOT input, for
`Δ = im Ψ_i`): `p_v(σ) ∈ ker π` for `v ∈ P`. -/
theorem locMap_mem_ker_movingPi {K : Type} [Field K] [NumberField K]
    {S₀ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ)
    (Ψ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀ →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
    {P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (hΨ : ∀ v ∈ P, ∀ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K v,
      Ψ (ZInQ.Manuscript.RC.SelmerComplex.locMap K S₀ v σ) = 1)
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∈ P)
    (σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K v) :
    ZInQ.Manuscript.RC.SelmerComplex.locMap K S₀ v σ ∈ (movingPi i Ψ).ker :=
  MonoidHom.mem_ker.2 (Subtype.ext (hΨ v hv σ))

/-! ### Non-vacuity -/

/-- **Non-vacuity of the hypotheses of `transfer_kummer_bridge`**: the trivial group with
`H_R = H_P = ⊤`, trivial characters, `k = 1`, `Q_R = Q_P = y_R = 0`. Kind: PROVED. -/
theorem nonVacuity_bridge :
    ∃ (ρ : Unit →* Module.End ℤ ℤ) (HP HR : Subgroup Unit) (_ : HP.Normal) (_ : HR.Normal)
      (_ : Fintype (Unit ⧸ HP)) (_ : Fintype (Unit ⧸ HR)) (rP : Unit ⧸ HP → Unit)
      (rR : Unit ⧸ HR → Unit) (θP : Unit ⧸ HP →* ℤˣ) (θR : Unit ⧸ HR →* ℤˣ) (U : Subgroup HP)
      (_ : Fintype (HP ⧸ U)) (t : HP ⧸ U → HP) (yR QR QP : ℤ),
      (∀ δ, ((rP δ : Unit) : Unit ⧸ HP) = δ) ∧ (∀ δ, ((rR δ : Unit) : Unit ⧸ HR) = δ) ∧
      (∀ h : HP, h ∈ U ↔ (h : Unit) ∈ HR) ∧
      (∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ) ∧ HR ≤ HP ∧
      (∀ x : Unit, ((θR (x : Unit ⧸ HR) : ℤˣ) : ℤ) = θP (x : Unit ⧸ HP)) ∧
      (1 : ℤ) • QR = yR ∧ (1 : ℤ) • QP = ∑ τ : HP ⧸ U, ρ (t τ : Unit) yR ∧
      (∀ h ∈ HR, ρ h yR = yR) := by
  classical
  refine ⟨1, ⊤, ⊤, inferInstance, inferInstance, Fintype.ofFinite _, Fintype.ofFinite _,
    fun _ => (), fun _ => (), 1, 1, ⊤, Fintype.ofFinite _, fun _ => 1, 0, 0, 0,
    fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _, fun _ => by simp,
    fun _ => Subsingleton.elim _ _, le_rfl, fun _ => rfl, rfl, ?_, fun _ _ => rfl⟩
  simp

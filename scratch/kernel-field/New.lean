/-! # Part 6 (new, task kernel-field): `KernelFieldExists` from the G4 leaves and two glue Props

Everything above is a verbatim copy (see `assemble.sh`). This part proves
`G0ModField.KernelField.kernelFieldExists_of_pieces`:

  `HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
  `RaynaudCriterion`, `TorsionStructure` (the kernel's leaves, used by `QML3.goodReduction`)
  + `ConjMapsOnHomField` (glue: the conjugacy maps `m_σ = μ_σ ∘ σ` on the Hom field, with an
    integral discrepancy) + `TorsionCountPts` (glue: `|A(ℚ̄)[n]| = n⁴` for abelian surfaces over
    subfields of `ℚ̄`)
  ⟹ `KernelFieldExists` (g0-mod-field's statement, unchanged).

* §6.1 `conjugacyData_of_maps`: pure algebra. The rational discrepancy `c`, its cocycle identity,
  inflation, `c(1,1) = 1` and the kernel-size identity `|ker m_σ||ker m_τ| = c⁴|ker m_στ|` all
  follow from the maps, an integral relation `d·m_σ m_τ = n·m_στ`, and `|V[n]| = n⁴`.
* §6.2 `kernelField_core`: `homField_core` with the kernel field `E = ℚ̄^{ker ρ}` and the finite
  group `G = ρ(G_ℚ) ≤ GL_r(ℤ)` exposed (`[E:ℚ] = |G|`).
* §6.3 `kernelField_of_model`: G4 (g4-weilres + inertia-homs + morph-descend) in
  `KernelFieldOut`'s shape: `r ≤ 16F₀²`, `G`, `E` unramified outside `T`, and `G_{E⊔K}` fixes
  every homomorphism between the conjugates of `A`.
* §6.4 the hypotheses of G4 on a rational fibre: `hdim` from `G0Dim.dim_baseChange` (g0-dim,
  proved), `hgood` from `QML3.goodReduction` (leaves NOS, Raynaud, TorsionStructure), `hK` from
  `galUnramifiedOutside_iff`.
* §6.5 the remaining glue Props and the headline.
-/

section Part61

open CategoryTheory AlgebraicGeometry Limits
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-! ## §6.1 The discrepancy: pure algebra -/

section Algebra

variable {V : Type*} [AddCommGroup V]

/-- `V[n]`, the `n`-torsion subgroup. -/
abbrev tors (V : Type*) [AddCommGroup V] (n : ℕ) : AddSubgroup V := (n • AddMonoidHom.id V).ker

/-- `|V[n]| = n⁴` for every `n ≥ 1` (the `ℚ̄`-points of an abelian surface in characteristic 0). -/
def TorsCount (V : Type*) [AddCommGroup V] : Prop :=
  ∀ n : ℕ, 0 < n → Nat.card (tors V n) = n ^ 4

theorem mem_tors {n : ℕ} {x : V} : x ∈ tors V n ↔ n • x = 0 := by
  simp [tors, AddMonoidHom.mem_ker]

theorem zsmul_eq_zero_iff_natAbs {d : ℤ} {y : V} : d • y = 0 ↔ d.natAbs • y = 0 := by
  rcases Int.natAbs_eq d with h | h
  · conv_lhs => rw [h]
    rw [natCast_zsmul]
  · conv_lhs => rw [h]
    rw [neg_smul, neg_eq_zero, natCast_zsmul]

/-- A group with `|V[n]| = n⁴` has no nonzero integer exponent. -/
theorem eq_zero_of_forall_zsmul (hT : TorsCount V) {k : ℤ} (hk : ∀ x : V, k • x = 0) : k = 0 := by
  by_contra hk0
  set N := k.natAbs with hN
  have hNpos : 0 < N := Int.natAbs_pos.mpr hk0
  have h1 : tors V N = ⊤ := by
    ext x; simp only [mem_tors, AddSubgroup.mem_top, iff_true]
    exact zsmul_eq_zero_iff_natAbs.mp (hk x)
  have h2 : tors V (2 * N) = ⊤ := by
    ext x; simp only [mem_tors, AddSubgroup.mem_top, iff_true]
    have hx : x ∈ tors V N := by rw [h1]; exact AddSubgroup.mem_top x
    rw [mem_tors] at hx
    rw [mul_smul, hx, smul_zero]
  have c1 := hT N hNpos
  have c2 := hT (2 * N) (by omega)
  rw [h1] at c1
  rw [h2, c1] at c2
  have h16 : (2 * N) ^ 4 = 16 * N ^ 4 := by ring
  rw [h16] at c2
  have hN4 : 0 < N ^ 4 := pow_pos hNpos 4
  omega

/-- `f = q·g` rationally: `d·f = n·g` with `q = n/d`. -/
def Rel (f g : V →+ V) (q : ℚ) : Prop := ∃ n d : ℤ, d ≠ 0 ∧ q = n / d ∧ d • f = n • g

theorem rel_unique (hT : TorsCount V) {f g : V →+ V} (hg : Function.Surjective g) {q q' : ℚ}
    (h : Rel f g q) (h' : Rel f g q') : q = q' := by
  obtain ⟨n, d, hd, rfl, e⟩ := h
  obtain ⟨n', d', hd', rfl, e'⟩ := h'
  have key : ∀ y : V, (d' * n - d * n') • y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    have a := DFunLike.congr_fun e x
    have b := DFunLike.congr_fun e' x
    simp only [AddMonoidHom.smul_apply] at a b
    rw [sub_smul, mul_smul, mul_smul, ← a, ← b, smul_comm d' d, sub_self]
  have := eq_zero_of_forall_zsmul hT key
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hdq' : (d' : ℚ) ≠ 0 := by exact_mod_cast hd'
  rw [div_eq_div_iff hdq hdq']
  have : (d' : ℚ) * n = d * n' := by exact_mod_cast sub_eq_zero.mp this
  linarith

theorem rel_comp_right {f g : V →+ V} {q : ℚ} (h : Rel f g q) (k : V →+ V) :
    Rel (f.comp k) (g.comp k) q := by
  obtain ⟨n, d, hd, hq, e⟩ := h
  refine ⟨n, d, hd, hq, AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e (k x)
  simpa only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply] using a

theorem rel_comp_left {f g : V →+ V} {q : ℚ} (h : Rel f g q) (k : V →+ V) :
    Rel (k.comp f) (k.comp g) q := by
  obtain ⟨n, d, hd, hq, e⟩ := h
  refine ⟨n, d, hd, hq, AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e x
  simp only [AddMonoidHom.smul_apply] at a
  simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, ← map_zsmul, a]

theorem rel_trans {f g k : V →+ V} {q q' : ℚ} (h : Rel f g q) (h' : Rel g k q') :
    Rel f k (q * q') := by
  obtain ⟨n, d, hd, rfl, e⟩ := h
  obtain ⟨n', d', hd', rfl, e'⟩ := h'
  refine ⟨n * n', d * d', mul_ne_zero hd hd', by push_cast; rw [div_mul_div_comm],
    AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e x
  have b := DFunLike.congr_fun e' x
  simp only [AddMonoidHom.smul_apply] at a b ⊢
  rw [mul_comm d d', mul_smul, a, smul_comm, b, ← mul_smul]

theorem rel_self (f : V →+ V) : Rel f f 1 := ⟨1, 1, one_ne_zero, by simp, rfl⟩

/-- `|f⁻¹(H)| = |H|·|ker f|` for surjective `f`. -/
theorem card_comap {f : V →+ V} (hf : Function.Surjective f) (H : AddSubgroup V) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  let g : H.comap f →+ H := f.addSubgroupComap H
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have e1 : (H.comap f ⧸ g.ker) ≃+ H := QuotientAddGroup.quotientKerEquivOfSurjective g hg
  have e2 : g.ker ≃ f.ker :=
    { toFun := fun x => ⟨x.1.1, AddMonoidHom.mem_ker.mpr
        (congrArg Subtype.val (AddMonoidHom.mem_ker.mp x.2))⟩
      invFun := fun y => ⟨⟨y.1, by
          show f y.1 ∈ H
          rw [AddMonoidHom.mem_ker.mp y.2]; exact H.zero_mem⟩,
        AddMonoidHom.mem_ker.mpr (Subtype.ext (AddMonoidHom.mem_ker.mp y.2))⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, Nat.card_congr e1.toEquiv,
    Nat.card_congr e2]

theorem card_ker_comp {f g : V →+ V} (hg : Function.Surjective g) :
    Nat.card (f.comp g).ker = Nat.card f.ker * Nat.card g.ker := by
  have : (f.comp g).ker = f.ker.comap g := by
    ext x; simp [AddMonoidHom.mem_ker]
  rw [this, card_comap hg]

theorem card_ker_zsmul (hT : TorsCount V) {f : V →+ V} (hf : Function.Surjective f) {d : ℤ}
    (hd : d ≠ 0) : Nat.card (d • f).ker = d.natAbs ^ 4 * Nat.card f.ker := by
  have : (d • f).ker = (tors V d.natAbs).comap f := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.smul_apply, AddSubgroup.mem_comap, mem_tors]
    exact zsmul_eq_zero_iff_natAbs
  rw [this, card_comap hf, hT _ (Int.natAbs_pos.mpr hd)]

/-- **The kernel identity from the integral relation** (`deg(d·φ) = d⁴ deg φ` on a surface). -/
theorem card_identity (hT : TorsCount V) {f g h : V →+ V} (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hh : Function.Surjective h) {n d : ℤ} (hn : n ≠ 0) (hd : d ≠ 0)
    (e : d • f.comp g = n • h) :
    (Nat.card f.ker : ℚ) * Nat.card g.ker = ((n : ℚ) / d) ^ 4 * Nat.card h.ker := by
  have h1 : Nat.card (d • f.comp g).ker = d.natAbs ^ 4 * Nat.card (f.comp g).ker :=
    card_ker_zsmul hT (f := f.comp g) (hf.comp hg) hd
  have h2 := card_ker_zsmul hT hh hn
  rw [card_ker_comp hg, e] at h1
  rw [h1] at h2
  have hq : ((d.natAbs : ℚ)) ^ 4 = (d : ℚ) ^ 4 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Even.pow_abs ⟨2, rfl⟩]
  have hq' : ((n.natAbs : ℚ)) ^ 4 = (n : ℚ) ^ 4 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Even.pow_abs ⟨2, rfl⟩]
  have h3 : ((d.natAbs ^ 4 * (Nat.card f.ker * Nat.card g.ker) : ℕ) : ℚ) =
      ((n.natAbs ^ 4 * Nat.card h.ker : ℕ) : ℚ) := by rw [h2]
  push_cast at h3
  rw [hq, hq'] at h3
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [div_pow]
  field_simp
  linarith

end Algebra

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem act_mul (σ τ : GQ) (x : Qbar) : act (σ * τ) x = act σ (act τ x) := rfl

theorem act_inv_act (σ : GQ) (x : Qbar) : act σ⁻¹ (act σ x) = x := by
  rw [← act_mul, inv_mul_cancel]; rfl

/-- **§6.1, the reduction of `ConjugacyData` to the maps (proved).** For `L` finite Galois and
`A/L` with `|A(ℚ̄)[n]| = n⁴`: maps `m_σ` on `A(ℚ̄)` with `ConjugacyData`'s clauses on the Galois
action, inflation, commutation with `End_L(A)`, surjectivity/finite kernel and algebraicity, and
an integral relation `d·m_σ m_τ = n·m_στ` (`d ≠ 0`), carry a rational discrepancy `c` with all of
`ConjugacyData`: `c = n/d` is well defined (`rel_unique`), `≠ 0`, a 2-cocycle, inflated from
`Gal(L/ℚ)`, `c(1,1) = 1`, and `|ker m_σ||ker m_τ| = c⁴|ker m_στ|`. -/
theorem conjugacyData_of_maps (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (hgal : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hinfl : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (hend : ∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ))
    (hfin : ∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite)
    (hdisc : ∀ σ τ, ∃ n d : ℤ, d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ))
    (halg : ∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ) :
    ∃ c : GQ → GQ → ℚ, ConjugacyData L A m c := by
  choose n d hd hnd using hdisc
  let c : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have hsurj : ∀ σ, Function.Surjective (m σ) := fun σ => (hfin σ).1
  have hR : ∀ σ τ, Rel ((m σ).comp (m τ)) (m (σ * τ)) (c σ τ) :=
    fun σ τ => ⟨n σ τ, d σ τ, hd σ τ, rfl, hnd σ τ⟩
  have hn : ∀ σ τ, n σ τ ≠ 0 := by
    intro σ τ hn0
    have key : ∀ y : PtQ L A, d σ τ • y = 0 := by
      intro y
      obtain ⟨x, rfl⟩ := ((hsurj σ).comp (hsurj τ)) y
      simp only [Function.comp_apply]
      have a := DFunLike.congr_fun (hnd σ τ) x
      rw [hn0] at a
      simpa only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, zero_smul] using a
    exact hd σ τ (eq_zero_of_forall_zsmul hT key)
  have hnorm : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hone : (1 : GQ) ∈ GQL L := (GQL L).one_mem
  refine ⟨c, hgal, hinfl, hend, hfin, fun σ τ => ⟨div_ne_zero (by exact_mod_cast hn σ τ)
    (by exact_mod_cast hd σ τ), n σ τ, d σ τ, hd σ τ, rfl, hnd σ τ⟩, ?_, ?_, ?_, ?_, halg⟩
  · -- the cocycle identity
    intro σ τ ρ
    have r1 := rel_trans (rel_comp_right (hR σ τ) (m ρ)) (hR (σ * τ) ρ)
    have r2 := rel_trans (rel_comp_left (hR τ ρ) (m σ)) (hR σ (τ * ρ))
    rw [← _root_.mul_assoc] at r2
    have := rel_unique hT (hsurj _) r1 r2
    rw [mul_comm]; exact this
  · -- inflation from `Gal(L/ℚ)`
    intro σ σ' τ τ' h1 h2
    set k := σ⁻¹ * σ' with hk
    set k' := τ⁻¹ * τ' with hk'
    have hkL : k ∈ GQL L := by
      rw [mem_GQL]; intro x hx
      rw [act_mul, ← h1 x hx, act_inv_act]
    have hk'L : k' ∈ GQL L := by
      rw [mem_GQL]; intro x hx
      rw [act_mul, ← h2 x hx, act_inv_act]
    have eσ : σ' = σ * k := by rw [hk, mul_inv_cancel_left]
    have eτ : τ' = τ * k' := by rw [hk', mul_inv_cancel_left]
    set k'' := τ⁻¹ * k * τ with hk''
    have hk''L : k'' ∈ GQL L := by
      have := hnorm.conj_mem k hkL τ⁻¹
      rwa [inv_inv] at this
    have hkτ : k * τ = τ * k'' := by rw [hk'']; group
    have hmm : (m σ').comp (m τ') = ((m σ).comp (m τ)).comp (m (k'' * k')) := by
      rw [eσ, eτ, (hinfl σ k hkL).1, (hinfl τ k' hk'L).1, (hinfl k'' k' hk'L).1]
      have h3 : (m k).comp (m τ) = (m τ).comp (m k'') := by
        rw [← (hinfl τ k hkL).2, hkτ, (hinfl τ k'' hk''L).1]
      refine AddMonoidHom.ext fun x => ?_
      have := DFunLike.congr_fun h3 (m k' x)
      simp only [AddMonoidHom.comp_apply] at this ⊢
      rw [this]
    have hgrp : σ' * τ' = σ * τ * (k'' * k') := by
      rw [eσ, eτ, hk'']; group
    have r1 : Rel ((m σ').comp (m τ')) (m (σ' * τ')) (c σ τ) := by
      rw [hmm, hgrp, (hinfl (σ * τ) (k'' * k') ((GQL L).mul_mem hk''L hk'L)).1]
      exact rel_comp_right (hR σ τ) _
    exact (rel_unique hT (hsurj _) (hR σ' τ') r1).symm
  · -- `c(1,1) = 1`
    have r : Rel ((m 1).comp (m 1)) (m (1 * 1)) 1 := by
      rw [← (hinfl 1 1 hone).1]; exact rel_self _
    exact rel_unique hT (hsurj _) (hR 1 1) r
  · -- the kernel identity
    intro σ τ
    exact card_identity hT (hsurj σ) (hsurj τ) (hsurj (σ * τ)) (hn σ τ) (hd σ τ) (hnd σ τ)

/-- **`ConjugacyData` without the discrepancy**: the maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` with the
Galois action on `G_L`, inflation from `Gal(L/ℚ)`, commutation with `End_L(A)`, surjectivity and
finite kernel, an integral relation `d·m_σ m_τ = n·m_στ` (`d ≠ 0`; Glazer N5 L640-644: the
discrepancy `μ_σ ^σμ_τ μ_στ⁻¹` commutes with `B`, hence is a rational scalar), and algebraicity
(`m_σ(x) = F_σ ∘ x ∘ Spec σ`, `F_σ` finite surjective). Clauses 1-4 and 10 of `ConjugacyData`
verbatim; clause 5 without `c`. -/
def ConjMaps (L : IF) (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, ∃ n d : ℤ, d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ)) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

theorem conjugacyData_of_conjMaps (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (h : ConjMaps L A m) : ∃ c : GQ → GQ → ℚ, ConjugacyData L A m c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact conjugacyData_of_maps L A m hT h1 h2 h3 h4 h5 h6

end G0ModField.KernelField

end Part61

/-! ## §6.2-6.3 The kernel field `E` and the group `G ≤ GL_r(ℤ)` (G4, exposed) -/

section KernelCore

open GlueB3Unram GlueDescent.B2Q NumberField PkgI3 PkgI3.AbVar CategoryTheory MonObj

namespace G0ModField.KernelField

/-- **`homField_core` with the kernel field exposed (proved; the proof is `homField_core`'s).**
For a continuous `ℤ`-linear action `ρ` of `G_ℚ` on a free `ℤ`-module with basis `Fin r`, trivial
on inertia outside `T`: `E = ℚ̄^{ker ρ}` is finite Galois with `[E:ℚ] = |G|` for the finite group
`G = ρ(G_ℚ) ≤ GL_r(ℤ)`, `G_E` acts trivially, and `E` is unramified outside `T`. -/
theorem kernelField_core {M : Type*} [AddCommGroup M] {r : ℕ} (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M)) (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IntermediateField ℚ Qbar)
      (_ : FiniteDimensional ℚ E) (_ : IsGalois ℚ E),
      Module.finrank ℚ E = Nat.card G ∧ (∀ σ ∈ E.fixingSubgroup, ρ σ = 1) ∧
      (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt E p) := by
  classical
  let ρ' : Gal →* Matrix.GeneralLinearGroup (Fin r) ℤ := (G4WeilRes.toGL b).comp ρ
  have hker : ρ'.ker = ρ.ker := by
    ext σ
    simp only [MonoidHom.mem_ker]
    exact G4WeilRes.toGL_eq_one_iff b (ρ σ)
  have hset : (ρ.ker : Set Gal) = ⋂ i, {σ : Gal | ρ σ (b i) = b i} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    exact G4WeilRes.eq_one_iff_basis b (ρ σ)
  have hNopen : IsOpen (ρ.ker : Set Gal) := by
    rw [hset]; exact isOpen_iInter_of_finite fun i => hcont (b i)
  have hNclosed : IsClosed (ρ.ker : Set Gal) := Subgroup.isClosed_of_isOpen _ hNopen
  let NC : ClosedSubgroup Gal := { toSubgroup := ρ.ker, isClosed' := hNclosed }
  let E : IntermediateField ℚ Qbar := IntermediateField.fixedField NC.toSubgroup
  have hE : E.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField NC
  have hEfd : FiniteDimensional ℚ E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      show IsOpen (E.fixingSubgroup : Set Gal)
      rw [hE]; exact hNopen)
  have hEgal : IsGalois ℚ E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (by rw [hE]; exact ρ.normal_ker)
  have hcardE : Module.finrank ℚ E = Nat.card ρ'.range := by
    rw [← IsGalois.card_aut_eq_finrank]
    have e1 := QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := ℚ)
      (K₁ := Qbar) E) (AlgEquiv.restrictNormalHom_surjective (E := Qbar))
    have e2 := QuotientGroup.quotientKerEquivRange ρ'
    have c1 : Nat.card (E ≃ₐ[ℚ] E) =
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) E).ker.index :=
      (Nat.card_congr e1.toEquiv).symm
    have c2 : Nat.card ρ'.range = ρ'.ker.index := (Nat.card_congr e2.toEquiv).symm
    rw [c1, c2, IntermediateField.restrictNormalHom_ker, hE, hker]
  haveI : Finite ρ'.range := by
    apply Nat.finite_of_card_ne_zero
    rw [← hcardE]; exact Module.finrank_pos.ne'
  refine ⟨ρ'.range, inferInstance, E, hEfd, hEgal, hcardE, fun σ hσ => ?_, ?_⟩
  · rw [hE] at hσ; exact hσ
  · apply G4WeilRes.unramifiedAt_of_galUnramifiedOutside
    intro p hp hpT w hw s hs
    rw [hE]
    exact hinert p hp hpT w hw s hs

/-- **G4 in `KernelFieldOut`'s shape (proved from the leaves `HomFreeFinite` and
`NeronOggShafarevich`; `MorphismsDescend` is proved, morph-descend).** For `A/K` (`K` finite
Galois, `[K:ℚ] ≤ F₀`, unramified outside `T`) whose conjugates are surfaces and which has good
reduction at every place over every `p ∉ T`: the Hom lattice `⊕ Hom(A_e, A_e')` (the endomorphism
lattice of `Res_{K/ℚ} A ⊗ ℚ̄`) has rank `r ≤ 16F₀²`, the image `G` of `G_ℚ` in `GL_r(ℤ)` is
finite with kernel field `E`, `[E:ℚ] = |G|`, `E` is unramified outside `T`, and `G_{E⊔K}` fixes
every homomorphism between conjugates (`E ⊔ K` is the Hom field). -/
theorem kernelField_of_model (hHFF : HomFreeFinite) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((G4WeilRes.conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ r : ℕ, r ≤ 16 * ZInQ.heightF0 ^ 2 ∧
    ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IntermediateField ℚ Qbar)
      (_ : FiniteDimensional ℚ E) (_ : IsGalois ℚ E),
      Module.finrank ℚ E = Nat.card G ∧
      (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt E p) ∧
      (∀ σ ∈ (E ⊔ K).fixingSubgroup, G4WeilRes.conjAction K A σ = 1) := by
  obtain ⟨hfree, hfin, hrank⟩ := G4WeilRes.homLattice_free hHFF (G4WeilRes.conjData K A).A hdim
  have hr : Module.finrank ℤ (G4WeilRes.HomLattice (G4WeilRes.conjData K A).A) ≤
      16 * ZInQ.heightF0 ^ 2 :=
    hrank.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by rw [G4WeilRes.card_conjugates]; exact hKF) 2))
  obtain ⟨G, hG, E, hfE, hgE, hEG, hfix, hram⟩ :=
    kernelField_core (Module.finBasisOfFinrankEq ℤ _ rfl) (G4WeilRes.conjAction K A)
      (G4WeilRes.conjAction_continuous K G4WeilRes.homDescends A) T
      (G4WeilRes.conjAction_inertia' K (G4WeilRes.inertiaFixesHomsMon_of_leaves hNOS hHFF) A T
        hK hgood)
  exact ⟨_, hr, G, hG, E, hfE, hgE, hEG, hram,
    fun σ hσ => hfix σ (IntermediateField.fixingSubgroup_antitone le_sup_left hσ)⟩

end G0ModField.KernelField

end KernelCore

/-! ## §6.4-6.5 G4's hypotheses on a rational fibre; the remaining Props; the headline -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

theorem three_mem_T (u : ℚ) : 3 ∈ T u :=
  Finset.mem_union_left _ (Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- `hdim` of G4 (proved, from g0-dim's `G0Dim.dim_baseChange`): the conjugates
`A ×_{K,e} ℚ̄` of an abelian surface are surfaces. -/
theorem conj_dim (K : IF) (A : PkgI3.AbVar K) (hA : A.dim = 2) (e : K →ₐ[ℚ] Qbar) :
    ((G4WeilRes.conjData K A).A e).dim = 2 := by
  letI : Algebra K Qbar := (e : K →+* Qbar).toAlgebra
  exact (G0Dim.dim_baseChange (K := K) Qbar A.X.left A.X.hom).trans hA

/-- The base change `A_L` of an abelian surface `A/K` is a surface (g0-dim). -/
theorem bc_dim {K L : IF} (hKL : K ≤ L) (A : PkgI3.AbVar K) (hA : A.dim = 2) :
    (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)).dim = 2 := by
  letI : Algebra K L := incAlg hKL
  exact (G0Dim.dim_baseChange (K := K) L A.X.left A.X.hom).trans hA

/-- `hgood` of G4 on a `QML3` object (G3; proved from the leaves `NeronOggShafarevich`,
`RaynaudCriterion`, `TorsionStructure` through `LeafQM.AV.QML3.goodReduction`, with
inertia-homs' `comap_isDVR` and `isUnit_prime_of_liesOver`): good reduction at every place over
every `p ∉ T` when `3 ∈ T`. -/
theorem good_of_QML3 (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (K : IF) [FiniteDimensional ℚ K] (PK : QML3 K)
    (T : Finset ℕ) (h3 : 3 ∈ T) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, GlueB3Unram.LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar,
        PkgI2.HasGoodReduction (ObjBridge.toGrp PK.A) (w.comap (e : K →+* Qbar)) := by
  intro p hp hpT w hw e
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI := InertiaHoms.comap_isDVR (e : K →+* Qbar) w p hp hw
  have h3u : IsUnit ((3 : ℕ) : w.comap (e : K →+* Qbar)) :=
    InertiaHoms.isUnit_prime_of_liesOver _ w p hp hw 3 Nat.prime_three
      (by rintro rfl; exact hpT h3)
  exact QML3.goodReduction (P := PK) hNOS hRay hTors _ (by simpa using h3u)

/-- **Remaining glue 1 (`|A(ℚ̄)[n]| = n⁴`).** For an abelian surface `A` over a subfield
`L ⊆ ℚ̄`, the `n`-torsion of `A(ℚ̄)` has `n⁴` elements for every `n ≥ 1` (Mumford, *Abelian
varieties*, §4 Application 2 / §6, UNVERIFIED locator: `[n]` is separable of degree `n^{2g}` in
characteristic 0). It is the leaf `PkgI2.TorsionStructure` (`A(K̄)[n] ≅ (ℤ/n)^{2g}` over
`K̄ = AlgebraicClosure K`) transported along `AlgebraicClosure L ≅ ℚ̄` over `L` and from
`PkgI2.Pts (toGrp A)` to `PkgI3.AbVar.Pt`: glue. -/
def TorsionCountPts : Prop :=
  ∀ (L : IF) (A : PkgI3.AbVar L), A.dim = 2 → TorsCount (PtQ L A)

/-- **`TorsionCountPts`, proved from the leaf `PkgI2.TorsionStructure`** (`A(K̄)[n] ≅ (ℤ/n)^{2g}`,
Mumford §4/§6, the kernel's leaf): `ℚ̄` is an algebraic closure of `L` (inertia-homs'
`exists_closure_equiv`), and precomposition with `Spec ι : Spec ℚ̄ ≅ Spec K̄` over `Spec L` is a
bijection of points respecting powers (`MonObj.comp_pow`). -/
theorem torsionCountPts_of_leaf (hTors : PkgI2.TorsionStructure.{0}) : TorsionCountPts := by
  intro L A hA n hn
  obtain ⟨jj, hjj⟩ := InertiaHoms.exists_closure_equiv L L.val
  have hcomp : CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)) ≫
      CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) =
      CommRingCat.ofHom (algebraMap L Qbar) := by
    ext x; exact hjj x
  have hcomp' : CommRingCat.ofHom (algebraMap L Qbar) ≫
      CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) =
      CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)) := by
    rw [← hcomp]; ext x; simp
  let s : PkgI3.AbVar.ptObj (K := L) Qbar ⟶ PkgI2.specOver L (AlgebraicClosure L) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar))) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, hcomp])
  let s' : PkgI2.specOver L (AlgebraicClosure L) ⟶ PkgI3.AbVar.ptObj (K := L) Qbar :=
    Over.homMk (Spec.map (CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L))) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, hcomp'])
  have h1 : CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) ≫
      CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) = 𝟙 _ := by
    ext x; simp
  have h2 : CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) ≫
      CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) = 𝟙 _ := by
    ext x; simp
  have hss' : s ≫ s' = 𝟙 _ := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, h1, Spec.map_id]
  have hs's : s' ≫ s = 𝟙 _ := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, h2, Spec.map_id]
  have hdim : topologicalKrullDim (ObjBridge.toGrp A).X.left = ((2 : ℕ) : WithBot ℕ∞) := by
    change A.dim = _
    rw [hA]; rfl
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨e, -⟩ := hTors L (ObjBridge.toGrp A) 2 n hdim hn (by exact_mod_cast hn.ne')
  let F : PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) n ≃ tors (PtQ L A) n :=
    { toFun := fun x => ⟨Additive.ofMul (s ≫ x.1), by
        rw [mem_tors, ← ofMul_pow, ← MonObj.comp_pow]
        have hx : x.1 ^ n = 1 := x.2
        rw [hx, MonObj.comp_one]; rfl⟩
      invFun := fun y => ⟨s' ≫ Additive.toMul y.1, by
        have hy : n • y.1 = 0 := mem_tors.mp y.2
        show (s' ≫ Additive.toMul y.1) ^ n = 1
        rw [← MonObj.comp_pow, ← toMul_nsmul, hy]
        exact MonObj.comp_one _⟩
      left_inv := fun x => by
        apply Subtype.ext
        show s' ≫ s ≫ x.1 = x.1
        rw [← Category.assoc, hs's, Category.id_comp]
      right_inv := fun y => by
        apply Subtype.ext
        show Additive.ofMul (s ≫ s' ≫ Additive.toMul y.1) = y.1
        rw [← Category.assoc, hss', Category.id_comp]; rfl }
  rw [← Nat.card_congr F, Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **Remaining glue 2 (G4 + B1's geometric half on the Hom field: the conjugacy maps).** For
every fibre context, every rational fibre `PK/K` as in G2's output, and every finite Galois
`L ⊇ K` that is a Hom field of `PK.A` (`G_L` fixes every homomorphism between the conjugates of
`PK.A` over `ℚ̄`, g4-weilres' `conjAction`), the base change `A_L` carries the maps
`m_σ = μ_σ ∘ σ` of `ConjMaps` (N5 L632-645: `μ_σ : ^σA → A` the conjugacy isogenies, from A7
`conj_twist_of_rational` and Skolem–Noether, `B`-linear; rational discrepancy by
`End⁰(A_ℚ̄) = B`, i.e. NoCM). -/
def ConjMapsOnHomField : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K], Module.finrank ℚ K ≤ heightF0 →
      (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) →
      ∀ PK : QML3 K, RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjMaps L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) m

/-- **Headline (proved): `KernelFieldExists` from four leaves and two glue Props.** Leaves:
`HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
`RaynaudCriterion`, `TorsionStructure` (the kernel's leaves behind `QML3.goodReduction`). Glue:
`TorsionCountPts`, `ConjMapsOnHomField`. Proved on the way: G4 with `E` and `G` exposed
(`kernelField_of_model`), `MorphismsDescend` (morph-descend), `hdim` (g0-dim), `hgood` (G3 on
`QML3` objects), and the discrepancy algebra (`conjugacyData_of_maps`). -/
theorem kernelFieldExists_of_pieces (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hCount : TorsionCountPts)
    (hMaps : ConjMapsOnHomField) : KernelFieldExists := by
  intro Y Φ π u P hctx K _ _ hKF hramK PK hPK
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model hHFF hNOS K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3 hNOS hRay hTors K PK (T u) (three_mem_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  obtain ⟨m, hm⟩ := hMaps Y Φ π u P hctx K hKF hramK PK hPK (E ⊔ K) le_sup_right hfix
  obtain ⟨c, hc⟩ := conjugacyData_of_conjMaps _ _ m
    (hCount _ _ (bc_dim le_sup_right PK.A PK.surface)) hm
  exact ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hc⟩

/-- **Headline, final form (proved): `KernelFieldExists` from four leaves and one glue Prop.**
Leaves: `HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
`RaynaudCriterion` (Raynaud / Grothendieck SGA 7 IX), `TorsionStructure` (Mumford §4/§6).
Glue: `ConjMapsOnHomField` (the conjugacy maps on the Hom field: A7 + Skolem–Noether + NoCM). -/
theorem kernelFieldExists_of_leaves (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hMaps : ConjMapsOnHomField) : KernelFieldExists :=
  kernelFieldExists_of_pieces hHFF hNOS hRay hTors (torsionCountPts_of_leaf hTors) hMaps

end G0ModField.KernelField

#print axioms G0ModField.KernelField.kernelFieldExists_of_leaves
#print axioms G0ModField.KernelField.conjugacyData_of_maps
#print axioms G0ModField.KernelField.kernelField_core
#print axioms G0ModField.KernelField.kernelField_of_model
#print axioms G0ModField.KernelField.good_of_QML3
#print axioms G0ModField.KernelField.conj_dim
#print axioms G0ModField.KernelField.kernelFieldExists_of_pieces
#print axioms G0ModField.KernelField.torsionCountPts_of_leaf

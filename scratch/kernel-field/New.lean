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


/-! ## §6.6 The NoCM input made explicit: `FibreComTrivial` (g0-fibresimple's FS5, verbatim) -/

section FS5Copy

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV

namespace G0FibreSimple

/-- **Glue piece FS5 = G6 (NoCM, rv-h-cm §7.2, on the actual fibre object).** For `u ∉ 𝒞` and an
object `P` of `Y₃` at a `ℚ̄`-point over `J(u)`, the centralizer `End_𝒪(P.A)` is `ℤ` (the point is
not a CM point). *Why true* (rv-h-cm §7.2, model-checked, no human review): `R1fpProps`,
`R2fpProps` pin down `Y₃` and the Hauptmodul (g0-split §3); the fibre of `X₆ → P¹` over `t(u)` is
a free `W`-orbit with residue field `ℚ(i)` (Elkies' model; `GlueRepo.PR.fibre_free`, proved); a CM
order `R` has conductor prime to 6 with 2, 3 non-split (Vignéras, (Emb)); González–Rotger
Thm 5.12 (leaf R5, `LeafQM.AV.R5ptProps`) and Prop. 5.6 then force `R = ℤ[i]` (excluded since
`t(u) ≠ 1`, `F(u) ≠ 0`) or `#CM(R) = 2 < 4 = #W·x`. Unproved: the Kummer model of `X₆ → P¹`
(function-field Galois theory), the identification of an arbitrary `(Y, Φ, π)` with the bundle's
`X₆`, the class-number arithmetic. Glue, using the leaves R1, R2, R5. -/
def FibreComTrivial : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

end G0FibreSimple

end FS5Copy

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- **Remaining glue 2′ (the conjugacy maps, NoCM given).** As `ConjMapsOnHomField`, with the
NoCM input `End_𝒪(P.A) = ℤ` (FS5's conclusion) as an explicit hypothesis and with only what the
construction uses: moduli data with R1-R2's clauses, a `ℚ̄`-point `y` over a rational `j₀` with
object `P`, a rational fibre `PK/K` over `P`, and a Hom field `L ⊇ K` of `PK.A`. Construction
(N5 L632-645): A7 (`LeafQM.AV.conj_twist_of_rational`, compiled, for every such triple) gives
`^σP ≅ P` up to a twist `α_σ ∈ Aut 𝒪`; Skolem–Noether (T13, proved,
`ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`) writes `α_σ` as conjugation by `b_σ ∈ B^×`, and
`μ_σ = ι(b_σ)∘(iso)` is a `B`-linear isogeny, defined over the Hom field `L`; the discrepancy
`μ_σ ^σμ_τ μ_στ⁻¹` commutes with `ι(𝒪)`, hence is rational by `End_𝒪 = ℤ`; with T27 (Yu)
`End⁰ = B`, so `m_σ = μ_σ∘σ` commutes with `End_L(A_L)`. The quantifier over `(Y, Φ, π)` costs
nothing here: A7 holds for every triple with R1fp-R2fp, and the NoCM input is a hypothesis. -/
def ConjMapsNoCM : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjMaps L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) m

/-- **`ConjMapsOnHomField` from FS5 and the NoCM-given maps (proved).** -/
theorem conjMapsOnHomField_of (h5 : G0FibreSimple.FibreComTrivial) (h : ConjMapsNoCM) :
    ConjMapsOnHomField := by
  intro Y Φ π u P hctx K _ _ _ _ PK hPK L _ _ hKL hfix
  obtain ⟨hR1, hR2, hu, y, hy, hπ⟩ := hctx
  exact h Y Φ π hR1 hR2 (ZInQ.JHeight.Jmap u) y P hy hπ (h5 Y Φ π hR1 hR2 u hu y P hy hπ) K PK hPK
    L hKL hfix

/-- **Headline with the NoCM input explicit (proved).** `KernelFieldExists` from the leaves
`HomFreeFinite`, `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, the glue FS5
`FibreComTrivial` (g0-fibresimple; its truth for every triple is qm-pin's repair) and the glue
`ConjMapsNoCM`. -/
theorem kernelFieldExists_of_leaves_FS5 (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hMaps : ConjMapsNoCM) : KernelFieldExists :=
  kernelFieldExists_of_leaves hHFF hNOS hRay hTors (conjMapsOnHomField_of h5 hMaps)

end G0ModField.KernelField


/-! ## §6.7 Skolem–Noether on `𝒪` (proved): every twist `α ∈ Aut(𝒪)` is inner in `B`

A7 (`LeafQM.AV.conj_twist_of_rational`) gives `^σP ≅ P` only up to a twist of the QM action by a
ring automorphism `α_σ` of `𝒪`. The algebraic half of the Skolem–Noether descent (N5 L632-640):
`α` extends to a `ℚ`-automorphism of `B = (2,-3)_ℚ` (through the quaternion basis
`α(i), α(j)`), which is inner by Skolem–Noether (T13, proved in
`ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`). So `α(a) = u a u⁻¹` for some `u ∈ B^×`, and
`ι(Nu) ∘ (QM iso)` is a `B`-linear isogeny for any `N ≥ 1` with `Nu ∈ 𝒪`. -/

section AutO

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

theorem oj_mul_oi' : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- The quaternion basis `α(i), α(j), α(i)α(j)` of `B` given by a ring automorphism `α` of `𝒪`. -/
noncomputable def autBasis (α : O ≃+* O) : QuaternionAlgebra.Basis B (2 : ℚ) 0 (-3) where
  i := (α oi : B)
  j := (α oj : B)
  k := (α oi : B) * (α oj : B)
  i_mul_i := by
    rw [← Subring.coe_mul, ← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def,
      _root_.mul_one, map_ofNat]
    rfl
  j_mul_j := by
    rw [← Subring.coe_mul, ← map_mul, oj_mul_oj, map_neg, map_ofNat, Subring.coe_neg,
      Algebra.smul_def, _root_.mul_one, map_neg, map_ofNat]
    rfl
  i_mul_j := rfl
  j_mul_i := by
    rw [← Subring.coe_mul, ← map_mul, oj_mul_oi', map_neg, map_mul]
    simp

/-- **Skolem–Noether on `𝒪` (proved, from T13).** Every ring automorphism `α` of the maximal
order `𝒪 ⊂ B = (2,-3)_ℚ` is conjugation by a unit of `B`. -/
theorem aut_O_inner (α : O ≃+* O) : ∃ u : Bˣ, ∀ a : O, (α a : B) = u * a * (u⁻¹ : Bˣ) := by
  let φ : B →ₐ[ℚ] B := (autBasis α).liftHom
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := φ.toLinearMap)).mp hinj⟩
  obtain ⟨u, hu⟩ := TSkolemKW.leafSkolemNoether ℚ B (AlgEquiv.ofBijective φ hbij)
  refine ⟨u, fun a => ?_⟩
  rw [← hu]
  show (α a : B) = φ a
  let ψ1 : O →+* B := (Subring.subtype O).comp α.toRingHom
  let ψ2 : O →+* B := φ.toRingHom.comp (Subring.subtype O)
  have hi : ψ1 oi = ψ2 oi := by
    show (α oi : B) = (autBasis α).lift (oi : B)
    simp [QuaternionAlgebra.Basis.lift, oi, LeafQM.ofInt, autBasis]
  have hj : ψ1 oj = ψ2 oj := by
    show (α oj : B) = (autBasis α).lift (oj : B)
    simp [QuaternionAlgebra.Basis.lift, oj, LeafQM.ofInt, autBasis]
  obtain ⟨n, hn⟩ := a.2
  have h2 : (2 : O) * a = ((2 * n 0 + n 2 : ℤ) : O) + ((2 * n 1 + n 3 : ℤ) : O) * oi +
      ((n 2 : ℤ) : O) * oj + ((n 3 : ℤ) : O) * (oi * oj) := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
    rw [show ((2 : O) : B) = 2 from rfl, hn]
    ext <;> simp [oi, oj, LeafQM.ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
  have key : ∀ ψ : O →+* B, ψ ((2 : O) * a) = ((2 * n 0 + n 2 : ℤ) : B) +
      ((2 * n 1 + n 3 : ℤ) : B) * ψ oi + ((n 2 : ℤ) : B) * ψ oj +
      ((n 3 : ℤ) : B) * (ψ oi * ψ oj) := by
    intro ψ
    rw [h2]; simp only [map_add, map_mul, map_intCast]
  have e : (2 : B) * ψ1 a = (2 : B) * ψ2 a := by
    have := key ψ1
    rw [map_mul, map_ofNat] at this
    rw [this, hi, hj, ← key ψ2, map_mul, map_ofNat]
  have e2 : (2 : ℚ) • ψ1 a = (2 : ℚ) • ψ2 a := by
    rw [two_smul, two_smul, ← two_mul, ← two_mul]; exact e
  exact smul_right_injective B (two_ne_zero : (2 : ℚ) ≠ 0) e2

end G0ModField.KernelField

end AutO


/-! ## §6.8 Where NoCM enters (proved): integrality and commutation from `End(A_L) = ι(𝒪)`

`ConjMaps` splits into a geometric part with no NoCM content (`ConjIsogMaps`: the maps
`m_σ = μ_σ∘σ` are `𝒪`-linear, and the discrepancy is an endomorphism of `A_L` up to a nonzero
integer, which holds for any isogenies `μ_σ` by the quasi-inverse `ψ μ_στ = [e]`) and the NoCM
input `End_L(A_L) = ι(𝒪)` (FS5 + T27 + maximality of `𝒪`, on the Hom field). The passage is pure
algebra: an endomorphism commuting with `ι(𝒪)` is `ι(b)` with `b` central in `𝒪`, hence an
integer; faithfulness of `𝒪` on `A(ℚ̄)` follows from `|A[n]| = n⁴` and the anisotropy of the norm
form of `B` (`GlueDescent.aniso_rat`). -/

section NoCMAlg

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

/-- Every element of `B` has a nonzero integer multiple in `𝒪`. -/
theorem exists_nat_mul_mem_O (y : B) : ∃ N : ℕ, 0 < N ∧ (N : B) * y ∈ O := by
  set D : ℕ := y.re.den * y.imI.den * y.imJ.den * y.imK.den with hD
  have hD0 : 0 < D := by positivity
  have hnum : ∀ q : ℚ, (q.num : ℚ) = q * q.den := fun q =>
    (div_eq_iff (by positivity)).mp (Rat.num_div_den q)
  set a : ℤ := y.re.num * (y.imI.den * y.imJ.den * y.imK.den)
  set b : ℤ := y.imI.num * (y.re.den * y.imJ.den * y.imK.den)
  set c : ℤ := y.imJ.num * (y.re.den * y.imI.den * y.imK.den)
  set d : ℤ := y.imK.num * (y.re.den * y.imI.den * y.imJ.den)
  have ha : (a : ℚ) = D * y.re := by simp only [a, hD]; push_cast; rw [hnum]; ring
  have hb : (b : ℚ) = D * y.imI := by simp only [b, hD]; push_cast; rw [hnum]; ring
  have hc : (c : ℚ) = D * y.imJ := by simp only [c, hD]; push_cast; rw [hnum]; ring
  have hd : (d : ℚ) = D * y.imK := by simp only [d, hD]; push_cast; rw [hnum]; ring
  refine ⟨D, hD0, ![a - c, b - d, 2 * c, 2 * d], ?_⟩
  ext <;> simp [LeafQM.ofInt, QuaternionAlgebra.re_natCast, QuaternionAlgebra.imI_natCast,
    QuaternionAlgebra.imJ_natCast, QuaternionAlgebra.imK_natCast] <;> push_cast <;>
    linarith [ha, hb, hc, hd]

/-- A rational element of `𝒪` is an integer. -/
theorem int_of_rat_mem_O {r : ℚ} (h : algebraMap ℚ B r ∈ O) : ∃ k : ℤ, r = k := by
  obtain ⟨n, hn⟩ := h
  have e0 := congrArg QuaternionAlgebra.re hn
  have e1 := congrArg QuaternionAlgebra.imI hn
  have e2 := congrArg QuaternionAlgebra.imJ hn
  have e3 := congrArg QuaternionAlgebra.imK hn
  simp [LeafQM.ofInt, QuaternionAlgebra.algebraMap_eq] at e0 e1 e2 e3
  refine ⟨n 0, ?_⟩
  rw [e0]
  have h2 : (n 2 : ℚ) = 0 := by linarith
  simp [h2]

theorem coe_intCast_O (k : ℤ) : ((k : O) : B) = algebraMap ℚ B k := by
  rw [Subring.coe_intCast, map_intCast]

/-- **The centre of `𝒪` is `ℤ`.** -/
theorem center_O {b : O} (hb : ∀ a : O, b * a = a * b) : ∃ k : ℤ, b = k := by
  have hi : (b : B) * GlueDescent.qi = GlueDescent.qi * b := by
    have := congrArg Subtype.val (hb oi)
    rw [Subring.coe_mul, Subring.coe_mul] at this
    rwa [show ((oi : O) : B) = GlueDescent.qi by ext <;> simp [oi, LeafQM.ofInt, GlueDescent.qi]]
      at this
  have hj : (b : B) * GlueDescent.qj = GlueDescent.qj * b := by
    have := congrArg Subtype.val (hb oj)
    rw [Subring.coe_mul, Subring.coe_mul] at this
    rwa [show ((oj : O) : B) = GlueDescent.qj by ext <;> simp [oj, LeafQM.ofInt, GlueDescent.qj]]
      at this
  have hs := GlueDescent.B6_commute_i_j (b : B) hi hj
  obtain ⟨k, hk⟩ := int_of_rat_mem_O (hs ▸ b.2)
  refine ⟨k, Subtype.ext ?_⟩
  rw [coe_intCast_O, ← hk]
  exact hs

variable {V : Type*} [AddCommGroup V]

/-- **`𝒪` acts faithfully on a group with `|V[n]| = n⁴`.** -/
theorem faithful_O (hT : TorsCount V) (ρ : O →+* AddMonoid.End V) {c : O} (hc : ρ c = 0) :
    c = 0 := by
  by_contra hc0
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O (star (c : B))
  let c' : O := ⟨(N : B) * star (c : B), hmem⟩
  set nf : ℚ := (c : B).re ^ 2 - 2 * (c : B).imI ^ 2 + 3 * (c : B).imJ ^ 2 - 6 * (c : B).imK ^ 2
  have hprod : ((c' * c : O) : B) = algebraMap ℚ B (N * nf) := by
    rw [Subring.coe_mul]
    show (N : B) * star (c : B) * c = _
    rw [_root_.mul_assoc, GlueDescent.B6_star_mul, map_mul, map_natCast]
  obtain ⟨k, hk⟩ := int_of_rat_mem_O (hprod ▸ (c' * c).2)
  have hck : c' * c = (k : O) := Subtype.ext (by rw [hprod, coe_intCast_O, hk])
  have hρ : ρ (k : O) = 0 := by rw [← hck, map_mul, hc, mul_zero]
  rw [map_intCast] at hρ
  have hk0 : k = 0 := eq_zero_of_forall_zsmul hT (fun x => by
    have := DFunLike.congr_fun hρ x
    simpa using this)
  rw [hk0, Int.cast_zero] at hk
  have hnf : nf = 0 := by
    rcases mul_eq_zero.mp hk with h | h
    · exact absurd h (by exact_mod_cast hN.ne')
    · exact h
  obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ hnf
  exact hc0 (Subtype.ext (QuaternionAlgebra.ext h1 h2 h3 h4))


/-- **Skolem–Noether descent at the level of homomorphisms (proved).** A7
(`LeafQM.AV.conj_twist_of_rational`) gives, for each `σ`, a QM isomorphism `e : (A, ι∘α) ≅ (A', ι')`
twisted by some `α ∈ Aut 𝒪`. Writing `α = u(·)u⁻¹` (`aut_O_inner`) and `b = Nu ∈ 𝒪`
(`exists_nat_mul_mem_O`), the homomorphism `μ = e.φ ∘ ι(b) : A → A'` is nonzero-scaled and
`𝒪`-linear: `μ ∘ ι(a) = ι'(a) ∘ μ` for all `a ∈ 𝒪`. This is N5's `B`-linear conjugacy isogeny
`μ_σ` (here `A = P.A`, `A' = (^σP).A`; reverse the roles for `^σA → A`). -/
theorem blinear_of_twisted_iso {k : Type} [Field k] {A A' : PkgI3.AbVar k} (q : QMStr A)
    (q' : QMStr A') (α : O ≃+* O) (e : QMIso (q.twist α) q') :
    ∃ b : O, b ≠ 0 ∧ ∀ a : O,
      (q.iota a).hom ≫ ((q.iota b).hom ≫ e.φ.hom) = ((q.iota b).hom ≫ e.φ.hom) ≫ (q'.iota a).hom := by
  obtain ⟨u, hu⟩ := aut_O_inner α
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O (u : B)
  let b : O := ⟨(N : B) * u, hmem⟩
  have hcomm : ∀ a : O, b * a = α a * b := by
    intro a
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hu a]
    show (N : B) * u * a = u * a * (u⁻¹ : Bˣ) * ((N : B) * u)
    have hc : ((u⁻¹ : Bˣ) : B) * ((N : B) * u) = (N : B) := by
      rw [← _root_.mul_assoc, (Nat.cast_commute N _).symm.eq, _root_.mul_assoc, Units.inv_mul,
        _root_.mul_one]
    rw [_root_.mul_assoc (u * a : B), hc, (Nat.cast_commute N ((u : B) * a)).eq.symm,
      _root_.mul_assoc]
  refine ⟨b, fun hb => ?_, fun a => ?_⟩
  · have h0 := congrArg Subtype.val hb
    change (N : B) * u = 0 at h0
    have h1 := congrArg (· * ((u⁻¹ : Bˣ) : B)) h0
    simp only [_root_.mul_assoc, Units.mul_inv, _root_.mul_one, zero_mul] at h1
    have h2 := congrArg QuaternionAlgebra.re h1
    simp at h2
    omega
  · have e1 : (q.iota a).hom ≫ (q.iota b).hom = (q.iota b).hom ≫ (q.iota (α a)).hom := by
      show (q.iota b * q.iota a).hom = (q.iota (α a) * q.iota b).hom
      rw [← map_mul, ← map_mul, hcomm]
    rw [← Category.assoc, e1, Category.assoc, Category.assoc]
    congr 1
    exact e.equivariant a

end G0ModField.KernelField

end NoCMAlg


section NoCMSplit

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

/-! Base change on endomorphisms, `End_K(A) → End_L(A_L)` (copied from
`scratch/bp-qmmoduli/QMAbVar.lean` §BaseChangeEnd, lines 528-556, with `AbVar` qualified). -/

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (first half of node N8): `End_K(A) → End_L(A_L)`,
`f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism (functoriality, and
`Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC {K : Type} [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl


/-- The geometric clauses of the conjugacy maps for a ring map `ι' : 𝒪 → End_L(A)` (the QM action
on `A`), with no NoCM content: `ConjMaps`' clauses 1, 2, 4, 6 verbatim; `m_σ` is `𝒪`-linear
(`μ_σ` is `B`-linear, A7 + Skolem–Noether `aut_O_inner`); and the discrepancy is an endomorphism up
to a nonzero integer, `e·m_σ m_τ = δ∘m_στ` with `δ ∈ End_L(A)` (`δ = μ_σ ^σμ_τ ψ` with `ψ` a
quasi-inverse, `ψ μ_στ = [e]`, Mumford §8; defined over `L` because `L` is a Hom field). -/
def ConjIsogMapsAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (m : GQ → (PtQ L A →+ PtQ L A)) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (a : O), (m σ).comp (endPt A Qbar (ι' a)) = (endPt A Qbar (ι' a)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, ∃ e : ℤ, e ≠ 0 ∧ ∃ δ : PkgI3.AbVar.End A,
      e • (m σ).comp (m τ) = (endPt A Qbar δ).comp (m (σ * τ))) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

/-- **NoCM enters only through `End_L(A) = ι(𝒪)` (proved).** With `|A(ℚ̄)[n]| = n⁴`: the geometric
clauses and `End_L(A) = ι'(𝒪)` give `ConjMaps` (commutation with `End_L(A)`; the discrepancy
`δ = ι'(b)` commutes with `ι'(𝒪)` on points, so `b` is central by faithfulness, hence an
integer). -/
theorem conjMaps_of_qm (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (hEnd : ∀ f : PkgI3.AbVar.End A, ∃ a : O, f = ι' a)
    (h : ConjIsogMapsAt L A ι' m) : ConjMaps L A m := by
  obtain ⟨hgal, hinfl, hB, hfin, hdisc, halg⟩ := h
  let ρ : O →+* AddMonoid.End (PtQ L A) := (endPt A Qbar).comp ι'
  have hBx : ∀ σ a x, m σ (ρ a x) = ρ a (m σ x) := fun σ a x =>
    DFunLike.congr_fun (hB σ a) x
  refine ⟨hgal, hinfl, fun σ f => ?_, hfin, fun σ τ => ?_, halg⟩
  · obtain ⟨a, rfl⟩ := hEnd f
    exact hB σ a
  · obtain ⟨e, he, δ, hδ⟩ := hdisc σ τ
    obtain ⟨b, rfl⟩ := hEnd δ
    have hδx : ∀ x, e • m σ (m τ x) = ρ b (m (σ * τ) x) := fun x => by
      have := DFunLike.congr_fun hδ x
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply] at this
      exact this
    have hcomm : ∀ a : O, b * a = a * b := by
      intro a
      have h2 : ρ (b * a) = ρ (a * b) := by
        refine AddMonoidHom.ext fun y => ?_
        obtain ⟨x, rfl⟩ := (hfin (σ * τ)).1 y
        rw [map_mul, map_mul]
        show ρ b (ρ a (m (σ * τ) x)) = ρ a (ρ b (m (σ * τ) x))
        rw [← hBx, ← hδx, ← hδx, hBx, hBx, map_zsmul]
      have : ρ (b * a - a * b) = 0 := by rw [map_sub, h2, sub_self]
      exact sub_eq_zero.mp (faithful_O hT ρ this)
    obtain ⟨k, rfl⟩ := center_O hcomm
    refine ⟨k, e, he, ?_⟩
    rw [hδ]
    refine AddMonoidHom.ext fun x => ?_
    have hk : ρ (k : O) = (k : AddMonoid.End (PtQ L A)) := map_intCast ρ k
    show ρ (k : O) (m (σ * τ) x) = _
    rw [hk, AddMonoid.End.intCast_apply, AddMonoidHom.smul_apply]

end G0ModField.KernelField

end NoCMSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField


/-! ### Sanity check (proved): the new clause lists are satisfiable

For an abelian variety over `ℚ` (`L = ⊥`) with any ring map `ι' : 𝒪 → End(A)`, the Galois action
`m_σ = σ` satisfies `ConjIsogMapsAt` (with `e = 1`, `δ = 1`, `F_σ = id`), hence `ConjMaps`. So
the definitions are not contradictory (as g0-mod-field's `descentDatum_bot` for `DescentDatum`). -/

theorem conjIsogMapsAt_bot (A : PkgI3.AbVar (⊥ : IF)) (ι' : LeafQM.O →+* PkgI3.AbVar.End A) :
    ConjIsogMapsAt ⊥ A ι' (fun σ => MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))) := by
  let m : GQ → (PtQ ⊥ A →+ PtQ ⊥ A) := fun σ =>
    MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))
  have hmul : ∀ σ τ : GQ, (m σ).comp (m τ) = m (σ * τ) := by
    intro σ τ
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (A.galAct _ (A.galAct _ (Additive.toMul x))) =
      Additive.ofMul (A.galAct _ (Additive.toMul x))
    rw [galAct_mul]
    rfl
  have hbij : ∀ σ, Function.Bijective (m σ) := fun σ => galAct_bijective A _
  have hcomm : ∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ) := by
    intro σ f
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom _ ≫ (Additive.toMul x ≫ f.hom)) =
      Additive.ofMul ((PkgI3.AbVar.galHom _ ≫ Additive.toMul x) ≫ f.hom)
    rw [Category.assoc]
  refine ⟨?_, ?_, fun σ a => hcomm σ (ι' a), ?_, ?_, ?_⟩
  · intro σ σ' h
    have : σ' = toLAut σ (mem_GQL_bot σ) := AlgEquiv.ext h
    rw [this]
  · intro σ k _
    exact ⟨(hmul σ k).symm, (hmul k σ).symm⟩
  · intro σ
    refine ⟨(hbij σ).2, ?_⟩
    have : ((m σ).ker : Set (PtQ ⊥ A)) = {0} := by
      ext x
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_singleton_iff]
      constructor
      · intro h; exact (hbij σ).1 (h.trans (map_zero _).symm)
      · rintro rfl; exact map_zero _
    rw [this]; exact Set.finite_singleton 0
  · intro σ τ
    refine ⟨1, one_ne_zero, 1, ?_⟩
    rw [one_smul, hmul, map_one]
    rfl
  · refine ⟨fun _ => 𝟙 _, fun σ => ⟨inferInstance, inferInstance, fun x => ?_⟩⟩
    show (PkgI3.AbVar.galHom (toLAut σ (mem_GQL_bot σ)) ≫ Additive.toMul x).left =
      Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ 𝟙 _
    erw [Category.comp_id]
    rfl

/-- **Remaining glue 3 (geometric: the conjugacy maps without NoCM).** For moduli data with
R1-R2's clauses, a `ℚ̄`-point over a rational `j₀` with object `P`, a rational fibre `PK/K` over
`P` and a Hom field `L ⊇ K` of `PK.A`: maps `m_σ = μ_σ∘σ` on `A_L(ℚ̄)` with `ConjIsogMapsAt` for
the base-changed QM action `ι_L = endBC ∘ PK.q.iota`. Inputs (N5 L632-645): A7
(`conj_twist_of_rational`, compiled, every triple), Skolem–Noether on `𝒪` (`aut_O_inner`,
proved), a quasi-inverse of an isogeny (Mumford §8, UNVERIFIED locator), Galois descent of
`G_L`-fixed morphisms to `L`, and the semilinear identification of `^σA` with `A` as schemes. -/
def ConjIsogMaps : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjIsogMapsAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) m

/-- **Remaining glue 4 (NoCM on the Hom field: `End_L(A_L) = ι_L(𝒪)`).** Given FS5's conclusion
`End_𝒪(P.A) = ℤ`: by Yu's dichotomy (T27, leaf) `End⁰(P.A) ≅ B`, so `End(P.A)` is an order of
`ι(B)` containing the maximal order `ι(𝒪)`, hence equal to it; `P ≅ (PK)_ℚ̄` as QM objects (R1's
naturality and `RationalFibre`), and `End_L(A_L) → End_ℚ̄` is injective (faithful base change). -/
def EndEqOOnHomField : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∀ f : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
          ∃ a : LeafQM.O, f = ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) a

/-- **`ConjMapsNoCM` from the geometric maps and `End_L(A_L) = ι(𝒪)` (proved; leaf
`TorsionStructure` for `|A(ℚ̄)[n]| = n⁴`).** -/
theorem conjMapsNoCM_of (hTors : PkgI2.TorsionStructure.{0}) (hG : ConjIsogMaps)
    (hE : EndEqOOnHomField) : ConjMapsNoCM := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ hcom K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨m, hm⟩ := hG Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact ⟨m, conjMaps_of_qm L _ _ m
    (torsionCountPts_of_leaf hTors L _ (bc_dim hKL PK.A PK.surface))
    (hE Y Φ π hR1 hR2 j₀ y P hy hπ hcom K PK hPK L hKL hfix) hm⟩

/-- **Headline, split form (proved).** `KernelFieldExists` from the leaves `HomFreeFinite`,
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` and the glue `FibreComTrivial`
(FS5, g0-fibresimple), `ConjIsogMaps` (geometric) and `EndEqOOnHomField` (NoCM consequence). -/
theorem kernelFieldExists_of_split (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) (hE : EndEqOOnHomField) : KernelFieldExists :=
  kernelFieldExists_of_leaves_FS5 hHFF hNOS hRay hTors h5 (conjMapsNoCM_of hTors hG hE)

/-- **Remaining glue 4a (one QM surface over `ℚ̄`): `End_𝒪 = ℤ ⟹ End = ι(𝒪)`.** For an object `P`
(abelian surface over `ℚ̄` with QM by the maximal order `𝒪` of `(2,-3)_ℚ`) whose `𝒪`-centralizer
is `ℤ`, every endomorphism is `ι(a)`. *Argument* (model check): T27 (Yu 2013, leaf
`PkgI3.QMDichotomyYu`) gives `End⁰ ≅ B` or `M₂(ℚ(√d))`; FS4 (`CentralizerOfMatrixEnd0`, proved
from T6 by g0-fibresimple) excludes the second; `B → End⁰` (g0-fibresimple's `qm_embeds_end0`) is
injective (`B` simple) between 4-dimensional spaces, so `End⁰ = ι(B)`; `End` is an order (T6)
of `ι(B)` containing `ι(𝒪)`, which is maximal, so `End = ι(𝒪)`. No moduli data. -/
def EndEqOFibre : Prop :=
  ∀ P : QML3 Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ f : PkgI3.AbVar.End P.A, ∃ a : LeafQM.O, f = P.q.iota a

/-- **Remaining glue 4b (transport to the Hom field).** If `End(P.A) = ι(𝒪)`, then
`End_L(A_L) = ι_L(𝒪)`: `P ≅ (PK)_ℚ̄` as QM objects (R1's naturality applied to
`RationalFibre`), and base change `End_L(A_L) → End_ℚ̄((A_L)_ℚ̄)` is injective and compatible
with `ι` (`endBC`, faithful base change: bp-qmmoduli's `endBC_injective`). -/
def EndTransport : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ f : PkgI3.AbVar.End P.A, ∃ a : LeafQM.O, f = P.q.iota a) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∀ f : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
          ∃ a : LeafQM.O, f = ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) a

/-- `EndEqOOnHomField` from 4a and 4b (proved). -/
theorem endEqOOnHomField_of (ha : EndEqOFibre) (hb : EndTransport) : EndEqOOnHomField := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ hcom K _ _ PK hPK L _ _ hKL hfix
  exact hb Y Φ π hR1 hR2 j₀ y P hy hπ (ha P hcom) K PK hPK L hKL hfix

/-- **Headline, finest form (proved).** `KernelFieldExists` from the leaves `HomFreeFinite`,
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` and the glue FS5
`FibreComTrivial`, `ConjIsogMaps`, `EndEqOFibre`, `EndTransport`. -/
theorem kernelFieldExists_of_split' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) (ha : EndEqOFibre) (hb : EndTransport) : KernelFieldExists :=
  kernelFieldExists_of_split hHFF hNOS hRay hTors h5 hG (endEqOOnHomField_of ha hb)

end G0ModField.KernelField


/-! ## §6.9 `EndEqOFibre` from T27, T6 and the maximality of `𝒪`

Copied verbatim from `scratch/g0-fibresimple/olean/Tail.lean`: lines 38-117 (`B6_isUnit`,
`division_of_algEquiv`, `qmBasis`, `qm_embeds_end0`), 152-164 (FS4 `CentralizerOfMatrixEnd0`) and
208-282 (FS4 proved from T6, `centralizerOfMatrixEnd0_of_homFree`). -/

section FS4Copy

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV
open scoped Quaternion TensorProduct

namespace G0FibreSimple

/-! ## §1 Proved glue: `B` is a division algebra -/

/-- `B = (2, -3)_ℚ` is a division algebra: every nonzero element is a unit (the norm form
`a² - 2b² + 3c² - 6d²` is anisotropic, `GlueDescent.aniso_rat`). -/
theorem B6_isUnit (x : ℍ[ℚ, 2, -3]) (hx : x ≠ 0) : IsUnit x := by
  set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 with hn_def
  have hn : n ≠ 0 := fun h0 => by
    obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext h1 h2 h3 h4)
  have hs : star x * x = algebraMap ℚ ℍ[ℚ, 2, -3] n := GlueDescent.B6_star_mul x
  have hs' : x * star x = algebraMap ℚ ℍ[ℚ, 2, -3] n := by
    rw [QuaternionAlgebra.mul_star_eq_coe]
    congr 1
    simp [QuaternionAlgebra.re_mul]
    ring
  refine ⟨⟨x, n⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, hs', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  · rw [smul_mul_assoc, hs, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]

/-- Division transported along an algebra isomorphism. -/
theorem division_of_algEquiv {D E : Type*} [Ring D] [Ring E] [Algebra ℚ D] [Algebra ℚ E]
    (e : D ≃ₐ[ℚ] E) (hE : ∀ x : E, x ≠ 0 → IsUnit x) : ∀ x : D, x ≠ 0 → IsUnit x := by
  intro x hx
  have h1 : e x ≠ 0 := by
    intro h; apply hx; rw [← e.symm_apply_apply x, h, map_zero]
  have := (hE (e x) h1).map e.symm
  rwa [e.symm_apply_apply] at this

/-! ## §2 Proved glue: a QM structure gives `B →ₐ[ℚ] End⁰(A)` -/

/-- `i ∈ 𝒪`. -/
def oi : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def oj : LeafQM.O := ⟨LeafQM.ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem coe_two_O : ((2 : LeafQM.O) : LeafQM.B) = 2 := map_ofNat LeafQM.O.subtype 2
theorem coe_three_O : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  rw [coe_two_O, Subring.coe_mul]
  ext <;> simp [oi, LeafQM.ofInt] <;> rfl

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  rw [Subring.coe_neg, coe_three_O, Subring.coe_mul]
  ext <;> simp [oj, LeafQM.ofInt] <;> rfl

theorem oj_mul_oi : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- **Glue (proved): the QM structure gives `B ↪ End⁰(A)`.** For a QM structure
`ι : 𝒪 → End_k(A)` (`LeafQM.AV.QMStr`), the elements `1 ⊗ ι(i)`, `1 ⊗ ι(j)` of
`End⁰(A) = ℚ ⊗ End(A)` satisfy `i² = 2`, `j² = -3`, `ji = -ij`, so `B = ℍ[ℚ,2,-3]` maps to
`End⁰(A)` (`QuaternionAlgebra.Basis.liftHom`). This is Yu's hypothesis "`B` embeds in `End⁰(A)`"
(injectivity is automatic: `B` is simple and `End⁰(A) ≠ 0` when a QM structure exists). -/
def qmBasis {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    QuaternionAlgebra.Basis (PkgI3.AbVar.End0 A) (2 : ℚ) 0 (-3) :=
  let g : LeafQM.O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A).toRingHom.comp
      q.iota
  { i := g oi
    j := g oj
    k := g oi * g oj
    i_mul_i := by
      rw [← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
        map_ofNat]
    j_mul_j := by
      rw [← map_mul, oj_mul_oj, map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
        map_ofNat]
    i_mul_j := rfl
    j_mul_i := by
      rw [← map_mul, oj_mul_oi, map_neg, map_mul, zero_smul, zero_sub] }

theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩


/-- **Glue piece FS4 (the CM case of Yu's dichotomy has a non-integral `𝒪`-centralizer).** If
`End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, for an abelian variety with QM by `𝒪`, then the centralizer
`End_𝒪(A) = com q` contains a non-integer. *Why true* (STANDARD linear algebra): the image of
`B` in `M₂(k)`, `k = ℚ(√d)`, spans `M₂(k)` over `k` (`B ⊗ k` is simple of `k`-dimension 4), so
its centralizer is the centre `k`; `n√d` lies in the image of `End(A)` for some `n ≥ 1`, and
commutation and non-integrality pass from `End⁰(A)` to `End(A)` because `End(A)` is torsion-free
(Mumford §19 Thm 3). Glue. -/
def CentralizerOfMatrixEnd0 : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (q : QMStr A) (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 A ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    ∃ φ ∈ com q, ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End A)


/-! ## §4′ Proved: `CentralizerOfMatrixEnd0` from the leaf T6 (`PkgI3.HomFreeFinite`) -/

/-- **FS4 is proved from T6** (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3: `Hom(A, B)` is a free
`ℤ`-module; `TextbookLeaves.t6`). Proof: the scalar matrix `√d` is central in `M₂(ℚ(√d))`, so
`c' = e⁻¹(√d)` is central in `End⁰(A)` and is not a rational scalar (`(√d)² = d < 0`); `ℚ ⊗ End(A)`
is the localization of `End(A)` at `ℤ \ {0}`, so `s • c' = 1 ⊗ φ` for some `φ ∈ End(A)`,
`s ≠ 0`; freeness makes `m ↦ 1 ⊗ m` injective, so `φ` commutes with `ι(𝒪)` and is not an
integer. -/
theorem centralizerOfMatrixEnd0_of_homFree (hHF : PkgI3.HomFreeFinite) :
    CentralizerOfMatrixEnd0 := by
  intro k _ _ A q d hd hM
  obtain ⟨e⟩ := hM
  set c' : PkgI3.AbVar.End0 A :=
    e.symm (Matrix.scalar (Fin 2) (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d))) with hc'
  have hcen : ∀ x : PkgI3.AbVar.End0 A, c' * x = x * c' := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hc', e.apply_symm_apply]
    exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') (e x)).eq
  have hnq : ∀ t : ℚ, c' ≠ algebraMap ℚ _ t := by
    intro t ht
    have h1 : Matrix.scalar (Fin 2) (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d)) =
        algebraMap ℚ _ t := by
      rw [← AlgEquiv.commutes e t, ← ht, hc', e.apply_symm_apply]
    have h2 : AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d) =
        AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C d) t := by
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, AdjoinRoot.algebraMap_eq]
        using this
    have hdeg : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num
    have h3 := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C d)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h3
    rw [h2, ← map_pow, ← map_sub] at h3
    have h4 : t ^ 2 - d = 0 :=
      (AdjoinRoot.of.injective_of_degree_ne_zero hdeg) (h3.trans (map_zero _).symm)
    nlinarith [sq_nonneg t]
  have hfree : Module.Free ℤ (PkgI3.AbVar.End A) := (hHF k A A).1
  let f := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  obtain ⟨⟨φ, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f c'
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] φ = (s : ℤ) • c' := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) f).mp hm
    rw [Submonoid.smul_def] at hs'
    exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')
  refine ⟨φ, ?_, ?_⟩
  · rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have key : (1 : ℚ) ⊗ₜ[ℤ] (q.iota a * φ - φ * q.iota a) = 0 := by
      have e1 : ∀ x y : PkgI3.AbVar.End A,
          (1 : ℚ) ⊗ₜ[ℤ] (x * y) = ((1 : ℚ) ⊗ₜ[ℤ] x) * ((1 : ℚ) ⊗ₜ[ℤ] y) := by
        intro x y; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
      rw [TensorProduct.tmul_sub, e1, e1, hs', mul_smul_comm, smul_mul_assoc, ← smul_sub,
        hcen, sub_self, smul_zero]
    exact sub_eq_zero.mp (hinj _ key)
  · intro n hn
    apply hnq ((n : ℚ) / (s : ℤ))
    have h1 : algebraMap ℚ (PkgI3.AbVar.End0 A) ((s : ℤ) : ℚ) * c' =
        algebraMap ℚ (PkgI3.AbVar.End0 A) (n : ℚ) := by
      rw [map_intCast, map_intCast, ← zsmul_eq_mul, ← hs', hn]
      exact map_intCast (Algebra.TensorProduct.includeRight :
        PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) n
    have hs1 : ((s : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs0
    calc c' = algebraMap ℚ (PkgI3.AbVar.End0 A) (((s : ℤ) : ℚ)⁻¹) *
          (algebraMap ℚ (PkgI3.AbVar.End0 A) ((s : ℤ) : ℚ) * c') := by
          rw [← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hs1, map_one, _root_.one_mul]
      _ = algebraMap ℚ _ ((n : ℚ) / (s : ℤ)) := by
          rw [h1, ← map_mul, div_eq_inv_mul]

end G0FibreSimple

end

end FS4Copy


/-! ## §6.10 `𝒪` is a maximal order (proved)

An element of `B` integral over `ℤ` has integral reduced trace and norm (division by
`X² - tX + n`, Gauss's lemma `IsIntegrallyClosed.eq_map_mul_C_of_dvd`). For `x` in an order
`R ⊇ 𝒪`, the traces `t₁..t₄` of `x·1, x·i, x·(1+j)/2, x·(i+k)/2` and `nrd(x)` are integers;
`24·nrd(x) = 6t₁² - 3t₂² + 2(t₁-2t₃)² - (2t₄-t₂)²`, and the congruences mod 3 and mod 8
(`decide` on `ZMod 3`, `ZMod 8`) put `x` in `𝒪`. (Python check: of the 36 classes of `𝒪^∨/𝒪`,
only `0` has integral norm.) -/

section OMaxSec

open Polynomial


namespace G0ModField.KernelField

/-- The reduced norm form of `B = (2,-3)_ℚ`. -/
def nrdB (x : LeafQM.B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

/-- **An element of `B` integral over `ℤ` has integral reduced trace and norm.** -/
theorem int_of_integral {x : LeafQM.B} (hx : IsIntegral ℤ x) :
    (∃ t : ℤ, 2 * x.re = t) ∧ ∃ n : ℤ, nrdB x = n := by
  by_cases hq : x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0
  · -- `x ∈ ℚ`
    obtain ⟨h1, h2, h3⟩ := hq
    have hxr : x = algebraMap ℚ LeafQM.B x.re := by
      ext <;> simp [QuaternionAlgebra.algebraMap_eq, h1, h2, h3]
    have hint : IsIntegral ℤ x.re := by
      rw [hxr] at hx
      exact (isIntegral_algHom_iff ((Algebra.ofId ℚ LeafQM.B).restrictScalars ℤ)
        (algebraMap ℚ LeafQM.B).injective).mp hx
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hk' : x.re = k := by rw [← hk]; rfl
    refine ⟨⟨2 * k, by rw [hk']; push_cast; ring⟩, ⟨k ^ 2, ?_⟩⟩
    simp only [nrdB, hk', h1, h2, h3]; push_cast; ring
  · obtain ⟨p, hpm, hpx⟩ := hx
    set t : ℚ := 2 * x.re
    set n : ℚ := nrdB x
    let q : ℚ[X] := X ^ 2 - C t * X + C n
    have hqm : q.Monic := by
      have : q = X ^ 2 + (-(C t) * X + C n) := by ring
      rw [this]
      refine Monic.add_of_left (monic_X_pow 2) ?_
      refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · calc (-(C t) * X).degree ≤ 1 := by
              rw [← C_neg]; exact degree_C_mul_X_le _
          _ < (X ^ 2 : ℚ[X]).degree := by rw [degree_X_pow]; norm_num
      · calc (C n).degree ≤ 0 := degree_C_le
          _ < (X ^ 2 : ℚ[X]).degree := by rw [degree_X_pow]; norm_num
    have hqx : aeval x q = 0 := by
      simp only [q, map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X]
      ext <;> simp [sq, QuaternionAlgebra.algebraMap_eq, t, n, nrdB] <;> ring
    have hpx' : aeval x (p.map (algebraMap ℤ ℚ)) = 0 := by
      rw [aeval_map_algebraMap]; exact hpx
    set r := p.map (algebraMap ℤ ℚ) %ₘ q with hr
    have hrx : aeval x r = 0 := by
      have e := modByMonic_add_div (p.map (algebraMap ℤ ℚ)) q
      have := congrArg (aeval x) e
      rw [map_add, map_mul, hqx, zero_mul, add_zero, hpx'] at this
      exact this
    have hq2 : q.natDegree = 2 := by
      simp only [q]; compute_degree!
    have hrdeg : r.degree ≤ 1 := by
      have := natDegree_modByMonic_lt (p.map (algebraMap ℤ ℚ)) hqm
        (fun h => by rw [h, natDegree_one] at hq2; exact absurd hq2 (by norm_num))
      rw [hq2] at this
      exact degree_le_of_natDegree_le (Nat.lt_succ_iff.mp this)
    have hr0 : r = 0 := by
      rw [eq_X_add_C_of_degree_le_one hrdeg] at hrx ⊢
      simp only [map_add, map_mul, aeval_C, aeval_X] at hrx
      have e1 := congrArg QuaternionAlgebra.imI hrx
      have e2 := congrArg QuaternionAlgebra.imJ hrx
      have e3 := congrArg QuaternionAlgebra.imK hrx
      have e0 := congrArg QuaternionAlgebra.re hrx
      simp [QuaternionAlgebra.algebraMap_eq] at e0 e1 e2 e3
      have hc1 : r.coeff 1 = 0 := by
        by_contra hc
        apply hq
        exact ⟨(e1.resolve_left hc), (e2.resolve_left hc), (e3.resolve_left hc)⟩
      rw [hc1] at e0 ⊢
      simp at e0
      simp [e0]
    have hdvd : q ∣ p.map (algebraMap ℤ ℚ) := (modByMonic_eq_zero_iff_dvd hqm).mp hr0
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hpm hdvd
    rw [hqm.leadingCoeff, C_1, _root_.mul_one] at hg
    have c1 := congrArg (fun f : ℚ[X] => f.coeff 1) hg
    have c0 := congrArg (fun f : ℚ[X] => f.coeff 0) hg
    simp [q, coeff_X, coeff_C] at c1 c0
    refine ⟨⟨-g.coeff 1, ?_⟩, ⟨g.coeff 0, ?_⟩⟩
    · push_cast; linarith
    · linarith

end G0ModField.KernelField

namespace G0ModField.KernelField

theorem zmod3_aux : ∀ u v : ZMod 3, 2 * u ^ 2 - v ^ 2 = 0 → u = 0 ∧ v = 0 := by decide

theorem zmod8_aux : ∀ a b c d : ZMod 8,
    6 * a ^ 2 - 3 * b ^ 2 + 2 * (a - 2 * c) ^ 2 - (2 * d - b) ^ 2 = 0 → 4 * b = 0 ∧ 4 * d = 0 := by
  decide


/-- `𝒪` is a maximal order (statement as `OMaximal` in `New.lean`). -/
theorem oMaximal' : ∀ R : Subring LeafQM.B, LeafQM.O ≤ R → (∀ x ∈ R, IsIntegral ℤ x) →
    R ≤ LeafQM.O := by
  intro R hOR hint x hx
  have hmem : ∀ v : Fin 4 → ℤ, x * LeafQM.ofInt v ∈ R := fun v =>
    R.mul_mem hx (hOR ⟨v, rfl⟩)
  obtain ⟨⟨t1, ht1⟩, ⟨nn, hnn⟩⟩ := int_of_integral (hint x hx)
  obtain ⟨⟨t2, ht2⟩, -⟩ := int_of_integral (hint _ (hmem ![0, 1, 0, 0]))
  obtain ⟨⟨t3, ht3⟩, -⟩ := int_of_integral (hint _ (hmem ![0, 0, 1, 0]))
  obtain ⟨⟨t4, ht4⟩, -⟩ := int_of_integral (hint _ (hmem ![0, 0, 0, 1]))
  simp [LeafQM.ofInt, QuaternionAlgebra.re_mul] at ht2 ht3 ht4
  unfold nrdB at hnn
  set a := x.re
  set b := x.imI
  set c := x.imJ
  set d := x.imK
  -- `a = t1/2`, `b = t2/4`, `c = (t1 - 2 t3)/6`, `d = (2 t4 - t2)/12`
  have hQ : 6 * t1 ^ 2 - 3 * t2 ^ 2 + 2 * (t1 - 2 * t3) ^ 2 - (2 * t4 - t2) ^ 2 = 24 * nn := by
    have : ((6 * t1 ^ 2 - 3 * t2 ^ 2 + 2 * (t1 - 2 * t3) ^ 2 - (2 * t4 - t2) ^ 2 : ℤ) : ℚ) =
        ((24 * nn : ℤ) : ℚ) := by
      push_cast
      rw [← ht1, ← hnn]
      have e2 : (t2 : ℚ) = 4 * b := by linarith
      have e3 : (t3 : ℚ) = a - 3 * c := by linarith
      have e4 : (t4 : ℚ) = 2 * b + 6 * d := by linarith
      rw [e2, e3, e4]; ring
    exact_mod_cast this
  -- mod 3
  set u := t1 - 2 * t3 with hu
  set v := 2 * t4 - t2 with hv
  have h3dvd : (3 : ℤ) ∣ 2 * u ^ 2 - v ^ 2 :=
    ⟨8 * nn - 2 * t1 ^ 2 + t2 ^ 2, by linear_combination hQ⟩
  have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3dvd
  push_cast at h3
  obtain ⟨hu3, hv3⟩ := zmod3_aux _ _ h3
  obtain ⟨u', hu'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd u 3).mp hu3
  obtain ⟨v', hv'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd v 3).mp hv3
  -- mod 8
  have h8dvd : (8 : ℤ) ∣ 6 * t1 ^ 2 - 3 * t2 ^ 2 + 2 * (t1 - 2 * t3) ^ 2 - (2 * t4 - t2) ^ 2 :=
    ⟨3 * nn, by rw [hQ]; ring⟩
  have h8 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h8dvd
  push_cast at h8
  obtain ⟨hb8, hd8⟩ := zmod8_aux _ _ _ _ h8
  have hb2 : (8 : ℤ) ∣ 4 * t2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact hb8)
  have hd2 : (8 : ℤ) ∣ 4 * t4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact hd8)
  obtain ⟨s2, hs2⟩ : ∃ s, t2 = 2 * s := ⟨t2 / 2, by omega⟩
  obtain ⟨s4, hs4⟩ : ∃ s, t4 = 2 * s := ⟨t4 / 2, by omega⟩
  -- the coordinates of `x` in `𝒪`
  have hn2 : 2 * c = u' := by
    have : (u : ℚ) = 3 * u' := by exact_mod_cast hu'
    rw [hu] at this; push_cast at this; linarith
  obtain ⟨w, hw⟩ : ∃ w : ℤ, v' = 2 * w := ⟨v' / 2, by omega⟩
  have hn3 : 2 * d = w := by
    have : (v : ℚ) = 3 * v' := by exact_mod_cast hv'
    rw [hv] at this; push_cast at this
    have : (v' : ℚ) = 2 * w := by exact_mod_cast hw
    linarith
  have hvz : 2 * t4 - t2 = 3 * v' := by rw [← hv, hv']; norm_num
  have hvq : (3 * v' : ℚ) = 4 * s4 - 2 * s2 := by
    have : 3 * v' = 4 * s4 - 2 * s2 := by rw [← hvz, hs2, hs4]; ring
    exact_mod_cast this
  have es4 : (t4 : ℚ) = 2 * s4 := by exact_mod_cast hs4
  refine ⟨![t3 + u', s4 - v', u', w], ?_⟩
  have e2 : (t2 : ℚ) = 4 * b := by linarith
  have e3 : (t3 : ℚ) = a - 3 * c := by linarith
  have e4 : (t4 : ℚ) = 2 * b + 6 * d := by linarith
  have es2 : (t2 : ℚ) = 2 * s2 := by exact_mod_cast hs2
  ext <;> simp [LeafQM.ofInt] <;> linarith

end G0ModField.KernelField

end OMaxSec

section EndEqOSec

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Quaternion

namespace G0ModField.KernelField

/-- **Remaining glue 4a′ (pure algebra): `𝒪` is a maximal order of `B = (2,-3)_ℚ`.** A subring of
`B` containing `𝒪` whose elements are integral over `ℤ` is contained in `𝒪`. STANDARD (the
order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` has reduced discriminant `6 = disc B`; Vignéras,
*Arithmétique des algèbres de quaternions*, III §5, UNVERIFIED locator). A finite lattice
computation, proved below (`oMaximal`). -/
def OMaximal : Prop :=
  ∀ R : Subring LeafQM.B, LeafQM.O ≤ R → (∀ x ∈ R, IsIntegral ℤ x) → R ≤ LeafQM.O

/-- **`OMaximal`, proved** (§6.10). -/
theorem oMaximal : OMaximal := oMaximal'

/-- **`EndEqOFibre` from T27 (Yu), T6 (Mumford §19 Thm 3) and `OMaximal` (proved).** -/
theorem endEqOFibre_of (t27 : PkgI3.QMDichotomyYu) (hHF : PkgI3.HomFreeFinite)
    (hmax : OMaximal) : EndEqOFibre := by
  intro P hcom f
  have hY := PkgI3.qmDichotomy_B6 t27 Qbar P.A P.surface G0FibreSimple.B6_isUnit
    (G0FibreSimple.qm_embeds_end0 P.q)
  have hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) := by
    rcases hY with hB | ⟨d, hd, hM⟩
    · exact hB
    · exfalso
      obtain ⟨φ, hφ, hne⟩ :=
        G0FibreSimple.centralizerOfMatrixEnd0_of_homFree hHF Qbar P.A P.q d hd hM
      obtain ⟨n, hn⟩ := hcom φ hφ
      exact hne n hn
  obtain ⟨e⟩ := hB
  let φ : LeafQM.B →ₐ[ℚ] PkgI3.AbVar.End0 P.A := (G0FibreSimple.qmBasis P.q).liftHom
  haveI : Nontrivial (PkgI3.AbVar.End0 P.A) := e.toEquiv.nontrivial
  have hinj : Function.Injective φ := φ.toRingHom.injective
  haveI : FiniteDimensional ℚ (PkgI3.AbVar.End0 P.A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hrank : Module.finrank ℚ LeafQM.B = Module.finrank ℚ (PkgI3.AbVar.End0 P.A) :=
    e.toLinearEquiv.finrank_eq.symm
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).mp hinj
  let j : PkgI3.AbVar.End P.A →ₐ[ℤ] PkgI3.AbVar.End0 P.A := Algebra.TensorProduct.includeRight
  have hfree : Module.Free ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar P.A P.A).1
  haveI : Module.Finite ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar P.A P.A).2.1
  let tm := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End P.A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End P.A) (S := ℚ))
  have hjinj : Function.Injective j := by
    intro x y hxy
    have hm : (1 : ℚ) ⊗ₜ[ℤ] (x - y) = 0 := by
      rw [TensorProduct.tmul_sub]
      exact sub_eq_zero.mpr hxy
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) tm).mp hm
    rw [Submonoid.smul_def] at hs'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s'))
  -- `φ` agrees with `j ∘ ι` on `𝒪`
  have hagree : ∀ a : LeafQM.O, φ (a : LeafQM.B) = j (P.q.iota a) := by
    let ψ1 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := φ.toRingHom.comp (Subring.subtype _)
    let ψ2 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := j.toRingHom.comp P.q.iota
    have hi : ψ1 G0FibreSimple.oi = ψ2 G0FibreSimple.oi := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oi : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oi, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    have hj : ψ1 G0FibreSimple.oj = ψ2 G0FibreSimple.oj := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oj : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oj, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    intro a
    obtain ⟨n, hn⟩ := a.2
    have h2 : (2 : LeafQM.O) * a = ((2 * n 0 + n 2 : ℤ) : LeafQM.O) +
        ((2 * n 1 + n 3 : ℤ) : LeafQM.O) * G0FibreSimple.oi +
        ((n 2 : ℤ) : LeafQM.O) * G0FibreSimple.oj +
        ((n 3 : ℤ) : LeafQM.O) * (G0FibreSimple.oi * G0FibreSimple.oj) := by
      apply Subtype.ext
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
      rw [show ((2 : LeafQM.O) : LeafQM.B) = 2 from rfl, hn]
      ext <;> simp [G0FibreSimple.oi, G0FibreSimple.oj, LeafQM.ofInt, QuaternionAlgebra.re_ofNat,
        QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;>
        ring
    have key : ∀ ψ : LeafQM.O →+* PkgI3.AbVar.End0 P.A, ψ ((2 : LeafQM.O) * a) =
        ((2 * n 0 + n 2 : ℤ) : PkgI3.AbVar.End0 P.A) +
        ((2 * n 1 + n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oi +
        ((n 2 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oj +
        ((n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * (ψ G0FibreSimple.oi * ψ G0FibreSimple.oj) := by
      intro ψ
      rw [h2]; simp only [map_add, map_mul, map_intCast]
    have e1 : (2 : PkgI3.AbVar.End0 P.A) * ψ1 a = (2 : PkgI3.AbVar.End0 P.A) * ψ2 a := by
      have := key ψ1
      rw [map_mul, map_ofNat] at this
      rw [this, hi, hj, ← key ψ2, map_mul, map_ofNat]
    have e2 : (2 : ℚ) • ψ1 a = (2 : ℚ) • ψ2 a := by
      rw [two_smul, two_smul, ← two_mul, ← two_mul]; exact e1
    exact smul_right_injective (PkgI3.AbVar.End0 P.A) (two_ne_zero : (2 : ℚ) ≠ 0) e2
  -- the order `R = φ⁻¹(End)`
  let R : Subring LeafQM.B := (j.toRingHom.range).comap φ.toRingHom
  have hOR : LeafQM.O ≤ R := fun x hx => ⟨P.q.iota ⟨x, hx⟩, (hagree ⟨x, hx⟩).symm⟩
  have hint : ∀ x ∈ R, IsIntegral ℤ x := by
    rintro x ⟨g, hg⟩
    have h1 : IsIntegral ℤ g := Algebra.IsIntegral.isIntegral g
    have h2 : IsIntegral ℤ (φ x) := by
      have := h1.map j
      rwa [show j g = φ x from hg] at this
    exact (isIntegral_algHom_iff (φ.restrictScalars ℤ) hinj).mp h2
  obtain ⟨x, hx⟩ := hsurj (j f)
  have hxO : x ∈ LeafQM.O := hmax R hOR hint ⟨f, hx.symm⟩
  refine ⟨⟨x, hxO⟩, hjinj ?_⟩
  rw [← hagree, ← hx]

/-- **Headline, with the NoCM side down to leaves + FS5 + `OMaximal` (proved).** Leaves:
`HomFreeFinite` (T6), `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`,
`QMDichotomyYu` (T27). Glue: FS5 `FibreComTrivial`, `OMaximal` (pure algebra),
`EndTransport`, `ConjIsogMaps`. -/
theorem kernelFieldExists_of_split'' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hmax : OMaximal) (hb : EndTransport)
    (hG : ConjIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_split' hHFF hNOS hRay hTors h5 hG (endEqOFibre_of t27 hHFF hmax) hb

/-- **Headline, final split form (proved).** `KernelFieldExists` from the leaves `HomFreeFinite`
(T6), `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, `QMDichotomyYu` (T27) and the
glue FS5 `FibreComTrivial`, `EndTransport`, `ConjIsogMaps`. -/
theorem kernelFieldExists_of_final (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hb : EndTransport) (hG : ConjIsogMaps) :
    KernelFieldExists :=
  kernelFieldExists_of_split'' hHFF hNOS hRay hTors t27 h5 oMaximal hb hG


/-- `End = ι(𝒪)` moves along an isomorphism of `QML3` objects (proved). -/
theorem endEqO_of_iso {k : Type} [Field k] {P Q : QML3 k} (e : QML3.Iso Q P)
    (h : ∀ f : PkgI3.AbVar.End P.A, ∃ a : LeafQM.O, f = P.q.iota a) :
    ∀ g : PkgI3.AbVar.End Q.A, ∃ a : LeafQM.O, g = Q.q.iota a := by
  intro g
  let g' : PkgI3.AbVar.End P.A := PkgI3.AbVar.Hom.mk' (e.ψ.hom ≫ g.hom ≫ e.φ.hom)
  obtain ⟨a, ha⟩ := h g'
  refine ⟨a, PkgI3.AbVar.Hom.ext' ?_⟩
  have h1 : g.hom = e.φ.hom ≫ g'.hom ≫ e.ψ.hom := by
    change g.hom = e.φ.hom ≫ (e.ψ.hom ≫ g.hom ≫ e.φ.hom) ≫ e.ψ.hom
    simp only [Category.assoc, e.left, Category.comp_id]
    rw [← Category.assoc, e.left, Category.id_comp]
  rw [h1, ha, ← Category.assoc, ← e.equivariant a, Category.assoc, e.left, Category.comp_id]

/-- **Remaining glue 4b′ (base change and rigidity).** For a base change `Q` of `PK` along
`K ⊆ ℚ̄` (`IsBaseChangeOf`, a pullback square compatible with `ι` and `η`): if
`End(Q.A) = ι_Q(𝒪)`, then `End_L(A_L) = ι_L(𝒪)` for every `L ⊇ K`. *Argument* (model check):
`(A_L)_ℚ̄` and `Q.A` are two pullbacks of `PK.A` along `Spec ℚ̄ → Spec K` (pasting), hence
isomorphic as `ℚ̄`-schemes; the isomorphism preserves the identity (`η(0) = 0`), so it is a
homomorphism by rigidity (g0-fibresimple's leaf `RigidityHom`, Mumford §4 Cor. 1), and it carries
the base change of `ι_L(a)` to `ι_Q(a)`; an `f ∈ End_L(A_L)` has base change `ι_Q(a)` for some
`a`, so `f = ι_L(a)` because base change along `Spec ℚ̄ → Spec L` is faithful (fpqc;
bp-qmmoduli's `endBC_injective`). `IsBaseChangeOf` records no group law, which is why rigidity
is needed. -/
def EndTransportBC : Prop :=
  ∀ (K : IF) (PK : QML3 K) (Q : QML3 Qbar), IsBaseChangeOf (K.val : K →+* Qbar) PK Q →
    (∀ g : PkgI3.AbVar.End Q.A, ∃ a : LeafQM.O, g = Q.q.iota a) →
    ∀ (L : IF) (hKL : K ≤ L),
      ∀ f : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
        ∃ a : LeafQM.O, f = ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) a

/-- `EndTransport` from `EndTransportBC` (proved: R1's naturality at `K ⊆ ℚ̄` gives the base
change `Q` of `PK` with `[Q] = [P]`, so `Q ≅ P`, and `endEqO_of_iso`). -/
theorem endTransport_of (h : EndTransportBC) : EndTransport := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ hEndP K _ _ PK hPK L _ _ hKL hfix f
  obtain ⟨⟨yK, hyK, hyKP⟩, -⟩ := hPK
  obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2 K Qbar K.val yK PK hyK
  have hQP : M3.mk Q = M3.mk P := hQ.symm.trans hyKP
  obtain ⟨e⟩ := Quotient.exact hQP
  exact h K PK Q hbc (endEqO_of_iso e hEndP) L hKL f

/-- **Headline, final form with `EndTransportBC` (proved).** -/
theorem kernelFieldExists_of_final' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hbc : EndTransportBC) (hG : ConjIsogMaps) :
    KernelFieldExists :=
  kernelFieldExists_of_final hHFF hNOS hRay hTors t27 h5 (endTransport_of hbc) hG

end G0ModField.KernelField

end EndEqOSec


/-! ## §6.11 `EndTransportBC` from rigidity (attempt)

Copied verbatim: `RigidityHom` (g0-fibresimple `Tail.lean` lines 357-363) and the faithful base
change instances and `endBC_injective` (bp-qmmoduli `QMAbVar.lean` lines 558-575, `AbVar`
qualified). -/

section RigCopy

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace G0FibreSimple


/-- **Textbook leaf (rigidity; Mumford, *Abelian varieties*, §4 Cor. 1; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Cor. 2.2, over any field; locators UNVERIFIED).** A morphism
of `k`-schemes between abelian varieties that sends the identity to the identity is a
homomorphism. -/
def RigidityHom : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k) (h : A.X ⟶ B.X), η[A.X] ≫ h = η[B.X] → IsMonHom h

end G0FibreSimple

namespace G0ModField.KernelField

variable {K : Type} [Field K]

/-- `Spec L → Spec K` is flat, surjective and quasi-compact, so `Over.pullback` along it is
faithful (Mathlib, `Morphisms/FlatDescent.lean`). -/
instance specMap_flat (L : Type) [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance specMap_surjective (L : Type) [Field L] [Algebra K L] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- Base change on endomorphisms is injective. -/
theorem endBC_injective (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    Function.Injective (endBC A L) := by
  intro f g h
  apply PkgI3.AbVar.Hom.ext'
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map_injective
    (congrArg PkgI3.AbVar.Hom.hom h)

end G0ModField.KernelField

end RigCopy

section RigProof

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open LeafQM.AV

namespace G0ModField.KernelField

/-- **`EndTransportBC` from the textbook leaf `RigidityHom` (proved).** -/
theorem endTransportBC_of_rigidity (hR : G0FibreSimple.RigidityHom) : EndTransportBC := by
  intro K PK Q hbc hEndQ L hKL f
  letI : Algebra K L := incAlg hKL
  obtain ⟨g, hpb, hι, hη⟩ := hbc
  let sKL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let sLQ := Spec.map (CommRingCat.ofHom (algebraMap L Qbar))
  let AL : PkgI3.AbVar L := PK.A.baseChange L
  let ALQ : PkgI3.AbVar Qbar := AL.baseChange Qbar
  have hcomp : sLQ ≫ sKL = Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) := by
    rw [← Spec.map_comp]; congr 1
  have hpb1 : IsPullback (pullback.fst AL.X.hom sLQ) (pullback.snd AL.X.hom sLQ) AL.X.hom sLQ :=
    IsPullback.of_hasPullback _ _
  have hpb2 : IsPullback (pullback.fst PK.A.X.hom sKL) (pullback.snd PK.A.X.hom sKL)
      PK.A.X.hom sKL := IsPullback.of_hasPullback _ _
  have hpb3 : IsPullback (pullback.fst AL.X.hom sLQ ≫ pullback.fst PK.A.X.hom sKL)
      (pullback.snd AL.X.hom sLQ) PK.A.X.hom
      (Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar))) := by
    rw [← hcomp]; exact hpb1.paste_horiz hpb2
  let θ : ALQ.X.left ≅ Q.A.X.left := hpb3.isoIsPullback _ _ hpb
  have hθfst : θ.hom ≫ g =
      (pullback.fst AL.X.hom sLQ ≫ pullback.fst PK.A.X.hom sKL : ALQ.X.left ⟶ PK.A.X.left) :=
    hpb3.isoIsPullback_hom_fst _ _ hpb
  have hθsnd : θ.hom ≫ Q.A.X.hom = (pullback.snd AL.X.hom sLQ : ALQ.X.left ⟶ _) :=
    hpb3.isoIsPullback_hom_snd _ _ hpb
  let h : ALQ.X ⟶ Q.A.X := Over.homMk θ.hom hθsnd
  let hinv : Q.A.X ⟶ ALQ.X := Over.homMk θ.inv ((Iso.inv_comp_eq θ).mpr hθsnd.symm)
  have hhi : h ≫ hinv = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.hom_inv_id
  have hih : hinv ≫ h = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.inv_hom_id
  -- the identity sections correspond
  have hu : ∀ {R : Type} [Field R] {U : Over (Spec (CommRingCat.of R))},
      (toUnit U).left = U.hom := fun {R _ U} => by
    have := Over.w (toUnit U); simpa using this
  have hid : ∀ (R : Type) [Field R], Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ :=
    fun R _ => by rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hηQ : η[Q.A.X].left ≫ g =
      Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ η[PK.A.X].left := by
    have := hη 0
    have h0Q : Additive.toMul (Q.e.eta 0) = 1 := by rw [map_zero]; rfl
    have h0P : Additive.toMul (PK.e.eta 0) = 1 := by rw [map_zero]; rfl
    rw [h0Q, h0P] at this
    change (toUnit (PkgI3.AbVar.ptObj (K := Qbar) Qbar) ≫ η[Q.A.X]).left ≫ g =
      Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫
        (toUnit (PkgI3.AbVar.ptObj (K := K) K) ≫ η[PK.A.X]).left at this
    rw [Over.comp_left, Over.comp_left, hu, hu] at this
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, hid, Category.assoc] at this
    erw [Category.id_comp, Category.id_comp] at this
    exact this
  have hηW : η[ALQ.X].left ≫ pullback.fst AL.X.hom sLQ ≫ pullback.fst PK.A.X.hom sKL =
      Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ η[PK.A.X].left := by
    have e1 := G4Conj.one_left_fst sLQ AL.X
    have e2 := G4Conj.one_left_fst sKL PK.A.X
    calc η[ALQ.X].left ≫ pullback.fst AL.X.hom sLQ ≫ pullback.fst PK.A.X.hom sKL
        = (η[ALQ.X].left ≫ pullback.fst AL.X.hom sLQ) ≫ pullback.fst PK.A.X.hom sKL :=
          (Category.assoc _ _ _).symm
      _ = (sLQ ≫ η[AL.X].left) ≫ pullback.fst PK.A.X.hom sKL := by erw [e1]
      _ = sLQ ≫ (η[AL.X].left ≫ pullback.fst PK.A.X.hom sKL) := Category.assoc _ _ _
      _ = sLQ ≫ (sKL ≫ η[PK.A.X].left) := by erw [e2]
      _ = _ := by rw [← Category.assoc, hcomp]
  have hunit : η[ALQ.X] ≫ h = η[Q.A.X] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply hpb.hom_ext
    · show η[ALQ.X].left ≫ θ.hom ≫ g = η[Q.A.X].left ≫ g
      rw [hθfst, hηW, hηQ]
    · rw [Category.assoc, Over.w h, Over.w η[ALQ.X], Over.w η[Q.A.X]]
  have hunit' : η[Q.A.X] ≫ hinv = η[ALQ.X] := by
    rw [← hunit, Category.assoc, hhi, Category.comp_id]
  haveI hmh : IsMonHom h := hR Qbar ALQ Q.A h hunit
  haveI hmi : IsMonHom hinv := hR Qbar Q.A ALQ hinv hunit'
  -- transport `f` to `Q.A`
  let g' : PkgI3.AbVar.End Q.A := PkgI3.AbVar.Hom.mk' (hinv ≫ (endBC AL Qbar f).hom ≫ h)
  obtain ⟨a, ha⟩ := hEndQ g'
  have hf1 : (endBC AL Qbar f).hom = h ≫ (Q.q.iota a).hom ≫ hinv := by
    have : g'.hom = (Q.q.iota a).hom := by rw [ha]
    change hinv ≫ (endBC AL Qbar f).hom ≫ h = _ at this
    rw [← this]
    simp only [← Category.assoc, hhi, Category.id_comp]
    rw [Category.assoc, hhi, Category.comp_id]
  have hf2 : (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom ≫ h = h ≫ (Q.q.iota a).hom := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    apply hpb.hom_ext
    · change (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom.left ≫ θ.hom ≫ g =
        θ.hom ≫ (Q.q.iota a).hom.left ≫ g
      have hm1 : (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom.left ≫
          (pullback.fst AL.X.hom sLQ : ALQ.X.left ⟶ AL.X.left) =
          (pullback.fst AL.X.hom sLQ : ALQ.X.left ⟶ AL.X.left) ≫
            (endBC PK.A L (PK.q.iota a)).hom.left :=
        pullback.lift_fst _ _ _
      have hm2 : (endBC PK.A L (PK.q.iota a)).hom.left ≫
          (pullback.fst PK.A.X.hom sKL : AL.X.left ⟶ PK.A.X.left) =
          (pullback.fst PK.A.X.hom sKL : AL.X.left ⟶ PK.A.X.left) ≫ (PK.q.iota a).hom.left :=
        pullback.lift_fst _ _ _
      rw [hι a, hθfst, ← Category.assoc θ.hom g, hθfst]
      have key : (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom.left ≫
          ((pullback.fst AL.X.hom sLQ : ALQ.X.left ⟶ AL.X.left) ≫
            (pullback.fst PK.A.X.hom sKL : AL.X.left ⟶ PK.A.X.left)) =
          ((pullback.fst AL.X.hom sLQ : ALQ.X.left ⟶ AL.X.left) ≫
            (pullback.fst PK.A.X.hom sKL : AL.X.left ⟶ PK.A.X.left)) ≫ (PK.q.iota a).hom.left := by
        erw [← Category.assoc, hm1, Category.assoc, hm2, Category.assoc]
        rfl
      exact key
    · rw [Category.assoc, Category.assoc, Over.w h, Over.w (Q.q.iota a).hom, Over.w h]
      exact Over.w ((Over.pullback sLQ).map ((Over.pullback sKL).map (PK.q.iota a).hom))
  have hf3 : (endBC AL Qbar f).hom = (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom := by
    rw [hf1, ← Category.assoc, ← hf2, Category.assoc, hhi, Category.comp_id]
  refine ⟨a, endBC_injective AL Qbar (PkgI3.AbVar.Hom.ext' hf3)⟩

/-- **Headline (proved): `KernelFieldExists` from six leaves and two glue Props.** Leaves:
`HomFreeFinite` (T6), `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`,
`QMDichotomyYu` (T27), `RigidityHom` (Mumford §4 Cor. 1; g0-fibresimple's textbook leaf). Glue:
FS5 `FibreComTrivial` (g0-fibresimple) and `ConjIsogMaps`. -/
theorem kernelFieldExists_of_rigidity (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (hRig : G0FibreSimple.RigidityHom) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_final' hHFF hNOS hRay hTors t27 h5 (endTransportBC_of_rigidity hRig) hG

end G0ModField.KernelField

end RigProof

#print axioms G0ModField.KernelField.conjMaps_of_qm
#print axioms G0ModField.KernelField.conjIsogMapsAt_bot
#print axioms G0ModField.KernelField.kernelFieldExists_of_split
#print axioms G0ModField.KernelField.kernelFieldExists_of_split'
#print axioms G0ModField.KernelField.kernelFieldExists_of_split''
#print axioms G0ModField.KernelField.endEqOFibre_of
#print axioms G0ModField.KernelField.oMaximal
#print axioms G0ModField.KernelField.kernelFieldExists_of_final
#print axioms G0ModField.KernelField.kernelFieldExists_of_final'
#print axioms G0ModField.KernelField.endTransportBC_of_rigidity
#print axioms G0ModField.KernelField.kernelFieldExists_of_rigidity
#print axioms G0ModField.KernelField.faithful_O
#print axioms G0ModField.KernelField.blinear_of_twisted_iso
#print axioms G0ModField.KernelField.center_O
#print axioms G0ModField.KernelField.aut_O_inner
#print axioms G0ModField.KernelField.kernelFieldExists_of_leaves_FS5
#print axioms G0ModField.KernelField.kernelFieldExists_of_leaves
#print axioms G0ModField.KernelField.conjugacyData_of_maps
#print axioms G0ModField.KernelField.kernelField_core
#print axioms G0ModField.KernelField.kernelField_of_model
#print axioms G0ModField.KernelField.good_of_QML3
#print axioms G0ModField.KernelField.conj_dim
#print axioms G0ModField.KernelField.kernelFieldExists_of_pieces
#print axioms G0ModField.KernelField.torsionCountPts_of_leaf

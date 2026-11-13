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

end G0ModField.KernelField

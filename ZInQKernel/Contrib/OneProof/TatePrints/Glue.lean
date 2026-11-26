import ZInQKernel.Contrib.OneProof.VpDualMerge.Row
import ZInQKernel.Contrib.OneProof.TatePrints.Rows

/-!
# tate-module-prints: the glue from the two rows to `VpDualDeRhamAbVar`

`vpDual_of_colmezFontaine : Colmez1992DeRhamAbVar → Fontaine1982HTAbVar → VpDualDeRhamAbVar`,
derived in Lean from the two single-print rows of `TatePrints/Rows.lean` and results proved in the
tree. Notation: `ρ = A.galRep p` on `V = V_p(A)`, `D = ddrSpaceOver p ρ = Hom_{G_F}(V, B_dR)` (the
Hom form of `D_dR(V^∨)`), `htSpaceOver p ρ j = Hom_{G_F}(V, ℂ_p(j))`.

* §1 (`Gen`, pure linear algebra): a family of `G`-equivariant maps `V → B` (`B` a field) that is
  non-degenerate after base change to `B` spans `Hom_K(V, B)` over `B` (`span_eq_top_of_nondeg`);
  it then contains a basis, whose coordinates of an equivariant map are invariant, so
  `dim_K Hom_G(V, B) = dim_K B^G · dim_K V` (`finrank_of_nondeg`), and the values of every
  equivariant map lie in any subring containing `B^G` and the values of the family
  (`forall_prop_of_nondeg`).
* §2 (G1): from R1, `dim_{ℚ_p} D = [F:ℚ_p] · dim V` and `D ⊆ Hom(V, B_dR⁺)`
  (`dual_deRham_fil0_of_colmez`). The coordinates lie in `B_dR^{G_F}`, whose nonzero elements are
  units of `B_dR⁺` (`BdRInv.key`); the dimension of `B_dR^{G_F}` is `bdRInvariantsPrinted_proof`.
* §3 (G2): from `dim Hom_{G_F}(V, ℂ_p) + dim Hom_{G_F}(V, ℂ_p(1)) = dim V`, Hodge-Tate spaces of
  every other weight vanish (`htSpaceOver_eq_bot_of_card`; Tate's theorems, proved in the tree).
* §4 (G3): `D ∩ Fil² = 0` when the Hodge-Tate spaces of the weights `j ≥ 2` vanish
  (`ddr_inf_filH_two_eq_bot`): `gr^j : D ∩ Fil^j → Hom_{G_F}(V, ℂ_p(j))` has kernel in `Fil^{j+1}`,
  and `⋂_j Fil^j B_dR⁺ = 0` (Krull, `B_dR⁺` a discrete valuation ring).
* §5 (G4): assembly, with the weight-1 count from `HTAbVar.finrank_fil1_bounds`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.TatePrints

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

/-! ## §1. Linear algebra: non-degenerate families of equivariant maps -/

namespace Gen

variable {K B G V : Type*} [Field K] [Field B] [Algebra K B] [AddCommGroup V] [Module K V]

/-- Non-degeneracy on the `V` side after base change to `B` makes the family span `Hom_K(V, B)`
over `B` (`Hom_K(V, B) ≅ Hom_B(B ⊗ V, B)`, and a subspace of a finite-dimensional dual with zero
coannihilator is everything). -/
theorem span_eq_top_of_nondeg [FiniteDimensional K V] (S : Set (V →ₗ[K] B))
    (hS : ∀ x : B ⊗[K] V, (∀ φ ∈ S, φ.liftBaseChange B x = 0) → x = 0) :
    Submodule.span B S = ⊤ := by
  let e := LinearMap.liftBaseChangeEquiv (R := K) (M := V) (N := B) B
  set W : Submodule B (Module.Dual B (B ⊗[K] V)) := (Submodule.span B S).map e.toLinearMap
  have hW : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    rw [Submodule.mem_bot]
    refine hS x fun φ hφ => ?_
    have := hx (e φ) (Submodule.mem_map_of_mem (Submodule.subset_span hφ))
    simpa [e] using this
  have hW' : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW, Submodule.dualAnnihilator_bot]
  rw [eq_top_iff]
  intro f _
  have hf : e f ∈ W := hW' ▸ Submodule.mem_top
  obtain ⟨g, hg, hgf⟩ := hf
  rw [← e.injective hgf]
  exact hg

/-- `Hom_K(V, B)` has `B`-dimension `dim_K V`. -/
theorem finrank_hom [FiniteDimensional K V] : finrank B (V →ₗ[K] B) = finrank K V := by
  rw [← ((Module.finBasis K V).constr B).finrank_eq, Module.finrank_fin_fun]

/-- A spanning family of `Hom_K(V, B)` contains a `B`-basis. -/
theorem exists_basis_of_span [FiniteDimensional K V] (S : Set (V →ₗ[K] B))
    (hspan : Submodule.span B S = ⊤) :
    ∃ b : Basis (Fin (finrank K V)) B (V →ₗ[K] B), ∀ i, b i ∈ S := by
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent B S
  have hfd : FiniteDimensional B (V →ₗ[K] B) :=
    LinearEquiv.finiteDimensional ((Module.finBasis K V).constr B)
  let bT : Basis T B (V →ₗ[K] B) := Basis.mk hTli (by rw [Subtype.range_coe, hTspan, hspan])
  have : Finite T := Module.Finite.finite_basis bT
  let _ : Fintype T := Fintype.ofFinite T
  have hc : Fintype.card T = finrank K V := by
    rw [← finrank_hom (B := B), Module.finrank_eq_card_basis bT]
  refine ⟨bT.reindex (Fintype.equivFinOfCardEq hc), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hTS (Subtype.mem _)

variable (aR : G → B →+* B) (ρ : G → V →ₗ[K] V)

/-- `f ↦ f ∘ ρ g` on `Hom_K(V, B)`, a `B`-linear map. -/
def precomp (g : G) : (V →ₗ[K] B) →ₗ[B] (V →ₗ[K] B) where
  toFun f := f ∘ₗ ρ g
  map_add' _ _ := LinearMap.add_comp _ _ _
  map_smul' _ _ := LinearMap.smul_comp _ _ _

theorem precomp_injective (g : G) (hρ : Function.Surjective (ρ g)) :
    Function.Injective (precomp ρ g (B := B)) := by
  intro f f' h
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := hρ v
  exact LinearMap.congr_fun h w

/-- **The coordinates of an equivariant map in a basis of equivariant maps are invariant.** -/
theorem repr_fixed {ι : Type*} [Fintype ι] (hρ : ∀ g, Function.Surjective (ρ g))
    (b : Basis ι B (V →ₗ[K] B)) (hb : ∀ i g v, b i (ρ g v) = aR g (b i v))
    (ψ : V →ₗ[K] B) (hψ : ∀ g v, ψ (ρ g v) = aR g (ψ v)) (i : ι) (g : G) :
    aR g (b.repr ψ i) = b.repr ψ i := by
  classical
  have hli : LinearIndependent B (fun j => precomp ρ g (b j)) :=
    b.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr (precomp_injective ρ g (hρ g)))
  have hrel : ∑ j, (b.repr ψ j - aR g (b.repr ψ j)) • precomp ρ g (b j) = 0 := by
    refine LinearMap.ext fun v => ?_
    have h1 : ψ (ρ g v) = ∑ j, b.repr ψ j * aR g (b j v) := by
      conv_lhs => rw [← b.sum_repr ψ]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb]
    have h2 : aR g (ψ v) = ∑ j, aR g (b.repr ψ j) * aR g (b j v) := by
      conv_lhs => rw [← b.sum_repr ψ]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply,
      precomp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, hb, sub_mul,
      Finset.sum_sub_distrib]
    rw [← h1, ← h2, hψ, sub_self]
  have := Fintype.linearIndependent_iff.mp hli _ hrel i
  exact (sub_eq_zero.mp this).symm

/-- **Admissible implies de Rham, Hom form.** If `Hom_G(V, B)` (`D`) contains a `B`-basis of
`Hom_K(V, B)` indexed by `ι`, then `dim_K D = #ι · dim_K B^G` (`dim_K B^G = d > 0`). -/
theorem finrank_of_basis {ι : Type*} [Fintype ι] (hρ : ∀ g, Function.Surjective (ρ g))
    (D : Submodule K (V →ₗ[K] B)) (hD : ∀ φ, φ ∈ D ↔ ∀ g v, φ (ρ g v) = aR g (φ v))
    (E : Submodule K B) (hE : ∀ x, x ∈ E ↔ ∀ g, aR g x = x) {d : ℕ} (hEd : finrank K E = d)
    (hd : 0 < d) (b : Basis ι B (V →ₗ[K] B)) (hb : ∀ i, b i ∈ D) :
    finrank K D = Fintype.card ι * d := by
  classical
  haveI : FiniteDimensional K E := Module.finite_of_finrank_pos (by rw [hEd]; exact hd)
  have hb' : ∀ i g v, b i (ρ g v) = aR g (b i v) := fun i => (hD _).mp (hb i)
  let Ψ : D →ₗ[K] (ι → E) :=
    { toFun := fun ψ i => ⟨b.repr ψ i, (hE _).mpr fun g =>
        repr_fixed aR ρ hρ b hb' ψ ((hD _).mp ψ.2) i g⟩
      map_add' := fun ψ ψ' => by
        funext i; apply Subtype.ext
        simp only [Submodule.coe_add, map_add, Finsupp.add_apply, Pi.add_apply]
      map_smul' := fun c ψ => by
        funext i; apply Subtype.ext
        simp only [RingHom.id_apply, Pi.smul_apply, SetLike.val_smul]
        rw [← algebraMap_smul B c (ψ : V →ₗ[K] B), map_smul, Finsupp.smul_apply, smul_eq_mul,
          Algebra.smul_def] }
  have hΨi : Function.Injective Ψ := by
    intro ψ ψ' h
    apply Subtype.ext
    apply b.repr.injective
    ext i
    exact congrArg Subtype.val (congrFun h i)
  have hmem : ∀ e : ι → E, (∑ i, (e i : B) • b i) ∈ D := by
    intro e
    rw [hD]
    intro g v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb', map_sum, map_mul,
      ((hE _).mp (e _).2 g)]
  have hΨs : Function.Surjective Ψ := by
    intro e
    refine ⟨⟨_, hmem e⟩, ?_⟩
    funext i
    apply Subtype.ext
    change b.repr (∑ j, (e j : B) • b j) i = e i
    simp [Finsupp.single_apply]
  rw [(LinearEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, hEd]

/-- **A non-degenerate family of equivariant maps: the dimension count.**
`dim_K Hom_G(V, B) = d · dim_K V` when `dim_K B^G = d > 0`. -/
theorem finrank_of_nondeg [FiniteDimensional K V] (hρ : ∀ g, Function.Surjective (ρ g))
    (D : Submodule K (V →ₗ[K] B)) (hD : ∀ φ, φ ∈ D ↔ ∀ g v, φ (ρ g v) = aR g (φ v))
    (E : Submodule K B) (hE : ∀ x, x ∈ E ↔ ∀ g, aR g x = x) {d : ℕ} (hEd : finrank K E = d)
    (hd : 0 < d) (S : Set (V →ₗ[K] B)) (hSD : S ⊆ D)
    (hS : ∀ x : B ⊗[K] V, (∀ φ ∈ S, φ.liftBaseChange B x = 0) → x = 0) :
    finrank K D = d * finrank K V := by
  obtain ⟨b, hb⟩ := exists_basis_of_span S (span_eq_top_of_nondeg S hS)
  rw [finrank_of_basis aR ρ hρ D hD E hE hEd hd b (fun i => hSD (hb i)), Fintype.card_fin,
    mul_comm]

/-- **A non-degenerate family of equivariant maps: the values.** A property of elements of `B`
closed under `0`, `+` and `·`, held by `B^G` and by the values of the family, is held by the
values of every equivariant map. -/
theorem forall_prop_of_nondeg [FiniteDimensional K V] (hρ : ∀ g, Function.Surjective (ρ g))
    (E : Submodule K B) (hE : ∀ x, x ∈ E ↔ ∀ g, aR g x = x)
    (S : Set (V →ₗ[K] B)) (hSD : ∀ φ ∈ S, ∀ g v, φ (ρ g v) = aR g (φ v))
    (hS : ∀ x : B ⊗[K] V, (∀ φ ∈ S, φ.liftBaseChange B x = 0) → x = 0)
    (P : B → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hmul : ∀ x y, P x → P y → P (x * y)) (hPE : ∀ x ∈ E, P x) (hPS : ∀ φ ∈ S, ∀ v, P (φ v))
    (ψ : V →ₗ[K] B) (hψ : ∀ g v, ψ (ρ g v) = aR g (ψ v)) (v : V) : P (ψ v) := by
  obtain ⟨b, hb⟩ := exists_basis_of_span S (span_eq_top_of_nondeg S hS)
  have hb' : ∀ i g v, b i (ρ g v) = aR g (b i v) := fun i => hSD _ (hb i)
  have hsum : ψ v = ∑ i, b.repr ψ i * b i v := by
    conv_lhs => rw [← b.sum_repr ψ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsum]
  refine Finset.sum_induction _ P hadd h0 fun i _ => hmul _ _ ?_ (hPS _ (hb i) v)
  exact hPE _ ((hE _).mpr fun g => repr_fixed aR ρ hρ b hb' ψ hψ i g)

end Gen

/-! ## §2. G1: from Colmez's pairing, `D_dR(V^∨)` has full dimension and `Fil⁰ = D_dR` -/

section G1

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `ρ(σ)` is surjective for a representation. -/
theorem rep_surjective {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (σ : Field.absoluteGaloisGroup F) :
    Function.Surjective (ρ σ) := fun v => ⟨ρ σ⁻¹ v, by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩

/-- `B_dR^{G_F} ⊆ B_dR⁺`: every `G_F`-invariant of `B_dR` lies in `Fil⁰ B_dR` (`BdRInv.key`). -/
theorem bdrFix_le_filB_zero (x : BdR p) (hx : x ∈ DeRhamPrint.bdrFix p F) : x ∈ filB p 0 := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem _
  have hS' : ∀ τ ∈ (fieldF p F).fixingSubgroup, ∃ σ, gfToGqp p F σ = τ := fun τ hτ => by
    have h : τ ∈ ((fieldF p F).fixingSubgroup : Set (GQp p)) := hτ
    rw [← range_gfToGqp_eq p F] at h
    exact h
  obtain ⟨u, hu⟩ := BdRInv.key p (fieldF p F) x hx0 fun τ hτ => by
    obtain ⟨σ, rfl⟩ := hS' τ hτ
    exact hx σ
  exact ⟨u, by simp, hu.symm⟩

/-- `Fil⁰ B_dR = B_dR⁺` is closed under multiplication. -/
theorem filB_zero_mul {x y : BdR p} (hx : x ∈ filB p 0) (hy : y ∈ filB p 0) :
    x * y ∈ filB p 0 := by
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨b, -, rfl⟩ := hy
  exact ⟨a * b, by simp, map_mul _ a b⟩

/-- The non-degeneracy clause for the family `range P`. -/
theorem nondeg_range {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] {H : Type}
    (P : H → (V →ₗ[ℚ_[p]] BdR p))
    (hnd : ∀ x : BdR p ⊗[ℚ_[p]] V, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0) :
    ∀ x : BdR p ⊗[ℚ_[p]] V, (∀ φ ∈ Set.range P, φ.liftBaseChange (BdR p) x = 0) → x = 0 :=
  fun x hx => hnd x fun ω => hx (P ω) ⟨ω, rfl⟩

/-- The equivariance clause for the family `range P`. -/
theorem equivariant_range {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) {H : Type}
    (P : H → (V →ₗ[ℚ_[p]] BdR p))
    (hgal : ∀ ω (σ : Field.absoluteGaloisGroup F) u,
      P ω (ρ σ u) = bdrAct p (gfToGqp p F σ) (P ω u)) :
    ∀ φ ∈ Set.range P, ∀ σ v, φ (ρ σ v) = bdrAct p (gfToGqp p F σ) (φ v) := by
  rintro _ ⟨ω, rfl⟩ σ v
  exact hgal ω σ v

set_option maxHeartbeats 4000000 in
/-- **G1, Hom form, dimension.** For a finite-dimensional representation `V` of `G_F` with a
family of `G_F`-equivariant maps `V → B_dR`, non-degenerate after base change to `B_dR`
(Colmez's pairing), `dim_{ℚ_p} Hom_{G_F}(V, B_dR) = [F:ℚ_p] · dim V`. -/
theorem finrank_ddr_of_nondeg {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    {H : Type} (P : H → (V →ₗ[ℚ_[p]] BdR p))
    (hgal : ∀ ω (σ : Field.absoluteGaloisGroup F) u,
      P ω (ρ σ u) = bdrAct p (gfToGqp p F σ) (P ω u))
    (hnd : ∀ x : BdR p ⊗[ℚ_[p]] V, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0) :
    finrank ℚ_[p] (ddrSpaceOver p ρ) = finrank ℚ_[p] F * finrank ℚ_[p] V := by
  have hpos : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hB : finrank ℚ_[p] (DeRhamPrint.bdrFix p F) = finrank ℚ_[p] F :=
    BdRInv.bdRInvariantsPrinted_proof p F
  exact @Gen.finrank_of_nondeg ℚ_[p] (BdR p) (Field.absoluteGaloisGroup F) V _
    (DeRhamPrint.bdrField p) (inferInstance : Algebra ℚ_[p] (BdR p)) _ _
    (fun σ => bdrAct p (gfToGqp p F σ)) (fun σ => ρ σ) _ (rep_surjective ρ)
    (ddrSpaceOver p ρ) (fun _ => Iff.rfl) (DeRhamPrint.bdrFix p F) (fun _ => Iff.rfl)
    (finrank ℚ_[p] F) hB hpos (Set.range P) (equivariant_range ρ P hgal) (nondeg_range P hnd)

set_option maxHeartbeats 4000000 in
/-- **G1, Hom form, values.** Under the same hypotheses, with the family valued in `B_dR⁺`,
every `G_F`-equivariant map `V → B_dR` has values in `B_dR⁺`. -/
theorem ddr_le_filH_zero_of_nondeg {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    {H : Type} (P : H → (V →ₗ[ℚ_[p]] BdR p)) (h0 : ∀ ω u, P ω u ∈ filB p 0)
    (hgal : ∀ ω (σ : Field.absoluteGaloisGroup F) u,
      P ω (ρ σ u) = bdrAct p (gfToGqp p F σ) (P ω u))
    (hnd : ∀ x : BdR p ⊗[ℚ_[p]] V, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0) :
    ddrSpaceOver p ρ ≤ filH p 0 := by
  have hPS : ∀ φ ∈ Set.range P, ∀ u, φ u ∈ filB p 0 := by
    rintro _ ⟨ω, rfl⟩ u
    exact h0 ω u
  intro ψ hψ v
  exact @Gen.forall_prop_of_nondeg ℚ_[p] (BdR p) (Field.absoluteGaloisGroup F) V _
    (DeRhamPrint.bdrField p) (inferInstance : Algebra ℚ_[p] (BdR p)) _ _
    (fun σ => bdrAct p (gfToGqp p F σ)) (fun σ => ρ σ) _ (rep_surjective ρ)
    (DeRhamPrint.bdrFix p F) (fun _ => Iff.rfl) (Set.range P) (equivariant_range ρ P hgal)
    (nondeg_range P hnd) (fun x => x ∈ filB p 0) (zero_mem _)
    (fun _ _ hx hy => add_mem hx hy) (fun _ _ hx hy => filB_zero_mul hx hy)
    bdrFix_le_filB_zero hPS ψ hψ v

end G1

/-- **G1.** From R1, `V_p(A)^∨` is de Rham and `Fil⁰ D_dR = D_dR` (Hom form:
`Hom_{G_F}(V_p(A), B_dR) ⊆ Hom(V_p(A), B_dR⁺)`). -/
theorem dual_deRham_fil0_of_colmez (hC : Colmez1992DeRhamAbVar) (p : ℕ) [Fact p.Prime] (F : Type)
    [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ ddrSpaceOver p (A.galRep p) ≤ filH p 0 := by
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  haveI := (DeRhamPrint.finrank_V_of_tateModuleFree p (DeRhamPrint.tateModuleFree_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof)
    (DeRhamPrint.natCast_p_ne_zero p F) A g hg).1
  obtain ⟨H, P, h0, hgal, hnd⟩ := hC p F A
  have hD := finrank_ddr_of_nondeg (A.galRep p) P hgal hnd
  have hfil := ddr_le_filH_zero_of_nondeg (A.galRep p) P h0 hgal hnd
  refine ⟨⟨inferInstance, ?_⟩, hfil⟩
  rw [← LinearEquiv.finrank_map_eq (tensorDualEquiv p (V := A.V p)), map_ddrFam_dual, hD,
    Subspace.dual_finrank_eq]

/-! ## §3. G2: Hodge-Tate weights only in `{0, 1}` -/

section G2

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

set_option maxHeartbeats 1600000 in
/-- **G2.** If `dim_{F'} Hom_{G_F}(V, ℂ_p) + dim_{F'} Hom_{G_F}(V, ℂ_p(1)) = dim_{ℚ_p} V`, then
`Hom_{G_F}(V, ℂ_p(j)) = 0` for `j ∉ {0, 1}`: the two spaces give a `ℂ_p`-basis of
`Hom(V, ℂ_p)` (Tate-Sen, `linIndep_two`), and the coordinates of an element of weight `j` are
fixed by a nontrivial twist, hence `0` (Tate's `ℂ_p(i)^{G_F} = 0`, `i ≠ 0`). -/
theorem htSpaceOver_eq_bot_of_card
    (hab : finrank (fieldF p F) (htF ρ 0) + finrank (fieldF p F) (htF ρ 1) = finrank ℚ_[p] V)
    {j : ℤ} (hj0 : j ≠ 0) (hj1 : j ≠ 1) : htSpaceOver p ρ j = ⊥ := by
  have hT := ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
  have hA := ZInQ.Contrib.CloudB3W11.axSenTate_proof
  obtain ⟨hfa, -⟩ := fd_htF0 ρ hT hA
  obtain ⟨hfb, -⟩ := fd_htF1 ρ hT hA
  haveI := hfa
  haveI := hfb
  haveI := fd_hom (p := p) (V := V)
  set a := finrank (fieldF p F) (htF ρ 0)
  set b := finrank (fieldF p F) (htF ρ 1)
  let bx := Module.finBasis (fieldF p F) (htF ρ 0)
  let by' := Module.finBasis (fieldF p F) (htF ρ 1)
  have hz := linIndep_two ρ hT hA (fun i => bx i) (fun i => by' i) bx.linearIndependent
    by'.linearIndependent
  have hcard : Fintype.card (Fin a ⊕ Fin b) = finrank ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_hom]
    exact hab
  let B := basisOfLinearIndependentOfCardEqFinrank' _ hz hcard
  have hB : ∀ k, (B k) ∈ htSpaceOver p ρ (wt k) := by
    rintro (i | i)
    · simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl]; exact (bx i).2
    · simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr]; exact (by' i).2
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  have hc : ∀ k, B.repr f k = 0 := by
    intro k
    have hjk : j - wt k ≠ 0 := by
      apply sub_ne_zero.mpr
      rcases k with k | k
      · exact hj0
      · exact hj1
    refine twist_fixed_eq_zero (F := F) hT (i := j - wt k) hjk fun σ => ?_
    have hexp : tAct ρ σ f = ∑ k, (cpAct p (gfToGqp p F σ) (B.repr f k) *
        algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k))) • B k := by
      conv_lhs => rw [← B.sum_repr f]
      rw [tAct_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [tAct_of_mem ρ (hB k), smul_smul, mul_comm]
    have hrep : B.repr (tAct ρ σ f) = fun k => cpAct p (gfToGqp p F σ) (B.repr f k) *
        algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k)) := by
      rw [hexp]
      ext k
      rw [B.repr_sum_self]
    have hk : algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-j)) * B.repr f k =
        cpAct p (gfToGqp p F σ) (B.repr f k) *
          algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k)) := by
      have h := congrFun hrep k
      rw [tAct_of_mem ρ hf σ, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
      exact h
    have e1 : cycPow p (gfToGqp p F σ) (j - wt k) =
        cycPow p (gfToGqp p F σ) j * cycPow p (gfToGqp p F σ) (-wt k) := by
      rw [← HT.cycPow_add, sub_eq_add_neg]
    have e2 : cycPow p (gfToGqp p F σ) j * cycPow p (gfToGqp p F σ) (-j) = 1 := by
      rw [← HT.cycPow_add, add_neg_cancel, cycPow_zero]
    rw [Algebra.smul_def, e1, map_mul (algebraMap ℚ_[p] ℂ_[p])]
    calc algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) j) *
          algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k)) *
          cpAct p (gfToGqp p F σ) (B.repr f k)
        = algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) j) *
          (cpAct p (gfToGqp p F σ) (B.repr f k) *
            algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k))) := by ring
      _ = algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) j) *
          (algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-j)) * B.repr f k) := by rw [← hk]
      _ = B.repr f k := by
        rw [← mul_assoc, ← map_mul (algebraMap ℚ_[p] ℂ_[p]), e2, map_one, one_mul]
  rw [← B.sum_repr f]
  simp [hc]

end G2

/-! ## §4. G3: `D_dR ∩ Fil² = 0` from the vanishing of the weights `j ≥ 2` -/

section G3

variable {p : ℕ} [Fact p.Prime]

/-- `χ(σ)^j` for `j ∈ ℕ` is the `j`-th power of `χ(σ)`. -/
theorem cycPow_natCast (σ : GQp p) (j : ℕ) : cycPow p σ (j : ℤ) = cycPow p σ 1 ^ j := by
  induction j with
  | zero => rw [Nat.cast_zero, pow_zero, cycPow_zero]
  | succ j ih => rw [Nat.cast_succ, HT.cycPow_add, ih, pow_succ]

/-- `⋂_n Fil^n B_dR = 0` (Krull's intersection theorem in the discrete valuation ring `B_dR⁺`). -/
theorem eq_zero_of_forall_mem_filB (x : BdR p) (h : ∀ n, x ∈ filB p (n + 2)) :
    x = 0 := by
  haveI : IsDiscreteValuationRing (BDeRhamPlus 𝓞_ℂ_[p] p) :=
    ZInQ.Contrib.G9.BdrKer.Cp.isDiscreteValuationRing_BDeRhamPlus p
  obtain ⟨b, -, hb⟩ := h 0
  have hall : ∀ n, b ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) ^ (n + 2) := by
    intro n
    obtain ⟨b', hb', hb'x⟩ := h n
    rwa [iota_injective p (hb'x.trans hb.symm)] at hb'
  have hb0 : b ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) ^ n :=
    (Submodule.mem_iInf _).mpr fun n => Ideal.pow_le_pow_right (by omega) (hall n)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    Ideal.mem_bot] at hb0
  rw [← hb, hb0, map_zero]

variable {t : BDeRhamPlus 𝓞_ℂ_[p] p}
  (ht : IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t})
include ht

/-- The preimage `c` of `x = ι(t^j c) ∈ Fil^j B_dR`. -/
def preJ (j : ℕ) (x : filB p j) : BDeRhamPlus 𝓞_ℂ_[p] p :=
  ((mem_filB_iff ht j x).mp x.2).choose

theorem iota_preJ (j : ℕ) (x : filB p j) : iota p (t ^ j * preJ ht j x) = x :=
  ((mem_filB_iff ht j x).mp x.2).choose_spec

theorem preJ_eq (j : ℕ) {x : filB p j} {c : BDeRhamPlus 𝓞_ℂ_[p] p}
    (h : iota p (t ^ j * c) = x) : preJ ht j x = c :=
  mul_left_cancel₀ (pow_ne_zero j (t_ne_zero ht))
    (iota_injective p ((iota_preJ ht j x).trans h.symm))

/-- `gr^j B_dR → ℂ_p(j)`: `ι(t^j c) ↦ θ(c)`, a `ℚ_p`-linear map on `Fil^j B_dR`. -/
def thetaJ (j : ℕ) : filB p j →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := theta p (preJ ht j x)
  map_add' x y := by
    rw [preJ_eq ht j (show iota p (t ^ j * (preJ ht j x + preJ ht j y)) =
        ((x + y : filB p j) : BdR p) by
      rw [mul_add, map_add, iota_preJ, iota_preJ, Submodule.coe_add]), map_add]
  map_smul' c x := by
    rw [preJ_eq ht j (show iota p (t ^ j * (qpToPlus p c * preJ ht j x)) =
        ((c • x : filB p j) : BdR p) by
      rw [mul_left_comm, iota_qpToPlus_mul, iota_preJ, Submodule.coe_smul]), map_mul,
      theta_qpToPlus, RingHom.id_apply, Algebra.smul_def]

theorem thetaJ_spec (j : ℕ) {x : filB p j} {c : BDeRhamPlus 𝓞_ℂ_[p] p}
    (h : iota p (t ^ j * c) = x) : thetaJ ht j x = theta p c := by
  change theta p (preJ ht j x) = _
  rw [preJ_eq ht j h]

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `gr^j : Hom(V, Fil^j B_dR) → Hom(V, ℂ_p)`, `φ ↦ θ ∘ (φ/t^j)`. -/
def grJ (j : ℕ) :
    (filH p j : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) →ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  LinearMap.llcomp ℚ_[p] V (filB p j) ℂ_[p] (thetaJ ht j) ∘ₗ codR j

theorem grJ_apply (j : ℕ) (φ : (filH p j : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (v : V)
    {c : BDeRhamPlus 𝓞_ℂ_[p] p} (hc : iota p (t ^ j * c) = φ.1 v) :
    grJ ht j φ v = theta p c :=
  thetaJ_spec ht j (x := ⟨φ.1 v, φ.2 v⟩) hc

/-- `gr^j` lands in `Hom_{G_F}(V, ℂ_p(j))`, given `σ(t) = χ(σ) t`. -/
theorem grJ_mem (j : ℕ)
    (hσ : ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t)
    (φ : (filH p j : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (hφ : φ.1 ∈ ddrSpaceOver p ρ) :
    grJ ht j φ ∈ htSpaceOver p ρ (j : ℤ) := by
  intro σ v
  obtain ⟨c, hc⟩ := (mem_filB_iff ht j _).mp (φ.2 v)
  have h2 : iota p (t ^ j * (qpToPlus p (cycPow p (gfToGqp p F σ) (j : ℤ)) *
      DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) c)) = φ.1 (ρ σ v) := by
    rw [hφ σ v, ← hc, BdRInv.bdrAct_algebraMap,
      RingHom.map_mul (DR.bdrPlusMap p (oAct p (gfToGqp p F σ))) (t ^ j) c,
      RingHom.map_pow (DR.bdrPlusMap p (oAct p (gfToGqp p F σ))) t j, hσ, mul_pow,
      cycPow_natCast, RingHom.map_pow (qpToPlus p)]
    congr 1
    ring
  rw [grJ_apply ht j φ (ρ σ v) h2, grJ_apply ht j φ v hc, map_mul, theta_qpToPlus,
    thetaPlusCp_bdrPlusMap, Algebra.smul_def]

/-- `ker gr^j ⊆ Fil^{j+1}`. -/
theorem mem_filH_succ_of_grJ (j : ℕ) (φ : (filH p j : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)))
    (h : grJ ht j φ = 0) : φ.1 ∈ (filH p (j + 1) : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) := by
  intro v
  obtain ⟨c, hc⟩ := (mem_filB_iff ht j _).mp (φ.2 v)
  have h0 : theta p c = 0 := by rw [← grJ_apply ht j φ v hc, h]; rfl
  have hm : c ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := by
    rw [← ker_theta]; exact h0
  rw [ht, Ideal.mem_span_singleton'] at hm
  obtain ⟨d, rfl⟩ := hm
  exact (mem_filB_iff ht (j + 1) _).mpr ⟨d, by rw [← hc]; congr 1; ring⟩

/-- **G3.** If `Hom_{G_F}(V, ℂ_p(j)) = 0` for every `j ≥ 2`, then `D_dR ∩ Fil² = 0`
(Hom form, for `σ(t) = χ(σ) t`). -/
theorem ddr_inf_filH_two_eq_bot
    (hσ : ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t)
    (hvan : ∀ j : ℕ, 2 ≤ j → htSpaceOver p ρ (j : ℤ) = ⊥) :
    ddrSpaceOver p ρ ⊓ filH p 2 = ⊥ := by
  have key : ∀ n, ∀ φ ∈ ddrSpaceOver p ρ ⊓ filH p 2,
      φ ∈ (filH p (n + 2) : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) := by
    intro n
    induction n with
    | zero => intro φ hφ; exact (Submodule.mem_inf.mp hφ).2
    | succ n ih =>
      intro φ hφ
      have h1 := ih φ hφ
      have hg : grJ ht (n + 2) ⟨φ, h1⟩ = 0 := by
        have := grJ_mem ht ρ (n + 2) hσ ⟨φ, h1⟩ (Submodule.mem_inf.mp hφ).1
        rw [hvan (n + 2) (by omega), Submodule.mem_bot] at this
        exact this
      have := mem_filH_succ_of_grJ ht (n + 2) ⟨φ, h1⟩ hg
      rwa [show n + 1 + 2 = n + 2 + 1 by omega]
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  exact eq_zero_of_forall_mem_filB _ fun n => key n φ hφ v

end G3

/-! ## §5. G4: assembly -/

/-- **G4, for one abelian variety.** From R1 and R2: `V_p(A)^∨` is de Rham, its Hodge jumps lie
in `[0, 1]`, and `dim_{ℚ_p} Fil¹ D_dR = [F:ℚ_p] · g`. -/
theorem vpDual_clauses_of_colmezFontaine (hC : Colmez1992DeRhamAbVar)
    (hF : Fontaine1982HTAbVar) (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) :
    HTMerge.VpDualIsDeRham p A ∧ HTMerge.VpDualHodgeRange p A ∧
      HTMerge.VpDualFilOneDim p A g := by
  obtain ⟨hfdV, hdimV⟩ := DeRhamPrint.finrank_V_of_tateModuleFree p
    (DeRhamPrint.tateModuleFree_of_mumford
      ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof)
    (DeRhamPrint.natCast_p_ne_zero p F) A g hg
  haveI := hfdV
  obtain ⟨t, ht, hσ⟩ := DeRhamScholze.TT.fontaineTwistT p
  obtain ⟨hdR, h0⟩ := dual_deRham_fil0_of_colmez hC p F A
  obtain ⟨hF1, hF0⟩ := hF p F A g hg
  have hT := ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
  have hA := ZInQ.Contrib.CloudB3W11.axSenTate_proof
  -- `dim_{ℚ_p} D = [F:ℚ_p] · 2g`
  have hD : finrank ℚ_[p] (ddrSpaceOver p (A.galRep p)) = finrank ℚ_[p] F * (2 * g) := by
    rw [← map_ddrFam_dual (A.galRep p), LinearEquiv.finrank_map_eq, hdR.2,
      Subspace.dual_finrank_eq, hdimV]
  -- weights only in `{0, 1}`, so `D ∩ Fil² = 0`
  have hab : finrank (fieldF p F) (htF (A.galRep p) 0) +
      finrank (fieldF p F) (htF (A.galRep p) 1) = finrank ℚ_[p] (A.V p) := by
    rw [hF0, hF1, hdimV]; ring
  have h2 : ddrSpaceOver p (A.galRep p) ⊓ filH p 2 = ⊥ :=
    ddr_inf_filH_two_eq_bot ht (A.galRep p) hσ fun j hj =>
      htSpaceOver_eq_bot_of_card (A.galRep p) hab (by omega) (by omega)
  -- the weight-1 count
  obtain ⟨hfa, -⟩ := fd_htF0 (A.galRep p) hT hA
  obtain ⟨hfb, -⟩ := fd_htF1 (A.galRep p) hT hA
  haveI := hfa
  haveI := hfb
  haveI := fd_htSpaceOver (A.galRep p) (0 : ℤ)
  haveI := fd_htSpaceOver (A.galRep p) (1 : ℤ)
  obtain ⟨hl1, hl2⟩ := DeRhamScholze.HTAbVar.finrank_fil1_bounds (A.galRep p) ht hσ h0 h2
  rw [finrank_htSpaceOver_eq, hF1] at hl1
  rw [hD, finrank_htSpaceOver_eq, hF0] at hl2
  have hX : finrank ℚ_[p] (ddrSpaceOver p (A.galRep p) ⊓ filH p 1 :
      Submodule ℚ_[p] (A.V p →ₗ[ℚ_[p]] BdR p)) = finrank ℚ_[p] F * g := by
    have e : finrank ℚ_[p] F * (2 * g) = finrank ℚ_[p] F * g + finrank ℚ_[p] F * g := by ring
    rw [e] at hl2
    generalize finrank ℚ_[p] F * g = m at hl1 hl2 ⊢
    omega
  -- back to the tensor form on `V^∨`
  have hfil : ∀ j, Submodule.map (tensorDualEquiv p).toLinearMap
      (filD p (fun σ => (A.galRep p).dual σ) j) = ddrSpaceOver p (A.galRep p) ⊓ filH p j := by
    intro j
    rw [filD, Submodule.map_inf _ (tensorDualEquiv p).injective, map_ddrFam_dual,
      map_filRange_dual]
  refine ⟨hdR, ⟨?_, ?_⟩, ?_⟩
  · apply Submodule.map_injective_of_injective
      (f := (tensorDualEquiv p (V := A.V p)).toLinearMap) (tensorDualEquiv p).injective
    rw [hfil 0, map_ddrFam_dual]
    exact inf_eq_left.mpr h0
  · show filD p (fun σ => (A.galRep p).dual σ) 2 = ⊥
    apply Submodule.map_injective_of_injective
      (f := (tensorDualEquiv p (V := A.V p)).toLinearMap) (tensorDualEquiv p).injective
    rw [hfil 2, h2, Submodule.map_bot]
  · change finrank ℚ_[p] (filD p (fun σ => (A.galRep p).dual σ) 1) = finrank ℚ_[p] F * g
    rw [← hX, ← hfil 1, LinearEquiv.finrank_map_eq]

/-- **The glue: the two single-print rows imply `VpDualDeRhamAbVar`.** -/
theorem vpDual_of_colmezFontaine (hC : Colmez1992DeRhamAbVar) (hF : Fontaine1982HTAbVar) :
    HTMerge.VpDualDeRhamAbVar :=
  fun p _ F _ _ _ A g hg => vpDual_clauses_of_colmezFontaine hC hF p F A g hg

end

end DeRhamScholze.TatePrints

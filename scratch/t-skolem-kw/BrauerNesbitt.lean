import Mathlib

/-!
# t-skolem-kw: leaf T19 (Brauer–Nesbitt in characteristic 0)

The statement `BrauerNesbittChar0` is copied verbatim from `scratch/h-decomposition/Leaves.lean`
(`PkgI6.BrauerNesbittChar0`, also `GlueC10.BrauerNesbittChar0`).

Proof (standard; cf. Curtis–Reiner (27.13), Lang, *Algebra* XVII Cor. 3.8, both UNVERIFIED
locators), for modules over an arbitrary `k`-algebra `R`:
1. `isNilpotent_of_trace_pow_eq_zero`: in characteristic 0 an endomorphism all of whose powers
   have trace 0 is nilpotent (Cayley–Hamilton gives `det = 0`; induct on the range).
2. `exists_injective_of_trace_eq`: if `M`, `N` have equal traces, `N` is semisimple and `S ⊆ M`
   is simple, then `S` embeds in `N`: the annihilator `J` of `N` acts nilpotently on `M` (1),
   hence kills `S` (if `t • s = s` for some `t ∈ J` then `s = 0`); so `S` is a quotient of
   `R / ann N ⊆ N^d`, hence (semisimplicity) a submodule of `N^d`, hence of `N`.
3. Induction on `dim M`: split off `S` from both sides.
-/

open Module

namespace TSkolemKW

/-! ## The statement (verbatim from `scratch/h-decomposition/Leaves.lean`) -/

/-- **Leaf I6.5 (Brauer–Nesbitt, characteristic 0, trace form).** Verbatim
`PkgI6.BrauerNesbittChar0`. -/
def BrauerNesbittChar0 : Prop :=
  ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
    (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)

/-! ## Step 1. Traces of powers vanish ⇒ nilpotent (characteristic 0) -/

theorem isNilpotent_of_trace_pow_eq_zero {k : Type*} [Field k] [CharZero k] :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    finrank k V = n → ∀ f : V →ₗ[k] V,
    (∀ j, 0 < j → LinearMap.trace k V (f ^ j) = 0) → IsNilpotent f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn f hf
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨1, Subsingleton.elim _ _⟩
  -- `f` is not injective: the constant term of the characteristic polynomial vanishes
  have hc0 : f.charpoly.coeff 0 = 0 := by
    have h0 := congrArg (LinearMap.trace k V) (LinearMap.aeval_self_charpoly f)
    rw [Polynomial.aeval_eq_sum_range, map_sum, map_zero, Finset.sum_range_succ'] at h0
    rw [Finset.sum_eq_zero (fun i _ => by rw [map_smul, hf (i + 1) (Nat.succ_pos i), smul_zero]),
      zero_add, pow_zero, map_smul, LinearMap.trace_one, smul_eq_mul] at h0
    have hpos : (finrank k V : k) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    exact (mul_eq_zero.1 h0).resolve_right hpos
  have hroot : f.charpoly.IsRoot 0 := by
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, hc0]
  obtain ⟨v, hv, hv0⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f 0).2 hroot).exists_hasEigenvector
  have hfv : f v = 0 := by
    have := Module.End.mem_eigenspace_iff.1 hv
    simpa using this
  -- restrict to the range
  let W := LinearMap.range f
  let g : W →ₗ[k] W := f.restrict (fun x _ => LinearMap.mem_range_self f x)
  have hgpow : ∀ j (w : W), (((g ^ j) w : W) : V) = (f ^ j) (w : V) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ihj =>
      intro w
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihj]
      rfl
  have hW : finrank k W < n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : 0 < finrank k (LinearMap.ker f) := by
      have : Nontrivial (LinearMap.ker f) := ⟨⟨⟨v, hfv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
      exact Module.finrank_pos
    change finrank k (LinearMap.range f) < n
    omega
  have hgtr : ∀ j, 0 < j → LinearMap.trace k W (g ^ j) = 0 := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e1 : g ^ (i + 1) = (f.rangeRestrict ∘ₗ (f ^ i)) ∘ₗ W.subtype := by
      ext w
      rw [hgpow, pow_succ', Module.End.mul_apply]
      rfl
    have e2 : f ^ (i + 1) = W.subtype ∘ₗ (f.rangeRestrict ∘ₗ (f ^ i)) := by
      ext x
      rw [pow_succ']
      rfl
    rw [e1, ← LinearMap.trace_comp_comm', ← e2]
    exact hf _ hj
  obtain ⟨m, hm⟩ := ih _ hW rfl g hgtr
  refine ⟨m + 1, ?_⟩
  ext x
  rw [pow_succ, Module.End.mul_apply, ← show (((g ^ m) ⟨f x, LinearMap.mem_range_self f x⟩ : W) : V)
    = (f ^ m) (f x) from hgpow m _, hm]
  rfl

/-! ## The action of `R` on a module, as `k`-linear maps -/

section Act

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

/-- `r : R` acting on `M`, as a `k`-linear endomorphism. -/
abbrev act (M : Type*) [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    (r : R) : M →ₗ[k] M :=
  DistribSMul.toLinearMap k M r

variable {M P A B : Type*} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [AddCommGroup P] [Module k P] [Module R P] [IsScalarTower k R P]
  [AddCommGroup A] [Module k A] [Module R A] [IsScalarTower k R A]
  [AddCommGroup B] [Module k B] [Module R B] [IsScalarTower k R B]

theorem act_pow (r : R) (j : ℕ) : act (k := k) M (r ^ j) = (act M r) ^ j := by
  induction j with
  | zero => ext x; rw [pow_zero, pow_zero, Module.End.one_apply]; exact one_smul R x
  | succ j ih =>
    ext x
    rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih]
    exact mul_smul (r ^ j) r x

theorem trace_act_equiv [FiniteDimensional k M] [FiniteDimensional k P] (e : M ≃ₗ[R] P) (r : R) :
    LinearMap.trace k M (act M r) = LinearMap.trace k P (act P r) := by
  rw [← LinearMap.trace_conj' (act M r) (e.restrictScalars k)]
  congr 1
  ext x
  change e (r • e.symm x) = r • x
  rw [map_smul, e.apply_symm_apply]

theorem trace_act_prod [FiniteDimensional k A] [FiniteDimensional k B] (r : R) :
    LinearMap.trace k (A × B) (act (A × B) r) =
      LinearMap.trace k A (act A r) + LinearMap.trace k B (act B r) := by
  rw [← LinearMap.trace_prodMap']
  rfl

end Act

/-! ## Step 2. A simple constituent of `M` embeds in `N` -/

section Main

variable {k R : Type*} [Field k] [CharZero k] [Ring R] [Algebra k R]

omit [CharZero k] in
theorem fd_sub {M : Type*} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    [FiniteDimensional k M] (S : Submodule R M) : FiniteDimensional k S :=
  Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective

theorem exists_injective_of_trace_eq {M N : Type*}
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [FiniteDimensional k N]
    [IsSemisimpleModule R N]
    (htr : ∀ r : R, LinearMap.trace k M (act M r) = LinearMap.trace k N (act N r))
    (S : Submodule R M) [IsSimpleModule R S] : ∃ j : S →ₗ[R] N, Function.Injective j := by
  classical
  -- the annihilator of `N` acts nilpotently on `M`
  have hnil : ∀ r : R, (∀ n : N, r • n = 0) → IsNilpotent (act (k := k) M r) := by
    intro r hr
    refine isNilpotent_of_trace_pow_eq_zero _ rfl _ fun j hj => ?_
    rw [← act_pow, htr, act_pow]
    have : act (k := k) N r = 0 := LinearMap.ext hr
    rw [this, zero_pow hj.ne', map_zero]
  -- the left ideal `ann N`
  let Jl : Submodule R R :=
    { carrier := {t | ∀ n : N, t • n = 0}
      add_mem' := fun {a b} ha hb n => by rw [add_smul, ha n, hb n, add_zero]
      zero_mem' := fun n => zero_smul R n
      smul_mem' := fun c t ht n => by
        change (c * t) • n = 0
        rw [mul_smul, ht n, smul_zero] }
  -- it kills `S`
  have hkill : ∀ r : R, (∀ n : N, r • n = 0) → ∀ s ∈ S, r • s = 0 := by
    intro r hr s hs
    by_contra hne
    let Jm : Submodule R M := Jl.map (LinearMap.toSpanSingleton R M s)
    have hle : Jm ≤ S := by
      rintro _ ⟨t, -, rfl⟩
      exact S.smul_mem t hs
    have hne' : Jm ≠ ⊥ := by
      intro h
      apply hne
      have : r • s ∈ Jm := ⟨r, hr, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot R).1 this
    have hatom : IsAtom S := isSimpleModule_iff_isAtom.1 ‹_›
    have hJS : Jm = S := ((hatom.le_iff).1 hle).resolve_left hne'
    have hsJ : s ∈ Jm := hJS ▸ hs
    obtain ⟨t, ht, hts⟩ := hsJ
    change t • s = s at hts
    obtain ⟨m, hm⟩ := hnil t ht
    have hpow : ∀ i, ((act (k := k) M t) ^ i) s = s := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Module.End.mul_apply, ih]; exact hts
    have := hpow m
    rw [hm, LinearMap.zero_apply] at this
    exact hne (by rw [← this, smul_zero])
  -- `S` is a quotient of `R / ann N ⊆ N^d`
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  let b := Module.finBasis k N
  let L : R →ₗ[R] (Fin (finrank k N) → N) :=
    LinearMap.pi fun i => LinearMap.toSpanSingleton R N (b i)
  have hker : ∀ t, L t = 0 → ∀ n : N, t • n = 0 := by
    intro t ht n
    have hti : ∀ i, t • b i = 0 := fun i => congrFun ht i
    rw [← b.sum_repr n, Finset.smul_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_comm, hti i, smul_zero]
  let ψ0 : R →ₗ[R] S := LinearMap.toSpanSingleton R S s
  have hle : LinearMap.ker L ≤ LinearMap.ker ψ0 := by
    intro t ht
    rw [LinearMap.mem_ker] at ht ⊢
    exact Subtype.ext (hkill t (hker t ht) s s.2)
  let φ := (LinearMap.ker L).liftQ ψ0 hle
  let e := L.quotKerEquivRange
  let ψ : LinearMap.range L →ₗ[R] S := φ ∘ₗ e.symm.toLinearMap
  have hψ : ψ ≠ 0 := by
    intro h
    apply hs
    have h1 : ψ (e (Submodule.Quotient.mk 1)) = s := by
      simp [ψ, φ, ψ0]
    rw [← h1, h, LinearMap.zero_apply]
  obtain ⟨T, ⟨eT⟩⟩ := LinearMap.linearEquiv_of_ne_zero hψ
  let g : S →ₗ[R] (Fin (finrank k N) → N) :=
    (LinearMap.range L).subtype ∘ₗ T.subtype ∘ₗ eT.toLinearMap
  have hg : Function.Injective g :=
    Subtype.val_injective.comp (Subtype.val_injective.comp eT.injective)
  have hg0 : g ≠ 0 := by
    intro h
    apply hs
    apply hg
    rw [h, map_zero, LinearMap.zero_apply]
  obtain ⟨i, hi⟩ : ∃ i, LinearMap.proj i ∘ₗ g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hg0
    ext x i
    exact congrArg (fun F => F x) (hcon i)
  exact ⟨_, LinearMap.injective_of_ne_zero hi⟩

/-! ## Step 3. Brauer–Nesbitt for modules over a `k`-algebra -/

theorem brauerNesbitt_module : ∀ (n : ℕ) (M N : Type*)
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [FiniteDimensional k N],
    finrank k M = n → IsSemisimpleModule R M → IsSemisimpleModule R N →
    (∀ r : R, LinearMap.trace k M (act M r) = LinearMap.trace k N (act N r)) →
    Nonempty (M ≃ₗ[R] N) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M N _ _ _ _ _ _ _ _ _ _ hn hM hN htr
  rcases subsingleton_or_nontrivial M with hMs | hMn
  · have h1 := htr 1
    have e1 : act (k := k) M (1 : R) = LinearMap.id := LinearMap.ext fun x => one_smul R x
    have e2 : act (k := k) N (1 : R) = LinearMap.id := LinearMap.ext fun x => one_smul R x
    rw [e1, e2, ← Module.End.one_eq_id, ← Module.End.one_eq_id, LinearMap.trace_one,
      LinearMap.trace_one, Module.finrank_zero_of_subsingleton, Nat.cast_zero, eq_comm,
      Nat.cast_eq_zero, Module.finrank_zero_iff] at h1
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule R M
  obtain ⟨j, hj⟩ := exists_injective_of_trace_eq htr S
  obtain ⟨M', hM'⟩ := exists_isCompl S
  obtain ⟨N', hN'⟩ := exists_isCompl (LinearMap.range j)
  have := fd_sub (k := k) S
  have := fd_sub (k := k) M'
  have := fd_sub (k := k) (LinearMap.range j)
  have := fd_sub (k := k) N'
  let eM := Submodule.prodEquivOfIsCompl S M' hM'
  let eN := Submodule.prodEquivOfIsCompl _ N' hN'
  let eS : S ≃ₗ[R] LinearMap.range j := LinearEquiv.ofInjective j hj
  have htr' : ∀ r : R, LinearMap.trace k M' (act M' r) = LinearMap.trace k N' (act N' r) := by
    intro r
    have h1 := htr r
    rw [← trace_act_equiv eM, ← trace_act_equiv eN, trace_act_prod, trace_act_prod,
      trace_act_equiv eS] at h1
    exact add_left_cancel h1
  have hdim : finrank k M' < n := by
    have h1 := (eM.restrictScalars k).finrank_eq
    rw [Module.finrank_prod] at h1
    have : Nontrivial S := IsSimpleModule.nontrivial R S
    have h2 : 0 < finrank k S := Module.finrank_pos
    omega
  obtain ⟨e'⟩ := ih _ hdim M' N' rfl inferInstance inferInstance htr'
  exact ⟨eM.symm.trans ((eS.prodCongr e').trans eN)⟩

end Main

/-! ## The leaf -/

theorem brauerNesbittChar0 : BrauerNesbittChar0 := by
  intro k G V W _ _ _ _ _ _ _ _ _ ρ σ hρ hσ htr
  refine brauerNesbitt_module (k := k) (R := MonoidAlgebra k G) _ ρ.asModule σ.asModule rfl hρ hσ ?_
  intro r
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    have e1 : ∀ (U : Type) [AddCommGroup U] [Module k U] [FiniteDimensional k U]
        (τ : Representation k G U),
        LinearMap.trace k τ.asModule (act τ.asModule (MonoidAlgebra.of k G g)) =
          LinearMap.trace k U (τ g) := by
      intro U _ _ _ τ
      rw [← LinearMap.trace_conj' _ τ.asModuleEquiv]
      congr 1
      ext x
      simp [LinearEquiv.conj_apply]
      rfl
    rw [e1, e1]
    exact htr g
  | add f g hf hg =>
    rw [show act (k := k) ρ.asModule (f + g) = act ρ.asModule f + act ρ.asModule g from
      LinearMap.ext fun x => add_smul f g x,
      show act (k := k) σ.asModule (f + g) = act σ.asModule f + act σ.asModule g from
      LinearMap.ext fun x => add_smul f g x, map_add, map_add, hf, hg]
  | smul c f hf =>
    rw [show act (k := k) ρ.asModule (c • f) = c • act ρ.asModule f from
      LinearMap.ext fun x => smul_assoc c f x,
      show act (k := k) σ.asModule (c • f) = c • act σ.asModule f from
      LinearMap.ext fun x => smul_assoc c f x, map_smul, map_smul, hf]

end TSkolemKW

#print axioms TSkolemKW.brauerNesbitt_module
#print axioms TSkolemKW.brauerNesbittChar0

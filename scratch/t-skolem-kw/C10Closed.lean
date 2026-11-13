import Mathlib

-- ===== BrauerNesbitt.lean =====

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


/-! ## The matrix form `HSyn.BrauerNesbitt` -/

/-- **L19. Brauer–Nesbitt.** Verbatim `HSyn.BrauerNesbitt`. -/
def HSynBrauerNesbitt : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

section Matrix

variable {G E : Type} [Group G] [Field E] {n : ℕ}

/-- The representation of `G` on `E^n` given by a homomorphism to `GL_n(E)`. -/
noncomputable def repOfGL (ρ : G →* GL (Fin n) E) : Representation E G (Fin n → E) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) E ≃ₐ[E] Module.End E (Fin n → E)).toAlgHom
    |>.toMonoidHom.comp ((Units.coeHom _).comp ρ)

theorem repOfGL_apply (ρ : G →* GL (Fin n) E) (g : G) :
    repOfGL ρ g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E) := rfl

theorem isSemisimpleModule_repOfGL (ρ : G →* GL (Fin n) E)
    (h : ∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ W') :
    IsSemisimpleModule (MonoidAlgebra E G) (repOfGL ρ).asModule := by
  rw [isSemisimpleModule_iff]
  refine (OrderIso.complementedLattice_iff (repOfGL ρ).mapSubmodule).1 ⟨fun ⟨p, hp⟩ => ?_⟩
  have hp' : ∀ g, p.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ p := fun g =>
    (Module.End.mem_invtSubmodule_iff_map_le _).1 ((repOfGL ρ).mem_invtSubmodule.1 hp g)
  obtain ⟨W', hc, hW'⟩ := h p hp'
  have hW'mem : W' ∈ (repOfGL ρ).invtSubmodule :=
    (repOfGL ρ).mem_invtSubmodule.2 fun g => (Module.End.mem_invtSubmodule_iff_map_le _).2 (hW' g)
  refine ⟨⟨W', hW'mem⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    apply Subtype.ext
    exact hc.inf_eq_bot
  · rw [codisjoint_iff]
    apply Subtype.ext
    exact hc.sup_eq_top

end Matrix

theorem hsynBrauerNesbitt : HSynBrauerNesbitt := by
  intro G _ E _ _ n ρ₁ ρ₂ h₁ h₂ htr
  obtain ⟨φ⟩ := brauerNesbittChar0 E G (Fin n → E) (Fin n → E) (repOfGL ρ₁) (repOfGL ρ₂)
    (isSemisimpleModule_repOfGL ρ₁ h₁) (isSemisimpleModule_repOfGL ρ₂ h₂)
    (fun g => by rw [repOfGL_apply, repOfGL_apply, Matrix.trace_toLin'_eq,
      Matrix.trace_toLin'_eq, htr g])
  let f : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
    ((repOfGL ρ₁).asModuleEquiv.symm.trans (φ.restrictScalars E)).trans
      (repOfGL ρ₂).asModuleEquiv
  have hf : ∀ g x, f (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E) x) =
      Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E) (f x) := by
    intro g x
    rw [← repOfGL_apply, ← repOfGL_apply]
    simp only [f, LinearEquiv.trans_apply, Representation.asModuleEquiv_symm_map_rho,
      LinearEquiv.restrictScalars_apply, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  let P : GL (Fin n) E :=
    ⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨P, fun g => Units.ext ?_⟩
  change (ρ₂ g : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' f.toLinearMap *
    (ρ₁ g : Matrix (Fin n) (Fin n) E) * LinearMap.toMatrix' f.symm.toLinearMap
  rw [← LinearMap.toMatrix'_toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E), ← LinearMap.toMatrix'_comp,
    ← LinearMap.toMatrix'_comp]
  conv_lhs => rw [← LinearMap.toMatrix'_toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hf, LinearEquiv.apply_symm_apply]

end TSkolemKW


-- ===== GlueC10 (verbatim from Leaves.lean 11325-11776) =====
open NumberField
namespace TSkolemKW.C10

/-! ## Leaves (copied from pkg-I6) -/

/-- **Leaf I6.4 (Chebotarev, existence form)** — verbatim from pkg-I6. -/
def ChebotarevExists : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

/-- **Leaf I6.5 (Brauer–Nesbitt, characteristic 0, trace form)** — verbatim from pkg-I6. -/
def BrauerNesbittChar0 : Prop :=
  ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
    (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)

/-! ## Part A. Finite level (the form recommended by glue-I6-rest)

A representation that factors through a finite Galois group `Gal(M/ℚ)`: traces that agree at
every unramified Frobenius outside `S` agree everywhere, hence the representations are
isomorphic. -/

/-- `σ ∈ Gal(M/ℚ)` is the Frobenius at some prime of `𝓞_M` over a rational prime `p ∉ S`
that is unramified in `M`. -/
def IsUnramFrob (M : Type) [Field M] [NumberField M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

/-- Chebotarev: every element of `Gal(M/ℚ)` is an unramified Frobenius outside `S`. -/
theorem isUnramFrob_all (hC : ChebotarevExists) (M : Type) [Field M] [NumberField M]
    [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M) : IsUnramFrob M S σ :=
  hC M S σ

/-- **C10 at finite level (GLUE, proved from I6.4 and I6.5).** Two semisimple
finite-dimensional representations of `Gal(M/ℚ)` over a field of characteristic `0` whose traces
agree at every unramified Frobenius outside a finite set `S` are isomorphic. -/
theorem iso_of_trace_eq_frob_finite (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ)
    (k V W : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k (M ≃ₐ[ℚ] M) V) (σ : Representation k (M ≃ₐ[ℚ] M) W)
    (hρ : IsSemisimpleModule (MonoidAlgebra k (M ≃ₐ[ℚ] M)) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k (M ≃ₐ[ℚ] M)) σ.asModule)
    (htr : ∀ g, IsUnramFrob M S g → LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (M ≃ₐ[ℚ] M)] σ.asModule) :=
  hBN k _ V W ρ σ hρ hσ fun g => htr g (isUnramFrob_all hC M S g)

/-! ## Part B. The absolute Galois group `G_ℚ` -/

/-- `\bar ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(\bar ℚ/ℚ)` with the Krull topology.  Definitionally Mathlib's
`GQ` (which is a non-reducible `def` of the same type). -/
abbrev GQ : Type := Qbar ≃ₐ[ℚ] Qbar

example : GQ = Field.absoluteGaloisGroup ℚ := rfl

/-- `\bar ℤ`, the integral closure of `ℤ` in `\bar ℚ`. -/
abbrev Zbar : Type := integralClosure ℤ Qbar

/-- `g ∈ G_ℚ` is an arithmetic Frobenius at the rational prime `p`: there is a prime `𝔓` of
`\bar ℤ` over `p` with `g x ≡ x^p (mod 𝔓)` for every `x ∈ \bar ℤ`. -/
def IsFrobAt (g : GQ) (p : ℕ) : Prop :=
  ∃ P : Ideal Zbar, P.IsPrime ∧ P.under ℤ = Ideal.span {(p : ℤ)} ∧
    ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P

/-- **Frobenius density (GLUE).** For every finite subextension `E/ℚ` of `\bar ℚ` and every
`g ∈ G_ℚ` there is a Frobenius `h` at a prime `p ∉ S` with `h = g` on `E`.  By
`krullTopology_mem_nhds_one_iff` this says that Frobenius elements at primes outside `S` are
dense in `G_ℚ`. -/
def FrobDense (S : Finset ℕ) : Prop :=
  ∀ (E : IntermediateField ℚ Qbar), FiniteDimensional ℚ E → ∀ g : GQ,
    ∃ h : GQ, ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ IsFrobAt h p ∧
      ∀ x ∈ E, h x = g x

/-- **The lift of a finite-level Frobenius to `G_ℚ` (GLUE, proved below: `frobLift`).**  For a finite
Galois `E ⊂ \bar ℚ` and `τ ∈ Gal(E/ℚ)` that is the Frobenius at a prime `Q` of `𝓞_E` over `p`
unramified in `E`, some `h ∈ G_ℚ` restricting to `τ` is a Frobenius at `p` in `G_ℚ`.
Proof sketch: choose `𝔓 | Q` in `\bar ℤ`; an arithmetic Frobenius `h ∈ D_𝔓` exists by
compactness of `G_ℚ` and `exists_isArithFrobAt` in every finite Galois layer; `h|_E` is a
Frobenius at `Q`, and Frobenius at an unramified prime is unique
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`). -/
def FrobLift : Prop :=
  ∀ (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E] [IsGalois ℚ E]
    (τ : E ≃ₐ[ℚ] E) (p : ℕ) (Q : Ideal (𝓞 E)) [Q.IsPrime], p.Prime →
    Q.under ℤ = Ideal.span {(p : ℤ)} → Algebra.IsUnramifiedAt ℤ Q → IsArithFrobAt ℤ τ Q →
      ∃ h : GQ, IsFrobAt h p ∧ AlgEquiv.restrictNormal h E = τ

/-! ### Proof of `FrobLift` (merged from `Lift.lean`) -/

/-- `𝓞_E → \bar ℤ`. -/
noncomputable def toZbar (E : IntermediateField ℚ Qbar) : 𝓞 E →+* Zbar :=
  RingHom.codRestrict ((algebraMap E Qbar).comp (algebraMap (𝓞 E) E)) (integralClosure ℤ Qbar)
    (fun x => (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E Qbar))

@[simp] lemma toZbar_coe (E : IntermediateField ℚ Qbar) (x : 𝓞 E) :
    ((toZbar E x : Zbar) : Qbar) = ((x : E) : Qbar) := rfl

lemma card_quot (p : ℕ) [Fact p.Prime] : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- **Step (c) of `FrobLift` (GLUE, proved).** -/
theorem restrictNormal_eq_of_frob (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E]
    [IsGalois ℚ E] (τ : E ≃ₐ[ℚ] E) (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) [Algebra.IsUnramifiedAt ℤ Q]
    (hτ : IsArithFrobAt ℤ τ Q) (h : GQ) (P : Ideal Zbar) (hPQ : P.comap (toZbar E) = Q)
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    AlgEquiv.restrictNormal h E = τ := by
  have : NumberField E := ⟨⟩
  set σ := AlgEquiv.restrictNormal h E
  have hσ : IsArithFrobAt ℤ σ Q := by
    intro x
    rw [hQp, card_quot, ← hPQ, Ideal.mem_comap]
    apply hh (toZbar E x)
    rw [map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
      toZbar_coe]
    congr 1
    exact AlgEquiv.restrictNormal_commutes h E (x : E)
  have hQ : Q.primeCompl ≤ nonZeroDivisors (𝓞 E) := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    exact hx Q.zero_mem
  have heq := hσ.eq_of_isUnramifiedAt hτ hQ
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have ha := congrArg (fun f => ((f a : 𝓞 E) : E)) heq
  have hb := congrArg (fun f => ((f b : 𝓞 E) : E)) heq
  simp only [MulSemiringAction.toAlgHom_apply] at ha hb
  have key : ∀ (g : E ≃ₐ[ℚ] E) (c : 𝓞 E), g (algebraMap (𝓞 E) E c) = ((g • c : 𝓞 E) : E) :=
    fun g c => rfl
  have e1 := (key σ a).trans (ha.trans (key τ a).symm)
  have e2 := (key σ b).trans (hb.trans (key τ b).symm)
  rw [map_div₀, map_div₀, e1, e2]

/-- **Step (b) of `FrobLift` (GLUE).** Every prime `𝔓` of `\bar ℤ` over a rational prime
`p` has an arithmetic Frobenius in `G_ℚ`.  (Compactness of `G_ℚ` and Mathlib's
`exists_isArithFrobAt` in each finite Galois layer.) -/
def FrobExistsAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∃ h : GQ, ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P


lemma toZbar_injective (E : IntermediateField ℚ Qbar) : Function.Injective (toZbar E) := by
  intro x y hxy
  have := congrArg (fun z : Zbar => (z : Qbar)) hxy
  simp only [toZbar_coe] at this
  exact RingOfIntegers.ext (Subtype.ext this)

/-- **`FrobLift` from step (b) (GLUE, proved): lying-over plus step (c).** -/
theorem frobLift_of_frobExistsAt (hb : FrobExistsAt) : FrobLift := by
  intro E _ _ τ p Q _ hp hQp hQu hτ
  have : Fact p.Prime := ⟨hp⟩
  let _ : Algebra (𝓞 E) Zbar := (toZbar E).toAlgebra
  have : Algebra.IsIntegral (𝓞 E) Zbar := Algebra.IsIntegral.tower_top ℤ
  obtain ⟨P, -, hP, hPQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal Zbar)
    (by
      intro x hx
      have : toZbar E x = 0 := hx
      rw [toZbar_injective E (this.trans (map_zero _).symm)]
      exact Q.zero_mem)
  have hPQ' : P.comap (toZbar E) = Q := hPQ
  have hPp : P.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hQp, Ideal.under, Ideal.under, ← hPQ', Ideal.comap_comap]
    congr 1
  obtain ⟨h, hh⟩ := hb p P hPp
  exact ⟨h, ⟨P, hP, hPp, hh⟩, restrictNormal_eq_of_frob E τ p Q hQp hτ h P hPQ' hh⟩

/-- The Frobenius condition at `𝔓` on the elements of `\bar ℤ` lying in `F`. -/
def FrobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar) : Set GQ :=
  {h | ∀ x y : Zbar, (x : Qbar) ∈ F → (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P}

/-- **Step (b), finite layer (GLUE, proved: `frobExistsFinite`; a consequence of Mathlib's
`IsArithFrobAt.exists_of_isInvariant` for `Gal(F/ℚ)` acting on `𝓞_F`, and the surjectivity
`G_ℚ → Gal(F/ℚ)`).** -/
def FrobExistsFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∀ (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [IsGalois ℚ F],
      (FrobOn p P F).Nonempty

lemma frobOn_anti {p : ℕ} {P : Ideal Zbar} {F F' : IntermediateField ℚ Qbar} (hF : F ≤ F') :
    FrobOn p P F' ⊆ FrobOn p P F :=
  fun _ hh x y hx hy => hh x y (hF hx) hy

lemma isClosed_frobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ F] : IsClosed (FrobOn p P F) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro h hh
  simp only [FrobOn, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hh
  obtain ⟨x, y, hx, hy, hyP⟩ := hh
  refine ⟨(fun k => h⁻¹ * k) ⁻¹' (F.fixingSubgroup : Set GQ), ?_, ?_, ?_⟩
  · intro k hk hk'
    have hfix := (IntermediateField.mem_fixingSubgroup_iff F _).mp hk (x : Qbar) hx
    change h⁻¹ (k (x : Qbar)) = (x : Qbar) at hfix
    have hkx : k (x : Qbar) = h (x : Qbar) := by
      have e := congrArg h hfix
      rwa [show h (h⁻¹ (k (x : Qbar))) = k (x : Qbar) from AlgEquiv.apply_symm_apply h _] at e
    exact hyP (hk' x y hx (by rw [hy, hkx]))
  · exact (IntermediateField.fixingSubgroup_isOpen F).preimage (continuous_const.mul continuous_id)
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact one_mem _

instance : IsGalois ℚ Qbar := ⟨⟩

/-- **Step (b) from its finite layer (GLUE, proved): compactness of `G_ℚ`.** -/
theorem frobExistsAt_of_finite (hf : FrobExistsFinite) : FrobExistsAt := by
  intro p _ P _ hP
  let ι := {F : IntermediateField ℚ Qbar // FiniteDimensional ℚ F}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  let t : ι → Set GQ := fun F => FrobOn p P F.1
  have htd : Directed (· ⊇ ·) t := by
    rintro ⟨F₁, h₁⟩ ⟨F₂, h₂⟩
    refine ⟨⟨F₁ ⊔ F₂, inferInstance⟩, frobOn_anti le_sup_left, frobOn_anti le_sup_right⟩
  have htn : ∀ F, (t F).Nonempty := by
    rintro ⟨F, hF⟩
    let N := IntermediateField.normalClosure ℚ F Qbar
    have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ F Qbar
    have : Normal ℚ N := normalClosure.normal ℚ F Qbar
    have : IsGalois ℚ N := ⟨⟩
    exact (hf p P hP N).mono (frobOn_anti F.le_normalClosure)
  have htcl : ∀ F, IsClosed (t F) := fun F => by
    have := F.2
    exact isClosed_frobOn p P F.1
  obtain ⟨h, hh⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun F => (htcl F).isCompact) htcl
  refine ⟨h, fun x y hy => ?_⟩
  have hxi : IsIntegral ℚ (x : Qbar) := Algebra.IsIntegral.isIntegral _
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(x : Qbar)}) :=
    IntermediateField.adjoin.finiteDimensional hxi
  exact Set.mem_iInter.mp hh ⟨IntermediateField.adjoin ℚ {(x : Qbar)}, this⟩ x y
    (IntermediateField.mem_adjoin_simple_self ℚ _) hy

/-- **Step (b), finite layer (GLUE, proved from Mathlib).** -/
theorem frobExistsFinite : FrobExistsFinite := by
  intro p _ P _ hP F _ _
  have : NumberField F := ⟨⟩
  set QF := P.comap (toZbar F) with hQF
  have hQFp : QF.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hP, Ideal.under, Ideal.under, hQF, Ideal.comap_comap]
    congr 1
  have hQFprime : QF.IsPrime := Ideal.comap_isPrime _ _
  have hQFne : QF ≠ ⊥ := by
    intro h0
    have hp : ((p : ℤ) : 𝓞 F) ∈ QF := by
      change algebraMap ℤ (𝓞 F) (p : ℤ) ∈ QF
      rw [← Ideal.mem_comap]
      change (p : ℤ) ∈ QF.under ℤ
      rw [hQFp]
      exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.mem_bot] at hp
    have : ((p : ℤ) : 𝓞 F) ≠ 0 := by
      have := (Fact.out : p.Prime).ne_zero
      exact_mod_cast this
    exact this hp
  have : QF.IsMaximal := hQFprime.isMaximal hQFne
  let _ := IsIntegralClosure.MulSemiringAction ℤ ℚ F (𝓞 F)
  have := Algebra.isInvariant_of_isGalois ℤ ℚ F (𝓞 F)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (F ≃ₐ[ℚ] F) QF
  obtain ⟨h, hres⟩ : ∃ h : GQ, AlgEquiv.restrictNormal h F = σ :=
    ⟨σ.liftNormal Qbar, σ.restrict_liftNormal Qbar⟩
  subst hres
  refine ⟨h, fun x y hx hy => ?_⟩
  have hxi : IsIntegral ℤ (⟨(x : Qbar), hx⟩ : F) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F Qbar) (algebraMap F Qbar).injective]
    exact x.2
  let x' : 𝓞 F := ⟨⟨(x : Qbar), hx⟩, hxi⟩
  have hmem := hσ x'
  rw [hQFp, card_quot, hQF, Ideal.mem_comap] at hmem
  convert hmem using 1
  apply Subtype.ext
  rw [hy, map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
    toZbar_coe]
  congr 1
  change h (x : Qbar) = ((algebraMap (𝓞 F) F (galRestrict ℤ ℚ F (𝓞 F) _ x')) : Qbar)
  rw [algebraMap_galRestrict_apply]
  exact (AlgEquiv.restrictNormal_commutes h F (algebraMap (𝓞 F) F x')).symm

/-- **`FrobLift` holds (GLUE, proved from Mathlib).** -/
theorem frobLift : FrobLift :=
  frobLift_of_frobExistsAt (frobExistsAt_of_finite frobExistsFinite)


/-- **Frobenius density from Chebotarev (GLUE, proved from I6.4 and `FrobLift`).** -/
theorem frobDense_of_chebotarev (hC : ChebotarevExists) (hL : FrobLift) (S : Finset ℕ) :
    FrobDense S := by
  intro E hE g
  set N := IntermediateField.normalClosure ℚ E Qbar
  have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ E Qbar
  have : Normal ℚ N := normalClosure.normal ℚ E Qbar
  have : IsGalois ℚ N := ⟨⟩
  have : NumberField N := ⟨⟩
  obtain ⟨p, hp, hpS, Q, hQ, hQp, hQu, hQf⟩ := hC N S (AlgEquiv.restrictNormal g N)
  obtain ⟨h, hh, hres⟩ := hL N _ p Q hp hQp hQu hQf
  refine ⟨h, p, hp, hpS, hh, fun x hx => ?_⟩
  have hxN : x ∈ N := E.le_normalClosure hx
  have e1 := AlgEquiv.restrictNormal_commutes h N ⟨x, hxN⟩
  have e2 := AlgEquiv.restrictNormal_commutes g N ⟨x, hxN⟩
  rw [hres] at e1
  simpa using e1.symm.trans e2

/-- **Passage from Frobenius classes to `G_ℚ` (GLUE, proved).**  Two continuous functions on
`G_ℚ` with values in a Hausdorff space that agree on the Frobenius elements at primes outside `S`
are equal, given `FrobDense S`. -/
theorem eq_of_eq_on_frob {X : Type*} [TopologicalSpace X] [T2Space X] (S : Finset ℕ)
    (hD : FrobDense S) (f₁ f₂ : GQ → X)
    (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hfr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → f₁ g = f₂ g) : f₁ = f₂ := by
  funext g
  by_contra hne
  have hopen : IsOpen {x | f₁ x ≠ f₂ x} := isOpen_ne_fun h₁ h₂
  have hmem : (fun y => g * y) ⁻¹' {x | f₁ x ≠ f₂ x} ∈ nhds (1 : GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  obtain ⟨h, p, hp, hpS, hh, hEq⟩ := hD E hE g
  have hfix : g⁻¹ * h ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change g⁻¹ (h x) = x
    rw [hEq x hx]
    exact AlgEquiv.symm_apply_apply g x
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_setOf_eq] at this
  exact this (hfr h p hp hpS hh)

/-- The trace of `ρ g` is the trace of its matrix in any basis. -/
lemma trace_eq_matrix {E V ι : Type*} [Field E] [AddCommGroup V] [Module E V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι E V) (f : V →ₗ[E] V) :
    LinearMap.trace E V f = (LinearMap.toMatrix b b f).trace :=
  LinearMap.trace_eq_matrix_trace E b f

lemma continuous_trace {E V ι : Type*} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [AddCommGroup V] [Module E V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E V)
    {G : Type*} [Monoid G] [TopologicalSpace G] (ρ : Representation E G V)
    (hρ : Continuous fun g => LinearMap.toMatrix b b (ρ g)) :
    Continuous fun g => LinearMap.trace E V (ρ g) := by
  simp_rw [trace_eq_matrix b]
  exact (continuous_finsetSum _ fun i _ => (continuous_apply_apply i i).comp hρ)

/-- **C10, the comparison in `G_ℚ` (GLUE, proved from I6.5 and `FrobDense`).**  Two continuous
semisimple finite-dimensional representations of `G_ℚ` over a Hausdorff topological field of
characteristic `0` (e.g. `ℚ_ℓ`, a finite extension, or `\bar ℚ_ℓ`) whose traces agree at the
Frobenius elements at all primes outside `S` are isomorphic.  Continuity is that of the matrix
coefficients in some basis. -/
theorem iso_of_trace_eq_on_frob (hBN : BrauerNesbittChar0) (S : Finset ℕ) (hD : FrobDense S)
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k (GQ) V)
    (σ : Representation k (GQ) W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra k (GQ)) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k (GQ)) σ.asModule)
    (htr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (GQ)] σ.asModule) := by
  have heq := eq_of_eq_on_frob S hD _ _ (continuous_trace bV ρ hρc) (continuous_trace bW σ hσc)
    htr
  exact hBN k _ V W ρ σ hρ hσ fun g => congrFun heq g

/-! ## Part C. N5's transport from five to three -/

/-- **C10, the identification of `r₃` (GLUE, proved from I6.5 and `FrobDense`).**  N5 L776-795:
`C` is the coefficient field, `ι₃ : C → k₃`, `ι₅ : C → k₅` the chosen embeddings.  For a
Frobenius `g` at `p ∉ S`, the abelian-variety side gives one element `c p ∈ C` with
`tr r_ℓ(g) = ι_ℓ(c p)` for `ℓ = 3, 5` (Mumford §19 Thm 4, see `Trace.lean`), and the modular side
gives `a p ∈ C` with `tr ρ_ℓ(g) = ι_ℓ(a p)`.  If `r₅` and `ρ₅` have the same traces at
Frobenius (C9: `r₅ ≅ ρ_{f,ι₅}`), then `c p = a p` in `C`, so the traces of `r₃` and `ρ₃` agree at
every Frobenius outside `S`, and `r₃ ≅ ρ₃`. -/
theorem iso_three_of_five (hBN : BrauerNesbittChar0) (S : Finset ℕ) (hD : FrobDense S)
    (C : Type) [Field C] (c a : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (r₅ : Representation k₅ GQ V₅) (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ V₅ (r₅ g) = LinearMap.trace k₅ W₅ (ρ₅ g))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ V₅ (r₅ g) = ι₅ (c p))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (a p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) := by
  refine iso_of_trace_eq_on_frob hBN S hD k V W ι κ bV bW r₃ ρ₃ hrc hρc hr hρ ?_
  intro g p hp hpS hg
  have hca : c p = a p := ι₅.injective
    ((hr₅ g p hp hpS hg).symm.trans ((h₅ g p hp hpS hg).trans (hρ₅ g p hp hpS hg)))
  rw [hr₃ g p hp hpS hg, hρ₃ g p hp hpS hg, hca]

/-- **The semisimplification step.**  A subrepresentation (here: a `k[G]`-submodule) of a
semisimple representation is semisimple; so `r_ℓ ⊂ V_ℓ(A) ⊗ k` inherits semisimplicity from
Faltings' Satz 3 (pkg-I3 `FaltingsSemisimple`, after base change to `k`). -/
theorem semisimple_of_le {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (hρ : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule)
    (N : Submodule (MonoidAlgebra k G) ρ.asModule) :
    IsSemisimpleModule (MonoidAlgebra k G) N := inferInstance

/-- **Step 3 of glue-assembly §2.2 (halving).**  If `ρ ≅ r ⊕ r` on traces, `tr ρ(g) = 2·tr r(g)`,
and `tr ρ(g) = ι(s)` for some `s ∈ C`, then `tr r(g) = ι(s/2)`: the element `c p = s/2 ∈ C` of
`iso_three_of_five`. -/
theorem trace_half {C k : Type} [Field C] [CharZero C] [Field k] [CharZero k] (ι : C →+* k)
    (tr tr' : k) (x : C) (h2 : tr = 2 * tr') (hs : tr = ι x) : tr' = ι (x / 2) := by
  rw [map_div₀, map_ofNat, ← hs, h2]
  field_simp


/-- Frobenius elements at primes outside `S` are dense in `G_ℚ` (from Chebotarev alone). -/
theorem frobDense (hC : ChebotarevExists) (S : Finset ℕ) : FrobDense S :=
  frobDense_of_chebotarev hC frobLift S

/-- **C10 (GLUE, proved from I6.4 Chebotarev and I6.5 Brauer–Nesbitt only).**  The statement of
`iso_three_of_five` with `FrobDense` discharged. -/
theorem c10 (hC : ChebotarevExists) (hBN : BrauerNesbittChar0) (S : Finset ℕ)
    (C : Type) [Field C] (c a : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (r₅ : Representation k₅ GQ V₅) (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ V₅ (r₅ g) = LinearMap.trace k₅ W₅ (ρ₅ g))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ V₅ (r₅ g) = ι₅ (c p))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (a p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) :=
  iso_three_of_five hBN S (frobDense hC S) C c a k₅ V₅ W₅ ι₅ r₅ ρ₅ h₅ hr₅ hρ₅ k V W ι κ ι₃ bV bW
    r₃ ρ₃ hrc hρc hr hρ hr₃ hρ₃

end TSkolemKW.C10

namespace TSkolemKW.C10

/-- `GlueC10.BrauerNesbittChar0` is the same Prop as `TSkolemKW.BrauerNesbittChar0`. -/
theorem brauerNesbittChar0' : BrauerNesbittChar0 := TSkolemKW.brauerNesbittChar0

/-- **C10 from Chebotarev alone (GLUE, proved).** `GlueC10.c10` with the Brauer–Nesbitt
hypothesis discharged by `TSkolemKW.brauerNesbittChar0`. -/
theorem c10_of_chebotarev (hC : ChebotarevExists) (S : Finset ℕ)
    (C : Type) [Field C] (c a : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (r₅ : Representation k₅ GQ V₅) (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ V₅ (r₅ g) = LinearMap.trace k₅ W₅ (ρ₅ g))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ V₅ (r₅ g) = ι₅ (c p))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (a p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) :=
  c10 hC brauerNesbittChar0' S C c a k₅ V₅ W₅ ι₅ r₅ ρ₅ h₅ hr₅ hρ₅ k V W ι κ ι₃ bV bW
    r₃ ρ₃ hrc hρc hr hρ hr₃ hρ₃

end TSkolemKW.C10

#print axioms TSkolemKW.C10.c10_of_chebotarev

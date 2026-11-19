import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate13Switch
import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalQuotientStage

/-!
# One presentation of the genuine support complexes at a coefficient stage ring

Manuscript `diophantine_zq.tex`, the support complexes of Lemma `ex:arith-common-coordinate`
(tex 4142–4194), the actual support comparisons (tex 3470–3498: "replacing the unramified
condition by the full condition then gives the singular quotient") and the two quotient blocks at
an unused split prime (tex 4176–4184), at the finite coefficient stages of the inner limit
(tex 4385–4451): the coefficients form a commutative topological ring `k`, a stage ring.

Round 9's presentation (`presCond`, `suppCx`, `presSplit`) and its switches (`suppSwitch`,
`suppQuotEquiv`, `suppSwitchRetract`) are written over a topological field. Their constructions
only use pieces stated over a commutative ring (`idSplit`, `selSplitOfCond`, `piExtract`,
`prodGCx`, lane RC30's `genuineUq`, `genuineLq`, `genuineιq`, lane RC26's `selData`,
`LocalConditions`, `CondInclusion`), so they are restated here over a coefficient stage ring, with
the same definitions and names suffixed `S`. The places of the presentation, their local groups
and localization maps (`presPrime`, `presGv`, `presLoc`), the identity split inclusion `idSplit`,
the distinctness `inr_ne_inr` of the two places above a prime and `equiv_trans_d` do not involve
the coefficients and are used as they stand.

* `condCxS`, `condιS`, `presCondS T`, `suppDataS T`, **`suppCxS T`**: the local conditions, the
  Selmer data and the support complex of the support `T`.
* `condSplitS`, **`presSplitS T p`**, `presCondInclS`, **`suppInclS T p`**: the switches of the
  local conditions at the two places above `p` and the inclusion `C_T → C_{T ∪ {p}}`, with lane
  RC26's change-of-condition sequence (`suppInclS_shortExact`).
* **`suppSwitchS T p`**, **`suppQuotEquivS`**, `suppQuotEquivS_d`: the switch of the support
  complexes; for `p ∉ T` its quotient is, as a complex, the sum of the two local quotients.
* `suppSwitchRetractS`, **`exists_suppSwitchRetractS`**: the quotient of the switch retracts onto
  `twoSingCx Fr q z z⁻¹` over the stage ring, from lane RC31's
  `exists_retract_twoPlaces_place_stage` (`TameCochainQuasiIso`, `IwasawaGenerators`,
  `GenuineCochainsInjective`).
* **`exists_splitInclusion_of_injective`**: over a commutative ring, a degreewise injective chain
  map whose source terms are injective modules extends to a `SplitInclusion` (a retraction from
  the extension property, the complement its kernel). **`exists_genuineSplitS`**: over a ring
  injective over itself, for a finite free `W` and an injective equivariant `f : W → M`, the
  genuine inflation `genuineιq` is the inclusion of a `SplitInclusion` (the terms of `[W → W]` are
  injective modules, `genuineUq_X_injective`); `exists_genuineSplitsS`: the family of splits `EU`
  of the presentation.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom)
open ZInQ.Manuscript.RC.Local (prodGCx twoSingCx IwasawaGenerators TameCochainQuasiIso
  GenuineCochainsInjective exists_retract_twoPlaces_place_stage)

/-! ### Splittings over a ring from injective source terms -/

section RingSplit

variable {R : Type} [CommRing R]

/-- **A retraction gives a complement** (tex 3470–3487 for the genuine splittings, tex 4385–4451
for the stage rings): if `r ∘ i = 1`, then `ker r` is a complement of `im i`. Kind: PROVED. -/
theorem isCompl_range_ker_of_leftInverse {P Q : Type} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (i : P →ₗ[R] Q) (r : Q →ₗ[R] P) (h : ∀ x, r (i x) = x) :
    IsCompl (LinearMap.range i) (LinearMap.ker r) := by
  refine ⟨Submodule.disjoint_def.2 fun y hy hr => ?_,
    Submodule.codisjoint_iff_exists_add_eq.2 fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hy
    rw [LinearMap.mem_ker, h] at hr
    rw [hr, map_zero]
  · refine ⟨i (r y), y - i (r y), LinearMap.mem_range_self i _, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, h, sub_self]

/-- **An injective map out of an injective module has a retraction** (tex 3470–3487,
4385–4451): extend the identity along the map. Kind: PROVED. -/
theorem exists_retraction_of_injective {P Q : Type} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [Module.Injective R P] (i : P →ₗ[R] Q)
    (hi : Function.Injective i) : ∃ r : Q →ₗ[R] P, ∀ x, r (i x) = x :=
  Module.Injective.out i hi LinearMap.id

/-- **A degreewise injective chain map with injective source terms is a split inclusion**
(tex 3470–3487, 4385–4451; over a field this is `exists_splitInclusion`, tex 5394–5403): if every
term of `C_P` is an injective module, each `iⁿ` has a retraction `rⁿ` and `ker rⁿ` is a
complement of `im iⁿ`. Kind: PROVED. -/
theorem exists_splitInclusion_of_injective {CP CR : GCx R} (i : GHom CP CR)
    (hi : ∀ n, Function.Injective (i.f n n rfl)) [∀ n, Module.Injective R (CP.X n)] :
    ∃ E : SplitInclusion CP CR, E.i = i := by
  choose r hr using fun n => exists_retraction_of_injective (i.f n n rfl) (hi n)
  exact ⟨⟨i, hi, fun n => LinearMap.ker (r n),
    fun n => isCompl_range_ker_of_leftInverse (i.f n n rfl) (r n) (hr n)⟩, rfl⟩

/-- **A subsingleton module is injective** (tex 3471–3487: the unramified condition vanishes
outside degrees `0` and `1`; tex 4385–4451). Kind: PROVED. -/
theorem moduleInjective_of_subsingleton {Q : Type} [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : Module.Injective R Q :=
  ⟨fun _ _ _ _ _ _ _ _ _ => ⟨0, fun _ => Subsingleton.elim _ _⟩⟩

/-- **A module linearly equivalent to an injective module is injective** (tex 3470–3487,
4385–4451). Kind: PROVED. -/
theorem moduleInjective_of_linearEquiv {P Q : Type} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) (hP : Module.Injective R P) :
    Module.Injective R Q :=
  ⟨fun _ _ _ _ _ _ f hf g => by
    have := hP
    obtain ⟨h, hh⟩ := Module.Injective.out f hf (e.symm.toLinearMap ∘ₗ g)
    exact ⟨e.toLinearMap ∘ₗ h, fun x => by simp [hh]⟩⟩

/-- **A finite free module over a ring injective over itself is injective** (tex 3470–3487,
4385–4451): `V ≅ R^n`, and a product of injective modules is injective (`Module.Injective.pi`).
Kind: PROVED. -/
theorem moduleInjective_of_finite_free [Module.Injective R R] (V : Type) [AddCommGroup V]
    [Module R V] [Module.Free R V] [Module.Finite R V] : Module.Injective R V :=
  moduleInjective_of_linearEquiv (Module.Free.chooseBasis R V).equivFun.symm
    (Module.Injective.pi R _)

end RingSplit

/-! ### The genuine inflation is split at a self-injective stage ring -/

section GenuineSplitS

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The terms of the unramified complex of an injective module are injective** (tex 3471–3487,
4385–4451): `[W --(Ψ − 1)--> W]` has `W` in degrees `0` and `1` and zero elsewhere.
Kind: PROVED. -/
theorem frobCx_X_injective {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W]
    (Ψ : W →ₗ[R] W) (hW : Module.Injective R W) (n : ℤ) :
    Module.Injective R ((frobCx Ψ).X n) := by
  by_cases h0 : n = 0
  · subst h0
    exact moduleInjective_of_linearEquiv
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Ψ - 1)) rel01).toLinearEquiv.symm hW
  by_cases h1 : n = 1
  · subst h1
    exact moduleInjective_of_linearEquiv
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Ψ - 1)) rel01
        (by decide)).toLinearEquiv.symm hW
  have := ModuleCat.subsingleton_of_isZero
    (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.isZero_X Ψ n h0 h1)
  exact moduleInjective_of_subsingleton

/-- **The terms of the genuine unramified condition are injective at a self-injective stage
ring** (tex 3471–3487, 4385–4451): for `W` finite free over a ring injective over itself, every
term of `[W --(Φ_w − 1)--> W]` is an injective module. Kind: PROVED. -/
theorem genuineUq_X_injective (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type) [CommRing k] [TopologicalSpace k]
    [Module.Injective k k] (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [Module.Free k X.V] [Module.Finite k X.V] (n : ℤ) :
    Module.Injective k ((genuineUq K S k w X).X n) :=
  frobCx_X_injective (frob (eUr K w.1) X) (moduleInjective_of_finite_free X.V) n

/-- **The genuine `ι_q` is a split inclusion at a self-injective stage ring** (tex 3470–3487,
4157–4194, 4385–4451): over a commutative ring `k` injective over itself, for a finite free `W`
and an injective `G_{K_w}`-equivariant `f : W → M`, the genuine inflation `genuineιq` is the
inclusion of a `SplitInclusion` of the unramified complex into `C^•_cont(G_{K_w}, M)`
(`exists_splitInclusion_of_injective`, `genuineιq_f_injective`, `genuineUq_X_injective`).
Kind: PROVED. -/
theorem exists_genuineSplitS (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type) [CommRing k] [TopologicalSpace k]
    [Module.Injective k k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] (w : Places K S)
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] [Module.Free k X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (hinj : Function.Injective f) :
    ∃ EUq : SplitInclusion (genuineUq K S k w X) (genuineLq K S k M w),
      EUq.i = genuineιq K S k M w X f hf := by
  have : Module.Finite k X.V := Module.Finite.of_finite
  have : ∀ n, Module.Injective k ((genuineUq K S k w X).X n) := genuineUq_X_injective K S k w X
  exact exists_splitInclusion_of_injective _ (genuineιq_f_injective K S k M w X f hf hinj)

/-- **The splits of the presentation exist at a self-injective stage ring** (tex 3470–3487,
4142–4194, 4385–4451): for finite free `W_j` and injective equivariant `f_j : W_j → M` at the
places `place j` of the presentation, there are split inclusions `EU j` of the genuine inflations
whose inclusions are `genuineιq … (f j)` (`exists_genuineSplitS` at every place).
Kind: PROVED. -/
theorem exists_genuineSplitsS (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type) [CommRing k] [TopologicalSpace k]
    [Module.Injective k k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] {ι : Type}
    (place : ι × Bool → Places K S) (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
    [∀ j, ContinuousSMul (GUr K (place j).1) (X j).V] [∀ j, DiscreteTopology (X j).V]
    [∀ j, Finite (X j).V] [∀ j, Module.Free k (X j).V] (f : ∀ j, (X j).V →ₗ[k] M)
    (hf : ∀ j (g : Gloc K (place j).1) (x : (X j).V),
      f j (resUr K (place j).1 g • x) = locMap K S (place j).1 g • f j x)
    (hinj : ∀ j, Function.Injective (f j)) :
    ∃ EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)),
      ∀ j, (EU j).i = genuineιq K S k M (place j) (X j) (f j) (hf j) := by
  choose EU hEU using fun j =>
    exists_genuineSplitS K S k M (place j) (X j) (f j) (hf j) (hinj j)
  exact ⟨EU, hEU⟩

end GenuineSplitS

/-! ### The presentation at a coefficient stage ring -/

section PresentationS

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))

/-- **The local condition at a new place, at a coefficient stage ring** (tex 3471–3498,
4385–4451): the full condition `C^•_cont(G_{K_w}, M)` (`true`) or the genuine unramified
condition `[W --(Φ_w − 1)--> W]` (`false`), with coefficients in a stage ring `k`.
Kind: definition. -/
def condCxS (j : ι × Bool) : Bool → GCx k
  | true => genuineLq K S k M (place j)
  | false => genuineUq K S k (place j) (X j)

/-- **The map of the local condition at a new place to the local complex, at a coefficient stage
ring** (tex 3471–3498, 4385–4451): the identity for the full condition, the chosen split
inclusion of the genuine inflation for the unramified one. Kind: definition. -/
def condιS (j : ι × Bool) : (b : Bool) → GHom (condCxS K S k M place X j b)
    (genuineLq K S k M (place j))
  | true => idGHom _
  | false => (EU j).i

omit [DecidableEq ι] in
/-- **Pinning: the full condition is the identity, at a coefficient stage ring** (tex 4157–4166,
4385–4451); this holds by definition. Kind: PROVED. -/
theorem condιS_true (j : ι × Bool) : condιS K S k M place X EU j true = idGHom _ :=
  rfl

omit [DecidableEq ι] in
/-- **Pinning: the unramified condition is the genuine one, at a coefficient stage ring**
(tex 3471–3487, 4385–4451): when the chosen split inclusion at `j` is a split inclusion of the
genuine inflation, the condition at `j` for `j.1 ∉ T` is lane RC30's `genuineιq` (lane RC31's
`ofCCHom (urToLocal_galois …)`). Kind: PROVED. -/
theorem condιS_false (j : ι × Bool) [ContinuousSMul (GUr K (place j).1) (X j).V]
    [DiscreteTopology (X j).V] [Finite (X j).V] (f : (X j).V →ₗ[k] M)
    (hf : ∀ (g : Gloc K (place j).1) (x : (X j).V),
      f (resUr K (place j).1 g • x) = locMap K S (place j).1 g • f x)
    (hE : (EU j).i = genuineιq K S k M (place j) (X j) f hf) :
    condιS K S k M place X EU j false = genuineιq K S k M (place j) (X j) f hf :=
  hE

/-- **The local conditions of the support `T`, at a coefficient stage ring** (tex 4142–4194,
4385–4451): the old conditions at `S₀`, the full condition at the two places above `p ∈ T`, the
unramified condition at those above `p ∉ T`. Kind: definition. -/
def presCondS (T : Finset ι) :
    LocalConditions k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M where
  U v := match v with
    | .inl v₀ => Δ.U v₀
    | .inr j => condCxS K S k M place X j (decide (j.1 ∈ T))
  i v := match v with
    | .inl v₀ => Δ.i v₀
    | .inr j => condιS K S k M place X EU j (decide (j.1 ∈ T))

/-- **The genuine Selmer data of the support `T`, at a coefficient stage ring** (tex 4142–4194,
3455–3463, 4385–4451): global continuous cochains of `G_{K,S}`, the local complexes at all the
places, the conditions `presCondS T`. Kind: definition. -/
abbrev suppDataS (T : Finset ι) : SelData k :=
  selData k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M
    (presCondS K S₀ S k M Δ place X EU T)

/-- **The genuine support complex `C_T` at a coefficient stage ring** (tex 4142–4194,
4385–4451): the Selmer complex of the support `T`. Kind: definition. -/
abbrev suppCxS (T : Finset ι) : GCx k := selCx (suppDataS K S₀ S k M Δ place X EU T)

/-- **The switch of the condition at a new place, at a coefficient stage ring** (tex 3489–3498,
4385–4451): from `b` to `b'` with `b → b'`; the identity if unchanged, the split inclusion of the
unramified condition in the full condition if switched. Kind: definition. -/
def condSplitS (j : ι × Bool) : (b b' : Bool) → (b = true → b' = true) →
    SplitInclusion (condCxS K S k M place X j b) (condCxS K S k M place X j b')
  | false, false, _ => idSplit _
  | false, true, _ => EU j
  | true, true, _ => idSplit _
  | true, false, h => absurd (h rfl) Bool.false_ne_true

omit [DecidableEq ι] in
/-- The switch is compatible with the maps to the local complex, at a coefficient stage ring
(tex 3489–3498, 4385–4451). Kind: PROVED. -/
theorem condSplitS_compat (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true) (n : ℤ)
    (x : (condCxS K S k M place X j b).X n) :
    (condιS K S k M place X EU j b').f n n rfl
        ((condSplitS K S k M place X EU j b b' h).i.f n n rfl x) =
      (condιS K S k M place X EU j b).f n n rfl x := by
  cases b <;> cases b'
  · rfl
  · rfl
  · exact absurd (h rfl) Bool.false_ne_true
  · rfl

/-- **The split inclusion of the local conditions `C_T ⊂ C_{T ∪ {p}}`, at a coefficient stage
ring** (tex 3489–3498, 4385–4451): the identity at the old places and at the places above primes
other than `p`, the switch at the two places above `p`. Kind: definition. -/
def presSplitS (T : Finset ι) (p : ι) : ∀ v : Places K S₀ ⊕ (ι × Bool),
    SplitInclusion ((presCondS K S₀ S k M Δ place X EU T).U v)
      ((presCondS K S₀ S k M Δ place X EU (insert p T)).U v)
  | .inl v₀ => idSplit (Δ.U v₀)
  | .inr j => condSplitS K S k M place X EU j (decide (j.1 ∈ T)) (decide (j.1 ∈ insert p T))
      (fun h => by
        rw [decide_eq_true_iff] at h ⊢
        exact Finset.mem_insert_of_mem h)

/-- The switch of the local conditions is compatible with the maps to the local complexes, at a
coefficient stage ring (tex 3489–3498, 4385–4451). Kind: PROVED. -/
theorem presSplitS_compat (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ)
    (x : ((presCondS K S₀ S k M Δ place X EU T).U v).X n) :
    ((presCondS K S₀ S k M Δ place X EU (insert p T)).i v).f n n rfl
        ((presSplitS K S₀ S k M Δ place X EU T p v).i.f n n rfl x) =
      ((presCondS K S₀ S k M Δ place X EU T).i v).f n n rfl x := by
  match v with
  | .inl v₀ => rfl
  | .inr j => exact condSplitS_compat K S k M place X EU j _ _ _ n x

omit [DecidableEq ι] in
/-- An unchanged condition has zero quotient, at a coefficient stage ring (tex 3489–3498,
4385–4451). Kind: PROVED. -/
theorem condSplitS_quot_subsingleton (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true)
    (hbb : b = b') (n : ℤ) :
    Subsingleton ((condSplitS K S k M place X EU j b b' h).quotientCx.X n) := by
  subst hbb
  cases b
  · exact idSplit_quot_subsingleton _ n
  · exact idSplit_quot_subsingleton _ n

/-- **Away from the two places above `p` the local quotients vanish, at a coefficient stage
ring** (tex 3489–3498, 4176–4184, 4385–4451). Kind: PROVED. -/
theorem presSplitS_quot_subsingleton (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool))
    (h₁ : v ≠ .inr (p, false)) (h₂ : v ≠ .inr (p, true)) (n : ℤ) :
    Subsingleton ((presSplitS K S₀ S k M Δ place X EU T p v).quotientCx.X n) := by
  match v with
  | .inl v₀ => exact idSplit_quot_subsingleton _ n
  | .inr j =>
    have hj : j.1 ≠ p := by
      intro hj
      obtain ⟨q, c⟩ := j
      simp only at hj
      subst hj
      cases c
      · exact h₁ rfl
      · exact h₂ rfl
    refine condSplitS_quot_subsingleton K S k M place X EU j _ _ _ ?_ n
    refine decide_eq_decide.2 ⟨fun h => Finset.mem_insert_of_mem h, fun h => ?_⟩
    rcases Finset.mem_insert.1 h with h | h
    · exact absurd h hj
    · exact h

/-- **At a switched place the local quotient is the quotient of the genuine unramified condition
in the full condition, at a coefficient stage ring** (tex 3489–3498, 4385–4451), degreewise.
Kind: definition. -/
def condSplitQuotEquivS (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true)
    (hb : b = false) (hb' : b' = true) (n : ℤ) :
    (condSplitS K S k M place X EU j b b' h).quotientCx.X n ≃ₗ[k] (EU j).quotientCx.X n := by
  subst hb hb'
  exact LinearEquiv.refl k _

omit [DecidableEq ι] in
/-- The identification at a switched place commutes with the differentials, at a coefficient
stage ring (tex 3489–3498, 4385–4451). Kind: PROVED. -/
theorem condSplitQuotEquivS_d (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true)
    (hb : b = false) (hb' : b' = true) (a c : ℤ) (hac : a + 1 = c)
    (x : (condSplitS K S k M place X EU j b b' h).quotientCx.X a) :
    (EU j).quotientCx.d a c hac (condSplitQuotEquivS K S k M place X EU j b b' h hb hb' a x) =
      condSplitQuotEquivS K S k M place X EU j b b' h hb hb' c
        ((condSplitS K S k M place X EU j b b' h).quotientCx.d a c hac x) := by
  subst hb hb'
  rfl

/-- **The change of conditions `C_T ⊂ C_{T ∪ {p}}` at a coefficient stage ring** as lane RC26's
termwise injective morphism of local conditions (tex 3489–3498, 4385–4451; Nekovář 6.4.2(i)).
Kind: definition. -/
def presCondInclS (T : Finset ι) (p : ι) :
    CondInclusion (presCondS K S₀ S k M Δ place X EU T)
      (presCondS K S₀ S k M Δ place X EU (insert p T)) where
  φ v := (presSplitS K S₀ S k M Δ place X EU T p v).i
  compat := presSplitS_compat K S₀ S k M Δ place X EU T p
  inj v n := (presSplitS K S₀ S k M Δ place X EU T p v).inj n

/-- **The inclusion of support complexes `C_T → C_{T ∪ {p}}` at a coefficient stage ring**,
`(a, u, x) ↦ (a, φ u, x)` (tex 3489–3498, 4157–4166, 4385–4451): lane RC26's `changeIncl`.
Kind: definition. -/
def suppInclS (T : Finset ι) (p : ι) :
    GHom (suppCxS K S₀ S k M Δ place X EU T) (suppCxS K S₀ S k M Δ place X EU (insert p T)) :=
  changeIncl (presCondInclS K S₀ S k M Δ place X EU T p)

/-- **`0 → C_T → C_{T ∪ {p}} → ⊕_v (local quotients) → 0` is short exact at a coefficient stage
ring** (tex 3489–3498, 4385–4451; lane RC26's `changeCondSES_shortExact`). Kind: PROVED. -/
theorem suppInclS_shortExact (T : Finset ι) (p : ι) :
    (changeCondSES (presCondInclS K S₀ S k M Δ place X EU T p)).ShortExact :=
  changeCondSES_shortExact _

/-- **Consecutive steps share their complexes literally, at a coefficient stage ring**
(tex 4185–4193, 4385–4451): the inclusions at `(T, p)` and at `(insert p T, p')` compose as they
stand (the target of the first is, by definition, the source of the second). Kind: definition. -/
def suppInclTwoS (T : Finset ι) (p p' : ι) :
    GHom (suppCxS K S₀ S k M Δ place X EU T)
      (suppCxS K S₀ S k M Δ place X EU (insert p' (insert p T))) :=
  ZInQ.Contrib.CloudB3RC53.SelmerDuality.ghomComp (suppInclS K S₀ S k M Δ place X EU T p)
    (suppInclS K S₀ S k M Δ place X EU (insert p T) p')

/-! ### The switches at a coefficient stage ring -/

variable [DecidableEq (Places K S₀)]

/-- **The switch `C_T ⊂ C_{T ∪ {p}}` at a coefficient stage ring** (tex 3489–3498, 4157–4166,
4385–4451): the split inclusion of genuine Selmer complexes from the switches of the local
conditions at the two places above `p`. Kind: definition. -/
def suppSwitchS (T : Finset ι) (p : ι) :
    SplitInclusion (suppCxS K S₀ S k M Δ place X EU T)
      (suppCxS K S₀ S k M Δ place X EU (insert p T)) :=
  selSplitOfCond (presCondS K S₀ S k M Δ place X EU T)
    (presCondS K S₀ S k M Δ place X EU (insert p T)) (presSplitS K S₀ S k M Δ place X EU T p)
    (presSplitS_compat K S₀ S k M Δ place X EU T p)

omit [DecidableEq (Places K S₀)] in
/-- The inclusion of the switch is lane RC26's change of conditions, at a coefficient stage ring
(tex 3489–3498, 4385–4451); this holds by definition. Kind: PROVED. -/
theorem suppSwitchS_i (T : Finset ι) (p : ι) :
    (suppSwitchS K S₀ S k M Δ place X EU T p).i = suppInclS K S₀ S k M Δ place X EU T p :=
  rfl

omit [DecidableEq (Places K S₀)] in
/-- The local quotients away from the two places above `p` vanish, in the form of the extraction
of two components, at a coefficient stage ring (tex 3489–3498, 4176–4184, 4385–4451).
Kind: PROVED. -/
theorem suppQuotS_sub (T : Finset ι) (p : ι) :
    ∀ (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ), v ≠ .inr (p, false) → v ≠ .inr (p, true) →
      Subsingleton ((presSplitS K S₀ S k M Δ place X EU T p v).quotientCx.X n) :=
  fun v n h₁ h₂ => presSplitS_quot_subsingleton K S₀ S k M Δ place X EU T p v h₁ h₂ n

/-- The identification of the two switched local quotients with the quotients of the genuine
unramified conditions, at a coefficient stage ring (tex 3489–3498, 4385–4451), degreewise, for
`p ∉ T`. Kind: definition. -/
def suppQuotEquivTwoS (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ) :
    (prodGCx (presSplitS K S₀ S k M Δ place X EU T p (.inr (p, false))).quotientCx
      (presSplitS K S₀ S k M Δ place X EU T p (.inr (p, true))).quotientCx).X n ≃ₗ[k]
      (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx).X n :=
  LinearEquiv.prodCongr
    (condSplitQuotEquivS K S k M place X EU (p, false) _ _ _ (decide_eq_false hp)
      (decide_eq_true (Finset.mem_insert_self p T)) n)
    (condSplitQuotEquivS K S k M place X EU (p, true) _ _ _ (decide_eq_false hp)
      (decide_eq_true (Finset.mem_insert_self p T)) n)

omit [DecidableEq (Places K S₀)] in
/-- The identification of the two switched local quotients commutes with the differentials, at a
coefficient stage ring (tex 3489–3498, 4385–4451). Kind: PROVED. -/
theorem suppQuotEquivTwoS_d (T : Finset ι) (p : ι) (hp : p ∉ T) (a b : ℤ) (h : a + 1 = b)
    (x : (prodGCx (presSplitS K S₀ S k M Δ place X EU T p (.inr (p, false))).quotientCx
      (presSplitS K S₀ S k M Δ place X EU T p (.inr (p, true))).quotientCx).X a) :
    (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx).d a b h
        (suppQuotEquivTwoS K S₀ S k M Δ place X EU T p hp a x) =
      suppQuotEquivTwoS K S₀ S k M Δ place X EU T p hp b
        ((prodGCx (presSplitS K S₀ S k M Δ place X EU T p (.inr (p, false))).quotientCx
          (presSplitS K S₀ S k M Δ place X EU T p (.inr (p, true))).quotientCx).d a b h x) :=
  Prod.ext
    (condSplitQuotEquivS_d K S k M place X EU (p, false) _ _ _ (decide_eq_false hp)
      (decide_eq_true (Finset.mem_insert_self p T)) a b h x.1)
    (condSplitQuotEquivS_d K S k M place X EU (p, true) _ _ _ (decide_eq_false hp)
      (decide_eq_true (Finset.mem_insert_self p T)) a b h x.2)

/-- **The quotient of the switch is the sum of the two local quotients, at a coefficient stage
ring** (tex 3489–3498, 4176–4184, 4385–4451), degreewise, for `p ∉ T`:
`C_{T ∪ {p}} / C_T ≅ L_w / U_w ⊕ L_w̄ / U_w̄`. Kind: definition. -/
def suppQuotEquivS (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ) :
    (suppSwitchS K S₀ S k M Δ place X EU T p).quotientCx.X n ≃ₗ[k]
      (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx).X n :=
  ((selSplitOfCond_quotEquiv (presCondS K S₀ S k M Δ place X EU T)
    (presCondS K S₀ S k M Δ place X EU (insert p T)) (presSplitS K S₀ S k M Δ place X EU T p)
    (presSplitS_compat K S₀ S k M Δ place X EU T p) n).trans
    (piExtract (inr_ne_inr K S₀ p) (suppQuotS_sub K S₀ S k M Δ place X EU T p) n)).trans
    (suppQuotEquivTwoS K S₀ S k M Δ place X EU T p hp n)

/-- **The identification of the quotient of the switch commutes with the differentials**, so it
is an isomorphism of complexes, at a coefficient stage ring (tex 3489–3498, 4176–4184,
4385–4451). Kind: PROVED. -/
theorem suppQuotEquivS_d (T : Finset ι) (p : ι) (hp : p ∉ T) (a b : ℤ) (h : a + 1 = b)
    (x : (suppSwitchS K S₀ S k M Δ place X EU T p).quotientCx.X a) :
    (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx).d a b h
        (suppQuotEquivS K S₀ S k M Δ place X EU T p hp a x) =
      suppQuotEquivS K S₀ S k M Δ place X EU T p hp b
        ((suppSwitchS K S₀ S k M Δ place X EU T p).quotientCx.d a b h x) :=
  equiv_trans_d _ _
    (equiv_trans_d _ _
      (selSplitOfCond_quotEquiv_d (presCondS K S₀ S k M Δ place X EU T)
        (presCondS K S₀ S k M Δ place X EU (insert p T)) (presSplitS K S₀ S k M Δ place X EU T p)
        (presSplitS_compat K S₀ S k M Δ place X EU T p))
      (piExtract_d (inr_ne_inr K S₀ p) (suppQuotS_sub K S₀ S k M Δ place X EU T p)))
    (suppQuotEquivTwoS_d K S₀ S k M Δ place X EU T p hp) a b h x

/-- **A retraction of the sum of the two local quotients is a retraction of the quotient of the
switch, at a coefficient stage ring** (tex 3489–3498, 4176–4184, 4385–4451): transport along
`suppQuotEquivS`. Kind: definition. -/
def suppSwitchRetractS (T : Finset ι) (p : ι) (hp : p ∉ T) {Y : GCx k}
    (R : GRetract (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx) Y) :
    GRetract (suppSwitchS K S₀ S k M Δ place X EU T p).quotientCx Y :=
  R.ofEquiv (fun n => (suppQuotEquivS K S₀ S k M Δ place X EU T p hp n).symm)
    (fun a b h x => (equiv_symm_d (suppQuotEquivS K S₀ S k M Δ place X EU T p hp)
      (suppQuotEquivS_d K S₀ S k M Δ place X EU T p hp) a b h x).symm)

/-- **The quotient retraction of a switch exists at a coefficient stage ring** (tex 3470–3481,
4176–4184, 4385–4451): for a Noetherian stage ring `k` injective over itself, a finite coefficient
module `M`, free over `k`, of `2`-power exponent, `p ∉ T`, genuine bijective inflations `f_w`,
`f_w̄` at the two places above `p` (the chosen splits `EU` of the genuine inflations), residue
cardinality `q` (odd) at both, and stage bases in which Frobenius is `z Fr` at `w` and `z⁻¹ Fr` at
`w̄`, the quotient of the switch `C_T ⊂ C_{T ∪ {p}}` retracts onto `twoSingCx Fr q z z⁻¹` over the
stage ring, given `TameCochainQuasiIso`, `IwasawaGenerators` and `GenuineCochainsInjective`
(lane RC31's `exists_retract_twoPlaces_place_stage`, transported by `suppSwitchRetractS`).
Kind: PROVED. -/
theorem exists_suppSwitchRetractS (hT : TameCochainQuasiIso) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) [IsNoetherianRing k] [Module.Injective k k]
    [Module.Free k M] [Finite M] (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) (T : Finset ι)
    (p : ι) (hp : p ∉ T) (q : ℕ) (hq : Odd q) (Fr : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    [∀ j, ContinuousSMul (GUr K (place j).1) (X j).V] [∀ j, DiscreteTopology (X j).V]
    [∀ j, Finite (X j).V] (f : ∀ j, (X j).V →ₗ[k] M)
    (hf : ∀ j (g : Gloc K (place j).1) (x : (X j).V),
      f j (resUr K (place j).1 g • x) = locMap K S (place j).1 g • f j x)
    (hbij : ∀ j, Function.Bijective (f j))
    (hqc : ∀ c : Bool, q = Nat.card (𝓞 K ⧸ (place (p, c)).1.asIdeal))
    (hE : ∀ j, (EU j).i = ofCCHom (urToLocal_galois K S (place j) (X j) (f j) (hf j)))
    (b₁ : (X (p, false)).V ≃ₗ[k] (Fin 2 → k))
    (hb₁ : ∀ v, b₁ (frob (eUr K (place (p, false)).1) (X (p, false)) v) =
      Matrix.toLin' (z • Fr) (b₁ v))
    (b₂ : (X (p, true)).V ≃ₗ[k] (Fin 2 → k))
    (hb₂ : ∀ v, b₂ (frob (eUr K (place (p, true)).1) (X (p, true)) v) =
      Matrix.toLin' (zi • Fr) (b₂ v)) :
    Nonempty (GRetract (suppSwitchS K S₀ S k M Δ place X EU T p).quotientCx
      (twoSingCx Fr q z zi)) := by
  obtain ⟨R⟩ := exists_retract_twoPlaces_place_stage hT hI hInj hexp q hq Fr z zi
    (place (p, false)) (X (p, false)) (f (p, false)) (hf (p, false)) (hbij (p, false))
    (hqc false) (EU (p, false)) (hE (p, false)) b₁ hb₁ (place (p, true)) (X (p, true))
    (f (p, true)) (hf (p, true)) (hbij (p, true)) (hqc true) (EU (p, true)) (hE (p, true))
    b₂ hb₂
  exact ⟨suppSwitchRetractS K S₀ S k M Δ place X EU T p hp R⟩

end PresentationS

end ZInQ.Manuscript.RC.Wiring

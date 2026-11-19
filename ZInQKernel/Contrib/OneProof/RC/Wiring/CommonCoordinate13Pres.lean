import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate12Leaf

/-!
# One presentation of the genuine support complexes

Manuscript `diophantine_zq.tex`, the support complexes of Lemma `ex:arith-common-coordinate`
(tex 4142–4194) and the actual support comparisons (tex 3489–3498: "replacing the unramified
condition by the full condition then gives the singular quotient").

All the places are present from the start: the old places `v ∈ S₀` with the old conditions `Δ`,
and, for every unused prime `p` (an element of the index type `ι`), its two places `(p, false)`,
`(p, true)` (the places `w`, `w̄` above the split prime). For a support `T ⊆ ι` the condition at a
place above `p` is the full condition `C^•_cont(G_{K_w}, M)` (the identity) if `p ∈ T` and the
genuine unramified condition `[W → W]` (through a split inclusion of the genuine inflation) if
`p ∉ T`. The support complex `C_T` is the genuine Selmer complex (lane RC26's `selData`) of these
conditions. Since `C_T` is a function of `T`, consecutive steps of a chain of relaxations share
their complexes literally.

* `presPrime`, `presGv`, `presLoc`: the places of the presentation, their local groups and
  localization maps (lane RC26's conventions).
* `condCx`, `condι`: the local condition at a new place, full (`true`) or unramified (`false`).
* `presCond T`, `suppData T`, **`suppCx T`**: the local conditions, the Selmer data and the
  support complex of the support `T`.
* `idSplit`, `condSplit`, **`presSplit T p`**: the split inclusions of the local conditions
  `C_T ⊂ C_{T ∪ {p}}` switching the two places above `p` (the identity elsewhere);
  `presSplit_compat`: the compatibility with the maps to the local complexes.
* `presCondIncl`, **`suppIncl T p : C_T → C_{T ∪ {p}}`** (lane RC26's `changeIncl`),
  `suppIncl_shortExact` (lane RC26's change-of-condition sequence).
* `condSplit_quot_subsingleton`, `presSplit_quot_subsingleton`: away from the two places above
  `p` the local quotients vanish; `condSplitQuotEquiv`, `condSplitQuotEquiv_d`: at the two places
  above `p ∉ T` the local quotient is the quotient of the genuine unramified condition in the full
  condition.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom)

/-! ### The identity split inclusion -/

section IdSplit

variable {A : Type} [CommRing A]

/-- **The identity split inclusion** `C ⊂ C` with zero complement (tex 3489–3498: the unchanged
places). Kind: definition. -/
def idSplit (C : GCx A) : SplitInclusion C C where
  i := idGHom C
  inj _ := fun _ _ h => h
  Qc _ := ⊥
  compl n := by
    have h : LinearMap.range ((idGHom C).f n n rfl) = ⊤ := LinearMap.range_eq_top.2
      (fun x => ⟨x, rfl⟩)
    rw [h]
    exact isCompl_top_bot

/-- The quotient of the identity split inclusion vanishes (tex 3489–3498). Kind: PROVED. -/
theorem idSplit_quot_subsingleton (C : GCx A) (n : ℤ) :
    Subsingleton ((idSplit C).quotientCx.X n) := by
  change Subsingleton ↥(⊥ : Submodule A (C.X n))
  infer_instance

end IdSplit

/-! ### The presentation -/

section Presentation

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))

/-- **The prime of a place of the presentation** (tex 4142–4143): the old places `S₀` and the two
places above each unused prime. Kind: definition. -/
def presPrime : Places K S₀ ⊕ (ι × Bool) → HeightOneSpectrum (𝓞 K) :=
  Sum.elim (fun v => v.1) (fun j => (place j).1)

/-- The local Galois groups `G_{K_v}` of the places of the presentation (tex 3455–3463).
Kind: definition. -/
abbrev presGv (v : Places K S₀ ⊕ (ι × Bool)) : Type := Gloc K (presPrime K S₀ S place v)

/-- The localization maps `G_{K_v} → G_{K,S}` of the places of the presentation
(tex 3455–3463). Kind: definition. -/
abbrev presLoc (v : Places K S₀ ⊕ (ι × Bool)) : presGv K S₀ S place v →ₜ* GKS K S :=
  locMap K S (presPrime K S₀ S place v)

/-- **The local condition at a new place** (tex 3471–3498): the full condition
`C^•_cont(G_{K_w}, M)` (`true`) or the genuine unramified condition `[W --(Φ_w − 1)--> W]`
(`false`). Kind: definition. -/
def condCx (j : ι × Bool) : Bool → GCx k
  | true => genuineLq K S k M (place j)
  | false => genuineUq K S k (place j) (X j)

/-- **The map of the local condition at a new place** to the local complex (tex 3471–3498): the
identity for the full condition, the chosen split inclusion of the genuine inflation for the
unramified one. Kind: definition. -/
def condι (j : ι × Bool) : (b : Bool) → GHom (condCx K S k M place X j b)
    (genuineLq K S k M (place j))
  | true => idGHom _
  | false => (EU j).i

omit [DecidableEq ι] in
/-- **Pinning: the full condition is the identity** (tex 4157–4166). Kind: PROVED
(definitional). -/
theorem condι_true (j : ι × Bool) : condι K S k M place X EU j true = idGHom _ :=
  rfl

omit [DecidableEq ι] in
/-- **Pinning: the unramified condition is the genuine one** (tex 3471–3487): when the chosen
split inclusion at `j` is a split inclusion of the genuine inflation, the condition at `j` for
`j.1 ∉ T` is lane RC30's `genuineιq` (lane RC31's `ofCCHom (urToLocal_galois …)`).
Kind: PROVED. -/
theorem condι_false (j : ι × Bool) [ContinuousSMul (GUr K (place j).1) (X j).V]
    [DiscreteTopology (X j).V] [Finite (X j).V] (f : (X j).V →ₗ[k] M)
    (hf : ∀ (g : Gloc K (place j).1) (x : (X j).V),
      f (resUr K (place j).1 g • x) = locMap K S (place j).1 g • f x)
    (hE : (EU j).i = genuineιq K S k M (place j) (X j) f hf) :
    condι K S k M place X EU j false = genuineιq K S k M (place j) (X j) f hf :=
  hE

/-- **The local conditions of the support `T`** (tex 4142–4194): the old conditions at `S₀`, the
full condition at the two places above `p ∈ T`, the unramified condition at those above `p ∉ T`.
Kind: definition. -/
def presCond (T : Finset ι) :
    LocalConditions k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M where
  U v := match v with
    | .inl v₀ => Δ.U v₀
    | .inr j => condCx K S k M place X j (decide (j.1 ∈ T))
  i v := match v with
    | .inl v₀ => Δ.i v₀
    | .inr j => condι K S k M place X EU j (decide (j.1 ∈ T))

/-- **The genuine Selmer data of the support `T`** (tex 4142–4194, 3455–3463): global continuous
cochains of `G_{K,S}`, the local complexes at all the places, the conditions `presCond T`.
Kind: definition. -/
abbrev suppData (T : Finset ι) : SelData k :=
  selData k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M
    (presCond K S₀ S k M Δ place X EU T)

/-- **The genuine support complex `C_T`** (tex 4142–4194): the Selmer complex of the support `T`.
Kind: definition. -/
abbrev suppCx (T : Finset ι) : GCx k := selCx (suppData K S₀ S k M Δ place X EU T)

/-- **The switch of the condition at a new place** (tex 3489–3498): from `b` to `b'` with
`b → b'`; the identity if unchanged, the split inclusion of the unramified condition in the full
condition if switched. Kind: definition. -/
def condSplit (j : ι × Bool) : (b b' : Bool) → (b = true → b' = true) →
    SplitInclusion (condCx K S k M place X j b) (condCx K S k M place X j b')
  | false, false, _ => idSplit _
  | false, true, _ => EU j
  | true, true, _ => idSplit _
  | true, false, h => absurd (h rfl) Bool.false_ne_true

omit [DecidableEq ι] in
/-- The switch is compatible with the maps to the local complex (tex 3489–3498). Kind: PROVED. -/
theorem condSplit_compat (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true) (n : ℤ)
    (x : (condCx K S k M place X j b).X n) :
    (condι K S k M place X EU j b').f n n rfl
        ((condSplit K S k M place X EU j b b' h).i.f n n rfl x) =
      (condι K S k M place X EU j b).f n n rfl x := by
  cases b <;> cases b'
  · rfl
  · rfl
  · exact absurd (h rfl) Bool.false_ne_true
  · rfl

/-- **The split inclusion of the local conditions `C_T ⊂ C_{T ∪ {p}}`** (tex 3489–3498): the
identity at the old places and at the places above primes other than `p`, the switch at the two
places above `p`. Kind: definition. -/
def presSplit (T : Finset ι) (p : ι) : ∀ v : Places K S₀ ⊕ (ι × Bool),
    SplitInclusion ((presCond K S₀ S k M Δ place X EU T).U v)
      ((presCond K S₀ S k M Δ place X EU (insert p T)).U v)
  | .inl v₀ => idSplit (Δ.U v₀)
  | .inr j => condSplit K S k M place X EU j (decide (j.1 ∈ T)) (decide (j.1 ∈ insert p T))
      (fun h => by
        rw [decide_eq_true_iff] at h ⊢
        exact Finset.mem_insert_of_mem h)

/-- The switch of the local conditions is compatible with the maps to the local complexes
(tex 3489–3498). Kind: PROVED. -/
theorem presSplit_compat (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ)
    (x : ((presCond K S₀ S k M Δ place X EU T).U v).X n) :
    ((presCond K S₀ S k M Δ place X EU (insert p T)).i v).f n n rfl
        ((presSplit K S₀ S k M Δ place X EU T p v).i.f n n rfl x) =
      ((presCond K S₀ S k M Δ place X EU T).i v).f n n rfl x := by
  match v with
  | .inl v₀ => rfl
  | .inr j => exact condSplit_compat K S k M place X EU j _ _ _ n x

omit [DecidableEq ι] in
/-- An unchanged condition has zero quotient (tex 3489–3498). Kind: PROVED. -/
theorem condSplit_quot_subsingleton (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true)
    (hbb : b = b') (n : ℤ) :
    Subsingleton ((condSplit K S k M place X EU j b b' h).quotientCx.X n) := by
  subst hbb
  cases b
  · exact idSplit_quot_subsingleton _ n
  · exact idSplit_quot_subsingleton _ n

/-- **Away from the two places above `p` the local quotients vanish** (tex 3489–3498, 4176–4184).
Kind: PROVED. -/
theorem presSplit_quot_subsingleton (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool))
    (h₁ : v ≠ .inr (p, false)) (h₂ : v ≠ .inr (p, true)) (n : ℤ) :
    Subsingleton ((presSplit K S₀ S k M Δ place X EU T p v).quotientCx.X n) := by
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
    refine condSplit_quot_subsingleton K S k M place X EU j _ _ _ ?_ n
    refine decide_eq_decide.2 ⟨fun h => Finset.mem_insert_of_mem h, fun h => ?_⟩
    rcases Finset.mem_insert.1 h with h | h
    · exact absurd h hj
    · exact h

/-- **At a switched place the local quotient is the quotient of the genuine unramified condition
in the full condition** (tex 3489–3498), degreewise. Kind: definition. -/
def condSplitQuotEquiv (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true) (hb : b = false)
    (hb' : b' = true) (n : ℤ) :
    (condSplit K S k M place X EU j b b' h).quotientCx.X n ≃ₗ[k] (EU j).quotientCx.X n := by
  subst hb hb'
  exact LinearEquiv.refl k _

omit [DecidableEq ι] in
/-- The identification at a switched place commutes with the differentials (tex 3489–3498).
Kind: PROVED. -/
theorem condSplitQuotEquiv_d (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true)
    (hb : b = false) (hb' : b' = true) (a c : ℤ) (hac : a + 1 = c)
    (x : (condSplit K S k M place X EU j b b' h).quotientCx.X a) :
    (EU j).quotientCx.d a c hac (condSplitQuotEquiv K S k M place X EU j b b' h hb hb' a x) =
      condSplitQuotEquiv K S k M place X EU j b b' h hb hb' c
        ((condSplit K S k M place X EU j b b' h).quotientCx.d a c hac x) := by
  subst hb hb'
  rfl

/-- **The change of conditions `C_T ⊂ C_{T ∪ {p}}`** as lane RC26's termwise injective morphism
of local conditions (tex 3489–3498; Nekovář 6.4.2(i)). Kind: definition. -/
def presCondIncl (T : Finset ι) (p : ι) :
    CondInclusion (presCond K S₀ S k M Δ place X EU T)
      (presCond K S₀ S k M Δ place X EU (insert p T)) where
  φ v := (presSplit K S₀ S k M Δ place X EU T p v).i
  compat := presSplit_compat K S₀ S k M Δ place X EU T p
  inj v n := (presSplit K S₀ S k M Δ place X EU T p v).inj n

/-- **The inclusion of support complexes `C_T → C_{T ∪ {p}}`**, `(a, u, x) ↦ (a, φ u, x)`
(tex 3489–3498, 4157–4166): lane RC26's `changeIncl`. Kind: definition. -/
def suppIncl (T : Finset ι) (p : ι) :
    GHom (suppCx K S₀ S k M Δ place X EU T) (suppCx K S₀ S k M Δ place X EU (insert p T)) :=
  changeIncl (presCondIncl K S₀ S k M Δ place X EU T p)

/-- **`0 → C_T → C_{T ∪ {p}} → ⊕_v (local quotients) → 0` is short exact** (tex 3489–3498;
lane RC26's `changeCondSES_shortExact`). Kind: PROVED. -/
theorem suppIncl_shortExact (T : Finset ι) (p : ι) :
    (changeCondSES (presCondIncl K S₀ S k M Δ place X EU T p)).ShortExact :=
  changeCondSES_shortExact _

/-- **Consecutive steps share their complexes literally** (tex 4185–4193): the inclusions at
`(T, p)` and at `(insert p T, p')` compose as they stand (the target of the first is, by
definition, the source of the second). Kind: definition. -/
def suppInclTwo (T : Finset ι) (p p' : ι) :
    GHom (suppCx K S₀ S k M Δ place X EU T)
      (suppCx K S₀ S k M Δ place X EU (insert p' (insert p T))) :=
  ZInQ.Contrib.CloudB3RC53.SelmerDuality.ghomComp (suppIncl K S₀ S k M Δ place X EU T p)
    (suppIncl K S₀ S k M Δ place X EU (insert p T) p')

end Presentation

end ZInQ.Manuscript.RC.Wiring

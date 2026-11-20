import ZInQKernel.Contrib.OneProof.SelmerTwoPower
import ZInQKernel.Contrib.OneProof.CofinitePrimary

/-!
# The Selmer groups of `SelmerTwoPower` over one family of completions

`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean` defines `Sha(E/ℚ)`, `Sel_{2^n}(E/ℚ)` and
`Sel_{2^∞}(E/ℚ)` with two families of local fields, `ℚ_p` at the primes (`embFin`) and `ℝ` at the infinite
place (`embInf`). Tau Ceti's descent sequences (`WeierstrassCurve.kummerSelmerMap`,
`WeierstrassCurve.selmerShaMap`) are stated for one family. This file indexes the same local fields by
`Place = Nat.Primes ⊕ Unit` (`emb`), defines the groups over that one family (`Fam.sha`, `Fam.selmerAt`,
`Fam.selmerTwoPower`, `Fam.SelmerCorankOne`), proves that they are the groups of `SelmerTwoPower`
(`sha_eq`, `selmerAt_eq`, `selmerTwoPower_eq`, `selmerCorankOne_iff`: the same subgroups of the same `H¹`;
the local fields and embeddings are literally those of `SelmerTwoPower`, only reindexed), and proves:

* `twoPowerShortExact`: `0 → E[2^n] → E[2^∞] → E[2^∞] → 0`, multiplication by `2^n` on the right;
* `range_selmerAtToTwoPower`: the image of `Sel_{2^n} → Sel_{2^∞}` is `Sel_{2^∞}[2^n]`;
* `exists_z2Corank`: a `2`-primary group with finite `2`-torsion has a `ℤ₂`-corank
  (`ZInQ.Cofinite.exists_addEquiv_of_isPPrimary`).
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower.Fam

open TauCeti TauCeti.ContCohomology

/-! ### The places of `ℚ` and their completions -/

/-- **The places of `ℚ`**: the primes `p` (`Sum.inl p`) and the infinite place (`Sum.inr ()`). -/
abbrev Place : Type := Nat.Primes ⊕ Unit

/-- **The completion of `ℚ` at a place**: `ℚ_p` at `p`, `ℝ` at the infinite place. -/
abbrev Completion : Place → Type :=
  Sum.elim (fun p : Nat.Primes => ℚ_[(p : ℕ)]) (fun _ : Unit => ℝ)

instance instFieldCompletion : ∀ v, Field (Completion v) := fun v =>
  Sum.rec (motive := fun v => Field (Completion v)) (fun p => (inferInstance : Field ℚ_[(p : ℕ)]))
    (fun _ => (inferInstance : Field ℝ)) v

instance instAlgebraCompletion : ∀ v, Algebra ℚ (Completion v) := fun v =>
  Sum.rec (motive := fun v => Algebra ℚ (Completion v))
    (fun p => (inferInstance : Algebra ℚ ℚ_[(p : ℕ)])) (fun _ => (inferInstance : Algebra ℚ ℝ)) v

/-- **A fixed `ℚ`-embedding of separable closures `ℚˢ → (ℚ_v)ˢ` at every place `v`** (its type,
`SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ_v`, is inferred from `sepClosureEmb` so that it carries
the algebra structures Tau Ceti's groups expect). The Selmer and Shafarevich–Tate groups below do
not depend on this choice (Tau Ceti `WeierstrassCurve.shafarevichTateGroup_eq_shafarevichTateGroup`,
`EmbeddingIndependence.lean`). -/
def emb (v : Place) :=
  sepClosureEmb ℚ (Completion v)

/-! ### `E(ℚˢ)[2^∞]` as a discrete Galois module -/

variable (E : WeierstrassCurve ℚ)

/-! ### The `2`-primary Selmer group -/

/-- **`Sha(E/ℚ)`**: Tau Ceti's Shafarevich–Tate group for the family of completions of `ℚ` at all
places, i.e. the classes in `H¹(G_ℚ, E(ℚˢ))` that restrict to zero over every `ℚ_p` and over `ℝ`. -/
def sha : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff) :=
  E.shafarevichTateGroup emb

/-- **The `2`-primary Selmer group `Sel_{2^∞}(E/ℚ)`**: the classes in `H¹(G_ℚ, E(ℚˢ)[2^∞])` whose
image in `H¹(G_ℚ, E(ℚˢ))` lies in `Sha(E/ℚ)`, that is, restricts to zero over the completion of `ℚ`
at every place (Silverman X.4, with `E[m]` replaced by `E[2^∞]`; compare Tau Ceti's
`WeierstrassCurve.mem_selmerGroup_iff` for `E[m]`). -/
def selmerTwoPower : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) :=
  (sha E).comap
    (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
      continuous_of_discreteTopology)

/-- Membership in `Sel_{2^∞}(E/ℚ)`: the image in `H¹(G_ℚ, E(ℚˢ))` restricts to zero at every place
of `ℚ`. -/
theorem mem_selmerTwoPower_iff {c : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)} :
    c ∈ selmerTwoPower E ↔ ∀ v, E.pointRes (emb v)
      (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
        continuous_of_discreteTopology c) = 0 := by
  rw [selmerTwoPower, AddSubgroup.mem_comap, sha, WeierstrassCurve.mem_shafarevichTateGroup_iff]

/-! ### The `2^n`-Selmer groups and the maps `Sel_{2^n} → Sel_{2^∞}` -/

/-- **`Sel_{2^n}(E/ℚ)`**: Tau Ceti's `2^n`-Selmer group with the local conditions at every place of
`ℚ`. -/
def selmerAt (n : ℕ) : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))) :=
  E.selmerGroup emb (2 ^ n)

/-- The map `H¹(G_ℚ, E[2^n]) → H¹(G_ℚ, E[2^∞])` sends `Sel_{2^n}(E/ℚ)` into `Sel_{2^∞}(E/ℚ)`: both
classes have the same image in `H¹(G_ℚ, E(ℚˢ))`. -/
theorem explicitCoeff1_torsionToTwoPower_mem {n : ℕ}
    {c : H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))} (hc : c ∈ selmerAt E n) :
    explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (torsionToTwoPower E n)
      continuous_of_discreteTopology c ∈ selmerTwoPower E := by
  have hcomp : explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
      continuous_of_discreteTopology
      (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (torsionToTwoPower E n)
        continuous_of_discreteTopology c) =
      explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (E.torsionCoeffIncl (2 ^ n))
        continuous_of_discreteTopology c := by
    rw [← twoPowerCoeffIncl_comp_torsionToTwoPower, explicitCoeff1_comp]
    rfl
  rw [selmerAt, WeierstrassCurve.mem_selmerGroup_iff] at hc
  rw [selmerTwoPower, AddSubgroup.mem_comap, hcomp, sha]
  exact hc

/-- **The map `Sel_{2^n}(E/ℚ) → Sel_{2^∞}(E/ℚ)`** induced by `E[2^n] ⊆ E[2^∞]`. -/
def selmerAtToTwoPower (n : ℕ) : selmerAt E n →+ selmerTwoPower E where
  toFun c := ⟨explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
      (torsionToTwoPower E n) continuous_of_discreteTopology c,
    explicitCoeff1_torsionToTwoPower_mem E c.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-! ### `0 → E[2^n] → E[2^∞] → E[2^∞] → 0` and `Sel_{2^n} ↠ Sel_{2^∞}[2^n]` -/

/-- **The short exact sequence `0 → E(ℚˢ)[2^n] → E(ℚˢ)[2^∞] → E(ℚˢ)[2^∞] → 0`**, the second map
being multiplication by `2^n`. Exactness on the right is the divisibility of `E(ℚˢ)` by `2^n`
(Tau Ceti `Affine.nsmul_surjective`): a `2^n`-th part of a point of `2`-power order again has
`2`-power order. -/
def twoPowerShortExact [E.IsElliptic] (n : ℕ) :
    DiscreteShortExact (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (TwoPowerCoeff E)
      (TwoPowerCoeff E) where
  incl := (torsionToTwoPower E n).toAddMonoidHom
  proj := nsmulAddMonoidHom (2 ^ n)
  incl_equivariant σ P := (torsionToTwoPower E n).map_smul σ P
  proj_equivariant σ P := smul_comm (2 ^ n) σ P
  incl_injective a b h := Subtype.ext (congrArg (fun x : TwoPowerCoeff E => (x : E.PointCoeff)) h)
  proj_surjective P := by
    classical
    obtain ⟨Q, hQ⟩ := WeierstrassCurve.Affine.nsmul_surjective (E.baseChange (SeparableClosure ℚ)).toAffine
      (n := 2 ^ n) (Nat.cast_ne_zero.mpr (pow_ne_zero n two_ne_zero)) (E.pointCoeffEquiv.symm P)
    have hQ' : (2 ^ n) • E.pointCoeffEquiv Q = (P : E.PointCoeff) := by
      rw [← map_nsmul]
      exact (congrArg E.pointCoeffEquiv hQ).trans (E.pointCoeffEquiv.apply_symm_apply _)
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp P.2
    refine ⟨⟨E.pointCoeffEquiv Q, AddCommGroup.mem_primaryComponent.mpr ⟨n + k, ?_⟩⟩,
      Subtype.ext ?_⟩
    · calc (2 ^ (n + k)) • E.pointCoeffEquiv Q = (2 ^ k) • ((2 ^ n) • E.pointCoeffEquiv Q) := by
            rw [← mul_nsmul, ← pow_add, add_comm]
        _ = 0 := by rw [hQ', hk]
    · simpa [nsmulAddMonoidHom_apply] using hQ'
  exact P := by
    constructor
    · intro h
      have h' : (2 ^ n) • (P : E.PointCoeff) = 0 := by
        simpa [nsmulAddMonoidHom_apply] using congrArg Subtype.val h
      exact ⟨⟨P, (AddSubgroup.torsionBy.nsmul_iff).mpr h'⟩, Subtype.ext rfl⟩
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      simpa [nsmulAddMonoidHom_apply, torsionToTwoPower] using
        (AddSubgroup.torsionBy.nsmul_iff).mp a.2

theorem twoPowerShortExact_inclDistribMulActionHom [E.IsElliptic] (n : ℕ) :
    (twoPowerShortExact E n).inclDistribMulActionHom = torsionToTwoPower E n :=
  rfl

/-- **`Sel_{2^n}(E/ℚ)` maps onto `Sel_{2^∞}(E/ℚ)[2^n]`**: every Selmer class of `E[2^∞]` killed by
`2^n` comes from a class of `Sel_{2^n}(E/ℚ)`. By the long exact sequence of
`0 → E[2^n] → E[2^∞] → E[2^∞] → 0` it comes from some class of `H¹(G_ℚ, E[2^n])`, and that class is
Selmer because it has the same image in `H¹(G_ℚ, E(ℚˢ))`. -/
theorem exists_selmerAt_eq_of_nsmul_eq_zero [E.IsElliptic] {n : ℕ}
    {c : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)} (hc : c ∈ selmerTwoPower E)
    (hn : (2 ^ n) • c = 0) :
    ∃ c' ∈ selmerAt E n, explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
      (torsionToTwoPower E n) continuous_of_discreteTopology c' = c := by
  have hker : c ∈ (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)
      (twoPowerShortExact E n).projDistribMulActionHom continuous_of_discreteTopology).ker := by
    rw [AddMonoidHom.mem_ker, explicitCoeff1_eq_nsmul (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)
      (k := 2 ^ n) _ _ (fun _ => rfl)]
    exact hn
  rw [← (twoPowerShortExact E n).explicitLongExact_H1B,
    twoPowerShortExact_inclDistribMulActionHom] at hker
  obtain ⟨c', rfl⟩ := hker
  refine ⟨c', ?_, rfl⟩
  have hcomp : explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
      (E.torsionCoeffIncl (2 ^ n)) continuous_of_discreteTopology c' =
      explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
        continuous_of_discreteTopology
        (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (torsionToTwoPower E n)
          continuous_of_discreteTopology c') := by
    rw [← twoPowerCoeffIncl_comp_torsionToTwoPower, explicitCoeff1_comp]
    rfl
  rw [selmerAt, WeierstrassCurve.mem_selmerGroup_iff, hcomp]
  exact hc

/-- **The image of `Sel_{2^n}(E/ℚ) → Sel_{2^∞}(E/ℚ)` is the `2^n`-torsion of `Sel_{2^∞}(E/ℚ)`.** -/
theorem range_selmerAtToTwoPower [E.IsElliptic] (n : ℕ) :
    (selmerAtToTwoPower E n).range = AddSubgroup.torsionBy (selmerTwoPower E) ((2 ^ n : ℕ) : ℤ) := by
  ext c
  constructor
  · rintro ⟨c', rfl⟩
    rw [AddSubgroup.torsionBy.nsmul_iff]
    apply Subtype.ext
    change (2 ^ n) • explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
      (torsionToTwoPower E n) continuous_of_discreteTopology (c' : _) = 0
    rw [← map_nsmul, nsmul_H1_eq_zero (fun P => AddSubgroup.torsionBy.nsmul P)
      (c' : H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))), map_zero]
  · intro hc
    rw [AddSubgroup.torsionBy.nsmul_iff] at hc
    obtain ⟨c', hc', h⟩ := exists_selmerAt_eq_of_nsmul_eq_zero E c.2
      (by simpa using congrArg Subtype.val hc)
    exact ⟨⟨c', hc'⟩, Subtype.ext h⟩

/-! ### The `ℤ₂`-corank -/

/-- `ℚ₂/ℤ₂` is `ZInQ.Cofinite.Qp 2`. -/
theorem q2z2_eq : Q2Z2 = ZInQ.Cofinite.Qp 2 := rfl

/-- **Every `2`-primary abelian group with finite `2`-torsion has a `ℤ₂`-corank** (the structure
theorem `ZInQ.Cofinite.exists_addEquiv_of_isPPrimary` at `p = 2`). -/
theorem exists_z2Corank (M : Type) [AddCommGroup M] (hM : ZInQ.Cofinite.IsPPrimary 2 M)
    (hfin : Finite (ZInQ.Cofinite.tors M 2)) : ∃ r, Z2Corank M r := by
  obtain ⟨t, F, _, hF, ⟨e⟩⟩ := ZInQ.Cofinite.exists_addEquiv_of_isPPrimary (p := 2) M hM hfin
  exact ⟨t, F, inferInstance, hF, ⟨e⟩⟩

/-- **`corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1`**, the hypothesis of Theorem 5.3. -/
def SelmerCorankOne : Prop :=
  Z2Corank (selmerTwoPower E) 1

/-! ### Theorem 5.3 over the genuine Selmer condition -/

/-! ### The groups of `SelmerTwoPower` are the one-family groups -/

/-- **`Sha(E/ℚ)` of `SelmerTwoPower` (two families) is the one-family `Sha`.** -/
theorem sha_eq : _root_.ZInQ.Manuscript.SelmerTwoPower.sha E = sha E := by
  ext c
  rw [_root_.ZInQ.Manuscript.SelmerTwoPower.sha, sha, AddSubgroup.mem_inf,
    WeierstrassCurve.mem_shafarevichTateGroup_iff, WeierstrassCurve.mem_shafarevichTateGroup_iff,
    WeierstrassCurve.mem_shafarevichTateGroup_iff]
  exact ⟨fun h v => match v with
    | .inl p => h.1 p
    | .inr u => h.2 u, fun h => ⟨fun p => h (Sum.inl p), fun u => h (Sum.inr u)⟩⟩

/-- **`Sel_{2^n}(E/ℚ)` of `SelmerTwoPower` (two families) is the one-family `Sel_{2^n}`.** -/
theorem selmerAt_eq (n : ℕ) : _root_.ZInQ.Manuscript.SelmerTwoPower.selmerAt E n = selmerAt E n := by
  ext c
  rw [_root_.ZInQ.Manuscript.SelmerTwoPower.selmerAt, selmerAt, AddSubgroup.mem_inf,
    WeierstrassCurve.mem_selmerGroup_iff, WeierstrassCurve.mem_selmerGroup_iff,
    WeierstrassCurve.mem_selmerGroup_iff, ← AddSubgroup.mem_inf]
  rw [← _root_.ZInQ.Manuscript.SelmerTwoPower.sha, sha_eq, sha]

/-- **`Sel_{2^∞}(E/ℚ)` of `SelmerTwoPower` is the one-family `Sel_{2^∞}`.** -/
theorem selmerTwoPower_eq :
    _root_.ZInQ.Manuscript.SelmerTwoPower.selmerTwoPower E = selmerTwoPower E := by
  rw [_root_.ZInQ.Manuscript.SelmerTwoPower.selmerTwoPower, selmerTwoPower, sha_eq]

/-- **`SelmerCorankOne` of `SelmerTwoPower` is the one-family condition.** -/
theorem selmerCorankOne_iff :
    _root_.ZInQ.Manuscript.SelmerTwoPower.SelmerCorankOne E ↔ SelmerCorankOne E := by
  rw [_root_.ZInQ.Manuscript.SelmerTwoPower.SelmerCorankOne, SelmerCorankOne, selmerTwoPower_eq]

end ZInQ.Manuscript.SelmerTwoPower.Fam

import ZInQKernel.Hypotheses.PoleManuscript
import ZInQKernel.Contrib.OneProof.CofinitePrimary
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer
import ZInQKernel.Contrib.TauCeti.Algebra.GroupAction.QuotientAddGroup
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The `2`-primary Selmer group of an elliptic curve over `ℚ`, its `ℤ₂`-corank, and Theorem 5.3

Fork issue #83 asks for a genuine definition of `Sel_{2^∞}(E/ℚ)` and of its `ℤ₂`-corank, so that the
manuscript's Theorem 5.3 (`hyp:RC`, `diophantine_zq.tex` lines 1005–1011) can be stated without a
free Selmer predicate. `ZInQ.Manuscript.RestrictedConverse` (`ZInQKernel/Hypotheses/PoleManuscript.lean`)
takes the condition `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1` as a parameter; this file supplies it.

The definitions follow Silverman, *The Arithmetic of Elliptic Curves*, X.4, as formalised by Tau Ceti
(`WeierstrassCurve.selmerGroup`, `WeierstrassCurve.shafarevichTateGroup`, vendored under
`ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/`), with Galois cohomology
the continuous cohomology of `G_ℚ = Gal(ℚˢ/ℚ)` in discrete modules:

* the places of `ℚ` are `Place = HeightOneSpectrum ℤ ⊕ Unit` (the finite places `v = (p)` and the
  infinite place), with completions `Completion v` (the `v`-adic completion `ℚ_v`, which is `ℚ_p` by
  Mathlib's `Rat.HeightOneSpectrum.padicEquiv`, and `ℝ`) and a fixed `ℚ`-embedding of separable
  closures at each place (`emb`); the Selmer and Shafarevich–Tate groups do not depend on that choice
  (Tau Ceti `EmbeddingIndependence`);
* `TwoPowerCoeff E = E(ℚˢ)[2^∞]`, the `2`-primary torsion of `E(ℚˢ)` (`AddCommGroup.primaryComponent`),
  a discrete `G_ℚ`-module;
* `sha E = Sha(E/ℚ)`: Tau Ceti's Shafarevich–Tate group for the completions at all places;
* `selmerTwoPower E = Sel_{2^∞}(E/ℚ)`: the classes in `H¹(G_ℚ, E(ℚˢ)[2^∞])` whose image in
  `H¹(G_ℚ, E(ℚˢ))` lies in `Sha(E/ℚ)`, i.e. restricts to zero at every completion `ℚ_v`
  (`mem_selmerTwoPower_iff`). This is Silverman's `Sel^{(m)}` with `E[m]` replaced by `E[2^∞]`, the
  standard definition of the `p`-primary Selmer group;
* `Z2Corank M r`: the cofinitely generated `ℤ₂`-module `M` has corank `r`, i.e.
  `M ≅ (ℚ₂/ℤ₂)^r × F` with `F` finite (the structure theorem for cofinitely generated `ℤ_p`-modules,
  where the corank is the multiplicity of `ℚ_p/ℤ_p`);
* `SelmerCorankOne E : Prop := Z2Corank (selmerTwoPower E) 1`;
* `RestrictedConverseGenuine := ZInQ.Manuscript.RestrictedConverse SelmerCorankOne`: Theorem 5.3 over
  the genuine Selmer condition.

Nothing here is used by the main theorem, and nothing is assumed: this file only defines and states.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology

/-! ### The places of `ℚ` and their completions -/

open IsDedekindDomain in
/-- **The places of `ℚ`**: the finite places, the height-one primes `v = (p)` of `ℤ` (`Sum.inl v`),
and the infinite place (`Sum.inr ()`). -/
abbrev Place : Type := HeightOneSpectrum ℤ ⊕ Unit

open IsDedekindDomain in
/-- **The completion of `ℚ` at a place**: the `v`-adic completion `ℚ_v` at a finite place
`v = (p)` (it is `ℚ_p`: Mathlib's `Rat.HeightOneSpectrum.padicEquiv`), `ℝ` at the infinite place. -/
abbrev Completion : Place → Type :=
  Sum.elim (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ) (fun _ : Unit => ℝ)

instance instFieldCompletion : ∀ v, Field (Completion v) := fun v =>
  Sum.rec (motive := fun v => Field (Completion v))
    (fun v => IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v)
    (fun _ => (inferInstance : Field ℝ)) v

/-- The `ℚ`-algebra structure of the completions: at a finite place, the one of the `v`-adic
completion of the fraction field `ℚ` of `ℤ` (the one Tau Ceti's comparison of Selmer groups uses,
`IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion`; any two `ℚ`-algebra structures on a
ring agree, but only propositionally). -/
instance instAlgebraCompletion : ∀ v, Algebra ℚ (Completion v) := fun v =>
  Sum.rec (motive := fun v => Algebra ℚ (Completion v))
    (fun v => IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ v)
    (fun _ => (inferInstance : Algebra ℚ ℝ)) v

/-- A `K`-embedding of separable closures `Kˢ → Lˢ` for a field extension `L/K`, elaborated over
a general `K` so that its type carries the algebra structure `Algebra K Lˢ` induced by `L/K`, the
one Tau Ceti's Selmer and Shafarevich–Tate groups expect. -/
def sepClosureEmb (K L : Type*) [Field K] [Field L] [Algebra K L] :
    SeparableClosure K →ₐ[K] SeparableClosure L :=
  IsSepClosed.lift

/-- **A fixed `ℚ`-embedding of separable closures `ℚˢ → (ℚ_v)ˢ` at every place `v`** (its type,
`SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ_v`, is inferred from `sepClosureEmb` so that it carries
the algebra structures Tau Ceti's groups expect). The Selmer and Shafarevich–Tate groups below do
not depend on this choice (Tau Ceti `WeierstrassCurve.shafarevichTateGroup_eq_shafarevichTateGroup`,
`EmbeddingIndependence.lean`). -/
def emb (v : Place) :=
  sepClosureEmb ℚ (Completion v)

open IsDedekindDomain in
/-- `emb` at the finite places, as a family over `HeightOneSpectrum ℤ` with the completions
`v.adicCompletion ℚ` (definitionally `emb (Sum.inl v)`). -/
def embFin (v : HeightOneSpectrum ℤ) :=
  @sepClosureEmb ℚ (v.adicCompletion ℚ) _ (HeightOneSpectrum.adicCompletion.instField ℚ v)
    (HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ v)

/-- `emb` at the infinite place, as a family over `Unit` (definitionally `emb (Sum.inr i)`). -/
def embInf (_ : Unit) :=
  sepClosureEmb ℚ ℝ

/-! ### `E(ℚˢ)[2^∞]` as a discrete Galois module -/

variable (E : WeierstrassCurve ℚ)

/-- **`E(ℚˢ)[2^∞]`**, the `2`-primary torsion of `E(ℚˢ)`: the points `P` with `2^k • P = 0` for
some `k`. Its topology is the subspace topology of the discrete module `E(ℚˢ)`. -/
abbrev TwoPowerCoeff : Type := AddCommGroup.primaryComponent E.PointCoeff 2

variable {E} in
/-- The Galois action commutes with multiplication by `2^k`, so it preserves `E(ℚˢ)[2^∞]`. -/
theorem smul_mem_twoPowerCoeff (σ : AbsoluteGaloisGroup ℚ) {P : E.PointCoeff}
    (hP : P ∈ AddCommGroup.primaryComponent E.PointCoeff 2) :
    σ • P ∈ AddCommGroup.primaryComponent E.PointCoeff 2 := by
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hP
  exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by rw [← smul_comm, hk, smul_zero]⟩

instance : DistribMulAction (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) :=
  (AddCommGroup.primaryComponent E.PointCoeff 2).restrictDistribMulAction
    fun σ _ => smul_mem_twoPowerCoeff σ

/-- The Galois action on `E(ℚˢ)[2^∞]` is the action on `E(ℚˢ)`. -/
@[simp]
theorem coe_smul_twoPowerCoeff (σ : AbsoluteGaloisGroup ℚ) (P : TwoPowerCoeff E) :
    ((σ • P : TwoPowerCoeff E) : E.PointCoeff) = σ • (P : E.PointCoeff) :=
  AddSubgroup.restrictDistribMulAction_coe_smul _ (fun σ _ => smul_mem_twoPowerCoeff σ) σ P

/-- `E(ℚˢ)[2^∞]` is a discrete `G_ℚ`-module. -/
instance : ContinuousSMul (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) :=
  AddSubgroup.restrictDistribMulAction_continuousSMul _ fun σ _ => smul_mem_twoPowerCoeff σ

/-- The inclusion `E(ℚˢ)[2^∞] → E(ℚˢ)`, a `G_ℚ`-equivariant map. -/
def twoPowerCoeffIncl : TwoPowerCoeff E →+[AbsoluteGaloisGroup ℚ] E.PointCoeff where
  toFun P := P
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' σ P := coe_smul_twoPowerCoeff E σ P

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

/-- The inclusion `E(ℚˢ)[2^n] → E(ℚˢ)[2^∞]`, a `G_ℚ`-equivariant map. -/
def torsionToTwoPower (n : ℕ) :
    E.TorsionCoeff (2 ^ n) →+[AbsoluteGaloisGroup ℚ] TwoPowerCoeff E where
  toFun P := ⟨P, AddCommGroup.mem_primaryComponent.mpr
    ⟨n, (AddSubgroup.torsionBy.nsmul_iff).mp P.2⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' σ P := Subtype.ext (by simp)

/-- `E[2^n] → E[2^∞] → E` is the inclusion `E[2^n] → E`. -/
theorem twoPowerCoeffIncl_comp_torsionToTwoPower (n : ℕ) :
    (twoPowerCoeffIncl E).comp (torsionToTwoPower E n) = E.torsionCoeffIncl (2 ^ n) :=
  rfl

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

/-- `ℚ₂/ℤ₂`. -/
abbrev Q2Z2 : Type := ℚ_[2] ⧸ (PadicInt.subring 2).toAddSubgroup

/-- **`corank_{ℤ₂} M = r`** for a cofinitely generated `ℤ₂`-module `M`: `M ≅ (ℚ₂/ℤ₂)^r × F` with
`F` finite (the structure theorem for cofinitely generated `ℤ_p`-modules; the corank is the number
of copies of `ℚ_p/ℤ_p`). -/
def Z2Corank (M : Type*) [AddCommGroup M] (r : ℕ) : Prop :=
  ∃ (F : Type) (_ : AddCommGroup F) (_ : Finite F), Nonempty (M ≃+ (Fin r → Q2Z2) × F)

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

/-- **Theorem 5.3 of the 11/5 manuscript (restricted converse, `hyp:RC`), over the genuine Selmer
condition.** For every positive squarefree `ℓ ≡ 11 (mod 12)`,
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1` implies `ord_{s=1} L(E_ℓ, s) = 1`, where
`E_ℓ : y² = x(x - ℓ)(x + 3ℓ)` (`ZInQ.Manuscript.curve`) and `ord_{s=1}` is
`ZInQ.Manuscript.AnalyticRankOne`. It is `ZInQ.Manuscript.RestrictedConverse` at the predicate
`SelmerCorankOne`. -/
def RestrictedConverseGenuine : Prop :=
  ZInQ.Manuscript.RestrictedConverse SelmerCorankOne

theorem restrictedConverseGenuine_iff :
    RestrictedConverseGenuine ↔
      ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
        SelmerCorankOne (ZInQ.Manuscript.curve ℓ) → ZInQ.Manuscript.AnalyticRankOne
          (ZInQ.Manuscript.curve ℓ) :=
  Iff.rfl

end ZInQ.Manuscript.SelmerTwoPower

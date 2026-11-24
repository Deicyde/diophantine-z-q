import ZInQKernel.Contrib.PoleRC.PoleManuscript
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer
import TauCeti.Algebra.GroupAction.QuotientAddGroup
import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The `2`-primary Selmer group of an elliptic curve over `ℚ`, its `ℤ₂`-corank, and Theorem 5.3

Fork issue #83 asks for a genuine definition of `Sel_{2^∞}(E/ℚ)` and of its `ℤ₂`-corank, so that the
manuscript's Theorem 5.3 (`hyp:RC`, `diophantine_zq.tex` lines 1005–1011) can be stated without a
free Selmer predicate. `ZInQ.Manuscript.RestrictedConverse` (`ZInQKernel/Contrib/PoleRC/PoleManuscript.lean`)
takes the condition `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1` as a parameter; this file supplies it.

The definitions follow Silverman, *The Arithmetic of Elliptic Curves*, X.4, as formalised by Tau Ceti
(`WeierstrassCurve.selmerGroup`, `WeierstrassCurve.shafarevichTateGroup`, vendored under
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/`), with Galois cohomology
the continuous cohomology of `G_ℚ = Gal(ℚˢ/ℚ)` in discrete modules:

* the places of `ℚ` are the primes `p` (completion `ℚ_p`) and the infinite place (completion `ℝ`),
  with a fixed `ℚ`-embedding of separable closures at each place (`embFin`, `embInf`); the Selmer and
  Shafarevich–Tate groups do not depend on that choice (Tau Ceti `EmbeddingIndependence`);
* `TwoPowerCoeff E = E(ℚˢ)[2^∞]`, the `2`-primary torsion of `E(ℚˢ)` (`AddCommGroup.primaryComponent`),
  a discrete `G_ℚ`-module;
* `sha E = Sha(E/ℚ)`: Tau Ceti's Shafarevich–Tate group at the finite places meet the one at the
  infinite place, i.e. local triviality at every place of `ℚ`;
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

Nothing is assumed here: this file only defines and states. `ZInQ.OneProof.frozenTarget` takes
`RestrictedConverseGenuine` from this file as its hypothesis `hRC`.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology

/-! ### The places of `ℚ` and their completions -/

/-- Every `p : Nat.Primes` is prime, so `ℚ_p` is a field. -/
instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The completion `ℚ_p` of `ℚ` at the finite place `p`. -/
abbrev QpCompletion (p : Nat.Primes) : Type := ℚ_[(p : ℕ)]

/-- The completion `ℝ` of `ℚ` at its infinite place (indexed by `Unit`). -/
abbrev RealCompletion (_ : Unit) : Type := ℝ

/-- A `K`-embedding of separable closures `Kˢ → Lˢ` for a field extension `L/K`, elaborated over
a general `K` so that its type carries the algebra structure `Algebra K Lˢ` induced by `L/K`, the
one Tau Ceti's Selmer and Shafarevich–Tate groups expect. -/
def sepClosureEmb (K L : Type*) [Field K] [Field L] [Algebra K L] :
    SeparableClosure K →ₐ[K] SeparableClosure L :=
  IsSepClosed.lift

/-- A fixed `ℚ`-embedding of separable closures `ℚˢ → (ℚ_p)ˢ` at every finite place `p` (its type,
`SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ_p`, is inferred from `sepClosureEmb` so that it carries
the algebra structures Tau Ceti's groups expect). The Selmer
and Shafarevich–Tate groups below do not depend on this choice (Tau Ceti
`WeierstrassCurve.shafarevichTateGroup_eq_shafarevichTateGroup`, `EmbeddingIndependence.lean`). -/
def embFin (p : Nat.Primes) :=
  sepClosureEmb ℚ (QpCompletion p)

/-- A fixed `ℚ`-embedding of separable closures `ℚˢ → ℝˢ` at the infinite place (indexed by
`Unit`). -/
def embInf (u : Unit) :=
  sepClosureEmb ℚ (RealCompletion u)

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

/-- **`Sha(E/ℚ)`**: the classes in `H¹(G_ℚ, E(ℚˢ))` that restrict to zero at every place of `ℚ`,
as the meet of Tau Ceti's Shafarevich–Tate groups for the family of completions `ℚ_p` at the finite
places and for `ℝ` at the infinite place. -/
def sha : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff) :=
  E.shafarevichTateGroup embFin ⊓ E.shafarevichTateGroup embInf

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
    c ∈ selmerTwoPower E ↔
      (∀ p, E.pointRes (embFin p)
        (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
          continuous_of_discreteTopology c) = 0) ∧
      E.pointRes (embInf ())
        (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
          continuous_of_discreteTopology c) = 0 := by
  simp only [selmerTwoPower, sha, AddSubgroup.mem_comap, AddSubgroup.mem_inf]
  rw [WeierstrassCurve.mem_shafarevichTateGroup_iff, WeierstrassCurve.mem_shafarevichTateGroup_iff]
  exact and_congr Iff.rfl ⟨fun h => h (), fun h _ => h⟩

/-! ### The `2^n`-Selmer groups and the maps `Sel_{2^n} → Sel_{2^∞}` -/

/-- **`Sel_{2^n}(E/ℚ)`**: Tau Ceti's `2^n`-Selmer group with the local conditions at every place of
`ℚ` (the meet of the groups for the finite places and for the infinite place). -/
def selmerAt (n : ℕ) : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))) :=
  E.selmerGroup embFin (2 ^ n) ⊓ E.selmerGroup embInf (2 ^ n)

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
  obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.mp hc
  rw [WeierstrassCurve.mem_selmerGroup_iff] at h1 h2
  rw [selmerTwoPower, AddSubgroup.mem_comap, hcomp, sha]
  exact AddSubgroup.mem_inf.mpr ⟨h1, h2⟩

/-- **The map `Sel_{2^n}(E/ℚ) → Sel_{2^∞}(E/ℚ)`** induced by `E[2^n] ⊆ E[2^∞]`. -/
def selmerAtToTwoPower (n : ℕ) : selmerAt E n →+ selmerTwoPower E where
  toFun c := ⟨explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
      (torsionToTwoPower E n) continuous_of_discreteTopology c,
    explicitCoeff1_torsionToTwoPower_mem E c.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-! ### The `ℤ₂`-corank -/

/-- `ℚ₂/ℤ₂`. -/
abbrev Q2Z2 : Type := ℚ_[2] ⧸ (PadicInt.subring 2).toAddSubgroup

/-- **`corank_{ℤ₂} M = r`** for a cofinitely generated `ℤ₂`-module `M`: `M ≅ (ℚ₂/ℤ₂)^r × F` with
`F` finite (the structure theorem for cofinitely generated `ℤ_p`-modules; the corank is the number
of copies of `ℚ_p/ℤ_p`). -/
def Z2Corank (M : Type*) [AddCommGroup M] (r : ℕ) : Prop :=
  ∃ (F : Type) (_ : AddCommGroup F) (_ : Finite F), Nonempty (M ≃+ (Fin r → Q2Z2) × F)

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

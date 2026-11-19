import ZInQKernel.Contrib.OneProof.RC.Wiring.UniformSwitch
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSwitch
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois

/-!
**Theorem 5.3, Lane RC0 round 4: the height-one leaf on batch 3's genuine switching data**

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity, including quadratic
specializations", tex 4976–5195 (with the unknown base, tex 5196–5200).

**The defect.** `PrimRegularityInputsS` (`Wiring/UniformSwitch.lean`) asks, at every height-one prime
`𝔭 ≠ (2)`, for `HeightOneSwitchDataS` starting at `u`. Its stages are free two-term models tied to
the actual configuration only through the starting coordinate, so a one-stage model of fiber
dimension one satisfies it: `regularityInputsS_iff : RegularityInputsS u ↔ u ∈ Λ[1/2]`.

**The new leaf.** `RegularityInputsG u` asks, at every height-one prime `𝔭 ≠ (2)`, for

* a configuration family `Φ` of the switching argument over `R = Λ_𝔭` and its residue field `k`
  (batch 3's `SwitchFamily`: configurations, the switch successor `c ↦ next c p`, the actual
  configuration, the fiber Selmer data of each configuration, the actual class and paired
  functional, the moving variable), which is **genuine at `𝔭`** (`IsGenuineFamilyAt`):
  - every fiber is lane RC26's genuine Selmer data `galoisSelData K S k M Δ` over the genuine
    `G_{K,S}` and `G_{K_v}` (continuous cochains, (4.3) at tex 3455–3463), for a finite support `S`
    and local conditions that are subcomplexes of the local cochains (`IsGaloisSelData`);
  - the moving variable of the family is the genuine `t = X ∈ Λ`, so "quadratic" is the genuine
    condition `t̄ (t̄ + 2) = 0` in `k` (tex 5004–5008), i.e. `𝔭 = (t)` or `(t + 2)`;
* batch 3's `GenuineSwitchData Φ ι ρ u` over that family: each stage is a homotopy-equivalent
  two-term model of its configuration's genuine fiber, the starting stage carries the actual class,
  the actual functional and the coordinate `u`, and the switches follow the configuration sequence.

`PrimRegularityInputsG D` replaces `PrimRegularityInputsS D`: at every address of every final
family, `u` with `IsTExpansion u (D.uPrim F x)` and `RegularityInputsG u`.

PROVED here: `RegularityInputsG.mem_lambdaHalf` (batch 3's `regular_of_genuineSwitchData` at every
height-one prime, then the intersection formula `mem_range_lambdaHalf_iff_forall_height_one`),
`heightOneTarget_of_inputsG`, `primRegularityInputsS_of_G`, `primRegularityInputs_of_G`.

**Caveat.** The configuration family is existential and only required to be some genuine Galois
Selmer data with `t = X`. With one genuine complex of the homotopy type of `[k --0--> k]` at each
`𝔭` (true, not formalized), the leaf is equivalent to `∀ F x, InLamHalf (D.uPrim F x)`, i.e.
Elliot's regularity assertion (ELLIOT). Over the address's own genuine complexes no switch step can
be formed (`fG`: `C¹_cont` is infinite-dimensional), so the address's family witnesses the leaf only
when `s(𝔭) = 1`. UNCLEAR/DEPARTURE of this leaf: batch 3's `GenuineSwitchData.primitive` requires
the actual class to be primitive, which the text does not supply. `Leaves.lean` uses instead
`RegularityInputsGPK` (`GenuineSwitchPK.lean`): the actual classes are only asked to be nonzero, the
text's primitive kernel vector is PROVED from them over the DVR `Λ_𝔭`, and this leaf implies it
(`RegularityInputsG.toPK`).

The `Ties` section records structural facts of the witnesses (`RegularityInputsG.fiberDim_forced`,
`RegularityInputsG.oneStage_forces`, `isEmpty_genuineSwitchData_of_h1_eq_zero`); they constrain the
witnesses over a fixed family, not the existential family. The GLUE inputs inside the switch steps
are batch 3's `GenuineMixedStep`, `GenuineNonquadStep`, `GenuineSingleStep` (duality, detection,
detecting primes, the side involutions, `CoordStep`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module NumberField IsDedekindDomain
  CategoryTheory

open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily GenuineSwitchData Reach)
open ZInQ.Manuscript.RC.SelmerComplex (GKS galoisSelData GaloisLocalConditions)

attribute [local instance] Nat.fact_prime_two

/-! **Genuine Galois Selmer data** -/

/-- **Selmer data that are lane RC26's genuine Galois Selmer data** ((4.3), tex 3455–3463; Nekovář
6.1.2): `D = galoisSelData K S k M Δ` for a number field `K`, a finite set `S` of finite primes of
`K`, a topological `k[G_{K,S}]`-module `M` and local conditions `Δ` at the places of `S` whose maps
`U_v → C^•_cont(G_{K_v}, M)` are injective in every degree (the local conditions of the text are
subcomplexes of the local cochains: unramified, Kummer, the derivative conditions
`D⁰ ⊕ F[−1]`, `D⁰ ⊕ S[−1]`, full and strict). Kind: definition. -/
def IsGaloisSelData {k : Type} [CommRing k] (D : SelData k) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (M : Type) (_ : AddCommGroup M) (_ : Module k M) (_ : DistribMulAction (GKS K S) M)
    (_ : SMulCommClass (GKS K S) k M) (_ : TopologicalSpace M) (_ : ContinuousAdd M)
    (_ : ContinuousConstSMul k M) (_ : ContinuousSMul (GKS K S) M)
    (Δ : GaloisLocalConditions K S k M),
    S.Finite ∧ (∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) ∧
      D = galoisSelData K S k M Δ

/-! **Genuine configuration families at a height-one prime** -/

section Family

variable (P : Ideal Lambda) [P.IsPrime]

/-- The residue field `k = Frac(Λ/𝔭)` of `Λ_𝔭`. -/
abbrev ResAt : Type := IsLocalRing.ResidueField (Localization.AtPrime P)

/-- The residue map `ρ : Λ_𝔭 → k`. -/
abbrev resAt : Localization.AtPrime P →+* ResAt P := IsLocalRing.residue (Localization.AtPrime P)

/-- **A configuration family of the switching argument at `𝔭` that is genuine** (tex 4976–4996,
5004–5008): every configuration's fiber `C ⊗_R k` is genuine Galois Selmer data over `k`
(`IsGaloisSelData`), and the moving variable of the family is the genuine `t = X ∈ Λ`, so that
"quadratic" (`t̄ (t̄ + 2) = 0` in `k`, batch 3's `SwitchFamily.quadratic`) is the genuine condition
on `𝔭`. That `Φ` is the actual primitive scalar Selmer complex of the address and its derivative
switches is the GLUE identification of the leaf (see `RegularityInputsG`). Kind: definition. -/
def IsGenuineFamilyAt (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)) : Prop :=
  (∀ c, IsGaloisSelData (Φ.fibre c)) ∧
    Φ.t = algebraMap Lambda (Localization.AtPrime P) PowerSeries.X

end Family

/-! **The new height-one leaf** -/

/-- **The height-one regularity inputs on batch 3's genuine switching data** (replaces
`RegularityInputsS u`; tex 4976–5200). Either `u = 0` ("If its actual generic class is zero, its
coordinate is zero", tex 5196–5197; ELLIOT; owner RC15 / RC16), or at every height-one prime
`𝔭 ≠ (2)` of `Λ` (tex; kind; owner):

1. a configuration family `Φ` over `R = Λ_𝔭` and `k = Frac(Λ/𝔭)`, genuine at `𝔭`
   (`IsGenuineFamilyAt`: lane RC26's `galoisSelData` fibers with finite support and subcomplex
   conditions, the genuine moving variable); "use the actual primitive scalar Selmer complex over
   `R`", the derivative switches retaining `D⁰` (tex 4976–4984, 5055–5072); GLUE identification of
   `Φ` with the address's actual Selmer complex and its switches; owners RC26 (genuine complexes),
   batch 3 (switch configurations), RC15 (actual class and functional);
2. batch 3's `GenuineSwitchData Φ ι ρ u` with `ι : Λ_𝔭 → Frac Λ`, `ρ` the residue map: the
   homotopy equivalences of the genuine fibers with the stages' two-term fibers (tex 4976–4996;
   GLUE minimal models), the actual class and functional at the start and the coordinate `u`
   (tex 4986–4992, 5159–5189; definition + GLUE), the sign involutions (tex 5009–5054; GLUE), the
   primitive vectors (tex 4986–4990; ELLIOT), and the switches along the configuration sequence with
   their GLUE step data (tex 4997–5003, 5055–5153; owners RC16 `Switch`/`QuadraticCase`, batch 3
   SwitchInputs / SignSplitting / ExactSequences).

Kind: definition. -/
def RegularityInputsG (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      Nonempty (GenuineSwitchData Φ (UniformSwitch.toFracAt P) (resAt P) u)

/-- **`u ∈ Λ[1/2]` from the new inputs**: batch 3's `regular_of_genuineSwitchData` gives
`u ∈ ι(Λ_𝔭)` at every height-one prime `𝔭 ≠ (2)`, and the normal-domain intersection formula
(`mem_range_lambdaHalf_iff_forall_height_one`, tex 5190–5194) gives `u ∈ Λ[1/2]`. Kind: PROVED from
the inputs. -/
theorem RegularityInputsG.mem_lambdaHalf {u : FractionRing Lambda} (h : RegularityInputsG u) :
    u ∈ lambdaHalfToFrac.range := by
  rw [mem_range_lambdaHalf_iff_forall_height_one]
  intro P _ hP hne
  rcases h with rfl | h
  · exact Subalgebra.zero_mem _
  · obtain ⟨Φ, -, ⟨G⟩⟩ := h P hP hne
    obtain ⟨a, ha⟩ := SwitchInputs.regular_of_genuineSwitchData (ResAt P)
      (Localization.AtPrime P) (FractionRing Lambda) Φ (UniformSwitch.toFracAt P) (resAt P) u
      (UniformSwitch.toFracAt_injective P)
      (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) G
    rw [← ha]
    exact ⟨a, rfl⟩

/-- `RegularityInputsG u → RegularityInputsS u` (through `u ∈ Λ[1/2]` and
`regularityInputsS_iff`). Kind: PROVED. -/
theorem RegularityInputsG.toS {u : FractionRing Lambda} (h : RegularityInputsG u) :
    RegularityInputsS u :=
  (regularityInputsS_iff u).mpr h.mem_lambdaHalf

section HeightOneTarget

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The height-one leaf on batch 3's genuine switching data** (replaces `PrimRegularityInputsS D`;
tex 4976–5200, at the ring instances `(h_x, k)` of the final field; at `x = 0` the unknown
full-corank-one base, tex 5196–5200). For every final family `F` (any `C_o, C_e`) and every address
`x` there is `u ∈ Frac Λ` with (tex; kind; owner):

1. `IsTExpansion u (D.uPrim F x)` (tex 3877–3892, 3895–3985; GLUE interface identification; owner
   RC0, with RC15);
2. `RegularityInputsG u`: `u = 0` (tex 5196–5197; ELLIOT; owner RC15 / RC16) or, at every
   height-one prime `𝔭 ≠ (2)`, a configuration family genuine at `𝔭` (lane RC26's Galois fibers,
   the genuine moving variable) and batch 3's `GenuineSwitchData` over it starting at `u` (fields
   and owners as listed at `RegularityInputsG`).

PROVED from it (not inputs): `pos` from primitivity, `terminal`, `s₊ + s₋ = s`, the nonquadratic
`U = F`, the descent (batch 3's `regular_of_genuineSwitchData`, through
`SelmerModelSwitchData.toSelmerSwitchData`), the intersection formula and the transfer to
`ℚ₂[[t]]`. Kind: definition. -/
def PrimRegularityInputsG : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsG u

/-- **`u_{prim,x} ∈ Λ[1/2]`** at every address of every final family, from the new leaf.
Kind: PROVED from the inputs. -/
theorem primLambdaHalf_of_inputsG (h : PrimRegularityInputsG D) :
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      InLamHalf (D.uPrim F x) := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact inLamHalf_of_isTExpansion hT hreg.mem_lambdaHalf

/-- **`RCSteps.height_one`** (tex 4909–5205, 5703–5704) from the new leaf and (4.7).
Kind: PROVED from the inputs. -/
theorem heightOneTarget_of_inputsG (h : PrimRegularityInputsG D)
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D :=
  heightOneTarget_of_prim D (primLambdaHalf_of_inputsG D h) h47

/-- **Conversion to the round-3 leaf** `PrimRegularityInputsS D`. Kind: PROVED. -/
theorem primRegularityInputsS_of_G (h : PrimRegularityInputsG D) : PrimRegularityInputsS D :=
  (primRegularityInputsS_iff D).mpr (primLambdaHalf_of_inputsG D h)

/-- **Conversion to the old leaf** `PrimRegularityInputs D` (the form consumed by lane RC25's
base-zero assembly). Kind: PROVED. -/
theorem primRegularityInputs_of_G (h : PrimRegularityInputsG D) : PrimRegularityInputs D :=
  primRegularityInputs_of_S D (primRegularityInputsS_of_G D h)

end HeightOneTarget

/-! **Ties to the genuine objects** -/

section Ties

variable {k A F : Type} [Field k] [CommRing A] [Field F]

/-- **The actual genuine fiber has nonzero `H¹`**: a genuine switching datum over `Φ` forces
`dim_k H¹(selCx (Φ.fibre actual)) ≥ 1` (its stage at the actual configuration has a primitive
cycle, so fiber dimension `≥ 1`, and the fiber dimension is the genuine `dim_k H¹`, batch 3's
`fiberDim_eq`). Kind: PROVED. -/
theorem genuineSwitchData_one_le_h1 {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}
    (G : GenuineSwitchData Φ ι ρ u) :
    1 ≤ finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) := by
  rw [← G.fiberDim_eq]
  exact UniformSwitch.TwoTermStage.one_le_fiberDim ρ _ (G.primitive Φ.actual Reach.start)

/-- **No datum over a family whose actual fiber has `H¹ = 0`**, whatever the coordinate `u`. Over a
fixed family the existence of a datum is therefore a condition on the genuine fiber, not on `u`.
Kind: PROVED. -/
theorem isEmpty_genuineSwitchData_of_h1_eq_zero {Φ : SwitchFamily k A} {ι : A →+* F}
    {ρ : A →+* k} (u : F) (h0 : finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 0) :
    IsEmpty (GenuineSwitchData Φ ι ρ u) :=
  ⟨fun G => by have := genuineSwitchData_one_le_h1 G; omega⟩

/-- **The fiber dimensions in every witness of the new leaf are the genuine ones**: at a height-one
prime `𝔭 ≠ (2)` (and `u ≠ 0`), the family of the witness is genuine at `𝔭`, every stage's fiber
dimension is `dim_k H¹` of the genuine Galois Selmer complex of its configuration, and the actual
one is at least one. Kind: PROVED. -/
theorem RegularityInputsG.fiberDim_forced {u : FractionRing Lambda} (h : RegularityInputsG u)
    (hu : u ≠ 0) (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ∃ G : GenuineSwitchData Φ (UniformSwitch.toFracAt P) (resAt P) u,
        (∀ c, (G.stage c).fiberDim (resAt P) =
          finrank (ResAt P) ((selCx (Φ.fibre c)).toCC.homology 1)) ∧
        1 ≤ finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) := by
  rcases h with h0 | h
  · exact absurd h0 hu
  · obtain ⟨Φ, hΦ, ⟨G⟩⟩ := h P hP hne
    exact ⟨Φ, hΦ, G, G.fiberDim_eq, genuineSwitchData_one_le_h1 G⟩

/-- **The one-stage bypass forces the genuine fiber**: in a witness of the new leaf whose starting
stage has fiber dimension one (no switch demanded), the genuine Galois Selmer complex of the actual
configuration has `dim_k H¹ = 1` (batch 3's `collapse_forces_fibre`). Kind: PROVED. -/
theorem RegularityInputsG.oneStage_forces (P : Ideal Lambda) [P.IsPrime] {u : FractionRing Lambda}
    {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    (G : GenuineSwitchData Φ (UniformSwitch.toFracAt P) (resAt P) u)
    (h1 : (G.stage Φ.actual).fiberDim (resAt P) = 1) :
    finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 1 :=
  SwitchInputs.collapse_forces_fibre (ResAt P) (Localization.AtPrime P) (FractionRing Lambda) Φ
    _ _ u G h1

end Ties

end ZInQ.Manuscript.RC.Wiring

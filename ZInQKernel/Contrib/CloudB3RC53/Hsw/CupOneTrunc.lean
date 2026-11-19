import ZInQKernel.Contrib.CloudB3RC53.Hsw.CupOneReverse

/-!
# RC53 cup-one: the `τ≥2`-truncated pairing data

The cup-one datum of `CupOneReverse.lean` is pushed into the canonical truncation `τ≥2 E_L`. Then
the `hsw` descent runs on truncated Selmer pairing data (`SelPairDataTrunc`, as in
`switchAdjunction_of_trunc`).

* `PairCupOne`: a cup-one datum for a self-pairing of complexes `P : A × A → T` in degrees
  `(1, 1)`.
* `PairCupOne.trunc`: its image under `T → τ≥2 T`, a cup-one datum for `truncPair P`.
* `CupOneDatum.ofPair`, `CupOneDatum.ofTrunc`: cup-one data for `SelPairData` and for
  `SelPairDataTrunc.toSelPairData`, whenever the local cup product agrees in degrees `(1, 1)` with
  a pairing carrying a cup-one datum.
* `exists_residuePairing_trunc_of_cupOne`: the descent for truncated data. Assume a cup-one
  datum and a strict condition vanishing in degree two. Then the truncated `hsw` left-hand side
  `tr0((0, s, −ι u) ∪ (0, t, 0))` is `P(eR[g t], eR[g u])`.
* `localPairCupOne`: the genuine cup-one datum of `⊕_v C^•_cont(G_v, −)` for a `c`-symmetric
  equivariant self-pairing. Any truncated data whose local cup product is `localSumPair` plug in
  with `hP := fun _ _ => rfl`.
* Non-vacuity: `exGenuine_trunc_residuePairing`, all hypotheses at once on the example
  genuine switch (via `SelPairData.toTrunc`).

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.SwitchInputs

section Pair

variable {k : Type} [Field k]

/-- **A cup-one datum for a self-pairing of complexes** `P : A × A → T` in degrees `(1, 1)`:
`d(a ∪₁ b) = −a ∪ b − c • (b ∪ a) + X₂(da, b)` for every `1`-cocycle `b`. -/
structure PairCupOne {A T : GCx k} (P : GPair A A T) (c : k) where
  /-- The cup-one product `A¹ × A¹ → T¹`. -/
  C11 : A.X 1 →ₗ[k] A.X 1 →ₗ[k] T.X 1
  /-- The correction term `A² × A¹ → T²`. -/
  X2 : A.X 2 →ₗ[k] A.X 1 →ₗ[k] T.X 2
  /-- The coboundary formula. -/
  formula : ∀ a b : A.X 1, A.d 1 2 rfl b = 0 →
    T.d 1 2 rfl (C11 a b) = -P.P 1 1 2 rfl a b - c • P.P 1 1 2 rfl b a + X2 (A.d 1 2 rfl a) b

/-- **Pushing a cup-one datum into `τ≥2`** (`PROVED`): compose with the projections
`T → τ≥2 T`. -/
def PairCupOne.trunc {A T : GCx k} {P : GPair A A T} {c : k} (Cd : PairCupOne P c) :
    PairCupOne (truncPair P) c where
  C11 := Cd.C11.compr₂ (truncSub T 1).mkQ
  X2 := Cd.X2.compr₂ (truncSub T 2).mkQ
  formula a b hb := by
    change (truncSub T 2).mkQ (T.d 1 2 rfl (Cd.C11 a b)) =
      -(truncSub T 2).mkQ (P.P 1 1 2 rfl a b) - c • (truncSub T 2).mkQ (P.P 1 1 2 rfl b a) +
        (truncSub T 2).mkQ (Cd.X2 (A.d 1 2 rfl a) b)
    rw [Cd.formula a b hb, map_add, map_sub, map_neg, map_smul]

variable (D : SelData k) (Ustr : GCx k) (f : GHom Ustr D.U)

/-- A cup-one datum for `Q` from one for a pairing that agrees with `Q.cupL` in degrees
`(1, 1)`. -/
def CupOneDatum.ofPair (Q : SelPairData (restrictData D f) D) {P : GPair D.L D.L Q.EL} {c : k}
    (Cd : PairCupOne P c) (hP : ∀ a b, Q.cupL.P 1 1 2 rfl a b = P.P 1 1 2 rfl a b) :
    CupOneDatum D Ustr f Q c where
  C11 := Cd.C11
  X2 := Cd.X2
  formula a b hb := by
    rw [hP a b, hP b a]
    exact Cd.formula a b hb

/-- **The cup-one datum of `τ≥2`-truncated pairing data** (`PROVED`). Suppose the local cup
product of `Q : SelPairDataTrunc` agrees in degrees `(1, 1)` with a pairing `P` that has a cup-one
datum. Then `Q.toSelPairData` (local target `τ≥2 E_L`) has a cup-one datum. -/
def CupOneDatum.ofTrunc (Q : SelPairDataTrunc (restrictData D f) D) {P : GPair D.L D.L Q.EL}
    {c : k} (Cd : PairCupOne P c) (hP : ∀ a b, Q.cupL.P 1 1 2 rfl a b = P.P 1 1 2 rfl a b) :
    CupOneDatum D Ustr f Q.toSelPairData c :=
  CupOneDatum.ofPair D Ustr f Q.toSelPairData Cd.trunc fun a b => by
    change (truncSub Q.EL 2).mkQ (Q.cupL.P 1 1 2 rfl a b) =
      (truncSub Q.EL 2).mkQ (P.P 1 1 2 rfl a b)
    rw [hP]

/-- **The `hsw` descent for `τ≥2`-truncated data from a cup-one datum** (`PROVED`). Assume the
switch exactness data, a trace `tr0` killing cone coboundaries, a cup-one datum for the local cup
product, and a strict condition vanishing in degree two. Then the left-hand side of the truncated
`hsw` (`switchAdjunction_of_trunc`) is a residue pairing. -/
theorem exists_residuePairing_trunc_of_cupOne (R : QuasiRelaxedLocalization k) (Ustr : GCx k)
    (f : GHom Ustr R.D.U) (Q : SelPairDataTrunc (restrictData R.D f) R.D)
    (tr0 : (coneCx Q.resE).X 3 →ₗ[k] k) (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    {P : GPair R.D.L R.D.L Q.EL} {c : k} (Cd : PairCupOne P c)
    (hP : ∀ a b, Q.cupL.P 1 1 2 rfl a b = P.P 1 1 2 rfl a b) (h2 : ∀ x : Ustr.X 2, x = 0) :
    ∃ P' : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)),
      ∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
        (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
        (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
        tr0 (selCupFunT Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
            ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
          P' (R.eR (cls1 R.Wrel ct)) (R.eR (cls1 R.Wrel cu)) :=
  exists_residuePairing_trunc R Ustr f Q tr0 htr0 hfg hf hg hex
    (strictOrth_of_reverseIsotropy R.D Ustr f Q.toSelPairData (Q.trT tr0 htr0)
      (Q.trT_kills tr0 htr0)
      (reverseIsotropy_of_cupOne R.D Ustr f Q.toSelPairData c
        (CupOneDatum.ofTrunc R.D Ustr f Q Cd hP) h2))

end Pair

/-! ### The genuine local cup product -/

section Local

variable {k : Type} [Field k] (GS : Type) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} (Gv : ι → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {M T : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GS) (a b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M × M => β x.1 x.2)

/-- **The cup-one datum of the genuine local cup product** `⊕_v C^•_cont(G_v, −)` (`PROVED`), for
a `c`-symmetric equivariant self-pairing. Push it into `τ≥2` with `PairCupOne.trunc`. -/
def localPairCupOne (c : k) (hc : ∀ x y, β x y = c • β y x) :
    PairCupOne (localSumPair k GS Gv loc β hβ hβc) c where
  C11 := sumCupOne GS Gv loc β hβc
  X2 := sumX2 GS Gv loc β hβc
  formula a b hb := sumCupOne_formula GS Gv loc β hβc hβ c hc a b hb

end Local

/-! ### Non-vacuity -/

section NonVacuity

variable {k : Type} [Field k] (K : Type) [Field K] [NumberField K]
  (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- The truncation of the example genuine pairing data. -/
abbrev exQT : SelPairDataTrunc (restrictData (exGenuineSwitch (k := k) K q).toQuasi.D
    (piMap (exGenuineSwitch (k := k) K q).φ)) (exGenuineSwitch (k := k) K q).toQuasi.D :=
  SelPairData.toTrunc (galoisPairData K {q} k _ _ _ _ (exIsotropy (k := k) K q))

/-- The genuine cup-one datum of the example (zero pairing, `c = 1`). -/
abbrev exCupOne := localPairCupOne (k := k) (GKS K {q}) (fun v : Places K {q} => Gloc K v.1)
  (fun v => locMap K {q} v.1)
  (0 : TrivMod (GKS K {q}) PUnit →ₗ[k] TrivMod (GKS K {q}) PUnit →ₗ[k] TrivMod (GKS K {q}) PUnit)
  (fun _ _ _ => rfl) (continuous_pairing _) (1 : k) (fun _ _ => rfl)

/-- **End-to-end non-vacuity of the truncated descent** (`PROVED`). Take the example genuine switch
with the zero pairing and zero isotropy data, truncated with `SelPairData.toTrunc`. All
hypotheses of `exists_residuePairing_trunc_of_cupOne` then hold, with the genuine cup-one datum
`localPairCupOne`. -/
theorem exGenuine_trunc_residuePairing :
    ∃ P' : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)),
      ∀ (t u : (exGenuineSwitch (k := k) K q).toQuasi.D.U.X 1)
        (s : (piCx (exGenuineSwitch (k := k) K q).US).X 2)
        (_ht : (exGenuineSwitch (k := k) K q).toQuasi.D.U.d 1 2 rfl t = 0)
        (_hu : (exGenuineSwitch (k := k) K q).toQuasi.D.U.d 1 2 rfl u =
          (piMap (exGenuineSwitch (k := k) K q).φ).f 2 2 rfl s)
        (ct cu : LinearMap.ker ((exGenuineSwitch (k := k) K q).toQuasi.Wrel.d 1 2 rfl))
        (_hct : ct.1 = (exGenuineSwitch (k := k) K q).toQuasi.gR.f 1 1 rfl t)
        (_hcu : cu.1 = (exGenuineSwitch (k := k) K q).toQuasi.gR.f 1 1 rfl u),
        (0 : (coneCx (exQT (k := k) K q).resE).X 3 →ₗ[k] k)
          (selCupFunT (exQT (k := k) K q) 2 1 3 rfl
            ((0 : (exGenuineSwitch (k := k) K q).toQuasi.D.G.X 2), s,
              -((exGenuineSwitch (k := k) K q).toQuasi.D.ι.f 1 (2 - 1) (by omega) u))
            ((0 : (exGenuineSwitch (k := k) K q).toQuasi.D.G.X 1), t,
              (0 : (exGenuineSwitch (k := k) K q).toQuasi.D.L.X (1 - 1)))) =
          P' ((exGenuineSwitch (k := k) K q).toQuasi.eR
              (cls1 (exGenuineSwitch (k := k) K q).toQuasi.Wrel ct))
            ((exGenuineSwitch (k := k) K q).toQuasi.eR
              (cls1 (exGenuineSwitch (k := k) K q).toQuasi.Wrel cu)) :=
  exists_residuePairing_trunc_of_cupOne (exGenuineSwitch K q).toQuasi _ _ (exQT K q) 0
    (fun _ => rfl) (exGenuineSwitch K q).hfg (exGenuineSwitch K q).φ_inj
    (exGenuineSwitch K q).g_surj (exGenuineSwitch K q).ex (exCupOne K q) (fun _ _ => rfl)
    (fun x => funext fun v => exGenuineSwitch_US2 K q v (x v))

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.Hsw

import ZInQKernel.Contrib.TYZGenus.RingClassBridge

/-!
# cm-bridge: cm-numeric's class-7 file rewired to ring class field theory

Task cm-bridge (2026-11-13). Report: `docs/research/cm-bridge.md`; log: `scratch/cm-bridge/log.md`.

§0–§9 are a verbatim copy of cm-numeric's `scratch/cm-numeric/Class7.lean` (namespace renamed
`CMNumeric → CMBridge`; every `Prop` unchanged, checked by `rfl` in §0 against cm-points'
`Package`). §10 onwards are new: they discharge, from ring-class's theorems
(`ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean`, `RingClassGenus.lean`), the leaves
`IInH4`, `HprimeNormal` (ring-class), `IInHprime` (`Lni_le_Hprimebar`), `CMFieldOfDefinition7`
(from the general `CM.CMFieldOfDefinition ringClassFieldD`, `ringClassFieldD_neg`), and state the
main theorem with only the remaining leaves. §11 proves cm-numeric's leaf `GenusFieldLeLni` (genus
field of `ℚ(√−e)`, `e ≡ 7 (mod 8)`, inside `L_e(i)`; Bauer + genus characters). §12 reduces TYZ Lemma
3.21(4) (`Lemma321Seven`) to TYZ Theorem 3.6(3) (`TYZThm36Seven`, a leaf about the pinned class-7 CM
point) and the glue `BetaOnGenus7`; §13 proves `BetaOnGenus7` (the genus field is `K_n(√p* : p ∣ n)`,
the Artin symbols act on `√p*` by the genus characters, `N𝔭₂ = 2`). Final theorem:
`tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven`.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option maxRecDepth 8000

namespace ZInQ.Contrib.TYZGenus.CMBridge

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b

/-! ## §0. Verbatim copies of the Props of this task (checked equal by `rfl`) -/

namespace Copy

/-- Verbatim copy of `CM.CMFieldOfDefinition`. -/
def CMFieldOfDefinition (H : ℤ → IntermediateField ℚ Qbar) : Prop :=
  ∀ (D : ℤ) (Q : HeegnerForm 32 D), heegnerPt Q ∈ ptsOver (H D)

/-- Verbatim copy of `Package.TYZSigmaFixesZn`. -/
def TYZSigmaFixesZn : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → galPt ρ (tyzZn n) = tyzZn n

/-- Verbatim copy of `Package.Lemma318Literal`. -/
def Lemma318Literal (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ P ∈ ptsOver (Hn n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0

/-- Verbatim copy of `Package.GenusPtsDefined`. -/
def GenusPtsDefined (Hn : ℕ → IntermediateField ℚ Qbar) (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ ptsOver (Hn n)

/-- Verbatim copy of `Package.Thm35First`. -/
def Thm35First (ℓ : ℕ → ℤ) (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧ (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n))

/-- Verbatim copy of `Package.Lemma321`. -/
def Lemma321 (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 → galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG 1)

/-- Verbatim copy of `Package.GenusPointLeafCM`. -/
def GenusPointLeafCM (ℓ : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ (Φ : ℕ → Finset GalQ) (Z7 : ℕ → PtA),
    (∀ e ∈ n.divisors, e % 8 = 7 → Z7 e ∈ ptsOver (Lni e)) ∧
    (∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧
      (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε (tyzGenusPt Φ Z7) n))) ∧
    (∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 → ∃ k : ℤ,
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 →
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG 1))

theorem cmFieldOfDefinition_eq : CMFieldOfDefinition = CM.CMFieldOfDefinition := rfl
theorem tyzSigmaFixesZn_eq : TYZSigmaFixesZn = Package.TYZSigmaFixesZn := rfl
theorem lemma318Literal_eq : Lemma318Literal = Package.Lemma318Literal := rfl
theorem genusPtsDefined_eq : GenusPtsDefined = Package.GenusPtsDefined := rfl
theorem thm35First_eq : Thm35First = Package.Thm35First := rfl
theorem lemma321_eq : Lemma321 = Package.Lemma321 := rfl
theorem genusPointLeafCM_eq : GenusPointLeafCM = Package.GenusPointLeafCM := rfl

end Copy

/-! ## §1. TYZ's class-7 CM point -/

/-- TYZ's `δ` (L1205: "an integer such that `δ² ≡ −n (mod 128)`"), pinned as the least `δ ∈ [0, 128)`
with `δ² + n ≡ 0 (mod 128)` (junk `0` if there is none; there is one for `n ≡ 7 (mod 8)`,
`tyzDelta_spec`). Numerically the CM point depends only on `δ mod 64`, and `δ ↦ −δ` conjugates it
(`class7.out`). -/
def tyzDelta (n : ℕ) : ℕ :=
  ((List.range 128).find? fun d => (d * d + n) % 128 == 0).getD 0

theorem tyzDelta_mod (n : ℕ) : tyzDelta n = tyzDelta (n % 128) := by
  unfold tyzDelta
  congr 2
  funext d
  rw [Nat.add_mod (d * d) n, Nat.add_mod (d * d) (n % 128), Nat.mod_mod]

theorem tyzDelta_spec_aux : ∀ m < 128, m % 8 = 7 → (tyzDelta m * tyzDelta m + m) % 128 = 0 := by
  decide +kernel

theorem tyzDelta_spec {n : ℕ} (hn : n % 8 = 7) : (tyzDelta n * tyzDelta n + n) % 128 = 0 := by
  have h := tyzDelta_spec_aux (n % 128) (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [← tyzDelta_mod] at h
  rw [Nat.add_mod, ← Nat.mod_mod n 128, ← Nat.add_mod]
  rw [Nat.add_mod] at h
  simpa [Nat.mod_mod] using h

theorem tyzDelta_dvd {n : ℕ} (hn : n % 8 = 7) :
    (128 : ℤ) ∣ (n : ℤ) + (tyzDelta n : ℤ) ^ 2 := by
  have h := Nat.dvd_of_mod_eq_zero (tyzDelta_spec hn)
  have h' : ((128 : ℕ) : ℤ) ∣ ((tyzDelta n * tyzDelta n + n : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
  push_cast at h'
  rw [pow_two, add_comm]
  exact h'

/-- **TYZ's class-7 Heegner form** `[(n+δ²)/4, δ, 1]` (level 32, discriminant `−n`): the fixed point
of TYZ's embedding `√−n ↦ [[δ, 2], [−(n+δ²)/2, −δ]]` (L1203–1205) solves `(n+δ²)h² + 4δh + 4 = 0`. -/
def tyzForm7 (n : ℕ) (hn : n % 8 = 7) : HeegnerForm 32 (-(n : ℤ)) where
  A := ((n : ℤ) + (tyzDelta n : ℤ) ^ 2) / 4
  B := tyzDelta n
  C := 1
  A_pos := by
    have := tyzDelta_dvd hn
    have h0 : (0 : ℤ) ≤ (tyzDelta n : ℤ) ^ 2 := by positivity
    have h7 : (7 : ℤ) ≤ n := by have : 7 ≤ n := by omega
                                exact_mod_cast this
    omega
  N_dvd := by
    have := tyzDelta_dvd hn
    omega
  disc := by
    have := tyzDelta_dvd hn
    omega
  D_neg := by
    have : (0 : ℤ) < n := by have : 0 < n := by omega
                             exact_mod_cast this
    omega
  primitive := by simp

/-- **`z_n = f_n(P_n)` for `n ≡ 7 (mod 8)`** (TYZ L1196: `f_n = i₀`), the Heegner point of
`tyzForm7 n` on `A = X₀(32)` (junk `0` otherwise). -/
def tyzZ7 (n : ℕ) : PtA :=
  if hn : n % 8 = 7 then heegnerPt (tyzForm7 n hn) else 0

/-! ## §2. Artin symbols of an arbitrary order, lifted to `ℚ̄` -/

section ArtinO

variable (d : ℕ) [NeZero d] (O : NumberFieldOrder (QNeg d))

/-- `ρ ∈ Gal(ℚ̄/ℚ)` acts on the ring class field of `O` (inside `ℚ̄` through ring-class's `embed d`)
as Tau Ceti's Artin symbol of `c ∈ Pic(O)` (for `O = O4 d` the same shape as `Package.ActsAsArtin4`). -/
def ActsAsArtinO (ρ : GalQ) (c : Pic O) : Prop :=
  ∀ x : ringClassField O, ρ (embed d (x : SeparableClosure (QNeg d))) =
    embed d ((ringClassArtinEquiv O c x : ringClassField O) : SeparableClosure (QNeg d))

/-- The ring class field restricted to `ℚ`-scalars. -/
abbrev RQ : IntermediateField ℚ (SeparableClosure (QNeg d)) := (ringClassField O).restrictScalars ℚ

/-- The ring automorphism of the ring class field (as `ℚ`-subfield) given by `g`. -/
def gQO (g : Gal(ringClassField O/QNeg d)) : RQ d O ≃+* RQ d O := g.toRingEquiv

/-- The induced automorphism of its image in `ℚ̄`. -/
def gBarO (g : Gal(ringClassField O/QNeg d)) : (RQ d O).map (embed d) ≃ₐ[ℚ] (RQ d O).map (embed d) :=
  AlgEquiv.ofRingEquiv (f := ((IntermediateField.equivMap (RQ d O) (embed d)).toRingEquiv.symm.trans
    ((gQO d O g).trans (IntermediateField.equivMap (RQ d O) (embed d)).toRingEquiv)))
    (fun q => by simp)

/-- **Every element of `Gal(ring class field / K_d)` is induced by an automorphism of `ℚ̄`** (the
proof of cm-points' `exists_actsAsArtin4`, for an arbitrary order). -/
theorem exists_actsAsArtinO (c : Pic O) : ∃ ρ : GalQ, ActsAsArtinO d O ρ c := by
  let χ := gBarO d O (ringClassArtinEquiv O c)
  refine ⟨AlgEquiv.ofBijective (χ.toAlgHom.liftNormal Qbar) (AlgHom.normal_bijective _ _ _ _), ?_⟩
  intro x
  have hx : embed d (x : SeparableClosure (QNeg d)) =
      algebraMap ((RQ d O).map (embed d)) Qbar (IntermediateField.equivMap (RQ d O) (embed d) x) := rfl
  rw [AlgEquiv.ofBijective_apply, hx, AlgHom.liftNormal_commutes]
  have e : χ (IntermediateField.equivMap (RQ d O) (embed d) x) =
      IntermediateField.equivMap (RQ d O) (embed d) (ringClassArtinEquiv O c x) := by
    simp only [χ, gBarO, gQO, AlgEquiv.ofRingEquiv_apply]
    change IntermediateField.equivMap (RQ d O) (embed d) (ringClassArtinEquiv O c
      ((IntermediateField.equivMap (RQ d O) (embed d)).symm
        (IntermediateField.equivMap (RQ d O) (embed d) x))) = _
    have h := AlgEquiv.symm_apply_apply (IntermediateField.equivMap (RQ d O) (embed d))
      (show ↥(RQ d O) from x)
    exact congrArg (fun y : ↥(RQ d O) => IntermediateField.equivMap (RQ d O) (embed d)
      (show ↥(RQ d O) from ringClassArtinEquiv O c (show ↥(ringClassField O) from y))) h
  show algebraMap _ Qbar (χ (IntermediateField.equivMap (RQ d O) (embed d) x)) = _
  rw [e]
  rfl

end ArtinO

/-! ## §3. The class-7 genus point -/

/-- The maximal order of `K_d = ℚ(√−d)`; its ring class field is ring-class's `hilbertField d`. -/
abbrev OK (d : ℕ) [NeZero d] : NumberFieldOrder (QNeg d) := maximalNumberFieldOrder (QNeg d)

/-- A fixed lift to `ℚ̄` of the Artin symbol of `c ∈ Cl(K_d)` on the Hilbert class field. -/
def liftMax (d : ℕ) [NeZero d] (c : Pic (OK d)) : GalQ := (exists_actsAsArtinO d (OK d) c).choose

theorem liftMax_spec (d : ℕ) [NeZero d] (c : Pic (OK d)) : ActsAsArtinO d (OK d) (liftMax d c) c :=
  (exists_actsAsArtinO d (OK d) c).choose_spec

/-- `2Cl_d = Cl(K_d)²` as a finite set. -/
def sqClasses (d : ℕ) [NeZero d] : Finset (Pic (OK d)) :=
  ((picSquares (OK d) : Subgroup (Pic (OK d))) : Set (Pic (OK d))).toFinite.toFinset

/-- **TYZ's class-7 genus point** `Z(e) = Σ_{t ∈ 2Cl_e} z_e^t` (L1316–1318 with `σ = 1`, L1268;
`Φ₀ = 2Cl_e` since `H'_e = H_e`, Prop 3.2(3)), each `t` realized by `liftMax`. On `A(H_e)` the value
does not depend on the lifts (`z_e ∈ A(H_e)` is the leaf `CMFieldOfDefinition7`). Junk `0` at `e = 0`. -/
def Z7 (e : ℕ) : PtA :=
  if h : e = 0 then 0 else
    haveI : NeZero e := ⟨h⟩
    ∑ c ∈ sqClasses e, galPt (liftMax e c) (tyzZ7 e)

/-! ## §4. TYZ's sets `Φ₀` for class 5, pinned -/

/-- `T` is a choice of TYZ's `Φ₀` for `e ≡ 5 (mod 8)` (L1316–1317): every `ρ ∈ T` acts on `H_{e,4}`
as the Artin symbol of a square class (so its restriction to `H'_e` lies in `2Cl'_e`), and over each
element of `2Cl_e = Cl(K_e)²` (acting on the Hilbert class field) lies exactly one `ρ ∈ T`; i.e. `T`
represents `2Cl'_e/⟨σ⟩ ≅ 2Cl_e` (L1270–1272). -/
def IsPhi0 (e : ℕ) [NeZero e] (T : Finset GalQ) : Prop :=
  (∀ ρ ∈ T, ∃ c ∈ picSquares (O4 e), ActsAsArtin4 ρ e c) ∧
    ∀ c' ∈ picSquares (OK e), ∃! ρ, ρ ∈ T ∧ ActsAsArtinO e (OK e) ρ c'

open Classical in
/-- **TYZ's `Φ₀` for class 5, pinned by choice** (the `∅` branches are never taken for `e ≠ 0`:
`phi0_spec : IsPhi0 e (Phi0 e)`, §9, from the extension of automorphisms `H_e → H_{e,4}`; TYZ
L1270–1276). TYZ: Lemma 3.21 holds for any choice (L2547–2554). -/
def Phi0 (e : ℕ) : Finset GalQ :=
  if h0 : e = 0 then ∅ else
    haveI : NeZero e := ⟨h0⟩
    if h : ∃ T : Finset GalQ, IsPhi0 e T then h.choose else ∅

/-- **TYZ's genus points, every one pinned**: `Z(e) = Σ_{t ∈ Φ₀(e)} t(z_e)` for `e ≡ 5 (mod 8)` and
`Z7 e` otherwise. -/
def tyzZ : ℕ → PtA := tyzGenusPt Phi0 Z7

theorem tyzZ_five {e : ℕ} (he : e % 8 = 5) : tyzZ e = genusSum (Phi0 e) (tyzZn e) := by
  simp only [tyzZ, tyzGenusPt, he, ↓reduceIte]

theorem tyzZ_seven {e : ℕ} (he : e % 8 = 7) : tyzZ e = Z7 e := by
  have : ¬ e % 8 = 5 := by omega
  simp only [tyzZ, tyzGenusPt, this, ↓reduceIte]

/-! ## §5. The leaves about the pinned genus points -/

/-- The Hilbert class field `H_d ⊂ ℚ̄` (`⊥` at `d = 0`). -/
def hilbertBar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((hilbertField d).restrictScalars ℚ).map (embed d)

/-- **Leaf CM-2-7 (field of definition of TYZ's class-7 CM point)**: for squarefree `n ≡ 7 (mod 8)`,
`z_n` (the Heegner point of `[(n+δ²)/4, δ, 1]`, maximal order, discriminant `−n`) is defined over the
Hilbert class field `H_n`. Classical case of Shimura's reciprocity law (conductor 1, prime to `N`):
Gross, *Heegner points on X₀(N)* (1984) §1–3; Gross–Zagier (1986) II §1; Shimura (1971) Thm. 5.7
(UNVERIFIED numbers); TYZ Prop. 3.2(3) (`H'_n = H_n`, L1260, VERIFIED read). Refereed. Numerically
the coordinates generate exactly `H_n` for n = 7, …, 71 (`class7.out`). Instance of
`CM.CMFieldOfDefinition` at `D = −n`, `H(−n) = H_n`. -/
def CMFieldOfDefinition7 : Prop :=
  ∀ n : ℕ, n % 8 = 7 → Squarefree n → tyzZ7 n ∈ ptsOver (hilbertBar n)

/-- **Leaf TYZ-2558 (field of definition of the class-7 genus point)**: for squarefree `e ≡ 7
(mod 8)`, `Z(e) ∈ A(L_e(i))`, `L_e(i) = ℚ(i, √p : p ∣ e)`. TYZ L2558 ("`H_n' = H_n` and thus `Z(n)` is
already defined over `L_n`", n ≡ 7), from `z_n ∈ A(H_n)` and genus theory (the subfield of `H_e` fixed
by `2Cl_e` is the genus field `ℚ(√p* : p ∣ e) ⊆ L_e(i)`, L2525). Refereed. Proved as glue below
(`class7GenusPtDefined_of`). Numerically the coordinates of `Z(e)` lie in `ℚ(√p* : p ∣ e)` for 12
values of `e` (`lemma321_7.out`). -/
def Class7GenusPtDefined : Prop :=
  ∀ e : ℕ, e % 8 = 7 → Squarefree e → Z7 e ∈ ptsOver (Lni e)

/-- **Leaf TYZ-3.21(4) (pinned)**: for squarefree `e ≡ 7 (mod 8)` and every `σ` acting on the
quadratic fields as `β₁` (`IsBetaOneLift`), `Z(e)^{σ} + Z(e) = g(e)·τ(1/2)`. TYZ Lemma 3.21(4)
(L2514–2516, "for any lifting"); since `Z(e) ∈ A(L_e(i))` (multiquadratic) the action of `σ` on it
only depends on `IsBetaOneLift`, so this follows from TYZ's statement with `Class7GenusPtDefined`.
Refereed. VERIFIED numerically for e = 7, 15, …, 103 (12 values, `lemma321_7.out`). -/
def Lemma321Seven : Prop :=
  ∀ e : ℕ, e % 8 = 7 → Squarefree e → ∀ σ : GalQ, IsBetaOneLift σ →
    galPt σ (Z7 e) + Z7 e = (gNat e : ℤ) • tauG 1

/-- **Leaf TYZ-3.21(1) (pinned)**: for squarefree `n ≡ 5 (mod 8)` there is `σ` with
`IsBetaOneLift σ` such that `Z(e)^{σ} + Z(e) ∈ g(e)τ((1−i)/2) + ℤτ(1)` for every `e ∣ n`,
`e ≡ 5 (mod 8)`, `Z(e) = Σ_{t ∈ Φ₀(e)} t(z_e)`. TYZ Lemma 3.21(1) (L2496–2512, for any lifting `β'`
and any choice of `Φ₀`, L2547–2554). Refereed. VERIFIED numerically for n = 5, 13, 37 with both
choices `Φ₀ = {1}, {σ}` and 8 lifts each (`lemma321_5.out`; uses ShimuraReciprocity). -/
def Lemma321Five : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ σ : GalQ, IsBetaOneLift σ ∧
      ∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (tyzZ e) + tyzZ e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2

/-! ## §6. Glue: the split of `GenusPointLeafCM` -/

theorem lemma321_of (h5 : Lemma321Five) (h7 : Lemma321Seven) : Lemma321 tyzZ := by
  intro n hn hsq
  obtain ⟨σ, hσ, h5'⟩ := h5 n hn hsq
  refine ⟨σ, hσ, h5', fun e he he7 => ?_⟩
  have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
  rw [tyzZ_seven he7]
  exact h7 e he7 hse σ hσ

theorem genusPtsDefined_tyzZ (hz : TYZZnOverHprime) (hN : HprimeNormal) (h7 : Class7GenusPtDefined) :
    GenusPtsDefined HHprime tyzZ :=
  genusPtsDefined_of hz hN Phi0 tyzZ (fun e he => tyzZ_five he)
    (fun e he hsq => by rw [tyzZ_seven he]; exact h7 e he hsq)

/-- **`GenusPointLeafCM` from the pinned leaves** (witnesses `Φ := Phi0`, `Z7 := Z7`). -/
theorem genusPointLeafCM_of_pinned {ℓ : ℕ → ℤ} (h7 : Class7GenusPtDefined)
    (h35 : Thm35First ℓ tyzZ) (h321 : Lemma321 tyzZ) : GenusPointLeafCM ℓ := by
  intro n hn hsq
  obtain ⟨ε, hε, hP⟩ := h35 n hn hsq
  obtain ⟨σ, hσ, h5, h7'⟩ := h321 n hn hsq
  refine ⟨Phi0, Z7, fun e he he7 => h7 e he7 (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)),
    ⟨ε, hε, hP⟩, σ, hσ, h5, h7'⟩

/-- **`GenusPointLeaf` via cm-points' `genusPointLeaf_of_split`**, for the pinned genus points. -/
theorem genusPointLeaf_of_pinned {ℓ : ℕ → ℤ} (hz : TYZZnOverHprime) (hN : HprimeNormal)
    (h7 : Class7GenusPtDefined) (h35 : Thm35First ℓ tyzZ) (h321 : Lemma321 tyzZ) :
    GenusPointLeaf ℓ HHprime :=
  genusPointLeaf_of_split (genusPtsDefined_tyzZ hz hN h7) h35 h321

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem, every genus point pinned.** The premise `TYZThm35ReadingA` from the three
`𝓛`-leaves, the CM leaves `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`,
TYZ Lemma 3.18 (literal) and the closed leaves about the pinned genus points `tyzZ`:
`Class7GenusPtDefined` (TYZ L2458), `Thm35First ℓ tyzZ` (TYZ Thm 3.3/3.5), `Lemma321Five`
(TYZ Lemma 3.21(1)) and `Lemma321Seven` (TYZ Lemma 3.21(4)). No existential over genus points
remains. -/
theorem tyzThm35ReadingA_of_pinned (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (h7 : Class7GenusPtDefined)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ) (h5 : Lemma321Five)
    (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_ringClass h11 h1 h29 tyzZ hN ((lemma318_iff_literal HHprime).mpr h318)
    (genusPtsDefined_tyzZ (tyzZnOverHprime_of hcm hi hs) hN h7) h35 (lemma321_of h5 h7')

open ZInQ.Contrib.TYZDecomp in
/-- The same, through cm-points' `tyzThm35ReadingA_of_cmLeaves` (consistency check: the pinned
leaves imply cm-points' bundled `GenusPointLeafCM`). -/
theorem tyzThm35ReadingA_of_pinned' (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (h7 : Class7GenusPtDefined)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ) (h5 : Lemma321Five)
    (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves h11 h1 h29 hcm hi hs hN h318
    fun ℓ hℓ => genusPointLeafCM_of_pinned h7 (h35 ℓ hℓ) (lemma321_of h5 h7')

/-! ## §7. `TYZSigmaFixesZn` from the shape of the Galois action (computation) -/

/-- `τ(1) = (0, 0)` is fixed by `[i]`, so `(1 − [i])` kills it. -/
theorem sub_iPt_pt00 : pt00 - iPt pt00 = 0 := by rw [iPt_pt00, sub_self]

/-- Points of `H'_d ⊂ ℚ̄` are fixed by every `ρ` acting on `H_{d,4}` as `σ_{1+2ϖ}` (the easy
direction of the Galois correspondence; converse: cm-points' `mem_Hprimebar_of_fixed`). -/
theorem fixed_of_mem_Hprimebar (d : ℕ) [NeZero d] {x : Qbar} (hx : x ∈ Hprimebar d) (ρ : GalQ)
    (hρ : ActsAsArtin4 ρ d (sigmaClass d)) : ρ x = x := by
  rw [Hprimebar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ H4 d := Hprime_le_H4 d hy
  have h1 : ρ (embed d y) =
      embed d ((artin4 d (sigmaClass d) ⟨y, hy'⟩ : H4 d) : SeparableClosure (QNeg d)) := hρ ⟨y, hy'⟩
  change ρ (embed d y) = embed d y
  rw [h1]
  congr 1
  have hy3 : (⟨y, hy'⟩ : H4 d).1 ∈ IntermediateField.lift
      (IntermediateField.fixedField (Subgroup.zpowers (artin4 d (sigmaClass d)))) := hy
  have hy2 := (IntermediateField.mem_lift _).mp hy3
  rw [IntermediateField.mem_fixedField_iff] at hy2
  exact congrArg Subtype.val (hy2 _ (Subgroup.mem_zpowers _))

/-- **Leaf GT' (`i ∈ H'_n`)**: for squarefree `n ≡ 5 (mod 8)`, `i ∈ H'_n`. Genus theory (`i` lies in
the genus field of `ℚ(√−n)`, hence in `H_n`; Cox Thm 6.1, UNVERIFIED number) and `H_n ⊆ H'_n` (TYZ
Prop. 3.2(1): `σ_{1+2ϖ} ∈ Gal(H_{n,4}/H_n)`, L1253–1256). Refereed (textbook + TYZ). -/
def IInHprime : Prop := ∀ n : ℕ, n % 8 = 5 → Squarefree n → iQ ∈ Hprimebar n

/-- **Leaf TYZ-3.7(1)+SR (the Galois action of `σ_{1+2ϖ}` on `f₀(P_n)` is translation by
`τ(1) = (0,0)`)**. Consequence of TYZ's Proposition `heckeaction5`(1) (L1488–1490: `Q^{1+2ϖ} = Q + τ(1)`
for every `Q ∈ X_U(ℂ)`; proposition number UNVERIFIED) and Shimura's reciprocity law at the CM point
`P_n` (`σ_t P_n = P_n^t`), `f₀` being defined over `ℚ`. Refereed. VERIFIED numerically for
n = 5, 13, 21, 29, 37 (3 primes each, `sigma5.out`, through `CM.ShimuraReciprocity`, whose direction is
VERIFIED in `shimura.out`). Unlike `TYZSigmaFixesZn` (printed as TYZ Thm 3.6(1), L1413) it does not
involve the `[i]`-sign of `CM.tyzZn`. -/
def TYZSigmaShiftsF0 : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → galPt ρ (tyzHeegnerPt n) = tyzHeegnerPt n + pt00

/-- **`TYZSigmaFixesZn` from `TYZSigmaShiftsF0` and `i ∈ H'_n`** (glue): `ρ` fixes `i`, so it commutes
with `[i]`, and `(1 − [i])(f₀ + (0,0)) = (1 − [i])f₀`. -/
theorem tyzSigmaFixesZn_of (hsh : TYZSigmaShiftsF0) (hi : IInHprime) : TYZSigmaFixesZn := by
  intro n hn0 hn hsq ρ hρ
  have hρi : ρ iQ = iQ := fixed_of_mem_Hprimebar n (hi n hn hsq) ρ hρ
  have e := hsh n hn0 hn hsq ρ hρ
  unfold tyzZn
  rw [map_sub, galPt_iPt ρ hρi, e, iPt_add, iPt_pt00]
  abel

/-! ## §8. `Class7GenusPtDefined` from the CM field of definition and genus theory -/

section Class7Descent

/-- `galPt` is multiplicative: `(στ)(P) = σ(τ(P))`. -/
theorem galPt_mul (σ τ : GalQ) (P : PtA) : galPt (σ * τ) P = galPt σ (galPt τ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h1, e1⟩ := galPt_some (σ * τ) h
    obtain ⟨h2, e2⟩ := galPt_some τ h
    obtain ⟨h3, e3⟩ := galPt_some σ h2
    rw [e1, e2, e3, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨AlgEquiv.mul_apply σ τ x, AlgEquiv.mul_apply σ τ y⟩

/-- Two automorphisms agreeing on `K` act identically on `A(K)`. -/
theorem galPt_congr {K : IntermediateField ℚ Qbar} {ρ ρ' : GalQ} (h : ∀ x ∈ K, ρ x = ρ' x)
    {P : PtA} (hP : P ∈ ptsOver K) : galPt ρ P = galPt ρ' P := by
  rw [mem_ptsOver_iff] at hP
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · obtain ⟨h1, e1⟩ := galPt_some ρ hxy
    obtain ⟨h2, e2⟩ := galPt_some ρ' hxy
    rw [e1, e2, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨h x hP.1, h y hP.2⟩

variable (d : ℕ) [NeZero d]

theorem hilbertBar_eq : hilbertBar d = ((hilbertField d).restrictScalars ℚ).map (embed d) := by
  simp only [hilbertBar, NeZero.ne d, ↓reduceDIte]

variable {d}

theorem actsO_mem {ρ : GalQ} {c : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c) {x : Qbar}
    (hx : x ∈ hilbertBar d) : ρ x ∈ hilbertBar d := by
  rw [hilbertBar_eq] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ρ (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ ⟨y, hy⟩
  change ρ (embed d y) ∈ _
  rw [h1]
  exact ⟨_, (ringClassArtinEquiv (OK d) c ⟨y, hy⟩).2, rfl⟩

theorem actsO_agree {ρ ρ' : GalQ} {c : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c)
    (hρ' : ActsAsArtinO d (OK d) ρ' c) : ∀ x ∈ hilbertBar d, ρ x = ρ' x := by
  intro x hx
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ρ (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ ⟨y, hy⟩
  have h2 : ρ' (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ' ⟨y, hy⟩
  change ρ (embed d y) = ρ' (embed d y)
  rw [h1, h2]

theorem actsO_mul {ρ ρ' : GalQ} {c c' : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c)
    (hρ' : ActsAsArtinO d (OK d) ρ' c') : ActsAsArtinO d (OK d) (ρ * ρ') (c * c') := by
  intro x
  rw [AlgEquiv.mul_apply, hρ' x, hρ (ringClassArtinEquiv (OK d) c' x), map_mul, AlgEquiv.mul_apply]

theorem mem_sqClasses {c : Pic (OK d)} : c ∈ sqClasses d ↔ c ∈ picSquares (OK d) := by
  simp [sqClasses]

theorem sum_sqClasses_mul {s : Pic (OK d)} (hs : s ∈ picSquares (OK d)) (f : Pic (OK d) → PtA) :
    ∑ c ∈ sqClasses d, f (s * c) = ∑ c ∈ sqClasses d, f c := by
  refine Finset.sum_nbij' (fun c => s * c) (fun c => s⁻¹ * c) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).mul_mem hs hc
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).mul_mem ((picSquares (OK d)).inv_mem hs) hc
  · intro c _; simp
  · intro c _; simp
  · intro c _; rfl

theorem Z7_eq (e : ℕ) [NeZero e] : Z7 e = ∑ c ∈ sqClasses e, galPt (liftMax e c) (tyzZ7 e) := by
  simp only [Z7, NeZero.ne e, ↓reduceDIte]

theorem Z7_mem {e : ℕ} [NeZero e] (hz : tyzZ7 e ∈ ptsOver (hilbertBar e)) :
    Z7 e ∈ ptsOver (hilbertBar e) := by
  rw [Z7_eq]
  exact (ptsOver _).sum_mem fun c _ =>
    galPt_mem (liftMax e c) (fun x hx => actsO_mem (liftMax_spec e c) hx) hz

/-- **The lifts of `2Cl_e` fix `Z(e)`** (reindexing the genus sum; the lifts act on `A(H_e)` through
their Artin symbols). -/
theorem galPt_Z7 {e : ℕ} [NeZero e] (hz : tyzZ7 e ∈ ptsOver (hilbertBar e)) {s : Pic (OK e)}
    (hs : s ∈ picSquares (OK e)) : galPt (liftMax e s) (Z7 e) = Z7 e := by
  rw [Z7_eq, map_sum]
  have : ∀ c ∈ sqClasses e, galPt (liftMax e s) (galPt (liftMax e c) (tyzZ7 e)) =
      galPt (liftMax e (s * c)) (tyzZ7 e) := fun c _ => by
    rw [← galPt_mul]
    exact galPt_congr (actsO_agree (actsO_mul (liftMax_spec e s) (liftMax_spec e c))
      (liftMax_spec e (s * c))) hz
  rw [Finset.sum_congr rfl this, sum_sqClasses_mul hs (fun c => galPt (liftMax e c) (tyzZ7 e))]

/-- The genus field `G_d ⊂ ℚ̄` of `K_d` (ring-class's `genusField` of the maximal order: the subfield
of `H_d` fixed by `2Cl_d`), `⊥` at `d = 0`. -/
def genusBar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((genusField (OK d)).restrictScalars ℚ).map (embed d)

/-- **Galois descent `H_d → G_d`**: a point of `H_d ⊂ ℚ̄` fixed by the lifts of `2Cl_d` lies in the
genus field. -/
theorem mem_genusBar_of_fixed {x : Qbar} (hx : x ∈ hilbertBar d)
    (hfix : ∀ s ∈ picSquares (OK d), liftMax d s x = x) : x ∈ genusBar d := by
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hg : genusBar d = ((genusField (OK d)).restrictScalars ℚ).map (embed d) := by
    simp only [genusBar, NeZero.ne d, ↓reduceDIte]
  rw [hg]
  refine ⟨y, ?_, rfl⟩
  show y ∈ genusField (OK d)
  rw [genusField, show y = (⟨y, hy⟩ : ringClassField (OK d)).1 from rfl, IntermediateField.mem_lift,
    IntermediateField.mem_fixedField_iff]
  rintro f ⟨s, hs, rfl⟩
  have h1 : liftMax d s (embed d y) = embed d ((ringClassArtinEquiv (OK d) s ⟨y, hy⟩ :
      ringClassField (OK d)) : SeparableClosure (QNeg d)) := liftMax_spec d s ⟨y, hy⟩
  have h0 : liftMax d s (embed d y) = embed d y := hfix s hs
  rw [h0] at h1
  exact Subtype.ext ((embed d).injective h1).symm

/-- **Leaf GT-7 (genus theory)**: for squarefree `e ≡ 7 (mod 8)` the genus field of `ℚ(√−e)` (the
subfield of the Hilbert class field fixed by `Cl²`) lies in `L_e(i) = ℚ(i, √p : p ∣ e)`; it is
`ℚ(√p* : p ∣ e)`, `p* = (−1)^{(p−1)/2} p` (Gauss; Cox, *Primes of the form x² + ny²*, Thm. 6.1 and
§6.C, UNVERIFIED numbers; TYZ L2525 uses it). Refereed (textbook). -/
def GenusFieldLeLni : Prop := ∀ e : ℕ, e % 8 = 7 → Squarefree e → genusBar e ≤ Lni e

/-- **`Class7GenusPtDefined` is glue** from the field of definition of TYZ's class-7 CM point
(`CMFieldOfDefinition7`, Gross/Shimura) and genus theory (`GenusFieldLeLni`). -/
theorem class7GenusPtDefined_of (hcm : CMFieldOfDefinition7) (hg : GenusFieldLeLni) :
    Class7GenusPtDefined := by
  intro e he hsq
  have : NeZero e := ⟨by omega⟩
  have hz := hcm e he hsq
  have hZ := Z7_mem hz
  have hfix : ∀ s ∈ picSquares (OK e), galPt (liftMax e s) (Z7 e) = Z7 e :=
    fun s hs => galPt_Z7 hz hs
  rw [mem_ptsOver_iff] at hZ ⊢
  revert hZ hfix
  rcases Z7 e with _ | ⟨x, y, h⟩
  · intro _ _; trivial
  · intro hZ hfix
    have hc : ∀ s ∈ picSquares (OK e), liftMax e s x = x ∧ liftMax e s y = y := by
      intro s hs
      have e1 := hfix s hs
      obtain ⟨h', e'⟩ := galPt_some (liftMax e s) h
      rw [e', WeierstrassCurve.Affine.Point.some.injEq] at e1
      exact e1
    exact ⟨hg e he hsq (mem_genusBar_of_fixed hZ.1 fun s hs => (hc s hs).1),
      hg e he hsq (mem_genusBar_of_fixed hZ.2 fun s hs => (hc s hs).2)⟩

end Class7Descent

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem, finest form**: as `tyzThm35ReadingA_of_pinned`, with `Class7GenusPtDefined`
replaced by the textbook leaves `CMFieldOfDefinition7` and `GenusFieldLeLni`. -/
theorem tyzThm35ReadingA_of_pinnedLeaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (hcm7 : CMFieldOfDefinition7)
    (hg : GenusFieldLeLni) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_pinned h11 h1 h29 hcm hi hs hN h318 (class7GenusPtDefined_of hcm7 hg) h35 h5 h7'


/-! ## §9. Existence of TYZ's `Φ₀` (so `Phi0` is never the junk value) -/

section Phi0Exists

variable (e : ℕ) [NeZero e]

theorem hle : hilbertField e ≤ H4 e := hilbertLeH4 e inferInstance

instance : Normal (QNeg e) (SeparableClosure (QNeg e)) := inferInstance

/-- **Every element of `Gal(H_e/K_e)` extends to `Gal(H_{e,4}/K_e)`**: for `d' ∈ Cl(K_e)` there is
`c₄ ∈ Pic(O_{e,4})` whose Artin symbol restricts to that of `d'` on `H_e ⊆ H_{e,4}`. -/
theorem exists_restrict (d' : Pic (OK e)) : ∃ c4 : Pic (O4 e), ∀ x : hilbertField e,
    ((artin4 e c4 ⟨x, hle e x.2⟩ : H4 e) : SeparableClosure (QNeg e)) =
      ((ringClassArtinEquiv (OK e) d' x : hilbertField e) : SeparableClosure (QNeg e)) := by
  let g := ringClassArtinEquiv (OK e) d'
  let τ : SeparableClosure (QNeg e) ≃ₐ[QNeg e] SeparableClosure (QNeg e) :=
    AlgEquiv.ofBijective (g.toAlgHom.liftNormal (SeparableClosure (QNeg e)))
      (AlgHom.normal_bijective _ _ _ _)
  refine ⟨(artin4 e).symm (AlgEquiv.restrictNormal τ (H4 e)), fun x => ?_⟩
  rw [MulEquiv.apply_symm_apply]
  have h1 := AlgEquiv.restrictNormal_commutes τ (H4 e) ⟨x, hle e x.2⟩
  have h2 := AlgHom.liftNormal_commutes g.toAlgHom (SeparableClosure (QNeg e)) x
  exact h1.trans h2

theorem exists_phi0_elem {c' : Pic (OK e)} (hc : c' ∈ picSquares (OK e)) :
    ∃ ρ : GalQ, (∃ c ∈ picSquares (O4 e), ActsAsArtin4 ρ e c) ∧ ActsAsArtinO e (OK e) ρ c' := by
  obtain ⟨d', rfl⟩ := hc
  obtain ⟨c4, hc4⟩ := exists_restrict e d'
  obtain ⟨ρ, hρ⟩ := exists_actsAsArtin4 e (c4 ^ 2)
  refine ⟨ρ, ⟨c4 ^ 2, ⟨c4, rfl⟩, hρ⟩, fun x => ?_⟩
  have h := hρ ⟨x, hle e x.2⟩
  change ρ (embed e (x : SeparableClosure (QNeg e))) = _ at h
  rw [h]
  congr 1
  have hx1 := hc4 x
  have hx2 := hc4 (ringClassArtinEquiv (OK e) d' x)
  simp only [powMonoidHom_apply, pow_two, map_mul, AlgEquiv.mul_apply]
  rw [show (artin4 e c4 ⟨x, hle e x.2⟩ : H4 e) =
      ⟨_, hle e (ringClassArtinEquiv (OK e) d' x).2⟩ from Subtype.ext hx1]
  exact hx2

open Classical in
/-- A fixed `ρ` for each square class (`exists_phi0_elem`). -/
def phi0Elem (c' : Pic (OK e)) : GalQ :=
  if h : c' ∈ picSquares (OK e) then (exists_phi0_elem e h).choose else 1

theorem artinO_inj {ρ : GalQ} {c c' : Pic (OK e)} (h : ActsAsArtinO e (OK e) ρ c)
    (h' : ActsAsArtinO e (OK e) ρ c') : c = c' := by
  apply (ringClassArtinEquiv (OK e)).injective
  ext x
  have := (h x).symm.trans (h' x)
  rw [(embed e).injective this]

/-- **TYZ's `Φ₀` exists** (TYZ L1270–1276), so `Phi0 e` satisfies `IsPhi0`. -/
theorem exists_isPhi0 : ∃ T : Finset GalQ, IsPhi0 e T := by
  classical
  refine ⟨(sqClasses e).image (phi0Elem e), ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hρ
    rw [mem_sqClasses] at hc'
    rw [phi0Elem, dite_eq_left hc']
    exact (exists_phi0_elem e hc').choose_spec.1
  · intro c' hc'
    have hspec : ∀ c ∈ picSquares (OK e), ActsAsArtinO e (OK e) (phi0Elem e c) c := fun c hc => by
      rw [phi0Elem, dite_eq_left hc]
      exact (exists_phi0_elem e hc).choose_spec.2
    refine ⟨phi0Elem e c', ⟨Finset.mem_image.mpr ⟨c', mem_sqClasses.mpr hc', rfl⟩, hspec c' hc'⟩, ?_⟩
    rintro ρ ⟨hρ, hρc⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hρ
    rw [mem_sqClasses] at hc
    rw [artinO_inj e (hspec c hc) hρc]

theorem phi0_spec : IsPhi0 e (Phi0 e) := by
  classical
  have h := exists_isPhi0 e
  simp only [Phi0, NeZero.ne e, ↓reduceDIte, h]
  exact h.choose_spec

end Phi0Exists


/-! ## §10. Rewiring to ring-class's theorems (cm-bridge) -/

section Rewire

open ZInQ.Contrib.TYZGenus.RingClassBridge

/-- **`i ∈ H'_n`** (cm-numeric's leaf `IInHprime`), proved: `i ∈ L_n(i) ⊆ H'_n` (ring-class's
`Lni_le_Hprimebar`, genus theory via Bauer + quadratic reciprocity). -/
theorem iInHprime : IInHprime := by
  intro n hn hsq
  haveI : NeZero n := ⟨by omega⟩
  exact Lni_le_Hprimebar (by omega) hsq (iQ_mem_Lni n)

/-- **`CMFieldOfDefinition7` from the general CM leaf** `CM.CMFieldOfDefinition ringClassFieldD`
(instance `D = −n`, `Q = tyzForm7 n`): the ring class field of discriminant `−n` is the Hilbert
class field for squarefree `n ≡ 3 (mod 4)` (ring-class's `ringClassFieldD_neg`). -/
theorem cmFieldOfDefinition7_of (h : CM.CMFieldOfDefinition ringClassFieldD) :
    CMFieldOfDefinition7 := by
  intro n hn hsq
  haveI : NeZero n := ⟨by omega⟩
  have h1 := h (-(n : ℤ)) (tyzForm7 n hn)
  have hr := ringClassFieldD_neg (d := n) (by omega) hsq
  simp only [tyzZ7, hn, ↓reduceDIte]
  rw [hilbertBar_eq]
  convert h1 using 2
  exact hr.symm

/-- `TYZSigmaFixesZn` from the printed Hecke-action identity alone (`IInHprime` is now proved). -/
theorem tyzSigmaFixesZn_of' (hsh : TYZSigmaShiftsF0) : TYZSigmaFixesZn :=
  tyzSigmaFixesZn_of hsh iInHprime

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem after the rewiring** (`GenusFieldLeLni` still a hypothesis): reading A of TYZ
Theorem 3.5 from the three `𝓛`-leaves, the general CM leaf `CM.CMFieldOfDefinition ringClassFieldD`,
`TYZSigmaShiftsF0` (TYZ Prop. 3.7(1) + Shimura reciprocity), TYZ Lemma 3.18 (literal),
`GenusFieldLeLni` (genus theory), `Thm35First ℓ tyzZ` (TYZ Thm 3.3/3.5), `Lemma321Five`,
`Lemma321Seven` (TYZ Lemma 3.21(1),(4)). `IInH4`, `HprimeNormal`, `IInHprime`,
`CMFieldOfDefinitionTYZ`, `CMFieldOfDefinition7` and `TYZSigmaFixesZn` are gone. -/
theorem tyzThm35ReadingA_of_rewired (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CM.CMFieldOfDefinition ringClassFieldD)
    (hsh : TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime) (hg : GenusFieldLeLni)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_pinnedLeaves h11 h1 h29 (cmFieldTYZ_of_ringClassD hcm) iInH4
    (tyzSigmaFixesZn_of' hsh) hprimeNormal h318 (cmFieldOfDefinition7_of hcm) hg h35 h5 h7'

end Rewire


/-! ## §11. `GenusFieldLeLni` proved (genus theory for `n ≡ 3 (mod 4)`)

For squarefree `n ≡ 3 (mod 4)`: a prime `𝔭 ∤ 2n` of `K_n` that splits completely in
`K_n(i, √p : p ∣ n)` has `−1` and every `p ∣ n` square mod `𝔭`, so `|O/𝔭| ≡ 1 (mod 4)` and
`(|O/𝔭| / p) = 1` (quadratic reciprocity, `FiniteField.isSquare_odd_prime_iff`); all genus
characters `χ_p` vanish on `[𝔭]`, so `[𝔭] ∈ Cl²` (`picSquares_eq_iInf_ker_chi`), i.e. `𝔭` splits in the
genus field. Bauer's theorem (`le_of_splitSet_diff_subset`) gives `G_n ⊆ K_n(i, √p : p ∣ n)`, and the
latter maps into `L_n(i)` (it contains `√−n = ±i∏√p`). -/

section GenusSeven

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

/-- The Picard class (Tau Ceti) of an ideal for the maximal order is its ideal class. -/
theorem picClass_maximal {K : Type} [Field K] [NumberField K]
    (J : integralIdealsPrimeTo (maximalNumberFieldOrder K).conductorModulus)
    (hJ : (J : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) :
    (maximalNumberFieldOrder K).picClass J =
      (ClassGroup.mk0 ⟨(J : Ideal (𝓞 K)), hJ⟩ : ClassGroup (𝓞 K)) := by
  rw [picClass_apply, ← ClassGroup.mk_mk0 K]
  congr 1
  apply Units.ext
  rw [coe_integralIdealsAwayConductorToInvertible_apply, FractionalIdeal.coe_mk0]
  congr 1
  ext x
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨(⟨x.1, x.2⟩ : 𝓞 K), (maximalNumberFieldOrder K).mem_toRingOfIntegers.mpr x.2⟩, hx, rfl⟩



variable {n : ℕ} [NeZero n]

/-- The square-root generators of `L_n(i)`: `−1` and the primes `p ∣ n`. -/
def sqrtSet (n : ℕ) : Finset ℤ := insert (-1) (n.primeFactors.image (fun p : ℕ => (p : ℤ)))

/-- `K_n(i, √p : p ∣ n) ⊆ K_nˢ`. -/
def genusAmb (n : ℕ) [NeZero n] : IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  IntermediateField.adjoin (QNeg n) (sqrtK (QNeg n) '' (sqrtSet n : Set ℤ))

theorem adjSqrt_le_genusAmb {a : ℤ} (ha : a ∈ sqrtSet n) : adjSqrt (QNeg n) a ≤ genusAmb n :=
  IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2
    (Set.mem_image_of_mem _ (Finset.mem_coe.2 ha)))

instance : FiniteDimensional (QNeg n) (genusAmb n) :=
  IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨a, -, rfl⟩ := hx
    exact isIntegral_sqrtK _ a

instance : Normal (QNeg n) (genusAmb n) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rw [genusAmb, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have h : g (sqrtK (QNeg n) a) ^ 2 = sqrtK (QNeg n) a ^ 2 := by
    rw [← map_pow, sqrtK_sq, map_intCast]
  have hmem : sqrtK (QNeg n) a ∈ genusAmb n :=
    IntermediateField.subset_adjoin _ _ (Set.mem_image_of_mem _ ha)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact hmem
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact neg_mem hmem

instance : IsGalois (QNeg n) (genusAmb n) := IsGalois.mk

/-- **Genus characters at a prime split in `K_n(i, √p : p ∣ n)`**: if `−1` and every `p ∣ n` are
squares modulo `𝔭 ∌ 2n`, then `χ_q([𝔭]) = 1` for every `q ∣ n` (`|O/𝔭| ≡ 1 (mod 4)` and
`(|O/𝔭| / q) = (q / |O/𝔭|) = 1`, quadratic reciprocity in Mathlib's finite-field form). -/
theorem chi_eq_one_of_isSquare (hn : Odd n) (hsq : Squarefree n)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal)
    (hm1 : IsSquare (((-1 : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)))
    (hp : ∀ p ∈ n.primeFactors, IsSquare (((p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)))
    (q : n.primeFactors) :
    chi n q (ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩) = 1 := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  have h2 : (2 : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h => h2n (by
    push_cast; exact 𝔭.asIdeal.mul_mem_right _ h)
  have hchar : ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ 2 := fun hc => h2 (by
    have : ((2 : ℕ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using this)
  have hq2 : (q : ℕ) ≠ 2 := by
    rintro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 this)
  have hqF : ((q : ℕ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ 0 := by
    intro h0
    apply h2n
    obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors q.2
    have h1 : ((q : ℕ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using h0
    have e2 : 2 * n = 2 * m * (q : ℕ) := by rw [mul_assoc, mul_comm m, ← hm]
    rw [show ((2 * n : ℕ) : 𝓞 (QNeg n)) = ((2 * m * q : ℕ) : 𝓞 (QNeg n)) from congrArg _ e2,
      Nat.cast_mul]
    exact 𝔭.asIdeal.mul_mem_left _ h1
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  rw [Int.cast_neg, Int.cast_one, FiniteField.isSquare_neg_one_iff] at hm1
  have h4 : Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) % 4 = 1 := by omega
  have hsqq := hp q q.2
  rw [Int.cast_natCast, FiniteField.isSquare_odd_prime_iff hchar hq2, ZMod.χ₄_nat_one_mod_four h4] at hsqq
  simp only [Int.cast_one, one_mul] at hsqq
  have hsquare : IsSquare ((Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) : ℕ) : ZMod q) := by
    by_contra hns
    exact hsqq (quadraticChar_neg_one_iff_not_isSquare.2 hns)
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    have hpr : (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)).Prime := hk
    rw [hcard] at hd
    have := (Nat.prime_dvd_prime_iff_eq hqp hpr).1 (hqp.dvd_of_dvd_pow hd)
    apply hqF
    rw [this]
    exact ringChar.Nat.cast_ringChar
  have hb : ZInQ.RouteK.legBit q ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ) = 0 := by
    unfold ZInQ.RouteK.legBit
    rw [if_pos]
    rw [hN, Int.cast_natCast]
    exact hsquare
  have hc := chi_mk0 n hn hsq q ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ hqN
  rw [hc, hb]
  rfl

/-- Transfer along `conductorOrder K 1 = maximal order`, then genus theory
(`picSquares_eq_iInf_ker_chi`). -/
theorem picClass_mem_picSquares (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n)
    (O : NumberFieldOrder (QNeg n)) (hO : O = maximalNumberFieldOrder (QNeg n))
    (J : integralIdealsPrimeTo O.conductorModulus) (hJ0 : (J : Ideal (𝓞 (QNeg n))) ∈ (Ideal _)⁰)
    (hchi : ∀ q, chi n q (ClassGroup.mk0 ⟨(J : Ideal (𝓞 (QNeg n))), hJ0⟩) = 1) :
    O.picClass J ∈ picSquares O := by
  subst hO
  rw [picClass_maximal J hJ0, picSquares_eq_iInf_ker_chi n hn hsq h1]
  exact Subgroup.mem_iInf.2 fun q => hchi q

/-- **The genus field of `K_n`, `n ≡ 3 (mod 4)` squarefree, lies in `K_n(i, √p : p ∣ n)`** (Bauer). -/
theorem genusField_le_genusAmb (hn : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) :
    genusField (maximalNumberFieldOrder (QNeg n)) ≤ genusAmb n := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hG : genusField (maximalNumberFieldOrder (QNeg n)) =
      ringSubfield (picSquares (conductorOrder (QNeg n) 1)) := by
    rw [← conductorOrder_one]; rfl
  rw [hG]
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have h2 : (2 : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h => h2n (by
    push_cast; exact 𝔭.asIdeal.mul_mem_right _ h)
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg n) 1).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  rw [mem_splitSet_iff (conductorOrder (QNeg n) 1) _ ⟨_, hJ⟩ 𝔭 rfl]
  have hsplit : ∀ a ∈ sqrtSet n, 𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) a) := fun a ha =>
    splitSet_anti (adjSqrt_le_genusAmb ha) h𝔭
  have hm1 := (mem_splitSet_adjSqrt_iff 𝔭 (a := -1) (by
    intro h; apply h2
    have : -((2 * (-1) : ℤ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := 𝔭.asIdeal.neg_mem h
    simpa using this)).1 (hsplit (-1) (Finset.mem_insert_self _ _))
  have hp : ∀ p ∈ n.primeFactors,
      IsSquare (((p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)) := by
    intro p hp
    refine (mem_splitSet_adjSqrt_iff 𝔭 (a := p) ?_).1
      (hsplit p (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)))
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors hp
    have e2 : 2 * n = 2 * p * n' := by rw [hn']; ring
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * (p : ℤ) : ℤ) : 𝓞 (QNeg n)) * (n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]; push_cast; ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  exact picClass_mem_picSquares hodd hsq h1 _ (conductorOrder_one _) ⟨_, hJ⟩
    (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot)
    (chi_eq_one_of_isSquare hodd hsq 𝔭 h2n hm1 hp)

/-! ### From `K_nˢ` to `ℚ̄` -/

theorem embed_sqrtK_mem_Lni {a : ℤ} (ha : a ∈ sqrtSet n) : embed n (sqrtK (QNeg n) a) ∈ Lni n := by
  apply IntermediateField.subset_adjoin
  have hs : embed n (sqrtK (QNeg n) a) ^ 2 = (a : Qbar) := by rw [← map_pow, sqrtK_sq, map_intCast]
  rcases Finset.mem_insert.1 ha with rfl | ha
  · left; simpa using hs
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
    right; exact ⟨p, hp, by simpa using hs⟩

theorem embed_omega_mem_Lni (hsq : Squarefree n) :
    embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega) ∈ Lni n := by
  have hroot : ∀ p ∈ n.primeFactors, ∃ r : Qbar, r ^ 2 = (p : Qbar) := fun p _ =>
    IsAlgClosed.exists_pow_nat_eq _ two_pos
  choose r hr using hroot
  set y := iQ * ∏ p ∈ n.primeFactors.attach, r p.1 p.2
  have hy : y ∈ Lni n := mul_mem (iQ_mem_Lni n) (prod_mem fun p _ =>
    IntermediateField.subset_adjoin _ _ (Or.inr ⟨p.1, p.2, hr _ _⟩))
  have hy2 : y ^ 2 = -(n : Qbar) := by
    rw [mul_pow, iQ_sq, ← Finset.prod_pow]
    have : ∏ p ∈ n.primeFactors.attach, r p.1 p.2 ^ 2 = ∏ p ∈ n.primeFactors.attach, ((p.1 : ℕ) : Qbar) :=
      Finset.prod_congr rfl fun p _ => hr _ _
    rw [this, Finset.prod_attach n.primeFactors (fun p => ((p : ℕ) : Qbar)), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
    ring
  have hw2 : (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) ^ 2 =
      -(n : Qbar) := by
    rw [← map_pow, ← map_pow]
    simp [QuadraticAlgebra.omega_pow_two_eq_add]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hw2.trans hy2.symm) with h | h
  · rw [h]; exact hy
  · rw [h]; exact neg_mem hy

theorem embed_algebraMap_mem_Lni (hsq : Squarefree n) (k : QNeg n) :
    embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k) ∈ Lni n := by
  rw [algebraMap_eq_re_im, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  exact add_mem (IntermediateField.algebraMap_mem _ _)
    (mul_mem (IntermediateField.algebraMap_mem _ _) (embed_omega_mem_Lni hsq))

/-- `L_n(i)` pulled back to `K_nˢ`, as a field over `K_n`. -/
def LniK (n : ℕ) [NeZero n] (hsq : Squarefree n) :
    IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  { ((Lni n).comap (embed n)) with
    algebraMap_mem' := fun k => embed_algebraMap_mem_Lni hsq k }

theorem mem_LniK (hsq : Squarefree n) {x : SeparableClosure (QNeg n)} :
    x ∈ LniK n hsq ↔ embed n x ∈ Lni n := Iff.rfl

theorem genusAmb_le_LniK (hsq : Squarefree n) : genusAmb n ≤ LniK n hsq := by
  rw [genusAmb, IntermediateField.adjoin_le_iff]
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_LniK hsq).2 (embed_sqrtK_mem_Lni ha)

/-- **Genus theory for `n ≡ 7 (mod 8)`** (cm-numeric's leaf `GenusFieldLeLni`), proved. -/
theorem genusFieldLeLni : GenusFieldLeLni := by
  intro e he hsq
  haveI : NeZero e := ⟨by omega⟩
  have hle := (genusField_le_genusAmb (n := e) (by omega) hsq (by omega)).trans
    (genusAmb_le_LniK hsq)
  simp only [genusBar, NeZero.ne e, ↓reduceDIte]
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_LniK hsq).1 (hle hx)



end GenusSeven

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem after §10–§11**: as `tyzThm35ReadingA_of_rewired`, with `GenusFieldLeLni` proved. -/
theorem tyzThm35ReadingA_of_cmLeaves7 (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CM.CMFieldOfDefinition ringClassFieldD)
    (hsh : TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_rewired h11 h1 h29 hcm hsh h318 genusFieldLeLni h35 h5 h7'


/-! ## §12. `Lemma321Seven` reduced to TYZ Theorem 3.6(3) and the action of `β₁` on the genus field

TYZ's proof of Lemma 3.21(4) (L2547–2566): `Z(n)` is defined over the genus field `L_n`; on `L_n(i)`
any lift `β'` of `β₁` acts as `σ_ϖ ∘ c` (`c` complex conjugation), and `σ_ϖ = σ_{ϖ^5}` on `L_n`; so
`Z(n)^{β'} = Z(n)^{σ_{ϖ^5} ∘ c}`, and Theorem 3.6(3) (`z̄_n + z_n^{σ_{ϖ^5}} = τ(1/2)`) gives the
result after summing over `2Cl_n`. Here `σ_{ϖ^5}` (geometric normalization, L1247–1250) acts on the
Hilbert class field `H_n` as the arithmetic Artin symbol of `[𝔭₂]^{−5}`, `𝔭₂` TYZ's place `v₂`. -/

section Seven

open ZInQ.Contrib.TYZGenus.RingClassBridge
open scoped nonZeroDivisors

/-- `γ ∈ Gal(ℚ̄/ℚ)` is complex conjugation for `CM`'s fixed embedding `ιC : ℚ̄ → ℂ`. -/
def IsComplexConj (γ : GalQ) : Prop := ∀ x : Qbar, ιC (γ x) = starRingEnd ℂ (ιC x)

/-- **Complex conjugation exists in `Gal(ℚ̄/ℚ)`** (the image of `ιC` is normal over `ℚ`). -/
theorem exists_complexConj : ∃ γ : GalQ, IsComplexConj γ := by
  let f : Qbar →ₐ[ℚ] ℂ := ιCA
  let e : Qbar ≃ₐ[ℚ] f.fieldRange := AlgEquiv.ofInjectiveField f
  haveI : Normal ℚ f.fieldRange := Normal.of_algEquiv e
  have hr : ∀ y ∈ f.fieldRange, conjQ y ∈ f.fieldRange := by
    intro y hy
    have h := AlgHom.fieldRange_of_normal (E := f.fieldRange) (conjQ.comp f.fieldRange.val)
    rw [← h]
    exact ⟨⟨y, hy⟩, rfl⟩
  let c : f.fieldRange →ₐ[ℚ] f.fieldRange :=
    (conjQ.comp f.fieldRange.val).codRestrict f.fieldRange.toSubalgebra fun y => hr y.1 y.2
  have hc : Function.Involutive c := fun y => Subtype.ext (by
    show conjQ (conjQ (y : ℂ)) = y
    simp [conjQ_apply])
  let c' : f.fieldRange ≃ₐ[ℚ] f.fieldRange := AlgEquiv.ofBijective c hc.bijective
  refine ⟨e.trans (c'.trans e.symm), fun x => ?_⟩
  have h1 : ∀ y : f.fieldRange, f (e.symm y) = y := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rfl
  show f (e.symm (c' (e x))) = starRingEnd ℂ (f x)
  rw [h1]
  rfl

theorem ιC_injective : Function.Injective ιC := ιC.injective

theorem IsComplexConj.mul_self {γ : GalQ} (hγ : IsComplexConj γ) (x : Qbar) : γ (γ x) = x :=
  ιC_injective (by rw [hγ, hγ, Complex.conj_conj])

theorem IsComplexConj.inv_apply {γ : GalQ} (hγ : IsComplexConj γ) (x : Qbar) : γ⁻¹ x = γ x := by
  apply γ.injective
  rw [hγ.mul_self]
  exact γ.apply_symm_apply x

/-- Complex conjugation moves `√−n`. -/
theorem IsComplexConj.ne_omega {γ : GalQ} (hγ : IsComplexConj γ) (n : ℕ) [NeZero n] :
    γ (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) ≠
      embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega) := by
  set w := embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)
  intro h
  have hw2 : w ^ 2 = -(n : Qbar) := by
    simp only [w]
    rw [← map_pow, ← map_pow]
    simp [QuadraticAlgebra.omega_pow_two_eq_add]
  have hc : starRingEnd ℂ (ιC w) = ιC w := by rw [← hγ, h]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 hc
  have h2 : (r : ℂ) ^ 2 = -(n : ℂ) := by rw [← hr, ← map_pow, hw2]; simp
  have h3 : r ^ 2 = -(n : ℝ) := by exact_mod_cast h2
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  nlinarith [sq_nonneg r]

/-- The orientation of `K_n ⊂ ℚ̄ ⊂ ℂ` (through ring-class's arbitrary `embed n` and `CM`'s `ιC`):
`ιC(embed(√−n)) = +i√n`. -/
def PosOrient (n : ℕ) [NeZero n] : Prop :=
  0 < (ιC (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega))).im

open Classical in
/-- TYZ's place `v₂` for `n ≡ 7 (mod 8)` (Theorem 3.6(3), L1424–1425: the place above 2 with
`v₂(√−n − δ) ≥ 6`), **oriented through `ιC`**: the prime of `𝓞_{K_n}` whose image in `ℂ` is
`(2, (i√n − δ)/2)`, `δ = tyzDelta n`, i.e. `(2, (√−n − δ)/2) = (2, θ − (δ+1)/2)` if
`ιC(embed √−n) = +i√n` and its conjugate `(2, (−√−n − δ)/2) = (2, 1 − θ − (δ+1)/2)` otherwise
(`θ = (1 + √−n)/2`). The orientation matters: with the conjugate prime the statement
`TYZThm36Seven` is false (`thm36_7.out`, "wrong sign"); the numerical check uses `√−n ↦ i√n` and the
form `[2, δ mod 4, ·]` of `(2, (i√n − δ)/2)`. (`⊤` if `n % 4 ≠ 3`.) -/
def p2Ideal (n : ℕ) [NeZero n] : Ideal (𝓞 (QNeg n)) :=
  if h : n % 4 = 3 then
    if PosOrient n then
      Ideal.span {2, ZInQ.RouteK.Redei.thetaO n h - (((tyzDelta n + 1) / 2 : ℕ) : 𝓞 (QNeg n))}
    else
      Ideal.span {2, 1 - ZInQ.RouteK.Redei.thetaO n h - (((tyzDelta n + 1) / 2 : ℕ) : 𝓞 (QNeg n))}
  else ⊤

theorem p2Ideal_mem (n : ℕ) [NeZero n] : p2Ideal n ∈ (Ideal (𝓞 (QNeg n)))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  have key : ∀ x : 𝓞 (QNeg n), Ideal.span {2, x} ≠ 0 := by
    intro x h0
    have h2 : (2 : 𝓞 (QNeg n)) ∈ Ideal.span {2, x} := Ideal.subset_span (by simp)
    rw [h0, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
    exact two_ne_zero h2
  unfold p2Ideal
  split_ifs
  · exact key _
  · exact key _
  · exact top_ne_bot

/-- The class `[𝔭₂] ∈ Cl(K_n) = Pic(𝓞_{K_n})`. -/
def p2Class (n : ℕ) [NeZero n] : Pic (OK n) :=
  (ClassGroup.mk0 ⟨p2Ideal n, p2Ideal_mem n⟩ : ClassGroup (𝓞 (QNeg n)))

/-- **Leaf TYZ-3.6(3) (Galois action on TYZ's class-7 CM point)**: for squarefree `n ≡ 7 (mod 8)`,
complex conjugation `γ` and any `ρ ∈ Gal(ℚ̄/ℚ)` acting on the Hilbert class field `H_n` as the
(arithmetic) Artin symbol of `[𝔭₂]^{−5}`, `𝔭₂` the prime with image `(2, (i√n − δ)/2)` in `ℂ`
(`p2Ideal`, oriented through `ιC`; independent review 2026-11-13 found that an unoriented `𝔭₂` makes
the statement depend on the arbitrary `embed n`): `γ(z_n) + ρ(z_n) = τ(1/2)`. TYZ Theorem 3.6(3) (L1424–1427,
VERIFIED read): `z̄_n + z_n^{σ_{ϖ^5}} = τ(1/2)` with `ϖ ∈ K_{n,2}`, `v₂(ϖ) = 1`, `v₂'(ϖ) = 0`, and `σ`
the geometric Artin map (L1247–1250), so `σ_{ϖ^5}|_{H_n} = Art([𝔭₂])^{−5}`. Refereed. Numerically
VERIFIED for the 12 squarefree `n ≡ 7 (mod 8)`, `7 ≤ n ≤ 103` (`thm36_7.out`); the opposite sign
`[𝔭₂]^{+5}` fails for 7 of them. -/
def TYZThm36Seven : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 7 → Squarefree n → ∀ γ ρ : GalQ, IsComplexConj γ →
    ActsAsArtinO n (OK n) ρ ((p2Class n)⁻¹ ^ 5) →
      galPt γ (tyzZ7 n) + galPt ρ (tyzZ7 n) = tauG 1

/-- **Glue BETA-7 (`β₁` on the genus field)**: for squarefree `n ≡ 7 (mod 8)`, a lift `σ` of
`β₁ = r_∞(−1)r₂(−2)`, complex conjugation `γ` and `ρ` acting on `H_n` as `Art([𝔭₂]^{−5})`, `σ` and
`γ ∘ ρ` agree on the genus field `G_n = ℚ(√p* : p ∣ n)`. TYZ L2526–2531 ("the action of `β_j'` on
`L_n(i)` is the same as that of `σ_ϖ ∘ c`") plus `σ_ϖ = σ_{ϖ^5}` on `L_n` (exponent 2). Glue: on
`√p*` both sides act by `(2/p)·sgn(p*)` (`betaOneSign`; Art`[𝔭₂]` acts on `√p*` by the genus character
`χ_p([𝔭₂]) = (N𝔭₂/p) = (2/p)`), and `G_n ⊆ K_n(√p* : p ∣ n)` (Gauss). Proved in §13 (`betaOnGenus7`). -/
def BetaOnGenus7 : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 7 → Squarefree n → ∀ σ γ ρ : GalQ, IsBetaOneLift σ →
    IsComplexConj γ → ActsAsArtinO n (OK n) ρ ((p2Class n)⁻¹ ^ 5) →
      ∀ x ∈ genusBar n, σ x = γ (ρ x)

/-- Restriction of ring class Artin symbols to the Hilbert class field, on elements. -/
theorem coe_artin_restrict {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (c : Pic O) (x : ringClassField (maximalNumberFieldOrder K)) :
    ((ringClassArtinEquiv O c (IntermediateField.inclusion (ringClassField_maximal_le O) x) :
        ringClassField O) : SeparableClosure K) =
      ((ringClassArtinEquiv (maximalNumberFieldOrder K) (picToMax O c) x :
        ringClassField (maximalNumberFieldOrder K)) : SeparableClosure K) := by
  rw [← restrict_ringClassArtinEquiv, ← IntermediateField.coe_inclusion (ringClassField_maximal_le O),
    restrictNormalHom_inclusion_apply]

variable {d : ℕ} [NeZero d]

theorem hilbertBar_eq_bar : hilbertBar d = ringClassFieldBar d 1 := by
  rw [hilbertBar_eq, ringClassFieldBar_eq, conductorOrder_one]

theorem map_mem_hilbertBar (τ : GalQ) {x : Qbar} (hx : x ∈ hilbertBar d) : τ x ∈ hilbertBar d := by
  haveI : Normal ℚ (hilbertBar d) := by rw [hilbertBar_eq_bar]; exact normal_ringClassFieldBar d 1
  exact (IntermediateField.normal_iff_forall_map_le'.1 inferInstance τ) ⟨x, hx, rfl⟩

/-- Restriction `H_{d,4} → H_d` of Artin symbols, in `ℚ̄`. -/
theorem actsO_of_acts4 {ρ : GalQ} {c4 : Pic (O4 d)} (h : ActsAsArtin4 ρ d c4) :
    ActsAsArtinO d (OK d) ρ (picToMax (O4 d) c4) := by
  intro x
  have h1 := h (IntermediateField.inclusion (ringClassField_maximal_le (O4 d)) x)
  rw [IntermediateField.coe_inclusion] at h1
  rw [h1, coe_artin_restrict]

/-- **Complex conjugation inverts the Artin symbols of `H_d`** (from ring-class's
`actsAsArtin4_conj` for `H_{d,4}` and restriction). -/
theorem actsO_conj {γ ρ : GalQ} (hγ : IsComplexConj γ) {c : Pic (OK d)}
    (hρ : ActsAsArtinO d (OK d) ρ c) : ActsAsArtinO d (OK d) (γ * ρ * γ⁻¹) c⁻¹ := by
  obtain ⟨c4, rfl⟩ := picToMax_surjective (O4 d) c
  obtain ⟨ρ4, h4⟩ := exists_actsAsArtin4 d c4
  have hc := actsO_of_acts4 (actsAsArtin4_conj (hγ.ne_omega d) h4)
  rw [map_inv] at hc
  intro x
  have hx : embed d (x : SeparableClosure (QNeg d)) ∈ hilbertBar d := by
    rw [hilbertBar_eq]; exact ⟨x, x.2, rfl⟩
  rw [← hc x]
  simp only [AlgEquiv.mul_apply]
  congr 1
  exact actsO_agree hρ (actsO_of_acts4 h4) _ (map_mem_hilbertBar _ hx)

theorem Z7_mem_genusBar {e : ℕ} [NeZero e] (hz : tyzZ7 e ∈ ptsOver (hilbertBar e)) :
    Z7 e ∈ ptsOver (genusBar e) := by
  have hZ := Z7_mem hz
  have hfix : ∀ s ∈ picSquares (OK e), galPt (liftMax e s) (Z7 e) = Z7 e :=
    fun s hs => galPt_Z7 hz hs
  rw [mem_ptsOver_iff] at hZ ⊢
  revert hZ hfix
  rcases Z7 e with _ | ⟨x, y, h⟩
  · intro _ _; trivial
  · intro hZ hfix
    have hc : ∀ s ∈ picSquares (OK e), liftMax e s x = x ∧ liftMax e s y = y := by
      intro s hs
      have e1 := hfix s hs
      obtain ⟨h', e'⟩ := galPt_some (liftMax e s) h
      rw [e', WeierstrassCurve.Affine.Point.some.injEq] at e1
      exact e1
    exact ⟨mem_genusBar_of_fixed hZ.1 fun s hs => (hc s hs).1,
      mem_genusBar_of_fixed hZ.2 fun s hs => (hc s hs).2⟩

theorem sum_sqClasses_inv (f : Pic (OK d) → PtA) :
    ∑ c ∈ sqClasses d, f c⁻¹ = ∑ c ∈ sqClasses d, f c := by
  refine Finset.sum_nbij' (fun c => c⁻¹) (fun c => c⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).inv_mem hc
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).inv_mem hc
  · intro c _; simp
  · intro c _; simp
  · intro c _; rfl

theorem card_sqClasses : (sqClasses d).card = gNat d := by
  rw [gNat, dif_neg (NeZero.ne d), gCl_eq_card_picSquares, sqClasses,
    ← Nat.card_eq_card_finite_toFinset]
  rfl

/-- **`Lemma321Seven` from TYZ Theorem 3.6(3) and glue BETA-7** (plus the CM field of definition). -/
theorem lemma321Seven_of (hcm : CMFieldOfDefinition7) (h36 : TYZThm36Seven)
    (hb : BetaOnGenus7) : Lemma321Seven := by
  intro e he hsq σ hσ
  haveI : NeZero e := ⟨by omega⟩
  obtain ⟨γ, hγ⟩ := exists_complexConj
  obtain ⟨ρ, hρ⟩ := exists_actsAsArtinO e (OK e) ((p2Class e)⁻¹ ^ 5)
  have hz := hcm e he hsq
  set z := tyzZ7 e
  have hleaf := h36 e inferInstance he hsq γ ρ hγ hρ
  have hρz : galPt ρ z = tauG 1 - galPt γ z := by rw [← hleaf]; abel
  have hZ := Z7_mem_genusBar hz
  have h1 : galPt σ (Z7 e) = galPt (γ * ρ) (Z7 e) :=
    galPt_congr (fun x hx => by rw [AlgEquiv.mul_apply]; exact hb e inferInstance he hsq σ γ ρ hσ hγ hρ x hx) hZ
  have hτ : ∀ τ' : GalQ, galPt τ' (tauG 1) = tauG 1 := fun τ' => by
    rw [tauG_apply, one_smul]; exact galPt_ptT τ'
  have hterm : ∀ c ∈ sqClasses e, galPt (γ * ρ) (galPt (liftMax e c) z) =
      tauG 1 - galPt (liftMax e c⁻¹) z := by
    intro c _
    -- `ρ t_c z = t_c ρ z` on `A(H_e)`
    have hcomm : galPt ρ (galPt (liftMax e c) z) = galPt (liftMax e c) (galPt ρ z) := by
      rw [← galPt_mul, ← galPt_mul]
      exact galPt_congr (actsO_agree (actsO_mul hρ (liftMax_spec e c))
        (by rw [mul_comm]; exact actsO_mul (liftMax_spec e c) hρ)) hz
    rw [galPt_mul, hcomm, hρz, map_sub, map_sub, hτ, hτ, ← galPt_mul, ← galPt_mul]
    congr 1
    -- `γ t_c γ = γ t_c γ⁻¹` acts as `Art(c⁻¹)` on `H_e`
    have hconj := actsO_conj hγ (liftMax_spec e c)
    have hγinv : γ⁻¹ = γ := by ext x; exact hγ.inv_apply x
    have hg : γ * liftMax e c * γ = γ * liftMax e c * γ⁻¹ := by rw [hγinv]
    rw [hg]
    exact galPt_congr (actsO_agree hconj (liftMax_spec e c⁻¹)) hz
  rw [h1, Z7_eq, map_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    sum_sqClasses_inv (fun c => galPt (liftMax e c) z), card_sqClasses, ← natCast_zsmul]
  abel

end Seven


/-! ## §13. Towards glue BETA-7: the genus field is `K_n(√p* : p ∣ n)` -/

section BetaSeven

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

/-- `p* = (−1)^{(p−1)/2} p` for odd `p`. -/
def pstar (p : ℕ) : ℤ := if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

/-- **Quadratic reciprocity, finite-field form with `p*`**: in a finite field `F` of odd
characteristic `≠ p`, `p*` is a square iff `|F|` is a square mod `p`. -/
theorem isSquare_pstar_iff {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpF : ringChar F ≠ p) :
    IsSquare ((pstar p : ℤ) : F) ↔ IsSquare ((Fintype.card F : ℕ) : ZMod p) := by
  classical
  obtain ⟨k, hk, hcard⟩ := FiniteField.card F (ringChar F)
  have hpF0 : ((p : ℕ) : F) ≠ 0 := by
    intro h
    exact hpF ((Nat.prime_dvd_prime_iff_eq hk hp.out).1 ((ringChar.spec F p).1 h))
  have hq0 : ((Fintype.card F : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    rw [hcard] at hd
    exact hpF ((Nat.prime_dvd_prime_iff_eq hp.out hk).1 (hp.out.dvd_of_dvd_pow hd)).symm
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := hp.out.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with he | ho
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 (even_iff_two_dvd.1 he)).symm hp2
    · omega
  have hq4 : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
  have hχp : quadraticChar (ZMod p) (-1) = ZMod.χ₄ p := by
    rw [quadraticChar_neg_one (by rwa [ZMod.ringChar_zmod_n]), ZMod.card]
  have key : quadraticChar F ((pstar p : ℤ) : F) = quadraticChar (ZMod p) (Fintype.card F) := by
    have hodd' := quadraticChar_odd_prime hF hp2 hpF
    unfold pstar
    rcases hp4 with h | h
    · rw [if_pos h, Int.cast_natCast, hodd', map_mul]
      rcases hq4 with hq | hq
      · rw [ZMod.χ₄_nat_one_mod_four hq]; simp
      · rw [ZMod.χ₄_nat_three_mod_four hq, Int.cast_neg, Int.cast_one, hχp,
          ZMod.χ₄_nat_one_mod_four h, one_mul]
    · rw [if_neg (by omega), Int.cast_neg, Int.cast_natCast, neg_eq_neg_one_mul, map_mul, hodd',
        map_mul, quadraticChar_neg_one hF]
      rcases hq4 with hq | hq
      · rw [ZMod.χ₄_nat_one_mod_four hq]; simp
      · rw [ZMod.χ₄_nat_three_mod_four hq, Int.cast_neg, Int.cast_one, hχp,
          ZMod.χ₄_nat_three_mod_four h]; ring
  have hps0 : ((pstar p : ℤ) : F) ≠ 0 := by
    unfold pstar; split_ifs <;> simpa using hpF0
  rw [← quadraticChar_one_iff_isSquare hps0, ← quadraticChar_one_iff_isSquare hq0, key]


section Star

variable {n : ℕ} [NeZero n]

/-- `{p* : p ∣ n}`. -/
def pstarSet (n : ℕ) : Finset ℤ := n.primeFactors.image pstar

/-- `K_n(√p* : p ∣ n) ⊆ K_nˢ` (the genus field, `genusField_le_genusStar`). -/
def genusStar (n : ℕ) [NeZero n] : IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  IntermediateField.adjoin (QNeg n) (sqrtK (QNeg n) '' (pstarSet n : Set ℤ))

theorem adjSqrt_le_genusStar {a : ℤ} (ha : a ∈ pstarSet n) : adjSqrt (QNeg n) a ≤ genusStar n :=
  IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2
    (Set.mem_image_of_mem _ (Finset.mem_coe.2 ha)))

instance : FiniteDimensional (QNeg n) (genusStar n) :=
  IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨a, -, rfl⟩ := hx
    exact isIntegral_sqrtK _ a

instance : Normal (QNeg n) (genusStar n) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rw [genusStar, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have h : g (sqrtK (QNeg n) a) ^ 2 = sqrtK (QNeg n) a ^ 2 := by
    rw [← map_pow, sqrtK_sq, map_intCast]
  have hmem : sqrtK (QNeg n) a ∈ genusStar n :=
    IntermediateField.subset_adjoin _ _ (Set.mem_image_of_mem _ ha)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact hmem
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact neg_mem hmem

instance : IsGalois (QNeg n) (genusStar n) := IsGalois.mk

theorem pstar_mem_or (p : ℕ) : pstar p = p ∨ pstar p = -p := by
  unfold pstar; split_ifs <;> simp

/-- The residue field at `𝔭 ∌ 2n` has characteristic `≠ 2` and `≠ p` for `p ∣ n`. -/
theorem residue_facts (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal) {p : ℕ} (hp : p ∈ n.primeFactors) :
    letI := Ideal.Quotient.field 𝔭.asIdeal
    ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ 2 ∧ ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ p := by
  letI := Ideal.Quotient.field 𝔭.asIdeal
  have hmem : ∀ k : ℕ, k ∣ 2 * n → ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ k := by
    intro k hk hc
    apply h2n
    obtain ⟨m, hm⟩ := hk
    have h0 : ((k : ℕ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    have h1 : ((k : ℕ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using h0
    rw [show ((2 * n : ℕ) : 𝓞 (QNeg n)) = ((k * m : ℕ) : 𝓞 (QNeg n)) from congrArg _ hm, Nat.cast_mul]
    exact 𝔭.asIdeal.mul_mem_right _ h1
  exact ⟨hmem 2 ⟨n, rfl⟩, hmem p (Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hp) 2)⟩

/-- Genus characters at a prime split in `K_n(√p* : p ∣ n)`. -/
theorem chi_eq_one_of_isSquare_pstar (hn : Odd n) (hsq : Squarefree n)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal)
    (hp : ∀ p ∈ n.primeFactors, IsSquare (((pstar p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)))
    (q : n.primeFactors) :
    chi n q (ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩) = 1 := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharq⟩ := residue_facts 𝔭 h2n q.2
  have hq2 : (q : ℕ) ≠ 2 := by
    rintro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 this)
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hsquare := (isSquare_pstar_iff hchar hq2 hcharq).1 (hp q q.2)
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    rw [hcard] at hd
    exact hcharq ((Nat.prime_dvd_prime_iff_eq hqp hk).1 (hqp.dvd_of_dvd_pow hd)).symm
  have hb : ZInQ.RouteK.legBit q ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ) = 0 := by
    unfold ZInQ.RouteK.legBit
    rw [if_pos]
    rw [hN, Int.cast_natCast]
    exact hsquare
  have hc := chi_mk0 n hn hsq q ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ hqN
  rw [hc, hb]
  rfl

end Star


variable {n : ℕ} [NeZero n]

/-- **The genus field of `K_n`, `n ≡ 3 (mod 4)` squarefree, lies in `K_n(√p* : p ∣ n)`** (Bauer, as
`genusField_le_genusAmb`, with `p*` square mod `𝔭` for all `p ∣ n` ⇒ all genus characters trivial). -/
theorem genusField_le_genusStar (hn : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) :
    genusField (maximalNumberFieldOrder (QNeg n)) ≤ genusStar n := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hG : genusField (maximalNumberFieldOrder (QNeg n)) =
      ringSubfield (picSquares (conductorOrder (QNeg n) 1)) := by
    rw [← conductorOrder_one]; rfl
  rw [hG]
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg n) 1).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  rw [mem_splitSet_iff (conductorOrder (QNeg n) 1) _ ⟨_, hJ⟩ 𝔭 rfl]
  have hp : ∀ p ∈ n.primeFactors,
      IsSquare (((pstar p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)) := by
    intro p hp
    refine (mem_splitSet_adjSqrt_iff 𝔭 (a := pstar p) ?_).1
      (splitSet_anti (adjSqrt_le_genusStar (Finset.mem_image_of_mem _ hp)) h𝔭)
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors hp
    have e2 : 2 * n = 2 * p * n' := by rw [hn']; ring
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * pstar p : ℤ) : 𝓞 (QNeg n)) * ((if p % 4 = 1 then 1 else -1 : ℤ) * n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]
      unfold pstar
      split_ifs <;> push_cast <;> ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  exact picClass_mem_picSquares hodd hsq h1 _ (conductorOrder_one _) ⟨_, hJ⟩
    (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot)
    (chi_eq_one_of_isSquare_pstar hodd hsq 𝔭 h2n hp)

/-- Norms in `𝓞_{K_n}`, `n ≡ 3 (mod 4)` squarefree, `p ∣ n`: `4N(β) ≡ t² (mod p)`. -/
theorem norm_sq_mod_prime3 (hsq : Squarefree n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (β : 𝓞 (QNeg n)) : ∃ t : ℤ, (p : ℤ) ∣ 4 * Algebra.norm ℤ β - t ^ 2 := by
  obtain ⟨s, hs⟩ := exists_two_re β
  obtain ⟨m, hm⟩ := exists_two_re (β * sqrtNeg n)
  have hN := normZ_eq_re_im β
  have hre : ((β * sqrtNeg n : 𝓞 (QNeg n)) : QNeg n).re = -(n : ℚ) * (β : QNeg n).im := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg]
  rw [hre] at hm
  refine ⟨s, ?_⟩
  set w := 4 * Algebra.norm ℤ β - s ^ 2
  have hw : (n : ℤ) * w = m ^ 2 := by
    have : ((n : ℤ) * w : ℚ) = (m : ℚ) ^ 2 := by
      simp only [w]; push_cast
      rw [hN, ← hs, ← hm]; ring
    exact_mod_cast this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨n', hn'⟩ := hpn
  have hpn' : ¬ (p : ℤ) ∣ n' := by
    intro h
    obtain ⟨k, rfl⟩ := Int.natCast_dvd_natCast.1 h
    have := hsq p ⟨k, by rw [hn']; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hpm : (p : ℤ) ∣ m := by
    apply hpZ.dvd_of_dvd_pow (n := 2)
    rw [← hw, hn']; push_cast
    exact ⟨n' * w, by ring⟩
  obtain ⟨m', rfl⟩ := hpm
  have h2 : (p : ℤ) * (n' * w) = (p : ℤ) * (p * m' ^ 2) := by
    rw [hn'] at hw; push_cast at hw; linear_combination hw
  have h3 : (n' : ℤ) * w = p * m' ^ 2 := mul_left_cancel₀ hpZ.ne_zero h2
  have h4 : (p : ℤ) ∣ n' * w := ⟨m' ^ 2, h3⟩
  rcases hpZ.dvd_or_dvd h4 with h | h
  · exact absurd h hpn'
  · exact h

/-- **Genus theory, `n ≡ 3 (mod 4)`**: `K_n(√p*) ⊆ H_n` for every prime `p ∣ n` (Bauer: a principal
prime `𝔭 = β𝓞_K ∤ 2n` has `4N𝔭 ≡ t² (mod p)`, so `p*` is a square mod `𝔭` by `isSquare_pstar_iff`). -/
theorem adjSqrt_pstar_le_hilbertField (hn : n % 4 = 3) (hsq : Squarefree n) {p : ℕ}
    (hp : p ∈ n.primeFactors) :
    adjSqrt (QNeg n) (pstar p) ≤ hilbertField n := by
  rw [hilbertField_eq_ringSubfield]
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by have := NeZero.ne n; omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg n) 1).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  have h1 := (mem_splitSet_iff (conductorOrder (QNeg n) 1) ⊥ ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  rw [Subgroup.mem_bot, picClass_eq_one_iff] at h1
  obtain ⟨β, -, hspan⟩ := h1
  have hq : Nat.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    change Ideal.absNorm (((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo
      (conductorOrder (QNeg n) 1).conductorModulus) : Ideal (𝓞 (QNeg n)))) = _
    rw [hspan, Ideal.absNorm_span_singleton]
  have hnn := normZ_nonneg (n := n) β
  have hc : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β := Int.natAbs_of_nonneg hnn
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hp
    omega
  haveI := Fact.mk hpp
  have h2a : ((2 * pstar p : ℤ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := by
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors hp
    have e2 : 2 * n = 2 * p * n' := by rw [hn']; ring
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * pstar p : ℤ) : 𝓞 (QNeg n)) * ((if p % 4 = 1 then 1 else -1 : ℤ) * n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]
      unfold pstar
      split_ifs <;> push_cast <;> ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  rw [mem_splitSet_adjSqrt_iff 𝔭 h2a]
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharp⟩ := residue_facts 𝔭 h2n hp
  rw [isSquare_pstar_iff hchar hp2 hcharp]
  have hcard : Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Nat.card_eq_fintype_card, hq]
  rw [hcard]
  obtain ⟨t, ht⟩ := norm_sq_mod_prime3 hsq hpp (Nat.dvd_of_mem_primeFactors hp) β
  set N : ZMod p := (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod p)
  have h4 : (4 : ZMod p) * N = (t : ZMod p) ^ 2 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 ht
    have hN : N = ((Algebra.norm ℤ β : ℤ) : ZMod p) := by
      simp only [N]; rw [← Int.cast_natCast, hc]
    rw [hN]
    push_cast at h0
    linear_combination h0
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h')
  have e : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact ⟨t * 2⁻¹, by linear_combination (2⁻¹ * 2⁻¹ : ZMod p) * h4 + (-N * (1 + 2 * 2⁻¹)) * e⟩

end BetaSeven

/-! ### Assembly of glue BETA-7 from genus theory -/

section BetaAssembly

open ZInQ.RouteK.Redei
open scoped nonZeroDivisors

/-- **Glue GT-H (genus theory, `n ≡ 3 (mod 4)`)**: `√p* ∈ H_n` for every prime `p ∣ n` (Gauss; Cox,
*Primes of the form x² + ny²*, Thm. 6.1, UNVERIFIED number). -/
def SqrtPstarInHilbert : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 4 = 3 → Squarefree n → ∀ p ∈ n.primeFactors,
    adjSqrt (QNeg n) (pstar p) ≤ hilbertField n

/-- **Glue GT-ART (genus characters as Artin characters)**: for squarefree `n ≡ 3 (mod 4)`, `p ∣ n`
and `c ∈ Cl(K_n)`, the Artin symbol of `c` acts on `√p* ∈ H_n` by the genus character `χ_p(c)`
(`RouteK.Redei.chi`, `χ_p([𝔞]) = (N𝔞 / p)`). Classical (Gauss genus theory; Frobenius on `K_n(√p*)`
plus quadratic reciprocity). -/
def ArtinPstarChi : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 4 = 3 → Squarefree n → ∀ (q : n.primeFactors) (c : Pic (OK n))
    (hs : sqrtK (QNeg n) (pstar q) ∈ hilbertField n),
    ((ringClassArtinEquiv (OK n) c ⟨_, hs⟩ : hilbertField n) : SeparableClosure (QNeg n)) =
      (if chi n q c = 1 then 1 else -1) * sqrtK (QNeg n) (pstar q)

/-- **Glue NORM-2**: `N𝔭₂ = 2` for `n ≡ 7 (mod 8)` (computation). -/
def NormP2 : Prop := ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 7 → Ideal.absNorm (p2Ideal n) = 2

/-- Complex conjugation on a square root of a nonzero integer `D`: `γ(√D) = sgn(D)·√D`. -/
theorem IsComplexConj.apply_sqrt {γ : GalQ} (hγ : IsComplexConj γ) {D : ℤ} (hD : D ≠ 0) {r : Qbar}
    (hr : r ^ 2 = (D : Qbar)) : γ r = (if D < 0 then -1 else 1) * r := by
  apply ιC_injective
  rw [hγ]
  have hz : ιC r ^ 2 = (D : ℂ) := by rw [← map_pow, hr, map_intCast]
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at hre him
  split_ifs with hneg
  · have h0 : (ιC r).re = 0 := by
      rcases mul_eq_zero.1 (show (ιC r).re * (ιC r).im = 0 by linarith) with h | h
      · exact h
      · exfalso
        rw [h] at hre
        have : (0 : ℝ) ≤ (ιC r).re * (ιC r).re := mul_self_nonneg _
        have : (D : ℝ) < 0 := by exact_mod_cast hneg
        linarith
    rw [map_mul, map_neg, map_one, neg_one_mul, Complex.ext_iff, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, h0]
    exact ⟨by simp, rfl⟩
  · have h0 : (ιC r).im = 0 := by
      rcases mul_eq_zero.1 (show (ιC r).re * (ιC r).im = 0 by linarith) with h | h
      · exfalso
        rw [h] at hre
        have : (0 : ℝ) ≤ (ιC r).im * (ιC r).im := mul_self_nonneg _
        have : (0 : ℝ) < D := by
          have : (0 : ℤ) < D := lt_of_le_of_ne (not_lt.1 hneg) (Ne.symm hD)
          exact_mod_cast this
        linarith
      · exact h
    rw [map_mul, map_one, one_mul, Complex.ext_iff, Complex.conj_re, Complex.conj_im, h0]
    exact ⟨rfl, by simp⟩

/-- The equalizer of `f ∘ embed` and `g ∘ embed`, as a field over `K_n` when `f`, `g` agree on `K_n`. -/
def eqField (n : ℕ) [NeZero n] (f g : GalQ)
    (hK : ∀ k : QNeg n, f (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k)) =
      g (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k))) :
    IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  { AlgHom.equalizer ((f : Qbar →ₐ[ℚ] Qbar).comp (embed n)) ((g : Qbar →ₐ[ℚ] Qbar).comp (embed n)) with
    algebraMap_mem' := hK
    inv_mem' := fun x hx => by
      show f (embed n x⁻¹) = g (embed n x⁻¹)
      simp only [map_inv₀]
      exact congrArg _ hx }

theorem mem_eqField {n : ℕ} [NeZero n] {f g : GalQ} {hK} {x : SeparableClosure (QNeg n)} :
    x ∈ eqField n f g hK ↔ f (embed n x) = g (embed n x) := Iff.rfl

theorem sqf_neg {x : ℤ} (h : Squarefree x) : Squarefree (-x) := fun y hy => h y ((dvd_neg).1 hy)

theorem squarefree_pstar {p : ℕ} (hp : p.Prime) : Squarefree (pstar p) := by
  have h : Squarefree (p : ℤ) := Int.squarefree_natCast.2 hp.squarefree
  unfold pstar; split_ifs
  · exact h
  · exact sqf_neg h

theorem betaOneSign_pstar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    betaOneSign (pstar p) = (if pstar p < 0 then -1 else 1) *
      (if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1) := by
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.mk hp).out).2 hp2
  unfold betaOneSign oddPartSqfree pstar
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h | h | h | h
  · have h4 : p % 4 = 1 := by omega
    simp only [h4, if_true, h, true_or]
    have : ¬ (2 : ℤ) ∣ (p : ℤ) := by omega
    simp only [this, if_false]
    have : (p : ℤ) % 8 = 1 := by omega
    simp [this]
  · have h4 : ¬ p % 4 = 1 := by omega
    simp only [h4, if_false]
    have : ¬ (2 : ℤ) ∣ -(p : ℤ) := by omega
    simp only [this, if_false]
    have : (-(p : ℤ)) % 8 = 5 := by omega
    simp [this, h]
  · have h4 : p % 4 = 1 := by omega
    simp only [h4, if_true]
    have : ¬ (2 : ℤ) ∣ (p : ℤ) := by omega
    simp only [this, if_false]
    have : (p : ℤ) % 8 = 5 := by omega
    simp [this, h]
  · have h4 : ¬ p % 4 = 1 := by omega
    simp only [h4, if_false]
    have : ¬ (2 : ℤ) ∣ -(p : ℤ) := by omega
    simp only [this, if_false]
    have : (-(p : ℤ)) % 8 = 1 := by omega
    simp [this, h]

/-- **Glue GT-H proved.** -/
theorem sqrtPstarInHilbert : SqrtPstarInHilbert := fun _ _ hn hsq _ hp =>
  adjSqrt_pstar_le_hilbertField hn hsq hp

theorem mul_two_inv_pow_five : ∀ x : Multiplicative (ZMod 2), x⁻¹ ^ 5 = x := by decide

/-- **Glue BETA-7 from genus theory** (`SqrtPstarInHilbert`, `ArtinPstarChi`, `NormP2`). -/
theorem betaOnGenus7_of (hsH : SqrtPstarInHilbert) (hart : ArtinPstarChi) (hnorm : NormP2) :
    BetaOnGenus7 := by
  intro n _ hn hsq σ γ ρ hσ hγ hρ x hx
  have h3 : n % 4 = 3 := by omega
  simp only [genusBar, NeZero.ne n, ↓reduceDIte] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyS : y ∈ genusStar n := genusField_le_genusStar h3 hsq (by omega) hy
  have hfixK : ∀ k : QNeg n, ρ (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k)) =
      embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k) := by
    intro k
    have h := hρ (algebraMap (QNeg n) (hilbertField n) k)
    rw [AlgEquiv.commutes] at h
    exact h
  set w := embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)
  have hw2 : w ^ 2 = ((-(n : ℤ) : ℤ) : Qbar) := by
    simp only [w]
    rw [← map_pow, ← map_pow]
    simp [QuadraticAlgebra.omega_pow_two_eq_add]
  have hn0 : (-(n : ℤ)) ≠ 0 := by have := NeZero.ne n; omega
  have hsqn : Squarefree (-(n : ℤ)) := sqf_neg (Int.squarefree_natCast.2 hsq)
  have hbn : betaOneSign (-(n : ℤ)) = -1 := by
    unfold betaOneSign oddPartSqfree
    have h2 : ¬ (2 : ℤ) ∣ -(n : ℤ) := by omega
    have h8 : (-(n : ℤ)) % 8 = 1 := by omega
    have hlt : -(n : ℤ) < 0 := by omega
    simp [h2, h8, hlt, NeZero.ne n]
  have hσw : σ w = -w := by
    rw [hσ _ hsqn w hw2, hbn]; simp
  have hγw : γ w = -w := by
    rw [hγ.apply_sqrt hn0 hw2, if_pos (by omega)]; simp
  have hK : ∀ k : QNeg n, σ (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k)) =
      (γ * ρ) (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k)) := by
    intro k
    rw [AlgEquiv.mul_apply, hfixK, algebraMap_eq_re_im, map_add, map_mul, AlgHom.commutes,
      AlgHom.commutes, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, map_add, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes]
    show _ + _ * σ w = _ + _ * γ w
    rw [hσw, hγw]
  have hle : genusStar n ≤ eqField n σ (γ * ρ) hK := by
    rw [genusStar, IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hp
      omega
    have hs : sqrtK (QNeg n) (pstar p) ∈ hilbertField n :=
      hsH n inferInstance h3 hsq p hp (IntermediateField.mem_adjoin_simple_self _ _)
    set r := embed n (sqrtK (QNeg n) (pstar p))
    have hr2 : r ^ 2 = ((pstar p : ℤ) : Qbar) := by
      simp only [r]; rw [← map_pow, sqrtK_sq, map_intCast]
    have hps0 : pstar p ≠ 0 := by unfold pstar; split_ifs <;> simp [hpp.ne_zero]
    rw [SetLike.mem_coe, mem_eqField, AlgEquiv.mul_apply]
    have hρr : ρ r = (if chi n ⟨p, hp⟩ (((p2Class n)⁻¹ ^ 5 : Pic (OK n))) = 1 then 1 else -1) * r := by
      have h1 := hρ ⟨_, hs⟩
      rw [hart n inferInstance h3 hsq ⟨p, hp⟩ _ hs] at h1
      rw [show r = embed n (sqrtK (QNeg n) (pstar p)) from rfl, h1, map_mul]
      split_ifs <;> simp [r]
    have hchi : chi n ⟨p, hp⟩ (((p2Class n)⁻¹ ^ 5 : Pic (OK n))) = chi n ⟨p, hp⟩ (p2Class n) := by
      erw [map_pow, map_inv, mul_two_inv_pow_five]
    have hp2' : ¬ p ∣ Ideal.absNorm (p2Ideal n) := by
      rw [hnorm n inferInstance hn]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h)
    have hchi2 : chi n ⟨p, hp⟩ (p2Class n) =
        Multiplicative.ofAdd (ZInQ.RouteK.legBit p ((2 : ℕ) : ℤ)) := by
      have := chi_mk0 n (Nat.odd_iff.mpr (by omega)) hsq ⟨p, hp⟩ ⟨p2Ideal n, p2Ideal_mem n⟩ hp2'
      rw [hnorm n inferInstance hn] at this
      exact this
    have hleg : (chi n ⟨p, hp⟩ (p2Class n) = 1) ↔ (p % 8 = 1 ∨ p % 8 = 7) := by
      haveI := Fact.mk hpp
      rw [hchi2, ← ZMod.exists_sq_eq_two_iff hp2]
      unfold ZInQ.RouteK.legBit
      split_ifs with h
      · simp only [ofAdd_zero, true_iff]; simpa using h
      · simp only [Nat.cast_ofNat, Int.cast_ofNat] at h
        simp only [h, iff_false]
        decide
    rw [hρr, map_mul, hγ.apply_sqrt hps0 hr2, hσ _ (squarefree_pstar hpp) r hr2,
      betaOneSign_pstar hpp hp2, hchi]
    by_cases hc : p % 8 = 1 ∨ p % 8 = 7
    · rw [if_pos (hleg.2 hc), if_pos hc]
      split_ifs <;> simp
    · rw [if_neg (fun h => hc (hleg.1 h)), if_neg hc]
      split_ifs <;> simp
  have := hle hyS
  rw [mem_eqField, AlgEquiv.mul_apply] at this
  exact this

end BetaAssembly

/-! ### Glue GT-ART proved: the Artin symbols act on `√p*` by the genus characters -/

section ArtinChi

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

/-- The subfield of `H_n` cut out by `S ≤ Cl(K_n)`. -/
abbrev maxSubfield (S : Subgroup (Pic (OK n))) :
    IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  IntermediateField.lift
    (IntermediateField.fixedField (S.map (ringClassArtinEquiv (OK n)).toMonoidHom))

instance (S : Subgroup (Pic (OK n))) : FiniteDimensional (QNeg n) (maxSubfield S) :=
  LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv _).toLinearEquiv

instance (S : Subgroup (Pic (OK n))) : IsGalois (QNeg n) (maxSubfield S) := by
  have : (S.map (ringClassArtinEquiv (OK n)).toMonoidHom).Normal := Subgroup.normal_of_comm _
  exact IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv _)

theorem mem_primeTo_max (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal) :
    𝔭.asIdeal ∈ integralIdealsPrimeTo (OK n).conductorModulus := by
  have := mem_primeTo_of_not_le (f := 1) 𝔭 h
  rwa [conductorOrder_one] at this

/-- The genus character as a subgroup of `Cl(K_n) = Pic(𝓞_{K_n})`. -/
abbrev kerChi (q : n.primeFactors) : Subgroup (Pic (OK n)) := (chi n q).ker

/-- Away from `2n`: `𝔭` splits in the fixed field of `ker χ_q` iff it splits in `K_n(√q*)`. -/
theorem splitSet_kerChi_iff (hn : n % 4 = 3) (hsq : Squarefree n) (q : n.primeFactors)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal)
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal) :
    𝔭 ∈ splitSet (QNeg n) (maxSubfield (kerChi q)) ↔
      𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) (pstar q)) := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hJ := mem_primeTo_max 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (OK n).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have hq2 : (q : ℕ) ≠ 2 := by
    intro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  have h2a : ((2 * pstar q : ℤ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := by
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors q.2
    have e2 : 2 * n = 2 * (q : ℕ) * n' := by rw [mul_assoc, ← hn']
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * pstar q : ℤ) : 𝓞 (QNeg n)) *
          ((if (q : ℕ) % 4 = 1 then 1 else -1 : ℤ) * n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]
      unfold pstar
      split_ifs <;> push_cast <;> ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  rw [mem_splitSet_iff (OK n) _ ⟨_, hJ⟩ 𝔭 rfl]
  change chi n q ((OK n).picClass ⟨_, hJ⟩) = 1 ↔ _
  rw [picClass_maximal ⟨_, hJ⟩ (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot),
    mem_splitSet_adjSqrt_iff 𝔭 h2a]
  have := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharq⟩ := residue_facts 𝔭 h2n q.2
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
      (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    rw [hcard] at hd
    exact hcharq ((Nat.prime_dvd_prime_iff_eq hqp hk).1 (hqp.dvd_of_dvd_pow hd)).symm
  have hc := chi_mk0 n hodd hsq q ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ hqN
  rw [hc, isSquare_pstar_iff hchar hq2 hcharq]
  unfold ZInQ.RouteK.legBit
  rw [hN, Int.cast_natCast]
  split_ifs with h
  · simp only [ofAdd_zero, true_iff]; exact h
  · simp only [h, iff_false]; decide

/-- **The fixed field of `ker χ_q` is `K_n(√q*)`** (Bauer, both directions). -/
theorem maxSubfield_kerChi (hn : n % 4 = 3) (hsq : Squarefree n) (q : n.primeFactors) :
    maxSubfield (kerChi q) = adjSqrt (QNeg n) (pstar q) := by
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by have := NeZero.ne n; omega)
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 (QNeg n)),
      𝔭 ∉ {𝔭 : HeightOneSpectrum (𝓞 (QNeg n)) | (conductorOrder (QNeg n) 1).conductor *
        Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≤ 𝔭.asIdeal} →
      (𝔭 ∈ splitSet (QNeg n) (maxSubfield (kerChi q)) ↔
        𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) (pstar q))) := fun 𝔭 hT =>
    splitSet_kerChi_iff hn hsq q 𝔭 (fun h => hT (le_trans Ideal.mul_le_left h))
      (fun h => hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h)))
  apply le_antisymm
  · exact le_of_splitSet_diff_subset _ (finite_le_primes _ hI)
      fun 𝔭 ⟨h𝔭, hT⟩ => (key 𝔭 hT).2 h𝔭
  · exact le_of_splitSet_diff_subset _ (finite_le_primes _ hI)
      fun 𝔭 ⟨h𝔭, hT⟩ => (key 𝔭 hT).1 h𝔭

/-- **Glue GT-ART proved.** -/
theorem artinPstarChi : ArtinPstarChi := by
  intro n _ hn hsq q c hs
  set s := sqrtK (QNeg n) (pstar q)
  set g := ringClassArtinEquiv (OK n) c
  set s' : hilbertField n := ⟨s, hs⟩
  have hs2 : s' ^ 2 = algebraMap (QNeg n) (hilbertField n) ((pstar q : ℤ) : QNeg n) := by
    apply Subtype.ext
    show s ^ 2 = algebraMap (QNeg n) (SeparableClosure (QNeg n)) ((pstar q : ℤ) : QNeg n)
    rw [sqrtK_sq, map_intCast]
  have hg2 : ((g s' : hilbertField n) : SeparableClosure (QNeg n)) ^ 2 = s ^ 2 := by
    have h0 : (g s') ^ 2 = algebraMap (QNeg n) (hilbertField n) ((pstar q : ℤ) : QNeg n) := by
      rw [← map_pow, hs2, AlgEquiv.commutes]
    have h' := congrArg Subtype.val h0
    change ((g s' : hilbertField n) : SeparableClosure (QNeg n)) ^ 2 =
      algebraMap (QNeg n) (SeparableClosure (QNeg n)) ((pstar q : ℤ) : QNeg n) at h'
    rw [h', map_intCast, sqrtK_sq]
  have hmemE : s ∈ maxSubfield (kerChi q) := by
    rw [maxSubfield_kerChi hn hsq q]; exact IntermediateField.mem_adjoin_simple_self _ _
  have hfix_iff : g s' = s' ↔ chi n q c = 1 := by
    constructor
    · intro hfix
      have hle : adjSqrt (QNeg n) (pstar q) ≤
          IntermediateField.lift (IntermediateField.fixedField (Subgroup.zpowers g)) := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact mem_lift_fixedField_zpowers g s' hfix
      rw [← maxSubfield_kerChi hn hsq q] at hle
      have hle' : IntermediateField.fixedField ((kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom) ≤
          IntermediateField.fixedField (Subgroup.zpowers g) := fun x hx =>
        (IntermediateField.mem_lift x).1 (hle ((IntermediateField.mem_lift x).2 hx))
      have hZ : Subgroup.zpowers g ≤ (kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom := by
        rw [← IntermediateField.fixingSubgroup_fixedField
          ((kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom)]
        exact (IntermediateField.le_iff_le _ _).1 (le_trans hle' le_rfl)
      obtain ⟨c', hc', hce⟩ := Subgroup.mem_map.1 (hZ (Subgroup.mem_zpowers g))
      rw [(ringClassArtinEquiv (OK n)).injective hce] at hc'
      exact hc'
    · intro hc
      have h1 := (IntermediateField.mem_lift s').1 hmemE
      rw [IntermediateField.mem_fixedField_iff] at h1
      exact h1 g (Subgroup.mem_map_of_mem _ hc)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hg2 with h | h
  · have hc : chi n q c = 1 := hfix_iff.1 (Subtype.ext h)
    rw [h, if_pos hc, one_mul]
  · have hc : chi n q c ≠ 1 := by
      intro hc
      have h' := congrArg Subtype.val (hfix_iff.2 hc)
      rw [h] at h'
      have h2 : (2 : SeparableClosure (QNeg n)) * s = 0 := by
        change -s = s at h'; linear_combination -h'
      have hs0 : s ≠ 0 := by
        intro h0
        have := sqrtK_sq (QNeg n) (pstar q)
        rw [← show s = sqrtK (QNeg n) (pstar q) from rfl, h0] at this
        have hp0 : pstar q ≠ 0 := by
          unfold pstar; split_ifs <;> simp [(Nat.prime_of_mem_primeFactors q.2).ne_zero]
        simp at this
        exact hp0 (by exact_mod_cast this.symm)
      rcases mul_eq_zero.1 h2 with h2 | h2
      · exact two_ne_zero h2
      · exact hs0 h2
    rw [h, if_neg hc]; ring

end ArtinChi

/-! ### Glue NORM-2 proved: `N𝔭₂ = 2` -/

section NormTwo

open ZInQ.RouteK.Redei

/-- An element of `𝓞_{K_n}` (`n` odd) with imaginary part `±1/2` is not divisible by `2`. -/
theorem not_two_dvd_of_im {n : ℕ} [NeZero n] (hn : n % 2 = 1) {v : 𝓞 (QNeg n)}
    (hv : (v : QNeg n).im = 1 / 2 ∨ (v : QNeg n).im = -1 / 2) : ¬ ∃ w : 𝓞 (QNeg n), v = 2 * w := by
  rintro ⟨w, rfl⟩
  obtain ⟨k, hk⟩ := exists_two_re (w * sqrtNeg n)
  have hre : ((w * sqrtNeg n : 𝓞 (QNeg n)) : QNeg n).re = -(n : ℚ) * (w : QNeg n).im := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg]
  have him : ((2 * w : 𝓞 (QNeg n)) : QNeg n).im = 2 * (w : QNeg n).im := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_ofNat]
    simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  rw [hre] at hk
  rw [him] at hv
  have hn' : (n : ℚ) = 2 * (n / 2 : ℕ) + 1 := by
    have : n = 2 * (n / 2) + 1 := by omega
    exact_mod_cast this
  rcases hv with h | h
  · have hw : (w : QNeg n).im = 1 / 4 := by linarith
    rw [hw] at hk
    have : (k : ℚ) = -(n : ℚ) / 2 := by linarith
    have h3 : ((n : ℤ) : ℚ) = ((-2 * k : ℤ) : ℚ) := by push_cast; linarith
    have h4 : (n : ℤ) = -2 * k := Int.cast_injective h3
    omega
  · have hw : (w : QNeg n).im = -1 / 4 := by linarith
    rw [hw] at hk
    have : (k : ℚ) = (n : ℚ) / 2 := by linarith
    have h3 : ((n : ℤ) : ℚ) = ((2 * k : ℤ) : ℚ) := by push_cast; linarith
    have h4 : (n : ℤ) = 2 * k := Int.cast_injective h3
    omega

/-- **Glue NORM-2 proved**: `(2) = 𝔭₂ 𝔭̄₂` with `𝔭₂, 𝔭̄₂ ≠ (1)`, so `N𝔭₂ = 2`. -/
theorem normP2 : NormP2 := by
  intro n _ hn
  have h3 : n % 4 = 3 := by omega
  have hδ := tyzDelta_spec hn
  set δ := tyzDelta n
  have hδodd : δ % 2 = 1 := by
    rcases Nat.even_or_odd δ with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso; rw [hk] at hδ; ring_nf at hδ; omega
    · omega
  set m := (δ + 1) / 2
  have hm : 2 * m = δ + 1 := by omega
  set N1 := (δ * δ + n) / 8
  have hN1 : 8 * N1 = δ * δ + n := by omega
  set θ := thetaO n h3
  set u : 𝓞 (QNeg n) := θ - (m : 𝓞 (QNeg n))
  set ub : 𝓞 (QNeg n) := 1 - θ - (m : 𝓞 (QNeg n))
  have hprod : u * ub = 2 * (N1 : 𝓞 (QNeg n)) := by
    have h2θ := two_mul_thetaO n h3
    have hω := omegaO_sq n
    have hmc : (2 : 𝓞 (QNeg n)) * m = δ + 1 := by exact_mod_cast hm
    have hNc : (8 : 𝓞 (QNeg n)) * N1 = δ * δ + n := by exact_mod_cast hN1
    have h8 : (4 : 𝓞 (QNeg n)) * (u * ub) = 8 * (N1 : 𝓞 (QNeg n)) := by
      rw [hNc]
      simp only [u, ub]
      linear_combination (1 - omegaO n - 2 * θ) * h2θ + ((δ : 𝓞 (QNeg n)) + 2 * m - 1) * hmc - hω
    have h4 : (4 : 𝓞 (QNeg n)) * (u * ub) = 4 * (2 * (N1 : 𝓞 (QNeg n))) := by rw [h8]; ring
    have h40 : (4 : 𝓞 (QNeg n)) ≠ 0 := fun h => by
      have h' := congrArg (algebraMap (𝓞 (QNeg n)) (QNeg n)) h
      rw [map_ofNat, map_zero] at h'
      norm_num at h'
    exact mul_left_cancel₀ h40 h4
  have hodd : n % 2 = 1 := by omega
  have himu : (u : QNeg n).im = 1 / 2 := by
    simp only [u, θ, map_sub, RingOfIntegers.coe_eq_algebraMap, algebraMap_thetaO, theta_eq, map_natCast]
    simp
  have himub : (ub : QNeg n).im = -1 / 2 := by
    simp only [ub, θ, map_sub, RingOfIntegers.coe_eq_algebraMap, algebraMap_thetaO, theta_eq, map_natCast,
      map_one]
    simp [QuadraticAlgebra.im_one]; norm_num
  have hP : p2Ideal n = Ideal.span {2, u} ∨ p2Ideal n = Ideal.span {2, ub} := by
    unfold p2Ideal
    split_ifs
    · left; rfl
    · right; rfl
  have hmul : Ideal.span {2, u} * Ideal.span {2, ub} = Ideal.span {(2 : 𝓞 (QNeg n))} := by
    apply le_antisymm
    · rw [Ideal.mul_le]
      intro x hx y hy
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hx
      obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hy
      rw [Ideal.mem_span_singleton]
      refine ⟨a * c * 2 + a * d * ub + b * c * u + b * d * N1, ?_⟩
      linear_combination (b * d) * hprod
    · rw [Ideal.span_singleton_le_iff_mem]
      have h1 : u * 2 ∈ Ideal.span {2, u} * Ideal.span {2, ub} :=
        Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      have h2 : 2 * ub ∈ Ideal.span {2, u} * Ideal.span {2, ub} :=
        Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      have h4 : 2 * 2 ∈ Ideal.span {2, u} * Ideal.span {2, ub} :=
        Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      have := add_mem (add_mem h1 h2) (Ideal.mul_mem_right (m : 𝓞 (QNeg n)) _ h4)
      convert this using 1
      simp only [u, ub]; ring
  have hne1 : Ideal.span {2, u} ≠ ⊤ := by
    intro h
    have h1 : (1 : 𝓞 (QNeg n)) ∈ Ideal.span {2, u} := by rw [h]; trivial
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h1
    apply not_two_dvd_of_im hodd (Or.inr himub)
    refine ⟨a * ub + b * N1, ?_⟩
    linear_combination (-ub) * hab + b * hprod
  have hne2 : Ideal.span {2, ub} ≠ ⊤ := by
    intro h
    have h1 : (1 : 𝓞 (QNeg n)) ∈ Ideal.span {2, ub} := by rw [h]; trivial
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h1
    apply not_two_dvd_of_im hodd (Or.inl himu)
    refine ⟨a * u + b * N1, ?_⟩
    linear_combination (-u) * hab + b * hprod
  have hN2 : Ideal.absNorm (Ideal.span {(2 : 𝓞 (QNeg n))}) = 4 := by
    rw [Ideal.absNorm_span_singleton]
    have h := normZ_eq_re_im (2 : 𝓞 (QNeg n))
    have hr : ((2 : 𝓞 (QNeg n)) : QNeg n).re = 2 := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_ofNat]; rfl
    have hi : ((2 : 𝓞 (QNeg n)) : QNeg n).im = 0 := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_ofNat]; rfl
    rw [hr, hi] at h
    have : Algebra.norm ℤ (2 : 𝓞 (QNeg n)) = 4 := by exact_mod_cast (by linarith : ((Algebra.norm ℤ (2 : 𝓞 (QNeg n)) : ℤ) : ℚ) = 4)
    rw [this]; rfl
  have hab := congrArg Ideal.absNorm hmul
  rw [map_mul, hN2] at hab
  have ha1 : Ideal.absNorm (Ideal.span {2, u}) ≠ 1 := fun h => hne1 (Ideal.absNorm_eq_one_iff.1 h)
  have hb1 : Ideal.absNorm (Ideal.span {2, ub}) ≠ 1 := fun h => hne2 (Ideal.absNorm_eq_one_iff.1 h)
  set a := Ideal.absNorm (Ideal.span {2, u})
  set b := Ideal.absNorm (Ideal.span {2, ub})
  have ha4 : a ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨b, hab.symm⟩
  have hb4 : b ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨a, by rw [mul_comm]; exact hab.symm⟩
  have ha2 : a = 2 := by interval_cases a <;> omega
  have hb2 : b = 2 := by interval_cases b <;> omega
  rcases hP with hP | hP
  · rw [hP]; exact ha2
  · rw [hP]; exact hb2

end NormTwo

/-- **Glue BETA-7 proved** (from genus theory: `sqrtPstarInHilbert`, `artinPstarChi`, `normP2`). -/
theorem betaOnGenus7 : BetaOnGenus7 := betaOnGenus7_of sqrtPstarInHilbert artinPstarChi normP2

/-- **`Lemma321Seven` from TYZ Theorem 3.6(3)** (and the CM field of definition); no glue left. -/
theorem lemma321Seven_of' (hcm : CMFieldOfDefinition7) (h36 : TYZThm36Seven) : Lemma321Seven :=
  lemma321Seven_of hcm h36 betaOnGenus7

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem after §10–§12** (`Lemma321Seven` replaced by TYZ Thm 3.6(3) + glue BETA-7). -/
theorem tyzThm35ReadingA_of_cmLeaves7' (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CM.CMFieldOfDefinition ringClassFieldD)
    (hsh : TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h36 : TYZThm36Seven) (hb : BetaOnGenus7) :
    ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves7 h11 h1 h29 hcm hsh h318 h35 h5
    (lemma321Seven_of (cmFieldOfDefinition7_of hcm) h36 hb)



/-! ## §14. `TYZThm36Seven` from Shimura reciprocity, the Fricke involution and algebraicity

TYZ's proof of Theorem 3.6(3) (L1799–1855: Prop. 3.9, `j ϖ^5 ∈ W·U₀(32)_2`) in Gross's language:
`Art([𝔭₂]^{−5})` sends the Heegner point of `Q = [(n+δ²)/4, δ, 1]` (class `[1]`) to that of
`Q' = [32, δ, (n+δ²)/128]` (class `[𝔭₂]^5`), and `τ_{Q'} = W τ_{Q̄}`, `W τ = −1/(32τ)`, so
`z_{Q'} = T − z̄_n` by the Fricke leaf. Inputs: tyz-cm's leaf `ShimuraReciprocityPic` (copied verbatim
below), x0-32's leaf `X0.EtaModelFricke`, cm-points' leaf `CM.CMAlgebraic` (the Heegner points exist
as algebraic points; `TYZThm36Seven` is not junk-safe) and cm-points' theorem `cmComplexConj`.
Numerical backbone: `plan36.out`. -/

namespace TyzCm

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

/-! Verbatim copy of tyz-cm's leaf and its definitions (branch `wip/tyz-cm`, commit `66d92d11`,
`ZInQKernel/Contrib/TYZGenus/ShimuraRecip.lean`, namespace `ZInQ.Contrib.TYZGenus.Shimura`). -/


/-- The normalized complex embedding `κ : ℚ(√−m) → ℂ`, `a + b√−m ↦ a + b·i√m` (as a function). -/
def kappa (m : ℕ) (x : QNeg m) : ℂ := (x.re : ℂ) + (x.im : ℂ) * (I * (Real.sqrt m : ℂ))

/-- The set `J ∩ O ⊂ K` for an ideal `J` of `𝓞_K` and the order `O = ℤ + f𝓞_K`. -/
def idealMeetOrder (m f : ℕ) [NeZero m] [NeZero f] (J : Ideal (𝓞 (QNeg m))) : Set (QNeg m) :=
  {x | x ∈ (conductorOrder (QNeg m) f).toSubalgebra ∧ ∃ y ∈ J, (y : QNeg m) = x}

/-- The lattice `κ(J ∩ O) ⊂ ℂ` (the `ℤ`-span of the image; `J ∩ O` is already a `ℤ`-module). -/
def idealLat (m f : ℕ) [NeZero m] [NeZero f] (J : Ideal (𝓞 (QNeg m))) : Submodule ℤ ℂ :=
  Submodule.span ℤ (kappa m '' idealMeetOrder m f J)

/-- The discriminant `f²·d_K` of `ℤ + f𝓞_K` in `K = ℚ(√−m)`, `m` squarefree:
`d_K = −m` for `m ≡ 3 (mod 4)` and `d_K = −4m` otherwise. -/
def discOf (m f : ℕ) : ℤ := if m % 4 = 3 then -((f : ℤ) ^ 2 * m) else -(4 * (f : ℤ) ^ 2 * m)

/-- **Leaf SHIMURA-PIC (main theorem of complex multiplication for Heegner points of `X₀(32)`,
Gross's form).** Let `K = ℚ(√−m)` (`m` squarefree), `O = ℤ + f𝓞_K` the order of discriminant `D`,
`H_O` its ring class field, and `e : Kˢ → ℚ̄` an embedding inducing on `K` the normalized complex
embedding `√−m ↦ i√m` (through cm-points' `ιC : ℚ̄ → ℂ`). Let `J` be an ideal of `𝓞_K` prime to
`f`, and `ρ ∈ Gal(ℚ̄/ℚ)` an automorphism acting on `e(H_O)` as the Artin symbol of the class of
`J ∩ O`. Then for Heegner forms `Q, Q'` of level 32 and discriminant `D` whose pairs of lattices
satisfy `κ(J ∩ O)·(⟨1,τ_{Q'}⟩, ⟨1/32,τ_{Q'}⟩) = c·(⟨1,τ_Q⟩, ⟨1/32,τ_Q⟩)` for one `c ∈ ℂ`
(i.e. `(L', L'_N) = c·(J∩O)⁻¹(L, L_N)`), `ρ` maps the Heegner point of `Q` to that of `Q'`:
`Art(𝔟)(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔟⁻¹𝔞])`.

Sources (refereed; theorem numbers UNVERIFIED, from memory, no network on this host):
the main theorem of complex multiplication, Shimura, *Introduction to the arithmetic theory of
automorphic functions* (1971), Thm. 5.4 (`E^{[s,K]} ≅ ℂ/s⁻¹𝔞`, with the action on torsion
`f(t)^σ = f'(s⁻¹t)`, which gives the action on the cyclic subgroup `L_N/L`); Silverman, *Advanced
topics in the arithmetic of elliptic curves*, GTM 151, Thm. II.8.2; Gross, *Heegner points on
`X₀(N)`*, in *Modular forms* (Durham 1983), 1984, §3 (`σ_𝔟(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔞𝔟⁻¹])`);
Cox, *Primes of the form x² + ny²*, Thm. 11.1 and Cor. 11.37 (the `j`-part). Normalization: the
idele `s` with `s_𝔭` a uniformizer has `[s, K] = ` arithmetic Frobenius (Tau Ceti's Artin map), so
`Art(J)` corresponds to `s⁻¹𝔞 = J⁻¹𝔞`. The theorem holds for every lattice pair (Shimura's form
needs no condition on the orders of `L` and `L_N`), so no Heegner condition `(f, 32) = 1` is
needed. It is stated through x0-32's eta-quotient model `X0.phiC` and cm-points' `ιC`, so it is
true because (and only if) that model is the `ℚ`-rational modular parametrization of `X₀(32)`
(x0-32's leaves `X0.X0AnalyticModel`; Shimura 1971 Ch. 6–7 for the canonical model). -/
def ShimuraReciprocityPic : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm 32 D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      galPt ρ (heegnerPt Q) = heegnerPt Q'

end TyzCm

section Thm36

open TyzCm Complex
open scoped nonZeroDivisors

/-! Helpers copied from tyz-cm's `ShimuraZn.lean` (same branch). -/

theorem sqrt_mul_self_C (m : ℕ) : (Real.sqrt m : ℂ) * Real.sqrt m = m := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg m)]; simp

/-- `i√m` as a root of `X² + m` in `ℂ`. -/
def kappaRoot (m : ℕ) : {u : ℂ // u * u = (-(m : ℚ)) • (1 : ℂ) + (0 : ℚ) • u} :=
  ⟨I * Real.sqrt m, by
    rw [show I * (Real.sqrt m : ℂ) * (I * Real.sqrt m) = (I * I) * (Real.sqrt m * Real.sqrt m) by ring,
      I_mul_I, sqrt_mul_self_C]
    simp [Rat.smul_def]⟩

/-- `κ` as a `ℚ`-algebra map. -/
def kappaAlg (m : ℕ) : QNeg m →ₐ[ℚ] ℂ := QuadraticAlgebra.lift (kappaRoot m)

theorem kappaAlg_apply (m : ℕ) (x : QNeg m) : kappaAlg m x = kappa m x := by
  simp [kappaAlg, kappa, kappaRoot, Rat.smul_def]

/-- `κ` as a `ℤ`-algebra map. -/
def kappaZ (m : ℕ) : QNeg m →ₐ[ℤ] ℂ := (kappaAlg m).restrictScalars ℤ

/-- `κ` as a `ℤ`-linear map. -/
def kappaLin (m : ℕ) : QNeg m →ₗ[ℤ] ℂ := (kappaZ m).toLinearMap

theorem kappaLin_apply (m : ℕ) (x : QNeg m) : kappaLin m x = kappa m x := kappaAlg_apply m x

theorem kappaLin_one (m : ℕ) : kappaLin m 1 = 1 := map_one (kappaZ m)

theorem map_mulLeft_span_pair (m : ℕ) (c a b : QNeg m) :
    ((Submodule.span ℤ {a, b}).map (kappaLin m)).map (LinearMap.mulLeft ℤ (kappa m c)) =
      (Submodule.span ℤ {c * a, c * b}).map (kappaLin m) := by
  simp only [Submodule.map_span, Set.image_pair, LinearMap.mulLeft_apply, kappaLin_apply]
  rw [← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply,
    map_mul, map_mul]

variable {n : ℕ} [NeZero n]

/-- `1/32 ∈ K`. -/
def oneN32 (n : ℕ) : QNeg n := ⟨1 / 32, 0⟩

omit [NeZero n] in
@[simp] theorem oneN32_re : (oneN32 n).re = 1 / 32 := rfl
omit [NeZero n] in
@[simp] theorem oneN32_im : (oneN32 n).im = 0 := rfl

theorem kappa_oneN32 : kappaLin n (oneN32 n) = 1 / ((32 : ℕ) : ℂ) := by
  rw [kappaLin_apply, kappa]; simp

theorem lat_eq_map' {D : ℤ} (Q : HeegnerForm 32 D) (t : QNeg n) (ht : Q.tau = kappa n t) :
    Q.lat = (Submodule.span ℤ {1, t}).map (kappaLin n) := by
  rw [HeegnerForm.lat, Submodule.map_span, Set.image_pair, kappaLin_one, kappaLin_apply, ht]

theorem latN_eq_map' {D : ℤ} (Q : HeegnerForm 32 D) (t : QNeg n) (ht : Q.tau = kappa n t) :
    Q.latN = (Submodule.span ℤ {oneN32 n, t}).map (kappaLin n) := by
  rw [HeegnerForm.latN, Submodule.map_span, Set.image_pair, kappa_oneN32, kappaLin_apply, ht]

/-- **Integer coordinates in `𝓞_K`, `n ≡ 3 (mod 4)` squarefree**: `y = (s + t√−n)/2`, `s ≡ t (2)`. -/
theorem int_coords3 (hn : n % 4 = 3) (hsq : Squarefree n) (y : 𝓞 (QNeg n)) :
    ∃ s t : ℤ, (y : QNeg n).re = s / 2 ∧ (y : QNeg n).im = t / 2 ∧ ∃ k : ℤ, s = t + 2 * k := by
  obtain ⟨a, ha⟩ := exists_two_re y
  obtain ⟨b, hb⟩ := exists_two_re (y * sqrtNeg n)
  have hN := normZ_eq_re_im y
  set N := Algebra.norm ℤ y
  set r := (y : QNeg n).re
  set s := (y : QNeg n).im
  have hb' : 2 * (-(n : ℚ) * s) = b := by
    rw [← hb]; simp [coe_sqrtNeg, s]
  have hnt : (n : ℚ) * (2 * s) = -b := by linarith
  have h4 : (a : ℚ) ^ 2 + n * (2 * s) ^ 2 = 4 * N := by
    rw [hN, ← ha]; ring
  have hdiv : (n : ℤ) ∣ b ^ 2 := by
    refine ⟨a ^ 2 * 0 + (4 * N - a ^ 2), ?_⟩
    have : (b : ℚ) ^ 2 = n * (4 * N - a ^ 2) := by
      have : (b : ℚ) ^ 2 = (n * (2 * s)) ^ 2 := by rw [hnt]; ring
      rw [this]; linear_combination (n : ℚ) * h4
    exact_mod_cast (by rw [this]; ring : (b : ℚ) ^ 2 = n * (a ^ 2 * 0 + (4 * N - a ^ 2)))
  have hsqZ : Squarefree (n : ℤ) := Int.squarefree_natCast.mpr hsq
  obtain ⟨t, ht⟩ := (hsqZ.dvd_pow_iff_dvd two_ne_zero).1 hdiv
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hs2 : 2 * s = -t := by
    have : (n : ℚ) * (2 * s) = n * (-t) := by rw [hnt, ht]; push_cast; ring
    exact mul_left_cancel₀ hn0 this
  have hZ : a ^ 2 + (n : ℤ) * t ^ 2 = 4 * N := by
    have : (a : ℚ) ^ 2 + n * t ^ 2 = 4 * N := by rw [← h4, hs2]; ring
    exact_mod_cast this
  have hn' : (n : ℤ) = 4 * ((n : ℤ) / 4) + 3 := by omega
  have hpar : 2 ∣ a + t := by
    rw [hn'] at hZ
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' a <;> obtain ⟨l, hl | hl⟩ := Int.even_or_odd' t <;>
      subst hk hl
    · exact ⟨k + l, by ring⟩
    · exfalso; ring_nf at hZ; omega
    · exfalso; ring_nf at hZ; omega
    · exact ⟨k + l + 1, by ring⟩
  obtain ⟨k, hk⟩ := hpar
  refine ⟨a, -t, by rw [← ha]; ring, by push_cast; linarith, k, by linarith⟩

end Thm36


section Thm36b

open TyzCm Complex
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

theorem int_dvd_n_delta {n : ℕ} (hn : n % 8 = 7) : (128 : ℤ) ∣ (n : ℤ) + (tyzDelta n : ℤ) ^ 2 :=
  tyzDelta_dvd hn

theorem delta_odd {n : ℕ} (hn : n % 8 = 7) : ∃ d : ℤ, (tyzDelta n : ℤ) = 2 * d + 1 := by
  have h := tyzDelta_dvd hn
  obtain ⟨d, hd | hd⟩ := Int.even_or_odd' (tyzDelta n : ℤ)
  · exfalso
    rw [hd] at h
    obtain ⟨c, hc⟩ := h
    have : (n : ℤ) = 128 * c - 4 * d ^ 2 := by linear_combination hc
    omega
  · exact ⟨d, hd⟩

/-- `Q' = [32, δ, (n+δ²)/128]` (level 32, discriminant `−n`; class `[𝔭₂]^5`, `τ_{Q'} = W τ_{Q̄}`). -/
def tyzForm7' (n : ℕ) (hn : n % 8 = 7) : HeegnerForm 32 (-(n : ℤ)) where
  A := 32
  B := tyzDelta n
  C := ((n : ℤ) + (tyzDelta n : ℤ) ^ 2) / 128
  A_pos := by norm_num
  N_dvd := by norm_num
  disc := by
    have := tyzDelta_dvd hn
    omega
  D_neg := by
    have : (0 : ℤ) < n := by have : 0 < n := by omega
                             exact_mod_cast this
    omega
  primitive := by
    obtain ⟨d, hd⟩ := delta_odd hn
    have h2 : IsCoprime (2 : ℤ) (tyzDelta n : ℤ) := ⟨-d, 1, by rw [hd]; ring⟩
    have h32 : Int.gcd 32 (tyzDelta n : ℤ) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.1 (by simpa using h2.pow_left (m := 5))
    rw [h32]; simp

/-- `A = (n + δ²)/4 ∈ ℤ`. -/
abbrev A7 (n : ℕ) : ℤ := ((n : ℤ) + (tyzDelta n : ℤ) ^ 2) / 4
/-- `N₄ = (n + δ²)/128 ∈ ℤ`. -/
abbrev N7 (n : ℕ) : ℤ := ((n : ℤ) + (tyzDelta n : ℤ) ^ 2) / 128

theorem four_A7 {n : ℕ} (hn : n % 8 = 7) : 4 * A7 n = (n : ℤ) + (tyzDelta n : ℤ) ^ 2 := by
  have := tyzDelta_dvd hn; simp only [A7]; omega

theorem A7_eq {n : ℕ} (hn : n % 8 = 7) : A7 n = 32 * N7 n := by
  have := tyzDelta_dvd hn; simp only [A7, N7]; omega

theorem A7_pos {n : ℕ} (hn : n % 8 = 7) : (0 : ℚ) < A7 n := by
  have h := four_A7 hn
  have : (0 : ℤ) < n := by have : 0 < n := by omega
                           exact_mod_cast this
  have : (0 : ℤ) < A7 n := by nlinarith [sq_nonneg (tyzDelta n : ℤ)]
  exact_mod_cast this

/-! Elements of `K = ℚ(√−n)` (coordinates `⟨re, im⟩`, `ω = √−n`). -/

/-- `u = (√−n − δ)/2`. -/
def uK (n : ℕ) : QNeg n := ⟨-(tyzDelta n : ℚ) / 2, 1 / 2⟩
/-- `ū = (−√−n − δ)/2`. -/
def ubK (n : ℕ) : QNeg n := ⟨-(tyzDelta n : ℚ) / 2, -1 / 2⟩
/-- `τ_Q = (−δ + √−n)/(2A)`. -/
def tK (n : ℕ) : QNeg n := ⟨-(tyzDelta n : ℚ) / (2 * A7 n), 1 / (2 * A7 n)⟩
/-- `τ_{Q̄} = (δ + √−n)/(2A)`. -/
def tbK (n : ℕ) : QNeg n := ⟨(tyzDelta n : ℚ) / (2 * A7 n), 1 / (2 * A7 n)⟩
/-- `τ_{Q'} = (−δ + √−n)/64`. -/
def t'K (n : ℕ) : QNeg n := ⟨-(tyzDelta n : ℚ) / 64, 1 / 64⟩
/-- `τ_{Q̄'} = (δ + √−n)/64`. -/
def tb'K (n : ℕ) : QNeg n := ⟨(tyzDelta n : ℚ) / 64, 1 / 64⟩

theorem sqrt_negn (n : ℕ) : Real.sqrt (-(((-(n : ℤ)) : ℤ) : ℝ)) = Real.sqrt n := by
  congr 1; push_cast; ring

theorem tyzForm7_tau (hn : n % 8 = 7) : (tyzForm7 n hn).tau = kappa n (tK n) := by
  have hA : (A7 n : ℂ) ≠ 0 := by exact_mod_cast (A7_pos hn).ne'
  simp only [HeegnerForm.tau, cmPoint, tyzForm7, kappa, tK, sqrt_negn]
  push_cast
  field_simp
  try ring

theorem tyzForm7_conj_tau (hn : n % 8 = 7) : (tyzForm7 n hn).conj.tau = kappa n (tbK n) := by
  have hA : (A7 n : ℂ) ≠ 0 := by exact_mod_cast (A7_pos hn).ne'
  simp only [HeegnerForm.tau, HeegnerForm.conj, cmPoint, tyzForm7, kappa, tbK, sqrt_negn]
  push_cast
  field_simp
  try ring

theorem tyzForm7'_tau (hn : n % 8 = 7) : (tyzForm7' n hn).tau = kappa n (t'K n) := by
  simp only [HeegnerForm.tau, cmPoint, tyzForm7', kappa, t'K, sqrt_negn]
  push_cast
  field_simp
  try ring

theorem tyzForm7'_conj_tau (hn : n % 8 = 7) : (tyzForm7' n hn).conj.tau = kappa n (tb'K n) := by
  simp only [HeegnerForm.tau, HeegnerForm.conj, cmPoint, tyzForm7', kappa, tb'K, sqrt_negn]
  push_cast
  field_simp
  try ring

/-! Relations in `K`. -/

theorem ubK_mul_tK (hn : n % 8 = 7) : ubK n * tK n = 1 := by
  have h4 : (4 : ℚ) * A7 n = n + (tyzDelta n : ℚ) ^ 2 := by exact_mod_cast four_A7 hn
  have hA : (A7 n : ℚ) ≠ 0 := (A7_pos hn).ne'
  ext <;> simp [ubK, tK, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;>
    first | linear_combination (-1 : ℚ) * h4 | linear_combination h4 | linear_combination (-1/2 : ℚ) * h4 | linear_combination (1/2 : ℚ) * h4 | ring1

theorem neg_uK_mul_tbK (hn : n % 8 = 7) : -uK n * tbK n = 1 := by
  have h4 : (4 : ℚ) * A7 n = n + (tyzDelta n : ℚ) ^ 2 := by exact_mod_cast four_A7 hn
  have hA : (A7 n : ℚ) ≠ 0 := (A7_pos hn).ne'
  ext <;> simp [uK, tbK, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;>
    first | linear_combination (-1 : ℚ) * h4 | linear_combination h4 | linear_combination (-1/2 : ℚ) * h4 | linear_combination (1/2 : ℚ) * h4 | ring1

theorem thirtytwo_t'K : (32 : QNeg n) * t'K n = uK n := by
  ext <;> simp [uK, t'K, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

theorem thirtytwo_tb'K : (32 : QNeg n) * tb'K n = -ubK n := by
  ext <;> simp [ubK, tb'K, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

theorem ubK_mul_t'K (hn : n % 8 = 7) : ubK n * t'K n = (N7 n : QNeg n) := by
  have h4 : (4 : ℚ) * A7 n = n + (tyzDelta n : ℚ) ^ 2 := by exact_mod_cast four_A7 hn
  have hA : (A7 n : ℚ) = 32 * N7 n := by exact_mod_cast A7_eq hn
  ext <;> simp [ubK, t'K] <;>
    first | linear_combination (-1/128 : ℚ) * h4 + (1/32 : ℚ) * hA | linear_combination (1/128 : ℚ) * h4 - (1/32 : ℚ) * hA | linear_combination (-1/64 : ℚ) * h4 + (1/16 : ℚ) * hA | linear_combination (1/64 : ℚ) * h4 - (1/16 : ℚ) * hA | ring1

theorem uK_mul_tb'K (hn : n % 8 = 7) : uK n * tb'K n = -(N7 n : QNeg n) := by
  have h4 : (4 : ℚ) * A7 n = n + (tyzDelta n : ℚ) ^ 2 := by exact_mod_cast four_A7 hn
  have hA : (A7 n : ℚ) = 32 * N7 n := by exact_mod_cast A7_eq hn
  ext <;> simp [uK, tb'K] <;>
    first | linear_combination (-1/128 : ℚ) * h4 + (1/32 : ℚ) * hA | linear_combination (1/128 : ℚ) * h4 - (1/32 : ℚ) * hA | linear_combination (-1/64 : ℚ) * h4 + (1/16 : ℚ) * hA | linear_combination (1/64 : ℚ) * h4 - (1/16 : ℚ) * hA | ring1

end Thm36b


section Thm36c

open TyzCm Complex
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

theorem n_delta_q {n : ℕ} (hn : n % 8 = 7) : (n : ℚ) + (tyzDelta n : ℚ) ^ 2 = 128 * N7 n := by
  have h1 : (4 : ℚ) * A7 n = n + (tyzDelta n : ℚ) ^ 2 := by exact_mod_cast four_A7 hn
  have h2 : (A7 n : ℚ) = 32 * N7 n := by exact_mod_cast A7_eq hn
  linarith

theorem ubK_sq (hn : n % 8 = 7) :
    ubK n * ubK n = -(tyzDelta n : QNeg n) * ubK n - 32 * (N7 n : QNeg n) := by
  have h := n_delta_q hn
  ext <;> simp [ubK, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    first | linear_combination (1/4 : ℚ) * h | linear_combination (-1/4 : ℚ) * h | ring1

theorem uK_sq (hn : n % 8 = 7) :
    uK n * uK n = -(tyzDelta n : QNeg n) * uK n - 32 * (N7 n : QNeg n) := by
  have h := n_delta_q hn
  ext <;> simp [uK, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    first | linear_combination (1/4 : ℚ) * h | linear_combination (-1/4 : ℚ) * h | ring1

theorem uK_add_ubK : uK n + ubK n = -(tyzDelta n : QNeg n) := by
  ext <;> simp [uK, ubK] <;> ring

omit [NeZero n] in
theorem mem_span_pair_of' {a b x : QNeg n} (p q : ℤ) (h : x = p • a + q • b) :
    x ∈ Submodule.span ℤ ({a, b} : Set (QNeg n)) :=
  Submodule.mem_span_pair.2 ⟨p, q, h.symm⟩

/-- `𝓞_K = ℤ + ℤū` (`n ≡ 7 (mod 8)`). -/
theorem coe_mem_span_ubK (hn : n % 8 = 7) (hsq : Squarefree n) (z : 𝓞 (QNeg n)) :
    (z : QNeg n) ∈ Submodule.span ℤ ({ubK n, 1} : Set (QNeg n)) := by
  obtain ⟨s, t, hs, ht, k, hk⟩ := int_coords3 (by omega) hsq z
  obtain ⟨d, hd⟩ := delta_odd hn
  refine mem_span_pair_of' (-t) (k - t * d) ?_
  have hdq : (tyzDelta n : ℚ) = 2 * d + 1 := by exact_mod_cast hd
  have hkq : (s : ℚ) = t + 2 * k := by exact_mod_cast hk
  ext <;> simp [ubK, hs, ht, zsmul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_intCast] <;>
    (try rw [hdq]) <;> (try rw [hkq]) <;> ring

/-- `𝓞_K = ℤ + ℤu`. -/
theorem coe_mem_span_uK (hn : n % 8 = 7) (hsq : Squarefree n) (z : 𝓞 (QNeg n)) :
    (z : QNeg n) ∈ Submodule.span ℤ ({-uK n, 1} : Set (QNeg n)) := by
  obtain ⟨s, t, hs, ht, k, hk⟩ := int_coords3 (by omega) hsq z
  obtain ⟨d, hd⟩ := delta_odd hn
  refine mem_span_pair_of' (-t) (k + t * (d + 1)) ?_
  have hdq : (tyzDelta n : ℚ) = 2 * d + 1 := by exact_mod_cast hd
  have hkq : (s : ℚ) = t + 2 * k := by exact_mod_cast hk
  ext <;> simp [uK, hs, ht, zsmul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_intCast] <;>
    (try rw [hdq]) <;> (try rw [hkq]) <;> ring

theorem coe_mem_span_ubK32 (hn : n % 8 = 7) (hsq : Squarefree n) (z : 𝓞 (QNeg n)) :
    (z : QNeg n) ∈ Submodule.span ℤ ({ubK n * oneN32 n, 1} : Set (QNeg n)) := by
  obtain ⟨s, t, hs, ht, k, hk⟩ := int_coords3 (by omega) hsq z
  obtain ⟨d, hd⟩ := delta_odd hn
  refine mem_span_pair_of' (-32 * t) (k - t * d) ?_
  have hdq : (tyzDelta n : ℚ) = 2 * d + 1 := by exact_mod_cast hd
  have hkq : (s : ℚ) = t + 2 * k := by exact_mod_cast hk
  ext <;> simp [ubK, hs, ht, zsmul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_intCast] <;>
    (try rw [hdq]) <;> (try rw [hkq]) <;> ring

theorem coe_mem_span_uK32 (hn : n % 8 = 7) (hsq : Squarefree n) (z : 𝓞 (QNeg n)) :
    (z : QNeg n) ∈ Submodule.span ℤ ({-uK n * oneN32 n, 1} : Set (QNeg n)) := by
  obtain ⟨s, t, hs, ht, k, hk⟩ := int_coords3 (by omega) hsq z
  obtain ⟨d, hd⟩ := delta_odd hn
  refine mem_span_pair_of' (-32 * t) (k + t * (d + 1)) ?_
  have hdq : (tyzDelta n : ℚ) = 2 * d + 1 := by exact_mod_cast hd
  have hkq : (s : ℚ) = t + 2 * k := by exact_mod_cast hk
  ext <;> simp [uK, hs, ht, zsmul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_intCast] <;>
    (try rw [hdq]) <;> (try rw [hkq]) <;> ring

theorem coe_mul_mem_span_ubK32 (hn : n % 8 = 7) (hsq : Squarefree n) (z : 𝓞 (QNeg n)) :
    (z : QNeg n) * (ubK n * oneN32 n) ∈ Submodule.span ℤ ({ubK n * oneN32 n, 1} : Set (QNeg n)) := by
  obtain ⟨s, t, hs, ht, k, hk⟩ := int_coords3 (by omega) hsq z
  obtain ⟨d, hd⟩ := delta_odd hn
  have hdq : (tyzDelta n : ℚ) = 2 * d + 1 := by exact_mod_cast hd
  have hkq : (s : ℚ) = t + 2 * k := by exact_mod_cast hk
  have h := n_delta_q hn
  rw [hdq] at h
  refine mem_span_pair_of' (k - t * d + t * (2 * d + 1)) (t * N7 n) ?_
  ext <;> simp [ubK, hs, ht, zsmul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_intCast] <;> (try rw [hkq]) <;> (try rw [hdq]) <;>
    first
    | ring1
    | linear_combination (t / 128 : ℚ) * h
    | linear_combination (-t / 128 : ℚ) * h
    | linear_combination (t / 256 : ℚ) * h
    | linear_combination (-t / 256 : ℚ) * h
    | linear_combination (t / 64 : ℚ) * h
    | linear_combination (-t / 64 : ℚ) * h

end Thm36c


section Thm36d

open TyzCm Complex
open scoped nonZeroDivisors Pointwise

variable {n : ℕ} [NeZero n]

theorem coe_mul_mem_span_uK32 (hn : n % 8 = 7) (hsq : Squarefree n) (z : 𝓞 (QNeg n)) :
    (z : QNeg n) * (-uK n * oneN32 n) ∈ Submodule.span ℤ ({-uK n * oneN32 n, 1} : Set (QNeg n)) := by
  obtain ⟨s, t, hs, ht, k, hk⟩ := int_coords3 (by omega) hsq z
  obtain ⟨d, hd⟩ := delta_odd hn
  have hdq : (tyzDelta n : ℚ) = 2 * d + 1 := by exact_mod_cast hd
  have hkq : (s : ℚ) = t + 2 * k := by exact_mod_cast hk
  have h := n_delta_q hn
  rw [hdq] at h
  refine mem_span_pair_of' (k - t * d) (t * N7 n) ?_
  ext <;> simp [uK, hs, ht, zsmul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_intCast] <;> (try rw [hkq]) <;> (try rw [hdq]) <;>
    first
    | ring1
    | linear_combination (t / 128 : ℚ) * h
    | linear_combination (-t / 128 : ℚ) * h
    | linear_combination (t / 256 : ℚ) * h
    | linear_combination (-t / 256 : ℚ) * h
    | linear_combination (t / 64 : ℚ) * h
    | linear_combination (-t / 64 : ℚ) * h

/-- `m = (δ+1)/2`. -/
abbrev m7 (n : ℕ) : ℕ := (tyzDelta n + 1) / 2

theorem two_m7 {n : ℕ} (hn : n % 8 = 7) : (2 * m7 n : ℚ) = tyzDelta n + 1 := by
  obtain ⟨d, hd⟩ := delta_odd hn
  have h : 2 * m7 n = tyzDelta n + 1 := by simp only [m7]; omega
  exact_mod_cast h

/-- `u = θ − m = (√−n − δ)/2 ∈ 𝓞_K`. -/
def uO (n : ℕ) [NeZero n] (h3 : n % 4 = 3) : 𝓞 (QNeg n) :=
  ZInQ.RouteK.Redei.thetaO n h3 - (m7 n : 𝓞 (QNeg n))
/-- `ū = 1 − θ − m = (−√−n − δ)/2 ∈ 𝓞_K`. -/
def ubO (n : ℕ) [NeZero n] (h3 : n % 4 = 3) : 𝓞 (QNeg n) :=
  1 - ZInQ.RouteK.Redei.thetaO n h3 - (m7 n : 𝓞 (QNeg n))

theorem alg_uO (hn : n % 8 = 7) :
    algebraMap (𝓞 (QNeg n)) (QNeg n) (uO n (by omega)) = uK n := by
  have h := two_m7 hn
  simp only [uO, map_sub, ZInQ.RouteK.Redei.algebraMap_thetaO, ZInQ.RouteK.Redei.theta_eq, map_natCast]
  ext <;> simp [uK] <;> linarith

theorem alg_ubO (hn : n % 8 = 7) :
    algebraMap (𝓞 (QNeg n)) (QNeg n) (ubO n (by omega)) = ubK n := by
  have h := two_m7 hn
  simp only [ubO, map_sub, map_one, ZInQ.RouteK.Redei.algebraMap_thetaO, ZInQ.RouteK.Redei.theta_eq,
    map_natCast]
  ext <;> simp [ubK, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> linarith

theorem coe_mem_meet {J : Ideal (𝓞 (QNeg n))} {y : 𝓞 (QNeg n)} (hy : y ∈ J) :
    (y : QNeg n) ∈ idealMeetOrder n 1 J :=
  ⟨⟨0, y, by simp⟩, y, hy, rfl⟩

omit [NeZero n] in
theorem mem_span_mul_four' {S T : Set (QNeg n)} (s₀ s₁ t₀ t₁ : QNeg n) (hs₀ : s₀ ∈ S)
    (hs₁ : s₁ ∈ S) (ht₀ : t₀ ∈ T) (ht₁ : t₁ ∈ T) {x : QNeg n} (a b c d : ℤ)
    (h : x = a • (s₀ * t₀) + b • (s₀ * t₁) + c • (s₁ * t₀) + d • (s₁ * t₁)) :
    x ∈ Submodule.span ℤ (S * T) := by
  rw [h]
  have hm : ∀ {s t : QNeg n}, s ∈ S → t ∈ T → s * t ∈ Submodule.span ℤ (S * T) :=
    fun hs ht => Submodule.subset_span (Set.mul_mem_mul hs ht)
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hm hs₀ ht₀)) (Submodule.smul_mem _ _ (hm hs₀ ht₁)))
    (Submodule.smul_mem _ _ (hm hs₁ ht₀))) (Submodule.smul_mem _ _ (hm hs₁ ht₁))

theorem bezout32 {n : ℕ} (hn : n % 8 = 7) : ∃ a b : ℤ, a * 32 + b * (tyzDelta n : ℤ) = 1 := by
  obtain ⟨d, hd⟩ := delta_odd hn
  have h2 : IsCoprime (2 : ℤ) (tyzDelta n : ℤ) := ⟨-d, 1, by rw [hd]; ring⟩
  obtain ⟨a, b, hab⟩ := h2.pow_left (m := 5)
  exact ⟨a, b, by norm_num at hab; linarith⟩

theorem thirtytwo_oneN32 : (32 : QNeg n) * oneN32 n = 1 := by
  ext <;> simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]

/-- `𝔭̄₂^5 = (32, ū)` and `𝔭₂^5 = (32, u)` as ideals of `𝓞_K` (generators). -/
abbrev Jub (n : ℕ) [NeZero n] (h3 : n % 4 = 3) : Ideal (𝓞 (QNeg n)) :=
  Ideal.span {(32 : 𝓞 (QNeg n)), ubO n h3}
abbrev Ju (n : ℕ) [NeZero n] (h3 : n % 4 = 3) : Ideal (𝓞 (QNeg n)) :=
  Ideal.span {(32 : 𝓞 (QNeg n)), uO n h3}

theorem alg32 : algebraMap (𝓞 (QNeg n)) (QNeg n) 32 = 32 := map_ofNat _ 32

theorem latK7 (hn : n % 8 = 7) (hsq : Squarefree n) :
    Submodule.span ℤ (idealMeetOrder n 1 (Jub n (by omega))) * Submodule.span ℤ {1, t'K n} =
      Submodule.span ℤ {ubK n * 1, ubK n * tK n} := by
  rw [Submodule.span_mul_span, mul_one, ubK_mul_tK hn]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨-, y, hyJ, rfl⟩, t, ht, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · rw [mul_one]; exact coe_mem_span_ubK hn hsq y
    · obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 hyJ
      have e : (y : QNeg n) * t'K n =
          ((α * uO n (by omega) + β * (N7 n : 𝓞 (QNeg n)) : 𝓞 (QNeg n)) : QNeg n) := by
        rw [← hαβ]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, alg_uO hn,
          alg_ubO hn, alg32]
        rw [add_mul, mul_assoc, mul_assoc, thirtytwo_t'K, ubK_mul_t'K hn]
      rw [e]; exact coe_mem_span_ubK hn hsq _
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · refine Submodule.subset_span ⟨_, coe_mem_meet (Ideal.subset_span (Set.mem_insert_of_mem _ rfl) :
        ubO n (by omega) ∈ Jub n (by omega)), 1, Set.mem_insert _ _, ?_⟩
      dsimp only
      rw [mul_one, RingOfIntegers.coe_eq_algebraMap, alg_ubO hn]
    · obtain ⟨a, b, hab⟩ := bezout32 hn
      have habK : (a : QNeg n) * 32 + (b : QNeg n) * (tyzDelta n : QNeg n) = 1 := by
        have := congrArg (Int.cast : ℤ → QNeg n) hab
        push_cast at this
        exact this
      have h32 : ((32 : 𝓞 (QNeg n)) : QNeg n) = 32 := alg32
      have hub : ((ubO n (by omega) : 𝓞 (QNeg n)) : QNeg n) = ubK n := alg_ubO hn
      refine mem_span_mul_four' (S := idealMeetOrder n 1 (Jub n (by omega))) (T := {1, t'K n})
        ((32 : 𝓞 (QNeg n)) : QNeg n) ((ubO n (by omega) : 𝓞 (QNeg n)) : QNeg n) 1 (t'K n)
        (coe_mem_meet (Ideal.subset_span (Set.mem_insert _ _) : (32 : 𝓞 (QNeg n)) ∈ Jub n (by omega)))
        (coe_mem_meet (Ideal.subset_span (Set.mem_insert_of_mem _ rfl) : ubO n (by omega) ∈ Jub n (by omega)))
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) a (-b) (-b) 0 ?_
      rw [h32, hub, thirtytwo_t'K]
      simp only [zsmul_eq_mul, mul_one, Int.cast_neg, Int.cast_zero, zero_mul, add_zero]
      linear_combination (-1 : QNeg n) * habK + (b : QNeg n) * (uK_add_ubK (n := n))

theorem latNK7 (hn : n % 8 = 7) (hsq : Squarefree n) :
    Submodule.span ℤ (idealMeetOrder n 1 (Jub n (by omega))) * Submodule.span ℤ {oneN32 n, t'K n} =
      Submodule.span ℤ {ubK n * oneN32 n, ubK n * tK n} := by
  rw [Submodule.span_mul_span, ubK_mul_tK hn]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨-, y, hyJ, rfl⟩, t, ht, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 hyJ
    rcases ht with rfl | rfl
    · have e : (y : QNeg n) * oneN32 n = (α : QNeg n) + (β : QNeg n) * (ubK n * oneN32 n) := by
        rw [← hαβ]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, alg_ubO hn, alg32]
        rw [add_mul, mul_assoc, thirtytwo_oneN32, mul_one, mul_assoc]
      rw [e]
      exact Submodule.add_mem _ (coe_mem_span_ubK32 hn hsq α) (coe_mul_mem_span_ubK32 hn hsq β)
    · have e : (y : QNeg n) * t'K n =
          ((α * uO n (by omega) + β * (N7 n : 𝓞 (QNeg n)) : 𝓞 (QNeg n)) : QNeg n) := by
        rw [← hαβ]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, alg_uO hn,
          alg_ubO hn, alg32]
        rw [add_mul, mul_assoc, mul_assoc, thirtytwo_t'K, ubK_mul_t'K hn]
      rw [e]; exact coe_mem_span_ubK32 hn hsq _
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · refine Submodule.subset_span ⟨_, coe_mem_meet (Ideal.subset_span (Set.mem_insert_of_mem _ rfl) :
        ubO n (by omega) ∈ Jub n (by omega)), oneN32 n, Set.mem_insert _ _, ?_⟩
      dsimp only
      rw [RingOfIntegers.coe_eq_algebraMap, alg_ubO hn]
    · refine Submodule.subset_span ⟨_, coe_mem_meet (Ideal.subset_span (Set.mem_insert _ _) :
        (32 : 𝓞 (QNeg n)) ∈ Jub n (by omega)), oneN32 n, Set.mem_insert _ _, ?_⟩
      dsimp only
      rw [RingOfIntegers.coe_eq_algebraMap, alg32, thirtytwo_oneN32]

theorem latK7c (hn : n % 8 = 7) (hsq : Squarefree n) :
    Submodule.span ℤ (idealMeetOrder n 1 (Ju n (by omega))) * Submodule.span ℤ {1, tb'K n} =
      Submodule.span ℤ {-uK n * 1, -uK n * tbK n} := by
  rw [Submodule.span_mul_span, mul_one, neg_uK_mul_tbK hn]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨-, y, hyJ, rfl⟩, t, ht, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · rw [mul_one]; exact coe_mem_span_uK hn hsq y
    · obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 hyJ
      have e : (y : QNeg n) * tb'K n =
          ((-(α * ubO n (by omega)) - β * (N7 n : 𝓞 (QNeg n)) : 𝓞 (QNeg n)) : QNeg n) := by
        rw [← hαβ]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_sub, map_neg,
          map_intCast, alg_uO hn, alg_ubO hn, alg32]
        rw [add_mul, mul_assoc, mul_assoc, thirtytwo_tb'K, uK_mul_tb'K hn]
        ring
      rw [e]; exact coe_mem_span_uK hn hsq _
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · have hm : uK n ∈ Submodule.span ℤ (idealMeetOrder n 1 (Ju n (by omega)) * {1, tb'K n}) :=
        Submodule.subset_span ⟨_, coe_mem_meet (Ideal.subset_span (Set.mem_insert_of_mem _ rfl) :
          uO n (by omega) ∈ Ju n (by omega)), 1, Set.mem_insert _ _, by
            dsimp only
            rw [mul_one, RingOfIntegers.coe_eq_algebraMap, alg_uO hn]⟩
      exact Submodule.neg_mem _ hm
    · obtain ⟨a, b, hab⟩ := bezout32 hn
      have habK : (a : QNeg n) * 32 + (b : QNeg n) * (tyzDelta n : QNeg n) = 1 := by
        have := congrArg (Int.cast : ℤ → QNeg n) hab
        push_cast at this
        exact this
      have h32 : ((32 : 𝓞 (QNeg n)) : QNeg n) = 32 := alg32
      have hu : ((uO n (by omega) : 𝓞 (QNeg n)) : QNeg n) = uK n := alg_uO hn
      refine mem_span_mul_four' (S := idealMeetOrder n 1 (Ju n (by omega))) (T := {1, tb'K n})
        ((32 : 𝓞 (QNeg n)) : QNeg n) ((uO n (by omega) : 𝓞 (QNeg n)) : QNeg n) 1 (tb'K n)
        (coe_mem_meet (Ideal.subset_span (Set.mem_insert _ _) : (32 : 𝓞 (QNeg n)) ∈ Ju n (by omega)))
        (coe_mem_meet (Ideal.subset_span (Set.mem_insert_of_mem _ rfl) : uO n (by omega) ∈ Ju n (by omega)))
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) a b (-b) 0 ?_
      rw [h32, hu, thirtytwo_tb'K]
      simp only [zsmul_eq_mul, mul_one, Int.cast_neg, Int.cast_zero, zero_mul, add_zero]
      linear_combination (-1 : QNeg n) * habK + (b : QNeg n) * (uK_add_ubK (n := n))

theorem latNK7c (hn : n % 8 = 7) (hsq : Squarefree n) :
    Submodule.span ℤ (idealMeetOrder n 1 (Ju n (by omega))) * Submodule.span ℤ {oneN32 n, tb'K n} =
      Submodule.span ℤ {-uK n * oneN32 n, -uK n * tbK n} := by
  rw [Submodule.span_mul_span, neg_uK_mul_tbK hn]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨-, y, hyJ, rfl⟩, t, ht, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 hyJ
    rcases ht with rfl | rfl
    · have e : (y : QNeg n) * oneN32 n =
          (α : QNeg n) + ((-β : 𝓞 (QNeg n)) : QNeg n) * (-uK n * oneN32 n) := by
        rw [← hαβ]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_neg, alg_uO hn, alg32]
        rw [add_mul, mul_assoc, thirtytwo_oneN32, mul_one]
        ring
      rw [e]
      exact Submodule.add_mem _ (coe_mem_span_uK32 hn hsq α) (coe_mul_mem_span_uK32 hn hsq _)
    · have e : (y : QNeg n) * tb'K n =
          ((-(α * ubO n (by omega)) - β * (N7 n : 𝓞 (QNeg n)) : 𝓞 (QNeg n)) : QNeg n) := by
        rw [← hαβ]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_sub, map_neg,
          map_intCast, alg_uO hn, alg_ubO hn, alg32]
        rw [add_mul, mul_assoc, mul_assoc, thirtytwo_tb'K, uK_mul_tb'K hn]
        ring
      rw [e]; exact coe_mem_span_uK32 hn hsq _
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · have hm : uK n * oneN32 n ∈
          Submodule.span ℤ (idealMeetOrder n 1 (Ju n (by omega)) * {oneN32 n, tb'K n}) :=
        Submodule.subset_span ⟨_, coe_mem_meet (Ideal.subset_span (Set.mem_insert_of_mem _ rfl) :
          uO n (by omega) ∈ Ju n (by omega)), oneN32 n, Set.mem_insert _ _, by
            dsimp only
            rw [RingOfIntegers.coe_eq_algebraMap, alg_uO hn]⟩
      rw [neg_mul]
      exact Submodule.neg_mem _ hm
    · refine Submodule.subset_span ⟨_, coe_mem_meet (Ideal.subset_span (Set.mem_insert _ _) :
        (32 : 𝓞 (QNeg n)) ∈ Ju n (by omega)), oneN32 n, Set.mem_insert _ _, ?_⟩
      dsimp only
      rw [RingOfIntegers.coe_eq_algebraMap, alg32, thirtytwo_oneN32]

end Thm36d


section Thm36e

open TyzCm Complex
open scoped nonZeroDivisors Pointwise

/-! General ideal identities in a commutative ring (for `𝔭₂𝔭̄₂ = (2)` and `𝔭₂^5 = (32, u)`). -/

theorem span_two_mul_span_two {R : Type*} [CommRing R] (g g' m N : R) (h1 : g + g' + 2 * m = 1)
    (h2 : g * g' = 32 * N) :
    Ideal.span {2, g} * Ideal.span {2, g'} = Ideal.span {(2 : R)} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro x hx y hy
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hx
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hy
    rw [Ideal.mem_span_singleton]
    refine ⟨a * c * 2 + a * d * g' + b * c * g + b * d * 16 * N, ?_⟩
    linear_combination (b * d) * h2
  · rw [Ideal.span_singleton_le_iff_mem]
    have e1 : g * 2 ∈ Ideal.span {2, g} * Ideal.span {2, g'} :=
      Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
        (Ideal.subset_span (Set.mem_insert _ _))
    have e2 : 2 * g' ∈ Ideal.span {2, g} * Ideal.span {2, g'} :=
      Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_insert _ _))
        (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    have e4 : 2 * 2 ∈ Ideal.span {2, g} * Ideal.span {2, g'} :=
      Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_insert _ _)) (Ideal.subset_span (Set.mem_insert _ _))
    have := add_mem (add_mem e1 e2) (Ideal.mul_mem_right m _ e4)
    convert this using 1
    linear_combination (-2 : R) * h1

theorem span_two_pow_le {R : Type*} [CommRing R] (g : R) (k : ℕ) :
    Ideal.span {2, g} ^ (k + 1) ≤ Ideal.span {(2 : R) ^ (k + 1), g} := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine le_trans (Ideal.mul_mono_left ih) ?_
    rw [Ideal.mul_le]
    intro x hx y hy
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hx
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hy
    rw [Ideal.mem_span_pair]
    exact ⟨a * c, a * d * 2 ^ (k + 1) + b * c * 2 + b * d * g, by ring⟩

theorem span_two_pow_five {R : Type*} [CommRing R] (g g' m N : R) (h1 : g + g' + 2 * m = 1)
    (h2 : g * g' = 32 * N) :
    Ideal.span {2, g} ^ 5 = Ideal.span {(32 : R), g} := by
  apply le_antisymm
  · have := span_two_pow_le g 4
    norm_num at this
    exact this
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    have hI2 : (2 : R) ∈ Ideal.span {2, g} := Ideal.subset_span (Set.mem_insert _ _)
    have hIg : g ∈ Ideal.span {2, g} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have h32 : (32 : R) ∈ Ideal.span {2, g} ^ 5 := by
      have := Ideal.pow_mem_pow hI2 5
      norm_num at this
      exact this
    refine ⟨h32, ?_⟩
    have hw : g + 2 * m ∈ Ideal.span {2, g} :=
      add_mem hIg (Ideal.mul_mem_right m _ hI2)
    have key : g = 32 * N * (1 + (g + 2 * m) + (g + 2 * m) ^ 2 + (g + 2 * m) ^ 3) +
        g * (g + 2 * m) ^ 4 := by
      linear_combination (1 + (g + 2 * m) + (g + 2 * m) ^ 2 + (g + 2 * m) ^ 3) * h2 -
        g * (1 + (g + 2 * m) + (g + 2 * m) ^ 2 + (g + 2 * m) ^ 3) * h1
    have hmem : 32 * N * (1 + (g + 2 * m) + (g + 2 * m) ^ 2 + (g + 2 * m) ^ 3) +
        g * (g + 2 * m) ^ 4 ∈ Ideal.span {2, g} ^ 5 := by
      refine add_mem ?_ ?_
      · rw [mul_assoc]; exact Ideal.mul_mem_right _ _ h32
      · rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ' (Ideal.span {2, g}) 4]
        exact Ideal.mul_mem_mul hIg (Ideal.pow_mem_pow hw 4)
    rw [← key] at hmem
    exact hmem

end Thm36e


section Thm36f

open TyzCm Complex
open scoped nonZeroDivisors Pointwise

variable {n : ℕ} [NeZero n]

theorem toC_ptT : toC Package.ptT = X0.ptTC := by
  simp [toC, Package.ptT, X0.ptTC, WeierstrassCurve.Affine.Point.map, map_ofNat]

theorem IsComplexConj.galPt_galPt {γ : GalQ} (hγ : IsComplexConj γ) (P : PtA) :
    galPt γ (galPt γ P) = P := by
  rw [← galPt_mul]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e'⟩ := galPt_some (γ * γ) h
    rw [e', WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hγ.mul_self x, hγ.mul_self y⟩

theorem t'K_mul_tbK (hn : n % 8 = 7) : t'K n * (32 * tbK n) = -1 := by
  have h4 : (4 : ℚ) * A7 n = n + (tyzDelta n : ℚ) ^ 2 := by exact_mod_cast four_A7 hn
  have hA : (A7 n : ℚ) ≠ 0 := (A7_pos hn).ne'
  ext <;> simp [t'K, tbK, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> field_simp <;>
    first | linear_combination (32 : ℚ) * h4 | linear_combination (-32 : ℚ) * h4 |
      linear_combination (-1 : ℚ) * h4 | linear_combination h4 | ring1

/-- **The Fricke step**: `z_{Q'} = T − z_{Q̄}` (`τ_{Q'} = −1/(32 τ_{Q̄})`). -/
theorem heegnerPt_tyzForm7' (hF : X0.EtaModelFricke) (hA : CMAlgebraic) (hn : n % 8 = 7) :
    heegnerPt (tyzForm7' n hn) = Package.ptT - heegnerPt (tyzForm7 n hn).conj := by
  have hex := hA _ (tyzForm7 n hn).conj
  have hW : ((tyzForm7' n hn).tauH : ℂ) = -1 / (32 * ((tyzForm7 n hn).conj.tauH : ℂ)) := by
    have h1 : ((tyzForm7' n hn).tauH : ℂ) = kappaAlg n (t'K n) := by
      rw [kappaAlg_apply, ← tyzForm7'_tau hn]; rfl
    have h2 : ((tyzForm7 n hn).conj.tauH : ℂ) = kappaAlg n (tbK n) := by
      rw [kappaAlg_apply, ← tyzForm7_conj_tau hn]; rfl
    have hne : (32 * ((tyzForm7 n hn).conj.tauH : ℂ)) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact (tyzForm7 n hn).conj.tauH.im_pos.ne' this
    rw [eq_div_iff hne, h1, h2]
    have := congrArg (kappaAlg n) (t'K_mul_tbK hn)
    simpa [map_ofNat] using this
  have hfr := hF _ _ hW
  apply heegnerPt_eq
  rw [map_sub, toC_heegnerPt _ hex, toC_ptT, ← hfr]
  abel

/-- The class `[𝔭₂]^{−5}` is the class of `(32, ū)` (positive orientation) resp. `(32, u)`. -/
theorem p2Class_inv_pow_five_pos (hn : n % 8 = 7) (hpos : PosOrient n) (h0 : Jub n (by omega) ∈ (Ideal (𝓞 (QNeg n)))⁰) :
    (p2Class n)⁻¹ ^ 5 = (ClassGroup.mk0 ⟨Jub n (by omega), h0⟩ : ClassGroup (𝓞 (QNeg n))) := by
  sorry

theorem p2Class_inv_pow_five_neg (hn : n % 8 = 7) (hpos : ¬ PosOrient n) (h0 : Ju n (by omega) ∈ (Ideal (𝓞 (QNeg n)))⁰) :
    (p2Class n)⁻¹ ^ 5 = (ClassGroup.mk0 ⟨Ju n (by omega), h0⟩ : ClassGroup (𝓞 (QNeg n))) := by
  sorry

theorem acts_transport (e : SeparableClosure (QNeg n) →ₐ[ℚ] Qbar) (ρ : GalQ)
    (O : TauCeti.GlobalNumberFields.NumberFieldOrder (QNeg n))
    (hO : O = TauCeti.GlobalNumberFields.maximalNumberFieldOrder (QNeg n))
    (J : Ideal (𝓞 (QNeg n))) (hJO : J ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo O.conductorModulus)
    (hJ0 : J ∈ (Ideal (𝓞 (QNeg n)))⁰)
    (h : ∀ x : hilbertField n, ρ (e (x : SeparableClosure (QNeg n))) =
      e ((TauCeti.ClassFieldTheory.ringClassArtinEquiv (OK n)
        (ClassGroup.mk0 ⟨J, hJ0⟩ : ClassGroup (𝓞 (QNeg n))) x : hilbertField n) :
          SeparableClosure (QNeg n))) :
    ∀ x : TauCeti.ClassFieldTheory.ringClassField O, ρ (e (x : SeparableClosure (QNeg n))) =
      e ((TauCeti.ClassFieldTheory.ringClassArtinEquiv O (O.picClass ⟨J, hJO⟩) x :
        TauCeti.ClassFieldTheory.ringClassField O) : SeparableClosure (QNeg n)) := by
  subst hO
  intro x
  rw [picClass_maximal ⟨J, hJO⟩ hJ0]
  exact h x

theorem J_mem_primeTo (J : Ideal (𝓞 (QNeg n))) (hJ : (32 : 𝓞 (QNeg n)) ∈ J) :
    J ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
      (conductorOrder (QNeg n) 1).conductorModulus := by
  rw [TauCeti.GlobalNumberFields.NumberFieldOrder.mem_integralIdealsPrimeTo_conductorModulus_iff]
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, Ideal.mem_bot] at hJ
    have h' := congrArg (algebraMap (𝓞 (QNeg n)) (QNeg n)) hJ
    rw [map_ofNat, map_zero] at h'
    norm_num at h'
  · rw [(TauCeti.GlobalNumberFields.NumberFieldOrder.conductor_eq_top_iff _).2 (conductorOrder_one _)]
    exact sup_top_eq _

theorem J_mem_nzd (J : Ideal (𝓞 (QNeg n))) (hJ : (32 : 𝓞 (QNeg n)) ∈ J) :
    J ∈ (Ideal (𝓞 (QNeg n)))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  rw [h, Ideal.zero_eq_bot, Ideal.mem_bot] at hJ
  have h' := congrArg (algebraMap (𝓞 (QNeg n)) (QNeg n)) hJ
  rw [map_ofNat, map_zero] at h'
  norm_num at h'

theorem ιC_omega_cases (n : ℕ) [NeZero n] :
    ιC (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt n : ℂ) ∨
      ιC (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        -(I * (Real.sqrt n : ℂ)) := by
  set z := ιC (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega))
  have hz : z ^ 2 = -(n : ℂ) := by
    simp only [z]
    rw [← map_pow, ← map_pow, ← map_pow]
    simp [QuadraticAlgebra.omega_pow_two_eq_add]
  have hs : (I * (Real.sqrt n : ℂ)) ^ 2 = -(n : ℂ) := by
    rw [mul_pow, I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hz.trans hs.symm) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **`TYZThm36Seven` from Shimura reciprocity (tyz-cm), the Fricke involution (x0-32) and
algebraicity of CM points (cm-points).** -/
theorem tyzThm36Seven_of (hS : ShimuraReciprocityPic) (hF : X0.EtaModelFricke)
    (hA : CMAlgebraic) : TYZThm36Seven := by
  intro n _ hn hsq γ ρ hγ hρ
  have h3 : n % 4 = 3 := by omega
  have hD : -(n : ℤ) = discOf n 1 := by simp [discOf, h3]
  have hfr := heegnerPt_tyzForm7' hF hA hn
  have hconj : galPt γ (heegnerPt (tyzForm7 n hn)) = heegnerPt (tyzForm7 n hn).conj :=
    cmComplexConj γ hγ _ _
  have hz : tyzZ7 n = heegnerPt (tyzForm7 n hn) := by simp [tyzZ7, hn]
  rw [hz, hconj, tauG_apply, one_smul]
  have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
  by_cases hpos : PosOrient n
  · have he : ιC (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt n : ℂ) := by
      rcases ιC_omega_cases n with h | h
      · exact h
      · exfalso; unfold PosOrient at hpos; rw [h] at hpos; simp at hpos; linarith
    have hJ32 : (32 : 𝓞 (QNeg n)) ∈ Jub n h3 := Ideal.subset_span (Set.mem_insert _ _)
    have hJO := J_mem_primeTo _ hJ32
    have hJ0 := J_mem_nzd _ hJ32
    have hc := p2Class_inv_pow_five_pos hn hpos hJ0
    have hρe := acts_transport (embed n) ρ (conductorOrder (QNeg n) 1) (conductorOrder_one _)
      (Jub n h3) hJO hJ0 (by intro x; rw [← hc]; exact hρ x)
    have hlat : idealLat n 1 (Jub n h3) * (tyzForm7' n hn).lat =
        (tyzForm7 n hn).lat.map (LinearMap.mulLeft ℤ (kappa n (ubK n))) := by
      rw [show idealLat n 1 (Jub n h3) = (Submodule.span ℤ (idealMeetOrder n 1 (Jub n h3))).map
          (kappaLin n) by
        rw [idealLat, show kappa n = kappaLin n from funext fun x => (kappaLin_apply n x).symm,
          Submodule.span_image],
        lat_eq_map' _ (t'K n) (tyzForm7'_tau hn), lat_eq_map' _ (tK n) (tyzForm7_tau hn),
        map_mulLeft_span_pair, kappaLin, ← Submodule.map_mul, latK7 hn hsq]
    have hlatN : idealLat n 1 (Jub n h3) * (tyzForm7' n hn).latN =
        (tyzForm7 n hn).latN.map (LinearMap.mulLeft ℤ (kappa n (ubK n))) := by
      rw [show idealLat n 1 (Jub n h3) = (Submodule.span ℤ (idealMeetOrder n 1 (Jub n h3))).map
          (kappaLin n) by
        rw [idealLat, show kappa n = kappaLin n from funext fun x => (kappaLin_apply n x).symm,
          Submodule.span_image],
        latN_eq_map' _ (t'K n) (tyzForm7'_tau hn), latN_eq_map' _ (tK n) (tyzForm7_tau hn),
        map_mulLeft_span_pair, kappaLin, ← Submodule.map_mul, latNK7 hn hsq]
    have hrec := hS n 1 hsq (embed n) he ⟨_, hJO⟩ ρ hρe (-(n : ℤ)) hD (tyzForm7 n hn)
      (tyzForm7' n hn) (kappa n (ubK n)) hlat hlatN
    rw [hrec, hfr]; abel
  · sorry

end Thm36f

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem of cm-bridge (final leaves).** Reading A of TYZ Theorem 3.5
(`ZInQ.Literature.TYZThm35ReadingA`) from:
* the three `𝓛`-leaves of tyz-decomp: `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2`;
* the CM leaf `CM.CMFieldOfDefinition ringClassFieldD` (Heegner points of discriminant `D` on
  `A = X₀(32)` are defined over the ring class field of discriminant `D`; task tyz-cm works on it);
* `TYZSigmaShiftsF0` (TYZ Prop. 3.7(1), L1488–1490, + Shimura reciprocity at `P_n`);
* `Lemma318Literal HHprime` (TYZ Lemma `torsion2`, L2230: torsion of `A(ℍ'_n)`);
* `Thm35First ℓ tyzZ` (TYZ Theorem 3.3/3.5 for the pinned genus points);
* `Lemma321Five` (TYZ Lemma 3.21(1), L2508–2510);
* `TYZThm36Seven` (TYZ Theorem 3.6(3), L1424–1427).
Proved here (no longer hypotheses): `IInH4`, `HprimeNormal` (ring-class), `IInHprime`,
`CMFieldOfDefinitionTYZ`, `CMFieldOfDefinition7`, `TYZSigmaFixesZn`, `GenusFieldLeLni`, and
`Lemma321Seven` (from `TYZThm36Seven` with the glue `BetaOnGenus7`, proved from genus theory). -/
theorem tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : CM.CMFieldOfDefinition ringClassFieldD) (hsh : TYZSigmaShiftsF0)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h36 : TYZThm36Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves7 h11 h1 h29 hcm hsh h318 h35 h5
    (lemma321Seven_of' (cmFieldOfDefinition7_of hcm) h36)

end ZInQ.Contrib.TYZGenus.CMBridge

/-! ## Axiom audit (output in `scratch/cm-bridge/audit-out.txt`) -/
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzDelta_spec
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms exists_actsAsArtinO
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms lemma321_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms genusPointLeafCM_of_pinned
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms genusPointLeaf_of_pinned
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_pinned
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_pinned'
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzSigmaFixesZn_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms galPt_Z7
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms class7GenusPtDefined_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_pinnedLeaves
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms Copy.genusPointLeafCM_eq
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms phi0_spec
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms iInHprime
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms cmFieldOfDefinition7_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_rewired
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms genusFieldLeLni
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_cmLeaves7
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms exists_complexConj
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms lemma321Seven_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_cmLeaves7'
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms sqrtPstarInHilbert
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms betaOnGenus7_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms artinPstarChi
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms normP2
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms lemma321Seven_of'
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven

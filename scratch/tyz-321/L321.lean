import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.TYZGenus.ShimuraFricke

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

theorem uO_mul_ubO (hn : n % 8 = 7) :
    uO n (by omega) * ubO n (by omega) = 32 * (N7 n : 𝓞 (QNeg n)) := by
  apply RingOfIntegers.ext
  have h := n_delta_q hn
  change algebraMap (𝓞 (QNeg n)) (QNeg n) (uO n _ * ubO n _) =
    algebraMap (𝓞 (QNeg n)) (QNeg n) (32 * (N7 n : 𝓞 (QNeg n)))
  rw [map_mul, map_mul, alg_uO hn, alg_ubO hn, map_ofNat, map_intCast]
  ext <;> simp [uK, ubK, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    first | linear_combination (1/4 : ℚ) * h | linear_combination (-1/4 : ℚ) * h | ring1

theorem uO_add_ubO (h3 : n % 4 = 3) : uO n h3 + ubO n h3 + 2 * (m7 n : 𝓞 (QNeg n)) = 1 := by
  simp only [uO, ubO]; ring

theorem mk0_inv_of_mul {I I' : Ideal (𝓞 (QNeg n))} (hI : I ∈ (Ideal (𝓞 (QNeg n)))⁰)
    (hI' : I' ∈ (Ideal (𝓞 (QNeg n)))⁰) (h : I * I' = Ideal.span {(2 : 𝓞 (QNeg n))}) :
    (ClassGroup.mk0 ⟨I', hI'⟩ : ClassGroup (𝓞 (QNeg n))) = (ClassGroup.mk0 ⟨I, hI⟩)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul]
  have h2 : (⟨I, hI⟩ : (Ideal (𝓞 (QNeg n)))⁰) * ⟨I', hI'⟩ =
      ⟨Ideal.span {(2 : 𝓞 (QNeg n))}, by rw [← h]; exact Submonoid.mul_mem _ hI hI'⟩ := Subtype.ext h
  rw [h2, ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨2, rfl⟩⟩

theorem mk0_pow_five {I J : Ideal (𝓞 (QNeg n))} (hI : I ∈ (Ideal (𝓞 (QNeg n)))⁰)
    (hJ : J ∈ (Ideal (𝓞 (QNeg n)))⁰) (h : I ^ 5 = J) :
    (ClassGroup.mk0 ⟨J, hJ⟩ : ClassGroup (𝓞 (QNeg n))) = (ClassGroup.mk0 ⟨I, hI⟩) ^ 5 := by
  rw [← map_pow]
  congr 1
  exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact h.symm)

theorem span2_mem (g : 𝓞 (QNeg n)) : Ideal.span {2, g} ∈ (Ideal (𝓞 (QNeg n)))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  have h2 : (2 : 𝓞 (QNeg n)) ∈ Ideal.span {2, g} := Ideal.subset_span (Set.mem_insert _ _)
  rw [h0, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  exact two_ne_zero h2

/-- The class `[𝔭₂]^{−5}` is the class of `(32, ū)` (positive orientation) resp. `(32, u)`. -/
theorem p2Class_inv_pow_five_pos (hn : n % 8 = 7) (hpos : PosOrient n)
    (h0 : Jub n (by omega) ∈ (Ideal (𝓞 (QNeg n)))⁰) :
    (p2Class n)⁻¹ ^ 5 = (ClassGroup.mk0 ⟨Jub n (by omega), h0⟩ : ClassGroup (𝓞 (QNeg n))) := by
  have h3 : n % 4 = 3 := by omega
  have hp : p2Ideal n = Ideal.span {2, uO n h3} := by
    unfold p2Ideal; rw [dif_pos h3, if_pos hpos]; rfl
  have hc : p2Class n = (ClassGroup.mk0 ⟨Ideal.span {2, uO n h3}, span2_mem _⟩ :
      ClassGroup (𝓞 (QNeg n))) := by
    unfold p2Class; congr 1; exact Subtype.ext hp
  have hmul := span_two_mul_span_two (uO n h3) (ubO n h3) (m7 n) (N7 n) (uO_add_ubO h3)
    (uO_mul_ubO hn)
  have hpow := span_two_pow_five (ubO n h3) (uO n h3) (m7 n) (N7 n)
    (by rw [add_comm (ubO n h3)]; exact uO_add_ubO h3) (by rw [mul_comm]; exact uO_mul_ubO hn)
  rw [mk0_pow_five (span2_mem _) h0 hpow, mk0_inv_of_mul (span2_mem _) (span2_mem _) hmul, hc]
  rfl

theorem p2Class_inv_pow_five_neg (hn : n % 8 = 7) (hpos : ¬ PosOrient n)
    (h0 : Ju n (by omega) ∈ (Ideal (𝓞 (QNeg n)))⁰) :
    (p2Class n)⁻¹ ^ 5 = (ClassGroup.mk0 ⟨Ju n (by omega), h0⟩ : ClassGroup (𝓞 (QNeg n))) := by
  have h3 : n % 4 = 3 := by omega
  have hp : p2Ideal n = Ideal.span {2, ubO n h3} := by
    unfold p2Ideal; rw [dif_pos h3, if_neg hpos]; rfl
  have hc : p2Class n = (ClassGroup.mk0 ⟨Ideal.span {2, ubO n h3}, span2_mem _⟩ :
      ClassGroup (𝓞 (QNeg n))) := by
    unfold p2Class; congr 1; exact Subtype.ext hp
  have hmul := span_two_mul_span_two (ubO n h3) (uO n h3) (m7 n) (N7 n)
    (by rw [add_comm (ubO n h3)]; exact uO_add_ubO h3) (by rw [mul_comm]; exact uO_mul_ubO hn)
  have hpow := span_two_pow_five (uO n h3) (ubO n h3) (m7 n) (N7 n) (uO_add_ubO h3)
    (uO_mul_ubO hn)
  rw [mk0_pow_five (span2_mem _) h0 hpow, mk0_inv_of_mul (span2_mem _) (span2_mem _) hmul, hc]
  rfl

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
  · have hneg : ιC (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        -(I * (Real.sqrt n : ℂ)) := by
      rcases ιC_omega_cases n with h | h
      · exfalso; apply hpos; unfold PosOrient; rw [h]; simpa using hsqrt
      · exact h
    let e : SeparableClosure (QNeg n) →ₐ[ℚ] Qbar := (γ : Qbar →ₐ[ℚ] Qbar).comp (embed n)
    have he : ιC (e (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt n : ℂ) := by
      change ιC (γ (embed n _)) = _
      rw [hγ, hneg]; simp
    have hJ32 : (32 : 𝓞 (QNeg n)) ∈ Ju n h3 := Ideal.subset_span (Set.mem_insert _ _)
    have hJO := J_mem_primeTo _ hJ32
    have hJ0 := J_mem_nzd _ hJ32
    have hc := p2Class_inv_pow_five_neg hn hpos hJ0
    have hρ'0 : ∀ x : hilbertField n, (γ * ρ * γ⁻¹) (e (x : SeparableClosure (QNeg n))) =
        e ((TauCeti.ClassFieldTheory.ringClassArtinEquiv (OK n)
          (ClassGroup.mk0 ⟨Ju n h3, hJ0⟩ : ClassGroup (𝓞 (QNeg n))) x : hilbertField n) :
            SeparableClosure (QNeg n)) := by
      intro x
      have hx : ρ (embed n (x : SeparableClosure (QNeg n))) =
          embed n ((TauCeti.ClassFieldTheory.ringClassArtinEquiv (OK n)
            (ClassGroup.mk0 ⟨Ju n h3, hJ0⟩ : ClassGroup (𝓞 (QNeg n))) x : hilbertField n) :
              SeparableClosure (QNeg n)) := by
        rw [← hc]; exact hρ x
      change (γ * ρ * γ⁻¹) (γ (embed n x)) = γ (embed n _)
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply,
        show γ⁻¹ (γ (embed n x)) = embed n x from γ.symm_apply_apply _, hx]
    have hρe := acts_transport e (γ * ρ * γ⁻¹) (conductorOrder (QNeg n) 1) (conductorOrder_one _)
      (Ju n h3) hJO hJ0 hρ'0
    have hlat : idealLat n 1 (Ju n h3) * (tyzForm7' n hn).conj.lat =
        (tyzForm7 n hn).conj.lat.map (LinearMap.mulLeft ℤ (kappa n (-uK n))) := by
      rw [show idealLat n 1 (Ju n h3) = (Submodule.span ℤ (idealMeetOrder n 1 (Ju n h3))).map
          (kappaLin n) by
        rw [idealLat, show kappa n = kappaLin n from funext fun x => (kappaLin_apply n x).symm,
          Submodule.span_image],
        lat_eq_map' _ (tb'K n) (tyzForm7'_conj_tau hn), lat_eq_map' _ (tbK n) (tyzForm7_conj_tau hn),
        map_mulLeft_span_pair, kappaLin, ← Submodule.map_mul, latK7c hn hsq]
    have hlatN : idealLat n 1 (Ju n h3) * (tyzForm7' n hn).conj.latN =
        (tyzForm7 n hn).conj.latN.map (LinearMap.mulLeft ℤ (kappa n (-uK n))) := by
      rw [show idealLat n 1 (Ju n h3) = (Submodule.span ℤ (idealMeetOrder n 1 (Ju n h3))).map
          (kappaLin n) by
        rw [idealLat, show kappa n = kappaLin n from funext fun x => (kappaLin_apply n x).symm,
          Submodule.span_image],
        latN_eq_map' _ (tb'K n) (tyzForm7'_conj_tau hn), latN_eq_map' _ (tbK n) (tyzForm7_conj_tau hn),
        map_mulLeft_span_pair, kappaLin, ← Submodule.map_mul, latNK7c hn hsq]
    have hrec := hS n 1 hsq e he ⟨_, hJO⟩ (γ * ρ * γ⁻¹) hρe (-(n : ℤ)) hD (tyzForm7 n hn).conj
      (tyzForm7' n hn).conj (kappa n (-uK n)) hlat hlatN
    have h1 : galPt (γ * ρ * γ⁻¹) (heegnerPt (tyzForm7 n hn).conj) =
        galPt γ (galPt ρ (heegnerPt (tyzForm7 n hn))) := by
      rw [← hconj, ← galPt_mul, show γ * ρ * γ⁻¹ * γ = γ * ρ by group, galPt_mul]
    have h2 : heegnerPt (tyzForm7' n hn).conj = Package.ptT - heegnerPt (tyzForm7 n hn) := by
      rw [← cmComplexConj γ hγ _ (tyzForm7' n hn), hfr, map_sub, Package.galPt_ptT, ← hconj,
        hγ.galPt_galPt]
    have h4 : galPt ρ (heegnerPt (tyzForm7 n hn)) = Package.ptT - heegnerPt (tyzForm7 n hn).conj := by
      have := congrArg (galPt γ) (h1.symm.trans (hrec.trans h2))
      rw [hγ.galPt_galPt, map_sub, Package.galPt_ptT, hconj] at this
      exact this
    rw [h4]; abel

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


open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem of cm-bridge, textbook CM form**: as the previous theorem, with TYZ Theorem 3.6(3)
replaced by the textbook leaves it is derived from in §14 — tyz-cm's `ShimuraReciprocityPic` (main
theorem of CM for Heegner points of `X₀(32)`, Gross's form), x0-32's `X0.EtaModelFricke` (the Fricke
involution acts on `A` as `P ↦ T − P`) and cm-points' `CM.CMAlgebraic` (CM values are algebraic) —
and `TYZSigmaShiftsF0` replaced by cm-points' `TYZSigmaFixesZn` (which tyz-cm derives from the same
two leaves, `Shimura.tyzSigmaFixesZn_of`, branch `wip/tyz-cm`; tyz-cm also derives
`CM.CMFieldOfDefinition ringClassFieldD` from `ShimuraReciprocityPic`). -/
theorem tyzThm35ReadingA_of_ringClassD_sigmaFixesZn_lemma318_thm35First_lemma321Five_shimura
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : CM.CMFieldOfDefinition ringClassFieldD) (hs : TYZSigmaFixesZn)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (hS : TyzCm.ShimuraReciprocityPic) (hF : X0.EtaModelFricke)
    (hA : CMAlgebraic) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_pinnedLeaves h11 h1 h29 (RingClassBridge.cmFieldTYZ_of_ringClassD hcm)
    RingClassBridge.iInH4 hs RingClassBridge.hprimeNormal h318 (cmFieldOfDefinition7_of hcm)
    genusFieldLeLni h35 h5
    (lemma321Seven_of' (cmFieldOfDefinition7_of hcm) (tyzThm36Seven_of hS hF hA))


/-! ## §15. Combination with tyz-cm (branch `wip/tyz-cm`, merged): the CM side from one textbook leaf

tyz-cm proves x0-32's leaves `X0.EtaModelFricke` (`Shimura.etaModelFricke`) and
`X0.EtaModelInvariant`, derives `ShimuraReciprocityPic` and `CMValueRingClass` from its textbook leaf
`Shimura.ShimuraReciprocityModFn`, `CM.CMFieldOfDefinition ringClassFieldD` from `CMValueRingClass`
and `TYZSigmaFixesZn` from `ShimuraReciprocityPic` + `EtaModelFricke`. With §14 and `CMAlgebraic`
(derived here from `CMValueRingClass`), the CM side of TYZ reading A rests on
`Shimura.ShimuraReciprocityModFn` alone. -/

section TyzCmCombined

open WeierstrassCurve.Affine

/-- The verbatim copy of §14 is tyz-cm's leaf. -/
theorem tyzCm_shimuraReciprocityPic_eq :
    TyzCm.ShimuraReciprocityPic = Shimura.ShimuraReciprocityPic := rfl

/-- **cm-points' leaf `CM.CMAlgebraic` from tyz-cm's `CMValueRingClass`** (the values `x(τ_Q)`,
`y(τ_Q)` are algebraic; the point they define, or `0`, maps to `φ(τ_Q)`). -/
theorem cmAlgebraic_of_cmValue (hV : Shimura.CMValueRingClass) : CMAlgebraic := by
  classical
  intro D Q
  obtain ⟨a, -, ha⟩ := hV 32 _ (Shimura.isRatModFn_xC_of Shimura.etaModelInvariant
    Shimura.etaCuspGrowth Shimura.xQExpRational) D Q
  obtain ⟨b, -, hb⟩ := hV 32 _ (Shimura.isRatModFn_yC_of Shimura.etaModelInvariant
    Shimura.etaCuspGrowth Shimura.yQExpRational) D Q
  by_cases h : curveAbar.toAffine.Nonsingular a b
  · refine ⟨.some a b h, ?_⟩
    have h' : X0.curveAC.toAffine.Nonsingular (X0.xC Q.tauH) (X0.yC Q.tauH) := by
      rw [← ha, ← hb]; exact Shimura.nonsingular_iff_C.2 h
    simp only [toC, X0.phiC, h', ↓reduceDIte]
    simp only [Point.map_some, Point.some.injEq]
    exact ⟨ha, hb⟩
  · refine ⟨0, ?_⟩
    have h' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC Q.tauH) (X0.yC Q.tauH) := by
      rw [← ha, ← hb]; exact fun h'' => h (Shimura.nonsingular_iff_C.1 h'')
    simp only [X0.phiC, h', ↓reduceDIte, map_zero]

/-- **`TYZThm36Seven` (TYZ Theorem 3.6(3)) from tyz-cm's one textbook leaf.** -/
theorem tyzThm36Seven_of_shimuraModFn (hS : Shimura.ShimuraReciprocityModFn) : TYZThm36Seven :=
  tyzThm36Seven_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS) Shimura.etaModelFricke
    (cmAlgebraic_of_cmValue (Shimura.cmValueRingClass_of_modFn hS))

end TyzCmCombined

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem, combined with tyz-cm: TYZ reading A from the three `𝓛`-leaves, the one
textbook CM leaf `Shimura.ShimuraReciprocityModFn` (main theorem of complex multiplication for
values of modular functions on `X₀(N)` at Heegner points, Gross's form; tyz-cm) and the TYZ
results `Lemma318Literal` (Lemma `torsion2`), `Thm35First` (Thm 3.3/3.5) and `Lemma321Five`
(Lemma 3.21(1)).** -/
theorem tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_ringClassD_sigmaFixesZn_lemma318_thm35First_lemma321Five_shimura h11 h1 h29
    (Shimura.cmFieldOfDefinition_of_shimuraModFn hS)
    (Shimura.tyzSigmaFixesZn_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS)
      Shimura.etaModelFricke)
    h318 h35 h5 (Shimura.shimuraReciprocityPic_of_shimuraModFn hS) Shimura.etaModelFricke
    (cmAlgebraic_of_cmValue (Shimura.cmValueRingClass_of_modFn hS))

end ZInQ.Contrib.TYZGenus.CMBridge

/-! ## §16a. tyz-321: existence of a lift of `β₁` (`BetaOneLiftExists`)

Number theory (`exists_prime_beta`: Dirichlet's theorem for `p ≡ 1 (mod 8)`, `p ≡ −2` modulo the odd parts;
`legendre_eq_betaOneSign`: quadratic reciprocity for Jacobi symbols), the action of an absolute
Frobenius on `√D` (`frob_sqrt`; absolute Frobenius elements copied from
`ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean`), and compactness of `Gal(ℚ̄/ℚ)`
(`betaOneLiftExists`). -/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.T321B

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  NumberField ZMod
open scoped NumberTheorySymbols

/-! ### Number theory: a prime `p` with `(D/p) = betaOneSign D` for finitely many `D` -/

theorem oddPart_facts {D : ℤ} (hD : Squarefree D) :
    oddPartSqfree D % 2 = 1 ∧ (D = oddPartSqfree D ∨ D = 2 * oddPartSqfree D) := by
  unfold oddPartSqfree
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    refine ⟨?_, Or.inr (by rw [Int.mul_ediv_cancel_left _ two_ne_zero])⟩
    rw [Int.mul_ediv_cancel_left _ two_ne_zero]
    by_contra hc
    have h4 : (2 : ℤ) * 2 ∣ 2 * c := by
      obtain ⟨e, he⟩ : 2 ∣ c := by omega
      exact ⟨e, by rw [he]; ring⟩
    have := hD 2 h4
    rw [Int.isUnit_iff] at this
    omega
  · exact ⟨by omega, Or.inl rfl⟩

theorem betaOneSign_eq_if {D : ℤ} (hD : Squarefree D) :
    betaOneSign D = if (oddPartSqfree D).natAbs % 8 = 1 ∨ (oddPartSqfree D).natAbs % 8 = 3
      then 1 else -1 := by
  obtain ⟨hodd, hDv⟩ := oddPart_facts hD
  unfold betaOneSign
  set v := oddPartSqfree D with hv
  rcases Int.natAbs_eq v with h | h
  · have hD0 : ¬ D < 0 := by omega
    rw [if_neg hD0, one_mul]
    rw [h] at hodd ⊢
    split_ifs <;> omega
  · have hD0 : D < 0 := by omega
    rw [if_pos hD0]
    rw [h] at hodd ⊢
    split_ifs <;> omega

theorem legendre_eq_betaOneSign (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) {D : ℤ}
    (hD : Squarefree D)
    (hpm : (p : ℤ) % ((oddPartSqfree D).natAbs : ℤ) = (-2) % ((oddPartSqfree D).natAbs : ℤ)) :
    legendreSym p D = betaOneSign D := by
  obtain ⟨hodd, hDv⟩ := oddPart_facts hD
  set v := oddPartSqfree D with hv
  set m := v.natAbs with hmdef
  have hm : Odd m := by
    rw [Nat.odd_iff]; omega
  have hpodd : Odd p := Nat.odd_iff.2 (by omega)
  have hp4 : p % 4 = 1 := by omega
  have hJ2 : J(2 | p) = 1 := by
    rw [jacobiSym.at_two hpodd, χ₈_nat_eq_if_mod_eight]
    simp [show p % 2 ≠ 0 by omega, hp8]
  have hJm1 : J(-1 | p) = 1 := by
    rw [jacobiSym.at_neg_one hpodd, χ₄_nat_eq_if_mod_four]
    simp [show p % 2 ≠ 0 by omega, hp4]
  have hJm : J(m | p) = χ₈' m := by
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four hp4 hm, jacobiSym.mod_left' hpm,
      jacobiSym.at_neg_two hm]
  have hJv : J(v | p) = χ₈' m := by
    rcases Int.natAbs_eq v with h | h
    · rw [h, hJm]
    · rw [h, show -((m : ℕ) : ℤ) = -1 * (m : ℤ) by ring, jacobiSym.mul_left, hJm1, one_mul, hJm]
  rw [jacobiSym.legendreSym.to_jacobiSym, betaOneSign_eq_if hD, ← hmdef]
  have hχ : χ₈' (m : ZMod 8) = if m % 8 = 1 ∨ m % 8 = 3 then 1 else -1 := by
    rw [χ₈'_nat_eq_if_mod_eight, if_neg (show ¬ (m % 2 = 0) by rw [Nat.odd_iff] at hm; omega)]
  rcases hDv with h | h
  · rw [h, hJv, hχ]
  · rw [h, jacobiSym.mul_left, hJ2, one_mul, hJv, hχ]

theorem odd_sq_mod_eight {M : ℤ} (hM : M % 2 = 1) : ∃ t : ℤ, M ^ 2 = 8 * t + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, M = 2 * j + 1 := ⟨M / 2, by omega⟩
  obtain ⟨e, he⟩ := Int.even_mul_succ_self j
  exact ⟨e, by rw [show (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 by ring, he]; ring⟩

/-- **Dirichlet + CRT**: for finitely many squarefree `D` and any bound `B` there is a prime `p > B`,
`p ≡ 1 (mod 8)`, `p ≡ −2` modulo the odd part of every `D`. -/
theorem exists_prime_beta (S : Finset ℤ) (B : ℕ) :
    ∃ p : ℕ, p.Prime ∧ B < p ∧ p % 8 = 1 ∧ ∀ D ∈ S, Squarefree D →
      (p : ℤ) % ((oddPartSqfree D).natAbs : ℤ) = (-2) % ((oddPartSqfree D).natAbs : ℤ) := by
  classical
  set f : ℤ → ℕ := fun D => if Squarefree D then (oddPartSqfree D).natAbs else 1 with hf
  set M : ℕ := ∏ D ∈ S, f D with hM
  have hfodd : ∀ D, Odd (f D) := by
    intro D
    simp only [hf]
    split_ifs with h
    · rw [Nat.odd_iff]; have := (oddPart_facts h).1; omega
    · exact odd_one
  have hModd : Odd M := Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    (fun D _ => hfodd D)
  have hM2 : (M : ℤ) % 2 = 1 := by rw [Nat.odd_iff] at hModd; omega
  obtain ⟨t, ht⟩ := odd_sq_mod_eight hM2
  set a : ℤ := 3 * (M : ℤ) ^ 2 - 2 with ha
  have hcop : IsCoprime a ((8 * M : ℕ) : ℤ) := by
    push_cast
    refine IsCoprime.mul_right ?_ ?_
    · rw [show (8 : ℤ) = 2 ^ 3 by norm_num]
      refine IsCoprime.pow_right ?_
      exact ⟨1, -(12 * t), by rw [ha, ht]; ring⟩
    · obtain ⟨j, hj⟩ : ∃ j, (M : ℤ) = 2 * j + 1 := ⟨(M : ℤ) / 2, by omega⟩
      exact ⟨j, 1 - 3 * j * M, by rw [ha, hj]; ring⟩
  obtain ⟨p, hpB, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_zmodEq B
    (q := 8 * M) (by have := hModd.pos; omega) hcop
  refine ⟨p, hp, hpB, ?_, ?_⟩
  · have h8 : (p : ℤ) ≡ a [ZMOD 8] := Int.ModEq.of_mul_right M (by push_cast at hpa; exact hpa)
    have : a % 8 = 1 := by rw [ha, ht]; omega
    have := h8.eq
    omega
  · intro D hD hsq
    have hdvd : ((oddPartSqfree D).natAbs : ℤ) ∣ (M : ℤ) := by
      have : f D ∣ M := Finset.dvd_prod_of_mem f hD
      simp only [hf, if_pos hsq] at this
      exact_mod_cast this
    have h1 : (p : ℤ) ≡ a [ZMOD ((oddPartSqfree D).natAbs : ℤ)] :=
      Int.ModEq.of_dvd (by rw [Nat.cast_mul, Nat.cast_ofNat]; exact Dvd.dvd.mul_left hdvd 8) hpa
    have h2 : a ≡ -2 [ZMOD ((oddPartSqfree D).natAbs : ℤ)] := by
      rw [Int.modEq_iff_dvd, ha, show (-2 : ℤ) - (3 * (M : ℤ) ^ 2 - 2) = (M : ℤ) * (-3 * M) by ring]
      exact Dvd.dvd.mul_right hdvd _
    exact (h1.trans h2)

/-! ### Absolute Frobenius elements (copied from `ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
namespace `ZInQ.Contrib.ChebFD.C10`, with `GQ` renamed `GalQ`; that module imports all of Mathlib) -/

/-- `\bar ℤ`. -/
abbrev Zbar : Type := integralClosure ℤ Qbar

/-- `𝓞_E → \bar ℤ`. -/
noncomputable def toZbar (E : IntermediateField ℚ Qbar) : 𝓞 E →+* Zbar :=
  RingHom.codRestrict ((algebraMap E Qbar).comp (algebraMap (𝓞 E) E)) (integralClosure ℤ Qbar)
    (fun x => (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E Qbar))

@[simp] lemma toZbar_coe (E : IntermediateField ℚ Qbar) (x : 𝓞 E) :
    ((toZbar E x : Zbar) : Qbar) = ((x : E) : Qbar) := rfl

lemma card_quot (p : ℕ) [Fact p.Prime] : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- The Frobenius condition at `𝔓` on the elements of `\bar ℤ` lying in `F`. -/
def FrobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar) : Set GalQ :=
  {h | ∀ x y : Zbar, (x : Qbar) ∈ F → (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P}

/-- Finite layer of the absolute Frobenius (copied from `ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean`). -/
def FrobExistsFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∀ (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [IsGalois ℚ F],
      (FrobOn p P F).Nonempty

/-- Absolute Frobenius at a prime of `\bar ℤ` (copied). -/
def FrobExistsAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∃ h : GalQ, ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P


lemma frobOn_anti {p : ℕ} {P : Ideal Zbar} {F F' : IntermediateField ℚ Qbar} (hF : F ≤ F') :
    FrobOn p P F' ⊆ FrobOn p P F :=
  fun _ hh x y hx hy => hh x y (hF hx) hy

lemma isClosed_frobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ F] : IsClosed (FrobOn p P F) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro h hh
  simp only [FrobOn, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hh
  obtain ⟨x, y, hx, hy, hyP⟩ := hh
  refine ⟨(fun k => h⁻¹ * k) ⁻¹' (F.fixingSubgroup : Set GalQ), ?_, ?_, ?_⟩
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
  let t : ι → Set GalQ := fun F => FrobOn p P F.1
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
  obtain ⟨h, hres⟩ : ∃ h : GalQ, AlgEquiv.restrictNormal h F = σ :=
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


theorem natCast_mem (P : Ideal Zbar) (p : ℕ) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) :
    (p : Zbar) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ Zbar (p : ℤ) ∈ P := h1
  simpa using h2

/-! ### The Frobenius at `p` acts on `√D` by `(D/p)` -/

theorem isIntegral_sqrt {D : ℤ} {r : Qbar} (hr : r ^ 2 = (D : Qbar)) : IsIntegral ℤ r := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C D, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hr]; simp

theorem frob_sqrt (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (h : GalQ) (P : Ideal Zbar) [P.IsPrime]
    (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P)
    {D : ℤ} (hpD : ¬ (p : ℤ) ∣ D) {r : Qbar} (hr : r ^ 2 = (D : Qbar)) :
    h r = (legendreSym p D : Qbar) * r := by
  set L := legendreSym p D with hL
  have hL2 : L = 1 ∨ L = -1 := by
    have hD0 : (D : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpD
    rcases legendreSym.eq_one_or_neg_one p hD0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hhr2 : (h r) ^ 2 = (D : Qbar) := by rw [← map_pow, hr, map_intCast]
  have hc2 : ((2 : Zbar) : Qbar) = 2 := rfl
  have hc4 : ((4 : Zbar) : Qbar) = 4 := rfl
  have hri := isIntegral_sqrt hr
  have hhri := isIntegral_sqrt hhr2
  set xr : Zbar := ⟨r, hri⟩
  set xh : Zbar := ⟨h r, hhri⟩
  -- `h r − r^p ∈ P`
  have h1 : xh - xr ^ p ∈ P := hh xr (xh - xr ^ p) (by simp [xr, xh])
  -- `r^p − L r = r (D^{p/2} − L) ∈ P`
  have hpodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out)).2 hp2
  have hrp : xr ^ p = xr * (D : Zbar) ^ (p / 2) := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, xr]
    have e : p = 2 * (p / 2) + 1 := by omega
    have hcD : (((D : Zbar)) : Qbar) = (D : Qbar) := by simp
    rw [hcD]
    calc r ^ p = r ^ (2 * (p / 2) + 1) := by rw [← e]
      _ = (r ^ 2) ^ (p / 2) * r := by ring
      _ = r * (D : Qbar) ^ (p / 2) := by rw [hr]; ring
  have hdvd : (p : ℤ) ∣ D ^ (p / 2) - L := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hL, legendreSym.eq_pow]; ring
  obtain ⟨c, hc⟩ := hdvd
  have h2 : xr ^ p - (L : Zbar) * xr ∈ P := by
    rw [hrp]
    have : xr * (D : Zbar) ^ (p / 2) - (L : Zbar) * xr = xr * ((p : Zbar) * (c : Zbar)) := by
      have hc' : ((D ^ (p / 2) - L : ℤ) : Zbar) = (((p : ℤ) * c : ℤ) : Zbar) := by rw [hc]
      push_cast at hc'
      linear_combination xr * hc'
    rw [this]
    exact P.mul_mem_left _ (P.mul_mem_right _ (natCast_mem P p hPp))
  have h3 : xh - (L : Zbar) * xr ∈ P := by
    have := P.add_mem h1 h2
    rwa [show xh - xr ^ p + (xr ^ p - (L : Zbar) * xr) = xh - (L : Zbar) * xr by ring] at this
  -- `h r = ± r`
  have hpm : h r = r ∨ h r = -r := sq_eq_sq_iff_eq_or_eq_neg.1 (hhr2.trans hr.symm)
  by_contra hne
  have hneg : h r = -((L : Qbar) * r) := by
    rcases hL2 with hl | hl <;> rcases hpm with hp' | hp'
    · exact absurd (by rw [hp', hl]; push_cast; ring) hne
    · rw [hp', hl]; push_cast; ring
    · rw [hp', hl]; push_cast; ring
    · exact absurd (by rw [hp', hl]; push_cast; ring) hne
  have h4 : (2 * (L : Zbar)) * xr ∈ P := by
    have : xh - (L : Zbar) * xr = -((2 * (L : Zbar)) * xr) := by
      apply Subtype.ext
      simp only [xh, xr, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, NegMemClass.coe_neg]
      rw [hneg]; push_cast; rw [hc2]; ring
    rw [this] at h3
    exact (neg_mem_iff).1 h3
  have h5 : ((4 * D : ℤ) : Zbar) ∈ P := by
    have := P.mul_mem_left ((2 * (L : Zbar)) * xr) h4
    have e : (2 * (L : Zbar)) * xr * ((2 * (L : Zbar)) * xr) = ((4 * D : ℤ) : Zbar) := by
      apply Subtype.ext
      simp only [xr, MulMemClass.coe_mul]
      push_cast
      have hl2 : (L : Qbar) ^ 2 = 1 := by rcases hL2 with hl | hl <;> simp [hl]
      rw [hc2, hc4]
      linear_combination (4 * (L : Qbar) ^ 2) * hr + 4 * (D : Qbar) * hl2
    rwa [e] at this
  have h6 : (4 * D : ℤ) ∈ P.under ℤ := by
    show algebraMap ℤ Zbar (4 * D) ∈ P
    simpa using h5
  rw [hPp, Ideal.mem_span_singleton] at h6
  have hp := hpf.out
  have : (p : ℤ) ∣ 4 ∨ (p : ℤ) ∣ D := (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).dvd_or_dvd h6
  rcases this with h7 | h7
  · have h8 : p ∣ 2 ^ 2 := by exact_mod_cast h7
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h8))
  · exact hpD h7

/-! ### Finite level and compactness -/

theorem exists_finite_beta (S : Finset ℤ) : ∃ σ : GalQ, ∀ D ∈ S, Squarefree D →
    ∀ r : Qbar, r ^ 2 = (D : Qbar) → σ r = (betaOneSign D : Qbar) * r := by
  obtain ⟨p, hp, hpB, hp8, hcong⟩ := exists_prime_beta S (∑ D ∈ S, D.natAbs)
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨P, -, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)})
    (⊥ : Ideal Zbar) (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx' : ((algebraMap ℤ Zbar x : Zbar) : Qbar) = 0 := by rw [hx]; rfl
      have : (x : Qbar) = 0 := by simpa using hx'
      have hx0 : x = 0 := by exact_mod_cast this
      rw [hx0]; exact Ideal.zero_mem _)
  obtain ⟨h, hh⟩ := frobExistsAt_of_finite frobExistsFinite p P hPp
  refine ⟨h, fun D hD hsq r hr => ?_⟩
  have hD0 : D ≠ 0 := hsq.ne_zero
  have hpD : ¬ (p : ℤ) ∣ D := by
    intro hdvd
    have h1 : D.natAbs ≤ ∑ D ∈ S, D.natAbs :=
      Finset.single_le_sum (f := fun D : ℤ => D.natAbs) (fun _ _ => Nat.zero_le _) hD
    have h2 : p ∣ D.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 hdvd
      simpa using this
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.2 hD0) h2
    omega
  rw [frob_sqrt p hp2 h P hPp hh hpD hr, legendre_eq_betaOneSign p hp8 hsq (hcong D hD hsq)]

/-- **Glue BETA-EX proved**: a lift of `β₁ = r_∞(−1)r₂(−2)` exists (compactness of `Gal(ℚ̄/ℚ)`;
at each finite level a Frobenius at a prime `p ≡ 1 (mod 8)`, `p ≡ −2` modulo the odd parts, by
Dirichlet, acts on `√D` by `(D/p) = betaOneSign D`, by quadratic reciprocity). -/
theorem betaOneLiftExists : ∃ σ : GalQ, IsBetaOneLift σ := by
  let t : Finset ℤ → Set GalQ := fun S => {σ | ∀ D ∈ S, Squarefree D →
    ∀ r : Qbar, r ^ 2 = (D : Qbar) → σ r = (betaOneSign D : Qbar) * r}
  have htd : Directed (· ⊇ ·) t := by
    intro S S'
    refine ⟨S ∪ S', fun σ hσ D hD => hσ D (Finset.mem_union_left _ hD),
      fun σ hσ D hD => hσ D (Finset.mem_union_right _ hD)⟩
  have htn : ∀ S, (t S).Nonempty := fun S => exists_finite_beta S
  have htcl : ∀ S, IsClosed (t S) := by
    intro S
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro σ hσ
    simp only [t, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hσ
    obtain ⟨D, hD, hsq, r, hr, hne⟩ := hσ
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {r}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral r)
    refine ⟨(fun k => σ⁻¹ * k) ⁻¹' ((IntermediateField.adjoin ℚ {r}).fixingSubgroup : Set GalQ),
      ?_, ?_, ?_⟩
    · intro k hk hkt
      have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hk r
        (IntermediateField.mem_adjoin_simple_self ℚ r)
      change σ⁻¹ (k r) = r at hfix
      have hkr : k r = σ r := by
        have e := congrArg σ hfix
        rwa [show σ (σ⁻¹ (k r)) = k r from AlgEquiv.apply_symm_apply σ _] at e
      exact hne (hkr ▸ hkt D hD hsq r hr)
    · exact (IntermediateField.fixingSubgroup_isOpen _).preimage
        (continuous_const.mul continuous_id)
    · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact one_mem _
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun S => (htcl S).isCompact) htcl
  refine ⟨σ, fun D hsq r hr => ?_⟩
  exact (Set.mem_iInter.1 hσ {D}) D (Finset.mem_singleton_self D) hsq r hr

end ZInQ.Contrib.TYZGenus.T321B

/-! ## §16. tyz-321: `Lemma321Five` (TYZ Lemma 3.21(1)) from Shimura reciprocity, ring class field
theory and genus theory

Task tyz-321 (2026-11-14). Report: `docs/research/tyz-321.md`; log: `scratch/tyz-321/log.md`.
Everything above this section is a verbatim copy of `scratch/cm-bridge/Bridge.lean` (§0–§15, without
its axiom-audit lines), which contains the statement `CMBridge.Lemma321Five` and everything it
depends on. -/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.T321

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.Contrib.TYZGenus.CMBridge ZInQ.PropN NumberField
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.RingClassBridge

/-! ### The class of `σ_ϖ` -/

/-- The odd part `𝔞 = (m, √−d − 1)`, `m = (d+1)/2`, of the principal ideal `(√−d − 1)` of
`𝓞_{K_d} = ℤ[√−d]` (`d ≡ 1 (mod 4)`): `(√−d − 1) = 𝔭₂ 𝔞`, `N𝔞 = m` (odd for `d ≡ 5 (mod 8)`). -/
def varpiIdeal (d : ℕ) [NeZero d] : Ideal (𝓞 (QNeg d)) :=
  Ideal.span {(((d + 1) / 2 : ℕ) : 𝓞 (QNeg d)), sqrtNeg d - 1}

open Classical in
/-- **The class `w ∈ Pic(O_{d,4})` of TYZ's `σ_ϖ`, `ϖ = √−d − 1`**: the Picard class of the contraction
of `𝔞` (`varpiIdeal`), an ideal prime to the conductor (`1` otherwise; never taken for
`d ≡ 5 (mod 8)`). The idele `ϖ` at the place 2 and the ideal `(ϖ)𝔭₂⁻¹ = 𝔞` have inverse Artin
symbols, so `w = σ_ϖ^{∓1}`; TYZ's `ϖ = 1 + √−d` gives the conjugate ideal, i.e. `w^{−1}`. The
statements below only use `w` modulo `ℤτ(1)` and are insensitive to `w ↔ w⁻¹`. -/
def wClass (d : ℕ) [NeZero d] : Pic (O4 d) :=
  if h : varpiIdeal d ∈ integralIdealsPrimeTo (O4 d).conductorModulus then (O4 d).picClass ⟨_, h⟩
  else 1

/-! ### The inputs (named `Prop`s) -/

/-- **Glue BETA-EX (existence of a lift of `β₁`)**: some `σ ∈ Gal(ℚ̄/ℚ)` acts on every quadratic field
as the idele `β₁ = r_∞(−1)r₂(−2)`. True because `D ↦ betaOneSign D` is a character of
`ℚ^×/ℚ^{×2}` (product of Hilbert symbols) and `Gal(ℚ(√D : D)/ℚ) = Hom(ℚ^×/ℚ^{×2}, ±1)` (Kummer
theory, with compactness of `Gal(ℚ̄/ℚ)`). TYZ L2496–2500 take "any lifting" of `β₁`. -/
def BetaOneLiftExists : Prop := ∃ σ : GalQ, IsBetaOneLift σ

/-- `z_n ∈ A(H_{n,4})` (consequence of the CM field of definition; proved below from
`Shimura.ShimuraReciprocityModFn`). -/
def ZnOverH4 : Prop := ∀ n : ℕ, n % 8 = 5 → Squarefree n → tyzZn n ∈ ptsOver (H4bar n)

/-- **TYZ Theorem 3.6(1), conjugation part (pinned)**: `z̄_n = −z_n + τ(1)` for squarefree
`n ≡ 5 (mod 8)` and complex conjugation `γ` (TYZ L1408–1428, as re-derived in rv-tyz-inputs §1.5,
"`z̄_n = −z_n + τ(1)`"). `τ(1) = tauG 2 = (0,0)`. -/
def TYZThm36ConjFive : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∀ γ : GalQ, IsComplexConj γ →
    galPt γ (tyzZn n) = tauG 2 - tyzZn n

/-- **TYZ Theorem 3.6(1), `σ_ϖ` part (pinned, modulo `ℤτ(1)`)**: every `ρ` acting on `H_{n,4}` as
the Artin symbol of `w = [𝔞]` moves `z_n` by `τ((1+i)/2) = tauG (1+i)` modulo `ℤτ(1)`. TYZ
Theorem 3.6(1): `z_n^{σ_ϖ} = z_n + τ((1+i)/2)` (rv-tyz-inputs §1.5). -/
def TYZThm36OneFive : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n → ∀ ρ : GalQ, ActsAsArtin4 ρ n (wClass n) →
    ∃ k : ℤ, galPt ρ (tyzZn n) = tyzZn n + tauG ⟨1, 1⟩ + k • tauG 2

/-- **Glue W-I (`σ_w` negates `i`)**: every `ρ` acting on `H_{n,4}` as `w` maps `i` to `−i`. Genus
theory: `K_n(i) = K_n(√n) ⊆ H_n` and `Art(𝔞)` acts on it by `Π_{q ∣ n} χ_q([𝔞]) = Π_q (N𝔞/q) =
Π_q (2/q) = (2/n) = −1` (`N𝔞 = (n+1)/2 ≡ 1/2 mod q`, `n ≡ 5 (mod 8)`). -/
def WNegatesI : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n → ∀ ρ : GalQ, ActsAsArtin4 ρ n (wClass n) →
    ρ iQ = -iQ

/-- **Glue KER (`Gal(H_{n,4}/H_n)` moves `z_n` only by `ℤτ(1)`)**: TYZ L2540 ("`z_n^σ ∈ z_n + {0, τ(1)}`"
for `σ ∈ Gal(H'_n/H_n)`). -/
def KerFixesZnMod : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n → ∀ k : Pic (O4 n), picToMax (O4 n) k = 1 →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n k → ∃ j : ℤ, galPt ρ (tyzZn n) = tyzZn n + j • tauG 2

/-- **Glue BETA-5 (`β₁` on the genus field, class 5)**: for a lift `σ` of `β₁` and complex conjugation
`γ`, the class `a ∈ Pic(O_{n,4})` of `σγ⁻¹` (which fixes `K_n`) is `w` modulo squares in `Cl(K_n)`.
TYZ L2526–2531 ("`β'_j` acts on `L_n(i)` as `σ_ϖ ∘ c`"); by genus theory (`Cl² = ⋂ ker χ_q`) it is
the equality of genus characters `χ_q(a) = χ_q(w) = (2/q)` for `q ∣ n`. -/
def BetaOnGenus5 : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n → ∀ σ γ : GalQ, IsBetaOneLift σ →
    IsComplexConj γ → ∀ a : Pic (O4 n), ActsAsArtin4 (σ * γ⁻¹) n a →
      picToMax (O4 n) (a * (wClass n)⁻¹) ∈ picSquares (OK n)

/-! ### Glue: Artin symbols of `O_{d,4}` in `ℚ̄` -/

section Acts4

variable {d : ℕ} [NeZero d]

theorem acts4_iff {ρ : GalQ} {c : Pic (O4 d)} : ActsAsArtin4 ρ d c ↔ ActsAsArtinO d (O4 d) ρ c :=
  Iff.rfl

theorem acts4_mul {ρ ρ' : GalQ} {c c' : Pic (O4 d)} (hρ : ActsAsArtin4 ρ d c)
    (hρ' : ActsAsArtin4 ρ' d c') : ActsAsArtin4 (ρ * ρ') d (c * c') := by
  intro x
  rw [AlgEquiv.mul_apply, hρ' x, hρ (artin4 d c' x), map_mul, AlgEquiv.mul_apply]

theorem acts4_agree {ρ ρ' : GalQ} {c : Pic (O4 d)} (hρ : ActsAsArtin4 ρ d c)
    (hρ' : ActsAsArtin4 ρ' d c) : ∀ x ∈ H4bar d, ρ x = ρ' x := by
  intro x hx
  rw [H4bar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ρ (embed d y) = embed d ((artin4 d c ⟨y, hy⟩ : H4 d) : SeparableClosure (QNeg d)) :=
    hρ ⟨y, hy⟩
  have h2 : ρ' (embed d y) = embed d ((artin4 d c ⟨y, hy⟩ : H4 d) : SeparableClosure (QNeg d)) :=
    hρ' ⟨y, hy⟩
  change ρ (embed d y) = ρ' (embed d y)
  rw [h1, h2]

theorem acts4_galPt {ρ ρ' : GalQ} {c : Pic (O4 d)} (hρ : ActsAsArtin4 ρ d c)
    (hρ' : ActsAsArtin4 ρ' d c) {P : PtA} (hP : P ∈ ptsOver (H4bar d)) :
    galPt ρ P = galPt ρ' P :=
  galPt_congr (acts4_agree hρ hρ') hP

/-- The image of `√−d` in `ℚ̄`. -/
abbrev omegaBar (d : ℕ) [NeZero d] : Qbar :=
  embed d (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega)

theorem omegaBar_sq : omegaBar d ^ 2 = -(d : Qbar) := by
  simp only [omegaBar]
  rw [← map_pow, ← map_pow]
  simp [QuadraticAlgebra.omega_pow_two_eq_add]

/-- **An automorphism of `ℚ̄` fixing `K_d` acts on `H_{d,4}` as an Artin symbol.** -/
theorem exists_acts4_of_fix {ρ : GalQ} (hρ : ρ (omegaBar d) = omegaBar d) :
    ∃ a : Pic (O4 d), ActsAsArtin4 ρ d a := by
  have hb := (Algebra.IsAlgebraic.algHom_bijective₂ (embed d)
    (IsAlgClosed.lift : Qbar →ₐ[ℚ] SeparableClosure (QNeg d))).1
  set e := AlgEquiv.ofBijective (embed d) hb
  set τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d) := e.trans (ρ.trans e.symm)
  have he : ∀ y, e y = embed d y := fun y => rfl
  have hγτ : ∀ y, ρ (embed d y) = embed d (τ y) := by
    intro y
    rw [← he, ← he]
    simp [τ]
  have hτω : τ (algebraMap (QNeg d) _ QuadraticAlgebra.omega) =
      algebraMap (QNeg d) _ QuadraticAlgebra.omega := by
    apply (embed d).injective
    change embed d (τ _) = embed d _
    rw [← hγτ]
    exact hρ
  have hq : ∀ q : ℚ, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) (algebraMap ℚ (QNeg d) q)) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) (algebraMap ℚ (QNeg d) q) := by
    intro q
    rw [← IsScalarTower.algebraMap_apply]
    exact τ.commutes q
  have hcomm : ∀ k : QNeg d, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) k) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) k := by
    intro k
    have hk : k = algebraMap ℚ (QNeg d) k.re + algebraMap ℚ (QNeg d) k.im * QuadraticAlgebra.omega := by
      ext <;> simp
    rw [hk, map_add, map_mul, map_add, map_mul, hq, hq, hτω]
  let τK : SeparableClosure (QNeg d) ≃ₐ[QNeg d] SeparableClosure (QNeg d) :=
    { τ with commutes' := hcomm }
  refine ⟨(artin4 d).symm (AlgEquiv.restrictNormal τK (H4 d)), fun x => ?_⟩
  rw [MulEquiv.apply_symm_apply, hγτ]
  congr 1
  exact (AlgEquiv.restrictNormal_commutes τK (H4 d) x).symm

end Acts4

/-! ### Glue: torsion bookkeeping -/

section Tors

theorem galPt_tauG_two (ρ : GalQ) : galPt ρ (tauG 2) = tauG 2 := by
  rw [← one_add_one_eq_two, map_add, tauG_apply, one_smul, map_add, galPt_ptT]

theorem tauG_one_one_add : tauG ⟨1, 1⟩ + tauG ⟨1, -1⟩ = tauG 2 := by
  rw [← map_add]; rfl

theorem iQ_cases (ρ : GalQ) : ρ iQ = iQ ∨ ρ iQ = -iQ := by
  have h : (ρ iQ) ^ 2 = iQ ^ 2 := by rw [← map_pow, iQ_sq, map_neg, map_one]
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

/-- An automorphism negating `i` anticommutes with `[i]`. -/
theorem galPt_iPt_of_neg {ρ : GalQ} (hρ : ρ iQ = -iQ) (P : PtA) :
    galPt ρ (iPt P) = -iPt (galPt ρ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h1, e1⟩ := galPt_some ρ (nonsingular_iPt h)
    obtain ⟨h2, e2⟩ := galPt_some ρ h
    rw [iPt_some, e1, e2, iPt_some, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨by rw [map_neg], ?_⟩
    rw [map_mul, hρ]
    simp only [WeierstrassCurve.Affine.negY, curveAbar_a₁, curveAbar_a₃]
    ring

theorem galPt_tauG_one_one (ρ : GalQ) :
    ∃ j : ℤ, galPt ρ (tauG ⟨1, 1⟩) = tauG ⟨1, 1⟩ + j • tauG 2 := by
  rcases iQ_cases ρ with h | h
  · exact ⟨0, by rw [galPt_tauG ρ h, zero_zsmul, add_zero]⟩
  · refine ⟨1, ?_⟩
    have h2 : tauG 2 = (2 : ℤ) • iPt ptT := by
      rw [two_zsmul_iPt_ptT, ← two_zsmul_ptT, ← one_add_one_eq_two, map_add, tauG_apply, one_smul,
        two_zsmul]
    have h4 : (4 : ℤ) • iPt ptT = 0 := by
      rw [show (4 : ℤ) = 2 + 2 by norm_num, add_zsmul, two_zsmul_iPt_ptT, pt00_add_self]
    rw [tauG_mk, map_add, one_smul, one_smul, galPt_ptT, galPt_iPt_of_neg h, galPt_ptT, one_smul,
      h2]
    have : -iPt ptT = iPt ptT + (2 : ℤ) • iPt ptT - (4 : ℤ) • iPt ptT := by
      rw [show (4 : ℤ) = 1 + 2 + 1 by norm_num, add_zsmul, add_zsmul, one_zsmul]; abel
    rw [this, h4]; abel

end Tors

/-! ### `TYZThm36ConjFive` from the Fricke involution and `τ ↦ τ + 1/4`

`τ_{Q̄} = W T₄ W τ_Q` (`W τ = −1/(32τ)`, `T₄ τ = τ + 1/4`), `φ(Wτ) = T − φ(τ)` (Fricke, proved by
tyz-cm) and `φ(τ + 1/4) = [i]φ(τ)` (proved here from the theta form of `x` and the eta form of `y`),
so `c(f₀(P_n)) = f₀(P_{Q̄}) = [i]f₀(P_n) + T − [i]T` and `c(z_n) = −z_n + τ(1)`. -/

section Conj

open Complex WeierstrassCurve.Affine

theorem etaD_add_quarter {d m : ℕ} (h : d = 4 * m) (z : ℂ) :
    X0.etaD d (z + 1 / 4) = cexp (2 * Real.pi * I / 24) ^ m * X0.etaD d z := by
  unfold X0.etaD
  rw [show (d : ℂ) * (z + 1 / 4) = d * z + (m : ℕ) by rw [h]; push_cast; ring, X0.eta_add_nat,
    ← Complex.exp_nat_mul]
  congr 2
  ring

theorem cexp_pi_div_two : cexp (Real.pi / 2 * I) = I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem cexp_pow_6 : cexp (2 * Real.pi * I / 24) ^ 6 = I := by
  rw [← Complex.exp_nat_mul,
    show ((6 : ℕ) : ℂ) * (2 * Real.pi * I / 24) = Real.pi / 2 * I by push_cast; ring]
  exact cexp_pi_div_two

/-- **`y(z + 1/4) = i·y(z)`** (`y` is an eta quotient in `η(4z), η(8z), η(16z), η(32z)`). -/
theorem yC_add_quarter (z : ℂ) : X0.yC (z + 1 / 4) = I * X0.yC z := by
  unfold X0.yC
  rw [etaD_add_quarter (m := 2) (by norm_num), etaD_add_quarter (m := 4) (by norm_num),
    etaD_add_quarter (m := 1) (by norm_num), etaD_add_quarter (m := 8) (by norm_num)]
  set c := cexp (2 * Real.pi * I / 24)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have key : c ^ 16 = I * c ^ 34 := by
    rw [← cexp_pow_6, show c ^ 34 = c ^ 10 * c ^ 24 by ring, X0.cexp_pow_24]; ring
  have e : (c ^ 2 * X0.etaD 8 z) ^ 4 * (c ^ 4 * X0.etaD 16 z) ^ 2 /
      ((c ^ 1 * X0.etaD 4 z) ^ 2 * (c ^ 8 * X0.etaD 32 z) ^ 4) =
      c ^ 16 * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2) /
        (c ^ 34 * (X0.etaD 4 z ^ 2 * X0.etaD 32 z ^ 4)) := by ring
  rw [e, key, show I * c ^ 34 * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2) =
    c ^ 34 * (I * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2)) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ hc)]
  ring

/-- `τ ↦ τ + 1/4` on `ℍ`. -/
def quarterH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + 1 / 4, by
    show 0 < ((τ : ℂ) + 1 / 4).im
    simpa using τ.im_pos⟩

theorem Qt_add_quarter (z : ℂ) : Shimura.Qt (z + 1 / 4) = Shimura.Qt z * I := by
  rw [Shimura.Qt_def, Shimura.Qt_def,
    show 2 * Real.pi * I * (z + 1 / 4) = 2 * Real.pi * I * z + Real.pi / 2 * I by ring,
    Complex.exp_add, cexp_pi_div_two]

/-- **`x(τ + 1/4) = −x(τ)`** (`x = 2θ(0;16τ)/(q²θ(8τ;16τ))`, tyz-cm's `xC_theta`). -/
theorem xC_add_quarter (τ : UpperHalfPlane) : X0.xC ((τ : ℂ) + 1 / 4) = -X0.xC τ := by
  have h1 := Shimura.xC_theta (quarterH τ)
  have h2 := Shimura.xC_theta τ
  change X0.xC ((quarterH τ : UpperHalfPlane) : ℂ) = _
  rw [h1, h2]
  have e1 : (16 : ℂ) * ((quarterH τ : UpperHalfPlane) : ℂ) = 16 * τ + 2 + 2 := by
    show (16 : ℂ) * ((τ : ℂ) + 1 / 4) = _; ring
  have e2 : (8 : ℂ) * ((quarterH τ : UpperHalfPlane) : ℂ) = 8 * τ + 1 + 1 := by
    show (8 : ℂ) * ((τ : ℂ) + 1 / 4) = _; ring
  have e3 : Shimura.Qt ((quarterH τ : UpperHalfPlane) : ℂ) = Shimura.Qt τ * I :=
    Qt_add_quarter τ
  rw [e1, e2, e3]
  simp only [jacobiTheta₂_add_right, jacobiTheta₂_add_left]
  rw [mul_pow, I_sq]
  ring

theorem curveAC_a₂ : X0.curveAC.a₂ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₄ : X0.curveAC.a₄ = 4 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₆ : X0.curveAC.a₆ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]

theorem nonsingular_iC {x y : ℂ} (h : X0.curveAC.toAffine.Nonsingular x y) :
    X0.curveAC.toAffine.Nonsingular (-x) (I * y) := by
  rw [nonsingular_iff', equation_iff'] at h ⊢
  simp only [Shimura.curveAC_a₁, curveAC_a₂, Shimura.curveAC_a₃, curveAC_a₄, curveAC_a₆] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by linear_combination y ^ 2 * I_sq - he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    linear_combination h'
  · right
    intro h'
    apply h
    have : I * (2 * y) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 I_ne_zero
    · linear_combination h0

theorem nonsingular_iC_iff {x y : ℂ} :
    X0.curveAC.toAffine.Nonsingular (-x) (I * y) ↔ X0.curveAC.toAffine.Nonsingular x y := by
  refine ⟨fun h => ?_, nonsingular_iC⟩
  have h2 := nonsingular_iC h
  have e1 : -(-x) = x := neg_neg x
  have e2 : I * (I * y) = X0.curveAC.toAffine.negY x y := by
    rw [Shimura.negY_AC, ← mul_assoc, I_mul_I]; ring
  rw [e1, e2] at h2
  exact (nonsingular_neg ..).1 h2

/-- **`φ(τ + 1/4) = [i]φ(τ)`**, on algebraic points. -/
theorem toC_iPt_of_quarter (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = τ + 1 / 4) (P : PtA)
    (hP : toC P = X0.phiC τ) : toC (iPt P) = X0.phiC τ' := by
  have hx : X0.xC τ' = -X0.xC τ := by rw [h, xC_add_quarter]
  have hy : X0.yC τ' = I * X0.yC τ := by rw [h, yC_add_quarter]
  unfold X0.phiC at hP ⊢
  by_cases hns : X0.curveAC.toAffine.Nonsingular (X0.xC τ) (X0.yC τ)
  · have hns' : X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy]; exact nonsingular_iC hns
    rw [dif_pos hns] at hP
    rw [dif_pos hns']
    rcases P with _ | ⟨x, y, hxy⟩
    · exact absurd hP (fun h => by cases h)
    · simp only [toC, Point.map_some, Point.some.injEq] at hP
      rw [iPt_some]
      simp only [toC, Point.map_some, Point.some.injEq]
      refine ⟨?_, ?_⟩
      · rw [hx, ← hP.1]; simp
      · rw [hy, ← hP.2, map_mul]
        congr 1
        exact ιC_iQ
  · have hns' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy]; exact fun h' => hns (nonsingular_iC_iff.1 h')
    rw [dif_neg hns] at hP
    rw [dif_neg hns']
    rcases P with _ | ⟨x, y, hxy⟩
    · rfl
    · exact absurd hP (fun h => by cases h)

theorem iPt_sub (P R : PtA) : iPt (P - R) = iPt P - iPt R := map_sub iHom P R

/-- The conjugate of TYZ's form. -/
def tbarK (n : ℕ) : QNeg n := ⟨-1 / (4 * (n + 1)), 1 / (4 * (n + 1))⟩

theorem tyzForm_conj_tau (n : ℕ) (hn : n % 8 = 5) :
    (tyzForm n hn).conj.tau = Shimura.kappa n (tbarK n) := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [HeegnerForm.tau, HeegnerForm.conj, cmPoint, tyzForm, Shimura.kappa, tbarK,
    Shimura.sqrt_64n]
  push_cast
  field_simp
  ring

theorem tbarK_mul (n : ℕ) [NeZero n] :
    tbarK n * (1 - 8 * Shimura.tauK n) = Shimura.tauK n := by
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  ext <;> simp [tbarK, Shimura.tauK, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> field_simp <;> ring

/-- `τ_{Q̄} = W T₄ W τ_Q`. -/
theorem tyzForm_conj_tauH (n : ℕ) [NeZero n] (hn : n % 8 = 5) :
    ((tyzForm n hn).conj.tauH : ℂ) =
      ((Shimura.frickeH (quarterH (Shimura.frickeH (tyzForm n hn).tauH)) : UpperHalfPlane) : ℂ) := by
  have hτ : ((tyzForm n hn).tauH : ℂ) = Shimura.kappaAlg n (Shimura.tauK n) := by
    rw [Shimura.kappaAlg_apply, ← Shimura.tyzForm_tau n hn]; rfl
  have hτ' : ((tyzForm n hn).conj.tauH : ℂ) = Shimura.kappaAlg n (tbarK n) := by
    rw [Shimura.kappaAlg_apply, ← tyzForm_conj_tau n hn]; rfl
  have hrel := congrArg (Shimura.kappaAlg n) (tbarK_mul n)
  simp only [map_mul, map_sub, map_one, map_ofNat] at hrel
  rw [← hτ, ← hτ'] at hrel
  set τ := ((tyzForm n hn).tauH : ℂ)
  have hne : τ ≠ 0 := (tyzForm n hn).tauH.ne_zero
  have hne2 : (8 * τ - 1) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact (tyzForm n hn).tauH.im_pos.ne' this
  show _ = -1 / (32 * (-1 / (32 * τ) + 1 / 4))
  rw [show (32 : ℂ) * (-1 / (32 * τ) + 1 / 4) = (8 * τ - 1) / τ by field_simp; ring]
  rw [div_div_eq_mul_div, eq_div_iff hne2]
  linear_combination -hrel

/-- **`f₀(P_{Q̄}) = [i]f₀(P_n) + T − [i]T`** (given algebraicity of the Heegner point). -/
theorem heegnerPt_tyzForm_conj (hA : CMAlgebraic) (n : ℕ) [NeZero n] (hn : n % 8 = 5) :
    heegnerPt (tyzForm n hn).conj = ptT - iPt ptT + iPt (heegnerPt (tyzForm n hn)) := by
  set Q := tyzForm n hn
  obtain ⟨P, hP⟩ := hA _ Q
  rw [heegnerPt_eq Q hP]
  apply heegnerPt_eq
  set τ₁ := Shimura.frickeH Q.tauH
  set τ₂ := quarterH τ₁
  set τ₃ := Shimura.frickeH τ₂
  have hτ₃ : Q.conj.tauH = τ₃ := UpperHalfPlane.ext (tyzForm_conj_tauH n hn)
  have e1 : X0.phiC τ₁ + X0.phiC Q.tauH = X0.ptTC := Shimura.etaModelFricke Q.tauH τ₁ rfl
  have e3 : X0.phiC τ₃ + X0.phiC τ₂ = X0.ptTC := Shimura.etaModelFricke τ₂ τ₃ rfl
  have h1 : toC (ptT - P) = X0.phiC τ₁ := by
    rw [map_sub, toC_ptT, hP, ← e1]; abel
  have h2 : toC (iPt (ptT - P)) = X0.phiC τ₂ := toC_iPt_of_quarter τ₁ τ₂ rfl _ h1
  have h3 : toC (ptT - iPt (ptT - P)) = X0.phiC τ₃ := by
    rw [map_sub, toC_ptT, h2, ← e3]; abel
  rw [hτ₃, ← h3, iPt_sub]
  congr 1
  abel

theorem isComplexConj_apply_iQ {γ : GalQ} (hγ : IsComplexConj γ) : γ iQ = -iQ := by
  apply ιC_injective
  rw [hγ, ιC_iQ, map_neg, ιC_iQ, Complex.conj_I]

/-- **`TYZThm36ConjFive` from algebraicity of Heegner points** (x0-32's Fricke leaf is proved by
tyz-cm; `τ ↦ τ + 1/4` is proved here). -/
theorem tyzThm36ConjFive_of (hA : CMAlgebraic) : TYZThm36ConjFive := by
  intro n hn hsq γ hγ
  haveI : NeZero n := ⟨by omega⟩
  have hi := isComplexConj_apply_iQ hγ
  have hc : galPt γ (tyzHeegnerPt n) = ptT - iPt ptT + iPt (tyzHeegnerPt n) := by
    simp only [tyzHeegnerPt, hn, ↓reduceDIte]
    rw [cmComplexConj γ hγ, heegnerPt_tyzForm_conj hA n hn]
  have h2 : tauG 2 = ptT + ptT := by
    rw [← one_add_one_eq_two, map_add, tauG_apply, one_smul]
  simp only [tyzZn]
  rw [map_sub, galPt_iPt_of_neg hi, sub_neg_eq_add, hc, iPt_add, iPt_sub, iPt_iPt, iPt_iPt, h2]
  abel

end Conj

/-! ### `TYZThm36OneFive` from Shimura reciprocity (`𝔞`-action on TYZ's Heegner point)

With `𝔟 = 𝔞 ∩ O_{n,4} = ℤ⟨m, −4 + 4√−n⟩` (`m = (n+1)/2`, `idealMeetOrder_varpi`), `Q = [16(n+1), −8, 1]`
and `Q'' = [32(n+4), 8(n+2), m]` (`tyzFormW`): `τ_{Q''} = W(τ_Q + 1/4)` (`tyzFormW_tauH`) and
`𝔟·(⟨1,τ_{Q''}⟩, ⟨1/32,τ_{Q''}⟩) = c·(⟨1,τ_Q⟩, ⟨1/32,τ_Q⟩)`, `c = (−1 + ((n+3)/2)√−n)/(n+4)`
(`idealLat_varpi_mul`, `idealLat_varpi_mulN`; found and checked numerically for 10 values of `n` by
`scratch/tyz-321/wlat.py`, integer coefficients by `wcoef.py`). Shimura reciprocity
(`ShimuraReciprocityPic`) then gives `σ_w(f₀(P_n)) = f₀(P_{Q''}) = T − [i]f₀(P_n)`
(`heegnerPt_tyzFormW`, Fricke + `τ ↦ τ + 1/4`), and with `σ_w(i) = −i` (`WNegatesI`),
`σ_w(z_n) = z_n + τ((1+i)/2)`. -/

section WAction

open QuadraticAlgebra Pointwise WeierstrassCurve.Affine Complex

variable {n : ℕ} [NeZero n]

def hW0 (n : ℕ) : QNeg n := ⟨((n : ℚ) + 1) / 2, 0⟩
def hW1 (n : ℕ) : QNeg n := ⟨-4, 4⟩

@[simp] theorem hW0_re : (hW0 n).re = ((n : ℚ) + 1) / 2 := rfl
@[simp] theorem hW0_im : (hW0 n).im = 0 := rfl
@[simp] theorem hW1_re : (hW1 n).re = -4 := rfl
@[simp] theorem hW1_im : (hW1 n).im = 4 := rfl

theorem natCast_m (hn : n % 8 = 5) : (((n + 1) / 2 : ℕ) : ℚ) = ((n : ℚ) + 1) / 2 := by
  have : (n + 1) / 2 * 2 = n + 1 := by omega
  have h' : (((n + 1) / 2 : ℕ) : ℚ) * 2 = (n : ℚ) + 1 := by exact_mod_cast this
  linarith

theorem coe_m (hn : n % 8 = 5) :
    (((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n))) : QNeg n) = hW0 n := by
  have h2 : (((n + 1) / 2 : ℕ) : ℚ) = ((n : ℚ) + 1) / 2 := by
    have : (n + 1) / 2 * 2 = n + 1 := by omega
    have h' : (((n + 1) / 2 : ℕ) : ℚ) * 2 = (n : ℚ) + 1 := by exact_mod_cast this
    linarith
  rw [show ((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) : QNeg n) = (((n + 1) / 2 : ℕ) : QNeg n) from
    map_natCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) _]
  ext
  · rw [QuadraticAlgebra.re_natCast, h2]; rfl
  · rw [QuadraticAlgebra.im_natCast]; rfl

theorem varpiIdeal_mem (hn : n % 8 = 5) :
    varpiIdeal n ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
    conductorModulus_finitePart]
  have key : (1 : 𝓞 (QNeg n)) = (-1) * (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) +
      4 * (((n + 3) / 8 : ℕ) : 𝓞 (QNeg n)) := by
    have h' : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) + 1 = 4 * (((n + 3) / 8 : ℕ) : 𝓞 (QNeg n)) := by
      exact_mod_cast (show (n + 1) / 2 + 1 = 4 * ((n + 3) / 8) by omega)
    linear_combination h'
  refine ⟨?_, ?_⟩
  · intro h
    have hmem : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) ∈ varpiIdeal n :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h, Ideal.mem_bot] at hmem
    have h2 := congrArg (fun x : 𝓞 (QNeg n) => ((x : QNeg n)).re) hmem
    simp only [coe_m hn, hW0] at h2
    simp at h2
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  · rw [Ideal.eq_top_iff_one, key]
    refine Ideal.add_mem _ (Ideal.mem_sup_left
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))) (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg n) 4 ((((n + 3) / 8 : ℕ)) : 𝓞 (QNeg n))

theorem wClass_eq (hn : n % 8 = 5) : wClass n = (O4 n).picClass ⟨_, varpiIdeal_mem hn⟩ := by
  unfold wClass; rw [dif_pos (varpiIdeal_mem hn)]

theorem idealMeetOrder_varpi (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealMeetOrder n 4 (varpiIdeal n) =
      (Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) : Set (QNeg n)) := by
  have hn4 : n % 4 = 1 := by omega
  have hmq := natCast_m hn
  unfold varpiIdeal
  generalize (n + 1) / 2 = m at hmq ⊢
  have hcm : ((m : 𝓞 (QNeg n)) : QNeg n) = hW0 n := by
    rw [show ((m : 𝓞 (QNeg n)) : QNeg n) = (m : QNeg n) from
      map_natCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) _]
    ext
    · rw [QuadraticAlgebra.re_natCast, hmq]; rfl
    · rw [QuadraticAlgebra.im_natCast]; rfl
  ext x
  simp only [Shimura.idealMeetOrder, Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_pair,
    Shimura.mem_O4_iff']
  constructor
  · rintro ⟨⟨c, z, hz⟩, y, hy, rfl⟩
    obtain ⟨a, b, hab⟩ := hy
    simp only [smul_eq_mul] at hab
    obtain ⟨a1, a2, ha1, ha2⟩ := Shimura.int_coords hn4 hsq a
    obtain ⟨b1, b2, hb1, hb2⟩ := Shimura.int_coords hn4 hsq b
    obtain ⟨p, q, hp, hq⟩ := Shimura.int_coords hn4 hsq z
    have hy' : (y : QNeg n) = (a : QNeg n) * hW0 n + (b : QNeg n) * (QuadraticAlgebra.omega - 1) := by
      rw [← hab]; push_cast [hcm, coe_sqrtNeg]; rfl
    have him := congrArg QuadraticAlgebra.im hz
    rw [hy'] at him
    simp [ha1, ha2, hb1, hb2, hp, hq] at him
    refine ⟨a1 + a2 - 2 * b2, q, ?_⟩
    rw [hy']
    ext
    · simp [ha1, ha2, hb1, hb2]
      linear_combination him
    · simp [ha1, ha2, hb1, hb2]
      linear_combination -him
  · rintro ⟨P, Q, rfl⟩
    refine ⟨⟨P * m - 4 * Q, (Q : 𝓞 (QNeg n)) * sqrtNeg n, ?_⟩,
      (P : 𝓞 (QNeg n)) * (m : 𝓞 (QNeg n)) + ((4 * Q : ℤ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1), ?_, ?_⟩
    · ext
      · simp [hmq, coe_sqrtNeg]
        ring
      · simp [hmq, coe_sqrtNeg]
        ring
    · exact ⟨_, _, rfl⟩
    · ext
      · simp [hmq, coe_sqrtNeg, map_ofNat]
        ring
      · simp [hmq, coe_sqrtNeg, map_ofNat]
        ring

/-- **`Q'' = [32(n+4), 8(n+2), (n+1)/2]`**, a Heegner form of level 32 and discriminant `−64n`, with
`τ_{Q''} = W(τ_Q + 1/4)`. -/
def tyzFormW (n : ℕ) (hn : n % 8 = 5) : HeegnerForm 32 (-64 * n) where
  A := 32 * (n + 4)
  B := 8 * (n + 2)
  C := (((n + 1) / 2 : ℕ) : ℤ)
  A_pos := by positivity
  N_dvd := ⟨n + 4, by push_cast; ring⟩
  disc := by
    have h2 : (((n + 1) / 2 : ℕ) : ℤ) * 2 = n + 1 := by omega
    linear_combination (-64 * ((n : ℤ) + 4)) * h2
  D_neg := by
    have : (0 : ℤ) < n := by omega
    linarith
  primitive := by
    set g := Int.gcd (Int.gcd (32 * ((n : ℤ) + 4)) (8 * ((n : ℤ) + 2))) (((n + 1) / 2 : ℕ) : ℤ)
    have hB : (g : ℤ) ∣ 8 * ((n : ℤ) + 2) := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_right ..)
    have hC : (g : ℤ) ∣ (((n + 1) / 2 : ℕ) : ℤ) := Int.gcd_dvd_right ..
    have hCk : (((n + 1) / 2 : ℕ) : ℤ) = 4 * ((n / 8 : ℕ) : ℤ) + 3 := by omega
    have hnk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + 5 := by omega
    rw [hCk] at hC
    rw [hnk] at hB
    have h1 : (g : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = (4 * ((n / 8 : ℕ) : ℤ) + 3) * (4 * ((n / 8 : ℕ) : ℤ) + 3 +
          16 * (2 * ((n / 8 : ℕ) : ℤ) + 1) * ((n / 8 : ℕ) + 1)) -
          (2 * ((n / 8 : ℕ) : ℤ) + 1) * ((n / 8 : ℕ) + 1) * (8 * (8 * ((n / 8 : ℕ) : ℤ) + 5 + 2)) := by
        ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left hC _) (dvd_mul_of_dvd_right hB _)
    exact Nat.dvd_one.mp (by exact_mod_cast h1)

/-- `τ_{Q''} = (−(n+2) + √−n)/(8(n+4))`. -/
def tauW (n : ℕ) : QNeg n := ⟨-((n : ℚ) + 2) / (8 * (n + 4)), 1 / (8 * (n + 4))⟩
/-- The homothety factor `c = (−1 + ((n+3)/2)√−n)/(n+4)`. -/
def cW (n : ℕ) : QNeg n := ⟨-1 / ((n : ℚ) + 4), ((n : ℚ) + 3) / 2 / (n + 4)⟩

theorem tyzFormW_tau (n : ℕ) (hn : n % 8 = 5) : (tyzFormW n hn).tau = Shimura.kappa n (tauW n) := by
  have h4 : ((n : ℂ) + 4) ≠ 0 := by exact_mod_cast (show n + 4 ≠ 0 by omega)
  simp only [HeegnerForm.tau, cmPoint, tyzFormW, Shimura.kappa, tauW, Shimura.sqrt_64n]
  push_cast
  field_simp
  ring

theorem tauW_mul (n : ℕ) [NeZero n] : tauW n * (32 * Shimura.tauK n + 8) = -1 := by
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h4 : ((n : ℚ) + 4) ≠ 0 := by positivity
  ext <;> simp [tauW, Shimura.tauK, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    field_simp <;> ring

omit [NeZero n] in
@[simp] theorem tauW_re : (tauW n).re = -((n : ℚ) + 2) / (8 * (n + 4)) := rfl
omit [NeZero n] in
@[simp] theorem tauW_im : (tauW n).im = 1 / (8 * ((n : ℚ) + 4)) := rfl
omit [NeZero n] in
@[simp] theorem cW_re : (cW n).re = -1 / ((n : ℚ) + 4) := rfl
omit [NeZero n] in
@[simp] theorem cW_im : (cW n).im = ((n : ℚ) + 3) / 2 / (n + 4) := rfl
omit [NeZero n] in
@[simp] theorem tauK_re : (Shimura.tauK n).re = 1 / (4 * ((n : ℚ) + 1)) := rfl
omit [NeZero n] in
@[simp] theorem tauK_im : (Shimura.tauK n).im = 1 / (4 * ((n : ℚ) + 1)) := rfl

theorem latKW (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) * Submodule.span ℤ {1, tauW n} =
      Submodule.span ℤ {cW n * 1, cW n * Shimura.tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h4 : (8 * (k : ℚ) + 5 + 4) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Shimura.mem_span_pair_of 1 (-32 - 32 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 0 (3 + 4 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 8 32 (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of (-1) 0 (by ext <;> simp <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) 1 (tauW _) (by simp) (by simp) (by simp)
        (by simp) 0 0 0 (-1) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) 1 (tauW _) (by simp) (by simp) (by simp)
        (by simp) 0 (11 - 484 * k + 21296 * (k * k)) (-(1 - 44 * k + 1936 * (k * k) + 2662 * (k * k * k)))
        (8 * (-(1 - 44 * k + 1936 * (k * k) + 2662 * (k * k * k))))
        (by ext <;> simp <;> field_simp <;> ring)

theorem latNKW (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) * Submodule.span ℤ {Shimura.oneN n, tauW n} =
      Submodule.span ℤ {cW n * Shimura.oneN n, cW n * Shimura.tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h4 : (8 * (k : ℚ) + 5 + 4) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Shimura.mem_span_pair_of 1 (-1 - k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 0 (3 + 4 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 8 1 (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of (-32) 0 (by ext <;> simp <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) (Shimura.oneN _) (tauW _) (by simp) (by simp)
        (by simp) (by simp) 1 (3 * (k + 1)) (-4 * (k + 1) * (3 * k + 2)) (-(k + 1) * (3 * k + 2))
        (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) (Shimura.oneN _) (tauW _) (by simp) (by simp)
        (by simp) (by simp) 0 3 (-12 * k - 8) (-3 * k - 2)
        (by ext <;> simp <;> field_simp <;> ring)




theorem idealLat_varpi (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) = (Submodule.span ℤ {hW0 n, hW1 n}).map (Shimura.kappaLin n) := by
  rw [Shimura.idealLat, idealMeetOrder_varpi hn hsq,
    show Shimura.kappa n = Shimura.kappaLin n from funext fun x => (Shimura.kappaLin_apply n x).symm,
    Submodule.span_image, Submodule.span_eq]

theorem idealLat_varpi_mul (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) * (tyzFormW n hn).lat =
      (tyzForm n hn).lat.map (LinearMap.mulLeft ℤ (Shimura.kappa n (cW n))) := by
  rw [idealLat_varpi hn hsq, Shimura.lat_eq_map _ n _ (tyzFormW_tau n hn),
    Shimura.lat_eq_map _ n _ (Shimura.tyzForm_tau n hn), Shimura.map_mulLeft_span_pair,
    Shimura.kappaLin, ← Submodule.map_mul, latKW (n / 8) (by omega)]

theorem idealLat_varpi_mulN (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) * (tyzFormW n hn).latN =
      (tyzForm n hn).latN.map (LinearMap.mulLeft ℤ (Shimura.kappa n (cW n))) := by
  rw [idealLat_varpi hn hsq, Shimura.latN_eq_map _ n _ (tyzFormW_tau n hn),
    Shimura.latN_eq_map _ n _ (Shimura.tyzForm_tau n hn), Shimura.map_mulLeft_span_pair,
    Shimura.kappaLin, ← Submodule.map_mul, latNKW (n / 8) (by omega)]

/-- `τ_{Q''} = W(τ_Q + 1/4)`. -/
theorem tyzFormW_tauH (hn : n % 8 = 5) :
    ((tyzFormW n hn).tauH : ℂ) =
      ((Shimura.frickeH (quarterH (tyzForm n hn).tauH) : UpperHalfPlane) : ℂ) := by
  have hτ : ((tyzForm n hn).tauH : ℂ) = Shimura.kappaAlg n (Shimura.tauK n) := by
    rw [Shimura.kappaAlg_apply, ← Shimura.tyzForm_tau n hn]; rfl
  have hτ' : ((tyzFormW n hn).tauH : ℂ) = Shimura.kappaAlg n (tauW n) := by
    rw [Shimura.kappaAlg_apply, ← tyzFormW_tau n hn]; rfl
  have hrel := congrArg (Shimura.kappaAlg n) (tauW_mul n)
  simp only [map_mul, map_add, map_neg, map_one, map_ofNat] at hrel
  rw [← hτ, ← hτ'] at hrel
  set τ := ((tyzForm n hn).tauH : ℂ)
  have hne : (32 * (τ + 1 / 4)) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact (tyzForm n hn).tauH.im_pos.ne' this
  show _ = -1 / (32 * (τ + 1 / 4))
  rw [eq_div_iff hne]
  linear_combination hrel

/-- **`f₀(P_{Q''}) = T − [i]f₀(P_n)`** (given algebraicity of the Heegner point). -/
theorem heegnerPt_tyzFormW (hA : CMAlgebraic) (hn : n % 8 = 5) :
    heegnerPt (tyzFormW n hn) = ptT - iPt (heegnerPt (tyzForm n hn)) := by
  set Q := tyzForm n hn
  obtain ⟨P, hP⟩ := hA _ Q
  rw [heegnerPt_eq Q hP]
  apply heegnerPt_eq
  set τ₁ := quarterH Q.tauH
  set τ₂ := Shimura.frickeH τ₁
  have hτ₂ : (tyzFormW n hn).tauH = τ₂ := UpperHalfPlane.ext (tyzFormW_tauH hn)
  have e2 : X0.phiC τ₂ + X0.phiC τ₁ = X0.ptTC := Shimura.etaModelFricke τ₁ τ₂ rfl
  have h1 : toC (iPt P) = X0.phiC τ₁ := toC_iPt_of_quarter Q.tauH τ₁ rfl _ hP
  rw [hτ₂, map_sub, toC_ptT, h1, ← e2]
  abel

theorem acts4_inv {ρ : GalQ} {c : Pic (O4 n)} (hρ : ActsAsArtin4 ρ n c) :
    ActsAsArtin4 ρ⁻¹ n c⁻¹ := by
  intro x
  have e : artin4 n c (artin4 n c⁻¹ x) = x := by
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h := hρ (artin4 n c⁻¹ x)
  rw [e] at h
  calc ρ⁻¹ (embed n (x : SeparableClosure (QNeg n)))
      = ρ⁻¹ (ρ (embed n ((artin4 n c⁻¹ x : H4 n) : SeparableClosure (QNeg n)))) := by rw [h]
    _ = _ := ρ.symm_apply_apply _

set_option maxRecDepth 10000 in
/-- `ρ` acting on `H_{n,4}` as `c` (through `embed n`) acts as `c` through an embedding normalized by
`ιC(e(√−n)) = i√n`, either directly or after inverting `ρ`. -/
theorem normalized_cases {c : Pic (O4 n)} {ρ : GalQ} (hρ : ActsAsArtin4 ρ n c) :
    ∃ e : SeparableClosure (QNeg n) →ₐ[ℚ] Qbar,
      ιC (e (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt n : ℂ) ∧
      ((∀ x : ringClassField (conductorOrder (QNeg n) 4),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4) c x)) ∨
      (∀ x : ringClassField (conductorOrder (QNeg n) 4),
        ρ⁻¹ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4) c x))) := by
  set r := embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)
  have hr : r ^ 2 = -(n : Qbar) := by
    simp only [r, ← map_pow, Shimura.omega_sq', map_neg, map_natCast]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hC : ιC r ^ 2 = (I * (Real.sqrt n : ℂ)) ^ 2 := by
    rw [← map_pow, hr, mul_pow, I_sq, sq, Shimura.sqrt_mul_self_C]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hC with h | h
  · exact ⟨embed n, h, Or.inl hρ⟩
  · obtain ⟨γ, hγ⟩ := Shimura.exists_galQ_neg hn0 hr
    have hr0 : r ≠ 0 := by
      intro h0; rw [h0] at hr
      have : (n : Qbar) = 0 := by linear_combination hr
      exact NeZero.ne n (by exact_mod_cast this)
    have hγinv : γ⁻¹ r = -r := by
      apply γ.injective
      show γ (γ.symm r) = γ (-r)
      rw [AlgEquiv.apply_symm_apply, map_neg, hγ, neg_neg]
    have hne : γ⁻¹ r ≠ r := by
      rw [hγinv]; intro h'
      apply hr0
      have : (2 : Qbar) * r = 0 := by linear_combination -h'
      simpa using this
    have hconj := RingClassBridge.actsAsArtin4_conj (γ := γ⁻¹) hne (acts4_inv hρ)
    rw [inv_inv, inv_inv] at hconj
    refine ⟨γ.toAlgHom.comp (embed n), ?_, Or.inr fun x => ?_⟩
    · show ιC (γ r) = _
      rw [hγ, map_neg, h, neg_neg]
    · have h1 := hconj x
      simp only [AlgEquiv.mul_apply] at h1
      show ρ⁻¹ (γ (embed n (x : SeparableClosure (QNeg n)))) = γ (embed n _)
      rw [← h1]; exact (γ.apply_symm_apply _).symm

theorem galPt_one (P : PtA) : galPt 1 P = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e'⟩ := galPt_some 1 h
    rw [e']
    rfl

theorem galPt_tauG_one_one_of_neg {ρ : GalQ} (hρ : ρ iQ = -iQ) :
    galPt ρ (tauG ⟨1, 1⟩) = tauG ⟨1, -1⟩ := by
  rw [tauG_mk, tauG_mk, map_add, one_smul, one_smul, galPt_ptT, galPt_iPt_of_neg hρ, galPt_ptT,
    neg_one_zsmul]

/-- **`TYZThm36OneFive` from Shimura reciprocity, algebraicity and `WNegatesI`.** -/
theorem tyzThm36OneFive_of (hS : Shimura.ShimuraReciprocityPic) (hA : CMAlgebraic)
    (hneg : WNegatesI) : TYZThm36OneFive := by
  intro n hn0 hn hsq ρ hρ
  have hi := hneg n hn0 hn hsq ρ hρ
  have hD : -64 * (n : ℤ) = Shimura.discOf n 4 := by
    rw [Shimura.discOf, ite_eq_right (by omega)]; push_cast; ring
  rw [wClass_eq hn] at hρ
  obtain ⟨e, he, hcase⟩ := normalized_cases hρ
  have key : ∀ ρ' : GalQ, ρ' iQ = -iQ → (∀ x : ringClassField (conductorOrder (QNeg n) 4),
      ρ' (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4)
        ((O4 n).picClass ⟨_, varpiIdeal_mem hn⟩) x)) →
      galPt ρ' (tyzZn n) = tyzZn n + tauG ⟨1, 1⟩ := by
    intro ρ' hi' hρ'
    have hrec := hS n 4 hsq e he ⟨_, varpiIdeal_mem hn⟩ ρ' hρ' (-64 * n) hD (tyzForm n hn)
      (tyzFormW n hn) (Shimura.kappa n (cW n)) (idealLat_varpi_mul hn hsq)
      (idealLat_varpi_mulN hn hsq)
    rw [heegnerPt_tyzFormW hA hn] at hrec
    simp only [tyzZn, tyzHeegnerPt, hn, ↓reduceDIte]
    rw [map_sub, galPt_iPt_of_neg hi', hrec, sub_neg_eq_add, iPt_sub, iPt_iPt, tauG_mk, one_smul,
      one_smul]
    abel
  rcases hcase with h | h
  · exact ⟨0, by rw [key ρ hi h, zero_zsmul, add_zero]⟩
  · have hi' : ρ⁻¹ iQ = -iQ := by
      apply ρ.injective
      rw [show ρ (ρ⁻¹ iQ) = iQ from ρ.apply_symm_apply iQ, map_neg, hi, neg_neg]
    have h1 := key ρ⁻¹ hi' h
    have h2 : galPt ρ (galPt ρ⁻¹ (tyzZn n)) = tyzZn n := by
      rw [← galPt_mul, mul_inv_cancel, galPt_one]
    rw [h1, map_add, galPt_tauG_one_one_of_neg hi] at h2
    have h11 := tauG_one_one_add
    refine ⟨-1, ?_⟩
    rw [neg_one_zsmul, ← h11, eq_sub_of_add_eq h2]
    abel

end WAction

/-! ### Genus characters as Artin characters for odd `n` (port of cm-bridge §13 "GT-ART") -/

section ArtinChiOdd

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

/-- Away from `2n`: `𝔭` splits in the fixed field of `ker χ_q` iff it splits in `K_n(√q*)`. -/
theorem splitSet_kerChi_iff_odd (hodd : Odd n) (hsq : Squarefree n) (q : n.primeFactors)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal)
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal) :
    𝔭 ∈ splitSet (QNeg n) (maxSubfield (kerChi q)) ↔
      𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) (pstar q)) := by
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
theorem maxSubfield_kerChi_odd (hodd : Odd n) (hsq : Squarefree n) (q : n.primeFactors) :
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
    splitSet_kerChi_iff_odd hodd hsq q 𝔭 (fun h => hT (le_trans Ideal.mul_le_left h))
      (fun h => hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h)))
  apply le_antisymm
  · exact le_of_splitSet_diff_subset _ (finite_le_primes _ hI)
      fun 𝔭 ⟨h𝔭, hT⟩ => (key 𝔭 hT).2 h𝔭
  · exact le_of_splitSet_diff_subset _ (finite_le_primes _ hI)
      fun 𝔭 ⟨h𝔭, hT⟩ => (key 𝔭 hT).1 h𝔭

/-- **Genus characters as Artin characters, any odd squarefree `n`** (cm-bridge's `artinPstarChi`
with `n ≡ 3 (mod 4)` replaced by `n` odd; same proof). -/
theorem artinPstarChi_odd (hodd : Odd n) (hsq : Squarefree n) (q : n.primeFactors) (c : Pic (OK n))
    (hs : sqrtK (QNeg n) (pstar q) ∈ hilbertField n) :
    ((ringClassArtinEquiv (OK n) c ⟨_, hs⟩ : hilbertField n) : SeparableClosure (QNeg n)) =
      (if chi n q c = 1 then 1 else -1) * sqrtK (QNeg n) (pstar q) := by
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
    rw [maxSubfield_kerChi_odd hodd hsq q]; exact IntermediateField.mem_adjoin_simple_self _ _
  have hfix_iff : g s' = s' ↔ chi n q c = 1 := by
    constructor
    · intro hfix
      have hle : adjSqrt (QNeg n) (pstar q) ≤
          IntermediateField.lift (IntermediateField.fixedField (Subgroup.zpowers g)) := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact mem_lift_fixedField_zpowers g s' hfix
      rw [← maxSubfield_kerChi_odd hodd hsq q] at hle
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

end ArtinChiOdd

/-! ### Genus theory for class 5: `WNegatesI` and `BetaOnGenus5`

`w = [𝔞]`, `𝔞𝔭₂ = (√−n − 1)`, `𝔭₂² = (2)` (`a_mul_p2`, `p2_sq`), so `χ_q(w) = χ_q([𝔭₂]) = (2/q)`
(`chi_wClass`). By the port of cm-bridge's GT-ART (`artinPstarChi_odd`) the Artin symbol of `c`
acts on `√q*` by `χ_q(c)`; `√−1 = ±√−n / Π_q √q*` gives `σ_w(i) = Π_q (2/q) i = (2/n) i = −i`, and
`σγ⁻¹` acts on `√q*` by `(−2, q*)_2 = (2/q)`, so `χ_q(σγ⁻¹) = χ_q(w)` for all `q` and
`[σγ⁻¹]w⁻¹ ∈ Cl² = ⋂_q ker χ_q` (`picSquares_eq_iInf_ker_chi`, Gauss). -/

section Genus5

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

/-- The ramified prime `𝔭₂ = (2, √−n − 1)` of `𝓞_{K_n}` (`n ≡ 1 (mod 4)`). -/
def p2Ideal5 (n : ℕ) [NeZero n] : Ideal (𝓞 (QNeg n)) := Ideal.span {2, sqrtNeg n - 1}

theorem varpi_sq_add (n : ℕ) [NeZero n] :
    (sqrtNeg n - 1) * (sqrtNeg n - 1) + 2 * (sqrtNeg n - 1) = -((n : 𝓞 (QNeg n)) + 1) := by
  linear_combination sqrtNeg_mul_self (d := n)

theorem p2_sq (hn : n % 8 = 5) : p2Ideal5 n * p2Ideal5 n = Ideal.span {2} := by
  rw [p2Ideal5, Ideal.span_pair_mul_span_pair]
  have hv := varpi_sq_add n
  have hk : (n : 𝓞 (QNeg n)) + 1 = 8 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 6 := by
    have : n + 1 = 8 * (n / 8) + 6 := by omega
    exact_mod_cast this
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨2, by ring⟩
    · exact ⟨sqrtNeg n - 1, rfl⟩
    · exact ⟨sqrtNeg n - 1, by ring⟩
    · exact ⟨-(4 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 3) - (sqrtNeg n - 1), by linear_combination hv - hk⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set S : Set (𝓞 (QNeg n)) := {2 * 2, 2 * (sqrtNeg n - 1), (sqrtNeg n - 1) * 2,
      (sqrtNeg n - 1) * (sqrtNeg n - 1)} with hS
    have e : (2 : 𝓞 (QNeg n)) = (-1) * ((sqrtNeg n - 1) * (sqrtNeg n - 1)) +
        (-1) * (2 * (sqrtNeg n - 1)) + (-(2 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 1)) * (2 * 2) := by
      linear_combination hv - hk
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_))
      (Ideal.mul_mem_left _ _ ?_)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)

theorem absNorm_p2 (hn : n % 8 = 5) : Ideal.absNorm (p2Ideal5 n) = 2 := by
  have h := congrArg Ideal.absNorm (p2_sq hn)
  rw [map_mul, Ideal.absNorm_span_singleton] at h
  have h2 : (Algebra.norm ℤ (2 : 𝓞 (QNeg n))).natAbs = 4 := by
    have := normZ_natCast (n := n) 2
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num
  rw [h2] at h
  have : Ideal.absNorm (p2Ideal5 n) * Ideal.absNorm (p2Ideal5 n) = 2 * 2 := h
  nlinarith [Nat.zero_le (Ideal.absNorm (p2Ideal5 n))]

theorem a_mul_p2 (hn : n % 8 = 5) : varpiIdeal n * p2Ideal5 n = Ideal.span {sqrtNeg n - 1} := by
  rw [varpiIdeal, p2Ideal5, Ideal.span_pair_mul_span_pair]
  have hv := varpi_sq_add n
  have hm : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * 2 = (n : 𝓞 (QNeg n)) + 1 := by
    have : (n + 1) / 2 * 2 = n + 1 := by omega
    exact_mod_cast this
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨-(sqrtNeg n - 1) - 2, by linear_combination -hv - hm⟩
    · exact ⟨(((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)), by ring⟩
    · exact ⟨2, by ring⟩
    · exact ⟨sqrtNeg n - 1, rfl⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set S : Set (𝓞 (QNeg n)) := {(((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * 2,
      (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1), (sqrtNeg n - 1) * 2,
      (sqrtNeg n - 1) * (sqrtNeg n - 1)} with hS
    have e : sqrtNeg n - 1 = 1 * ((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1)) -
        (((n + 1) / 4 : ℕ) : 𝓞 (QNeg n)) * ((sqrtNeg n - 1) * 2) := by
      have : (n + 1) / 2 = 2 * ((n + 1) / 4) + 1 := by omega
      have h' : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) = 2 * (((n + 1) / 4 : ℕ) : 𝓞 (QNeg n)) + 1 := by
        exact_mod_cast this
      rw [h']; ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)


omit [NeZero n] in
theorem odd_of_mem_primeFactors (hodd : Odd n) {q : ℕ} (hq : q ∈ n.primeFactors) : q % 2 = 1 := by
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  rcases hqp.eq_two_or_odd with h | h
  · subst h; exact absurd (even_iff_two_dvd.2 hqd) (Nat.not_even_iff_odd.2 hodd)
  · exact h

omit [NeZero n] in
/-- `Π_{q ∣ n} (2/q) = (2/n) = −1` for squarefree `n ≡ 5 (mod 8)`. -/
theorem prod_sign_two (hn : n % 8 = 5) (hsq : Squarefree n) :
    ∏ q ∈ n.primeFactors, (if q % 8 = 1 ∨ q % 8 = 7 then (1 : ℤ) else -1) = -1 := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h1 : ∀ q ∈ n.primeFactors, (if q % 8 = 1 ∨ q % 8 = 7 then (1 : ℤ) else -1) =
      ZMod.χ₈ (q : ZMod 8) := by
    intro q hq
    have hq2 := odd_of_mem_primeFactors hodd hq
    rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (show ¬ (q % 2 = 0) by omega)]
  rw [Finset.prod_congr rfl h1, ← map_prod, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq,
    ZMod.χ₈_nat_eq_if_mod_eight, if_neg (show ¬ (n % 2 = 0) by omega),
    if_neg (show ¬ (n % 8 = 1 ∨ n % 8 = 7) by omega)]

omit [NeZero n] in
/-- `Π_{q ∣ n} q* = n` for squarefree `n ≡ 1 (mod 4)`. -/
theorem prod_pstar (hn : n % 4 = 1) (hsq : Squarefree n) :
    ∏ q ∈ n.primeFactors, pstar q = n := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h1 : ∀ q ∈ n.primeFactors, pstar q = ZMod.χ₄ (q : ZMod 4) * (q : ℤ) := by
    intro q hq
    have hq2 := odd_of_mem_primeFactors hodd hq
    rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg (show ¬ (q % 2 = 0) by omega)]
    unfold pstar
    split_ifs <;> ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ← map_prod, ← Nat.cast_prod, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hsq, ZMod.χ₄_nat_eq_if_mod_four,
    if_neg (show ¬ (n % 2 = 0) by omega), if_pos hn, one_mul]

theorem picToMax_picClass {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (J : integralIdealsPrimeTo O.conductorModulus) (hJ : (J : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) :
    picToMax O (O.picClass J) = (ClassGroup.mk0 ⟨(J : Ideal (𝓞 K)), hJ⟩ : ClassGroup (𝓞 K)) := by
  obtain ⟨t, ht⟩ := rayClassQuotient_surjective O.conductorModulus
    (idealClass O.conductorModulus J)
  have hQ : ringClassIdeleQuotient O t = O.picClass J := by
    rw [ringClassIdeleQuotient_apply, ht, rayClassToPic_idealClass]
  rw [← hQ, picToMax_ringClassIdeleQuotient, ringClassIdeleQuotient_apply,
    ← classMap_rayClassQuotient (maximal_conductorModulus_dvd O), ht, classMap_idealClass,
    rayClassToPic_idealClass]
  have hJ' : ((integralIdealsPrimeToInclusion (maximal_conductorModulus_dvd O) J :
      integralIdealsPrimeTo (maximalNumberFieldOrder K).conductorModulus) : Ideal (𝓞 K)) ∈
      (Ideal (𝓞 K))⁰ := by
    rw [coe_integralIdealsPrimeToInclusion]; exact hJ
  rw [picClass_maximal _ hJ']
  congr 2

theorem span_two_ne_zero (x : 𝓞 (QNeg n)) : Ideal.span {2, x} ≠ 0 := by
  intro h0
  have h2 : (2 : 𝓞 (QNeg n)) ∈ Ideal.span {2, x} := Ideal.subset_span (by simp)
  rw [h0, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  exact two_ne_zero h2

theorem chi_wClass (hn : n % 8 = 5) (hsq : Squarefree n) (q : n.primeFactors) :
    chi n q (picToMax (O4 n) (wClass n)) = Multiplicative.ofAdd (ZInQ.RouteK.legBit q 2) := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hq2 : (q : ℕ) % 2 = 1 := odd_of_mem_primeFactors hodd q.2
  have ha0 : varpiIdeal n ∈ (Ideal (𝓞 (QNeg n)))⁰ := mem_nonZeroDivisors_of_ne_zero (by
    rw [Ideal.zero_eq_bot]
    exact ((mem_integralIdealsPrimeTo_conductorModulus_iff (O4 n)).1 (varpiIdeal_mem hn)).1)
  have hp0 : p2Ideal5 n ∈ (Ideal (𝓞 (QNeg n)))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (span_two_ne_zero _)
  rw [wClass_eq hn, picToMax_picClass (O4 n) ⟨_, varpiIdeal_mem hn⟩ ha0]
  have hprod : ClassGroup.mk0 (⟨varpiIdeal n, ha0⟩ : (Ideal (𝓞 (QNeg n)))⁰) *
      ClassGroup.mk0 (⟨p2Ideal5 n, hp0⟩ : (Ideal (𝓞 (QNeg n)))⁰) = 1 := by
    rw [← map_mul]
    have h2 : (⟨varpiIdeal n, ha0⟩ : (Ideal (𝓞 (QNeg n)))⁰) * ⟨p2Ideal5 n, hp0⟩ =
        ⟨Ideal.span {sqrtNeg n - 1}, by rw [← a_mul_p2 hn]; exact Submonoid.mul_mem _ ha0 hp0⟩ :=
      Subtype.ext (a_mul_p2 hn)
    rw [h2, ClassGroup.mk0_eq_one_iff]
    exact ⟨⟨sqrtNeg n - 1, rfl⟩⟩
  have hq : ¬ (q : ℕ) ∣ Ideal.absNorm (p2Ideal5 n) := by
    rw [absNorm_p2 hn]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    have hqp := Nat.prime_of_mem_primeFactors q.2
    have := hqp.two_le
    omega
  have h3 := congrArg (chi n q) hprod
  rw [map_mul, map_one, chi_mk0 n hodd hsq q ⟨p2Ideal5 n, hp0⟩ hq, ← eq_inv_iff_mul_eq_one] at h3
  rw [h3, ← ofAdd_neg, ZMod.neg_eq_self_mod_two, absNorm_p2 hn, Nat.cast_ofNat]

theorem chi_wClass_eq_one_iff (hn : n % 8 = 5) (hsq : Squarefree n) (q : n.primeFactors) :
    chi n q (picToMax (O4 n) (wClass n)) = 1 ↔ (q : ℕ) % 8 = 1 ∨ (q : ℕ) % 8 = 7 := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hq2 : (q : ℕ) % 2 = 1 := odd_of_mem_primeFactors hodd q.2
  have hqp := Nat.prime_of_mem_primeFactors q.2
  haveI := Fact.mk hqp
  rw [chi_wClass hn hsq q, ← ZMod.exists_sq_eq_two_iff (by omega)]
  unfold ZInQ.RouteK.legBit
  rw [show (((2 : ℤ)) : ZMod q) = 2 by norm_num]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; decide

theorem sqrt_pstar_mem (hn4 : n % 4 = 1) (hsq : Squarefree n) (q : n.primeFactors) :
    sqrtK (QNeg n) (pstar q) ∈ hilbertField n := by
  have hi := adjSqrt_le_hilbertField hn4 hsq (-1) (Or.inl rfl)
    (IntermediateField.mem_adjoin_simple_self _ _)
  have hp := adjSqrt_le_hilbertField hn4 hsq (q : ℕ)
    (Or.inr ⟨q, Nat.prime_of_mem_primeFactors q.2, Nat.dvd_of_mem_primeFactors q.2, rfl⟩)
    (IntermediateField.mem_adjoin_simple_self _ _)
  unfold pstar
  split_ifs with h
  · exact hp
  · have e : (sqrtK (QNeg n) (-((q : ℕ) : ℤ))) ^ 2 =
        (sqrtK (QNeg n) (-1) * sqrtK (QNeg n) ((q : ℕ) : ℤ)) ^ 2 := by
      rw [mul_pow, sqrtK_sq, sqrtK_sq, sqrtK_sq]; push_cast; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with h' | h'
    · rw [h']; exact mul_mem hi hp
    · rw [h']; exact neg_mem (mul_mem hi hp)

theorem acts_sqrt_pstar (hn4 : n % 4 = 1) (hsq : Squarefree n) {ρ : GalQ} {c : Pic (OK n)}
    (hρ : ActsAsArtinO n (OK n) ρ c) (q : n.primeFactors) :
    ρ (embed n (sqrtK (QNeg n) (pstar q))) =
      (if chi n q c = 1 then 1 else -1) * embed n (sqrtK (QNeg n) (pstar q)) := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hs := sqrt_pstar_mem hn4 hsq q
  have h1 := hρ ⟨_, hs⟩
  rw [h1, artinPstarChi_odd hodd hsq q c hs, map_mul]
  split_ifs <;> simp

/-- **Glue W-I proved**: `σ_w(i) = −i`. -/
theorem wNegatesI : WNegatesI := by
  intro n _ hn hsq ρ hρ
  have hn4 : n % 4 = 1 := by omega
  have hO := actsO_of_acts4 hρ
  set f : ℕ → Qbar := fun q => embed n (sqrtK (QNeg n) (pstar q)) with hf
  set s := ∏ q ∈ n.primeFactors, f q with hsdef
  have hsign : ∀ q ∈ n.primeFactors,
      ρ (f q) = (((if q % 8 = 1 ∨ q % 8 = 7 then (1 : ℤ) else -1 : ℤ)) : Qbar) * f q := by
    intro q hq
    have h1 := acts_sqrt_pstar hn4 hsq hO ⟨q, hq⟩
    simp only [hf]
    rw [h1]
    congr 1
    by_cases hc : q % 8 = 1 ∨ q % 8 = 7
    · rw [if_pos ((chi_wClass_eq_one_iff hn hsq ⟨q, hq⟩).2 hc), if_pos hc]; simp
    · rw [if_neg (fun h => hc ((chi_wClass_eq_one_iff hn hsq ⟨q, hq⟩).1 h)), if_neg hc]; simp
  have hρs : ρ s = -s := by
    rw [hsdef, map_prod, Finset.prod_congr rfl hsign, Finset.prod_mul_distrib, ← Int.cast_prod,
      prod_sign_two hn hsq]
    simp
  have hs2 : s ^ 2 = (n : Qbar) := by
    rw [hsdef, ← Finset.prod_pow]
    rw [Finset.prod_congr rfl (fun q _ => show f q ^ 2 = ((pstar q : ℤ) : Qbar) by
      simp only [hf]; rw [← map_pow, sqrtK_sq, map_intCast])]
    rw [← Int.cast_prod, prod_pstar hn4 hsq]
    simp
  have hω : ρ (omegaBar n) = omegaBar n := by
    have h1 := hρ ⟨algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega,
      (H4 n).algebraMap_mem _⟩
    simp only [omegaBar]
    rw [h1]
    congr 1
    exact congrArg Subtype.val ((artin4 n (wClass n)).commutes QuadraticAlgebra.omega)
  have hiQs : (iQ * s) ^ 2 = (omegaBar n) ^ 2 := by
    rw [mul_pow, iQ_sq, hs2, omegaBar_sq]; ring
  have hfix : ρ (iQ * s) = iQ * s := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hiQs with h | h
    · rw [h, hω]
    · rw [h, map_neg, hω]
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs2
    have : (n : Qbar) = 0 := by rw [← hs2]; ring
    exact NeZero.ne n (by exact_mod_cast this)
  rw [map_mul, hρs] at hfix
  have h' : (ρ iQ + iQ) * s = 0 := by linear_combination -hfix
  rcases mul_eq_zero.1 h' with h | h
  · linear_combination h
  · exact absurd h hs0

theorem mult_zmod2_eq_of_iff : ∀ x y : Multiplicative (ZMod 2), (x = 1 ↔ y = 1) → x = y := by
  decide

/-- **Glue BETA-5 proved**: `[σγ⁻¹] ≡ w` modulo `Cl(K_n)²`. -/
theorem betaOnGenus5 : BetaOnGenus5 := by
  intro n _ hn hsq σ γ hσ hγ a ha
  have hn4 : n % 4 = 1 := by omega
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hO := actsO_of_acts4 ha
  rw [picSquares_eq_iInf_ker_chi n hodd hsq (by omega)]
  refine Subgroup.mem_iInf.2 fun q => ?_
  let φ : Pic (O4 n) →* Multiplicative (ZMod 2) := (chi n q).comp (picToMax (O4 n))
  show φ (a * (wClass n)⁻¹) = 1
  rw [map_mul, map_inv]
  suffices h : φ a = φ (wClass n) by rw [h, mul_inv_cancel]
  show chi n q (picToMax (O4 n) a) = chi n q (picToMax (O4 n) (wClass n))
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have hq2 : (q : ℕ) % 2 = 1 := odd_of_mem_primeFactors hodd q.2
  set r := embed n (sqrtK (QNeg n) (pstar q)) with hr
  have hr2 : r ^ 2 = ((pstar q : ℤ) : Qbar) := by rw [hr, ← map_pow, sqrtK_sq, map_intCast]
  have hD : pstar q ≠ 0 := by
    unfold pstar; split_ifs <;> simp [hqp.ne_zero]
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0] at hr2
    have : ((pstar q : ℤ) : Qbar) = 0 := by rw [← hr2]; ring
    exact hD (by exact_mod_cast this)
  have h1 := acts_sqrt_pstar hn4 hsq hO q
  have h2 : (σ * γ⁻¹) r = (if (q : ℕ) % 8 = 1 ∨ (q : ℕ) % 8 = 7 then 1 else -1) * r := by
    rw [AlgEquiv.mul_apply, hγ.inv_apply, hγ.apply_sqrt hD hr2, map_mul,
      hσ _ (squarefree_pstar hqp) r hr2, betaOneSign_pstar hqp (by omega)]
    push_cast
    split_ifs <;> simp [map_neg, map_one]
  rw [← hr] at h1
  have hne : (1 : Qbar) * r ≠ -1 * r := by
    intro h; apply hr0; linear_combination h / 2
  have hcmp : chi n q (picToMax (O4 n) a) = 1 ↔ ((q : ℕ) % 8 = 1 ∨ (q : ℕ) % 8 = 7) := by
    constructor
    · intro hc
      by_contra hc'
      rw [h1, if_pos hc, if_neg hc'] at h2
      exact hne h2
    · intro hc
      by_contra hc'
      rw [h1, if_neg hc', if_pos hc] at h2
      exact hne h2.symm
  exact mult_zmod2_eq_of_iff _ _ (hcmp.trans (chi_wClass_eq_one_iff hn hsq q).symm)

end Genus5

/-! ### `KerFixesZnMod`: the kernel of `Pic(O_{n,4}) → Cl(K_n)` is `{1, σ, w², σw²}`

A class in the kernel is `[(x) ∩ O]` with `x = u + v√−n ∈ 𝓞_K`, `u + v` odd (`odd_of_mem`: otherwise
`(x) + 𝔣 ⊆ 𝔭₂`). If `x ≡ a·y (mod 4𝓞_K)` with `a ∈ ℤ` then `[(x)] = [(y)]` (`picClass_congr`: `xȳ ∈ ℤ + 4𝓞_K`).
So the class is that of `1`, `1 + 2√−n` (`= σ`), `2 + √−n` (`= w²`, via `𝔞² = ((ω−1)²/2)`) or
`√−n ≡ (1+2√−n)(2+√−n)` (`= σw²`) (`ker_cases`). Then `σ` fixes `z_n` (tyz-cm) and `w²` moves it by
`τ((1+i)/2) + τ((1−i)/2) = τ(1)`. -/

section KerSec

open ZInQ.RouteK.Redei
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

/-! ### The kernel of `Pic(O_{n,4}) → Cl(K_n)` -/

section Ker

open QuadraticAlgebra

/-- `u + v√−n ∈ 𝓞_K`. -/
abbrev elt (n : ℕ) [NeZero n] (u v : ℤ) : 𝓞 (QNeg n) := (u : 𝓞 (QNeg n)) + (v : 𝓞 (QNeg n)) * sqrtNeg n

theorem coe_elt (u v : ℤ) : ((elt n u v : 𝓞 (QNeg n)) : QNeg n) = ⟨u, v⟩ := by
  simp only [elt]; push_cast [coe_sqrtNeg]; ext <;> simp

theorem eq_elt (hn4 : n % 4 = 1) (hsq : Squarefree n) (y : 𝓞 (QNeg n)) :
    ∃ u v : ℤ, y = elt n u v := by
  obtain ⟨u, v, hu, hv⟩ := Shimura.int_coords hn4 hsq y
  refine ⟨u, v, RingOfIntegers.ext ?_⟩
  rw [coe_elt]; ext <;> simp [hu, hv]

theorem elt_mul_conj (u v : ℤ) : elt n u v * elt n u (-v) = ((u ^ 2 + n * v ^ 2 : ℤ) : 𝓞 (QNeg n)) := by
  simp only [elt]; push_cast
  linear_combination (-(v : 𝓞 (QNeg n)) ^ 2) * sqrtNeg_mul_self (d := n)

theorem mem_O4_elt (a : ℤ) (z : 𝓞 (QNeg n)) : (a : 𝓞 (QNeg n)) + 4 * z ∈ (O4 n).toRingOfIntegers := by
  rw [NumberFieldOrder.mem_toRingOfIntegers, Shimura.mem_O4_iff']
  refine ⟨a, z, ?_⟩
  simp only [map_add, map_mul, map_intCast, map_ofNat]

theorem odd_norm {n : ℕ} (hn : n % 2 = 1) {u v : ℤ} (huv : (u + v) % 2 = 1) :
    ∃ M : ℤ, u ^ 2 + n * v ^ 2 = 2 * M + 1 := by
  rcases Int.emod_two_eq_zero_or_one u with hu | hu
  · obtain ⟨a, rfl⟩ : ∃ a, u = 2 * a := ⟨u / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = 2 * b + 1 := ⟨v / 2, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, (n : ℤ) = 2 * c + 1 := ⟨n / 2, by omega⟩
    exact ⟨2 * a ^ 2 + (2 * c + 1) * (2 * b ^ 2 + 2 * b) + c, by rw [hc]; ring⟩
  · obtain ⟨a, rfl⟩ : ∃ a, u = 2 * a + 1 := ⟨u / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = 2 * b := ⟨v / 2, by omega⟩
    exact ⟨2 * a ^ 2 + 2 * a + 2 * n * b ^ 2, by ring⟩

/-- `(u + v√−n)` with `u + v` odd is prime to the conductor of `O_{n,4}`. -/
theorem span_elt_mem (hn : n % 8 = 5) {u v : ℤ} (huv : (u + v) % 2 = 1) :
    Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  obtain ⟨M, hM⟩ := odd_norm (n := n) (by omega) huv
  have hN := elt_mul_conj (n := n) u v
  refine ⟨?_, ?_⟩
  · intro h
    have hx : elt n u v ∈ Ideal.span {elt n u v} := Ideal.subset_span rfl
    rw [h, Ideal.mem_bot] at hx
    rw [hx, zero_mul, hM] at hN
    have h1 : (((2 * M + 1 : ℤ)) : 𝓞 (QNeg n)) = ((0 : ℤ) : 𝓞 (QNeg n)) := by
      rw [← hN]; simp
    have := intCast_injective (n := n) h1
    omega
  · rw [Ideal.eq_top_iff_one]
    -- 1 = x * (x̄ * (2M+1)) - 4 * (M * (M + 1))
    have e : (1 : 𝓞 (QNeg n)) = elt n u v * (elt n u (-v) * ((2 * M + 1 : ℤ) : 𝓞 (QNeg n))) +
        4 * ((-(M * (M + 1)) : ℤ) : 𝓞 (QNeg n)) := by
      rw [← mul_assoc, hN, hM]; push_cast; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
      (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg n) 4 (((-(M * (M + 1)) : ℤ)) : 𝓞 (QNeg n))

/-- **Congruence lemma**: if `x ≡ a·y (mod 4𝓞_K)`, `a ∈ ℤ`, then `[x ∩ O] = [y ∩ O]` in `Pic(O_{n,4})`. -/
theorem picClass_congr (hn : n % 8 = 5) {u v u' v' : ℤ} (huv : (u + v) % 2 = 1)
    (huv' : (u' + v') % 2 = 1) (a : ℤ) (z : 𝓞 (QNeg n))
    (h : elt n u v = a * elt n u' v' + 4 * z) :
    (O4 n).picClass ⟨_, span_elt_mem hn huv⟩ = (O4 n).picClass ⟨_, span_elt_mem hn huv'⟩ := by
  have huv'' : (u' + -v') % 2 = 1 := by omega
  have hb := span_elt_mem hn huv''
  have hN := elt_mul_conj (n := n) u' v'
  -- `[x][ȳ] = 1` and `[y][ȳ] = 1`
  have hprod : ∀ {x : 𝓞 (QNeg n)} (hx : Ideal.span {x} ∈ integralIdealsPrimeTo (O4 n).conductorModulus)
      (hxy : x * elt n u' (-v') ∈ (O4 n).toRingOfIntegers),
      (O4 n).picClass ⟨_, hx⟩ * (O4 n).picClass ⟨_, hb⟩ = 1 := by
    intro x hx hxy
    rw [← map_mul]
    have hm : (⟨_, hx⟩ : integralIdealsPrimeTo (O4 n).conductorModulus) * ⟨_, hb⟩ =
        ⟨Ideal.span {x * elt n u' (-v')}, by
          rw [← Ideal.span_singleton_mul_span_singleton]; exact Submonoid.mul_mem _ hx hb⟩ :=
      Subtype.ext (Ideal.span_singleton_mul_span_singleton _ _)
    rw [hm, picClass_eq_one_iff]
    exact ⟨_, hxy, rfl⟩
  have h1 := hprod (span_elt_mem hn huv) (by
    rw [h, add_mul, mul_assoc, hN, ← Int.cast_mul, mul_assoc]
    exact mem_O4_elt _ _)
  have h2 := hprod (span_elt_mem hn huv') (by
    rw [hN]
    have := mem_O4_elt (n := n) (u' ^ 2 + n * v' ^ 2) 0
    rwa [mul_zero, add_zero] at this)
  exact mul_right_cancel (h1.trans h2.symm)

end Ker

section Ker2
open QuadraticAlgebra

theorem elt_mem_p2 {u v : ℤ} (huv : (u + v) % 2 = 0) : elt n u v ∈ p2Ideal5 n := by
  obtain ⟨t, ht⟩ : ∃ t, u + v = 2 * t := ⟨(u + v) / 2, by omega⟩
  have e : elt n u v = (t : 𝓞 (QNeg n)) * 2 + (v : 𝓞 (QNeg n)) * (sqrtNeg n - 1) := by
    simp only [elt]
    have : (u : 𝓞 (QNeg n)) = 2 * t - v := by
      have h' : ((u : ℤ) : 𝓞 (QNeg n)) = ((2 * t - v : ℤ) : 𝓞 (QNeg n)) := by rw [← ht]; ring_nf
      push_cast at h'; exact h'
    rw [this]; ring
  rw [e, p2Ideal5]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

theorem conductor_le_p2 (hn : n % 8 = 5) (hsq : Squarefree n) : (O4 n).conductor ≤ p2Ideal5 n := by
  have hn4 : n % 4 = 1 := by omega
  intro c hc
  rw [NumberFieldOrder.mem_conductor_iff] at hc
  have h1 := hc 1
  have h2 := hc (sqrtNeg n)
  rw [Shimura.mem_O4_iff'] at h1 h2
  obtain ⟨a, y, hy⟩ := h1
  obtain ⟨a', y', hy'⟩ := h2
  obtain ⟨y1, y2, hy1, hy2⟩ := Shimura.int_coords hn4 hsq y
  obtain ⟨y1', y2', hy1', hy2'⟩ := Shimura.int_coords hn4 hsq y'
  rw [show ((1 : 𝓞 (QNeg n)) : QNeg n) = 1 from rfl, mul_one] at hy
  rw [hy, coe_sqrtNeg] at hy'
  have him := congrArg QuadraticAlgebra.im hy'
  simp [hy1, hy2, hy1', hy2'] at him
  have ha : (a : ℚ) = 4 * (y2' - y1) := by linarith
  have ha' : a = 4 * (y2' - y1) := by exact_mod_cast ha
  have e : c = 2 * (2 * (((y2' - y1 : ℤ) : 𝓞 (QNeg n)) + y)) := by
    apply RingOfIntegers.ext
    have hcI : ∀ m : ℤ, ((m : 𝓞 (QNeg n)) : QNeg n) = m := fun m =>
      map_intCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) m
    rw [hy, ha']; push_cast [Shimura.coeO_two, hcI]; ring
  rw [e, p2Ideal5]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem p2_ne_top (hn : n % 8 = 5) : p2Ideal5 n ≠ ⊤ := by
  intro h
  have := absNorm_p2 (n := n) hn
  rw [h, Ideal.absNorm_top] at this
  omega

/-- A principal ideal `(u + v√−n)` prime to the conductor has `u + v` odd. -/
theorem odd_of_mem (hn : n % 8 = 5) (hsq : Squarefree n) {u v : ℤ}
    (h : Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus) :
    (u + v) % 2 = 1 := by
  by_contra hc
  have hc' : (u + v) % 2 = 0 := by omega
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff] at h
  apply p2_ne_top hn
  rw [eq_top_iff, ← h.2]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 (elt_mem_p2 hc')) (conductor_le_p2 hn hsq)

end Ker2

section Ker3
open QuadraticAlgebra

theorem elt_lin (a u' v' s t : ℤ) :
    (a : 𝓞 (QNeg n)) * elt n u' v' + 4 * elt n s t = elt n (a * u' + 4 * s) (a * v' + 4 * t) := by
  simp only [elt]; push_cast; ring

theorem elt_mul (u v u' v' : ℤ) :
    elt n u v * elt n u' v' = elt n (u * u' - n * v * v') (u * v' + v * u') := by
  simp only [elt]; push_cast
  linear_combination ((v : 𝓞 (QNeg n)) * v') * sqrtNeg_mul_self (d := n)

theorem pic_one (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 1) (v := 0) (by decide)⟩ = 1 := by
  rw [picClass_eq_one_iff]
  refine ⟨elt n 1 0, ?_, rfl⟩
  simpa [elt] using mem_O4_elt (n := n) 1 0

theorem pic_sigma (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 1) (v := 2) (by decide)⟩ = sigmaClass n := by
  rw [sigmaClass_eq]
  have e : alpha n = elt n 3 2 := by simp only [alpha, elt]; push_cast; ring
  have h1 : (O4 n).picClass ⟨_, alphaIdeal_mem⟩ =
      (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 3) (v := 2) (by decide)⟩ := by
    congr 1 <;> simp [e]
  rw [h1]
  exact (picClass_congr hn (u := 3) (v := 2) (u' := 1) (v' := 2) (by decide) (by decide) (-1)
    (elt n 1 1) (by rw [elt_lin]; norm_num)).symm

theorem varpi_sq (k : ℕ) (hk : n = 8 * k + 5) :
    (sqrtNeg n - 1) * (sqrtNeg n - 1) = 2 * elt n (-4 * k - 2) (-1) := by
  have hk' : (n : 𝓞 (QNeg n)) = 8 * (k : 𝓞 (QNeg n)) + 5 := by
    have := congrArg (Nat.cast (R := 𝓞 (QNeg n))) hk
    push_cast at this; exact this
  simp only [elt]; push_cast
  linear_combination sqrtNeg_mul_self (d := n) - hk'

theorem a_sq (hn : n % 8 = 5) (k : ℕ) (hk : n = 8 * k + 5) :
    varpiIdeal n * varpiIdeal n = Ideal.span {elt n (-4 * k - 2) (-1)} := by
  have h2 : (Ideal.span {(2 : 𝓞 (QNeg n))}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact two_ne_zero
  apply mul_right_cancel₀ h2
  rw [← p2_sq hn]
  calc varpiIdeal n * varpiIdeal n * (p2Ideal5 n * p2Ideal5 n)
      = (varpiIdeal n * p2Ideal5 n) * (varpiIdeal n * p2Ideal5 n) := by ring
    _ = Ideal.span {(sqrtNeg n - 1) * (sqrtNeg n - 1)} := by
        rw [a_mul_p2 hn, Ideal.span_singleton_mul_span_singleton]
    _ = _ := by
        rw [varpi_sq k hk, ← Ideal.span_singleton_mul_span_singleton, mul_comm, p2_sq hn]

theorem pic_w2 (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 2) (v := 1) (by decide)⟩ = wClass n ^ 2 := by
  have hb : ((-4 * ((n / 8 : ℕ) : ℤ) - 2) + -1) % 2 = 1 := by omega
  have hk : n = 8 * (n / 8) + 5 := by omega
  rw [wClass_eq hn, ← map_pow]
  have h1 : (⟨_, varpiIdeal_mem hn⟩ : integralIdealsPrimeTo (O4 n).conductorModulus) ^ 2 =
      ⟨_, span_elt_mem hn hb⟩ := Subtype.ext (by
        show varpiIdeal n ^ 2 = _
        rw [pow_two, a_sq hn (n / 8) hk])
  rw [h1]
  exact (picClass_congr hn (u' := 2) (v' := 1) hb (by decide) (-1) (elt n (-((n / 8 : ℕ) : ℤ)) 0)
    (by rw [elt_lin]; congr 1 <;> ring)).symm

theorem pic_omega (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 0) (v := 1) (by decide)⟩ =
      sigmaClass n * wClass n ^ 2 := by
  have hb : ((1 * 2 - (n : ℤ) * 2 * 1) + (1 * 1 + 2 * 2)) % 2 = 1 := by omega
  rw [← pic_sigma hn, ← pic_w2 hn, ← map_mul]
  have h1 : (⟨_, span_elt_mem (n := n) hn (u := 1) (v := 2) (by decide)⟩ :
      integralIdealsPrimeTo (O4 n).conductorModulus) *
        ⟨_, span_elt_mem (n := n) hn (u := 2) (v := 1) (by decide)⟩ =
      ⟨_, span_elt_mem hn hb⟩ := Subtype.ext (by
        show Ideal.span _ * Ideal.span _ = _
        rw [Ideal.span_singleton_mul_span_singleton, elt_mul])
  rw [h1]
  exact (picClass_congr hn (u' := 0) (v' := 1) hb (by decide) 1 (elt n (-4 * (n / 8 : ℕ) - 2) 1)
    (by rw [elt_lin]; congr 1 <;> omega)).symm

/-- **The kernel of `Pic(O_{n,4}) → Cl(K_n)` is `{1, σ, w², σw²}`** (for `n ≡ 5 (mod 8)`). -/
theorem ker_cases (hn : n % 8 = 5) (hsq : Squarefree n) {k : Pic (O4 n)}
    (hk : picToMax (O4 n) k = 1) :
    k = 1 ∨ k = sigmaClass n ∨ k = wClass n ^ 2 ∨ k = sigmaClass n * wClass n ^ 2 := by
  have hn4 : n % 4 = 1 := by omega
  obtain ⟨J, rfl⟩ := (O4 n).picClass_surjective k
  have hJ0 : (J : Ideal (𝓞 (QNeg n))) ∈ (Ideal (𝓞 (QNeg n)))⁰ := mem_nonZeroDivisors_of_ne_zero (by
    rw [Ideal.zero_eq_bot]
    exact ((mem_integralIdealsPrimeTo_conductorModulus_iff (O4 n)).1 J.2).1)
  rw [picToMax_picClass (O4 n) J hJ0] at hk
  have hk' : (ClassGroup.mk0 ⟨(J : Ideal (𝓞 (QNeg n))), hJ0⟩ : ClassGroup (𝓞 (QNeg n))) = 1 := hk
  rw [ClassGroup.mk0_eq_one_iff] at hk'
  obtain ⟨⟨x, hx⟩⟩ := hk'
  obtain ⟨u, v, rfl⟩ := eq_elt hn4 hsq x
  have hmem : Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
    have := J.2; rw [show (J : Ideal (𝓞 (QNeg n))) = Ideal.span {elt n u v} from hx] at this
    exact this
  have huv := odd_of_mem hn hsq hmem
  have hJ : J = ⟨_, span_elt_mem hn huv⟩ := Subtype.ext hx
  rw [hJ]
  rcases (by omega : v % 4 = 0 ∨ v % 4 = 2 ∨ (v % 2 = 1 ∧ u % 4 = 0) ∨ (v % 2 = 1 ∧ u % 4 = 2))
    with h | h | h | h
  · left
    rw [picClass_congr hn huv (u' := 1) (v' := 0) (by decide) u (elt n 0 (v / 4)) (by rw [elt_lin]; congr 1 <;> omega),
      pic_one hn]
  · right; left
    rw [picClass_congr hn huv (u' := 1) (v' := 2) (by decide) u (elt n 0 ((v - 2 * u) / 4))
      (by rw [elt_lin]; congr 1 <;> omega), pic_sigma hn]
  · right; right; right
    rw [picClass_congr hn huv (u' := 0) (v' := 1) (by decide) v (elt n (u / 4) 0) (by rw [elt_lin]; congr 1 <;> omega),
      pic_omega hn]
  · right; right; left
    rw [picClass_congr hn huv (u' := 2) (v' := 1) (by decide) v (elt n ((u - 2 * v) / 4) 0)
      (by rw [elt_lin]; congr 1 <;> omega), pic_w2 hn]

end Ker3

end KerSec

section KerFix

theorem acts4_one (n : ℕ) [NeZero n] : ActsAsArtin4 1 n 1 := by
  intro x; simp

/-- **Glue KER proved.** -/
theorem kerFixesZnMod (hs : TYZSigmaFixesZn) (hw : TYZThm36OneFive) (hz : ZnOverH4) :
    KerFixesZnMod := by
  intro n hn0 hn hsq k hk ρ hρ
  have hzH := hz n hn hsq
  let P : Pic (O4 n) → Prop := fun c => ∀ ρ : GalQ, ActsAsArtin4 ρ n c →
    ∃ j : ℤ, galPt ρ (tyzZn n) = tyzZn n + j • tauG 2
  have hmul : ∀ c c', P c → P c' → P (c * c') := by
    intro c c' hc hc' ρ hρ
    obtain ⟨ρ1, h1⟩ := exists_actsAsArtin4 n c
    obtain ⟨ρ2, h2⟩ := exists_actsAsArtin4 n c'
    obtain ⟨j1, hj1⟩ := hc ρ1 h1
    obtain ⟨j2, hj2⟩ := hc' ρ2 h2
    refine ⟨j1 + j2, ?_⟩
    rw [acts4_galPt hρ (acts4_mul h1 h2) hzH, galPt_mul, hj2, map_add, map_zsmul, galPt_tauG_two,
      hj1, add_zsmul]
    abel
  have h1 : P 1 := fun ρ hρ => ⟨0, by
    rw [acts4_galPt hρ (acts4_one n) hzH, galPt_one, zero_zsmul, add_zero]⟩
  have hσ : P (sigmaClass n) := fun ρ hρ => ⟨0, by
    rw [hs n hn0 hn hsq ρ hρ, zero_zsmul, add_zero]⟩
  have hw2 : P (wClass n ^ 2) := by
    intro ρ hρ
    obtain ⟨ρw, hρw⟩ := exists_actsAsArtin4 n (wClass n)
    obtain ⟨k1, hk1⟩ := hw n hn0 hn hsq ρw hρw
    have hi := wNegatesI n hn0 hn hsq ρw hρw
    refine ⟨1 + 2 * k1, ?_⟩
    rw [acts4_galPt hρ (by rw [pow_two]; exact acts4_mul hρw hρw) hzH, galPt_mul, hk1, map_add,
      map_add, hk1, map_zsmul, galPt_tauG_two, galPt_tauG_one_one_of_neg hi]
    have h11 := tauG_one_one_add
    rw [← h11]
    module
  rcases ker_cases hn hsq hk with rfl | rfl | rfl | rfl
  · exact h1 ρ hρ
  · exact hσ ρ hρ
  · exact hw2 ρ hρ
  · exact hmul _ _ hσ hw2 ρ hρ

end KerFix

/-! ### The main glue: `Lemma321Five` from the inputs -/

section Main

theorem betaOneSign_neg_five {e : ℕ} (he : e % 8 = 5) : betaOneSign (-(e : ℤ)) = -1 := by
  have h2 : ¬ (2 : ℤ) ∣ -(e : ℤ) := by omega
  have h8 : (-(e : ℤ)) % 8 = 3 := by omega
  have he0 : e ≠ 0 := by omega
  simp [betaOneSign, oddPartSqfree, h2, h8, he0]

theorem fixes_omegaBar {e : ℕ} [NeZero e] (he : e % 8 = 5) (hse : Squarefree e) {σ γ : GalQ}
    (hσ : IsBetaOneLift σ) (hγ : IsComplexConj γ) : (σ * γ⁻¹) (omegaBar e) = omegaBar e := by
  have hsq : omegaBar e ^ 2 = ((-(e : ℤ) : ℤ) : Qbar) := by rw [omegaBar_sq]; push_cast; ring
  have hD : (-(e : ℤ)) ≠ 0 := by omega
  have hγω : γ (omegaBar e) = -omegaBar e := by
    rw [hγ.apply_sqrt hD hsq, if_pos (by omega)]; ring
  have hsqf : Squarefree (-(e : ℤ)) := sqf_neg (Int.squarefree_natCast.2 hse)
  have hσω : σ (omegaBar e) = -omegaBar e := by
    rw [hσ _ hsqf _ hsq, betaOneSign_neg_five he]; push_cast; ring
  rw [AlgEquiv.mul_apply, hγ.inv_apply, hγω, map_neg, hσω, neg_neg]

/-- `z_n ∈ A(H_{n,4})` from `Shimura.ShimuraReciprocityModFn`. -/
theorem znOverH4_of (hS : Shimura.ShimuraReciprocityModFn) : ZnOverH4 := by
  intro n hn hsq
  have h1 := cmFieldTYZ_of_ringClassD (Shimura.cmFieldOfDefinition_of_shimuraModFn hS) n hn hsq
  have hi := iInH4 n hn hsq
  exact sub_mem h1 (iPt_mem hi h1)

/-- **The core glue**: TYZ's proof of Lemma 3.21(1) for one `e ≡ 5 (mod 8)` and any lift `σ`. -/
theorem five_single (hz : ZnOverH4) (hc : TYZThm36ConjFive) (hw : TYZThm36OneFive)
    (hk : KerFixesZnMod) (hg : BetaOnGenus5) {e : ℕ} [NeZero e] (he5 : e % 8 = 5)
    (hse : Squarefree e) {σ : GalQ} (hσ : IsBetaOneLift σ) :
    ∃ k : ℤ, galPt σ (genusSum (Phi0 e) (tyzZn e)) + genusSum (Phi0 e) (tyzZn e) =
      (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2 := by
  classical
  obtain ⟨γ, hγ⟩ := exists_complexConj
  obtain ⟨a, ha⟩ := exists_acts4_of_fix (fixes_omegaBar he5 hse hσ hγ)
  have hzH : (tyzZn e) ∈ ptsOver (H4bar e) := hz e he5 hse
  have hb := hg e inferInstance he5 hse σ γ hσ hγ a ha
  set T := Phi0 e with hTdef
  have hT : IsPhi0 e T := phi0_spec e
  set P := picToMax (O4 e) with hPdef
  set w := wClass e with hwdef
  have hcl : ∀ t ∈ T, ∃ c ∈ picSquares (O4 e), ActsAsArtin4 t e c := hT.1
  choose! cl hclsq hclact using hcl
  have hPsq : ∀ t ∈ T, P (cl t) ∈ picSquares (OK e) := by
    intro t ht
    obtain ⟨b, hb'⟩ := hclsq t ht
    exact ⟨P b, by rw [← hb']; simp [powMonoidHom_apply, map_pow]⟩
  have huniq : ∀ c' ∈ picSquares (OK e), ∀ ρ₁ ∈ T, ∀ ρ₂ ∈ T, ActsAsArtinO e (OK e) ρ₁ c' →
      ActsAsArtinO e (OK e) ρ₂ c' → ρ₁ = ρ₂ := by
    intro c' hc' ρ₁ h₁ ρ₂ h₂ a₁ a₂
    exact (hT.2 c' hc').unique ⟨h₁, a₁⟩ ⟨h₂, a₂⟩
  have hactsO : ∀ t ∈ T, ActsAsArtinO e (OK e) t (P (cl t)) := fun t ht =>
    actsO_of_acts4 (hclact t ht)
  have hinj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, P (cl t₁) = P (cl t₂) → t₁ = t₂ := by
    intro t₁ h₁ t₂ h₂ hP
    exact huniq _ (hPsq t₂ h₂) t₁ h₁ t₂ h₂ (hP ▸ hactsO t₁ h₁) (hactsO t₂ h₂)
  set B := P (a * w⁻¹) with hBdef
  have htgt : ∀ t ∈ T, B * (P (cl t))⁻¹ ∈ picSquares (OK e) := fun t ht =>
    Subgroup.mul_mem _ hb (Subgroup.inv_mem _ (hPsq t ht))
  have hex : ∀ t ∈ T, ∃ s, s ∈ T ∧ ActsAsArtinO e (OK e) s (B * (P (cl t))⁻¹) :=
    fun t ht => (hT.2 _ (htgt t ht)).exists
  choose! f hfT hfact using hex
  have hPf : ∀ t ∈ T, P (cl (f t)) = B * (P (cl t))⁻¹ := fun t ht =>
    artinO_inj e (hactsO (f t) (hfT t ht)) (hfact t ht)
  have hτ2 : ∀ ρ : GalQ, galPt ρ (tauG 2) = tauG 2 := galPt_tauG_two
  have key : ∀ t ∈ T, ∃ j : ℤ,
      galPt σ (galPt t (tyzZn e)) = tauG ⟨1, -1⟩ - galPt (f t) (tyzZn e) + j • tauG 2 := by
    intro t ht
    obtain ⟨ρw, hρw⟩ := exists_actsAsArtin4 e w
    set k := a * (cl t)⁻¹ * w⁻¹ * (cl (f t))⁻¹ with hkdef
    have hk1 : P k = 1 := by
      rw [hkdef, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hPf t ht, hBdef, map_mul,
        map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    obtain ⟨ρk, hρk⟩ := exists_actsAsArtin4 e k
    have h1 : σ * t = (σ * γ⁻¹) * (γ * t * γ⁻¹) * γ := by group
    have hA : ActsAsArtin4 ((σ * γ⁻¹) * (γ * t * γ⁻¹)) e (a * (cl t)⁻¹) :=
      acts4_mul ha (actsAsArtin4_conj (hγ.ne_omega e) (hclact t ht))
    have hB : ActsAsArtin4 (f t * ρk * ρw) e (a * (cl t)⁻¹) := by
      have := acts4_mul (acts4_mul (hclact (f t) (hfT t ht)) hρk) hρw
      convert this using 1
      rw [hkdef]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    obtain ⟨k1, hk1'⟩ := hw e inferInstance he5 hse ρw hρw
    obtain ⟨j2, hj2⟩ := hk e inferInstance he5 hse k hk1 ρk hρk
    obtain ⟨j3, hj3⟩ := galPt_tauG_one_one ρk
    have hfi : (f t) iQ = iQ := by
      obtain ⟨b, hb2⟩ := hclsq (f t) (hfT t ht)
      have hact := hclact (f t) (hfT t ht)
      rw [← hb2] at hact
      exact fixes_iQ_of_actsAsArtin4_sq hact
    refine ⟨-(k1 + j2 + j3), ?_⟩
    rw [← galPt_mul, h1, galPt_mul (σ * γ⁻¹ * (γ * t * γ⁻¹)) γ, hc e he5 hse γ hγ, map_sub, hτ2,
      acts4_galPt hA hB hzH, galPt_mul, galPt_mul, hk1']
    simp only [map_add, map_zsmul, hj2, hj3, hτ2, galPt_tauG _ hfi]
    have h11 : tauG ⟨1, 1⟩ = tauG 2 - tauG ⟨1, -1⟩ := eq_sub_of_add_eq tauG_one_one_add
    rw [h11]
    module
  choose! J hJ using key
  have hsum : ∑ t ∈ T, galPt (f t) (tyzZn e) = ∑ t ∈ T, galPt t (tyzZn e) := by
    refine Finset.sum_nbij f hfT ?_ ?_ (fun t _ => rfl)
    · intro t₁ h₁ t₂ h₂ he
      have h := (hPf t₁ h₁).symm.trans ((congrArg (fun s => P (cl s)) he).trans (hPf t₂ h₂))
      exact hinj t₁ h₁ t₂ h₂ (inv_injective (mul_left_cancel h))
    · intro s hs
      obtain ⟨t, ⟨htT, htact⟩, -⟩ := hT.2 (B * (P (cl s))⁻¹) (htgt s hs)
      refine ⟨t, htT, ?_⟩
      have hPt : P (cl t) = B * (P (cl s))⁻¹ := artinO_inj e (hactsO t htT) htact
      have : P (cl (f t)) = P (cl s) := by
        rw [hPf t htT, hPt]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      exact hinj _ (hfT t htT) s hs this
  have hcard : T.card = gNat e := by
    rw [← card_sqClasses]
    refine Finset.card_nbij (fun t => P (cl t)) (fun t ht => mem_sqClasses.2 (hPsq t ht)) ?_ ?_
    · intro t₁ h₁ t₂ h₂ he; exact hinj t₁ h₁ t₂ h₂ he
    · intro c' hc'
      rw [Finset.mem_coe, mem_sqClasses] at hc'
      obtain ⟨t, ⟨htT, htact⟩, -⟩ := hT.2 c' hc'
      exact ⟨t, htT, artinO_inj e (hactsO t htT) htact⟩
  refine ⟨∑ t ∈ T, J t, ?_⟩
  simp only [genusSum, map_sum]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t ht => by rw [hJ t ht])]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, hsum, hcard,
    ← Finset.sum_smul]
  rw [natCast_zsmul]
  abel

/-- **`Lemma321Five` from the inputs** (any lift `σ` works for every `e`). -/
theorem lemma321Five_of (hβ : BetaOneLiftExists) (hz : ZnOverH4) (hc : TYZThm36ConjFive)
    (hw : TYZThm36OneFive) (hk : KerFixesZnMod) (hg : BetaOnGenus5) : Lemma321Five := by
  intro n hn hsq
  obtain ⟨σ, hσ⟩ := hβ
  refine ⟨σ, hσ, fun e he he5 => ?_⟩
  have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
  haveI : NeZero e := ⟨by omega⟩
  rw [tyzZ_five he5]
  exact five_single hz hc hw hk hg he5 hse hσ

/-- **`Lemma321Five` from tyz-cm's textbook CM leaf, `BetaOneLiftExists` and `KerFixesZnMod`.** -/
theorem lemma321Five_of_shimuraModFn (hS : Shimura.ShimuraReciprocityModFn)
    (hβ : BetaOneLiftExists) (hk : KerFixesZnMod) : Lemma321Five :=
  lemma321Five_of hβ (znOverH4_of hS)
    (tyzThm36ConjFive_of (cmAlgebraic_of_cmValue (Shimura.cmValueRingClass_of_modFn hS)))
    (tyzThm36OneFive_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS)
      (cmAlgebraic_of_cmValue (Shimura.cmValueRingClass_of_modFn hS)) wNegatesI)
    hk betaOnGenus5

/-- **`Lemma321Five` from tyz-cm's textbook CM leaf and `BetaOneLiftExists`.** -/
theorem lemma321Five_of_shimuraModFn_betaOneLift (hS : Shimura.ShimuraReciprocityModFn)
    (hβ : BetaOneLiftExists) : Lemma321Five :=
  lemma321Five_of_shimuraModFn hS hβ
    (kerFixesZnMod
      (Shimura.tyzSigmaFixesZn_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS)
        Shimura.etaModelFricke)
      (tyzThm36OneFive_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS)
        (cmAlgebraic_of_cmValue (Shimura.cmValueRingClass_of_modFn hS)) wNegatesI)
      (znOverH4_of hS))

open ZInQ.Contrib.TYZDecomp in
/-- **TYZ reading A with `Lemma321Five` discharged**: from the three `𝓛`-leaves, tyz-cm's textbook CM
leaf `Shimura.ShimuraReciprocityModFn`, TYZ Lemma `torsion2` (`Lemma318Literal`), Theorem 3.3/3.5
(`Thm35First`) and the glue `BetaOneLiftExists` (Kummer theory over `ℚ`). -/
theorem tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_betaOneLift
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (hβ : BetaOneLiftExists) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five h11 h1 h29 hS h318 h35
    (lemma321Five_of_shimuraModFn_betaOneLift hS hβ)

/-- **Glue BETA-EX proved** (`T321B.betaOneLiftExists`). -/
theorem betaOneLiftExists' : BetaOneLiftExists := ZInQ.Contrib.TYZGenus.T321B.betaOneLiftExists

/-- **`Lemma321Five` (TYZ Lemma 3.21(1), pinned) from tyz-cm's textbook CM leaf alone.** -/
theorem lemma321Five_of_shimuraModFn' (hS : Shimura.ShimuraReciprocityModFn) : Lemma321Five :=
  lemma321Five_of_shimuraModFn_betaOneLift hS betaOneLiftExists'

open ZInQ.Contrib.TYZDecomp in
/-- **TYZ reading A from the three `𝓛`-leaves, `Shimura.ShimuraReciprocityModFn`, TYZ Lemma `torsion2`
(`Lemma318Literal`) and Theorem 3.3/3.5 (`Thm35First`)**: cm-bridge's headline with `Lemma321Five`
removed. -/
theorem tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ) :
    ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_betaOneLift h11 h1 h29 hS h318 h35
    betaOneLiftExists'

end Main

end ZInQ.Contrib.TYZGenus.T321

/-! ## Axiom audit (tyz-321) -/

#print axioms ZInQ.Contrib.TYZGenus.T321.lemma321Five_of
#print axioms ZInQ.Contrib.TYZGenus.T321.tyzThm36ConjFive_of
#print axioms ZInQ.Contrib.TYZGenus.T321.tyzThm36OneFive_of
#print axioms ZInQ.Contrib.TYZGenus.T321.wNegatesI
#print axioms ZInQ.Contrib.TYZGenus.T321.betaOnGenus5
#print axioms ZInQ.Contrib.TYZGenus.T321.kerFixesZnMod
#print axioms ZInQ.Contrib.TYZGenus.T321.lemma321Five_of_shimuraModFn_betaOneLift
#print axioms ZInQ.Contrib.TYZGenus.T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_betaOneLift
#print axioms ZInQ.Contrib.TYZGenus.T321B.betaOneLiftExists
#print axioms ZInQ.Contrib.TYZGenus.T321.lemma321Five_of_shimuraModFn'
#print axioms ZInQ.Contrib.TYZGenus.T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First

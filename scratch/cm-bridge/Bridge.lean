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
main theorem with only the remaining leaves.

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

/-- TYZ's place `v₂` for `n ≡ 7 (mod 8)` (Theorem 3.6(3), L1424–1425: the place above 2 with
`v₂(√−n − δ) ≥ 6`): the prime `𝔭₂ = (2, (√−n − δ)/2)` of `𝓞_{K_n}`, `δ = tyzDelta n`,
`(√−n − δ)/2 = θ − (δ+1)/2`, `θ = (1 + √−n)/2`. (`⊤` if `n % 4 ≠ 3`.) The binary form of `[𝔭₂]` is
`[2, δ mod 4, ·]` (used in `thm36_7.py`). -/
def p2Ideal (n : ℕ) [NeZero n] : Ideal (𝓞 (QNeg n)) :=
  if h : n % 4 = 3 then
    Ideal.span {2, ZInQ.RouteK.Redei.thetaO n h - (((tyzDelta n + 1) / 2 : ℕ) : 𝓞 (QNeg n))}
  else ⊤

theorem p2Ideal_mem (n : ℕ) [NeZero n] : p2Ideal n ∈ (Ideal (𝓞 (QNeg n)))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  unfold p2Ideal
  split_ifs with h
  · intro h0
    have h2 : (2 : 𝓞 (QNeg n)) ∈ Ideal.span {2, ZInQ.RouteK.Redei.thetaO n h -
        (((tyzDelta n + 1) / 2 : ℕ) : 𝓞 (QNeg n))} := Ideal.subset_span (by simp)
    rw [h0, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
    exact two_ne_zero h2
  · exact top_ne_bot

/-- The class `[𝔭₂] ∈ Cl(K_n) = Pic(𝓞_{K_n})`. -/
def p2Class (n : ℕ) [NeZero n] : Pic (OK n) :=
  (ClassGroup.mk0 ⟨p2Ideal n, p2Ideal_mem n⟩ : ClassGroup (𝓞 (QNeg n)))

/-- **Leaf TYZ-3.6(3) (Galois action on TYZ's class-7 CM point)**: for squarefree `n ≡ 7 (mod 8)`,
complex conjugation `γ` and any `ρ ∈ Gal(ℚ̄/ℚ)` acting on the Hilbert class field `H_n` as the
(arithmetic) Artin symbol of `[𝔭₂]^{−5}`: `γ(z_n) + ρ(z_n) = τ(1/2)`. TYZ Theorem 3.6(3) (L1424–1427,
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
`χ_p([𝔭₂]) = (N𝔭₂/p) = (2/p)`), and `G_n = K_n(√p* : p ∣ n)` (Gauss). Not proved here. -/
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

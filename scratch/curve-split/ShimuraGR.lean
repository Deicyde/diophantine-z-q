import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue

/-! # curve-split: row H-83 `VertWitness.ShimuraGoodReduction` (copied) and its guard clause

`pIdeal`, `Zloc`, `IsShimuraModel`, `ShimuraSmoothModel`, `ShimuraGoodReduction`, `CMObjectsExist` and
`cmObjectsExist_of_R1R2fp` are copied verbatim (docstrings included) from
`scratch/vert-witness/VertWitness.lean` (namespace `VertWitness`, under its `open`s); they depend
only on `ZInQKernel/` (the QM layer). The row cannot be split into published-form leaves today
(report §3.6). Proved here: the last clause of `IsShimuraModel` (a `ℚ̄`-point of `𝒴`) follows from
the surjectivity clause once one level-3 QM object over `ℚ̄` exists, and one exists by the kernel's
bundle leaf `R1R2fp` (`cmObjectsExist_of_R1R2fp`). So the published-form leaf, when it can be
stated, needs no guard clause. No `sorry`, no `axiom`. -/

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV GlueDescent.B2Q

noncomputable section

namespace VertWitness

open CategoryTheory AlgebraicGeometry Limits LeafQM.AV

/-- The prime ideal `(p)` of `ℤ`. -/
abbrev pIdeal (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

instance pIdeal_isPrime (p : ℕ) [hp : Fact p.Prime] : (pIdeal p).IsPrime :=
  (Ideal.span_singleton_prime (Int.natCast_ne_zero.2 hp.out.ne_zero)).2
    (Nat.prime_iff_prime_int.1 hp.out)

/-- `ℤ_(p)`, the localization of `ℤ` at `(p)`. -/
abbrev Zloc (p : ℕ) [Fact p.Prime] : Type := Localization.AtPrime (pIdeal p)

/-- **The smooth model of `Y₃` over `ℤ_(p)` (the data asserted by the leaf).** A scheme `𝒴`
over `ℤ_(p)`, proper and smooth of relative dimension 1, with a family `𝒜 → 𝒴` of level-3 QM
abelian surfaces (`QMFamily`: proper smooth of relative dimension 2, `ι(a)` and level sections
`η(a)`), such that

* (fibres) for every field `K ⊇ ℚ`, the fibre of `𝒜` at every `K`-point of `𝒴` is an object
  `(A, ι, η)` over `K` (`IsFibreOf`; a `K`-point of `𝒴` is automatically over `ℤ_(p)`, as
  `Hom(ℤ_(p), K)` is a singleton in characteristic 0);
* (moduli on `ℚ̄`-points) two `ℚ̄`-points with isomorphic fibres are equal, and every object over
  `ℚ̄` is a fibre;
* (Hecke) each twist `α ∈ Aut 𝒪` and each `u ∈ 𝒪^×` is induced on `ℚ̄`-points by an automorphism of
  `𝒴` over `ℤ_(p)`;
* (guard, as in R1fp) `𝒴` has a `ℚ̄`-point (without it `𝒴 = ∅` would satisfy every clause if
  `QML3 ℚ̄` were mis-encoded as empty). -/
def IsShimuraModel (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 : QMFamily 𝒴.left) : Prop :=
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : Spec (CommRingCat.of K) ⟶ 𝒴.left),
      ∃ P : QML3 K, IsFibreOf 𝒜 y P) ∧
    (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → M3.mk P = M3.mk P' → y = y') ∧
    (∀ P : QML3 Qbar, ∃ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, IsFibreOf 𝒜 y P) ∧
    (∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g : 𝒴 ≅ 𝒴, ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.twist α (M3.mk P)) ∧
    (∀ u : (LeafQM.O)ˣ, ∃ g : 𝒴 ≅ 𝒴, ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.rightMul u (M3.mk P)) ∧
    Nonempty (Spec (CommRingCat.of Qbar) ⟶ 𝒴.left)

/-- The leaf's assertion at `p`: some `(𝒴, 𝒜)` is a smooth model as in `IsShimuraModel`. -/
def ShimuraSmoothModel (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜

/-- **Leaf: good reduction of `Y₃` at the primes `p > 324`** (in the field-point form of the
representability of the integral moduli problem).

*Published statement* (locators UNVERIFIED; no network): for an indefinite quaternion algebra `B`
over `ℚ` of discriminant `D`, a maximal order `𝒪`, and a neat open compact `K = ∏ K_ℓ ⊂ 𝒪̂^×`
with `K_p = 𝒪_p^× ≅ GL₂(ℤ_p)` for a prime `p ∤ D`, the moduli problem of abelian surfaces with
`𝒪`-action (and, in the PEL form, a principal polarization of the fixed Rosati type) and
`K`-level structure, on `ℤ_(p)`-schemes, is representable by a smooth proper curve over `ℤ_(p)`
whose generic fibre is the Shimura curve `Sh_K` over `ℚ`.
- R. Kottwitz, *Points on some Shimura varieties over finite fields*, J. AMS 5 (1992), 373-444,
  §5 (bibliographic identity established in docs/research/locators.md row R1; §5 itself unread,
  UNVERIFIED): PEL moduli with neat `K^p` and hyperspecial `K_p` are smooth over `𝒪_{E,(p)}`;
  proper when `B` is a division algebra. This covers the level `K₃` at `3 ∣ D` (`3 ≠ p`).
- K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), §1-§4
  (UNVERIFIED): the polarization-free moduli of `(A, ι)` with level structure over `ℤ[1/DN]`.
- Y. Morita, *Reduction modulo 𝔓 of Shimura curves*, Hokkaido Math. J. 10 (1981), 209-238
  (main theorem; number UNVERIFIED): good reduction of `Sh_K` at `p ∤ D·level`.
- H. Carayol, *Sur la mauvaise réduction des courbes de Shimura*, Compositio Math. 59 (1986),
  151-230 (UNVERIFIED; its main construction is for totally real `F ≠ ℚ`, so cite Kottwitz or
  Buzzard first). Whether Morita and Carayol allow level at a prime dividing `D` is UNVERIFIED.

Here `B = (2, −3)`, `D = 6`, `K = K₃` (full level 3, neat), and `p > 324` (so `p ∤ 6`).

*Why this Lean form is a consequence, never stronger*: restrict the representing isomorphism to
`Spec K` for fields `K` of characteristic 0 (fibre clause: the object at `y` is `y*` of the
universal object; this is the shape of `IsFibreOf`, as in R1fp's `R1famProps`), and to
`K = ℚ̄` for the bijection (as in R1fp, the polarization is dropped by Lemma P in characteristic 0);
`twist α` and `rightMul u` are automorphisms of the moduli functor over `ℤ_(p)` (defined on
families over any base), hence by Yoneda automorphisms of `𝒴` over `ℤ_(p)`, which act on
`ℚ̄`-points as stated. Only `p > 324` is asserted (the published range is `p ∤ 6`). The leaf
says nothing about a coordinate on `𝒴/Γ'`; that is glue (`ModelGaussGlue`). -/
def ShimuraGoodReduction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraSmoothModel p

/-- **CM objects exist over `ℚ̄`** (an input of the coordinate glue: it pins the normalization of
the coordinate by the three CM orbits): level-3 QM surfaces over `ℚ̄` with CM by `ℤ[i]`, `ℤ[ζ₃]`
and `ℤ[√−6]`. Derived from the bundle leaf `R1R2fp` (`cmObjectsExist_of_R1R2fp`). -/
def CMObjectsExist : Prop :=
  (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧ (∃ P : QML3 Qbar, HasCM24 P.q)

/-- **`CMObjectsExist` from the bundle leaf `R1R2fp`** (compiled: `CMExists` on `X₆`, a level
structure from `X6Surj`, and invariance of the CM predicates under isomorphism). -/
theorem cmObjectsExist_of_R1R2fp (hRR : R1R2fp) : CMObjectsExist := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, hX, -, hE, -, hsurj, -⟩ := hRR
  obtain ⟨-, -, -, -, -, hf⟩ := hX
  have lift : ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      ∃ P' : QML3 Qbar, Nonempty (QMIso P.q P'.q) := by
    intro x P hP
    obtain ⟨y, hy⟩ := hsurj.2 x
    obtain ⟨P', hP'⟩ := Quotient.exists_rep (s := isoSetoid Qbar) (Φ Qbar y)
    have h1 := hf y P' hP'.symm
    rw [hy, hP] at h1
    exact ⟨P', Quotient.exact h1⟩
  obtain ⟨⟨x₄, P₄, h₄, c₄⟩, ⟨x₃, P₃, h₃, c₃⟩, ⟨x₂, P₂, h₂, c₂⟩⟩ := hE
  obtain ⟨Q₄, ⟨g₄⟩⟩ := lift x₄ P₄ h₄
  obtain ⟨Q₃, ⟨g₃⟩⟩ := lift x₃ P₃ h₃
  obtain ⟨Q₂, ⟨g₂⟩⟩ := lift x₂ P₂ h₂
  exact ⟨⟨Q₄, HasCM4.of_iso g₄ c₄⟩, ⟨Q₃, HasCM3.of_iso g₃ c₃⟩, ⟨Q₂, HasCM24.of_iso g₂ c₂⟩⟩

/-! ## Part 3: the glue and the composite -/


end VertWitness

namespace CurveSplit

open CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness

/-- `IsShimuraModel` without its last clause (the `ℚ̄`-point guard). -/
def IsShimuraModelNoGuard (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 : QMFamily 𝒴.left) : Prop :=
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : Spec (CommRingCat.of K) ⟶ 𝒴.left),
      ∃ P : QML3 K, IsFibreOf 𝒜 y P) ∧
    (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → M3.mk P = M3.mk P' → y = y') ∧
    (∀ P : QML3 Qbar, ∃ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, IsFibreOf 𝒜 y P) ∧
    (∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g : 𝒴 ≅ 𝒴, ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.twist α (M3.mk P)) ∧
    (∀ u : (LeafQM.O)ˣ, ∃ g : 𝒴 ≅ 𝒴, ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.rightMul u (M3.mk P))

/-- **The guard clause is redundant given one object over `ℚ̄`** (proved). -/
theorem isShimuraModel_iff (hobj : Nonempty (QML3 Qbar)) (p : ℕ) [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left) :
    IsShimuraModel p 𝒴 𝒜 ↔ IsShimuraModelNoGuard p 𝒴 𝒜 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, -⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    obtain ⟨P⟩ := hobj
    obtain ⟨y, -⟩ := h5 P
    exact ⟨h1, h2, h3, h4, h5, h6, h7, ⟨y⟩⟩

/-- `ShimuraGoodReduction` without the guard clause. -/
def ShimuraGoodReductionNoGuard : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModelNoGuard p 𝒴 𝒜

/-- **H-83 from its guard-free form and the kernel bundle leaf `R1R2fp`** (proved). -/
theorem shimuraGoodReduction_of_noGuard (hRR : R1R2fp) (h : ShimuraGoodReductionNoGuard) :
    ShimuraGoodReduction := by
  intro p _ hp
  obtain ⟨𝒴, 𝒜, hM⟩ := h p hp
  obtain ⟨⟨P, -⟩, -, -⟩ := cmObjectsExist_of_R1R2fp hRR
  exact ⟨𝒴, 𝒜, (isShimuraModel_iff ⟨P⟩ p 𝒴 𝒜).mpr hM⟩

end CurveSplit

#print axioms CurveSplit.shimuraGoodReduction_of_noGuard

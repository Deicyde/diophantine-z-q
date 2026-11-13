import ZInQKernel.HDecomp.QM.Pairs

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/leaf-qm-fp/QMLeaves.lean`, §8.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

noncomputable section

namespace LeafQM

namespace AV

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

variable {K : Type} [Field K]

/-! ## §8 The leaves -/

/-- **A family of level-3 QM abelian surfaces over a scheme `S`** (qm-pin; the data of an object
of the moduli problem over `S`, without the group law, which rigidity recovers): a scheme
`𝒜 → S`, proper and smooth of relative dimension 2, with endomorphisms `ι(a)` over `S`
(`a ∈ 𝒪`) and sections `η(a) : S → 𝒜` (`a ∈ 𝒪`; for the universal object, the images of the
constant sections under the level structure `(𝒪/3𝒪)_S ≅ 𝒜[3]`). -/
structure QMFamily (S : Scheme.{0}) where
  F : Over S
  proper : IsProper F.hom
  smooth : SmoothOfRelativeDimension 2 F.hom
  iota : O → (F.left ⟶ F.left)
  iota_over : ∀ a : O, iota a ≫ F.hom = F.hom
  eta : O → (S ⟶ F.left)
  eta_sec : ∀ a : O, eta a ≫ F.hom = 𝟙 S

/-- **`P` is the fibre of the family `𝒜` at the field point `y : Spec K → S`** (qm-pin): a
morphism `g : P.A → 𝒜` making `P.A → Spec K` the pullback of `𝒜 → S` along `y`, carrying `ι_P`
to `ι_𝒜` and the level points `η_P(a)` to the sections `η_𝒜(a)` (the shape of
`IsBaseChangeOf`). -/
def IsFibreOf {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K) : Prop :=
  ∃ g : P.A.X.left ⟶ 𝒜.F.left,
    IsPullback g P.A.X.hom 𝒜.F.hom y ∧
    (∀ a : O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a) ∧
    (∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = y ≫ 𝒜.eta a)

/-- **R1fam, clause** (qm-pin, repairing rv-g0pieces §4): `Φ` is induced by a family: there is a
family `𝒜` over `Y` (the universal object of R1(a), polarization forgotten) such that the class
`Φ_K(y)` of every field point is the class of the fibre `y*𝒜`. Without it, `Φ` composed with a
non-geometric natural relabeling of the points of `Y` satisfies every other clause
(rv-g0pieces `r1fp_relabel`, `r1fp_exotic`). -/
def R1famProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ 𝒜 : QMFamily Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
    Φ K y = M3.mk P → IsFibreOf 𝒜 y.left P

/-- **R1fp, clause list** (for a candidate `Y₃` with its bijections `Φ`): `Y` is proper and smooth
of relative dimension 1 over `ℚ`, has a `ℚ̄`-point (a guard against vacuity: with `Y = ∅` every
other clause would hold if `QML3` were mis-encoded as empty), `Φ` is natural in the field (the
class of a point pulled back along `f : K → L` is the base change of the class), and `Φ` is
induced by a family over `Y` (`R1famProps`, added by qm-pin: it pins `Φ` up to automorphisms of
`Y`). -/
def R1fpProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ

/-- **R1hecke, clause list**: each operation `twist α` (`α ∈ Aut 𝒪`) and `rightMul u`
(`u ∈ 𝒪^×`) of `Γ'` on the moduli problem is induced by an automorphism of `Y` over `ℚ`. -/
def R1heckeProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  (∀ α : O ≃+* O, ∃ g : Y ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ g.hom) = M3.twist α (Φ K y)) ∧
  (∀ u : Oˣ, ∃ g : Y ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ g.hom) = M3.rightMul u (Φ K y))

/-- **R2fp, clause list**: a morphism `π : Y → P¹` whose fibres on `ℚ̄`-points are exactly the
classes with `Aut(𝒪)`-twist-equivalent underlying QM pairs (the `W`-orbits on `X₆`), and which
takes the values `0, ∞, −16/27` at the CM points of discriminants `−4, −3, −24`. -/
def R2fpProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
    Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q → π.val (K := Qbar) y.left = OnePoint.some 0) ∧
      (HasCM3 P.q → π.val (K := Qbar) y.left = OnePoint.infty) ∧
      (HasCM24 P.q → π.val (K := Qbar) y.left = OnePoint.some (-16 / 27))

/-- The `Aut(𝒪)`-twist of a QM pair (the `W`-action on `X₆`, inner twists being trivial on
classes). -/
def QMPair.twist (P : QMPair K) (α : O ≃+* O) : QMPair K := ⟨P.A, P.surface, P.q.twist α⟩

/-- **The level-one curve `X₆ = X₀(6,1)`, clause list** (coarse moduli on `ℚ̄`-points): `X` is a
proper smooth curve over `ℚ`; `Ψ : X(ℚ̄) ≃ {QM pairs over ℚ̄}/≅` is Galois-equivariant; each twist
`α ∈ Aut 𝒪` is induced by an automorphism of `X` over `ℚ` (the Atkin–Lehner group `W`); the
forgetful morphism `fY : Y₃ → X₆` is `(A, ι, η) ↦ (A, ι)` on `ℚ̄`-points. -/
def X6Props (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) : Prop :=
  IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧ Nonempty (fieldPt Qbar ⟶ X) ∧
  (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
    Ψ x = Quotient.mk _ P → ∃ Q : QMPair Qbar,
      Ψ (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = Quotient.mk _ Q ∧
      IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q) ∧
  (∀ α : O ≃+* O, ∃ g : X ≅ X, ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ (x ≫ g.hom) = Quotient.mk _ (P.twist α)) ∧
  (∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    Ψ (y ≫ fY) = Quotient.mk _ P.forget)

/-- **R2 on `X₆` (Baba–Granath), clause list**: `π₆ : X₆ → X₆/W ≅ P¹`; two `ℚ̄`-points have the
same value iff their QM pairs are `Aut(𝒪)`-twists of each other (`W`-conjugate); the CM points
of discriminants `−4, −3, −24` go to `0, ∞, −16/27`. -/
def R2X6Props (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (π₆ : ToP1 X.left) : Prop :=
  ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
      (π₆.val (K := Qbar) x.left = π₆.val (K := Qbar) x'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q → π₆.val (K := Qbar) x.left = OnePoint.some 0) ∧
      (HasCM3 P.q → π₆.val (K := Qbar) x.left = OnePoint.infty) ∧
      (HasCM24 P.q → π₆.val (K := Qbar) x.left = OnePoint.some (-16 / 27))

/-- **Existence of the three CM points on `X₆`** (the "distinguished points" of Baba–Granath
Lemma 3.1 are images of CM points; also González–Rotger Prop. 5.6 gives `#CM(R) = 2^b h(R) = 2`
for each of the three orders; CM points by `R` exist iff `R` embeds optimally in `𝒪`,
Shimura/Eichler; `ℤ[i], ℤ[ζ₃], ℤ[√−6]` do, by `i + j`, `(1 + j)/2`, `μ = 2j + k`). With the
fibre clause of `R2X6Props` and the invariance of `com` under twists (`com_twist`) and
isomorphisms, it gives the converse clauses "`π₆(x) = 0 ⇒` CM by `ℤ[i]`" etc. used by h-b1 M9. -/
def CMExists (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Prop :=
  (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM4 P.q) ∧
  (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM3 P.q) ∧
  (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM24 P.q)

/-- The conductor `[𝒪_k : R]` of a subring `R ⊆ 𝒪_k` (0 if the index is infinite). -/
def conductor {k : Type} [Field k] (R : Subring k) : ℕ :=
  R.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup

open Classical in
/-- `b(k) = #{p ∣ 6 : p inert in k}` (`p·𝒪_k` prime). For an order of conductor prime to 6 this
is `b(R) = #{p ∣ D(R)}` of rv-nocm §3.1. -/
def inertCount6 (k : Type) [Field k] [NumberField k] : ℕ :=
  (if (Ideal.span {(2 : NumberField.RingOfIntegers k)}).IsPrime then 1 else 0) +
    (if (Ideal.span {(3 : NumberField.RingOfIntegers k)}).IsPrime then 1 else 0)

/-- **Surjectivity on `ℚ̄`-points, clause list**: `π₆ : X₆ → P¹` is onto `P¹(ℚ̄)` (it is the
quotient map `X₆ → X₆/W` followed by Baba–Granath's isomorphism `X₆/W ≅ P¹`), and the forgetful
map `Y₃ → X₆` is onto `X₆(ℚ̄)` (every QM pair over `ℚ̄` admits a level-3 structure: `Y₃ → X₆` is
the finite surjective forgetful map of R1). Needed to choose a fibre over `J(u)` (A4). -/
def X6Surj (Y : Over (Spec (CommRingCat.of ℚ))) (X : Over (Spec (CommRingCat.of ℚ)))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left) : Prop :=
  (∀ t : OnePoint Qbar, ∃ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = t) ∧
  (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x)

/-- The residue field `κ(x)` of the point `x` of a `ℚ̄`-point `y : Spec ℚ̄ → X`, as a subfield of
`ℚ̄` (the image of the embedding `κ(x) ↪ ℚ̄` determined by `y`; it is a subfield containing `ℚ`,
so it equals the `ℚ`-subfield it generates). -/
def residueImage {X : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X) :
    IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ (Set.range (Scheme.SpecToEquivOfField Qbar X y).2)

/-- **R1rec on points, clause list** (Shimura reciprocity at the three elliptic CM points,
unramified form): a `ℚ̄`-point of `Y₃` whose object has CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` has
residue field `ℚ(y)` a number field unramified at every `p ≥ 5`. Reciprocity is printed as the
Galois action on points of the canonical model; this unramifiedness is its consequence, on points,
in the form Lemma NV uses. -/
def R1recProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
      UnramifiedAbove5 (residueImage (X := Y.left) y.left)

/-- **R5 on points of `X₆`, clause list** (González–Rotger Thm 5.12 in its printed form: about
the residue field `ℚ(x)` of the CM point `x ∈ X₀(6,1)`): for a `ℚ̄`-point `x` of `X₆` whose pair
has `End_𝒪(A) ≅ R`, `R` of conductor prime to 6 in an imaginary quadratic `k`,
`[ℚ(x) : ℚ] = 2h(R)` and `k ↪ ℚ(x)` if some `p ∣ 6` is inert in `k`, and `[ℚ(x) : ℚ] = h(R)`
otherwise (see `R5fp` for the reading of `D(R)`). NoCM (A10) uses residue fields of points, and
the bridge from `fieldOfModuliPair` to residue fields needs rigidity, so this form is carried in
the bundle (as `R1recProps` is for reciprocity). -/
def R5ptProps (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        Nonempty (com P.q ≃+* R) →
        Module.finrank ℚ (residueImage (X := X.left) x.left) =
          (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] residueImage (X := X.left) x.left))

/-- **Glue (compiled), h-b1 M9 on `X₆`**: every `ℚ̄`-point of `X₆` over `0` (resp. `∞`,
`−16/27`) has CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`), from the fibre clause, the existence of
one such CM point, and the invariance of the CM predicates under twists and isomorphisms. -/
theorem cm_of_val {X : Over (Spec (CommRingCat.of ℚ))}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {π₆ : ToP1 X.left}
    (h2 : R2X6Props X Ψ π₆) (hE : CMExists X Ψ) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar)
    (hP : Ψ x = Quotient.mk _ P) :
    (π₆.val (K := Qbar) x.left = OnePoint.some 0 → HasCM4 P.q) ∧
    (π₆.val (K := Qbar) x.left = OnePoint.infty → HasCM3 P.q) ∧
    (π₆.val (K := Qbar) x.left = OnePoint.some (-16 / 27) → HasCM24 P.q) := by
  obtain ⟨⟨x₄, P₄, h₄, c₄⟩, ⟨x₃, P₃, h₃, c₃⟩, ⟨x₂, P₂, h₂, c₂⟩⟩ := hE
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨α, ⟨g⟩⟩ := ((h2 x₄ x P₄ P h₄ hP).1).1 (((h2 x₄ x₄ P₄ P₄ h₄ h₄).2.1 c₄).trans hx.symm)
    exact HasCM4.of_iso g ((hasCM4_twist P₄.q α).2 c₄)
  · obtain ⟨α, ⟨g⟩⟩ := ((h2 x₃ x P₃ P h₃ hP).1).1
      (((h2 x₃ x₃ P₃ P₃ h₃ h₃).2.2.1 c₃).trans hx.symm)
    exact HasCM3.of_iso g ((hasCM3_twist P₃.q α).2 c₃)
  · obtain ⟨α, ⟨g⟩⟩ := ((h2 x₂ x P₂ P h₂ hP).1).1
      (((h2 x₂ x₂ P₂ P₂ h₂ h₂).2.2.2 c₂).trans hx.symm)
    exact HasCM24.of_iso g ((hasCM24_twist P₂.q α).2 c₂)

/-- **Glue (compiled): R2 on `Y₃` from R2 on `X₆`**, for `π = π₆ ∘ fY` (`ToP1.comp`). -/
theorem R2fpProps_of_X6 {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (hX : X6Props Y Φ X Ψ fY)
    (h2 : R2X6Props X Ψ π₆) : R2fpProps Y Φ (π₆.comp fY.left) := by
  obtain ⟨-, -, -, -, -, hf⟩ := hX
  intro y y' P Q hP hQ
  have h := h2 (y ≫ fY) (y' ≫ fY) P.forget Q.forget (hf y P hP) (hf y' Q hQ)
  have e : ∀ z : fieldPt Qbar ⟶ Y,
      (π₆.comp fY.left).val (K := Qbar) z.left = π₆.val (K := Qbar) (z ≫ fY).left :=
    fun z => ToP1.val_comp_right π₆ fY.left z.left
  rw [e y, e y']
  exact h

/-- **Leaf R1fp (field-point form of Shimura–Deligne R1(a)).**

*Published statement* (Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), Thm 4.21,
Cor. 5.7, Ex. 5.8, §§4.8-4.17 (read by the locator audit; printed page mapping not recovered);
Shimura, Ann. of Math. 85 (1967), Main Thms I-II (UNVERIFIED); alternatively Buzzard, Duke Math.
J. 87 (1997), Thm 2.1, Cor. 2.3 (UNVERIFIED), for `(A, ι)` with level structure and no
polarization): for the maximal order `𝒪` of `B = (2,−3)` and the neat level `K₃`, the functor on
`ℚ`-schemes of `(A, ι, λ, η)` (abelian surface scheme, `𝒪`-action, principal polarization with
Rosati involution `a ↦ μ⁻¹āμ`, `𝒪`-linear `η : 𝒪/3𝒪 ≅ A[3]`) is represented by a smooth
projective curve `Y₃/ℚ`.

*Lean form*: some `Y` over `ℚ`, proper and smooth of relative dimension 1, with bijections
`Y(K) ≃ M3 K` for all fields `K ⊇ ℚ`, natural in `K`, induced by a family `𝒜 → Y` (proper,
smooth of relative dimension 2, with `ι` and level sections): `Φ_K(y)` is the class of the fibre
`y*𝒜` (qm-pin; `𝒜` is the universal object of the representing scheme, `λ` forgotten).

*Why faithful (a consequence, never stronger)*: restrict the representing isomorphism to
`Spec K` for fields `K`; projective implies proper; the universal object `(𝒜, ι, λ, η)` over
`Y₃` is an abelian scheme (proper, smooth of relative dimension 2), and by Yoneda the object at
`y : Spec K → Y₃` is `y*(𝒜, ι, λ, η)` (the pullback square of `IsFibreOf`; `η(a)` the section of
`𝒜[3]` matching `a mod 3`). `M3 K` drops `λ` (Lemma P (rv-qm-polar §0): for
a fixed `μ` (N5's `2j+ij`), the type-`μ` principal
polarization of `(A, ι)` exists and is unique in characteristic 0, also at CM points;
VERIFIED as an argument, lattice cores compiled for N5's `μ` on `Λ = 𝒪` only
(`RvQMPolar.eq_pm_E0_of_principal`, `RvQMPolar.type_eq_mu_mul`, `RvQMPolar.lemmaP_lattice` in
`QM/Polar.lean`; the passage to polarizations of `A`, `Λ = 𝒪v`, class number one and the descent
from `ℂ` are not compiled), published
locators UNVERIFIED;
not needed on Buzzard's route), and puts `η` on
`K`-points (equivalent in characteristic 0, §2 docstring). `Y` is **not** required to be
geometrically connected (it has two geometric components over `ℚ(√−3)`, bp-qmmoduli §2.1).

*Status of the faithfulness claim.* (i) Audit verdict on R1 (locators.md): "UNVERIFIED as the full
literal leaf; qualified CONSEQUENCE": the specialization of Deligne's PEL model to this functor
(lattice, polarization-compatible level structure, PEL conditions, component convention,
`E(G,h) = ℚ`) still needs a human check. (ii) On the Shimura–Deligne route the leaf is "published
theorem + Lemma P": the published moduli theorems are for the type-`μ` PEL problem; the λ-free
leaves are their consequences via Lemma P (see above) and do not depend on the choice of `μ`. On
Buzzard's route no polarization enters, but
whether his Thm 2.1 covers full level 3 directly is UNVERIFIED. -/
def R1fp : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ

/-- **Leaves R1fp + R1hecke + R1 at level one + R2fp (with `CMExists`, `X6Surj`) + R1rec and R5
(point forms), on one `Y₃` and one `X₆`** (the form the glue consumes; `R1R2fp_Y` extracts the `Y₃`
form). `R1recProps` is
documented at its definition; the object form `R1rec` is kept as a separate leaf.

*R1 at level one (`X6Props`), published statement*: `X₆ = X₀(6,1)` (Shimura's curve for the
maximal order, no level) is a coarse moduli space over `ℚ` for `(A, ι, λ)` (Shimura 1967, Deligne
1971 as for R1fp; UNVERIFIED as a literal locator, the audit read Deligne's §§4.9-4.17); the
Atkin–Lehner group acts on it over `ℚ`. *Why faithful*: coarse moduli give `X₆(ℚ̄) = {(A, ι)}/≅`
Galois-equivariantly in characteristic 0; the twists `(A, ι) ↦ (A, ι∘α)` are natural in families,
so the coarse space inherits them; `Y₃ → X₆` exists by the coarse universal property; the
morphism `Y₃ → P¹` is `π₆ ∘ fY` (`ToP1.comp`, `R1R2fp_Y`). Smooth proper curve: `X₆` is the quotient
of `ℍ` by a cocompact Fuchsian group without
cusps; its canonical model is smooth projective over `ℚ` (it is a smooth curve because a
coarse space of a one-dimensional smooth DM stack in characteristic 0 is a normal curve).

*R1hecke, published statement*: the finite-adelic normalizer of `K₃` acts on `Y₃` over `ℚ`
(Deligne 1971 §§4.15-4.21, Deligne 1979 §2.7, UNVERIFIED; the audit: at fixed level only the
subgroup preserving the level and the datum acts). *Why faithful*: `twist α` and `rightMul u`
are natural automorphisms of the moduli functor (they are defined for families over any base:
`(A, ι, η) ↦ (A, ι∘α, η∘α)` and `η ↦ η(·u)`), so by Yoneda each is induced by an automorphism of
the representing scheme. This is a consequence of R1(a) alone; on field points it is this
clause. (With `λ` in the functor: relative to `ι∘α` the kept `λ` has Rosati type `α⁻¹(μ)`, not
`μ`, unless `α(μ) ∈ ℚ^×μ`; a matching `λ' = λ∘ι(εv)`, `v = μ⁻¹α(μ) ∈ 𝒪¹` `†`-symmetric
(`RvQMPolar.twist_type`, the algebra only), `ε = sign trd v`, is defined in families, so the
twist is still a functor automorphism; for the Atkin–Lehner generators `i`, `j + k`, `v = −1`
and `λ' = λ`. Alternatively: `n ∈ N_B(𝒪)` normalizes `K₃`, so right
translation by `n_f` is an automorphism of `Y₃` over `E(G,X) = ℚ`; this is the "subgroup
preserving level and
datum" of the audit.) (`α = Ad n`, `n ∈ N_B(𝒪)`, by Skolem–Noether T13; `u` acts through `(𝒪/3𝒪)^×`,
`Level3.rightMul_eq_self`.)

*R2fp, published statement* (Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 p. 737 and
Lemma 3.1 pp. 739-740, read by the audit: YES): the forgetful map identifies the polarized
moduli space with `X₆/W`, `W ≅ (ℤ/2)²` the Atkin–Lehner group; `X₆/W ≅ P¹_ℚ`; the images of the
CM points of discriminants `−4, −3, −24` are rational. *Lean form*: `π = (Y₃ → X₆ → X₆/W ≅ P¹)`,
with the coordinate chosen so that the three CM images are `0, ∞, −16/27` (three distinct
rational points of `P¹_ℚ` can be moved to any three by `PGL₂(ℚ)`; so this normalization adds
nothing; identifying `π` with N5's `J` is F1's business, `PkgI1.QMHauptmodul`). Fibre clause:
two `ℚ̄`-points have the same image in `X₆/W` iff their `(A, ι)` are `W`-conjugate, i.e.
`(A', ι') ≅ (A, ι ∘ Ad w)`; `Aut(𝒪) = N_B(𝒪)/ℚ^×` (Skolem–Noether) and inner twists are trivial
on classes (`ι(u)` is an isomorphism `(A, ι∘Ad u) ≅ (A, ι)`), so `W`-conjugacy is
`∃ α ∈ Aut 𝒪`. The CM clauses need each of `CM(−4)`, `CM(−3)`, `CM(−24)` (two points on `X₆`
each: `2^b h` with `(b, h) = (1,1), (1,1), (0,2)`) to be a single `W`-orbit, i.e. one point of
`X₆/W`: this is Baba–Granath's §3.1 elliptic-order table (p. 740, read by the audit; signature
`(0; 2, 4, 6)`, forced by `1/3 ÷ 4 = 1/12 = 1 − 1/2 − 1/4 − 1/6`), not Thm 2.1/Lemma 3.1 alone.
**Not asserted**: the orbifold orders `(4, 6, 2)` (they are not ramification
indices of `X₆ → X₆/W`, which are `(2, 2, 2)`; the indices `(4, 6, 2)` of `Y₃ → P¹` are glue,
`RvNocm.ramification_eq_orbifold_order`). Composite: R2fp's fibre clause uses R1 (the forgetful
morphism `Y₃ → X₆` and the moduli interpretation of `X₆`) together with Baba–Granath. -/
def R1R2fp : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
      CMExists X Ψ ∧ R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

theorem R1fp_of_R1R2fp (h : R1R2fp) : R1fp := by
  obtain ⟨Y, Φ, -, -, -, -, h1, -, -, -, -, -, -, -⟩ := h
  exact ⟨Y, Φ, h1⟩

/-- The form consumed on `Y₃`: R1fp + R1hecke + R2fp on one `Y` with one `π`. -/
theorem R1R2fp_Y (h : R1R2fp) : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left), R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ R2fpProps Y Φ π := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, hX, h2, -, -, -, -⟩ := h
  exact ⟨Y, Φ, π₆.comp fY.left, h1, hh, R2fpProps_of_X6 hX h2⟩

/-- **Glue A7 from R1fp + R2fp (compiled).** Let `y` be a `ℚ̄`-point of `Y` with object `P` whose
`π`-value is rational. Then every Galois conjugate of `P` (its base change `Q` along `σ`) has an
underlying QM pair that is an `Aut(𝒪)`-twist of `P`'s; in particular `σA ≅ A` over `ℚ̄`
(h-trust A7: "the conjugates of `A` are geometrically isomorphic"). -/
theorem conj_twist_of_rational {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (π : ToP1 Y.left)
    (hfib : ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
      Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)))
    (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P) (j₀ : ℚ)
    (hj : π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀))
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    ∃ Q : QML3 Qbar, IsBaseChangeOf (σ : Qbar →+* Qbar) P Q ∧
      ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q) := by
  obtain ⟨-, -, -, hnat, -⟩ := h1
  obtain ⟨Q, hQ, hbc⟩ := hnat Qbar Qbar (σ : Qbar →ₐ[ℚ] Qbar) y P hP
  refine ⟨Q, hbc, (hfib y _ P Q hP hQ).1 ?_⟩
  calc π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) := hj
    _ = (OnePoint.some (algebraMap ℚ Qbar j₀)).map (σ : Qbar →+* Qbar) := by simp
    _ = (π.val (K := Qbar) y.left).map (σ : Qbar →+* Qbar) := by rw [hj]
    _ = π.val (K := Qbar) (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y).left :=
        (π.val_comp (σ : Qbar →+* Qbar) y.left).symm

/-- **Glue A7 (compiled), the manuscript's form.** Let `y` be a `K`-point of `Y` (e.g. `K` the
fibre field) with object `P` and rational `π`-value. For any two embeddings `ι₁, ι₂ : K → ℚ̄`, the
two base changes `P ⊗_{ι₁} ℚ̄`, `P ⊗_{ι₂} ℚ̄` exist as objects and their QM pairs are
`Aut(𝒪)`-twists of each other; in particular their abelian surfaces are isomorphic over `ℚ̄`
("every conjugate `σA` is isomorphic to `A` over `ℚ̄`", pkg-I1 (I1-out)(ii)). Uses only
`R1fpProps` (naturality) and `R2fpProps` (fibre clause), via `ToP1.val_comp`. -/
theorem conj_iso_of_rational {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π)
    {K : Type} [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K) (hP : Φ K y = M3.mk P)
    (j₀ : ℚ) (hj : π.val (K := K) y.left = OnePoint.some (algebraMap ℚ K j₀))
    (e₁ e₂ : K →ₐ[ℚ] Qbar) :
    ∃ Q₁ Q₂ : QML3 Qbar, IsBaseChangeOf (e₁ : K →+* Qbar) P Q₁ ∧
      IsBaseChangeOf (e₂ : K →+* Qbar) P Q₂ ∧
      ∃ α : O ≃+* O, Nonempty (QMIso (Q₁.q.twist α) Q₂.q) := by
  obtain ⟨-, -, -, hnat, -⟩ := h1
  obtain ⟨Q₁, hQ₁, hb₁⟩ := hnat K Qbar e₁ y P hP
  obtain ⟨Q₂, hQ₂, hb₂⟩ := hnat K Qbar e₂ y P hP
  refine ⟨Q₁, Q₂, hb₁, hb₂, ((h2 _ _ Q₁ Q₂ hQ₁ hQ₂).1).1 ?_⟩
  have e : ∀ e : K →ₐ[ℚ] Qbar, π.val (K := Qbar) (fieldMap e ≫ y).left =
      OnePoint.some (algebraMap ℚ Qbar j₀) := by
    intro e
    calc π.val (K := Qbar) (fieldMap e ≫ y).left
        = (π.val (K := K) y.left).map (e : K →+* Qbar) := π.val_comp (e : K →+* Qbar) y.left
      _ = OnePoint.some (algebraMap ℚ Qbar j₀) := by rw [hj]; simp
  rw [e e₁, e e₂]

/-- The underlying abelian surfaces of a QM-pair twist are isomorphic (A7's conclusion). -/
theorem QMIso.nonempty_abVarIso {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'}
    (f : QMIso q q') : ∃ (φ : AbVar.Hom A A') (ψ : AbVar.Hom A' A),
      φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ :=
  ⟨f.φ, f.ψ, f.left, f.right⟩

/-- **Leaf R1rec (Shimura reciprocity at the three elliptic CM points, unramified form).**

*Published statement*: Shimura reciprocity for CM points on the canonical model (Shimura 1967
Main Thm II; Deligne 1971 §§3.7-3.13, Thm 4.19 read by the audit, "CONSEQUENCE with
qualifications": reflex-field qualifications kept). For a CM point `y ∈ Y₃` with CM by the
maximal order `𝒪_E` of `E`, `Gal(E^ab/E)` acts on `y` through `rec : 𝔸_E^× → B̂^×/K₃`, and
`s ∈ ∏_{ℓ≠3} 𝒪_{E,ℓ}^×` maps into `gK₃g⁻¹` for `y = [τ, g]` (optimal embedding of the maximal
order `𝒪_E`), so `E(y)/E` is unramified outside `3` (h-b1 §3 step 2).

*Lean form*: for a level-3 object over `ℚ̄` whose centralizer contains `ℤ[i]`, `ℤ[ζ₃]` or
`ℤ[√−6]` (all maximal), the field of moduli `ℚ(y)` is a number field unramified at every
`p ≥ 5`.

*Why faithful*: `ℚ(y) ⊆ E(y)`, `E(y)/E` is unramified outside 3 and `E/ℚ` (discriminant `−4`,
`−3`, `−24`) is unramified outside `{2, 3}`; the field of moduli is `ℚ(y)` (fine moduli, R1). A
consequence of reciprocity plus R1's moduli interpretation; weaker than reciprocity. -/
def R1rec : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    UnramifiedAbove5 (fieldOfModuli3 P)

/-- **Glue (compiled): Lemma NV step 2** (h-b1 §3). A `ℚ̄`-point of `Y₃` over one of the three
branch values `0, ∞, −16/27` carries a CM object (by `cm_of_val` through the forgetful map), so by
`R1rec` its field of moduli `ℚ(y)` is a number field unramified at every `p ≥ 5`. -/
theorem unramified_over_branch (h : R1R2fp ∧ R1rec) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
        (π.val (K := Qbar) y.left = OnePoint.some 0 ∨
          π.val (K := Qbar) y.left = OnePoint.infty ∨
          π.val (K := Qbar) y.left = OnePoint.some (-16 / 27)) →
        UnramifiedAbove5 (fieldOfModuli3 P) := by
  obtain ⟨⟨Y, Φ, X, Ψ, fY, π₆, h1, -, hX, h2, hE, -, -, -⟩, hrec⟩ := h
  refine ⟨Y, Φ, π₆.comp fY.left, h1, R2fpProps_of_X6 hX h2, fun y P hP hv => hrec P ?_⟩
  obtain ⟨-, -, -, -, -, hf⟩ := hX
  have hc := cm_of_val h2 hE (y ≫ fY) P.forget (hf y P hP)
  have e : (π₆.comp fY.left).val (K := Qbar) y.left = π₆.val (K := Qbar) (y ≫ fY).left :=
    ToP1.val_comp_right π₆ fY.left y.left
  rw [e] at hv
  rcases hv with hv | hv | hv
  · exact Or.inl (hc.1 hv)
  · exact Or.inr (Or.inl (hc.2.1 hv))
  · exact Or.inr (Or.inr (hc.2.2 hv))

/-- **Glue (compiled): Lemma NV step 2, point form** (h-b1 §3, as used there): from `R1R2fp`
alone, a `ℚ̄`-point of `Y₃` over `0`, `∞` or `−16/27` has residue field `ℚ(y)` (`residueImage`) a
number field unramified at every `p ≥ 5`. -/
theorem residue_unramified_over_branch (h : R1R2fp) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ (y : fieldPt Qbar ⟶ Y),
        (π.val (K := Qbar) y.left = OnePoint.some 0 ∨
          π.val (K := Qbar) y.left = OnePoint.infty ∨
          π.val (K := Qbar) y.left = OnePoint.some (-16 / 27)) →
        UnramifiedAbove5 (residueImage (X := Y.left) y.left) := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, hX, h2, hE, hrec, -, -⟩ := h
  refine ⟨Y, Φ, π₆.comp fY.left, h1, R2fpProps_of_X6 hX h2, fun y hv => ?_⟩
  have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
  refine hrec y _ hP ?_
  obtain ⟨-, -, -, -, -, hf⟩ := hX
  have hc := cm_of_val h2 hE (y ≫ fY) _ (hf y _ hP)
  have e : (π₆.comp fY.left).val (K := Qbar) y.left = π₆.val (K := Qbar) (y ≫ fY).left :=
    ToP1.val_comp_right π₆ fY.left y.left
  rw [e] at hv
  rcases hv with hv | hv | hv
  · exact Or.inl (hc.1 hv)
  · exact Or.inr (Or.inl (hc.2.1 hv))
  · exact Or.inr (Or.inr (hc.2.2 hv))

/-- **Glue (compiled): A4, choosing a fibre.** From `R1R2fp`: over every value `t ∈ P¹(ℚ̄)`
(e.g. `t = J(u)`) there is a `ℚ̄`-point `y` of `Y₃` with an object `P` (an abelian surface with QM
by `𝒪` and level-3 structure over `ℚ̄`) and `π(y) = t`. -/
theorem exists_fibre_object (h : R1R2fp) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ t : OnePoint Qbar, ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
        Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = t := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, hX, h2, -, -, ⟨hπ, hf⟩, -⟩ := h
  refine ⟨Y, Φ, π₆.comp fY.left, h1, R2fpProps_of_X6 hX h2, fun t => ?_⟩
  obtain ⟨x, hx⟩ := hπ t
  obtain ⟨y, rfl⟩ := hf x
  refine ⟨y, Quotient.out (Φ Qbar y), (Quotient.out_eq _).symm, ?_⟩
  have e : (π₆.comp fY.left).val (K := Qbar) y.left = π₆.val (K := Qbar) (y ≫ fY).left :=
    ToP1.val_comp_right π₆ fY.left y.left
  rw [e, hx]

/-- **Glue (compiled): A4 + A7 from the leaves alone.** From `R1R2fp`: for every rational
`j₀`, there are `Y₃` (with `R1fpProps`), `π : Y₃ → P¹` (with `R2fpProps`), a `ℚ̄`-point `y` of
`Y₃` over `j₀` (`π(y) = j₀`) and the object `P` at `y` (`Φ y = [P]`), such that every Galois
conjugate of `P` (its base change `Q` along any `σ ∈ Aut(ℚ̄/ℚ)`) has abelian surface isomorphic
to that of `P` (through an `Aut(𝒪)`-twisted QM isomorphism). This is pkg-I1's (I1-out)(ii) for
the fibre over `J(u) = j₀`. (Strengthened by notes-fix, factcheck-w34b item 1: the earlier
conclusion `∃ P, ∀ σ, …` did not mention `j₀`.) -/
theorem fibre_conjugates_isomorphic (h : R1R2fp) (j₀ : ℚ) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧
        π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) ∧
        ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ Q : QML3 Qbar,
          IsBaseChangeOf (σ : Qbar →+* Qbar) P Q ∧
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q) := by
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ := exists_fibre_object h
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ Qbar j₀))
  exact ⟨Y, Φ, π, h1, h2, y, P, hP, hy, fun σ => conj_twist_of_rational h1 π
    (fun y y' P Q hP hQ => (h2 y y' P Q hP hQ).1) y P hP j₀ hy σ⟩

/-- **All glue conclusions on one witness** (so that A4, A5's Lemma NV step 2, A7 and M1 use the
same `Y₃` and `π`). -/
theorem leaves_on_one_witness (h : R1R2fp) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ R2fpProps Y Φ π ∧
      (∀ t : OnePoint Qbar, ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
        Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = t) ∧
      (∀ y : fieldPt Qbar ⟶ Y,
        (π.val (K := Qbar) y.left = OnePoint.some 0 ∨
          π.val (K := Qbar) y.left = OnePoint.infty ∨
          π.val (K := Qbar) y.left = OnePoint.some (-16 / 27)) →
        UnramifiedAbove5 (residueImage (X := Y.left) y.left)) := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, hX, h2, hE, hrec, ⟨hπ, hf⟩, -⟩ := h
  have e : ∀ z : fieldPt Qbar ⟶ Y,
      (π₆.comp fY.left).val (K := Qbar) z.left = π₆.val (K := Qbar) (z ≫ fY).left :=
    fun z => ToP1.val_comp_right π₆ fY.left z.left
  refine ⟨Y, Φ, π₆.comp fY.left, h1, hh, R2fpProps_of_X6 hX h2, fun t => ?_, fun y hv => ?_⟩
  · obtain ⟨x, hx⟩ := hπ t
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨y, Quotient.out (Φ Qbar y), (Quotient.out_eq _).symm, by rw [e, hx]⟩
  · have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
    refine hrec y _ hP ?_
    obtain ⟨-, -, -, -, -, hfo⟩ := hX
    have hc := cm_of_val h2 hE (y ≫ fY) _ (hfo y _ hP)
    rw [e] at hv
    rcases hv with hv | hv | hv
    · exact Or.inl (hc.1 hv)
    · exact Or.inr (Or.inl (hc.2.1 hv))
    · exact Or.inr (Or.inr (hc.2.2 hv))

/-- **Leaf R5fp (González–Rotger, fields of definition of CM points on `X₆`, degree form).**

*Published statement* (González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946, with
Thm 5.8, pp. 943-944, read by the audit in arXiv v1/v2 and the journal: YES on `X₀(D, N)`): for a
CM point `x ∈ X₀(6,1)` by an order `R` of conductor `f`, `(f, 6) = 1`, of an imaginary quadratic
`k`: `ℚ(x) = H_R` (the ring class field, `[H_R : ℚ] = 2h(R)`) if `D(R) ≠ 1`, and `ℚ(x)` is a
specified subfield of index 2 of `H_R` if `D(R) = 1`; `D(R)` = product of the primes `p ∣ 6`
inert in `k` (rv-nocm §3.1, h-decomposition R5); the printed condition is
`D(R)·N*(R) ≠ 1`, and `N*(R) = 1` at `N = 1`.

*Lean form*: for a QM pair over `ℚ̄` with `End_𝒪(A) ≅ R`,
`[ℚ(x) : ℚ] = 2h(R)` if `b(k) ≥ 1` and `h(R)` if `b(k) = 0`, `h(R) = #Pic(R)`; and if
`b(k) ≥ 1`, `k` embeds in `ℚ(x)` (from `ℚ(x) = H_R ⊇ k`). The containment is needed by NoCM
(rv-h-cm §7.2, case `D(R) ≠ 1`): the degree alone does not exclude `k = ℚ(√−19)` (`h = 1`,
`b = 2`, degree 2) against a fibre field `ℚ(i)`.

*Why faithful*: the degree of the printed field; `ℚ(x)` is the field of moduli for the coarse
space `X₆` (STANDARD); the points of `X₆` are QM pairs `(A, ι)`, which uses Lemma P
(rv-qm-polar §0: in characteristic 0, for a fixed `μ` the type-`μ` polarization exists and is
unique; see `R1fp`);
"CM by `R`" is `End_𝒪(A) = com ι ≅ R`. Only points of `X₆` (no level structure, no quotient). The
reading `D(R) = ∏_{p | 6 inert in k} p` is the audited one (checked on Elkies' 24 rows by
rv-nocm Part B); `R5fpWeak` below drops the case split. -/
def R5fp : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ P : QMPair Qbar, Nonempty (com P.q ≃+* R) →
        Module.finrank ℚ (fieldOfModuliPair P) =
          (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] fieldOfModuliPair P))

/-- R5fp without the case split (bp-qmmoduli's `R5fp`): `[ℚ(x) : ℚ] ∈ {h(R), 2h(R)}`. -/
def R5fpWeak : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ P : QMPair Qbar, Nonempty (com P.q ≃+* R) →
        Module.finrank ℚ (fieldOfModuliPair P) = Nat.card (CommRing.Pic R) ∨
          Module.finrank ℚ (fieldOfModuliPair P) = 2 * Nat.card (CommRing.Pic R)

theorem R5fpWeak_of_R5fp (h : R5fp) : R5fpWeak := by
  intro k _ _ _ hk R hR hc P hP
  have := (h k hk R hR hc P hP).1
  split_ifs at this
  · left; simpa using this
  · right; exact this

/-- **Leaf R5fpCount (González–Rotger Prop. 5.6, p. 943, read by the audit; Jordan 1981 §3),
corrected count.** For an order `R` of conductor prime to 6 in an imaginary quadratic `k`
occurring as some `End_𝒪(A)` (equivalently, embedding optimally in `𝒪`, so neither 2 nor 3
splits in `k`), the number of isomorphism classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R` (the
CM points by `R` on `X₆ = X₀(6,1)`) is `2^{b(R)} h(R)`. *Why faithful*: `#CM(R) =
2^{#{p | D(R)N(R)}} h(R)` with `N = 1`; points of `X₆(ℚ̄)` are classes of QM pairs (Lemma P in
characteristic 0, rv-qm-polar §0; see `R1fp`). **Not** the
false `h(R)` (disc −19: `h = 1`, four points). -/
def R5fpCount : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      (∃ P : QMPair Qbar, Nonempty (com P.q ≃+* R)) →
        Nat.card {c : Quotient (pairSetoid Qbar) //
            ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} =
          2 ^ inertCount6 k * Nat.card (CommRing.Pic R)

/-- **The bundle of this file's leaves** (replacing the placeholders `R01_ShimuraDeligne`,
`R02_BabaGranath`, `R05_GonzalezRotger` of `scratch/h-decomposition/Leaves.lean`, in their
field-point forms). Faithfulness of every leaf (`R1rec` too, whose objects are identified with
points of `Y₃`)
rests on the published theorems **plus**
Lemma P (rv-qm-polar §0): for a fixed `μ` (N5's `2j+ij`), the type-`μ` principal
polarization of `(A, ι)` exists and is unique in characteristic 0, also at CM points;
VERIFIED as an argument, lattice cores compiled for N5's `μ` on `Λ = 𝒪` only
(`RvQMPolar.eq_pm_E0_of_principal`, `RvQMPolar.type_eq_mu_mul`, `RvQMPolar.lemmaP_lattice` in
`QM/Polar.lean`; the passage to polarizations of `A`, `Λ = 𝒪v`, class number one and the descent
from `ℂ` are not compiled), published
locators UNVERIFIED, because `QML3`/`QMPair` omit `λ`. The published moduli theorems are for the
type-`μ` PEL problem; the λ-free leaves are their consequences via Lemma P and do not depend
on the choice of `μ`. Polarizations cannot be stated in Lean today (no dual abelian variety),
so Lemma P cannot be carried as a separate Lean hypothesis. -/
structure QMLeaves : Prop where
  r1r2 : R1R2fp
  r1rec : R1rec
  r5 : R5fp
  r5count : R5fpCount

end AV

end LeafQM

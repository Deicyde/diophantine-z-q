import Mathlib
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.Quotients
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves2

set_option autoImplicit false

/-!
# Normality of a scheme smooth over `ℤ[1/30]`

A scheme `X` smooth over `Spec ℤ[1/30]` is normal: its local rings are integrally closed
domains, and its rings of sections over affine opens are noetherian normal rings. The input is
the printed leaf EGA IV₄ (17.5.7), integrally closed case, in the direction from the base to the
source, applied to the structure map. The local rings of `Spec ℤ[1/30]` are integrally closed
domains because `ℤ[1/30]` is a localization of `ℤ` at nonzero elements.
-/

open CategoryTheory AlgebraicGeometry

namespace Y3Buzzard.SmoothNormal

/-- Leaf (EGA IV₄, Prop. (17.5.7)), the "intégralement clos" case, for a smooth morphism.

Source: A. Grothendieck, *Éléments de géométrie algébrique IV, Étude locale des schémas et des
morphismes de schémas (quatrième partie)*, Publ. Math. IHÉS 32 (1967), Prop. (17.5.7), p. 70:

"Proposition (17.5.7). — Soit f : X → Y un morphisme localement de présentation finie, lisse en
un point x ∈ X; posons y = f(x). Alors, pour que l'anneau 𝒪_{X,x} soit réduit (resp. intégralement
clos, resp. géométriquement unibranche), il faut et il suffit que 𝒪_{Y,y} le soit."

Convention. EGA 0_I (4.1.4) (Publ. Math. IHÉS 4 (1960), p. 37) calls a sheaf of rings normal
at a point "si sa fibre 𝒜_x est un anneau intègre et intégralement clos", and EGA IV₂ (5.13.5)
(Publ. Math. IHÉS 24 (1965), p. 133) says: "Nous dirons qu'un anneau A est normal si Spec(A) est
un schéma normal, autrement dit si, pour tout idéal premier p de A, A_p est intègre et
intégralement clos". In the proof of (5.8.6) (p. 108), "dire que X est normal signifie que pour
tout x ∈ X, O_x est un anneau local noethérien intégralement clos", and the proof goes on with
"puisque O_x est intègre": for local rings, EGA's "intégralement clos" includes "intègre"
(Bourbaki's convention). Here "integrally closed domain" is `IsDomain R ∧ IsIntegrallyClosed R`.

Only the "intégralement clos" case is stated, only in the direction from `𝒪_{Y,y}` to `𝒪_{X,x}`,
and for a morphism smooth at every point. The hypotheses of the Proposition hold at every point
`x`, with `y = f(x)`:
* `f` is locally of finite presentation: on affine opens its ring maps are smooth, and smooth
  algebras are finitely presented.
* `f` is lisse at `x`. For affine opens `U ⊆ Y` and `V ⊆ f⁻¹ U`, `Smooth f` makes the ring map
  `Γ(Y, U) → Γ(X, V)` smooth, so `Γ(X, V)` is a formally smooth `Γ(Y, U)`-algebra
  (`Algebra.Smooth`), and algebra maps into `B ⧸ I`, for `I` nilpotent, lift to `B`
  (`Algebra.FormallySmooth.exists_lift`). For affine schemes this lifting property is EGA's formal
  smoothness (17.1.1), by Remark (17.1.2)(i) (p. 56, via 0_IV (19.3.1) and (19.10.1)). Formal
  smoothness is local on `X` and on `Y` (17.1.6, pp. 58–59), so `f` is formally smooth, hence
  lisse (17.3.1, p. 61), and therefore lisse at every point of `X` (17.3.7, p. 62). -/
def EGAIV17_5_7 : Prop :=
  ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (x : X),
    IsDomain (Y.presheaf.stalk (f.base x)) → IsIntegrallyClosed (Y.presheaf.stalk (f.base x)) →
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-! ## Integrally closed domains -/

/-- The localization of an integrally closed domain at a prime is an integrally closed
domain. -/
theorem isDomain_isIntegrallyClosed_of_atPrime {R : Type*} (S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [IsDomain R] [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime S P] : IsDomain S ∧ IsIntegrallyClosed S :=
  ⟨IsLocalization.isDomain_of_atPrime S P,
    isIntegrallyClosed_of_isLocalization S P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P)⟩

/-- Being an integrally closed domain is invariant under ring isomorphisms. -/
theorem isDomain_isIntegrallyClosed_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : IsDomain R ∧ IsIntegrallyClosed R) :
    IsDomain S ∧ IsIntegrallyClosed S := by
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨MulEquiv.isDomain R e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e⟩

/-! ## The base `Spec ℤ[1/30]` -/

/-- `ℤ[1/30]` is a domain: it is the localization of `ℤ` at the powers of `30 ≠ 0`. -/
theorem isDomain_Z30 : IsDomain Y3RouteA.Z30 :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num))

/-- `ℤ[1/30]` is integrally closed: it is a localization of the integrally closed domain `ℤ` at
a submonoid of nonzero elements. -/
theorem isIntegrallyClosed_Z30 : IsIntegrallyClosed Y3RouteA.Z30 :=
  isIntegrallyClosed_of_isLocalization Y3RouteA.Z30 (Submonoid.powers (30 : ℤ))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num))

/-- The local rings of `Spec ℤ[1/30]` are integrally closed domains: the local ring at a prime
`P` is the localization `ℤ[1/30]_P`. -/
theorem stalk_Z30Base (y : Z30Base) :
    IsDomain (Z30Base.presheaf.stalk y) ∧ IsIntegrallyClosed (Z30Base.presheaf.stalk y) := by
  have := isDomain_Z30
  have := isIntegrallyClosed_Z30
  let P : PrimeSpectrum Y3RouteA.Z30 := y
  exact isDomain_isIntegrallyClosed_of_ringEquiv
    (Spec.stalkIso (CommRingCat.of Y3RouteA.Z30) P).commRingCatIsoToRingEquiv.symm
    (isDomain_isIntegrallyClosed_of_atPrime (Localization.AtPrime P.asIdeal) P.asIdeal)

/-! ## Schemes smooth over the base -/

/-- Smoothness of relative dimension `1` implies smoothness. -/
theorem smooth_of_smoothOfRelativeDimension_one {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

/-- The local rings of a scheme smooth over `Spec ℤ[1/30]` are integrally closed domains. -/
theorem stalk_of_smooth (hE : EGAIV17_5_7) (X : Over Z30Base) [Smooth X.hom] (x : X.left) :
    IsDomain (X.left.presheaf.stalk x) ∧ IsIntegrallyClosed (X.left.presheaf.stalk x) :=
  hE X.hom x (stalk_Z30Base (X.hom.base x)).1 (stalk_Z30Base (X.hom.base x)).2

/-! ## Rings of sections over affine opens -/

/-- A noetherian normal ring: a noetherian ring whose localizations at all primes are
integrally closed domains (a normal ring in the sense of EGA IV₂ (5.13.5), p. 133, quoted at
`EGAIV17_5_7`). -/
def IsNormalNoeth (R : Type) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ ∀ (p : Ideal R) (_ : p.IsPrime),
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)

/-- If `X` is smooth over `Spec ℤ[1/30]`, then the ring of sections of `X` over an affine open
is a noetherian normal ring. It is noetherian because `X` is locally of finite type over the
noetherian scheme `Spec ℤ[1/30]`; its localization at a prime is isomorphic to the local ring of
`X` at the corresponding point. -/
theorem isNormalNoeth_of_affine (hE : EGAIV17_5_7) (X : Over Z30Base) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) (hU : IsAffineOpen U) :
    IsNormalNoeth Γ(X.left, U) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  refine ⟨IsLocallyNoetherian.component_noetherian ⟨U, hU⟩, fun p hp => ?_⟩
  let y : PrimeSpectrum Γ(X.left, U) := ⟨p, hp⟩
  have hy : hU.fromSpec y ∈ U := (hU.isoSpec.inv y).2
  let _ : Algebra Γ(X.left, U) (X.left.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.left.presheaf.stalk (hU.fromSpec y)) p :=
    hU.isLocalization_stalk' y hy
  exact isDomain_isIntegrallyClosed_of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (X.left.presheaf.stalk (hU.fromSpec y))
      (Localization.AtPrime p)).toRingEquiv
    (stalk_of_smooth hE X (hU.fromSpec y))

/-! ## The base of the leaf B1′ -/

/-- The structure map of the moduli scheme of the leaf B1′ is smooth: B1′ makes it smooth of
relative dimension `1`. -/
theorem smooth_leafD (hB1 : BuzzardThm21Cor23V15') : Smooth (leafD hB1).X.hom :=
  @smooth_of_smoothOfRelativeDimension_one _ _ (leafD hB1).X.hom
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hB1))).2.1

/-- The rings of sections of the moduli scheme of the leaf B1′ over affine opens are noetherian
normal rings. -/
theorem isNormalNoeth_of_B1 (hE : EGAIV17_5_7) (hB1 : BuzzardThm21Cor23V15')
    (U : (leafD hB1).X.left.Opens) (hU : IsAffineOpen U) :
    IsNormalNoeth Γ((leafD hB1).X.left, U) :=
  haveI := smooth_leafD hB1
  isNormalNoeth_of_affine hE (leafD hB1).X U hU

/-- The local rings of the moduli scheme of the leaf B1′ are integrally closed domains: it is a
normal scheme. -/
theorem stalk_of_B1 (hE : EGAIV17_5_7) (hB1 : BuzzardThm21Cor23V15') (x : (leafD hB1).X.left) :
    IsDomain ((leafD hB1).X.left.presheaf.stalk x) ∧
      IsIntegrallyClosed ((leafD hB1).X.left.presheaf.stalk x) :=
  haveI := smooth_leafD hB1
  stalk_of_smooth hE (leafD hB1).X x

end Y3Buzzard.SmoothNormal

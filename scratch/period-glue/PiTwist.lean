import PGBase
/-! # period-glue: `PiTwistC` from R2fp and two smaller named Props

Task period-glue, 2026-11-13. `PiTwistC Y Φ π` (period-map, `PGBase`, unchanged) is proved from
* `R1fpProps Y Φ` (only: `Y` proper and smooth over `ℚ`) and `R2fpProps Y Φ π` (the leaves R1, R2;
  both already hypotheses at the own triple),
* `TwistOrbitFinite Y Φ` (**GLUE**, moduli: the twist relation on `ℚ̄`- and `ℂ`-points is the
  orbit relation of a finite set of automorphisms of `Y`), and
* `FibreTransferC Y π` (**GLUE**, algebraic geometry: a fibre statement for `π` that holds on
  `ℚ̄`-points holds on `ℂ`-points),
by `piTwistC_of`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

/-- **GLUE (moduli: the `Aut(𝒪)`-twist relation is a finite orbit relation).** There is a finite
set `G` of automorphisms of `Y` over `ℚ` such that, on `ℚ̄`-points and on `ℂ`-points, two points
have twist-equivalent QM pairs iff one is the image of the other under some `g ∈ G`.

Why true for the genuine `Y₃` (model argument): `G` = the automorphisms inducing `twist α`
(`α ∈ Aut 𝒪`) and `rightMul u` (`u ∈ 𝒪^×`) on points (`R1heckeProps`, a clause of R1), composed.
It is finite: `rightMul u` depends only on `u mod 3𝒪` (`Level3.rightMul_eq_self`), inner twists
are `rightMul`s up to isomorphism, and `Aut(𝒪)/Inn` is finite (mobius-glue `AutOInnerFinite`,
from the kernel's Skolem–Noether); an automorphism of the reduced `Y` is determined by its action
on field points. (⇐) is `Φ` of `y ≫ g`. (⇒) a QM isomorphism `Q.q.twist α ≅ Q'.q` transports
`Q'`'s level structure to one on `(A, ι∘α)`; over an algebraically closed field two level
structures on the same QM pair differ by right multiplication by a unit of `𝒪/3𝒪` (both are
`𝒪`-linear isomorphisms `𝒪/3𝒪 ≅ A[3]`, `|A[3]| = 81`), and `𝒪^× → (𝒪/3𝒪)^×` is onto (strong
approximation for `𝒪¹`, plus `1 + i` of reduced norm `−1`; a finite check on the 72 units of
`𝒪/3𝒪`); then `Φ` injective gives `y' = y ≫ g`. Size: medium. -/
def TwistOrbitFinite (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ G : Set (Y ≅ Y), G.Finite ∧
    (∀ (y y' : fieldPt Qbar ⟶ Y) (Q Q' : QML3 Qbar), Φ Qbar y = M3.mk Q → Φ Qbar y' = M3.mk Q' →
      ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
        ∃ g ∈ G, y' = y ≫ g.hom)) ∧
    (∀ (y y' : fieldPt ℂ ⟶ Y) (Q Q' : QML3 ℂ), Φ ℂ y = M3.mk Q → Φ ℂ y' = M3.mk Q' →
      ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
        ∃ g ∈ G, y' = y ≫ g.hom))

/-- **GLUE (algebraic geometry: transfer of a fibre statement from `ℚ̄`- to `ℂ`-points).** For a
proper smooth curve `Y` over `ℚ` (the hypotheses make the statement true for every `Y`; without
them it fails, e.g. for `Y = Spec ℂ`, which has no `ℚ̄`-points) and a finite set `G` of
automorphisms of `Y` over `ℚ`, if the fibres of `π` on `ℚ̄`-points are exactly
the `G`-orbits (in the sense below), the same holds on `ℂ`-points.

Why true (model argument), for `Y` of finite type and separated over `ℚ` (R1fp: proper):
`E = {(p, q) ∈ Y ×_ℚ Y : π(p) = π(q)}` (the equalizer of `π∘pr₁`, `π∘pr₂`, closed since `P¹` is
separated) and `Γ = ⋃_{g ∈ G} graph(g)` (finite union of closed graphs, `Y` separated) are closed
subsets of the finite-type `ℚ`-scheme `Y ×_ℚ Y`, hence Jacobson: each is the closure of its closed
points. Closed points are the images of `ℚ̄`-points (Nullstellensatz), and on those `E` and `Γ`
agree by hypothesis, so `E = Γ`. A `ℂ`-point `(y, y')` lies in `E` iff `π(y) = π(y')`, and in
`Γ` iff `y' = y ≫ g` for some `g ∈ G` (it factors through the reduced closed subscheme
`graph(g) ≅ Y`, `Y` smooth hence reduced). Mathlib has Jacobson schemes
(`AlgebraicGeometry.JacobsonSpace`) and equalizers/graphs of morphisms; the charts of `ToP1` must
be turned into a morphism to `P¹`. Size: medium. -/
def FibreTransferC (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ G : Set (Y ≅ Y), G.Finite →
    (∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)) →
    ∀ y y' : fieldPt ℂ ⟶ Y,
      (π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)

/-- **`PiTwistC` from R2fp, `TwistOrbitFinite` and `FibreTransferC` (proved).** -/
theorem piTwistC_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (hT : TwistOrbitFinite Y Φ)
    (hF : FibreTransferC Y π) :
    PiTwistC Y Φ π := by
  obtain ⟨G, hG, hQbar, hC⟩ := hT
  have hfibQ : ∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom) := by
    intro y y'
    have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
    have hQ : Φ Qbar y' = M3.mk (Quotient.out (Φ Qbar y')) := (Quotient.out_eq _).symm
    exact ((h2 y y' _ _ hP hQ).1).trans (hQbar y y' _ _ hP hQ)
  intro y y' Q Q' hQ hQ'
  exact (hF h1.1 h1.2.1 G hG hfibQ y y').trans (hC y y' Q Q' hQ hQ').symm

/-! ## `FibreTransferC` split into its two directions -/

/-- **GLUE (AG, textbook density): two maps to `P¹` agreeing on `ℚ̄`-points agree on `ℂ`-points.**
For `Y` proper and smooth over `ℚ` and `σ, ρ : Y → P¹` (by charts) with the same values at every
`ℚ̄`-point, the values agree at every `ℂ`-point.

Why true: the locus where two morphisms to the separated `P¹` agree, residue maps included, is a
closed subscheme (the equalizer). It contains every closed point, since closed points are images of
`ℚ̄`-points. `Y` is Jacobson (finite type over a field) and reduced (smooth), so the equalizer is
`Y`. Size: medium (the equalizer of two `ToP1` charts; Mathlib's `JacobsonSpace`). -/
def ToP1AgreeC (Y : Over (Spec (CommRingCat.of ℚ))) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ σ ρ : ToP1 Y.left,
    (∀ y : fieldPt Qbar ⟶ Y, σ.val (K := Qbar) y.left = ρ.val (K := Qbar) y.left) →
    ∀ y : fieldPt ℂ ⟶ Y, σ.val (K := ℂ) y.left = ρ.val (K := ℂ) y.left

/-- **GLUE (AG; the hard half of `FibreTransferC`).** If the fibres of `π` on `ℚ̄`-points are the
orbits of a finite set `G` of automorphisms, then two `ℂ`-points with the same `π`-value are in one
`G`-orbit.

Why true (model argument): the hypothesis forces `π` to be non-constant on every component (a
component has infinitely many `ℚ̄`-points, while `G`-orbits are finite). A `ℂ`-point over a closed
point of `Y` comes from a `ℚ̄`-point through one embedding `ℚ̄ → ℂ`, and so does every point in its
`π`-fibre (the value is algebraic, and `π` is non-constant on components). That case reduces to the
hypothesis. For points over generic points of components, the closed subsets `{π(p) = π(q)}` and
`⋃ graph(g)` of `Y ×_ℚ Y` agree on closed points, hence agree (Jacobson). Size: medium-large. -/
def FibreGenericC (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ G : Set (Y ≅ Y), G.Finite →
    (∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)) →
    ∀ y y' : fieldPt ℂ ⟶ Y,
      π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left → ∃ g ∈ G, y' = y ≫ g.hom

/-- **`FibreTransferC` from `ToP1AgreeC` and `FibreGenericC` (proved).** The direction (⇐) is
`ToP1AgreeC` applied to `π ∘ g` and `π`. -/
theorem fibreTransferC_of (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left)
    (hA : ToP1AgreeC Y) (hG : FibreGenericC Y π) : FibreTransferC Y π := by
  intro hP hS G hGf hQ y y'
  refine ⟨hG hP hS G hGf hQ y y', ?_⟩
  rintro ⟨g, hg, rfl⟩
  have e : ∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
      (π.comp g.hom.left).val (K := K) z.left = π.val (K := K) (z ≫ g.hom).left :=
    fun K _ _ z => ToP1.val_comp_right π g.hom.left (K := K) z.left
  have hagree := hA hP hS (π.comp g.hom.left) π (fun y0 => by
    rw [e]
    exact ((hQ y0 (y0 ≫ g.hom)).mpr ⟨g, hg, rfl⟩).symm) y
  rw [e] at hagree
  exact hagree.symm

/-! ## `TwistOrbitFinite` from R1hecke, `TorsionStructure` and two algebra facts -/

/-- **GLUE, proved in mobius-glue** (`scratch/mobius-glue/MobiusGlue.lean` §7, `AutOInnerFinite`,
from the kernel's Skolem–Noether and `N(𝒪)/ℚ^×𝒪^× = {1, i, j, ij}`; copied verbatim, it cannot be
imported here). Every automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely
many. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (LeafQM.O ≃+* LeafQM.O), T.Finite ∧ ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ t ∈ T,
    ∃ v : (LeafQM.O)ˣ, ∀ a : LeafQM.O,
      α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O)

/-- **GLUE (finite computation; strong approximation for `𝒪¹`).** Every element of `𝒪` that is
invertible modulo `3𝒪` is congruent modulo `3𝒪` to a unit of `𝒪` (`𝒪^× → (𝒪/3𝒪)^×` is onto).

Why true: `B` is indefinite, so `𝒪¹` is dense in `∏_p 𝒪_p¹` (Eichler's strong approximation,
Vignéras, *Arithmétique des algèbres de quaternions*, III.4; UNVERIFIED locator), hence
`𝒪¹ → (𝒪/3𝒪)¹` is onto; together with `1 + i` (reduced norm `−1`) this covers
`(𝒪/3𝒪)^×` (72 elements). A finite check: the reductions of finitely many explicit units of `𝒪`
generate the 72 classes. Size: small-medium (a `decide`-style computation over `(ℤ/3)⁴`). -/
def UnitLiftMod3 : Prop :=
  ∀ u₀ v₀ : LeafQM.O, (∃ c : LeafQM.O, v₀ * u₀ - 1 = 3 * c) →
    ∃ u : (LeafQM.O)ˣ, ∃ c : LeafQM.O, (u : LeafQM.O) - u₀ = 3 * c

section TwistOrbit

variable {K : Type} [Field K]

/-- Transport of a level structure along an isomorphism of QM pairs (copied from mobius-glue). -/
def transportLevel' {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (PkgI3.AbVar.ptMap (L := K) f.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ f.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ f.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ f.φ.hom) = _
    rw [Category.assoc, f.equivariant a, Category.assoc]
  ker a := by
    rw [← e.ker]
    constructor
    · intro h
      have h' : Additive.toMul (e.eta a) ≫ f.φ.hom = 1 := congrArg Additive.toMul h
      have : Additive.toMul (e.eta a) = 1 := by
        calc Additive.toMul (e.eta a) = Additive.toMul (e.eta a) ≫ f.φ.hom ≫ f.ψ.hom := by
              rw [f.left, Category.comp_id]
          _ = 1 := by rw [← Category.assoc, h', MonObj.one_comp]
      exact congrArg Additive.ofMul this
    · intro h
      change Additive.ofMul (Additive.toMul (e.eta a) ≫ f.φ.hom) = 0
      rw [h]
      change Additive.ofMul ((1 : _ ⟶ _) ≫ f.φ.hom) = 0
      rw [MonObj.one_comp]
      rfl

/-- A level-3 isomorphism gives a QM isomorphism. -/
def QML3.Iso.toQMIso {P Q : QML3 K} (f : P.Iso Q) : QMIso P.q Q.q where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant

/-- Twists by `t` and by `v t v⁻¹` are isomorphic through `ι(v)` (copied from mobius-glue). -/
def conjUnitIso' {A : PkgI3.AbVar K} (q : QMStr A) (t α : LeafQM.O ≃+* LeafQM.O) (v : (LeafQM.O)ˣ)
    (hv : ∀ a, α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O)) :
    QMIso (q.twist t) (q.twist α) where
  φ := q.iota v
  ψ := q.iota ↑v⁻¹
  left := by
    have : q.iota ↑v⁻¹ * q.iota ↑v = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    exact congrArg PkgI3.AbVar.Hom.hom this
  right := by
    have : q.iota ↑v * q.iota ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact congrArg PkgI3.AbVar.Hom.hom this
  equivariant a := by
    have : q.iota (v : LeafQM.O) * q.iota (t a) = q.iota (α a) * q.iota v := by
      rw [← map_mul, ← map_mul, hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact congrArg PkgI3.AbVar.Hom.hom this

/-- Finitely many representatives of the units of `𝒪` modulo `3𝒪`. -/
theorem unitReps : ∃ U : Set (LeafQM.O)ˣ, U.Finite ∧
    ∀ u : (LeafQM.O)ˣ, ∃ u' ∈ U, ∃ c : LeafQM.O, (u : LeafQM.O) - u' = 3 * c := by
  classical
  -- the class of `u` modulo `3𝒪`: its coordinates mod 3
  have hcoord : ∀ x : LeafQM.O, ∃ n : Fin 4 → ℤ, (x : LeafQM.B) = LeafQM.ofInt n := fun x => x.2
  choose n hn using hcoord
  let cls : (LeafQM.O)ˣ → (Fin 4 → ZMod 3) := fun u i => (n u i : ZMod 3)
  have hrep : ∀ c ∈ Set.range cls, ∃ u : (LeafQM.O)ˣ, cls u = c := fun c hc => hc
  choose! r hr using hrep
  refine ⟨r '' Set.range cls, (Set.toFinite (Set.range cls)).image r, fun u => ⟨r (cls u), ⟨_, ⟨u, rfl⟩, rfl⟩, ?_⟩⟩
  have hcl : cls (r (cls u)) = cls u := hr _ ⟨u, rfl⟩
  -- coordinates agree mod 3
  have hmod : ∀ i, (3 : ℤ) ∣ n u i - n (r (cls u)) i := by
    intro i
    have := congrFun hcl i
    simp only [cls] at this
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp this
    exact_mod_cast h3
  choose k hk using hmod
  refine ⟨⟨LeafQM.ofInt k, ⟨k, rfl⟩⟩, Subtype.ext ?_⟩
  show ((u : LeafQM.O) : LeafQM.B) - ((r (cls u) : LeafQM.O) : LeafQM.B) = 3 * LeafQM.ofInt k
  rw [hn, hn, LeafQM.AV.ofInt_sub, LeafQM.AV.three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  linear_combination hk i

/-- The twist relation is the orbit relation of `{g_t ∘ h_u : t ∈ T, u ∈ U}`, over any field of
characteristic `0` (proved). -/
theorem twist_iff_orbit (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hT : ObjBridge.TorsionStructure) (hU : UnitLiftMod3)
    (T : Set (LeafQM.O ≃+* LeafQM.O))
    (hTα : ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ t ∈ T, ∃ v : (LeafQM.O)ˣ, ∀ a : LeafQM.O,
      α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O))
    (U : Set (LeafQM.O)ˣ) (hUu : ∀ u : (LeafQM.O)ˣ, ∃ u' ∈ U, ∃ c : LeafQM.O, (u : LeafQM.O) - u' = 3 * c)
    (g : (LeafQM.O ≃+* LeafQM.O) → (Y ≅ Y))
    (hg : ∀ α (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ (g α).hom) = M3.twist α (Φ K y))
    (h : (LeafQM.O)ˣ → (Y ≅ Y))
    (hh : ∀ u (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ (h u).hom) = M3.rightMul u (Φ K y))
    (K : Type) [Field K] [Algebra ℚ K] [CharZero K] (y y' : fieldPt K ⟶ Y) (Q Q' : QML3 K)
    (hQ : Φ K y = M3.mk Q) (hQ' : Φ K y' = M3.mk Q') :
    (∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
      ∃ G' ∈ (fun p : (LeafQM.O ≃+* LeafQM.O) × (LeafQM.O)ˣ => g p.1 ≪≫ h p.2) '' (T ×ˢ U),
        y' = y ≫ G'.hom := by
  constructor
  · rintro ⟨α, ⟨f⟩⟩
    obtain ⟨t, ht, v, hv⟩ := hTα α
    let f' : QMIso (Q.q.twist t) Q'.q := (conjUnitIso' Q.q t α v hv).trans f
    let P : QML3 K := Q.twist t
    let e' : Level3 P.q := transportLevel' f'.symm Q'.e
    obtain ⟨u₀, v₀, hinv, hu₀⟩ := Level3.torsor hT P e'
    obtain ⟨u, cu, hcu⟩ := hU u₀ v₀ hinv
    obtain ⟨u', hu'U, cu', hcu'⟩ := hUu u
    have hlev : ∀ a : LeafQM.O, e'.eta a = P.e.eta (a * u') := by
      intro a
      rw [hu₀ a, P.e.eq_iff]
      exact ⟨a * (cu' - cu), by
        calc a * u₀ - a * (u' : LeafQM.O)
            = a * (((u : LeafQM.O) - u') - ((u : LeafQM.O) - u₀)) := by noncomm_ring
          _ = a * (3 * cu' - 3 * cu) := by rw [hcu, hcu']
          _ = 3 * (a * (cu' - cu)) := by noncomm_ring⟩
    let iso : (P.rightMul u').Iso Q' :=
      { φ := f'.φ
        ψ := f'.ψ
        left := f'.left
        right := f'.right
        equivariant := f'.equivariant
        level := fun a => by
          change Additive.ofMul (Additive.toMul (P.e.eta (a * u')) ≫ f'.φ.hom) = Q'.e.eta a
          rw [← hlev a]
          change Additive.ofMul ((Additive.toMul (Q'.e.eta a) ≫ f'.ψ.hom) ≫ f'.φ.hom) = _
          rw [Category.assoc, f'.right, Category.comp_id]
          rfl }
    have hm : Φ K (y ≫ (g t ≪≫ h u').hom) = M3.mk Q' := by
      rw [Iso.trans_hom, ← Category.assoc, hh, hg, hQ, M3.twist_mk]
      exact Quotient.sound ⟨iso⟩
    exact ⟨g t ≪≫ h u', ⟨(t, u'), ⟨ht, hu'U⟩, rfl⟩, (Φ K).injective (hQ'.trans hm.symm)⟩
  · rintro ⟨G', ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩, hy'⟩
    have hm : M3.mk Q' = M3.mk ((Q.twist t).rightMul u) := by
      rw [← hQ', hy', Iso.trans_hom, ← Category.assoc, hh, hg, hQ, M3.twist_mk]
      rfl
    obtain ⟨iso⟩ := Quotient.exact hm
    exact ⟨t, ⟨QML3.Iso.toQMIso iso.symm⟩⟩

end TwistOrbit

/-- **`TwistOrbitFinite` from R1hecke, the textbook leaf `TorsionStructure` (T5), `AutOInnerFinite`
(proved in mobius-glue) and `UnitLiftMod3` (proved).** -/
theorem twistOrbitFinite_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hH : R1heckeProps Y Φ) (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite)
    (hU : UnitLiftMod3) : TwistOrbitFinite Y Φ := by
  obtain ⟨hα, hu⟩ := hH
  choose g hg using hα
  choose h hh using hu
  obtain ⟨T, hTf, hTα⟩ := hA
  obtain ⟨U, hUf, hUu⟩ := unitReps
  exact ⟨_, (hTf.prod hUf).image (fun p => g p.1 ≪≫ h p.2),
    fun y y' Q Q' hQ hQ' => twist_iff_orbit Y Φ hT hU T hTα U hUu g hg h hh Qbar y y' Q Q' hQ hQ',
    fun y y' Q Q' hQ hQ' => twist_iff_orbit Y Φ hT hU T hTα U hUu g hg h hh ℂ y y' Q Q' hQ hQ'⟩

/-! ## `UnitLiftMod3` (proved by a finite computation) -/

/-- The reduced norm of `ofInt n` (`= nrd`, an integer). -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2

theorem nrdZ_mulCoord (n m : Fin 4 → ℤ) : nrdZ (LeafQM.mulCoord n m) = nrdZ n * nrdZ m := by
  simp [nrdZ, LeafQM.mulCoord]; ring

/-- Coordinates of the conjugate of `ofInt n`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : LeafQM.mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [LeafQM.mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : LeafQM.mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [LeafQM.mulCoord, conjC, nrdZ] <;> ring

/-- A unit of `𝒪` in each class of `(𝒪/3𝒪)^×` (`py/unit_table.py`; entry `c₀ + 3c₁ + 9c₂ + 27c₃`). -/
def unitTbl : Fin 81 → (Fin 4 → ℤ) :=
  ![![1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![-3, -2, 0, 0], ![1, 1, 0, 0], ![-1, 1, 0, 0], ![-3, -1, -3, -3], ![1, -1, 0, 0], ![-1, -1, 0, 0], ![0, 0, 1, 0], ![1, 0, 0, 0], ![-1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![-1, 1, 1, 0], ![0, -1, 1, 0], ![1, -1, 1, 0], ![-1, -1, 1, 0], ![0, 0, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, 0], ![-1, 1, -1, 0], ![0, -1, -1, 0], ![1, -1, -1, 0], ![-1, -1, -1, 0], ![-3, 0, 0, -2], ![1, 0, 0, 1], ![-1, 0, 0, 1], ![1, 0, 0, 0], ![-2, -2, 3, 1], ![-1, -2, 3, 1], ![-3, 2, 0, -2], ![1, -1, 0, 1], ![-1, -1, 0, 1], ![0, 0, 1, 1], ![1, 0, 1, 1], ![-1, 0, 1, 1], ![-3, -2, 1, 1], ![1, 0, 0, 0], ![-1, -2, -2, 1], ![0, -1, 1, 1], ![1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![1, 0, -1, 1], ![-1, 0, -1, 1], ![-3, -2, 2, 1], ![-2, -2, -1, 1], ![1, 0, 0, 0], ![0, -1, -1, 1], ![1, -1, -1, 1], ![-1, -1, -1, 1], ![-3, -3, -3, -1], ![1, 0, 0, -1], ![-1, 0, 0, -1], ![-3, -2, 0, 2], ![1, 1, 0, -1], ![-1, 1, 0, -1], ![1, 0, 0, 0], ![-2, -1, 3, -1], ![-1, -1, 3, -1], ![0, 0, 1, -1], ![1, 0, 1, -1], ![-1, 0, 1, -1], ![0, 1, 1, -1], ![1, 1, 1, -1], ![-1, 1, 1, -1], ![-3, -1, 1, -1], ![1, 0, 0, 0], ![-1, -1, -2, -1], ![0, 0, -1, -1], ![1, 0, -1, -1], ![-1, 0, -1, -1], ![0, 1, -1, -1], ![1, 1, -1, -1], ![-1, 1, -1, -1], ![-3, -1, 2, -1], ![-2, -1, -1, -1], ![1, 0, 0, 0]]

/-- The index of a class. -/
def encC (a b c d : ZMod 3) : Fin 81 :=
  ⟨a.val + 3 * b.val + 9 * c.val + 27 * d.val, by
    have ha : a.val < 3 := ZMod.val_lt a
    have hb : b.val < 3 := ZMod.val_lt b
    have hc : c.val < 3 := ZMod.val_lt c
    have hd : d.val < 3 := ZMod.val_lt d
    omega⟩

theorem unitTbl_spec : ∀ a b c d : ZMod 3, a ^ 2 + a * c + c ^ 2 - 2 * b ^ 2 - 2 * b * d - 2 * d ^ 2 ≠ 0 →
    (((unitTbl (encC a b c d) 0 : ℤ) : ZMod 3) = a ∧ ((unitTbl (encC a b c d) 1 : ℤ) : ZMod 3) = b ∧
      ((unitTbl (encC a b c d) 2 : ℤ) : ZMod 3) = c ∧ ((unitTbl (encC a b c d) 3 : ℤ) : ZMod 3) = d) ∧
    (nrdZ (unitTbl (encC a b c d)) = 1 ∨ nrdZ (unitTbl (encC a b c d)) = -1) := by
  set_option maxRecDepth 100000 in decide

/-- **`UnitLiftMod3` (proved).** -/
theorem unitLiftMod3_proof : UnitLiftMod3 := by
  rintro ⟨u₀, n, hn⟩ ⟨v₀, m, hm⟩ ⟨⟨c, k, hk⟩, hc⟩
  have hc' := congrArg Subtype.val hc
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] at hc'
  have h33 : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3
  rw [h33, hm, hn, hk, LeafQM.ofInt_mul, ← LeafQM.ofInt_one, LeafQM.AV.ofInt_sub,
    LeafQM.AV.three_mul_ofInt] at hc'
  have hco := LeafQM.AV.ofInt_injective hc'
  -- `nrd(u₀) ≢ 0 mod 3`
  have hmn : ∀ i, LeafQM.mulCoord m n i = ![1, 0, 0, 0] i + 3 * k i := fun i => by
    have := congrFun hco i
    simp only [Pi.sub_apply] at this
    linear_combination this
  have hn1 : ((nrdZ (LeafQM.mulCoord m n) : ℤ) : ZMod 3) = 1 := by
    have e : LeafQM.mulCoord m n = fun i => ![1, 0, 0, 0] i + 3 * k i := funext hmn
    rw [e]
    simp only [nrdZ]
    push_cast
    have h3 : (3 : ZMod 3) = 0 := rfl
    rw [h3]
    norm_num
  have hnrd : (nrdZ n : ZMod 3) ≠ 0 := by
    intro h0
    rw [nrdZ_mulCoord, Int.cast_mul, h0, mul_zero] at hn1
    exact zero_ne_one hn1
  obtain ⟨⟨t0, t1, t2, t3⟩, hpm⟩ := unitTbl_spec (n 0 : ZMod 3) (n 1 : ZMod 3) (n 2 : ZMod 3)
    (n 3 : ZMod 3) (by
      have : ((nrdZ n : ℤ) : ZMod 3) = (n 0 : ZMod 3) ^ 2 + (n 0 : ZMod 3) * (n 2 : ZMod 3) +
          (n 2 : ZMod 3) ^ 2 - 2 * (n 1 : ZMod 3) ^ 2 - 2 * (n 1 : ZMod 3) * (n 3 : ZMod 3) -
          2 * (n 3 : ZMod 3) ^ 2 := by simp [nrdZ]
      rw [← this]; exact hnrd)
  set t := unitTbl (encC (n 0 : ZMod 3) (n 1 : ZMod 3) (n 2 : ZMod 3) (n 3 : ZMod 3)) with htdef
  set ε := nrdZ t with hε
  have hεε : ε * ε = 1 := by rcases hpm with h | h <;> rw [h] <;> norm_num
  -- the unit `ofInt t`, with inverse `ε · conj`
  let x : LeafQM.O := ⟨LeafQM.ofInt t, t, rfl⟩
  let y : LeafQM.O := ⟨LeafQM.ofInt (ε • conjC t), ε • conjC t, rfl⟩
  have hxy : x * y = 1 := by
    apply Subtype.ext
    show LeafQM.ofInt t * LeafQM.ofInt (ε • conjC t) = 1
    rw [LeafQM.ofInt_mul, ← LeafQM.ofInt_one]
    congr 1
    funext i
    have := congrFun (mulCoord_conjC' t) i
    fin_cases i <;> simp [LeafQM.mulCoord, conjC] at this ⊢ <;>
      first | linear_combination ε * this | linear_combination ε * this + hεε
  have hyx : y * x = 1 := by
    apply Subtype.ext
    show LeafQM.ofInt (ε • conjC t) * LeafQM.ofInt t = 1
    rw [LeafQM.ofInt_mul, ← LeafQM.ofInt_one]
    congr 1
    funext i
    have := congrFun (mulCoord_conjC t) i
    fin_cases i <;> simp [LeafQM.mulCoord, conjC] at this ⊢ <;>
      first | linear_combination ε * this | linear_combination ε * this + hεε
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  -- the congruence
  have hdiv : ∀ i, ∃ q : ℤ, t i - n i = 3 * q := by
    intro i
    have hti : ((t i : ℤ) : ZMod 3) = (n i : ZMod 3) := by
      fin_cases i
      · exact t0
      · exact t1
      · exact t2
      · exact t3
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp hti.symm
    exact ⟨q, by push_cast at hq; linear_combination hq⟩
  choose q hq using hdiv
  refine ⟨⟨LeafQM.ofInt q, q, rfl⟩, Subtype.ext ?_⟩
  show LeafQM.ofInt t - u₀ = ((3 : LeafQM.O) : LeafQM.B) * LeafQM.ofInt q
  rw [h33, hn, LeafQM.AV.ofInt_sub, LeafQM.AV.three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact hq i

/-- **`TwistOrbitFinite` from R1hecke, `TorsionStructure` and `AutOInnerFinite` (proved).** -/
theorem twistOrbitFinite_of' (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hH : R1heckeProps Y Φ) (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) :
    TwistOrbitFinite Y Φ :=
  twistOrbitFinite_of Y Φ hH hT hA unitLiftMod3_proof

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.piTwistC_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.fibreTransferC_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.unitLiftMod3_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.twistOrbitFinite_of

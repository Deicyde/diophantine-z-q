import ZInQKernel.Contrib.OneProof.H.TailZ22

/-! # gt-elkies: `ElkiesEquationsX6Ab` from Elkies' theorem on `X*(6) = X₆/W` in printed form

Task gt-elkies (docs/research/gt-elkies.md). The open research field `elkiesEquationsX6Ab`
(`HDec.QMSplit.Moduli.ElkiesEquationsX6Ab`, TailZ22) counted GLUE under the strict rule because its fibre clause
"`t(x) = t(x')` iff the QM pairs are isomorphic up to a twist by `α ∈ Aut 𝒪`" combines two things:
* Elkies' theorem: `t` is a coordinate on the Atkin–Lehner quotient `X*(6) = X₆/W`, `W = {1, w₂, w₃, w₆}`, with the
  charts `s² = −t`, `r² = 3(t − 1)` and the CM values `t = 0, 1, ∞` at discriminants `−24, −4, −3`;
* the moduli meaning of `W`: the Atkin–Lehner involutions act on QM pairs by twisting the `𝒪`-action.

Here:
1. `IsAtkinLehner X Ψ k g` / `atkinLehnerW X Ψ` define the Atkin–Lehner group of the coarse witness `X₆` by its
   moduli action: `w_m` (`m = 1, 2, 3, 6` for `k = 0, 1, 2, 3`) sends the class of `(A, ι)` to the class of
   `(A, ι ∘ Ad μ_m)`, `μ_m = 1, i, j, ij` (the chain's `HDec.LeafQM.AV.Pin.Exact.tt`, `rep`).
2. `ElkiesX6StarPrinted` is Elkies' theorem on that witness: the fibres of `t` on `X₆(ℚ̄)` are the `W`-orbits
   (the `ℚ̄`-point form of "`t` is a coordinate on `X₆/W`"), the three CM values, and the charts
   (`X6Glue.ElkiesCharts`, unchanged from the field).
3. `orbit_iff_twist` (the moduli step, proved): two `ℚ̄`-points are in one `W`-orbit iff their QM pairs are
   isomorphic up to a twist by some `α ∈ Aut 𝒪`. It uses only the clause list `X6Props` (`Ψ` bijective, each twist
   induced by an automorphism of `X`), the chain's computation `Aut 𝒪 = Inn(𝒪^×)·{Ad 1, Ad i, Ad j, Ad ij}`
   (`HDec.LeafQM.AV.Pin.Exact.rep_cover`, from Skolem–Noether T13 and the normalizer descent) and the chain's
   `HDec.G0ModField.innerIso` (an inner twist is isomorphic to the untwisted pair).
4. `elkiesEquationsX6Ab_of_printed : ElkiesX6StarPrinted → ElkiesEquationsX6Ab`, and the converse
   (`elkiesX6StarPrinted_of_ab`), so the new leaf is equivalent to the field it replaces, not stronger. -/

namespace HDec.QMSplit.Moduli.ElkiesX6Star

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

/-- **The Atkin–Lehner involution `w_m` of `X₆`, by its moduli action** (`m = 1, 2, 3, 6` for `k = 0, 1, 2, 3`):
an automorphism `g` of the coarse witness `X` over `ℚ` such that on `ℚ̄`-points `g` sends the class of a QM pair
`(A, ι)` to the class of `(A, ι ∘ Ad μ_m)`, where `μ_m = 1, i, j, ij ∈ 𝒪` (reduced norms `1, −2, 3, −6`) are the
chain's representatives `HDec.LeafQM.AV.Pin.Exact.tt` of `N_B(𝒪)/ℚ^×𝒪^×` and `rep k = Ad μ_m`.

Definition (STANDARD; e.g. Rotger, Trans. AMS 356 (2004), and Baba–Granath, Canad. J. Math. 60 (2008) §2, locators
UNVERIFIED): `w_m(A, ι) = (A/A[I_m], ι_m)`, `I_m` the two-sided ideal of `𝒪` of reduced norm `m`. For `D = 6`,
`I_m = μ_m 𝒪` is principal, `A[I_m] = ker ι(μ_m)`, and `ι(μ_m) : A/A[I_m] ≅ A` carries `ι_m` to `ι ∘ Ad μ_m`
(`Ad μ_m = Ad μ_m⁻¹` since `μ_m² ∈ ℚ^×`), which is the clause below. -/
def IsAtkinLehner (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (k : Fin 4) (g : X ≅ X) : Prop :=
  ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
    Ψ (x ≫ g.hom) = Quotient.mk _ (P.twist (_root_.HDec.LeafQM.AV.Pin.Exact.rep k))

/-- **The Atkin–Lehner group `W = {1, w₂, w₃, w₆}` of `X₆`** (as a set of automorphisms of `X` over `ℚ`, each
acting on moduli as `IsAtkinLehner`). -/
def atkinLehnerW (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Set (X ≅ X) :=
  {g | ∃ k : Fin 4, IsAtkinLehner X Ψ k g}

/-- **LEAF (Elkies, *Shimura curve computations*, Algorithmic Number Theory (ANTS-III, Portland 1998), LNCS 1423,
pp. 1–47, §3 on `X*(6)`; section number, display and the `0/∞` orientation UNVERIFIED, recalled without a
source).** On some witness of the moduli clause lists (the canonical `Y₃` with `R1fpPropsAb`, and
`X₆ = X₀(6, 1)` with its moduli bijection `Ψ`, `X6Props`), Elkies' coordinate `t` on `X*(6) = X₆/W` satisfies:
* **`t` is a coordinate on `X₆/W`**, in its `ℚ̄`-point form: `t(x) = t(x')` iff `x' = w(x)` for some
  `w ∈ W = {1, w₂, w₃, w₆}` (`atkinLehnerW`). This is a consequence of the printed `X*(6) := X(6)/W ≅ P¹_t`: the
  `ℚ̄`-points of the quotient of a curve by a finite group are the orbits (SGA 1 V.1, Mumford, *Abelian
  varieties* §7; STANDARD, locators UNVERIFIED);
* **the CM values** `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3` (the elliptic points of orders
  2, 4, 6 of the `(2, 4, 6)` triangle group);
* **the equations** `X₆ = X*(6)(√−t, √(3(t − 1)))` as the curve over the `t`-line in its two charts
  (`X6Glue.ElkiesCharts X t`, the same clause as in the field `ElkiesEquationsX6Ab`; Elkies prints the function
  field, `ElkiesCharts` is its smooth projective model, see `ElkiesEquationsX6`'s docstring).
Never stronger than the printed statement: each clause is the printed statement on the canonical model or its
`ℚ̄`-point consequence. -/
def ElkiesX6StarPrinted : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ x x' : fieldPt Qbar ⟶ X,
      t.val (K := Qbar) x.left = t.val (K := Qbar) x'.left ↔ ∃ g ∈ atkinLehnerW X Ψ, x ≫ g.hom = x') ∧
    (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    X6Glue.ElkiesCharts X t

section Moduli

variable {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {X : Over (Spec (CommRingCat.of ℚ))}
  {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}

/-- Every twist is, up to an inner twist by a unit of `𝒪`, one of the four Atkin–Lehner twists:
`QMIso (q.twist (rep k)) (q.twist α)` for some `k` (from `rep_cover` and `innerIso`). -/
theorem exists_rep_iso {K : Type} [Field K] {A : PkgI3.AbVar K} (q : QMStr A)
    (α : _root_.LeafQM.O ≃+* _root_.LeafQM.O) :
    ∃ k : Fin 4, Nonempty (QMIso (q.twist (_root_.HDec.LeafQM.AV.Pin.Exact.rep k)) (q.twist α)) := by
  obtain ⟨k, v, hv⟩ := _root_.HDec.LeafQM.AV.Pin.Exact.rep_cover α
  set w := _root_.HDec.LeafQM.AV.Pin.Exact.rep k
  let u : (_root_.LeafQM.O)ˣ :=
    ⟨w.symm (v : _root_.LeafQM.O), w.symm ((v⁻¹ : (_root_.LeafQM.O)ˣ) : _root_.LeafQM.O),
      by rw [← map_mul, Units.mul_inv, map_one], by rw [← map_mul, Units.inv_mul, map_one]⟩
  have hα : ∀ a, α a = w (u * a * ↑u⁻¹) := fun a => by
    change α a = w (w.symm (v : _root_.LeafQM.O) * a * w.symm ((v⁻¹ : (_root_.LeafQM.O)ˣ) : _root_.LeafQM.O))
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hv a]
  exact ⟨k, ⟨(_root_.HDec.G0ModField.innerIso q w u α hα).symm⟩⟩

/-- **The moduli step (proved).** Two `ℚ̄`-points of `X₆` are in one orbit of the Atkin–Lehner group `W` iff their
QM pairs are isomorphic up to a twist by an automorphism of `𝒪`. -/
theorem orbit_iff_twist (h6 : X6Props Y Φ X Ψ fY) (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar)
    (hP : Ψ x = Quotient.mk _ P) (hQ : Ψ x' = Quotient.mk _ Q) :
    (∃ g ∈ atkinLehnerW X Ψ, x ≫ g.hom = x') ↔
      ∃ α : _root_.LeafQM.O ≃+* _root_.LeafQM.O, Nonempty (QMIso (P.q.twist α) Q.q) := by
  constructor
  · rintro ⟨g, ⟨k, hk⟩, rfl⟩
    refine ⟨_root_.HDec.LeafQM.AV.Pin.Exact.rep k, ?_⟩
    have := (hk x P hP).symm.trans hQ
    exact Quotient.exact this
  · rintro ⟨α, ⟨e⟩⟩
    obtain ⟨k, ⟨e'⟩⟩ := exists_rep_iso P.q α
    obtain ⟨g, hg⟩ := h6.2.2.2.2.1 (_root_.HDec.LeafQM.AV.Pin.Exact.rep k)
    refine ⟨g, ⟨k, hg⟩, Ψ.injective ?_⟩
    rw [hg x P hP, hQ]
    exact Quotient.sound ⟨e'.trans e⟩

end Moduli

/-- **`ElkiesEquationsX6Ab` from Elkies' theorem in printed form** (gt-elkies): the fibre clause is
`ElkiesX6StarPrinted`'s orbit clause through the moduli step `orbit_iff_twist`; the CM and chart clauses are
`ElkiesX6StarPrinted`'s. -/
theorem elkiesEquationsX6Ab_of_printed (h : ElkiesX6StarPrinted) : ElkiesEquationsX6Ab := by
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hfib, hcm, hc⟩ := h
  refine ⟨Y, Φ, X, Ψ, fY, t, h1, h6, fun x x' P Q hP hQ => ⟨?_, hcm x P hP⟩, hc⟩
  exact (hfib x x').trans (orbit_iff_twist h6 x x' P Q hP hQ)

/-- **The converse: the new leaf is not stronger than the field.** `ElkiesEquationsX6Ab` gives
`ElkiesX6StarPrinted` on the same witness (`Ψ` is onto the classes, and `orbit_iff_twist`). -/
theorem elkiesX6StarPrinted_of_ab (h : ElkiesEquationsX6Ab) : ElkiesX6StarPrinted := by
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hcl, hc⟩ := h
  refine ⟨Y, Φ, X, Ψ, fY, t, h1, h6, fun x x' => ?_, fun x P hP => (hcl x x P P hP hP).2, hc⟩
  have hx : Ψ x = Quotient.mk _ (Ψ x).out := (Quotient.out_eq _).symm
  have hx' : Ψ x' = Quotient.mk _ (Ψ x').out := (Quotient.out_eq _).symm
  exact ((hcl x x' _ _ hx hx').1).trans (orbit_iff_twist h6 x x' _ _ hx hx').symm

theorem elkiesX6StarPrinted_iff : ElkiesX6StarPrinted ↔ ElkiesEquationsX6Ab :=
  ⟨elkiesEquationsX6Ab_of_printed, elkiesX6StarPrinted_of_ab⟩

end HDec.QMSplit.Moduli.ElkiesX6Star

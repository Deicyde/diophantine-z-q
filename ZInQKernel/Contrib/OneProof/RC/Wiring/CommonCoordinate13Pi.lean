import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Local
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer

/-!
# The singular quotient of a change of local conditions is the sum over the places

Manuscript `diophantine_zq.tex`, the change of local conditions after the support change
(tex 3489–3498):

> Replacing the unramified condition by the full condition then gives the singular quotient by a
> cone of Selmer cones. In particular the old complex is an actual subcomplex of an upper
> triangular model, not just a complex with the same Euler characteristic.

and the two conjugate places `w`, `w̄` above an unused split prime in the support triangle of
Lemma `ex:arith-common-coordinate` (tex 4176–4184), where the quotient determinant
`δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q)` is a product over the two places. The local conditions
of a Selmer complex form the product `piCx` over the places, so a change of local conditions is a
family of split inclusions, one at each place, and its singular quotient is the sum over the
places of the local singular quotients. The index type of the places is arbitrary; only the
extraction of two places uses decidable equality on it.

* `piSplit`: the product of a family of split inclusions `E v : A v ⊂ B v`, with inclusion
  `piMap (E v).i` and complements `∏_v Q_vⁿ` (`Submodule.pi`). Injectivity and the complement
  property are componentwise (`piMap_f_injective`, `isCompl_range_piMap`): every element splits
  componentwise, and an element of the range and of `∏_v Q_vⁿ` lies componentwise in
  `im i_vⁿ ⊓ Q_vⁿ = 0`. `mem_piSplit_Qc`: membership in the complement is componentwise.
* `piSplit_coordQ`, `piSplit_dQ`: the quotient coordinate and the quotient differential of
  `piSplit E` are componentwise. Hence `piSplit_quotEquiv`, `piSplit_quotEquiv_d`: the quotient
  complex of `piSplit E` is degreewise the product of the local quotient complexes, compatibly
  with the differentials (`piSplit_quotEquiv_apply`: it reads off the components).
* `piExtract`, `piExtract_d`: if the components away from two distinct places `v₁`, `v₂` are
  degreewise subsingleton, the product is degreewise `A v₁ ⊕ A v₂` (`x ↦ (x v₁, x v₂)`, with
  inverse `(y₁, y₂) ↦ Pi.single v₁ y₁ + Pi.single v₂ y₂`), compatibly with the differentials.
* `piRetractOfTwo`: a retract of `A v₁ ⊕ A v₂` onto `Y` gives a retract of the product onto `Y`
  (`GRetract.ofEquiv` along `piExtract`). `piSplitRetractOfTwo`: if the local quotients vanish
  away from `v₁`, `v₂`, a retract of `Q_{v₁} ⊕ Q_{v₂}` onto `Y` gives a retract of the singular
  quotient of `piSplit E` onto `Y`. `subsingleton_quotientCx_of_Qc_eq_bot`: a vanishing
  complement (an unchanged local condition) gives a vanishing local quotient.
* `piSplitRetractProd`, `piSplitTwoSingRetract`: with `GRetract.prodR`, local retracts of the
  two quotients onto `Y₁`, `Y₂` give a retract of the singular quotient of `piSplit E` onto
  `Y₁ ⊕ Y₂`; for the singular blocks at the two conjugate places the target is
  `twoSingCx Fr q z z⁻¹`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.SelmerComplex (piCx piMap)
open ZInQ.Manuscript.RC.Local (prodGCx)

variable {S : Type} [CommRing S]

/-! ### The product of a family of split inclusions -/

section PiSplit

variable {ι : Type} {A B : ι → GCx S}

/-- **The product of injective chain maps is injective** in every degree (tex 3489–3498,
4176–4184): `(x_v)_v ↦ (f_v x_v)_v` is injective when every `f_v` is. Kind: PROVED. -/
theorem piMap_f_injective (f : ∀ v, GHom (A v) (B v))
    (hf : ∀ v n, Function.Injective ((f v).f n n rfl)) (n : ℤ) :
    Function.Injective ((piMap f).f n n rfl) := fun _ _ hxy =>
  funext fun v => hf v n (congrFun hxy v)

variable (E : ∀ v, SplitInclusion (A v) (B v))

/-- **The complements of a product of split inclusions** (tex 3489–3498, 4176–4184): the product
`∏_v Q_vⁿ` of the complements is a complement of the range of the product inclusion. Every
element splits componentwise, `x_v = i_v (coordP x_v) + coordQ x_v`, and an element of the range
and of `∏_v Q_vⁿ` lies componentwise in `im i_vⁿ ⊓ Q_vⁿ = 0`; no finiteness of the index type is
used. Kind: PROVED. -/
theorem isCompl_range_piMap (n : ℤ) :
    IsCompl (LinearMap.range ((piMap fun v => (E v).i).f n n rfl))
      (Submodule.pi Set.univ fun v => (E v).Qc n) := by
  refine ⟨Submodule.disjoint_def.2 fun x hx hq => ?_,
    Submodule.codisjoint_iff_exists_add_eq.2 fun x => ?_⟩
  · obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hx
    funext v
    exact Submodule.disjoint_def.1 ((E v).compl n).disjoint _ (LinearMap.mem_range_self _ (u v))
      (Submodule.mem_pi.1 hq v (Set.mem_univ v))
  · refine ⟨(piMap fun v => (E v).i).f n n rfl (fun v => (E v).coordP n (x v) : ∀ v, (A v).X n),
      (fun v => ((E v).coordQ n (x v) : (B v).X n) : ∀ v, (B v).X n),
      LinearMap.mem_range_self _ _, Submodule.mem_pi.2 fun v _ => ((E v).coordQ n (x v)).2, ?_⟩
    funext v
    exact (E v).decompose n (x v)

/-- **The product of a family of split inclusions** (tex 3489–3498, 4176–4184: the local
conditions are a product over the places): the product inclusion `piMap (E v).i` of `∏_v A v`
into `∏_v B v`, with complements `∏_v Q_vⁿ`. No finiteness of the index type is assumed.
Kind: definition. -/
def piSplit : SplitInclusion (piCx A) (piCx B) where
  i := piMap fun v => (E v).i
  inj := piMap_f_injective (fun v => (E v).i) fun v => (E v).inj
  Qc n := Submodule.pi Set.univ fun v => (E v).Qc n
  compl := isCompl_range_piMap E

/-- The inclusion of the product of split inclusions is componentwise (tex 3489–3498,
4176–4184); this holds by definition. Kind: PROVED. -/
theorem piSplit_i_f_apply (n : ℤ) (x : (piCx A).X n) (v : ι) :
    (piSplit E).i.f n n rfl x v = (E v).i.f n n rfl (x v) :=
  rfl

/-- **Membership in the complement of the product is componentwise** (tex 3489–3498,
4176–4184): `x ∈ ∏_v Q_vⁿ` if and only if `x_v ∈ Q_vⁿ` for every place `v`. Kind: PROVED. -/
theorem mem_piSplit_Qc (n : ℤ) (x : (piCx B).X n) :
    x ∈ (piSplit E).Qc n ↔ ∀ v, x v ∈ (E v).Qc n :=
  Submodule.mem_pi.trans ⟨fun h v => h v (Set.mem_univ v), fun h v _ => h v⟩

/-- **The quotient coordinate of the product is componentwise** (tex 3489–3498, 4176–4184):
`coordQ (x_v)_v = (coordQ_v x_v)_v`. Kind: PROVED. -/
theorem piSplit_coordQ (n : ℤ) (x : (piCx B).X n) :
    (((piSplit E).coordQ n x : (piSplit E).Qc n) : (piCx B).X n) =
      (fun v => ((E v).coordQ n (x v) : (B v).X n) : ∀ v, (B v).X n) :=
  congrArg Subtype.val (coordQ_eq_of_add (piSplit E) n x
    (fun v => (E v).coordP n (x v) : ∀ v, (A v).X n)
    ⟨fun v => ((E v).coordQ n (x v) : (B v).X n),
      (mem_piSplit_Qc E n _).2 fun v => ((E v).coordQ n (x v)).2⟩
    (funext fun v => (E v).decompose n (x v)))

/-- **The quotient differential of the product is componentwise** (tex 3489–3498, 4176–4184):
`d_Q (q_v)_v = (d_{Q_v} q_v)_v`. Kind: PROVED. -/
theorem piSplit_dQ (a b : ℤ) (h : a + 1 = b) (z : (piSplit E).Qc a) :
    (((piSplit E).dQ a b h z : (piSplit E).Qc b) : (piCx B).X b) =
      (fun v => ((E v).dQ a b h ⟨z.1 v, (mem_piSplit_Qc E a z.1).1 z.2 v⟩ : (B v).X b) :
        ∀ v, (B v).X b) :=
  piSplit_coordQ E b _

/-- **The quotient complex of the product is the product of the quotient complexes**,
degreewise (tex 3489–3498, 4176–4184): the complement `∏_v Q_vⁿ` of the product, with its
quotient differential, is the product of the local quotient complexes; `q ↦ (q_v)_v`.
Kind: definition. -/
def piSplit_quotEquiv (n : ℤ) :
    (piSplit E).quotientCx.X n ≃ₗ[S] (piCx fun v => (E v).quotientCx).X n where
  toFun z v := ⟨z.1 v, (mem_piSplit_Qc E n z.1).1 z.2 v⟩
  invFun y := ⟨fun v => (y v).1, (mem_piSplit_Qc E n _).2 fun v => (y v).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The degreewise equivalence reads off the components (tex 3489–3498, 4176–4184); this holds
by definition. Kind: PROVED. -/
theorem piSplit_quotEquiv_apply (n : ℤ) (z : (piSplit E).quotientCx.X n) (v : ι) :
    (piSplit_quotEquiv E n z v).1 = z.1 v :=
  rfl

/-- **The degreewise equivalence commutes with the differentials** (tex 3489–3498, 4176–4184):
the quotient differential of the product is the product of the local quotient differentials
(`piSplit_dQ`). Kind: PROVED. -/
theorem piSplit_quotEquiv_d (a b : ℤ) (h : a + 1 = b) (z : (piSplit E).quotientCx.X a) :
    (piCx fun v => (E v).quotientCx).d a b h (piSplit_quotEquiv E a z) =
      piSplit_quotEquiv E b ((piSplit E).quotientCx.d a b h z) := by
  funext v
  exact Subtype.ext (congrFun (piSplit_dQ E a b h z) v).symm

end PiSplit

/-! ### Two places -/

section Extract

variable {ι : Type} [DecidableEq ι] {A : ι → GCx S} {v₁ v₂ : ι} (hne : v₁ ≠ v₂)
  (hsub : ∀ v n, v ≠ v₁ → v ≠ v₂ → Subsingleton ((A v).X n))

/-- **The product over the places is the sum over two places** when the components at all the
other places vanish (tex 3489–3498, 4176–4184: the two conjugate places `w`, `w̄`): for distinct
`v₁`, `v₂` and degreewise subsingleton components away from them, `x ↦ (x v₁, x v₂)` is a linear
equivalence `∏_v A_vⁿ ≃ A_{v₁}ⁿ ⊕ A_{v₂}ⁿ`, with inverse
`(y₁, y₂) ↦ Pi.single v₁ y₁ + Pi.single v₂ y₂`. Kind: definition. -/
def piExtract (n : ℤ) : (piCx A).X n ≃ₗ[S] (prodGCx (A v₁) (A v₂)).X n where
  toFun x := ((x v₁, x v₂) : (A v₁).X n × (A v₂).X n)
  invFun y := (Pi.single v₁ y.1 : ∀ v, (A v).X n) + (Pi.single v₂ y.2 : ∀ v, (A v).X n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext v
    change (Pi.single v₁ (x v₁) : ∀ v, (A v).X n) v + (Pi.single v₂ (x v₂) : ∀ v, (A v).X n) v =
      x v
    by_cases h₁ : v = v₁
    · subst h₁
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, add_zero]
    · by_cases h₂ : v = v₂
      · subst h₂
        rw [Pi.single_eq_of_ne h₁, Pi.single_eq_same, zero_add]
      · have := hsub v n h₁ h₂
        exact Subsingleton.elim _ _
  right_inv y := by
    obtain ⟨y₁, y₂⟩ := y
    change ((Pi.single v₁ y₁ : ∀ v, (A v).X n) v₁ + (Pi.single v₂ y₂ : ∀ v, (A v).X n) v₁,
      (Pi.single v₁ y₁ : ∀ v, (A v).X n) v₂ + (Pi.single v₂ y₂ : ∀ v, (A v).X n) v₂) = (y₁, y₂)
    rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hne,
      Pi.single_eq_of_ne hne.symm, add_zero, zero_add]

/-- The extraction of two places reads off the two components (tex 3489–3498, 4176–4184); this
holds by definition. Kind: PROVED. -/
theorem piExtract_apply (n : ℤ) (x : (piCx A).X n) :
    piExtract hne hsub n x = ((x v₁, x v₂) : (A v₁).X n × (A v₂).X n) :=
  rfl

/-- **The extraction of two places commutes with the differentials** (tex 3489–3498,
4176–4184): both differentials are componentwise. Kind: PROVED. -/
theorem piExtract_d (a b : ℤ) (h : a + 1 = b) (x : (piCx A).X a) :
    (prodGCx (A v₁) (A v₂)).d a b h (piExtract hne hsub a x) =
      piExtract hne hsub b ((piCx A).d a b h x) :=
  rfl

/-- **A retract of the sum over two places is a retract of the product over all places**
(tex 3489–3498, 4176–4184): when the components away from `v₁ ≠ v₂` are degreewise
subsingleton, a normalized graded deformation retract of `A v₁ ⊕ A v₂` onto `Y` transports along
`piExtract` (`GRetract.ofEquiv`) to a retract of `∏_v A v` onto `Y`. Kind: definition. -/
def piRetractOfTwo {Y : GCx S} (R : GRetract (prodGCx (A v₁) (A v₂)) Y) :
    GRetract (piCx A) Y :=
  R.ofEquiv (fun n => (piExtract hne hsub n).symm)
    (fun a b h x => (equiv_symm_d (piExtract hne hsub) (piExtract_d hne hsub) a b h x).symm)

end Extract

/-! ### The singular quotient from two places -/

/-- **A vanishing complement gives a vanishing quotient** (tex 3489–3498, 4176–4184: at a place
where the local condition is not changed the local singular quotient vanishes): if `Qⁿ = 0`,
the quotient complex is subsingleton in degree `n`. Kind: PROVED. -/
theorem subsingleton_quotientCx_of_Qc_eq_bot {CP CR : GCx S} (E : SplitInclusion CP CR)
    (n : ℤ) (h : E.Qc n = ⊥) : Subsingleton (E.quotientCx.X n) := by
  change Subsingleton (E.Qc n)
  rw [h]
  infer_instance

/-- **The retract of the singular quotient from the two places** (tex 3489–3498, 4176–4184): for
a family of split inclusions `E` whose local quotient complexes are degreewise subsingleton away
from two distinct places `v₁`, `v₂`, a retract of `Q_{v₁} ⊕ Q_{v₂}` onto `Y` gives a retract of
the quotient complex of `piSplit E` onto `Y`: `piRetractOfTwo` for the product of the local
quotient complexes, transported along `piSplit_quotEquiv` (`GRetract.ofEquiv`).
Kind: definition. -/
def piSplitRetractOfTwo {ι : Type} [DecidableEq ι] {A B : ι → GCx S}
    (E : ∀ v, SplitInclusion (A v) (B v)) {v₁ v₂ : ι} (hne : v₁ ≠ v₂)
    (hsub : ∀ v n, v ≠ v₁ → v ≠ v₂ → Subsingleton ((E v).quotientCx.X n)) {Y : GCx S}
    (R : GRetract (prodGCx (E v₁).quotientCx (E v₂).quotientCx) Y) :
    GRetract (piSplit E).quotientCx Y :=
  (piRetractOfTwo (A := fun v => (E v).quotientCx) hne hsub R).ofEquiv
    (fun n => (piSplit_quotEquiv E n).symm)
    (fun a b h x => (equiv_symm_d (piSplit_quotEquiv E) (piSplit_quotEquiv_d E) a b h x).symm)

/-- **The retract of the singular quotient onto the sum of two local models** (tex 3489–3498,
4176–4184): when the local quotients are degreewise subsingleton away from `v₁ ≠ v₂`, local
retracts of `Q_{v₁}` onto `Y₁` and of `Q_{v₂}` onto `Y₂` give a retract of the quotient complex
of `piSplit E` onto `Y₁ ⊕ Y₂` (`GRetract.prodR`, then `piSplitRetractOfTwo`).
Kind: definition. -/
def piSplitRetractProd {ι : Type} [DecidableEq ι] {A B : ι → GCx S}
    (E : ∀ v, SplitInclusion (A v) (B v)) {v₁ v₂ : ι} (hne : v₁ ≠ v₂)
    (hsub : ∀ v n, v ≠ v₁ → v ≠ v₂ → Subsingleton ((E v).quotientCx.X n)) {Y₁ Y₂ : GCx S}
    (RQ₁ : GRetract (E v₁).quotientCx Y₁) (RQ₂ : GRetract (E v₂).quotientCx Y₂) :
    GRetract (piSplit E).quotientCx (prodGCx Y₁ Y₂) :=
  piSplitRetractOfTwo E hne hsub (GRetract.prodR RQ₁ RQ₂)

section TwoSing

open ZInQ.Manuscript.RC.Local (singCx twoSingCx)

/-- **The retract of the singular quotient onto the two singular blocks** (tex 3489–3498,
4176–4184): when the local quotients are degreewise subsingleton away from the two conjugate
places `v₁ = w`, `v₂ = w̄`, local retracts of the quotients at `w` and `w̄` onto
`[M --zFr−q--> M]` and `[M --z⁻¹Fr−q--> M]` give a retract of the quotient complex of
`piSplit E` onto `twoSingCx Fr q z z⁻¹` (`twoSingCx_eq_prodGCx`, `piSplitRetractProd`).
Kind: definition. -/
def piSplitTwoSingRetract {ι : Type} [DecidableEq ι] {A B : ι → GCx S}
    (E : ∀ v, SplitInclusion (A v) (B v)) {v₁ v₂ : ι} (hne : v₁ ≠ v₂)
    (hsub : ∀ v n, v ≠ v₁ → v ≠ v₂ → Subsingleton ((E v).quotientCx.X n))
    (Fr : Matrix (Fin 2) (Fin 2) S) (q : ℕ) (z zi : S)
    (RQ₁ : GRetract (E v₁).quotientCx (singCx (Matrix.toLin' (z • Fr)) q))
    (RQ₂ : GRetract (E v₂).quotientCx (singCx (Matrix.toLin' (zi • Fr)) q)) :
    GRetract (piSplit E).quotientCx (twoSingCx Fr q z zi) :=
  piSplitRetractProd E hne hsub RQ₁ RQ₂

end TwoSing

end ZInQ.Manuscript.RC.Wiring

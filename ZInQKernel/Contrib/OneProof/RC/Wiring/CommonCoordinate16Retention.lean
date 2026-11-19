import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15PresS
import ZInQKernel.Contrib.OneProof.RC.Wiring.RetentionGenuineFunctionals

/-!
# Lane RC30's naturality at the switches of the presentation, at a coefficient stage ring

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate`, tex 4157–4175:
`i : C_P → C_R` is the primitive-to-relaxed map, `j : C_S → C_{P⊥}` the paired strict-to-primitive
map; all old orthogonal conditions and their homotopies are retained; at `q` these are the maps
from the unramified condition to the full condition and from zero to the unramified condition;
naturality of the cup pairing (Nekovář 6.4.1–6.4.3) and the paired strict lift give
`λ_R ∘ i = e_q λ_P`. The switch is the actual support comparison of tex 3489–3498 ("replacing the
unramified condition by the full condition").

**Reading of the switch in lane RC30's data (a).** Lane RC30's
`PlaceRetentionG DR DPp fP fS Lq Uq ιq` has ONE new place `q`; the switch `suppSwitchS T p` changes
the conditions at the TWO places `w = (p, false)`, `w̄ = (p, true)` above the prime `p` at once
(both carry `decide (p ∈ T)`). The new place `q` of lane RC30 is read as the prime `p` with its two
places together:
`L_q = C^•(G_{K_w}, M) ⊕ C^•(G_{K_w̄}, M)` (`switchLq`, `prodGCx` of the two genuine local
complexes), `U_q = [W_w → W_w] ⊕ [W_w̄ → W_w̄]` (`switchUq`, `prodGCx` of the two genuine
unramified complexes) and `ι_q = EU_w.i ⊕ EU_w̄.i` (`switchιq`, `prodGHom` of the chosen split
inflations). Reasons: the text's `q` is a prime with ONE point factor `e_q = a_q − z − z⁻¹` and one
paired strict lift `j z_S = e_q z_{P⊥}` for both places (tex 4158, 4169–4174); a condition switched
at one place only is not a support complex of the presentation, so two successive one-place
switches would leave the presentation and produce two factors instead of `e_q`; the quotient of the
switch is the sum of the two local quotients (`suppQuotEquivS`), i.e. `L_q / U_q` in this reading;
and it is the reading of the earlier two-place step (`genuineL2`, `genuineU2`, `prodGHom`).

**The primitive data (b).** `DR = suppDataS (insert p T)`, `f_P = switchFP T p` (the product of the
local switches `presSplitS T p v`), `switchPrim T p = selRestrict DR f_P`. Its terms are those of
`C_T` by definition (`switchPrim_X`), its differentials agree (`switchPrim_d`), the Selmer data are
equal (`switchPrim_eq`), lane RC26's identity isomorphism `switchPrimIso` is compatible with the
maps (`switchPrimIso_comm`), and `changeMap DR f_P` is `suppInclS T p` on elements
(`switchChange_f`, by definition).

**What pins the components now (c, d).** In `SwitchRetentionInputs.toPlaceRetentionG`:
* definitions from the presentation: `Lq`, `Uq`, `ιq` (above); `qR = switchQR T p`, the components
  at `w`, `w̄` of the relaxed condition map `ι_R` (a chain map `switchQRHom`; by `switchQR_eq_cast`
  the projection of `U_{T ∪ {p}}` onto its two components above `p`, the relaxed conditions there
  being the full ones); `qP = switchQP T p hp`, the projection of `U_T` onto its two components
  above `p`, identified with the genuine unramified conditions (`condToUrS`; `switchQP_eq_cast`);
  the index type `ι` (the places of the presentation), `Uo` (the relaxed conditions), `pR` (the
  projections), `pP` (the local switches after the projections; the identity on every old summand,
  `switchPP_old`), `hR`, `hP` (the sums of the old homotopies, plus `hq` for `hP`);
* PROVED from the presentation: `q_P` (`switchQ_P`), `ret_P`, `hR_eq`, `hP_eq` (by definition);
* inputs (`SwitchRetentionInputs`): the orthogonal data `DPp`, `US`, `fS` (parameters); at `q` the
  orthogonal condition `Uq'`, its component `qPp`, the homotopy `hq` and `q_S`; the cup products
  `E`, `EL`, `resE`, `cupG`, `cupL`, `compat`; the old places `old` (avoiding `w`, `w̄`), the old
  orthogonal conditions `Uo'`, homotopies `hv`, components `pS`, `pPp` and `ret_S`; the isotropy
  identities `isoR`, `isoP`.

**`switch_natural`**: for every cocycle `w ∈ C_T²`, `λ_R(suppInclS T p w) = e · λ_P(w)` (lane RC30's
`PlaceRetentionG.pairedFunctional_natural`, transported along (b)); `switch_natural_switch` (the
same for the inclusion of `suppSwitchS T p`), `switch_hlamR` (the relation `lam ∘ Sum.inl = ψ e •
lam_P` of lane RC31's `KmStep`), `nonempty_switchRetentionInputs` (consistency: zero targets).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom ghomComp changeMap zeroGHom GHom.toCC)
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (pairedFun)
open ZInQ.Manuscript.RC.Local (prodGCx)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### Identifications of the condition at a new place -/

section NewPlace

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {ι : Type} (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))

/-- **An unswitched condition at a new place is the genuine unramified condition** (tex 3471–3487,
4163–4164, 4385–4451): for `b = false` the condition `condCxS j b` is `[W --(Φ_w − 1)--> W]`; the
identity, read along `b = false`. Kind: definition. -/
def condToUrS (j : ι × Bool) : (b : Bool) → b = false →
    GHom (condCxS K S k M place X j b) (genuineUq K S k (place j) (X j))
  | false, _ => idGHom _
  | true, h => Bool.noConfusion h

/-- **The map of an unswitched condition is the chosen split inflation** (tex 3471–3487,
4163–4164): for `b = false`, `ι_{j,b} = EU_j.i ∘ condToUrS`. Kind: PROVED. -/
theorem condιS_eq_ur (j : ι × Bool) (b : Bool) (hb : b = false) (n : ℤ)
    (x : (condCxS K S k M place X j b).X n) :
    (condιS K S k M place X EU j b).f n n rfl x =
      (EU j).i.f n n rfl ((condToUrS K S k M place X j b hb).f n n rfl x) := by
  subst hb
  rfl

/-- **The map of a switched condition is the identity of the full condition** (tex 3489–3498,
4163–4164): for `b = true`, `ι_{j,b}` is the canonical identification of `condCxS j b` with the
genuine local complex. Kind: PROVED. -/
theorem condιS_eq_cast (j : ι × Bool) (b : Bool) (hb : b = true) (n : ℤ)
    (x : (condCxS K S k M place X j b).X n) :
    (condιS K S k M place X EU j b).f n n rfl x =
      cast (congrArg (fun c => ((condCxS K S k M place X j c).X n : Type)) hb) x := by
  subst hb
  rfl

/-- **`condToUrS` is the canonical identification** (tex 3471–3487): along `b = false`.
Kind: PROVED. -/
theorem condToUrS_eq_cast (j : ι × Bool) (b : Bool) (hb : b = false) (n : ℤ)
    (x : (condCxS K S k M place X j b).X n) :
    (condToUrS K S k M place X j b hb).f n n rfl x =
      cast (congrArg (fun c => ((condCxS K S k M place X j c).X n : Type)) hb) x := by
  subst hb
  rfl

/-- **An unchanged condition is retained identically** (tex 4162, 3489–3498): if `b = b'`, the local
switch `condSplitS j b b'` is the canonical identification. Kind: PROVED. -/
theorem condSplitS_eq_cast (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true)
    (hbb : b = b') (n : ℤ) (hU : condCxS K S k M place X j b = condCxS K S k M place X j b')
    (x : (condCxS K S k M place X j b).X n) :
    (condSplitS K S k M place X EU j b b' h).i.f n n rfl x =
      cast (congrArg (fun C : GCx k => (C.X n : Type)) hU) x := by
  subst hbb
  cases b
  · exact (cast_eq _ x).symm
  · exact (cast_eq _ x).symm

end NewPlace

/-! ### The switch in lane RC30's form -/

section Presentation

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))

/-- **The primitive-to-relaxed map of local conditions of the switch** `f_P : U_T → U_{T ∪ {p}}`
(tex 4160–4164, 3489–3498): the product over the places of the presentation of the local switches
`presSplitS T p v` (the identity away from the two places above `p`, the split inclusion `EU` of
the unramified in the full condition at the two places above `p ∉ T`); the map of lane RC26's
change of conditions `presCondInclS T p`. Kind: definition. -/
def switchFP (T : Finset ι) (p : ι) :
    GHom (suppDataS K S₀ S k M Δ place X EU T).U
      (suppDataS K S₀ S k M Δ place X EU (insert p T)).U :=
  piMap fun v => (presSplitS K S₀ S k M Δ place X EU T p v).i

/-- **The primitive data of the switch in lane RC30's form** (tex 4160–4164, 3489–3498):
`selRestrict DR f_P` for the relaxed data `DR = suppDataS (insert p T)`. Kind: definition. -/
abbrev switchPrim (T : Finset ι) (p : ι) : SelData k :=
  selRestrict (suppDataS K S₀ S k M Δ place X EU (insert p T))
    (switchFP K S₀ S k M Δ place X EU T p)

/-- **The primitive data of the switch are the Selmer data of `T`** (tex 4160–4164, 3489–3498):
`selRestrict DR f_P = suppDataS T`; the condition maps agree by lane RC26's `restrict_ι_eq`.
Kind: PROVED. -/
theorem switchPrim_eq (T : Finset ι) (p : ι) :
    switchPrim K S₀ S k M Δ place X EU T p = suppDataS K S₀ S k M Δ place X EU T := by
  have h : ghomComp (switchFP K S₀ S k M Δ place X EU T p)
      (suppDataS K S₀ S k M Δ place X EU (insert p T)).ι =
      piMap (presCondS K S₀ S k M Δ place X EU T).i :=
    ghom_eq fun i j hij => LinearMap.ext fun u =>
      restrict_ι_eq (presCondInclS K S₀ S k M Δ place X EU T p) i j hij u
  exact congrArg (SelData.mk _ _ _ _) h

/-- **The terms of the primitive complex of the switch are those of `C_T`** (tex 4160–4164),
by definition. Kind: PROVED. -/
theorem switchPrim_X (T : Finset ι) (p : ι) (n : ℤ) :
    (selCx (switchPrim K S₀ S k M Δ place X EU T p)).X n =
      (suppCxS K S₀ S k M Δ place X EU T).X n :=
  rfl

/-- **The differentials of the primitive complex of the switch are those of `C_T`**
(tex 4160–4164, 3489–3498): lane RC26's identity chain map `restrictToSel`. Kind: PROVED. -/
theorem switchPrim_d (T : Finset ι) (p : ι) (a b : ℤ) (h : a + 1 = b)
    (w : (suppCxS K S₀ S k M Δ place X EU T).X a) :
    (selCx (switchPrim K S₀ S k M Δ place X EU T p)).d a b h w =
      (suppCxS K S₀ S k M Δ place X EU T).d a b h w :=
  (restrictToSel (presCondInclS K S₀ S k M Δ place X EU T p)).comm a b a b rfl h h rfl w

/-- **The primitive-to-relaxed map of the switch is the inclusion `C_T → C_{T ∪ {p}}`**
(tex 4160–4164, 3489–3498): `changeMap DR f_P` is `suppInclS T p` on elements, by definition.
Kind: PROVED. -/
theorem switchChange_f (T : Finset ι) (p : ι) (n : ℤ)
    (w : (suppCxS K S₀ S k M Δ place X EU T).X n) :
    (changeMap (suppDataS K S₀ S k M Δ place X EU (insert p T))
        (switchFP K S₀ S k M Δ place X EU T p)).f n n rfl w =
      (suppInclS K S₀ S k M Δ place X EU T p).f n n rfl w :=
  rfl

/-- **The primitive complex of the switch is `C_T`, as complexes** (tex 4160–4164, 3489–3498):
lane RC26's identity isomorphism `restrictIso`. Kind: definition. -/
def switchPrimIso (T : Finset ι) (p : ι) :
    (selCx (switchPrim K S₀ S k M Δ place X EU T p)).toCC ≅
      (suppCxS K S₀ S k M Δ place X EU T).toCC :=
  restrictIso (presCondInclS K S₀ S k M Δ place X EU T p)

/-- **The isomorphism carries the primitive-to-relaxed map to the inclusion of the switch**
(tex 4160–4164, 3489–3498). Kind: PROVED. -/
theorem switchPrimIso_comm (T : Finset ι) (p : ι) :
    (switchPrimIso K S₀ S k M Δ place X EU T p).hom ≫
        GHom.toCC (suppInclS K S₀ S k M Δ place X EU T p) =
      GHom.toCC (changeMap (suppDataS K S₀ S k M Δ place X EU (insert p T))
        (switchFP K S₀ S k M Δ place X EU T p)) := by
  ext n
  rfl

/-! ### The new place: the prime `p` with its two places -/

/-- **The full local complex at the switched prime** (tex 4163–4164, 4176–4184):
`L_q = C^•_cont(G_{K_w}, M) ⊕ C^•_cont(G_{K_w̄}, M)` at `w = (p, false)`, `w̄ = (p, true)`.
Kind: definition. -/
abbrev switchLq (p : ι) : GCx k :=
  prodGCx (genuineLq K S k M (place (p, false))) (genuineLq K S k M (place (p, true)))

/-- **The unramified condition at the switched prime** (tex 3471–3487, 4163–4164):
`U_q = [W_w --(Φ_w − 1)--> W_w] ⊕ [W_w̄ --(Φ_w̄ − 1)--> W_w̄]`. Kind: definition. -/
abbrev switchUq (p : ι) : GCx k :=
  prodGCx (genuineUq K S k (place (p, false)) (X (p, false)))
    (genuineUq K S k (place (p, true)) (X (p, true)))

/-- **The map `ι_q` at the switched prime** (tex 4163–4164, 3489–3498): the chosen split
inflations `EU_w.i ⊕ EU_w̄.i`. Kind: definition. -/
abbrev switchιq (p : ι) : GHom (switchUq K S k place X p) (switchLq K S k M place p) :=
  prodGHom (EU (p, false)).i (EU (p, true)).i

/-- **The `q`-component of the relaxed conditions, as a chain map** `U_{T ∪ {p}} → L_q`
(tex 4163–4164, 3489–3498): the components at `w`, `w̄` of the relaxed condition map `ι_R`.
Kind: definition. -/
def switchQRHom (T : Finset ι) (p : ι) :
    GHom (suppDataS K S₀ S k M Δ place X EU (insert p T)).U (switchLq K S k M place p) where
  f a b h := LinearMap.prod
    (((presCondS K S₀ S k M Δ place X EU (insert p T)).i (.inr (p, false))).f a b h ∘ₗ
      LinearMap.proj (Sum.inr (p, false) : Places K S₀ ⊕ (ι × Bool)))
    (((presCondS K S₀ S k M Δ place X EU (insert p T)).i (.inr (p, true))).f a b h ∘ₗ
      LinearMap.proj (Sum.inr (p, true) : Places K S₀ ⊕ (ι × Bool)))
  comm i i₁ j j₁ hij h₁ h₂ hj x := Prod.ext
    (((presCondS K S₀ S k M Δ place X EU (insert p T)).i (.inr (p, false))).comm
      i i₁ j j₁ hij h₁ h₂ hj (x (.inr (p, false))))
    (((presCondS K S₀ S k M Δ place X EU (insert p T)).i (.inr (p, true))).comm
      i i₁ j j₁ hij h₁ h₂ hj (x (.inr (p, true))))

/-- **Lane RC30's `qR` for the switch** (tex 4163–4164): the components of `switchQRHom`.
Kind: definition. -/
def switchQR (T : Finset ι) (p : ι) (n : ℤ) :
    (suppDataS K S₀ S k M Δ place X EU (insert p T)).U.X n →ₗ[k]
      (switchLq K S k M place p).X n :=
  (switchQRHom K S₀ S k M Δ place X EU T p).f n n rfl

/-- **`qR` is the projection onto the two components above `p`** (tex 4163–4164, 3489–3498):
the relaxed conditions at `w`, `w̄` are the full ones (`p ∈ insert p T`) and `qR` is the canonical
identification of the two components. Kind: PROVED. -/
theorem switchQR_eq_cast (T : Finset ι) (p : ι) (n : ℤ)
    (u : (suppDataS K S₀ S k M Δ place X EU (insert p T)).U.X n) :
    switchQR K S₀ S k M Δ place X EU T p n u =
      ((cast (congrArg (fun c => ((condCxS K S k M place X (p, false) c).X n : Type))
          (decide_eq_true (Finset.mem_insert_self p T))) (u (.inr (p, false))),
        cast (congrArg (fun c => ((condCxS K S k M place X (p, true) c).X n : Type))
          (decide_eq_true (Finset.mem_insert_self p T))) (u (.inr (p, true)))) :
        (genuineLq K S k M (place (p, false))).X n × (genuineLq K S k M (place (p, true))).X n) :=
  Prod.ext
    (condιS_eq_cast K S k M place X EU (p, false) _
      (decide_eq_true (Finset.mem_insert_self p T)) n (u (.inr (p, false))))
    (condιS_eq_cast K S k M place X EU (p, true) _
      (decide_eq_true (Finset.mem_insert_self p T)) n (u (.inr (p, true))))

/-- **The `q`-component of the primitive conditions, as a chain map** `U_T → U_q` for `p ∉ T`
(tex 4163–4164, 3471–3487): the components of `U_T` at `w`, `w̄`, identified with the genuine
unramified conditions (`condToUrS`). Kind: definition. -/
def switchQPHom (T : Finset ι) (p : ι) (hp : p ∉ T) :
    GHom (suppDataS K S₀ S k M Δ place X EU T).U (switchUq K S k place X p) where
  f a b h := LinearMap.prod
    ((condToUrS K S k M place X (p, false) (decide (p ∈ T)) (decide_eq_false hp)).f a b h ∘ₗ
      LinearMap.proj (Sum.inr (p, false) : Places K S₀ ⊕ (ι × Bool)))
    ((condToUrS K S k M place X (p, true) (decide (p ∈ T)) (decide_eq_false hp)).f a b h ∘ₗ
      LinearMap.proj (Sum.inr (p, true) : Places K S₀ ⊕ (ι × Bool)))
  comm i i₁ j j₁ hij h₁ h₂ hj x := Prod.ext
    ((condToUrS K S k M place X (p, false) (decide (p ∈ T)) (decide_eq_false hp)).comm
      i i₁ j j₁ hij h₁ h₂ hj (x (.inr (p, false))))
    ((condToUrS K S k M place X (p, true) (decide (p ∈ T)) (decide_eq_false hp)).comm
      i i₁ j j₁ hij h₁ h₂ hj (x (.inr (p, true))))

/-- **Lane RC30's `qP` for the switch** (tex 4163–4164): the components of `switchQPHom`.
Kind: definition. -/
def switchQP (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ) :
    (suppDataS K S₀ S k M Δ place X EU T).U.X n →ₗ[k] (switchUq K S k place X p).X n :=
  (switchQPHom K S₀ S k M Δ place X EU T p hp).f n n rfl

/-- **`qP` is the projection onto the two components above `p`** (tex 4163–4164, 3471–3487): for
`p ∉ T` the conditions of `T` at `w`, `w̄` are the unramified ones and `qP` is the canonical
identification of the two components. Kind: PROVED. -/
theorem switchQP_eq_cast (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ)
    (y : (suppDataS K S₀ S k M Δ place X EU T).U.X n) :
    switchQP K S₀ S k M Δ place X EU T p hp n y =
      ((cast (congrArg (fun c => ((condCxS K S k M place X (p, false) c).X n : Type))
          (decide_eq_false hp)) (y (.inr (p, false))),
        cast (congrArg (fun c => ((condCxS K S k M place X (p, true) c).X n : Type))
          (decide_eq_false hp)) (y (.inr (p, true)))) :
        (genuineUq K S k (place (p, false)) (X (p, false))).X n ×
          (genuineUq K S k (place (p, true)) (X (p, true))).X n) :=
  Prod.ext
    (condToUrS_eq_cast K S k M place X (p, false) _ (decide_eq_false hp) n
      (y (.inr (p, false))))
    (condToUrS_eq_cast K S k M place X (p, true) _ (decide_eq_false hp) n
      (y (.inr (p, true))))

/-- **At `q`, `f_P` is the map from the unramified condition to the full condition**
(tex 4163–4164, 3489–3498): `qR ∘ f_P = ι_q ∘ qP`, lane RC30's field `q_P`, from the presentation
(`presSplitS_compat`, `condιS_eq_ur`). Kind: PROVED. -/
theorem switchQ_P (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ)
    (y : (suppDataS K S₀ S k M Δ place X EU T).U.X n) :
    switchQR K S₀ S k M Δ place X EU T p n ((switchFP K S₀ S k M Δ place X EU T p).f n n rfl y) =
      (switchιq K S k M place X EU p).f n n rfl (switchQP K S₀ S k M Δ place X EU T p hp n y) :=
  Prod.ext
    ((presSplitS_compat K S₀ S k M Δ place X EU T p (.inr (p, false)) n
      (y (.inr (p, false)))).trans
      (condιS_eq_ur K S k M place X EU (p, false) _ (decide_eq_false hp) n (y (.inr (p, false)))))
    ((presSplitS_compat K S₀ S k M Δ place X EU T p (.inr (p, true)) n
      (y (.inr (p, true)))).trans
      (condιS_eq_ur K S k M place X EU (p, true) _ (decide_eq_false hp) n (y (.inr (p, true)))))

/-! ### The old places -/

/-- **Lane RC30's old components of `U_R` for the switch** (tex 4162): the projection of
`U_{T ∪ {p}}` onto its component at a place `v`. Kind: definition. -/
def switchPR (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ) :
    (suppDataS K S₀ S k M Δ place X EU (insert p T)).U.X n →ₗ[k]
      ((presCondS K S₀ S k M Δ place X EU (insert p T)).U v).X n :=
  LinearMap.proj v

/-- **Lane RC30's old components of `U_P` for the switch** (tex 4162, 3489–3498): the projection of
`U_T` onto its component at `v`, followed by the local switch at `v` (the identity on every old
summand, `switchPP_old`). Kind: definition. -/
def switchPP (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ) :
    (suppDataS K S₀ S k M Δ place X EU T).U.X n →ₗ[k]
      ((presCondS K S₀ S k M Δ place X EU (insert p T)).U v).X n :=
  (presSplitS K S₀ S k M Δ place X EU T p v).i.f n n rfl ∘ₗ LinearMap.proj v

/-- **Every old condition is retained by `f_P`** (tex 4162, 3489–3498): away from the two places
above `p` the old component of `U_P` is the canonical identification of the components of `U_T` and
`U_{T ∪ {p}}`. Kind: PROVED. -/
theorem switchPP_old (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool))
    (h₁ : v ≠ .inr (p, false)) (h₂ : v ≠ .inr (p, true)) (n : ℤ)
    (hU : (presCondS K S₀ S k M Δ place X EU T).U v =
      (presCondS K S₀ S k M Δ place X EU (insert p T)).U v)
    (y : (suppDataS K S₀ S k M Δ place X EU T).U.X n) :
    switchPP K S₀ S k M Δ place X EU T p v n y =
      cast (congrArg (fun C : GCx k => (C.X n : Type)) hU) (y v) := by
  match v with
  | .inl v₀ => exact (cast_eq _ _).symm
  | .inr j =>
    have hj : j.1 ≠ p := by
      intro hj
      obtain ⟨q, c⟩ := j
      simp only at hj
      subst hj
      cases c
      · exact h₁ rfl
      · exact h₂ rfl
    refine condSplitS_eq_cast K S k M place X EU j _ _ _ ?_ n hU _
    refine decide_eq_decide.2 ⟨fun h => Finset.mem_insert_of_mem h, fun h => ?_⟩
    rcases Finset.mem_insert.1 h with h | h
    · exact absurd h hj
    · exact h

/-- **The relaxed homotopy of the switch** (tex 4162–4165): the sum over the old places of the old
isotropy homotopies on the old components (the strict condition at `q` is zero).
Kind: definition. -/
def switchHR (T : Finset ι) (p : ι) {EL US : GCx k} {Uo' : Places K S₀ ⊕ (ι × Bool) → GCx k}
    (old : Finset (Places K S₀ ⊕ (ι × Bool)))
    (hv : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i j l : ℤ), i + j = l + 1 →
      (Uo' v).X i →ₗ[k] ((presCondS K S₀ S k M Δ place X EU (insert p T)).U v).X j →ₗ[k] EL.X l)
    (pS : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i : ℤ), US.X i →ₗ[k] (Uo' v).X i)
    (i j l : ℤ) (h : i + j = l + 1) :
    US.X i →ₗ[k] (suppDataS K S₀ S k M Δ place X EU (insert p T)).U.X j →ₗ[k] EL.X l :=
  LinearMap.mk₂ k
    (fun x y => ∑ v ∈ old, hv v i j l h (pS v i x) (switchPR K S₀ S k M Δ place X EU T p v j y))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum])
    (fun x y y' => by simp only [map_add, Finset.sum_add_distrib])
    (fun c x y => by simp only [map_smul, Finset.smul_sum])

/-- **The primitive homotopy of the switch** (tex 4162–4165): the sum over the old places of the
same old homotopies, plus the homotopy `hq` at `q` on the `q`-components. Kind: definition. -/
def switchHP (T : Finset ι) (p : ι) (hp : p ∉ T) {EL : GCx k} {DPp : SelData k}
    {Uo' : Places K S₀ ⊕ (ι × Bool) → GCx k} {Uq' : GCx k}
    (old : Finset (Places K S₀ ⊕ (ι × Bool)))
    (hv : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i j l : ℤ), i + j = l + 1 →
      (Uo' v).X i →ₗ[k] ((presCondS K S₀ S k M Δ place X EU (insert p T)).U v).X j →ₗ[k] EL.X l)
    (hq : ∀ i j l : ℤ, i + j = l + 1 → Uq'.X i →ₗ[k] (switchUq K S k place X p).X j →ₗ[k] EL.X l)
    (pPp : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i : ℤ), DPp.U.X i →ₗ[k] (Uo' v).X i)
    (qPp : ∀ i : ℤ, DPp.U.X i →ₗ[k] Uq'.X i) (i j l : ℤ) (h : i + j = l + 1) :
    DPp.U.X i →ₗ[k] (suppDataS K S₀ S k M Δ place X EU T).U.X j →ₗ[k] EL.X l :=
  LinearMap.mk₂ k
    (fun x y => ∑ v ∈ old, hv v i j l h (pPp v i x) (switchPP K S₀ S k M Δ place X EU T p v j y) +
      hq i j l h (qPp i x) (switchQP K S₀ S k M Δ place X EU T p hp j y))
    (fun x x' y => by
      simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
      abel)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_add])
    (fun x y y' => by
      simp only [map_add, Finset.sum_add_distrib]
      abel)
    (fun c x y => by simp only [map_smul, Finset.smul_sum, smul_add])

/-! ### The inputs and the retention datum of the switch -/

/-- **The inputs of lane RC30's retention datum at the switch `C_T ⊂ C_{T ∪ {p}}`, `p ∉ T`**
(tex 4157–4175, 3489–3498): everything that is not a component of the presentation. The orthogonal
Selmer data `DPp` (`C_{P⊥}`) and the strict conditions `fS : U_S → U_{P⊥}` are parameters (inputs:
the text's orthogonal diagrams, tex 4160–4164, 3830–3833). The relaxed data, the primitive data, the
new place and its `q`-components `qR`, `qP` are those of the presentation. Kind: definition. -/
structure SwitchRetentionInputs (T : Finset ι) (p : ι) (hp : p ∉ T) (DPp : SelData k)
    {US : GCx k} (fS : GHom US DPp.U) where
  /-- Data, not pinned: the genuine cup product (Nekovář 6.2.5–6.4.3) is the intended instance.
  GLUE (tex 4164–4168; Nekovář 6.2.5–6.2.8): the global target of the cup product. -/
  E : GCx k
  /-- Data, not pinned: the genuine cup product (Nekovář 6.2.5–6.4.3) is the intended instance.
  GLUE (tex 4164–4168; Nekovář 6.2.5–6.2.8): the local target of the cup product. -/
  EL : GCx k
  /-- Data, not pinned: the genuine cup product (Nekovář 6.2.5–6.4.3) is the intended instance.
  GLUE (tex 4164–4168): the restriction of the targets. -/
  resE : GHom E EL
  /-- Data, not pinned: the genuine cup product (Nekovář 6.2.5–6.4.3) is the intended instance.
  GLUE (tex 4164–4168, 3829–3833; Nekovář 6.4.1–6.4.3): the global cup product, shared by
  both pairings. -/
  cupG : GPair DPp.G (suppDataS K S₀ S k M Δ place X EU (insert p T)).G E
  /-- Data, not pinned: the genuine cup product (Nekovář 6.2.5–6.4.3) is the intended instance.
  GLUE (tex 4164–4168, 3829–3833; Nekovář 6.4.1–6.4.3): the local cup product, shared by
  both pairings. -/
  cupL : GPair DPp.L (suppDataS K S₀ S k M Δ place X EU (insert p T)).L EL
  /-- GLUE (tex 4164–4168; Nekovář 6.4.1–6.4.3): restriction commutes with the cup products. -/
  compat : ∀ (i j l i' j' l' : ℤ) (h : i + j = l) (h' : i' + j' = l') (hi : i = i') (hj : j = j')
    (hl : l = l') (a : DPp.G.X i) (b : (suppDataS K S₀ S k M Δ place X EU (insert p T)).G.X j),
    resE.f l l' hl (cupG.P i j l h a b) =
      cupL.P i' j' l' h' (DPp.res.f i i' hi a)
        ((suppDataS K S₀ S k M Δ place X EU (insert p T)).res.f j j' hj b)
  /-- ELLIOT (tex 4162): the old places, finitely many places of the presentation. -/
  old : Finset (Places K S₀ ⊕ (ι × Bool))
  /-- ELLIOT (tex 4162–4164): the old places are not above `p`. -/
  old_avoid : ∀ v ∈ old, v ≠ .inr (p, false) ∧ v ≠ .inr (p, true)
  /-- ELLIOT (tex 4161–4162, 3830–3833): the old orthogonal local conditions. -/
  Uo' : Places K S₀ ⊕ (ι × Bool) → GCx k
  /-- ELLIOT (tex 4162, 3830–3833): the old isotropy homotopies, retained. -/
  hv : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i j l : ℤ), i + j = l + 1 →
    (Uo' v).X i →ₗ[k] ((presCondS K S₀ S k M Δ place X EU (insert p T)).U v).X j →ₗ[k] EL.X l
  /-- ELLIOT (tex 4163–4164): the orthogonal condition at `q` (the text: the unramified one). -/
  Uq' : GCx k
  /-- GLUE (tex 4163–4165, 3830–3833; Nekovář 6.2.5–6.2.8): the isotropy homotopy at `q`. -/
  hq : ∀ i j l : ℤ, i + j = l + 1 → Uq'.X i →ₗ[k] (switchUq K S k place X p).X j →ₗ[k] EL.X l
  /-- ELLIOT (tex 4161–4162): the old components of `U_S`. -/
  pS : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i : ℤ), US.X i →ₗ[k] (Uo' v).X i
  /-- ELLIOT (tex 4161–4162): the old components of `U_{P⊥}`. -/
  pPp : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i : ℤ), DPp.U.X i →ₗ[k] (Uo' v).X i
  /-- ELLIOT (tex 4163–4164): the `q`-component of `U_{P⊥}`. -/
  qPp : ∀ i : ℤ, DPp.U.X i →ₗ[k] Uq'.X i
  /-- GLUE (tex 4162–4168, 3830–3833; Nekovář 6.2.5–6.2.8): the isotropy identity of the
  relaxed homotopy `switchHR`. -/
  isoR : ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hl : l + 1 = l₁) (x : US.X i)
    (y : (suppDataS K S₀ S k M Δ place X EU (insert p T)).U.X j),
    EL.d l l₁ hl (switchHR K S₀ S k M Δ place X EU T p old hv pS i j l h x y) +
        switchHR K S₀ S k M Δ place X EU T p old hv pS i₁ j l₁ (by omega) (US.d i i₁ hi x) y +
        sgn i • switchHR K S₀ S k M Δ place X EU T p old hv pS i j₁ l₁ (by omega) x
          ((suppDataS K S₀ S k M Δ place X EU (insert p T)).U.d j j₁ hj y) =
      cupL.P i j l₁ (by omega) ((ghomComp fS DPp.ι).f i i rfl x)
        ((suppDataS K S₀ S k M Δ place X EU (insert p T)).ι.f j j rfl y)
  /-- GLUE (tex 4162–4168, 3830–3833; Nekovář 6.2.5–6.2.8): the isotropy identity of the
  primitive homotopy `switchHP`. -/
  isoP : ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hl : l + 1 = l₁) (x : DPp.U.X i) (y : (suppDataS K S₀ S k M Δ place X EU T).U.X j),
    EL.d l l₁ hl (switchHP K S₀ S k M Δ place X EU T p hp old hv hq pPp qPp i j l h x y) +
        switchHP K S₀ S k M Δ place X EU T p hp old hv hq pPp qPp i₁ j l₁ (by omega)
          (DPp.U.d i i₁ hi x) y +
        sgn i • switchHP K S₀ S k M Δ place X EU T p hp old hv hq pPp qPp i j₁ l₁ (by omega) x
          ((suppDataS K S₀ S k M Δ place X EU T).U.d j j₁ hj y) =
      cupL.P i j l₁ (by omega) (DPp.ι.f i i rfl x)
        ((ghomComp (switchFP K S₀ S k M Δ place X EU T p)
          (suppDataS K S₀ S k M Δ place X EU (insert p T)).ι).f j j rfl y)
  /-- ELLIOT (tex 4161–4162): every old orthogonal condition is retained by `j`. -/
  ret_S : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i : ℤ) (x : US.X i), pPp v i (fS.f i i rfl x) = pS v i x
  /-- ELLIOT (tex 4163–4164): at `q`, `j` is the map from zero to the unramified condition. -/
  q_S : ∀ (i : ℤ) (x : US.X i), qPp i (fS.f i i rfl x) = 0

variable {K S₀ S k M Δ place X EU}

/-- **Lane RC30's retention datum at the switch** (tex 4157–4168, 3489–3498): relaxed data
`suppDataS (insert p T)`, primitive map `switchFP T p`, new place `switchLq p`, `switchUq p`,
`switchιq p`; the `q`-components `qR`, `qP`, the old index type, conditions and components of the
relaxed and primitive sides and the homotopies `hR`, `hP` are definitions from the presentation;
`q_P`, `ret_P`, `hR_eq`, `hP_eq` are PROVED; the rest are the inputs. Kind: definition. -/
def SwitchRetentionInputs.toPlaceRetentionG {T : Finset ι} {p : ι} {hp : p ∉ T} {DPp : SelData k}
    {US : GCx k} {fS : GHom US DPp.U}
    (I : SwitchRetentionInputs K S₀ S k M Δ place X EU T p hp DPp fS) :
    PlaceRetentionG (suppDataS K S₀ S k M Δ place X EU (insert p T)) DPp
      (switchFP K S₀ S k M Δ place X EU T p) fS (switchLq K S k M place p)
      (switchUq K S k place X p) (switchιq K S k M place X EU p) where
  E := I.E
  EL := I.EL
  resE := I.resE
  cupG := I.cupG
  cupL := I.cupL
  compat := I.compat
  ι := Places K S₀ ⊕ (ι × Bool)
  old := I.old
  Uo := (presCondS K S₀ S k M Δ place X EU (insert p T)).U
  Uo' := I.Uo'
  hv := I.hv
  Uq' := I.Uq'
  hq := I.hq
  pR := switchPR K S₀ S k M Δ place X EU T p
  pP := switchPP K S₀ S k M Δ place X EU T p
  pS := I.pS
  pPp := I.pPp
  qR := switchQR K S₀ S k M Δ place X EU T p
  qP := switchQP K S₀ S k M Δ place X EU T p hp
  qPp := I.qPp
  hR := switchHR K S₀ S k M Δ place X EU T p I.old I.hv I.pS
  hR_eq _ _ _ _ _ _ := rfl
  isoR := I.isoR
  hP := switchHP K S₀ S k M Δ place X EU T p hp I.old I.hv I.hq I.pPp I.qPp
  hP_eq _ _ _ _ _ _ := rfl
  isoP := I.isoP
  ret_P _ _ _ := rfl
  ret_S := I.ret_S
  q_P := switchQ_P K S₀ S k M Δ place X EU T p hp
  q_S := I.q_S

/-- **`λ_R ∘ i = e_q λ_P` at the switch `C_T ⊂ C_{T ∪ {p}}`** (tex 4157–4175, 3489–3498): for the
retention datum of the switch, a trace killing coboundaries and the paired strict lift
`j z_S = e z_{P⊥} + d b`, every cocycle `w ∈ C_T²` satisfies
`λ_R(suppInclS T p w) = e · λ_P(w)` with `λ_R = β_R(z_S, ·)`, `λ_P = β_P(z_{P⊥}, ·)`: lane RC30's
`PlaceRetentionG.pairedFunctional_natural`, transported along `switchPrim_d`, `switchChange_f`.
Kind: PROVED. -/
theorem switch_natural {T : Finset ι} {p : ι} {hp : p ∉ T} {DPp : SelData k} {US : GCx k}
    {fS : GHom US DPp.U} (I : SwitchRetentionInputs K S₀ S k M Δ place X EU T p hp DPp fS)
    (tr : (coneCx I.toPlaceRetentionG.toRetainedPairing.QP.resE).X 3 →ₗ[k] k)
    (htr : ∀ x, tr ((coneCx I.toPlaceRetentionG.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : k)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b) :
    ∀ w : (suppCxS K S₀ S k M Δ place X EU T).X 2,
      (suppCxS K S₀ S k M Δ place X EU T).d 2 3 rfl w = 0 →
      pairedFun I.toPlaceRetentionG.toRetainedPairing.QR
          (tr : (coneCx I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3 →ₗ[k] k) zS
          ((suppInclS K S₀ S k M Δ place X EU T p).f 2 2 rfl w) =
        e * pairedFun I.toPlaceRetentionG.toRetainedPairing.QP tr zP w := by
  intro w hw
  exact I.toPlaceRetentionG.pairedFunctional_natural tr htr zS zP e b hlift w
    ((switchPrim_d K S₀ S k M Δ place X EU T p 2 3 rfl w).trans hw)

/-- **The same at the inclusion of the switch `suppSwitchS T p`** (tex 4157–4175, 3489–3498): its
inclusion is `suppInclS T p` by definition (`suppSwitchS_i`). Kind: PROVED. -/
theorem switch_natural_switch [DecidableEq (Places K S₀)] {T : Finset ι} {p : ι} {hp : p ∉ T}
    {DPp : SelData k} {US : GCx k} {fS : GHom US DPp.U}
    (I : SwitchRetentionInputs K S₀ S k M Δ place X EU T p hp DPp fS)
    (tr : (coneCx I.toPlaceRetentionG.toRetainedPairing.QP.resE).X 3 →ₗ[k] k)
    (htr : ∀ x, tr ((coneCx I.toPlaceRetentionG.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : k)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    (w : (suppCxS K S₀ S k M Δ place X EU T).X 2)
    (hw : (suppCxS K S₀ S k M Δ place X EU T).d 2 3 rfl w = 0) :
    pairedFun I.toPlaceRetentionG.toRetainedPairing.QR
        (tr : (coneCx I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3 →ₗ[k] k) zS
        ((suppSwitchS K S₀ S k M Δ place X EU T p).i.f 2 2 rfl w) =
      e * pairedFun I.toPlaceRetentionG.toRetainedPairing.QP tr zP w :=
  switch_natural I tr htr zS zP e b hlift w hw

/-- **The relation `lam ∘ Sum.inl = ψ(e) • lam_P` at the switch** (tex 4170–4175): the input
`hlamR` of lane RC31's `KmStep`, for functionals `lam j = ψ(λ_R(φ_R j))`, `lam_P i = ψ(λ_P(φ_P i))`
on cocycles `φ_P i ∈ C_T²` with `φ_R (inl i) = suppInclS T p (φ_P i)` (lane RC30's
`hlamR_of_retention`). Kind: PROVED. -/
theorem switch_hlamR {F : Type} [CommRing F] {α κ : Type} {T : Finset ι} {p : ι} {hp : p ∉ T}
    {DPp : SelData k} {US : GCx k} {fS : GHom US DPp.U}
    (I : SwitchRetentionInputs K S₀ S k M Δ place X EU T p hp DPp fS)
    (tr : (coneCx I.toPlaceRetentionG.toRetainedPairing.QP.resE).X 3 →ₗ[k] k)
    (htr : ∀ x, tr ((coneCx I.toPlaceRetentionG.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : k)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    (φP : α → (suppCxS K S₀ S k M Δ place X EU T).X 2)
    (hφP : ∀ i, (suppCxS K S₀ S k M Δ place X EU T).d 2 3 rfl (φP i) = 0)
    (φR : α ⊕ κ → (suppCxS K S₀ S k M Δ place X EU (insert p T)).X 2)
    (hφR : ∀ i, φR (Sum.inl i) = (suppInclS K S₀ S k M Δ place X EU T p).f 2 2 rfl (φP i))
    (ψ : k →+* F) (lam : α ⊕ κ → F) (lamP : α → F)
    (hlam : ∀ j, lam j = ψ (pairedFun I.toPlaceRetentionG.toRetainedPairing.QR
      (tr : (coneCx I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3 →ₗ[k] k) zS (φR j)))
    (hlamP : ∀ i, lamP i = ψ (pairedFun I.toPlaceRetentionG.toRetainedPairing.QP tr zP (φP i))) :
    lam ∘ Sum.inl = ψ e • lamP :=
  hlamR_of_retention I.toPlaceRetentionG tr htr zS zP e b hlift φP
    (fun i => (switchPrim_d K S₀ S k M Δ place X EU T p 2 3 rfl (φP i)).trans (hφP i)) φR hφR ψ
    lam lamP hlam hlamP

/-- **Consistency of the inputs at every switch** (tex 4157–4175): for any orthogonal data, zero
targets, no old places and zero homotopies and components satisfy all the fields. Kind: PROVED. -/
theorem nonempty_switchRetentionInputs (T : Finset ι) (p : ι) (hp : p ∉ T) (DPp : SelData k)
    {US : GCx k} (fS : GHom US DPp.U) :
    Nonempty (SwitchRetentionInputs K S₀ S k M Δ place X EU T p hp DPp fS) :=
  ⟨{ E := zeroCx k
     EL := zeroCx k
     resE := zeroGHom _ _
     cupG := ⟨fun _ _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
     cupL := ⟨fun _ _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
     compat := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
     old := ∅
     old_avoid := fun _ h => by simp at h
     Uo' := fun _ => zeroCx k
     hv := fun _ _ _ _ _ => 0
     Uq' := zeroCx k
     hq := fun _ _ _ _ => 0
     pS := fun _ _ => 0
     pPp := fun _ _ => 0
     qPp := fun _ => 0
     isoR := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
     isoP := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
     ret_S := fun _ _ _ => rfl
     q_S := fun _ _ => rfl }⟩

end Presentation

end ZInQ.Manuscript.RC.Wiring

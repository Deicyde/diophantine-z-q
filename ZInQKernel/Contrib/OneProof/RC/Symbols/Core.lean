import Mathlib

/-!
# Lane RC2 core: compatible typed graphs and coefficient symbols (tex 2006–2149)

Manuscript: Definition `ex:sec7-typed-graph` (tex 2015–2066), Definition `ex:sec7-symbol`
(2068–2100), Lemma `ex:sec7-coefficient-rules` (2102–2136).

Abstract model (DEPARTURE of form, recorded in the lane report):
* vertices are named by natural numbers; a configuration is a finite vertex set with types and
  residue bits;
* the type alphabet `L` is the group of realizable types, with the sign coordinate
  `ε v = (p_v - 1)/2 mod 2` as an additive map `ε : L →+ ZMod 2`;
* stationary external incidences are absorbed as type coordinates;
* a symbol is one function `A` on all configurations; the coefficient rules of
  `ex:sec7-coefficient-rules` are hypotheses (`CoefficientRules`), their arithmetic proof being
  App F `ex:app-coefficient-rules` (tex 9447), another lane's.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

/-- A finite configuration (typed graph, `ex:sec7-typed-graph`): vertex set `V`, types `t`,
quadratic residue bits `z v w` (`= 0` or `1` as `(p_v/p_w) = 1` or `-1`). Only values on `V`
matter. -/
structure Config (L : Type*) where
  V : Finset ℕ
  t : ℕ → L
  z : ℕ → ℕ → ZMod 2

variable {L : Type*} [AddCommGroup L]

namespace Config

/-- Reciprocity compatibility `z_{vw} + z_{wv} = ε_v ε_w` (tex 2037–2041). -/
def Compatible (ε : L →+ ZMod 2) (Γ : Config L) : Prop :=
  ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, v ≠ w → Γ.z v w + Γ.z w v = ε (Γ.t v) * ε (Γ.t w)

/-- Change the independent bits of the pairs in `U` (and their reverse bits). -/
def flipBy (Γ : Config L) (U : Finset (Sym2 ℕ)) : Config L :=
  { Γ with z := fun a b => Γ.z a b + if a ≠ b ∧ s(a, b) ∈ U then 1 else 0 }

/-- Change the independent bit of one pair. -/
def flip (Γ : Config L) (v w : ℕ) : Config L := Γ.flipBy {s(v, w)}

/-- Contraction `Γ/(v,w)` (tex 2050–2054): `w` is merged into `v`, the type is summed and every
external incidence is summed; the internal bit is not retained. -/
def contract (Γ : Config L) (v w : ℕ) : Config L where
  V := Γ.V.erase w
  t := Function.update Γ.t v (Γ.t v + Γ.t w)
  z := fun a b => if a = v then Γ.z v b + Γ.z w b else if b = v then Γ.z a v + Γ.z a w
    else Γ.z a b

/-- Restriction to a vertex subset. -/
def restrict (Γ : Config L) (W : Finset ℕ) : Config L := { Γ with V := W }

/-- Isomorphic typed graphs. -/
def IsIso (Γ Δ : Config L) : Prop :=
  ∃ e : Γ.V ≃ Δ.V, (∀ v : Γ.V, Δ.t (e v) = Γ.t v) ∧
    ∀ v w : Γ.V, v ≠ w → Δ.z (e v) (e w) = Γ.z v w

/-- Total type `∑_v ℓ_v`, read by a filter (tex 2042–2044). -/
def total (Γ : Config L) : L := ∑ v ∈ Γ.V, Γ.t v

end Config

/-- **The coefficient rules** (`ex:sec7-coefficient-rules`, tex 2102–2136), as hypotheses on an
abstract symbol (kind: ELLIOT, proved arithmetically in App F `ex:app-coefficient-rules`, tex
9447–9976, another lane).
1. graph dependence and whole-prime omission: one function on all compatible typed graphs,
   determined by the typed graph (the omitted-prime reading is the same `A`);
2. contraction `Δ_{vw} A(Γ) = A(Γ/(v,w))`;
3. primary isolation. -/
structure CoefficientRules (ε : L →+ ZMod 2) (A : Config L → ZMod 2) : Prop where
  graph_dependence : ∀ Γ Δ : Config L, Γ.Compatible ε → Γ.IsIso Δ → A Γ = A Δ
  contraction : ∀ Γ : Config L, Γ.Compatible ε → ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, v ≠ w →
    A Γ + A (Γ.flip v w) = A (Γ.contract v w)
  primary_isolation : ∀ Γ : Config L, Γ.Compatible ε → ∀ v ∈ Γ.V, Γ.t v = 0 →
    (∀ w ∈ Γ.V, w ≠ v → Γ.z v w = 0 ∧ Γ.z w v = 0) → A Γ = 0

/-- The symbol is zero off its filter (total type `τ`) (tex 2079). -/
def VanishesOffFilter (A : Config L → ZMod 2) (τ : L) : Prop :=
  ∀ Γ : Config L, A Γ = 1 → Γ.total = τ

/-- Iterated finite difference in the pair bits of `S` (tex 2219). -/
def diff (A : Config L → ZMod 2) (Γ : Config L) (S : Finset (Sym2 ℕ)) : ZMod 2 :=
  ∑ U ∈ S.powerset, A (Γ.flipBy U)

/-- Pairs of distinct vertices of a finite set. -/
def pairs (V : Finset ℕ) : Finset (Sym2 ℕ) :=
  ((V ×ˢ V).filter (fun p => p.1 ≠ p.2)).image (fun p => s(p.1, p.2))

/-- The terminal polynomial (tex 2214–2219) is nonzero: some change of the pair bits makes the
symbol one. -/
def TerminalNonzero (A : Config L → ZMod 2) (Γ : Config L) : Prop :=
  ∃ U ⊆ pairs Γ.V, A (Γ.flipBy U) = 1

/-! ### Connectivity, contraction by a forest, rooted forests -/

/-- Connectivity through the pairs of `S`. -/
def conn (S : Finset (Sym2 ℕ)) : ℕ → ℕ → Prop :=
  Relation.EqvGen (fun a b => s(a, b) ∈ S)

open Classical in
/-- Block representative: the least vertex of `V` connected to `v`. -/
noncomputable def rep (V : Finset ℕ) (S : Finset (Sym2 ℕ)) (v : ℕ) : ℕ :=
  if h : (V.filter (fun u => conn S u v)).Nonempty then (V.filter (fun u => conn S u v)).min' h
  else v

/-- Number of blocks. -/
noncomputable def ncomp (V : Finset ℕ) (S : Finset (Sym2 ℕ)) : ℕ := (V.image (rep V S)).card

/-- `S` is a forest on `V`: edges plus components equal vertices. -/
def IsForest (V : Finset ℕ) (S : Finset (Sym2 ℕ)) : Prop :=
  S ⊆ pairs V ∧ S.card + ncomp V S = V.card

open Classical in
/-- Contraction of each `S`-block to its representative (summed types and incidences). -/
noncomputable def Config.contractBy (Γ : Config L) (S : Finset (Sym2 ℕ)) : Config L where
  V := Γ.V.image (rep Γ.V S)
  t := fun r => ∑ u ∈ Γ.V.filter (fun u => rep Γ.V S u = r), Γ.t u
  z := fun r r' => ∑ u ∈ Γ.V.filter (fun u => rep Γ.V S u = r),
    ∑ u' ∈ Γ.V.filter (fun u' => rep Γ.V S u' = r'), Γ.z u u'

/-- Aux-incident network edges present in `Γ` (bit one), `X` the auxiliary vertices. -/
def netEdges (Γ : Config L) (T X : Finset ℕ) : Finset (Sym2 ℕ) :=
  ((X ×ˢ (T ∪ X)).filter (fun p => p.1 ≠ p.2 ∧ Γ.z p.1 p.2 = 1)).image (fun p => s(p.1, p.2))

/-- Rooted forests of the network: forests on `T ∪ X` in which every auxiliary vertex is
connected to a terminal (tex 2635–2640). -/
def IsRootedForest (T X : Finset ℕ) (S : Finset (Sym2 ℕ)) : Prop :=
  IsForest (T ∪ X) S ∧ ∀ x ∈ X, ∃ a ∈ T, conn S x a

open Classical in
/-- The star spanning forest, on `T`, of the terminal partition induced by `S`. -/
noncomputable def starForest (T : Finset ℕ) (S : Finset (Sym2 ℕ)) : Finset (Sym2 ℕ) :=
  (T.filter (fun a => rep T S a ≠ a)).image (fun a => s(rep T S a, a))

open Classical in
/-- **The network operator** (tex 2635–2655): the sum over rooted forests of the forest
difference of their terminal partition. -/
noncomputable def netOp (Γ : Config L) (T X : Finset ℕ) : MvPolynomial (Sym2 ℕ) (ZMod 2) :=
  ∑ S ∈ (netEdges Γ T X).powerset.filter (IsRootedForest T X),
    ∏ e ∈ starForest T S, MvPolynomial.X e

open Classical in
/-- Action of a polynomial in the differences on a Boolean function of flip sets:
`X^m` acts by the iterated difference over `supp m` when `m` is squarefree, else by `0`. -/
noncomputable def act (p : MvPolynomial (Sym2 ℕ) (ZMod 2))
    (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) : ZMod 2 :=
  ∑ m ∈ p.support, p.coeff m *
    (if ∀ e, m e ≤ 1 then ∑ W ∈ m.support.powerset, f (symmDiff U W) else 0)

/-- Grounded Laplacian of the network on `X` over `ZMod 2` (tex 2641). -/
noncomputable def lap (Γ : Config L) (T X : Finset ℕ) : Matrix X X (ZMod 2) :=
  fun i j => if i = j then ∑ u ∈ (T ∪ X).erase i, Γ.z i u else Γ.z i j

/-- Attachment column of the terminal `a` (tex 2641). -/
def attach (Γ : Config L) (X : Finset ℕ) (a : ℕ) : X → ZMod 2 := fun i => Γ.z i a

/-! ### Addresses (`ex:sec7-address`, tex 2209–2220) -/

/-- Presence at an address: `none` is stationary; `some w` is present when `w ⬝ x = 1`. -/
def present {b : ℕ} (act' : ℕ → Option (Fin b → ZMod 2)) (x : Fin b → ZMod 2) (v : ℕ) : Prop :=
  match act' v with
  | none => True
  | some w => (∑ i, w i * x i) = 1

open Classical in
/-- The active configuration at address `x`. -/
noncomputable def Config.at {b : ℕ} (Γ : Config L) (act' : ℕ → Option (Fin b → ZMod 2))
    (x : Fin b → ZMod 2) : Config L :=
  { Γ with V := Γ.V.filter (present act' x) }

/-- `Γ'` extends `Γ`: original vertices, types and mutual bits unchanged. -/
def Config.Extends (Γ Γ' : Config L) : Prop :=
  Γ.V ⊆ Γ'.V ∧ (∀ v ∈ Γ.V, Γ'.t v = Γ.t v) ∧ ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, Γ'.z v w = Γ.z v w

end ZInQ.Manuscript.RC.Symbols

/-
NOS-CORE PROBE STAGING COPY (nos-core-probe-001, lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.lean
  Source sha256  : cf45b781c4ce0c79191d312207f2c89d16b76a89b45c14be5ea7118bb00435b8
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 33 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 15 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 1600000`; `set_option maxHeartbeats 6400000 in`; `set_option maxHeartbeats 16000000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 8 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

/-
H4 L2 C4-assigned NOS default-limit edition001, 2026-11-17.
Base5acd9423ce02a929ebaaa62538860ddf32044f40d57823d08bb865fa4b820c01.
Full Parent compile probe log read: two heartbeat sites, map_rawHom_comp_legIso and
asm_bZ; the final unknown constant is downstream fallout. Instantiate head'
with the actual named base-change maps/equalities instead of repeatedly reducing
chosen-pullback record projections. Split actual local-rigidified descent-data
isomorphism construction from generic equivalence transport and lifting along
the actual open-cover hom bijections. The original theorem statements, maps,
imports, attribution and every NON-numeric option are retained from base.
No numeric limit, import, caller Fact or admission is introduced. Source only:
parent probes and C4 binds; no lane native/default/kernel/Std3 success claimed.
-/

/-
Default-limit proof revision, 2026-11-17, edition 002.
The transition/rigidification comparison now uses explicit rewrite equalities
for its composition isomorphisms and square comparisons instead of a large
definitional conversion. Construction of the compatible descent isomorphism
is performed on symbolic pullback data before specialization to the line bundles.
Original statements, imports, attribution and non-numeric options are unchanged.
The preceding edition is retained; this revision requires a fresh compile check.
-/

/-
Default-limit proof revision, 2026-11-17, edition 003.
At the two transition comparison seams, explicitly rewrite the pseudofunctor's
map functor to the actual pullback functor and normalize composite objects.
This aligns the morphism categories while retaining the preceding coherence
and descent proofs. No declaration statement, import or option is changed.
-/

/-
Default-limit proof revision, 2026-11-17, edition 004.
The symbolic transition comparisons now use direct equality proofs, without
post-simplification type matching. The first applies the composition-isomorphism
equality directly; the second composes it with the defining transition equality.
Statements, imports, options and the preceding coherence proofs are unchanged.
-/

/-
Default-limit proof revision, 2026-11-17, edition 005.
Projection equalities are substituted while the chosen pullback is symbolic.
The comparison transports the dependent hom carriers explicitly, then recovers
the original ordinary equality on the common carrier. Its specialization uses
proved projection equalities rather than reducing the concrete pullback fields.
Statements, imports, options and preceding proof history are unchanged.
-/

/-
Default-limit proof revision, 2026-11-17, edition 006.
The transition comparison is split into projection specialization, dependent
identification on an explicit common hom carrier, and ordinary equality recovery.
Each step has its own theorem boundary; the final equation uses only the proved
identification. Statements, imports, options and earlier editions are unchanged.
-/

/-
Default-limit proof revision, 2026-11-17, edition 007.
Comparison components are retyped once on abstract functors, with nested-object
source and target types. Added transition and leg comparison helpers use these
components; a generic coherence lemma handles their composition before geometric
specialization. Every base declaration statement, import and option is retained.
Earlier editions remain unchanged; the new helper presentation requires checking.
-/

/-
Default-limit proof revision, 2026-11-17, edition 008.
The symbolic transition comparison transports the pullback object before its
leg maps. Its specialization supplies a separately proved object equality and
heterogeneous projection equalities at the exact target domain. Nested component
typing and every base statement, import and non-numeric option are retained.
Earlier editions are preserved; this revision awaits the diagnostic decision.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
r2nos_namespace_dual

set_option autoImplicit false

universe u v

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pseudofunctor Scheme.Modules.pullback Scheme.Pullback.range_fst Spec Scheme IsOpenImmersion Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RigidifiedLineBundle Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq Scheme.Modules.toDescentData_map_bijective_of_openCover Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Modules.pseudofunctor ringCatSheaf Modules.pullback Γ Pullback.range_fst Modules.pullbackCongr Modules Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.algebraOfHom Modules.toDescentData_map_bijective_of_openCover Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "pseudofunctor pullback pullbackCongr pullbackComp IsInvertible pullbackUnitIso toDescentData_map_bijective_of_openCover pullbackComp_pullbackCongr_pasteSquares_app"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

section NestedComponents

variable {𝓐 𝓑 𝓒 : Type*} [Category 𝓐] [Category 𝓑] [Category 𝓒]

/-- Type a composite comparison component in nested-object form while its
functors are symbolic. -/
def isoCompHomApp {F : 𝓐 ⥤ 𝓑} {G : 𝓑 ⥤ 𝓒} {H : 𝓐 ⥤ 𝓒}
    (e : F ⋙ G ≅ H) (X : 𝓐) : G.obj (F.obj X) ⟶ H.obj X := e.hom.app X

def isoCompInvApp {F : 𝓐 ⥤ 𝓑} {G : 𝓑 ⥤ 𝓒} {H : 𝓐 ⥤ 𝓒}
    (e : F ⋙ G ≅ H) (X : 𝓐) : H.obj X ⟶ G.obj (F.obj X) := e.inv.app X

lemma isoCompHomApp_eq {F : 𝓐 ⥤ 𝓑} {G : 𝓑 ⥤ 𝓒} {H : 𝓐 ⥤ 𝓒}
    (e : F ⋙ G ≅ H) (X : 𝓐) : isoCompHomApp e X = e.hom.app X := rfl

lemma isoCompInvApp_eq {F : 𝓐 ⥤ 𝓑} {G : 𝓑 ⥤ 𝓒} {H : 𝓐 ⥤ 𝓒}
    (e : F ⋙ G ≅ H) (X : 𝓐) : isoCompInvApp e X = e.inv.app X := rfl

lemma isoCompHomApp_invApp_id {F : 𝓐 ⥤ 𝓑} {G : 𝓑 ⥤ 𝓒} {H : 𝓐 ⥤ 𝓒}
    (e : F ⋙ G ≅ H) (X : 𝓐) : isoCompHomApp e X ≫ isoCompInvApp e X = 𝟙 _ :=
  (e.app X).hom_inv_id

lemma isoCompInvApp_homApp_id {F : 𝓐 ⥤ 𝓑} {G : 𝓑 ⥤ 𝓒} {H : 𝓐 ⥤ 𝓒}
    (e : F ⋙ G ≅ H) (X : 𝓐) : isoCompInvApp e X ≫ isoCompHomApp e X = 𝟙 _ :=
  (e.app X).inv_hom_id

end NestedComponents

section NestedSquares

variable {𝓐 𝓑₁ 𝓑₂ 𝓒 : Type*}
  [Category 𝓐] [Category 𝓑₁] [Category 𝓑₂] [Category 𝓒]

/-- Type both sides of a square comparison in nested-object form. -/
def isoSquareHomApp {F₁ : 𝓐 ⥤ 𝓑₁} {G₁ : 𝓑₁ ⥤ 𝓒}
    {F₂ : 𝓐 ⥤ 𝓑₂} {G₂ : 𝓑₂ ⥤ 𝓒}
    (e : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂) (X : 𝓐) :
    G₁.obj (F₁.obj X) ⟶ G₂.obj (F₂.obj X) := e.hom.app X

lemma isoSquareHomApp_eq {F₁ : 𝓐 ⥤ 𝓑₁} {G₁ : 𝓑₁ ⥤ 𝓒}
    {F₂ : 𝓐 ⥤ 𝓑₂} {G₂ : 𝓑₂ ⥤ 𝓒}
    (e : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂) (X : 𝓐) : isoSquareHomApp e X = e.hom.app X := rfl

/-- Transport a pair of comparison components before specializing its functors. -/
lemma isoCompPair_heq {F₁ : 𝓐 ⥤ 𝓑₁} {G₁ : 𝓑₁ ⥤ 𝓒}
    {F₂ : 𝓐 ⥤ 𝓑₂} {G₂ : 𝓑₂ ⥤ 𝓒} {H : 𝓐 ⥤ 𝓒}
    (e₁ : F₁ ⋙ G₁ ≅ H) (e₂ : F₂ ⋙ G₂ ≅ H) (X : 𝓐) :
    HEq (e₁.hom.app X ≫ e₂.inv.app X)
      (isoCompHomApp e₁ X ≫ isoCompInvApp e₂ X) := by
  rfl

end NestedSquares

section NestedLeg

variable {𝓐 𝓑 𝓒 𝓓 𝓔 𝓕 : Type*}
  [Category 𝓐] [Category 𝓑] [Category 𝓒] [Category 𝓓] [Category 𝓔] [Category 𝓕]

/-- Compute a three-comparison leg in nested carriers using abstract functors. -/
lemma isoLegHomApp {q : 𝓐 ⥤ 𝓑} {a : 𝓑 ⥤ 𝓒}
    {s : 𝓐 ⥤ 𝓓} {s₁ : 𝓑 ⥤ 𝓔} {s₀ : 𝓒 ⥤ 𝓕}
    {p : 𝓓 ⥤ 𝓔} {r : 𝓔 ⥤ 𝓕} {m : 𝓓 ⥤ 𝓕}
    (eρ : a ⋙ s₀ ≅ s₁ ⋙ r) (eψ : q ⋙ s₁ ≅ s ⋙ p) (em : p ⋙ r ≅ m) (X : 𝓐) :
    (show s₀.obj (a.obj (q.obj X)) ≅ m.obj (s.obj X) from
      eρ.app (q.obj X) ≪≫ r.mapIso (eψ.app X) ≪≫ em.app (s.obj X)).hom =
      isoSquareHomApp eρ (q.obj X) ≫ r.map (isoSquareHomApp eψ X) ≫
        isoCompHomApp em (s.obj X) := by
  rfl

end NestedLeg

section NestedHead

variable {𝓐 𝓑₁ 𝓑₂ 𝓒 𝓓 𝓔₁ 𝓔₂ 𝓕 : Type*}
  [Category 𝓐] [Category 𝓑₁] [Category 𝓑₂] [Category 𝓒]
  [Category 𝓓] [Category 𝓔₁] [Category 𝓔₂] [Category 𝓕]

/-- Retype a coherence equation on abstract functors, before substituting
geometric pullback functors into its nested-object conclusion. -/
lemma isoHeadApp {q₁ : 𝓐 ⥤ 𝓑₁} {q₂ : 𝓐 ⥤ 𝓑₂}
    {a₁ : 𝓑₁ ⥤ 𝓒} {a₂ : 𝓑₂ ⥤ 𝓒} {d : 𝓐 ⥤ 𝓒}
    {s₀ : 𝓒 ⥤ 𝓕} {s₁ : 𝓑₁ ⥤ 𝓔₁} {s₂ : 𝓑₂ ⥤ 𝓔₂} {s : 𝓐 ⥤ 𝓓}
    {r₁ : 𝓔₁ ⥤ 𝓕} {r₂ : 𝓔₂ ⥤ 𝓕} {p₁ : 𝓓 ⥤ 𝓔₁} {p₂ : 𝓓 ⥤ 𝓔₂} {m : 𝓓 ⥤ 𝓕}
    (ea₁ : q₁ ⋙ a₁ ≅ d) (ea₂ : q₂ ⋙ a₂ ≅ d)
    (es₁ : a₁ ⋙ s₀ ≅ s₁ ⋙ r₁) (es₂ : a₂ ⋙ s₀ ≅ s₂ ⋙ r₂)
    (ep₁ : q₁ ⋙ s₁ ≅ s ⋙ p₁) (ep₂ : q₂ ⋙ s₂ ≅ s ⋙ p₂)
    (eg₁ : p₁ ⋙ r₁ ≅ m) (eg₂ : p₂ ⋙ r₂ ≅ m) (X : 𝓐)
    (h : s₀.map (ea₁.hom.app X ≫ ea₂.inv.app X) ≫
        es₂.hom.app (q₂.obj X) ≫ r₂.map (ep₂.hom.app X) ≫ eg₂.hom.app (s.obj X) =
      es₁.hom.app (q₁.obj X) ≫ r₁.map (ep₁.hom.app X) ≫ eg₁.hom.app (s.obj X)) :
    s₀.map (isoCompHomApp ea₁ X ≫ isoCompInvApp ea₂ X) ≫
        isoSquareHomApp es₂ (q₂.obj X) ≫ r₂.map (isoSquareHomApp ep₂ X) ≫
          isoCompHomApp eg₂ (s.obj X) =
      isoSquareHomApp es₁ (q₁.obj X) ≫ r₁.map (isoSquareHomApp ep₁ X) ≫
        isoCompHomApp eg₁ (s.obj X) := by
  simpa only [isoCompHomApp, isoCompInvApp, isoSquareHomApp] using h

end NestedHead

variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

noncomputable def τ (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) : pullback g ⋙ pullback f ≅ pullback m :=
  pullbackComp f g ≪≫ pullbackCongr e

theorem τ_hom_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).hom.app M = (pullbackComp f g).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  simp [τ, pullbackCongr]

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (pullbackComp f g).inv.app M := by
  subst e
  simp [τ, pullbackCongr]

noncomputable def sqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) : pullback g ⋙ pullback f ≅ pullback k ⋙ pullback h :=
  pullbackComp f g ≪≫ pullbackCongr e ≪≫ (pullbackComp h k).symm

theorem sqIso_hom_app {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) (M : Z.Modules) :
    (sqIso e).hom.app M = (τ f g (h ≫ k) e).hom.app M ≫ (τ h k (h ≫ k) rfl).inv.app M := by
  simp [sqIso, τ, pullbackCongr]

section Route

variable {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
  (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
  (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
  (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s)

include e G E F in
theorem route_comm : s₀ ≫ d = m ≫ s := by
  rw [← e, ← Category.assoc, E, Category.assoc, F, ← Category.assoc, G]

theorem route (M : X.Modules) :
    (sqIso E).hom.app ((pullback b).obj M) ≫ (pullback r).map ((sqIso F).hom.app M) ≫
        (τ r p m G).hom.app ((pullback s).obj M) =
      (pullback s₀).map ((τ a b d e).hom.app M) ≫
        (τ s₀ d (m ≫ s) (route_comm a b d e s₀ s₁ s r p m G E F)).hom.app M ≫
          (τ m s (m ≫ s) rfl).inv.app M := by
  exact (AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app a b d e s₀ s₁ s r p m G E F
    (route_comm a b d e s₀ s₁ s r p m G E F) M).trans
    (congrArg (fun k => (pullback s₀).map ((τ a b d e).hom.app M) ≫ k)
      (sqIso_hom_app (route_comm a b d e s₀ s₁ s r p m G E F) M))

end Route

section Head

variable {X X₀' X₁' X₂' Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head (M : X.Modules) :
    (pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M) ≫
      (sqIso E₂).hom.app ((pullback b₂).obj M) ≫ (pullback r₂).map ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((pullback s).obj M) =
      (sqIso E₁).hom.app ((pullback b₁).obj M) ≫ (pullback r₁).map ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((pullback s).obj M) := by
  have h₁ := route a₁ b₁ d e₁ s₀ s₁ s r₁ p₁ m G₁ E₁ F₁ M
  have h₂ := route a₂ b₂ d e₂ s₀ s₂ s r₂ p₂ m G₂ E₂ F₂ M
  have h₂' := (Iso.inv_comp_eq ((pullback s₀).mapIso ((τ a₂ b₂ d e₂).app M))).mpr h₂
  simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun k => (pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M) ≫ k) h₂').trans h₁.symm

end Head

section HeadRaw

variable {X X₀' X₁' X₂' : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)

theorem τ_hom_app_comp_τ_inv_app (M : X.Modules) :
    (τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M =
      (pullbackComp a₁ b₁).hom.app M ≫ (pullbackCongr e₁).hom.app M ≫ (pullbackCongr e₂.symm).hom.app M ≫
        (pullbackComp a₂ b₂).inv.app M := by
  subst e₁
  simp [τ, pullbackCongr]

variable {Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head' (M : X.Modules) :
    (pullback s₀).map ((pullbackComp a₁ b₁).hom.app M ≫ (pullbackCongr e₁).hom.app M ≫
        (pullbackCongr e₂.symm).hom.app M ≫ (pullbackComp a₂ b₂).inv.app M) ≫
      (sqIso E₂).hom.app ((pullback b₂).obj M) ≫ (pullback r₂).map ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((pullback s).obj M) =
      (sqIso E₁).hom.app ((pullback b₁).obj M) ≫ (pullback r₁).map ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((pullback s).obj M) := by
  have h := head a₁ b₁ a₂ b₂ d e₁ e₂ s₀ s₁ s₂ s r₁ p₁ r₂ p₂ m G₁ G₂ E₁ F₁ E₂ F₂ M
  rw [τ_hom_app_comp_τ_inv_app] at h
  exact h

end HeadRaw

end AlgebraicGeometry.Scheme.Modules

noncomputable section
namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pseudofunctor Scheme.Modules.pullback Scheme.Pullback.range_fst Spec Scheme IsOpenImmersion Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RigidifiedLineBundle Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq Scheme.Modules.toDescentData_map_bijective_of_openCover Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace RelPicard
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_comp rigSection_baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq"
namespace DescentAux
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

open NeronModelInfra
r2nos_open_dual "NeronModelInfra"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

lemma isPullback_baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
  have big : IsPullback (baseChangeSnd c ψ ≫ pullback.fst c t) (pullback.snd c t') c (ψ.1 ≫ t) := by
    rw [ψ.2, show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
    exact IsPullback.of_hasPullback c t'
  exact big.of_right ((pullback.lift_snd _ _ _)) (IsPullback.of_hasPullback c t)

lemma isPullback_baseChangeSnd {X U V W : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)}
    {uS : U ⟶ Spec (CommRingCat.of R)} {vS : V ⟶ Spec (CommRingCat.of R)} {wS : W ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver uS x) (v : SchemeHomOver vS x) (a : SchemeHomOver wS uS) (b : SchemeHomOver wS vS)
    (h : IsPullback a.1 b.1 u.1 v.1) :
    IsPullback (baseChangeSnd c a) (baseChangeSnd c b) (baseChangeSnd c u) (baseChangeSnd c v) := by
  have hbig : IsPullback (pullback.snd c wS ≫ a.1) (baseChangeSnd c b) u.1 (pullback.snd c vS ≫ v.1) :=
    (isPullback_baseChangeSnd_snd c b).flip.paste_horiz h
  have hbig' : IsPullback (baseChangeSnd c a ≫ pullback.snd c uS) (baseChangeSnd c b) u.1
      (baseChangeSnd c v ≫ pullback.snd c x) := by
    rw [show baseChangeSnd c a ≫ pullback.snd c uS = pullback.snd c wS ≫ a.1 from pullback.lift_snd _ _ _,
      show baseChangeSnd c v ≫ pullback.snd c x = pullback.snd c vS ≫ v.1 from pullback.lift_snd _ _ _]
    exact hbig
  refine hbig'.of_right ?_ (isPullback_baseChangeSnd_snd c u).flip
  rw [baseChangeSnd_comp, baseChangeSnd_comp]
  congr 1
  exact Subtype.ext h.w

abbrev strMap₁₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    pullback ψ₁.1 ψ₂.1 ⟶ Spec (CommRingCat.of R) :=
  pullback.fst ψ₁.1 ψ₂.1 ≫ t₁

def pr₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₁ :=
  ⟨pullback.fst ψ₁.1 ψ₂.1, rfl⟩

def pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₂ :=
  ⟨pullback.snd ψ₁.1 ψ₂.1, by
    have h2 : pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 ≫ t = pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ := by rw [ψ₂.2]
    have h1 : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 ≫ t = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁ := by rw [ψ₁.2]
    change pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁
    rw [← h2, ← h1, ← Category.assoc, ← pullback.condition, Category.assoc]⟩

@[scoped simp] lemma pr₁_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₁ ψ₁ ψ₂).1 = pullback.fst ψ₁.1 ψ₂.1 := rfl

@[scoped simp] lemma pr₂_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₂ ψ₁ ψ₂).1 = pullback.snd ψ₁.1 ψ₂.1 := rfl

lemma postComp_pr₁_eq_postComp_pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    postComp ψ₁ (pr₁ ψ₁ ψ₂) = postComp ψ₂ (pr₂ ψ₁ ψ₂) :=
  Subtype.ext pullback.condition

def chosenPullback {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    ChosenPullback (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) where
  pullback := Limits.pullback c (strMap₁₂ ψ₁ ψ₂)
  p₁ := baseChangeSnd c (pr₁ ψ₁ ψ₂)
  p₂ := baseChangeSnd c (pr₂ ψ₁ ψ₂)
  condition := by
    rw [baseChangeSnd_comp, baseChangeSnd_comp, postComp_pr₁_eq_postComp_pr₂]
  isLimit := (isPullback_baseChangeSnd c ψ₁ ψ₂ (pr₁ ψ₁ ψ₂) (pr₂ ψ₁ ψ₂)
    (IsPullback.of_hasPullback ψ₁.1 ψ₂.1)).isLimit
  p := baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂))
  hp₁ := baseChangeSnd_comp c _ _

@[scoped simp] lemma chosenPullback_p₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p₁ = baseChangeSnd c (pr₁ ψ₁ ψ₂) := rfl

@[scoped simp] lemma chosenPullback_p₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p₂ = baseChangeSnd c (pr₂ ψ₁ ψ₂) := rfl

def chosenPullback₃ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    ChosenPullback₃ (chosenPullback c ψ ψ) (chosenPullback c ψ ψ) (chosenPullback c ψ ψ) where
  chosenPullback := chosenPullback c (pr₂ ψ ψ) (pr₁ ψ ψ)
  p := baseChangeSnd c (postComp (postComp ψ (pr₁ ψ ψ)) (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ ψ) (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ ψ) (pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  l :=
    { f := baseChangeSnd c
        ⟨pullback.lift ((pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)).1 ≫ (pr₁ ψ ψ).1) ((pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)).1 ≫ (pr₂ ψ ψ).1)
          (by
            have hT₂ : pullback.fst ψ.1 ψ.1 ≫ ψ.1 = pullback.snd ψ.1 ψ.1 ≫ ψ.1 := pullback.condition
            have hT₃ : pullback.fst (pullback.snd ψ.1 ψ.1) (pullback.fst ψ.1 ψ.1) ≫ pullback.snd ψ.1 ψ.1 =
                pullback.snd (pullback.snd ψ.1 ψ.1) (pullback.fst ψ.1 ψ.1) ≫ pullback.fst ψ.1 ψ.1 :=
              pullback.condition
            simp only [pr₁_val, pr₂_val, Category.assoc]
            rw [hT₂, ← Category.assoc, hT₃, Category.assoc, hT₂]),
         by
          simp only [pr₁_val, pr₂_val]
          rw [← Category.assoc, pullback.lift_fst, Category.assoc]
          rfl⟩
      f_p₁ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₁ ψ ψ) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_fst _ _ _)
      f_p₂ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₂ ψ ψ) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_snd _ _ _)
      f_p := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (postComp ψ (pr₁ ψ ψ)) = _
        erw [baseChangeSnd_comp]; congr 1
        exact Subtype.ext (by
          change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ.1 = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ ψ.1
          rw [pullback.lift_fst_assoc, Category.assoc]
          rfl) }
  hp₁ := by
    change baseChangeSnd c (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)) ≫ baseChangeSnd c (pr₁ ψ ψ) = _
    erw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)) ≫ baseChangeSnd c (pr₂ ψ ψ) = _
    erw [baseChangeSnd_comp]

end AlgebraicGeometry.RelPicard.DescentAux
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux"
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard"
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry"
end
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux"

noncomputable section
namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pseudofunctor Scheme.Modules.pullback Scheme.Pullback.range_fst Spec Scheme IsOpenImmersion Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RigidifiedLineBundle Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq Scheme.Modules.toDescentData_map_bijective_of_openCover Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace RelPicard
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_comp rigSection_baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq"
namespace DescentAux
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

w03_open "NeronModelInfra AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.Scheme.Modules"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

structure RigData {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) where
  L : (Limits.pullback c t).Modules
  isInvertible : Scheme.Modules.IsInvertible L
  α : (Scheme.Modules.pullback (rigSection c t ε)).obj L ≅ SheafOfModules.unit T.ringCatSheaf

namespace RigData
r2nos_namespace_dual

variable {c ε} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

def Compat (A B : RigData c ε t) (φ : A.L ⟶ B.L) : Prop :=
  (Scheme.Modules.pullback (rigSection c t ε)).map φ ≫ B.α.hom = A.α.hom

lemma Compat.id (A : RigData c ε t) : Compat A A (𝟙 A.L) := by
  simp [Compat]

lemma Compat.comp {A B D : RigData c ε t} {φ : A.L ⟶ B.L} {ψ : B.L ⟶ D.L} (hφ : Compat A B φ)
    (hψ : Compat B D ψ) : Compat A D (φ ≫ ψ) := by
  simp only [Compat, Functor.map_comp, Category.assoc] at *
  rw [hψ, hφ]

lemma compat_iff_mapIso (A B : RigData c ε t) (φ : A.L ≅ B.L) :
    Compat A B φ.hom ↔ (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ B.α = A.α := by
  constructor
  · intro h; ext : 1; first | exact h | simpa using h | simpa [Compat] using h
  · intro h; first | exact congrArg Iso.hom h | simpa using congrArg Iso.hom h | simpa [Compat] using congrArg Iso.hom h

lemma Compat.inv {A B : RigData c ε t} {φ : A.L ≅ B.L} (h : Compat A B φ.hom) : Compat B A φ.inv := by
  simp only [Compat] at *
  rw [← h, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

def ofIso (A : RigData c ε t) (L' : (Limits.pullback c t).Modules) (e : L' ≅ A.L)
    (hL' : Scheme.Modules.IsInvertible L') : RigData c ε t where
  L := L'
  isInvertible := hL'
  α := (Scheme.Modules.pullback (rigSection c t ε)).mapIso e ≪≫ A.α

lemma ofIso_compat_iff {A B : RigData c ε t} {LA LB : (Limits.pullback c t).Modules} (eA : LA ≅ A.L) (eB : LB ≅ B.L)
    (hA : Scheme.Modules.IsInvertible LA) (hB : Scheme.Modules.IsInvertible LB) (φ : LA ⟶ LB) :
    Compat (A.ofIso LA eA hA) (B.ofIso LB eB hB) φ ↔ Compat A B (eA.inv ≫ φ ≫ eB.hom) := by
  simp only [Compat, ofIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  constructor
  · intro h
    rw [h, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · intro h
    rw [← cancel_epi ((Scheme.Modules.pullback (rigSection c t ε)).map eA.inv), ← Category.assoc,
      ← Functor.map_comp] at *
    simpa using h

def rigNatIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Scheme.Modules.pullback (baseChangeSnd c ψ) ⋙ Scheme.Modules.pullback (rigSection c t' ε) ≅
      Scheme.Modules.pullback (rigSection c t ε) ⋙ Scheme.Modules.pullback ψ.1 :=
  Scheme.Modules.pullbackComp (rigSection c t' ε) (baseChangeSnd c ψ) ≪≫
    Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ψ) ≪≫
    (Scheme.Modules.pullbackComp ψ.1 (rigSection c t ε)).symm

/-- The rigidification comparison is the square comparison for the literal
unit-section/base-change square. -/
lemma rigNatIso_eq_sqIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    rigNatIso (c := c) (ε := ε) ψ =
      Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε ψ) := rfl

def pb (A : RigData c ε t) {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    RigData c ε t' where
  L := (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A.L
  isInvertible := A.isInvertible.pullback _
  α := (rigNatIso ψ).app A.L ≪≫ (Scheme.Modules.pullback ψ.1).mapIso A.α ≪≫ Scheme.Modules.pullbackUnitIso ψ.1

@[scoped simp] lemma pb_L (A : RigData c ε t) {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : (A.pb ψ).L = (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A.L := rfl

lemma Compat.pb {A B : RigData c ε t} {φ : A.L ⟶ B.L} (h : Compat A B φ) {T' : Scheme.{u}}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Compat (A.pb ψ) (B.pb ψ) ((Scheme.Modules.pullback (baseChangeSnd c ψ)).map φ) := by
  simp only [Compat, RigData.pb, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h ⊢
  have hn := (rigNatIso (c := c) (ε := ε) ψ).hom.naturality φ
  simp only [Functor.comp_map] at hn
  have hn' := hn =≫ ((Scheme.Modules.pullback ψ.1).map B.α.hom ≫ (Scheme.Modules.pullbackUnitIso ψ.1).hom)
  simp only [Category.assoc] at hn'
  refine hn'.trans ?_
  have h2 := congrArg (fun k => (rigNatIso (c := c) (ε := ε) ψ).hom.app A.L ≫
    (Scheme.Modules.pullback ψ.1).map k ≫ (Scheme.Modules.pullbackUnitIso ψ.1).hom) h
  simp only [Functor.map_comp, Category.assoc] at h2
  exact h2

end RigData
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

end AlgebraicGeometry.RelPicard.DescentAux
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
end
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

noncomputable section
namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pseudofunctor Scheme.Modules.pullback Scheme.Pullback.range_fst Spec Scheme IsOpenImmersion Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RigidifiedLineBundle Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq Scheme.Modules.toDescentData_map_bijective_of_openCover Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace RelPicard
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_comp rigSection_baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq"
namespace DescentAux
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

open NeronModelInfra CategoryTheory.Pseudofunctor
r2nos_open_dual "NeronModelInfra CategoryTheory.Pseudofunctor"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

namespace RigData
r2nos_namespace_dual
variable {c ε} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

def ofRLB (M : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf) :
    RigData c ε t := ⟨M.L, M.isInvertible, α⟩

def toRLB (A : RigData c ε t) : RigidifiedLineBundle c ε t := ⟨A.L, A.isInvertible, ⟨A.α⟩⟩

lemma exists_compat_iso (A B : RigData c ε t) (h : Nonempty (A.L ≅ B.L)) :
    ∃ φ : A.L ≅ B.L, Compat A B φ.hom := by
  obtain ⟨φ, hφ⟩ := AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
    R c ε t A.toRLB B.toRLB A.α B.α h.some
  exact ⟨φ, (compat_iff_mapIso A B φ).mpr hφ⟩

lemma compat_iso_unique
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A B : RigData c ε t) (φ ψ : A.L ≅ B.L) (hφ : Compat A B φ.hom) (hψ : Compat A B ψ.hom) : φ = ψ :=
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq R c ε hH0 t
    A.toRLB B.toRLB A.α B.α φ ψ ((compat_iff_mapIso A B φ).mp hφ) ((compat_iff_mapIso A B ψ).mp hψ)

lemma compat_hom_unique
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A B : RigData c ε t) (φ ψ : A.L ⟶ B.L) [IsIso φ] [IsIso ψ] (hφ : Compat A B φ) (hψ : Compat A B ψ) :
    φ = ψ :=
  congrArg Iso.hom (compat_iso_unique hH0 A B (asIso φ) (asIso ψ) hφ hψ)

end RigData
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

@[scoped simp] lemma chosenPullback_p {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) := rfl

def chosenPullback₃' {T T₁ T₂ T₃ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} {t₃ : T₃ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) (ψ₃ : SchemeHomOver t₃ t) :
    ChosenPullback₃ (chosenPullback c ψ₁ ψ₂) (chosenPullback c ψ₂ ψ₃) (chosenPullback c ψ₁ ψ₃) where
  chosenPullback := chosenPullback c (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)
  p := baseChangeSnd c (postComp (postComp ψ₁ (pr₁ ψ₁ ψ₂)) (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ₁ ψ₂) (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ₂ ψ₃) (pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  l :=
    { f := baseChangeSnd c
        ⟨pullback.lift ((pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)).1 ≫ (pr₁ ψ₁ ψ₂).1)
            ((pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)).1 ≫ (pr₂ ψ₂ ψ₃).1)
          (by
            have h₁₂ : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 = pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 := pullback.condition
            have h₂₃ : pullback.fst ψ₂.1 ψ₃.1 ≫ ψ₂.1 = pullback.snd ψ₂.1 ψ₃.1 ≫ ψ₃.1 := pullback.condition
            have h' : pullback.fst (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1) ≫ pullback.snd ψ₁.1 ψ₂.1 =
                pullback.snd (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1) ≫ pullback.fst ψ₂.1 ψ₃.1 :=
              pullback.condition
            simp only [pr₁_val, pr₂_val, Category.assoc]
            rw [h₁₂, ← Category.assoc, h', Category.assoc, h₂₃]),
         by
          simp only [pr₁_val, pr₂_val]
          rw [← Category.assoc, pullback.lift_fst, Category.assoc]
          rfl⟩
      f_p₁ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₁ ψ₁ ψ₃) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_fst _ _ _)
      f_p₂ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₂ ψ₁ ψ₃) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_snd _ _ _)
      f_p := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₃)) = _
        erw [baseChangeSnd_comp]; congr 1
        exact Subtype.ext (by
          change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ₁.1 = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ ψ₁.1
          rw [pullback.lift_fst_assoc, Category.assoc]
          rfl) }
  hp₁ := by
    change baseChangeSnd c (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) ≫ baseChangeSnd c (pr₁ ψ₁ ψ₂) = _
    erw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) ≫ baseChangeSnd c (pr₂ ψ₂ ψ₃) = _
    erw [baseChangeSnd_comp]

lemma exists_mem_range_baseChangeSnd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {ι : Type u} {U : ι → Scheme.{u}} {uS : ∀ i, U i ⟶ Spec (CommRingCat.of R)} (f : ∀ i, SchemeHomOver (uS i) t)
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base) (y : ↥(Limits.pullback c t)) :
    ∃ i, y ∈ Set.range (baseChangeSnd c (f i)).base := by
  obtain ⟨i, z, hz⟩ := hf ((pullback.snd c t).base y)
  refine ⟨i, ?_⟩
  have H := isPullback_baseChangeSnd_snd c (f i)
  have hy : y ∈ Set.range (pullback.fst (pullback.snd c t) (f i).1).base := by
    have h := Scheme.Pullback.range_fst (pullback.snd c t) (f i).1
    have hy' : y ∈ (pullback.snd c t).base ⁻¹' Set.range (f i).1.base := ⟨z, hz⟩
    rw [← h] at hy'
    exact hy'
  obtain ⟨w, hw⟩ := hy
  refine ⟨H.isoPullback.inv.base w, ?_⟩
  rw [← hw, ← H.isoPullback_inv_fst]
  rfl

section MODsec

abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem modMap_toFunctor {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ((MOD).map g.op.toLoc).toFunctor = Scheme.Modules.pullback g := rfl

theorem modMapComp'_eq_mapComp_app {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u : a ⟶ b) (v : b ⟶ d) (M : (MOD).obj a) :
    ((MOD).mapComp' u v (u ≫ v) rfl).hom.toNatTrans.app M = ((MOD).mapComp u v).hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem modMapComp'_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    ((MOD).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
      (Scheme.Modules.pullbackCongr h.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact modMapComp'_eq_mapComp_app g.op.toLoc f.op.toLoc L

theorem modMapComp'_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    ((MOD).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app L =
      (Scheme.Modules.pullbackComp f g).hom.app L ≫ (Scheme.Modules.pullbackCongr h).hom.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  have h2 : ((MOD).mapComp' g.op.toLoc f.op.toLoc (g.op.toLoc ≫ f.op.toLoc) rfl).inv.toNatTrans.app L =
      ((MOD).mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app L := by
    rw [Pseudofunctor.mapComp'_eq_mapComp]
  exact h2

def transHom₂ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (cp : ChosenPullback q₁ q₂) (L : S.Modules) :
    ((MOD).map cp.p₁.op.toLoc).toFunctor.obj (((MOD).map q₁.op.toLoc).toFunctor.obj L) ⟶
      ((MOD).map cp.p₂.op.toLoc).toFunctor.obj (((MOD).map q₂.op.toLoc).toFunctor.obj L) :=
  (Scheme.Modules.pullbackComp cp.p₁ q₁).hom.app L ≫ (Scheme.Modules.pullbackCongr cp.hp₁).hom.app L ≫
    (Scheme.Modules.pullbackCongr cp.hp₂.symm).hom.app L ≫ (Scheme.Modules.pullbackComp cp.p₂ q₂).inv.app L

scoped instance isIso_transHom₂ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (cp : ChosenPullback q₁ q₂)
    (L : S.Modules) : IsIso (transHom₂ q₁ q₂ cp L) := by
  dsimp only [transHom₂, modMap_toFunctor]
  exact IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _)
    (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (NatIso.inv_app_isIso _ _)))

/-- Express the transition through the two composition isomorphisms while
keeping the chosen pullback symbolic. -/
theorem transHom₂_eq_τ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S)
    (cp : ChosenPullback q₁ q₂) (L : S.Modules) :
    transHom₂ q₁ q₂ cp L =
      Scheme.Modules.isoCompHomApp (Scheme.Modules.τ cp.p₁ q₁ cp.p cp.hp₁) L ≫
        Scheme.Modules.isoCompInvApp (Scheme.Modules.τ cp.p₂ q₂ cp.p cp.hp₂) L := by
  exact eq_of_heq ((heq_of_eq (Scheme.Modules.τ_hom_app_comp_τ_inv_app
    cp.p₁ q₁ cp.p₂ q₂ cp.p cp.hp₁ cp.hp₂ L).symm).trans
      (Scheme.Modules.isoCompPair_heq (Scheme.Modules.τ cp.p₁ q₁ cp.p cp.hp₁)
        (Scheme.Modules.τ cp.p₂ q₂ cp.p cp.hp₂) L))

/-- Substitute the projection equalities on symbolic pullback data. Heterogeneous
 equality transports the dependent pullback-object carriers with the leg maps;
 the specialized comparison recovers ordinary equality on the common carrier. -/
theorem transHom₂_eq_τ_of_eq {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S)
    (cp : ChosenPullback q₁ q₂) (L : S.Modules)
    {P : Scheme.{u}} (hP : cp.pullback = P)
    {a₁ : P ⟶ X₁} {a₂ : P ⟶ X₂} {d : P ⟶ S}
    (h₁ : HEq cp.p₁ a₁) (h₂ : HEq cp.p₂ a₂) (hd : HEq cp.p d)
    (e₁ : a₁ ≫ q₁ = d) (e₂ : a₂ ≫ q₂ = d) :
    HEq (transHom₂ q₁ q₂ cp L)
      (Scheme.Modules.isoCompHomApp (Scheme.Modules.τ (X₀ := P) a₁ q₁ d e₁) L ≫
        Scheme.Modules.isoCompInvApp (Scheme.Modules.τ (X₀ := P) a₂ q₂ d e₂) L) := by
  subst P
  have h₁' : cp.p₁ = a₁ := eq_of_heq h₁
  have h₂' : cp.p₂ = a₂ := eq_of_heq h₂
  have hd' : cp.p = d := eq_of_heq hd
  subst a₁ a₂ d
  exact heq_of_eq (transHom₂_eq_τ q₁ q₂ cp L)

theorem fromDescentData_toDescentData_obj {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j)) (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : S.Modules) (i : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD) sq sq₃).obj (((MOD).toDescentData g).obj L)).obj i =
      ((MOD).map (g i).op.toLoc).toFunctor.obj L := rfl

set_option backward.defeqAttrib.useBackward true in
theorem fromDescentData_toDescentData_hom {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j)) (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : S.Modules) (i j : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD) sq sq₃).obj (((MOD).toDescentData g).obj L)).hom i j =
      transHom₂ (g i) (g j) (sq i j) L := by
  dsimp only [DescentData'.fromDescentDataFunctor_obj, DescentData'.ofDescentData_hom, Pseudofunctor.toDescentData_obj,
    DescentData.ofObj_hom, transHom₂]
  rw [modMapComp'_inv_app (sq i j).p₁ (g i) L (sq i j).p (sq i j).hp₁,
    modMapComp'_hom_app (sq i j).p₂ (g j) L (sq i j).p (sq i j).hp₂]
  exact Category.assoc _ _ _

end MODsec
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

section bridge

variable {c ε}
variable {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
  {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t)

lemma bc_pr₁_comp : baseChangeSnd c (pr₁ ψ₁ ψ₂) ≫ baseChangeSnd c ψ₁ = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) :=
  baseChangeSnd_comp c _ _

lemma bc_pr₂_comp : baseChangeSnd c (pr₂ ψ₁ ψ₂) ≫ baseChangeSnd c ψ₂ = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) := by
  rw [baseChangeSnd_comp, ← postComp_pr₁_eq_postComp_pr₂]

lemma pr₁_comp_val : (pr₁ ψ₁ ψ₂).1 ≫ ψ₁.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 := rfl

lemma pr₂_comp_val : (pr₂ ψ₁ ψ₂).1 ≫ ψ₂.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 := pullback.condition.symm

variable (c) in

def rawHom (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj L) ⟶
      (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj L) :=
  transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L

theorem transHom₂_eq_rawHom (L : (Limits.pullback c t).Modules) :
    transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L = rawHom c ψ₁ ψ₂ L := rfl

/-- Retain the defining transition identification together with its dependent
hom presentations, using the previously proved equality. -/
lemma rawHom_heq_transHom₂ (L : (Limits.pullback c t).Modules) :
    HEq (rawHom c ψ₁ ψ₂ L)
      (transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L) := by
  exact (heq_of_eq (transHom₂_eq_rawHom (c := c) ψ₁ ψ₂ L)).symm

/-- Check the chosen pullback's object presentation independently of the
component comparison and its dependent morphism carriers. -/
lemma chosenPullback_pullback :
    (chosenPullback c ψ₁ ψ₂).pullback = Limits.pullback c (strMap₁₂ ψ₁ ψ₂) := rfl

/-- Check the projection substitution separately from composition of the
transition identifications. The comparison uses the proved leg equations. -/
lemma transHom₂_heq_τ_baseChange (L : (Limits.pullback c t).Modules) :
    HEq (transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂)
      (chosenPullback c ψ₁ ψ₂) L)
      ((Scheme.Modules.isoCompHomApp
        (Scheme.Modules.τ (baseChangeSnd c (pr₁ ψ₁ ψ₂)) (baseChangeSnd c ψ₁)
          (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)))
          (bc_pr₁_comp (c := c) ψ₁ ψ₂)) L) ≫
      (Scheme.Modules.isoCompInvApp
        (Scheme.Modules.τ (baseChangeSnd c (pr₂ ψ₁ ψ₂)) (baseChangeSnd c ψ₂)
          (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)))
          (bc_pr₂_comp (c := c) ψ₁ ψ₂)) L)) := by
  exact transHom₂_eq_τ_of_eq (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂)
    (chosenPullback c ψ₁ ψ₂) L
    (P := Limits.pullback c (strMap₁₂ ψ₁ ψ₂))
    (chosenPullback_pullback (c := c) ψ₁ ψ₂)
    (heq_of_eq (chosenPullback_p₁ (c := c) ψ₁ ψ₂))
    (heq_of_eq (chosenPullback_p₂ (c := c) ψ₁ ψ₂))
    (heq_of_eq (chosenPullback_p (c := c) ψ₁ ψ₂))
    (bc_pr₁_comp (c := c) ψ₁ ψ₂) (bc_pr₂_comp (c := c) ψ₁ ψ₂)

/-- Compose the dependent transition comparisons with both endpoints typed
in the same explicit module-hom carrier. Equality recovery is a separate step. -/
lemma rawHom_heq_τ (L : (Limits.pullback c t).Modules) :
    @HEq
      ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj L) ⟶
        (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj L))
      (rawHom c ψ₁ ψ₂ L)
      ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj L) ⟶
        (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj L))
      ((Scheme.Modules.isoCompHomApp
        (Scheme.Modules.τ (baseChangeSnd c (pr₁ ψ₁ ψ₂)) (baseChangeSnd c ψ₁)
          (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)))
          (bc_pr₁_comp (c := c) ψ₁ ψ₂)) L) ≫
      (Scheme.Modules.isoCompInvApp
        (Scheme.Modules.τ (baseChangeSnd c (pr₂ ψ₁ ψ₂)) (baseChangeSnd c ψ₂)
          (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)))
          (bc_pr₂_comp (c := c) ψ₁ ψ₂)) L)) := by
  exact (rawHom_heq_transHom₂ (c := c) ψ₁ ψ₂ L).trans
    (transHom₂_heq_τ_baseChange (c := c) ψ₁ ψ₂ L)

/-- Rewrite the transition at the literal base-change maps, rather than
unfolding the chosen pullback's structure inside the coherence proof. -/
lemma rawHom_eq_τ (L : (Limits.pullback c t).Modules) :
    rawHom c ψ₁ ψ₂ L =
      (Scheme.Modules.isoCompHomApp
        (Scheme.Modules.τ (baseChangeSnd c (pr₁ ψ₁ ψ₂)) (baseChangeSnd c ψ₁)
          (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)))
          (bc_pr₁_comp (c := c) ψ₁ ψ₂)) L) ≫
      (Scheme.Modules.isoCompInvApp
        (Scheme.Modules.τ (baseChangeSnd c (pr₂ ψ₁ ψ₂)) (baseChangeSnd c ψ₂)
          (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)))
          (bc_pr₂_comp (c := c) ψ₁ ψ₂)) L) := by
  exact eq_of_heq (rawHom_heq_τ (c := c) ψ₁ ψ₂ L)

scoped instance isIso_rawHom (L : (Limits.pullback c t).Modules) : IsIso (rawHom c ψ₁ ψ₂ L) := by
  dsimp only [rawHom, transHom₂, modMap_toFunctor]
  exact IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _)
    (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (NatIso.inv_app_isIso _ _)))

def legIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t') (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1) (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ρ)).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L)) ≅
      (Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1).obj ((Scheme.Modules.pullback (rigSection c t ε)).obj L) :=
  (RigData.rigNatIso (c := c) (ε := ε) ρ).app ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) ≪≫
    (Scheme.Modules.pullback ρ.1).mapIso ((RigData.rigNatIso (c := c) (ε := ε) ψ).app L) ≪≫
      (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G).app ((Scheme.Modules.pullback (rigSection c t ε)).obj L)

/-- Expand only the composition of the three named comparisons, using the
square-comparison equality for each rigidification leg. -/
lemma legIso_hom {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t')
    (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1)
    (L : (Limits.pullback c t).Modules) :
    (legIso ψ₁ ψ₂ ψ ρ G L).hom =
      Scheme.Modules.isoSquareHomApp (Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε ρ))
          ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) ≫
        (Scheme.Modules.pullback ρ.1).map
          (Scheme.Modules.isoSquareHomApp (Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε ψ)) L) ≫
        Scheme.Modules.isoCompHomApp
          (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G)
          ((Scheme.Modules.pullback (rigSection c t ε)).obj L) := by
  rw [← RigData.rigNatIso_eq_sqIso (c := c) (ε := ε) ρ,
    ← RigData.rigNatIso_eq_sqIso (c := c) (ε := ε) ψ]
  exact Scheme.Modules.isoLegHomApp
    (RigData.rigNatIso (c := c) (ε := ε) ρ)
    (RigData.rigNatIso (c := c) (ε := ε) ψ)
    (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G) L

lemma map_map_eq_legIso_conj {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t') (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1)
    (A₁ A₂ : RigData c ε t)
    (φ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A₁.L ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A₂.L)
    (hφ : RigData.Compat (A₁.pb ψ) (A₂.pb ψ) φ) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
        ((Scheme.Modules.pullback (baseChangeSnd c ρ)).map φ) =
      (legIso ψ₁ ψ₂ ψ ρ G A₁.L).hom ≫ (Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1).map (A₁.α.hom ≫ A₂.α.inv) ≫
        (legIso ψ₁ ψ₂ ψ ρ G A₂.L).inv := by

  have n1 := (NatIso.naturality_2 (RigData.rigNatIso (c := c) (ε := ε) ρ) φ).symm
  have n2 := (NatIso.naturality_2 (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G) (A₁.α.hom ≫ A₂.α.inv)).symm
  dsimp only [Functor.comp_obj, Functor.comp_map] at n1 n2

  have hφ : (Scheme.Modules.pullback (rigSection c t' ε)).map φ ≫ (A₂.pb ψ).α.hom = (A₁.pb ψ).α.hom := hφ
  have hφ' : (Scheme.Modules.pullback (rigSection c t' ε)).map φ = (A₁.pb ψ).α.hom ≫ (A₂.pb ψ).α.inv :=
    (Iso.eq_comp_inv _).mpr hφ
  rw [n1, hφ']
  simp only [RigData.pb, legIso, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc] at n2
  dsimp only [Functor.comp_obj, RigData.pb_L] at n2 ⊢
  rw [reassoc_of% n2]

lemma map_rawHom_comp_legIso (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map (rawHom c ψ₁ ψ₂ L) ≫
        (legIso ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) L).hom =
      (legIso ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) L).hom := by
  rw [rawHom_eq_τ, legIso_hom, legIso_hom]
  exact Scheme.Modules.isoHeadApp
    (Scheme.Modules.τ (baseChangeSnd c (pr₁ ψ₁ ψ₂)) (baseChangeSnd c ψ₁)
      (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂))) (bc_pr₁_comp (c := c) ψ₁ ψ₂))
    (Scheme.Modules.τ (baseChangeSnd c (pr₂ ψ₁ ψ₂)) (baseChangeSnd c ψ₂)
      (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂))) (bc_pr₂_comp (c := c) ψ₁ ψ₂))
    (Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε (pr₁ ψ₁ ψ₂)))
    (Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε (pr₂ ψ₁ ψ₂)))
    (Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε ψ₁))
    (Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε ψ₂))
    (Scheme.Modules.τ (pr₁ ψ₁ ψ₂).1 ψ₁.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1
      (pr₁_comp_val ψ₁ ψ₂))
    (Scheme.Modules.τ (pr₂ ψ₁ ψ₂).1 ψ₂.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1
      (pr₂_comp_val ψ₁ ψ₂)) L
    (Scheme.Modules.head (baseChangeSnd c (pr₁ ψ₁ ψ₂)) (baseChangeSnd c ψ₁)
      (baseChangeSnd c (pr₂ ψ₁ ψ₂)) (baseChangeSnd c ψ₂)
      (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)))
      (bc_pr₁_comp (c := c) ψ₁ ψ₂) (bc_pr₂_comp (c := c) ψ₁ ψ₂)
      (rigSection c (strMap₁₂ ψ₁ ψ₂) ε) (rigSection c t₁ ε) (rigSection c t₂ ε) (rigSection c t ε)
      (pr₁ ψ₁ ψ₂).1 ψ₁.1 (pr₂ ψ₁ ψ₂).1 ψ₂.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1
      (pr₁_comp_val ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂)
      (rigSection_baseChangeSnd c ε (pr₁ ψ₁ ψ₂)) (rigSection_baseChangeSnd c ε ψ₁)
      (rigSection_baseChangeSnd c ε (pr₂ ψ₁ ψ₂)) (rigSection_baseChangeSnd c ε ψ₂) L)

theorem map_comp_rawHom_eq
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A₁ A₂ : RigData c ε t)
    (φ₁ : (Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₂.L)
    (φ₂ : (Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₁.L ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)
    [IsIso φ₁] [IsIso φ₂]
    (h₁ : RigData.Compat (A₁.pb ψ₁) (A₂.pb ψ₁) φ₁) (h₂ : RigData.Compat (A₁.pb ψ₂) (A₂.pb ψ₂) φ₂) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L =
      rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).map φ₂ := by
  have key : (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
      ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L) =
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
      (rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).map φ₂) := by
    have H1 := map_rawHom_comp_legIso (c := c) (ε := ε) ψ₁ ψ₂ A₁.L
    have H2 := map_rawHom_comp_legIso (c := c) (ε := ε) ψ₁ ψ₂ A₂.L
    have H2' : (legIso ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) A₂.L).inv ≫
        (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map (rawHom c ψ₁ ψ₂ A₂.L) =
        (legIso ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) A₂.L).inv :=
      (Iso.inv_comp_eq _).mpr ((Iso.eq_comp_inv _).mpr H2)
    rw [Functor.map_comp, Functor.map_comp,
      map_map_eq_legIso_conj ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) A₁ A₂ φ₁ h₁,
      map_map_eq_legIso_conj ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) A₁ A₂ φ₂ h₂]
    simp only [Category.assoc]
    rw [H2', ← H1, Category.assoc]

  let Φ : ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L) ≅
          (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)) :=
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).mapIso (asIso φ₁) ≪≫ asIso (rawHom c ψ₁ ψ₂ A₂.L)
  let Ψ : ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L) ≅
          (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)) :=
    asIso (rawHom c ψ₁ ψ₂ A₁.L) ≪≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).mapIso (asIso φ₂)
  have hΨ : (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Ψ ≪≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α =
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Φ ≪≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α :=
    Iso.ext (by
      first
        | simpa only [Φ, Ψ, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp, Category.assoc] using
            congrArg (· ≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α.hom) key.symm
        | (change (Scheme.Modules.pullback _).map
              (rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback _).map φ₂) ≫ _ =
              (Scheme.Modules.pullback _).map
                ((Scheme.Modules.pullback _).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L) ≫ _
           rw [key]))
  have hΦΨ : Φ = Ψ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq R c ε hH0
      (strMap₁₂ ψ₁ ψ₂) ((A₁.pb ψ₁).pb (pr₁ ψ₁ ψ₂)).toRLB ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).toRLB
      ((Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Φ ≪≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α)
      ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α Φ Ψ rfl hΨ
  exact congrArg Iso.hom hΦΨ

end bridge
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

/-- Transport an actual isomorphism back through an equivalence, without
unfolding any scheme-module or chosen-descent-data carrier. -/
def isoOfInverseIso {𝓒 𝓓 : Type*} [Category 𝓒] [Category 𝓓]
    (E : 𝓒 ≌ 𝓓) (X Y : 𝓓) (e : E.inverse.obj X ≅ E.inverse.obj Y) : X ≅ Y :=
  (E.counitIso.app X).symm ≪≫ E.functor.mapIso e ≪≫ E.counitIso.app Y

/-- A genuine object isomorphism lifts along bijective hom maps. The following
assembly supplies the actual open-cover bijections, not a new caller Fact. -/
theorem nonempty_iso_of_map_bijective {𝓒 𝓓 : Type*} [Category 𝓒] [Category 𝓓]
    (F : 𝓒 ⥤ 𝓓)
    (hF : ∀ X Y : 𝓒, Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)))
    (X Y : 𝓒) (e : F.obj X ≅ F.obj Y) : Nonempty (X ≅ Y) := by
  obtain ⟨ι₀, hι₀⟩ := (hF X Y).2 e.hom
  obtain ⟨κ₀, hκ₀⟩ := (hF Y X).2 e.inv
  refine ⟨⟨ι₀, κ₀, (hF X X).1 ?_, (hF Y Y).1 ?_⟩⟩
  · refine (F.map_comp ι₀ κ₀).trans ?_
    rw [hι₀, hκ₀, Iso.hom_inv_id]
    exact (F.map_id X).symm
  · refine (F.map_comp κ₀ ι₀).trans ?_
    rw [hι₀, hκ₀, Iso.inv_hom_id]
    exact (F.map_id Y).symm

/-- Construct an isomorphism of descent data from compatible component
isomorphisms. The pullback data stay symbolic throughout this construction. -/
theorem nonempty_descent_iso_of_components
    {𝓒 : Type*} [Category 𝓒]
    (F : Pseudofunctor (LocallyDiscrete 𝓒ᵒᵖ) Cat)
    {ι : Type*} {S : 𝓒} {X : ι → 𝓒} {g : ∀ i, X i ⟶ S}
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (D₁ D₂ : F.DescentData g) (e : ∀ i, D₁.obj i ≅ D₂.obj i)
    (he : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.map (e i).hom ≫
          ((DescentData'.fromDescentDataFunctor F sq sq₃).obj D₂).hom i j =
        ((DescentData'.fromDescentDataFunctor F sq sq₃).obj D₁).hom i j ≫
          (F.map (sq i j).p₂.op.toLoc).toFunctor.map (e j).hom) :
    Nonempty (D₁ ≅ D₂) := by
  let e' : (DescentData'.fromDescentDataFunctor F sq sq₃).obj D₁ ≅
      (DescentData'.fromDescentDataFunctor F sq sq₃).obj D₂ :=
    DescentData'.isoMk e he
  exact ⟨isoOfInverseIso (DescentData'.descentDataEquivalence F sq sq₃) D₁ D₂ e'⟩

section asm_bZ

variable {ι : Type u} {U : ι → Scheme.{u}} (uS : ∀ i, U i ⟶ Spec (CommRingCat.of R))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (f : ∀ i, SchemeHomOver (uS i) t)

scoped instance isOpenImmersion_baseChangeSnd [∀ i, IsOpenImmersion (f i).1] (i : ι) : IsOpenImmersion (baseChangeSnd c (f i)) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c (f i)).flip inferInstance

abbrev sqZ : ∀ (i j : ι), ChosenPullback (baseChangeSnd c (f i)) (baseChangeSnd c (f j)) :=
  fun i j => chosenPullback c (f i) (f j)
abbrev sq₃Z : ∀ (i j k : ι), ChosenPullback₃ (sqZ c uS t f i j) (sqZ c uS t f j k) (sqZ c uS t f i k) :=
  fun i j k => chosenPullback₃' c (f i) (f j) (f k)

lemma toDDZ_hom (L : (Limits.pullback c t).Modules) (i j : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD)
          (sqZ c uS t f) (sq₃Z c uS t f)).obj
        (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj L)).hom i j =
      rawHom c (f i) (f j) L :=
  (fromDescentData_toDescentData_hom (fun i => baseChangeSnd c (f i))
    (sqZ c uS t f) (sq₃Z c uS t f) L i j).trans
    (transHom₂_eq_rawHom (f i) (f j) L)

lemma toDDZ_obj (L : (Limits.pullback c t).Modules) (i : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD)
          (sqZ c uS t f) (sq₃Z c uS t f)).obj
        (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj L)).obj i = ((MOD).map (baseChangeSnd c (f i)).op.toLoc).toFunctor.obj L :=
  fromDescentData_toDescentData_obj (fun i => baseChangeSnd c (f i))
    (sqZ c uS t f) (sq₃Z c uS t f) L i


lemma isoMk_commZ
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A₁ A₂ : RigData c ε t) (ι' : ∀ i, (A₁.pb (f i)).L ≅ (A₂.pb (f i)).L)
    (hι' : ∀ i, RigData.Compat (A₁.pb (f i)) (A₂.pb (f i)) (ι' i).hom) (i j : ι) :
    ((MOD).map (sqZ c uS t f i j).p₁.op.toLoc).toFunctor.map (ι' i).hom ≫
        ((DescentData'.fromDescentDataFunctor (MOD)
          (sqZ c uS t f) (sq₃Z c uS t f)).obj
        (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj A₂.L)).hom i j =
      ((DescentData'.fromDescentDataFunctor (MOD)
          (sqZ c uS t f) (sq₃Z c uS t f)).obj
        (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj A₁.L)).hom i j ≫
        ((MOD).map (sqZ c uS t f i j).p₂.op.toLoc).toFunctor.map (ι' j).hom := by
  rw [toDDZ_hom, toDDZ_hom]
  dsimp only [sqZ, toDDZ_obj, modMap_toFunctor, chosenPullback_p₁, chosenPullback_p₂]
  exact map_comp_rawHom_eq (f i) (f j) hH0 A₁ A₂ (ι' i).hom (ι' j).hom (hι' i) (hι' j)

/-- Construct the ACTUAL descent-data isomorphism from the local rigidified
isomorphisms. Lifting it along the open-cover hom bijection is a separate proof. -/
theorem nonempty_iso_toDD_of_rigData
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A₁ A₂ : RigData c ε t)
    (h : ∀ i, Nonempty ((A₁.pb (f i)).L ≅ (A₂.pb (f i)).L)) :
    Nonempty ((((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj A₁.L) ≅
      (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj A₂.L)) := by
  classical
  have hι : ∀ i, ∃ φ : (A₁.pb (f i)).L ≅ (A₂.pb (f i)).L,
      RigData.Compat (A₁.pb (f i)) (A₂.pb (f i)) φ.hom :=
    fun i => RigData.exists_compat_iso (A₁.pb (f i)) (A₂.pb (f i)) (h i)
  choose ι' hι' using hι
  have comm := isoMk_commZ c ε uS t f hH0 A₁ A₂ ι' hι'
  exact nonempty_descent_iso_of_components (MOD)
    (sqZ c uS t f) (sq₃Z c uS t f)
    (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj A₁.L)
    (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj A₂.L) ι' comm

theorem asm_bZ
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    [∀ i, IsOpenImmersion (f i).1] (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base)
    (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : ∀ i, Nonempty ((M₁.pullbackAlong (f i)).L ≅ (M₂.pullbackAlong (f i)).L)) :
    Nonempty (M₁.L ≅ M₂.L) := by
  let A₁ : RigData c ε t := RigData.ofRLB M₁ M₁.rigidified.some
  let A₂ : RigData c ε t := RigData.ofRLB M₂ M₂.rigidified.some

  obtain ⟨ξ⟩ := nonempty_iso_toDD_of_rigData c ε uS t f hH0 A₁ A₂ h

  have hg : ∀ y : ↥(Limits.pullback c t), ∃ i, y ∈ Set.range (baseChangeSnd c (f i)).base :=
    exists_mem_range_baseChangeSnd c f hf
  have hbij := fun (L₁ L₂ : (Limits.pullback c t).Modules) =>
    AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover (fun i => baseChangeSnd c (f i)) hg L₁ L₂
  exact nonempty_iso_of_map_bijective
    ((MOD).toDescentData (fun i => baseChangeSnd c (f i))) hbij M₁.L M₂.L ξ

end asm_bZ
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

end AlgebraicGeometry.RelPicard.DescentAux
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
end
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard NeronModelInfra"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ Spec (CommRingCat.of R))
    (f : ∀ i, SchemeHomOver (u i) t) [∀ i, IsOpenImmersion (f i).1]
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base)
    (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : ∀ i, Nonempty ((M₁.pullbackAlong (f i)).L ≅ (M₂.pullbackAlong (f i)).L)) :
    Nonempty (M₁.L ≅ M₂.L) :=
  AlgebraicGeometry.RelPicard.DescentAux.asm_bZ c ε u t f hH0 hf M₁ M₂ h
end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT

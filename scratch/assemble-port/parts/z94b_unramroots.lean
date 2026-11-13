/-! ## assemble-port (stretch): `UnramRoots` (frob-contrib's kernel proof) for this file's copy

frob-contrib proves local-glue's textbook Prop `G15Ram.UnramRoots p ℓ` in the kernel module
`ZInQKernel/Contrib/UnramRoots/Main.lean` (`UnramRootsTask.unramRoots`; merged from origin/wip/frob-contrib, imported through
imports_tailD.txt), over the kernel's `LadicCond` definitions. This file's `G15Ram.UnramRoots` (local-glue's text, in part
z93z) is the same statement over this file's copies of those definitions; the kernel accepts the kernel theorem for it
by unfolding. -/

namespace HSyn

/-- **`UnramRoots` holds** (frob-contrib, via the kernel's statement). -/
theorem unramRoots_proved (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] : G15Ram.UnramRoots p ℓ :=
  _root_.UnramRootsTask.unramRoots

end HSyn

#print axioms HSyn.unramRoots_proved

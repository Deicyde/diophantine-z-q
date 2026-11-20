# CM field scope continuation

**Scope settled.** Only `HeegnerAnchor.cmPointsAtScale` and
`HeegnerAnchor.genuineHeegnerAnchor` require `2 ∣ newformLevel (Ecurve ℓ)`
to keep their old conclusions: both range over positive conductors prime
to `N · |D_K|`, while tex 2841–2844 includes `2`. The genus, missing-row,
ring-class and total-selector paths already satisfy the scoped conductor
condition. The selector field and the anchor use the same scoped CM
proposition. Splitting at `2N` does not imply parity of `N`. The actual
curve has bad reduction at 2 by the discriminant in tex 1761–1765, and
its level is the conductor by tex 1780–1782. The draft wrappers keep
parity explicit until the actual-curve lane supplies it in Lean.

**Scoped stop.** Inherited serial checks passed for `CMScope/Field.lean`
and `CMScope/Orientation.lean`: broad implies scoped, both level-one
instances, and orientation specialization. The resource gate remained
above 120 (222.08 at the final check, with other Lean jobs active). No
new Lean check or axiom audit ran. The corrected
[wrapper patch](../scratch/rc-cm-scope2/pending-wrappers.patch) fixes the
exclusion of discriminant `−4` by using coprimality at 2. The
[log](../scratch/rc-cm-scope2/log.md) lists the remaining checks. At
general level the scoped CM statement remains an input; no print was
added.

[Report](../docs/research/rc-cm-scope2.md) and scratch checkpoint:
`4dc756a99ece6340ad9dd02d1563fc8c2edf1e94`. Final handoff is the next
commit on `wip/rc-cm-scope2`.

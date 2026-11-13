"""Generate the texts of LinkedTateObjSCore and LocalPartS from g8-object's LinkedTateObjS.

Reads scratch/g8-object/part_split.lean, checks that LinkedTateObjS ends with the two LocalDataS
conjuncts, and prints (to stdout) the two derived definitions:
  * LinkedTateObjSCore: LinkedTateObjS without the last two conjuncts;
  * LocalPartS: the binders of LinkedTateObjS (up to the premise [L:Q] <= D) and the two
    LocalDataS conjuncts only.
Usage: python3 scratch/g8-local/py/gen_link2.py  (from the worktree root)
"""
src = open('scratch/g8-object/part_split.lean').read()
a = src.index("def LinkedTateObjS : Prop :=")
b = src.index("/-- **`LinkedTateObj` restricted", a)
block = src[a:b].rstrip() + "\n"
old = """      OnL L A Tm₅ (fun g => j5 (aQ g)) ψ₅ ∧ OnL L A Tm₃ (fun g => j3 (aQ g)) ψ₃ ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataS p ⟨hp⟩ L _ A 5 _ β) ∧
      LocalDataS 5 L A 3 β
"""
assert block.endswith(old)
core = block.replace(old, """      OnL L A Tm₅ (fun g => j5 (aQ g)) ψ₅ ∧ OnL L A Tm₃ (fun g => j3 (aQ g)) ψ₃
""").replace("def LinkedTateObjS : Prop :=", "def LinkedTateObjSCore : Prop :=")
hdr_end = block.index("    letI : NumberField L' := numberField_of_fd L'")
localpart = block[:hdr_end].replace("def LinkedTateObjS : Prop :=", "def LocalPartS : Prop :=") + \
    """    (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataS p ⟨hp⟩ L _ A 5 _ β) ∧
      LocalDataS 5 L A 3 β
"""
print(localpart)
print(core)

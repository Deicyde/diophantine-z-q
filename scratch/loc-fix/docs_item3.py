"""loc-fix item 3: leftover locator mentions (Lin-Yang Example 30, indices 4,6,2, TYZ char'/multiples1)."""
D="docs/research/"
LYNOTE=("*Note (loc-fix, 2026-11-12).* Lin–Yang's discriminant-6 example is arXiv:1807.00466v1 **Example 29**\n"
        "(pp. 20-21); v1's Example 30 treats discriminant 14 (locators.md item 3, read by the locator audit).\n"
        "The mentions of \"Ex. 30\" / \"Example 30\" below are corrected in place, each marked \"(formerly Ex. 30)\".")
ORBNOTE=("The numbers `4, 6, 2` at `j = 0, ∞, −16/27` are the orbifold (elliptic) orders of the normalizer\n"
         "group `Γ*` (Baba–Granath §3.1); they are the ramification indices of the level-three cover\n"
         "`Y₃ → P¹_j` (glue: `Γ₃` is torsion-free and normal in `Γ*`, rv-nocm §2.2), not of the degree-4\n"
         "map `X₆ → X₆/W`, which has indices `2, 2, 2`.")
def edit(path, reps, note=None, after_title=True):
    s=open(D+path).read()
    for a,b,c in reps:
        assert s.count(a)==c, (path,a[:60],s.count(a)); s=s.replace(a,b)
    if note:
        i=s.index("\n")+1  # after the title line
        s=s[:i]+"\n"+note+"\n"+s[i:]
    open(D+path,"w").write(s)
    print("ok",path)
F="(formerly Ex. 30)"
edit("pkg-I1.md",[
 ("`QMHauptmodul` (Lin–Yang Ex. 30 + Igusa","`QMHauptmodul` (Lin–Yang v1 Ex. 29 "+F+" + Igusa",1),
 ("| A2 | W | `X₆/W ≅ P¹_j` over `ℚ`, branch values `0, ∞, −16/27` of indices 4, 6, 2 at discs −4, −3, −24 |",
  "| A2 | W | `X₆/W ≅ P¹_j` over `ℚ`, elliptic points `0, ∞, −16/27` of orbifold orders 4, 6, 2 (indices of `Y₃ → P¹_j`; the map `X₆ → X₆/W` has indices 2, 2, 2) at discs −4, −3, −24 (wording corrected 2026-11-12 by loc-fix, rv-nocm §3.2) |",1),
 ("295 (2020), Example 30 (divisors","295 (2020), arXiv v1 Example 29 "+F+" (divisors",1),
 ("and Lin–Yang 2020, Ex. 30 with eqs.","and Lin–Yang 2020, v1 Ex. 29 "+F+" with eqs.",1),
], LYNOTE)
edit("rv-leaves-a.md",[
 ("Lin–Yang Ex. 30 (divi","Lin–Yang v1 Ex. 29 "+F+" (divi",1),
 ("1. Lin–Yang 2020, Ex. 30: on","1. Lin–Yang 2020, v1 Ex. 29 "+F+": on",1),
 ("The Lin–Yang Ex. 30 divisor statement","The Lin–Yang v1 Ex. 29 "+F+" divisor statement",1),
], LYNOTE+"\nThe \"local orders `4, 6, 2`\" checked below are orbifold orders of `Γ*`, as stated; "+ORBNOTE.split(";",1)[1].strip())
edit("wk-h.md",[
 ("LY 2020 Ex. 30: `X₆/W ≅ P¹_j`, elliptic points `j = 0, ∞, −16/27` of orders 4, 6, 2",
  "LY 2020 v1 Ex. 29 "+F+": `X₆/W ≅ P¹_j`, elliptic points `j = 0, ∞, −16/27` of orbifold orders 4, 6, 2 (indices of `Y₃ → P¹_j`, not of `X₆ → X₆/W`, which has 2, 2, 2; loc-fix 2026-11-12)",1),
], LYNOTE)
edit("h-v14.md",[
 ("| 714-718 | — | branch indices `4, 6, 2` from cyclic stabilizers |",
  "| 714-718 | — | branch indices `4, 6, 2` from cyclic stabilizers (note 2026-11-12, loc-fix: these are orbifold orders of `Γ*`, equal to the indices of the torsion-free level-3 cover `Y₃ → P¹_j`; the degree-4 map `X₆ → X₆/W` has indices 2, 2, 2; rv-nocm §2.2) |",1),
 ("| 719-721 | `linyang`, Example 30 |","| 719-721 | `linyang`, Example 30 (= arXiv v1 Example 29; v1's Example 30 is discriminant 14, locators.md item 3; note 2026-11-12, loc-fix) |",1),
], LYNOTE+"\n"+ORBNOTE)
edit("h-b1.md",[
 ("| M4 | branch points and indices | `(0,4)`, `(∞,6)`, `(−16/27,2)` | STANDARD (Baba–Granath, Canad. J. Math. 2008; Lin–Yang 2020; cited at N5 L418-419) |",
  "| M4 | branch points and indices | `(0,4)`, `(∞,6)`, `(−16/27,2)`: the orbifold orders of `Γ*` (Baba–Granath §3.1). They are the ramification indices of each geometric component `Γ₃\\ℍ → Γ*\\ℍ`, since `Γ₃` is torsion-free (`−1 ∉ K₃`; N5 L468-470) and normal in `Γ*` (`RvNocm.ramification_eq_orbifold_order`). They are not the indices of `X₆ → P¹_j`, which are `2, 2, 2` (used in Lemma NV step 4). (Value text replaced 2026-11-12 by loc-fix with rv-nocm §3.2.) | STANDARD (Baba–Granath, Canad. J. Math. 2008, §3.1 elliptic-order table, p. 740 per locators.md; Lin–Yang 2020, arXiv v1 Example 29; cited at N5 L418-419) plus glue (torsion-freeness, normality) |",1),
 ("4. **Branch data M4** still rests on Baba–Granath and Lin–Yang, as before.",
  "4. **Branch data M4** still rests on Baba–Granath and Lin–Yang, as before (since 2026-11-12, loc-fix: on Baba–Granath's orbifold orders plus the torsion-freeness and normality of `Γ₃`, see M4).",1),
], "*Note (loc-fix, 2026-11-12).* M4 is restated with rv-nocm §3.2's text. "+ORBNOTE+" Lin–Yang's\ndiscriminant-6 example is arXiv v1 Example 29 (v1's Example 30 is discriminant 14; locators.md item 3).")
edit("tyz-t1.md",[
 ("of Lemma 3.8 (`char'`).","of Lemma 3.14 (`char'`).",1),
 ("excluded by Lemma 3.8","excluded by Lemma 3.14",2),
 ("`χ` as in Lemma 3.8:","`χ` as in Lemma 3.14:",1),
 ("(Lemma 3.8 (2))","(Lemma 3.14 (2))",1),
 ("- `e ≡ 5, 7`: Lemma 3.8 excludes","- `e ≡ 5, 7`: Lemma 3.14 excludes",1),
], "*Note (loc-fix, 2026-11-12).* TYZ's `char'` (L1868) and `multiples1` (L1919) are **Lemmas 3.14 and 3.15**\n"
   "of arXiv:1411.4728v1 (VERIFIED by counting the environments that share the theorem counter in §3 of\n"
   "`Period7.tex`, as loc-adopt did). This note called `char'` \"Lemma 3.8\"; corrected in place.")

# pc90b-review: early verdict (item failed), head a8099a02

**a8099a02 is NOT clean on item (6), the labels.** It is a documentation fault; the Lean is still being checked.

* `Lemma54` is labelled a printed leaf, but it is a lemma of the manuscript. Places: `ZInQKernel/Contrib/OneProof/PoleS12/Leaves.lean:17`
  (module doc: "`Lemma54` (printed leaf, tex `lem:corank` ...)"), `Leaves.lean:81` ("printed form over genuine
  definitions"), `ZInQKernel/OneProof/Main.lean:12` and `Main.lean:137` ("the printed leaves Lemma 5.4, ...").
* `KolyvaginThm1` names the bridge (Shimura's construction plus Faltings' isogeny theorem, `Leaves.lean:57-60`), but it is
  still rated "printed leaf" (`Leaves.lean:14` and `Leaves.lean:53`, "printed leaf as cited"). The rating should be
  "consequence".
* Stale text: `Leaves.lean:21` and `Leaves.lean:91` still call `KummerSelmerM` "not proved", but 405c14903 discharges
  it by the proof `PoleS12.kummerSelmerM`.

Items (4) no S12, (5) Tau Ceti untouched by the five commits and (7) rename scope pass. Items (1)–(3) are still running.
Full report: docs/research/pc90b-review.md.

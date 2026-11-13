# Complete 214-variable manuscript, receiving revision 3

This is the current corrected receiving edition for PR30: [complete PDF](quartic214.pdf) and [complete TeX](quartic214.tex). The polynomial and all arithmetic arguments are unchanged from revision 2. The sufficient defining threshold remains ineffective; this edition certifies no particular parameter and does not promote a new official numbered release.

The two corrections restore the indices in the Lucas cross term `L_3 L_4` and the scale identity `t_1 = T t_0`. The current interpretation of source-inventory use U01 is **188 rows in 214 coordinates**, rather than 214 rows. [CORRECTIONS.json](CORRECTIONS.json) binds the exact earlier source passages and supplies this inventory addendum. Its `inventory.current_text` supersedes only the erroneous wording of U01. The historical reviewer record is unchanged.

The predecessor directories, their guides, source evidence and reviews remain frozen historical editions. In particular, references in the earlier root guide `CURRENT_214_REVIEW.md` to revision 2 being operative describe that earlier edition. Use [the revision 3 root guide](../../CURRENT_214_REVISION3.md) for this successor. Previous reviews retain their original scope and are not relabeled as approval of these changed files.

`assemble.py` applies the two exact notation corrections and updates the edition date. It emits a complete manuscript and preserves the source-map line numbering. `build_pdf.py` uses the retained serial builder with no shell escape and a 1 GiB child memory limit. `check_records.py` checks the exact delta, historical pins, current inventory wording, generated map, PDF source binding and separate independent review receipt. These are finite checks, not a proof of the mathematics or authentication of a model.

```sh
python3 -B research/quartic214-manuscript-revision3/assemble.py --check
python3 -B research/quartic214-manuscript-revision3/build_pdf.py --check
python3 -B research/quartic214-manuscript-revision3/check_records.py --self-test --reviewed-artifacts
```

The separate revision 3 independent review binds this directory's manifest. The designated protected App must still approve the final PR revision.

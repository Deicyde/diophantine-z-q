# pi0-prune generator

`gen.py CONFIG` writes one Lean file: `HEADER`, then for each `(source file, [declarations])` segment the source
file's namespace/section/open/set_option/attribute/variable skeleton with the selected declarations copied in source
order (empty blocks removed), renamed by `common.py`'s `RENAME` (whole identifiers: the 76 names of the copy set get
suffix `W`, `OpenAddedLeaves12..17` get suffix `P`, `R1R2fpRep` → `R1R2fpRepW`), then `FOOTER`.

Declarations are given by name (`cfg_*_n.py`, canonical; `cfg_*.py` are the same by line range at base 43513d87).
Per-declaration options: `nodoc` (structures: docstring omitted), `drop` (regexes of fields/assignments to delete,
with their docstrings: the two pruned fields), `subs` (literal replacements, asserted present: the three patterns
with one conjunct fewer, and the `X6Leaves` literal without `deligneX6P`/`geomConn`).

Regenerate (e.g. after r6-nf's fold changes the old generations):

    for c in base old upper; do python3 scratch/pi0-prune/tools/gen.py scratch/pi0-prune/tools/cfg_${c}_n.py; done
    lake build ZInQKernel.Contrib.OneProof.Pi0Prune

On a new base, first rerun `scratch/pi0-prune/Copy.lean` (`lake env lean`), which lists the copy set (live constants
whose type mentions `R1R2fpRep` or a bundle carrying it, the readers of the two fields, and everything above them);
add any new name to `common.py`'s `W_NAMES` and to the matching `cfg_*_n.py` segment. The hand-written producers are
in `base_producers.lean` (FOOTER of the Base config).

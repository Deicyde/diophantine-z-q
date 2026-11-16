# dioph_gaps1 task queue

A runner on the dioph_gaps1 devserver fetches this branch every 5 minutes and starts each queued task it has not
started yet, whenever fewer than 6 tasks are running there (effort high, 24G memory each).

A task is two files in `queue/`:
- `NN-TASK.md`: the full prompt, built with `bin/build-prompt.py` (the fleet's usual header, task, rules and tail).
- `NN-TASK.base`: one line, the start ref, for example `origin/main` or `origin/wip/height-dict`.

`NN-` sets the order (filename sort) and is not part of the task name. The task's branch is `wip/TASK`; its report
and `.fleet/TASK.md` land there through the host's pusher. A task name is started at most once; to rerun one, use a
new name. Add tasks with a plain commit and push (no force).

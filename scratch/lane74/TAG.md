# route-k-final tag (lane74, #77)

Push from the sandbox failed (CONNECT tunnel failed, response 403); not retried.
The tag exists locally in the shared repository. Lead: run, from a host with network,

    git tag route-k-final bf691da2236b494bb429caabc2f907d4ea428c4d   # if not already present
    git push origin refs/tags/route-k-final

SHA taken from the file: `grep LANDED ~/dzq-runs/landed.txt | tail -1 | cut -d' ' -f1`
= bf691da2236b494bb429caabc2f907d4ea428c4d (chk-w104 green, main fast-forward 19fdd483, 11-17_06:06).

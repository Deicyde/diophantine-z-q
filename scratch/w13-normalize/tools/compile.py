"""Compile staged modules in dependency order with plain `lean` (offline test harness).

  python3 compile.py --cone-json work/cone_core.json [--jobs 2] [--force]

Each module: `lake env lean -j2 -o <olean> -i <ilean> <file>` once all its staged imports have
succeeded; RSS and wall time via /usr/bin/time -v.  Logs: work/build/<module>.log, summary JSON.
Never builds a module whose staged import failed.  Respects the memory budget by running at most
--jobs compilations at once (default 2).
"""
import os, sys, json, subprocess, time, argparse, re, threading, queue
sys.path.insert(0, os.path.dirname(__file__))
from graph import ROOT, graph, path_of

WORK = '/home/jackmccarthy/cloud-b3/w13/normalize/work'
BUILD = os.path.join(WORK, 'build')


def olean_path(m):
    return os.path.join(ROOT, '.lake/build/lib/lean', m.replace('.', '/') + '.olean')


def compile_one(m):
    src = os.path.join(ROOT, path_of(m))
    ol = olean_path(m)
    il = ol[:-6] + '.ilean'
    os.makedirs(os.path.dirname(ol), exist_ok=True)
    log = os.path.join(BUILD, m + '.log')
    cmd = ['/usr/bin/time', '-v', 'lake', 'env', 'lean', '-j2', '-o', ol, '-i', il, src]
    env = dict(os.environ, LEAN_NUM_THREADS='2')
    t0 = time.time()
    with open(log, 'w') as fh:
        r = subprocess.run(cmd, cwd=ROOT, env=env, stdout=fh, stderr=subprocess.STDOUT)
    dt = time.time() - t0
    txt = open(log, errors='replace').read()
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', txt)
    errors = len(re.findall(r':\d+:\d+: error', txt))
    return {'module': m, 'rc': r.returncode, 'secs': round(dt, 1), 'rss_mb': int(rss.group(1)) // 1024 if rss else None,
            'errors': errors}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cone-json', required=True)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--summary', default=None)
    args = ap.parse_args()
    os.makedirs(BUILD, exist_ok=True)
    g = graph()
    mods = json.load(open(args.cone_json))
    mods = [m for m in mods if m in g]
    mset = set(mods)
    deps = {m: [i for i in g[m] if i in g] for m in mods}
    for m in mods:
        for i in deps[m]:
            if i not in mset:
                raise SystemExit('cone not closed: %s imports %s' % (m, i))
    status = {}
    results = []
    lock = threading.Lock()
    summary = args.summary or os.path.join(WORK, 'build_summary_%s.json' % os.path.basename(args.cone_json).replace('.json', ''))
    if not args.force:
        for m in mods:
            if os.path.exists(olean_path(m)) and os.path.getmtime(olean_path(m)) > os.path.getmtime(os.path.join(ROOT, path_of(m))):
                status[m] = 'ok-cached'
    pending = [m for m in mods if m not in status]
    running = {}
    q = queue.Queue()

    def worker(m):
        r = compile_one(m)
        q.put(r)

    while pending or running:
        # schedule
        progressed = False
        for m in list(pending):
            if len(running) >= args.jobs:
                break
            ds = deps[m]
            if any(status.get(d) in ('fail', 'blocked') for d in ds):
                status[m] = 'blocked'
                pending.remove(m)
                results.append({'module': m, 'rc': None, 'blocked_by': [d for d in ds if status.get(d) in ('fail', 'blocked')]})
                progressed = True
                continue
            if all(status.get(d) in ('ok', 'ok-cached') for d in ds):
                pending.remove(m)
                th = threading.Thread(target=worker, args=(m,))
                running[m] = th
                th.start()
                progressed = True
        if not running:
            if pending and not progressed:
                raise SystemExit('deadlock: %s' % pending[:5])
            continue
        r = q.get()
        running.pop(r['module']).join()
        status[r['module']] = 'ok' if r['rc'] == 0 else 'fail'
        results.append(r)
        print(json.dumps(r), flush=True)
        json.dump({'status': status, 'results': results}, open(summary, 'w'), indent=1)
    okc = sum(1 for v in status.values() if v in ('ok', 'ok-cached'))
    print('DONE ok=%d fail=%d blocked=%d of %d' % (okc, sum(1 for v in status.values() if v == 'fail'),
                                                   sum(1 for v in status.values() if v == 'blocked'), len(mods)))
    json.dump({'status': status, 'results': results}, open(summary, 'w'), indent=1)


if __name__ == '__main__':
    main()

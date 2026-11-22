"""Shared git readers for the batch split (no working tree is touched)."""
import re, subprocess

IMPORT_RE = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(\S+)", re.M)


class Repo:
    def __init__(self, path):
        self.path = path
        self._cache = {}
        self._reader = subprocess.Popen(["git", "-C", path, "cat-file", "--batch"],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def git(self, *a, inp=None, env=None):
        return subprocess.run(["git", "-C", self.path, *a], input=inp, capture_output=True,
                              check=True, env=env).stdout

    def rev(self, r):
        return self.git("rev-parse", r + "^{commit}").decode().strip()

    def tree(self, rev, *paths):
        t = {}
        for line in self.git("ls-tree", "-r", "-z", rev, "--", *paths).split(b"\0"):
            if line:
                meta, path = line.split(b"\t", 1)
                mode, _, sha = meta.split()
                t[path.decode()] = (mode.decode(), sha.decode())
        return t

    def blob(self, sha):
        if sha not in self._cache:
            self._reader.stdin.write(sha.encode() + b"\n")
            self._reader.stdin.flush()
            size = int(self._reader.stdout.readline().split()[2])
            self._cache[sha] = self._reader.stdout.read(size)
            self._reader.stdout.read(1)
        return self._cache[sha]

    def text(self, sha):
        return self.blob(sha).decode("utf-8")


def mod(p):
    return p[:-5].replace("/", ".")


def _strip_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i); i = len(s) if j < 0 else j; continue
        out.append(s[i]); i += 1
    return "".join(out)


HEADER_IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(.+)$")


def imports(text):
    """Modules imported in the file header (Lean 4 allows imports only before the first command)."""
    out = []
    for line in _strip_comments(text).splitlines():
        t = line.strip()
        if not t or t in ("module", "prelude"):
            continue
        m = HEADER_IMPORT.match(t)
        if not m:
            break
        out.extend(tok for tok in m.group(1).split() if tok != "all")
    return out

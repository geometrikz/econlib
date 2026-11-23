"""Produce statement-only Lean files: comments removed, theorem proofs replaced by `sorry`.
Definitions keep their bodies (they are part of what a statement means).
Usage: python3 strip_proofs.py SRC_ROOT OUT_ROOT [--keep-comments]"""
import re, sys, pathlib

def strip_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and s.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j; continue
        if s[i] == '"':  # string literal
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            out.append(s[i:j+1]); i = j + 1; continue
        out.append(s[i]); i += 1
    return re.sub(r'\n\s*\n(\s*\n)+', '\n\n', ''.join(out))

DECL = re.compile(r'^(@\[[^\]]*\]\s*)?(private |protected |noncomputable )*(theorem|lemma)\b')
TOP = re.compile(r'^\S')

def sig_end(text):
    """index of the depth-0 ':=' or 'where' ending the signature.
    A `let`/`have` inside the statement owns the next ':=' (e.g. `let k := f x; P k`)."""
    d, pending = 0, 0
    for m in re.finditer(r'[(\[{⟨]|[)\]}⟩]|:=|\bwhere\b|\blet\b|\bhave\b', text):
        t = m.group()
        if t in '([{⟨': d += 1
        elif t in ')]}⟩': d -= 1
        elif t in ('let', 'have'): pending += 1
        elif t == ':=' and pending: pending -= 1
        elif d == 0: return m.start()
    return None

def strip_proofs(s):
    lines = s.split('\n'); out = []; i = 0
    while i < len(lines):
        if DECL.match(lines[i]):
            j = i + 1
            while j < len(lines) and not TOP.match(lines[j]): j += 1
            block = '\n'.join(lines[i:j]).rstrip()
            k = sig_end(block)
            out.append((block[:k].rstrip() if k is not None else block) + ' := by\n  sorry\n')
            i = j
        else:
            out.append(lines[i]); i += 1
    return '\n'.join(out)

if __name__ == '__main__':
    src, dst = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
    for f in sorted(src.rglob('*.lean')):
        t = f.read_text()
        if '--keep-comments' not in sys.argv: t = strip_comments(t)
        t = strip_proofs(t)
        o = dst / f.relative_to(src); o.parent.mkdir(parents=True, exist_ok=True); o.write_text(t)
        print(o)

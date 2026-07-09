#!/usr/bin/env python3
import re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = [
    (r'\bsorry\b', 'sorry'), (r'\bsorryAx\b', 'sorryAx'), (r'\badmit\b', 'admit'),
    (r'\baxiom\b', 'axiom'), (r'\bunsafe\b', 'unsafe'), (r'\bimplemented_by\b', 'implemented_by'),
    (r'\bnative_decide\b', 'native_decide'), (r'\bopaque\b', 'opaque'),
    (r'set_option\s+profiler\s+true', 'set_option profiler true'),
]
SMELLS = [(r'set_option\s+linter\.[^\n]*false\b', 'linter suppression')]
def strip_comments_strings(text):
    out=[]; i=0; depth=0; string=False
    while i < len(text):
        ch=text[i]; nx=text[i+1] if i+1 < len(text) else ''
        if depth:
            if ch=='/' and nx=='-': depth+=1; out+=[' ',' ']; i+=2
            elif ch=='-' and nx=='/': depth-=1; out+=[' ',' ']; i+=2
            else: out.append('\n' if ch=='\n' else ' '); i+=1
        elif string:
            if ch=='\\' and nx: out+=[' ',' ']; i+=2
            elif ch=='"': string=False; out.append(' '); i+=1
            else: out.append('\n' if ch=='\n' else ' '); i+=1
        elif ch=='-' and nx=='-':
            out+=[' ',' ']; i+=2
            while i < len(text) and text[i] != '\n': out.append(' '); i+=1
        elif ch=='/' and nx=='-': depth=1; out+=[' ',' ']; i+=2
        elif ch=='"': string=True; out.append(' '); i+=1
        else: out.append(ch); i+=1
    return ''.join(out)
def lean_files():
    files=[]
    if (ROOT/'KolmogorovMathlib.lean').exists(): files.append(ROOT/'KolmogorovMathlib.lean')
    if (ROOT/'KolmogorovMathlib').exists(): files += sorted((ROOT/'KolmogorovMathlib').rglob('*.lean'))
    return files
def scan_sources():
    hits=[]
    regs=[(label,re.compile(p)) for p,label in FORBIDDEN+SMELLS]
    for f in lean_files():
        text=f.read_text(encoding='utf-8')
        clean=strip_comments_strings(text).splitlines()
        orig=text.splitlines()
        for n,line in enumerate(clean,1):
            for label,rx in regs:
                if rx.search(line):
                    hits.append((f.relative_to(ROOT),n,label,orig[n-1].strip() if n<=len(orig) else ''))
    if hits:
        print('FORBIDDEN/SMELL HITS:')
        for h in hits: print(f'{h[0]}:{h[1]} {h[2]}: {h[3]}')
        return False
    print('source scan: ok')
    return True
def main():
    p=subprocess.run(['lake','build','KolmogorovMathlib'],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    print(p.stdout)
    build_ok = p.returncode == 0
    warnings=[l for l in p.stdout.splitlines() if 'warning:' in l.lower()]
    print(f'build_rc={p.returncode} warning_count={len(warnings)}')
    for l in warnings[:50]: print(l)
    source_ok=scan_sources()
    # During migration: build and source invariants are hard. Warnings are reported
    # and become a hard acceptance criterion once the port builds.
    if build_ok and source_ok and not warnings:
        sys.exit(0)
    sys.exit(1)
if __name__ == '__main__': main()

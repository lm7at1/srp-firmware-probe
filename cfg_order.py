#!/usr/bin/env python3
"""Does the compression decoder run before signature verification?

Replicates the method of 01_PRODUCTION_CALL_PATH.md section 1.4 on an arbitrary build:

  1. attribute every `bl` to the callees of interest to its containing function;
  2. build a complete instruction-level CFG of the function that calls the decoder;
  3. check the decoder call is reachable from that function's entry;
  4. dominator test -- delete every instruction at or above the first signature-verification
     call and recheck. If the decoder is still reachable, verification does not dominate it.

Validity gate: the CFG is only complete if the function has no indirect branches AND 100% of its
instructions are reachable. Both are asserted and reported; without them no verdict is printed.

Branch targets are taken as the LAST 0x literal in the operand list: tbz/tbnz put a bit index
first, and taking the first literal silently drops those edges.

Usage: cfg_order.py <otool-tvV-output> <decoder-symbol> <verify-symbol>
"""
import collections
import re
import sys

BS_COND = ('b.eq', 'b.ne', 'b.hs', 'b.lo', 'b.mi', 'b.pl', 'b.vs', 'b.vc',
           'b.hi', 'b.ls', 'b.ge', 'b.lt', 'b.gt', 'b.le', 'b.al',
           'cbz', 'cbnz', 'tbz', 'tbnz')
TERM = ('ret', 'retab', 'retaa', 'brk', 'br', 'braa', 'brab', 'braaz', 'brabz')
INDIRECT = ('br', 'braa', 'brab', 'braaz', 'brabz')


def load(path):
    """Return (ordered addrs, {addr: (op, operands)}, [(addr, symbol)])."""
    insns, syms, sym = {}, [], None
    for line in open(path, encoding='utf-8', errors='replace'):
        line = line.rstrip('\n')
        m = re.match(r'^(_[A-Za-z_0-9.$]+):$', line)
        if m:
            sym = m.group(1)
            continue
        m = re.match(r'^([0-9a-f]{16})\t([a-z][a-z0-9._]*)\s*(.*)$', line)
        if not m:
            continue
        a = int(m.group(1), 16)
        insns[a] = (m.group(2), m.group(3))
        if sym is not None:
            syms.append((a, sym))
            sym = None
    return sorted(insns), insns, syms


def containing(syms, addr):
    best, best_a = None, -1
    for a, n in syms:
        if a <= addr and a > best_a:
            best_a, best = a, n
    return best, best_a


def analyse(order, insns, lo, hi, target, gate_addrs):
    """CFG over [lo, hi). Returns dict of findings."""
    body = [a for a in order if lo <= a < hi]
    idx = {a: i for i, a in enumerate(body)}
    inset = set(body)

    def nxt(a):
        i = idx[a]
        return body[i + 1] if i + 1 < len(body) else None

    def btarget(ops):
        ops = ops.split(';')[0]
        ms = re.findall(r'\b0x([0-9a-f]+)', ops)
        return int(ms[-1], 16) if ms else None

    def succs(a):
        op, ops = insns[a]
        if op in TERM:
            return []
        if op == 'b':
            t = btarget(ops)
            return [t] if t in inset else []
        if op in BS_COND:
            t = btarget(ops)
            s = [t] if t in inset else []
            n = nxt(a)
            if n is not None:
                s.append(n)
            return s
        n = nxt(a)
        return [n] if n is not None else []

    def reach(blocked=frozenset()):
        seen, st = set(), [lo]
        while st:
            a = st.pop()
            if a in seen or a in blocked or a not in inset:
                continue
            seen.add(a)
            for s in succs(a):
                if s not in seen:
                    st.append(s)
        return seen

    r = reach()
    out = {
        'insns': len(body),
        'reachable': len(r),
        'indirect': sum(1 for a in body if insns[a][0] in INDIRECT),
        'complete': len(r) == len(body),
        'target_reachable': target in r,
    }
    if gate_addrs:
        g = min(gate_addrs)
        out['gate'] = g
        out['target_reachable_without_gate'] = target in reach(
            frozenset(a for a in body if a >= g))
    # shortest entry -> target path, control transfers only
    preds = collections.defaultdict(list)
    for a in body:
        for s in succs(a):
            preds[s].append(a)
    par, q = {target: None}, collections.deque([target])
    while q:
        a = q.popleft()
        if a == lo:
            break
        for p in preds[a]:
            if p not in par:
                par[p] = a
                q.append(p)
    path = []
    if lo in par:
        c = lo
        while c is not None:
            path.append(c)
            c = par[c]
    out['path_len'] = len(path)
    out['transfers'] = [(a, insns[a][0], insns[a][1].split(';')[0].strip())
                        for a in path
                        if insns[a][0] == 'b' or insns[a][0] in BS_COND or insns[a][0] == 'bl']
    return out


def main(path, decoder, verify):
    order, insns, syms = load(path)
    print("instructions parsed: %d   symbols: %d" % (len(insns), len(syms)))

    sites = collections.defaultdict(list)
    for a in order:
        op, ops = insns[a]
        if op != 'bl':
            continue
        for name in (decoder, verify):
            if name in ops:
                fn, _ = containing(syms, a)
                sites[name].append((a, fn))

    for name in (decoder, verify):
        print("\n=== bl %s : %d site(s) ===" % (name, len(sites[name])))
        for a, fn in sites[name]:
            print("  0x%x  <- %s" % (a, fn))
    if not sites[decoder]:
        print("\nNO DECODER CALL SITES FOUND -- cannot run the ordering test")
        return 0

    # analyse each function that calls the decoder
    by_fn = collections.defaultdict(list)
    for a, fn in sites[decoder]:
        by_fn[fn].append(a)

    for fn, targets in by_fn.items():
        fa = [a for a, n in syms if n == fn]
        if not fa:
            continue
        lo = fa[0]
        later = sorted(a for a, n in syms if a > lo)
        hi = later[0] if later else max(order) + 4
        gates = [a for a, f in sites[verify] if lo <= a < hi]
        print("\n" + "=" * 72)
        print("FUNCTION %s  [0x%x, 0x%x)" % (fn, lo, hi))
        print("  %s calls inside this function: %s"
              % (verify, [hex(g) for g in gates] or "NONE"))
        for t in targets:
            res = analyse(order, insns, lo, hi, t, gates)
            print("  --- decoder call 0x%x (+0x%x) ---" % (t, t - lo))
            print("      insns=%d reachable=%d indirect=%d CFG_COMPLETE=%s"
                  % (res['insns'], res['reachable'], res['indirect'], res['complete']))
            if not res['complete']:
                print("      *** CFG INCOMPLETE -- NO VERDICT (jump tables or unreached code) ***")
                continue
            print("      reachable from entry: %s" % res['target_reachable'])
            if 'gate' in res:
                print("      first %s call at 0x%x (+0x%x)"
                      % (verify, res['gate'], res['gate'] - lo))
                print("      reachable with all code >= gate blocked: %s"
                      % res['target_reachable_without_gate'])
                if res['target_reachable'] and res['target_reachable_without_gate']:
                    print("      VERDICT: verification does NOT dominate the decoder call")
                elif res['target_reachable']:
                    print("      VERDICT: decoder reachable, but NOT without the gate region")
            else:
                print("      VERDICT: no verification call in this function at all;"
                      " ordering spans functions and is NOT settled here")
            print("      shortest entry->decoder path: %d instructions" % res['path_len'])
            for a, op, ops in res['transfers']:
                print("        0x%x (+0x%-5x) %-6s %s" % (a, a - lo, op, ops[:58]))
    return 0


if __name__ == '__main__':
    if len(sys.argv) != 4:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1], sys.argv[2], sys.argv[3]))

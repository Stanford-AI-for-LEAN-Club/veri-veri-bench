#!/usr/bin/env python3
"""Read Maude output from stdin, extract the Out buffer (the int list
after the last top-level comma in the result Configuration), and emit
one int per line — matching what CPython's `print(int)` would write."""

from __future__ import annotations
import re
import sys


def main() -> int:
    raw = sys.stdin.read()
    # Maude output is line-wrapped; un-wrap with continuation handling.
    # Find the line(s) starting with "result " (Maude wraps long results
    # across multiple indented lines).
    # Maude wraps long results across lines indented with at least 4
    # spaces.  Capture the result as long as continuation lines are
    # indented; stop at the next non-indented line (Bye./Maude>/etc.).
    m = re.search(
        r"^result\s+\S+\s*:\s*(?P<term>.+?)(?=^[^ \t])",
        raw,
        re.M | re.S,
    )
    if not m:
        # No result line — likely a parse / rewrite error upstream.
        return 2
    term = m.group("term").strip()
    # term looks like:  < <state>, <out> >
    # Strip the outermost angle brackets.
    if not (term.startswith("<") and term.endswith(">")):
        return 3
    inside = term[1:-1].strip()
    # In pythonlite v1 the state has the shape  'x |-> N & 'y |-> M & …
    # — note that `|->` contains a literal '>', so a naive bracket-depth
    # counter underflows.  Each variable in pythonlite gets its own
    # |-> binding (no IMP-style `(x,y) |-> 0` group bindings), so the
    # FIRST top-level ',' we see is always the state/out separator.
    split = inside.find(",")
    if split == -1:
        # No comma — just the state, output buffer is empty .Out.
        return 0
    out_str = inside[split + 1:].strip()
    out_str = re.sub(r"\s+", " ", out_str)
    if out_str == ".Out":
        return 0
    parts = [p.strip() for p in out_str.split("::")]
    for p in parts:
        # Strip whitespace and convert "(- N)" / "-Int N" to "-N".
        cleaned = p.replace("(", "").replace(")", "").strip()
        cleaned = re.sub(r"-Int\s*", "-", cleaned)
        cleaned = re.sub(r"\s+", "", cleaned)
        if cleaned:
            print(cleaned)
    return 0


if __name__ == "__main__":
    sys.exit(main())

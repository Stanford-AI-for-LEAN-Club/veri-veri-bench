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
    # The configuration is  < state, out >  — strip the outer angle
    # brackets above, then split state from out at the *outermost*
    # top-level comma.  Watch out: state can contain commas inside
    # `cons(_, _)` (cycle 2 list values), `consE(_, _)` (list-literal
    # nodes), and other constructors with multiple args; out can too.
    # Use a depth counter on `(` and `)` (and on `[` `]` for sort-kind
    # forms like `[Int]`); skip any comma at depth > 0.
    depth = 0
    split = -1
    for i, ch in enumerate(inside):
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif ch == "," and depth == 0:
            split = i
            break
    if split == -1:
        # No top-level comma — just the state, output buffer is empty.
        return 0
    out_str = inside[split + 1:].strip()
    out_str = re.sub(r"\s+", " ", out_str)
    if out_str == ".Out":
        return 0
    parts = [p.strip() for p in out_str.split("::")]
    for p in parts:
        cleaned = p.strip()
        if not cleaned:
            continue
        # Maude prints values:
        #   integers     ->  N    or  (- N)  or  -Int N
        #   booleans     ->  true / false              -> Python  True / False
        #   strings      ->  "the literal"             -> Python  the literal
        #   none         ->  none                      -> Python  None
        # We reformat to match Python's str(value) so byte-comparison
        # against CPython's stdout works.
        if cleaned == "true":
            print("True")
        elif cleaned == "false":
            print("False")
        elif cleaned == "none":
            print("None")
        elif cleaned.startswith('"') and cleaned.endswith('"'):
            inner = cleaned[1:-1]
            inner = (inner.replace("\\\\", "\\")
                          .replace('\\"', '"')
                          .replace("\\n", "\n")
                          .replace("\\t", "\t"))
            print(inner)
        else:
            # integer-ish:  strip parens, "-Int " prefix, internal whitespace
            num = cleaned.replace("(", "").replace(")", "")
            num = re.sub(r"-Int\s*", "-", num)
            num = re.sub(r"\s+", "", num)
            print(num)
    return 0


if __name__ == "__main__":
    sys.exit(main())

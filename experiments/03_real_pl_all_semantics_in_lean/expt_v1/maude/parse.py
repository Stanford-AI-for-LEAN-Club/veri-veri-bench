#!/usr/bin/env python3
"""Convert a real Python source file into the equivalent pythonlite Maude
AST (a single Pgm constant).

Scope: pythonlite v1 - integers, booleans, identifiers, the operators
+, -, *, //, %, unary -, comparisons (<, <=, >, >=, ==, !=), boolean
and / or / not, assignment, print, if/else, while, sequencing.

Usage:
    python3 parse.py tests/04_factorial.py myProgConst > /tmp/myProg.maude
    # produces a Maude module fragment:
    #   eq myProgConst = ( ... maude AST ... ) .
"""

from __future__ import annotations
import ast
import sys

UNSUPPORTED = "pythonlite v1 does not support: "


def emit_expr(n: ast.AST) -> str:
    if isinstance(n, ast.Constant):
        if n.value is None:
            return "none"
        if isinstance(n.value, bool):
            return "true" if n.value else "false"
        if isinstance(n.value, int):
            return f"({n.value})" if n.value < 0 else str(n.value)
        if isinstance(n.value, str):
            # Maude string literal: double-quoted, with backslash-escapes for
            # ", \, newline, tab.  Python's repr() for a str gives single
            # quotes by default; build it ourselves.
            esc = (
                n.value.replace("\\", "\\\\")
                       .replace("\"", "\\\"")
                       .replace("\n", "\\n")
                       .replace("\t", "\\t")
            )
            return f"\"{esc}\""
        raise SystemExit(UNSUPPORTED + f"literal {n.value!r}")
    if isinstance(n, ast.Name):
        return f"'{n.id}"
    if isinstance(n, ast.UnaryOp):
        op = n.op
        if isinstance(op, ast.USub):
            inner = emit_expr(n.operand)
            return f"(uminus {inner})"
        if isinstance(op, ast.Not):
            return f"(not {emit_expr(n.operand)})"
        raise SystemExit(UNSUPPORTED + f"unary op {type(op).__name__}")
    if isinstance(n, ast.BinOp):
        op = n.op
        ops = {
            ast.Add: "+",
            ast.Sub: "-",
            ast.Mult: "*",
            ast.FloorDiv: "//",
            ast.Mod: "%",
        }
        sym = ops.get(type(op))
        if sym is None:
            raise SystemExit(UNSUPPORTED + f"binop {type(op).__name__}")
        return f"({emit_expr(n.left)} {sym} {emit_expr(n.right)})"
    if isinstance(n, ast.BoolOp):
        sym = "and" if isinstance(n.op, ast.And) else "or"
        # left-associative fold
        parts = [emit_expr(v) for v in n.values]
        out = parts[0]
        for p in parts[1:]:
            out = f"({out} {sym} {p})"
        return out
    if isinstance(n, ast.Call):
        if isinstance(n.func, ast.Name) and n.func.id == "len":
            if len(n.args) != 1 or n.keywords:
                raise SystemExit(UNSUPPORTED + "len() with multiple / keyword args")
            return f"len({emit_expr(n.args[0])})"
        raise SystemExit(UNSUPPORTED + f"call to {ast.dump(n.func)}")
    if isinstance(n, ast.List):
        # Python:  [e1, e2, ..., en]   ->   listLit(consE(e1, consE(e2, ..., nilE)))
        elts = "nilE"
        for e in reversed(n.elts):
            elts = f"consE({emit_expr(e)}, {elts})"
        return f"listLit({elts})"
    if isinstance(n, ast.Subscript):
        # Python:  xs[i]   ->   (xs ! i)
        if not isinstance(n.slice, (ast.Constant, ast.Name, ast.BinOp, ast.Subscript, ast.Compare, ast.UnaryOp, ast.Call)):
            # ast.Slice (a:b) deferred
            raise SystemExit(UNSUPPORTED + f"subscript slice {type(n.slice).__name__}")
        return f"({emit_expr(n.value)} ! {emit_expr(n.slice)})"
    if isinstance(n, ast.Compare):
        if len(n.ops) != 1 or len(n.comparators) != 1:
            raise SystemExit(UNSUPPORTED + "chained comparisons")
        op = n.ops[0]
        sym = {
            ast.Lt: "<",
            ast.LtE: "<=",
            ast.Gt: ">",
            ast.GtE: ">=",
            ast.Eq: "eqq",
            ast.NotEq: "neq",
        }.get(type(op))
        if sym is None:
            raise SystemExit(UNSUPPORTED + f"comparison {type(op).__name__}")
        return f"({emit_expr(n.left)} {sym} {emit_expr(n.comparators[0])})"
    raise SystemExit(UNSUPPORTED + f"expr node {type(n).__name__}")


def emit_stmt(n: ast.AST) -> str:
    if isinstance(n, ast.Assign):
        if len(n.targets) != 1:
            raise SystemExit(UNSUPPORTED + "multi-target assignment")
        tgt = n.targets[0]
        if isinstance(tgt, ast.Name):
            return f"('{tgt.id} := {emit_expr(n.value)})"
        if isinstance(tgt, ast.Subscript) and isinstance(tgt.value, ast.Name):
            return f"('{tgt.value.id} [{emit_expr(tgt.slice)}] := {emit_expr(n.value)})"
        raise SystemExit(UNSUPPORTED + f"assignment target {type(tgt).__name__}")
    if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call):
        c = n.value
        if isinstance(c.func, ast.Name) and c.func.id == "print":
            if len(c.args) != 1 or c.keywords:
                raise SystemExit(UNSUPPORTED + "print() with multiple / keyword args")
            return f"print({emit_expr(c.args[0])})"
        # xs.append(v) — the canonical Python list-mutation idiom
        if isinstance(c.func, ast.Attribute) and c.func.attr == "append" \
                and isinstance(c.func.value, ast.Name):
            if len(c.args) != 1 or c.keywords:
                raise SystemExit(UNSUPPORTED + "append() with multiple / keyword args")
            return f"('{c.func.value.id} .append({emit_expr(c.args[0])}))"
        raise SystemExit(UNSUPPORTED + f"call statement to {ast.dump(c.func)}")
    if isinstance(n, ast.If):
        cond = emit_expr(n.test)
        body = emit_block(n.body)
        orelse = emit_block(n.orelse) if n.orelse else "pass"
        return f"ifelse({cond})" + "{" + body + "}else{" + orelse + "}"
    if isinstance(n, ast.While):
        if n.orelse:
            raise SystemExit(UNSUPPORTED + "while-else")
        cond = emit_expr(n.test)
        body = emit_block(n.body)
        return f"while({cond})" + "{" + body + "}"
    if isinstance(n, ast.Pass):
        return "pass"
    raise SystemExit(UNSUPPORTED + f"stmt node {type(n).__name__}")


def emit_block(stmts: list[ast.AST]) -> str:
    if not stmts:
        return "pass"
    return " ; ".join(emit_stmt(s) for s in stmts)


def main():
    if len(sys.argv) != 3:
        print("usage: parse.py <python-source.py> <pgm-const-name>", file=sys.stderr)
        sys.exit(2)
    src_path, const_name = sys.argv[1], sys.argv[2]
    with open(src_path) as h:
        src = h.read()
    tree = ast.parse(src, filename=src_path, mode="exec")
    body = emit_block(tree.body)
    # emit a Maude module fragment compatible with PYTHONLITE-PROGRAMS
    print("--- auto-generated by parse.py from " + src_path)
    print("mod " + const_name.upper() + "-PROG is including PYTHONLITE-SYNTAX .")
    print(f"  op {const_name} : -> Pgm .")
    print(f"  eq {const_name} = ( {body} ) .")
    print("endm")


if __name__ == "__main__":
    main()

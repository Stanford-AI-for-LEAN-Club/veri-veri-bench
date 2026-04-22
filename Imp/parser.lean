/-!
# IMP — tokenizer and recursive-descent parser

Turns raw IMP source (a `String`) into an abstract syntax tree (`Com`).

The pipeline is two stages:

1. **`tokenize`** — character-by-character lexer producing a `List String`
   of tokens. Identifiers and numbers are greedy; the multi-character
   operators `:=`, `<=`, `&&`, `||` are recognised explicitly; the single
   characters `( ) { } ; + - * = !` become tokens on their own; whitespace
   is discarded. Unknown characters are silently dropped.

2. **`parseCom`** (plus helpers `parseAexp`, `parseBexp`) — a recursive-descent
   parser over the token list. The top-level entry points are:
   - `parseComAll aNames tokens` : requires that the whole token list be consumed.
   - `parseComAllStr aNames s`   : convenience wrapper that tokenizes `s` first,
     and falls back to `Com.skip` on any parse failure.

The `aNames` argument is the list of variable names the parser is allowed to
recognise in arithmetic positions — anything else is rejected as an `Aexp.var`.

## Grammar (informal)

```
a ::= n | x | "(" a op a ")"                    op ∈ { +, -, * }
b ::= "true" | "false" | "!" b
    | "(" a rel a ")" | "(" b bop b ")"         rel ∈ { =, <= }, bop ∈ { &&, || }
c ::= "skip"
    | x ":=" a
    | "if" b "then" block "else" block
    | "while" b "do" block
    | c ";" c
block ::= c | "{" c ("; " c)* "}"
```

Because the parsers are mutually/deeply recursive they are marked `partial`.
-/

import Imp.main

open Imp

namespace Imp

/-- Parse an arithmetic expression from a token list, returning the parsed
`Aexp` together with the remaining tokens, or `none` on failure.

* A parenthesised form `"(" a op a ")"` handles `+`, `-`, `*`.
* A bare token is an `Aexp.const` if it parses as an integer, otherwise an
  `Aexp.var` if it appears in `aNames`; anything else fails.
-/
partial def parseAexp (aNames : List String) : List String → Option (Aexp × List String)
  | "(" :: rest => do
      let (a, rest1) ← parseAexp aNames rest
      match rest1 with
      | "+" :: rest2 =>
          let (b, rest3) ← parseAexp aNames rest2
          match rest3 with
          | ")" :: rest4 => some (Aexp.add a b, rest4)
          | _ => none
      | "-" :: rest2 =>
          let (b, rest3) ← parseAexp aNames rest2
          match rest3 with
          | ")" :: rest4 => some (Aexp.sub a b, rest4)
          | _ => none
      | "*" :: rest2 =>
          let (b, rest3) ← parseAexp aNames rest2
          match rest3 with
          | ")" :: rest4 => some (Aexp.mul a b, rest4)
          | _ => none
      | _ => none
  | tok :: rest =>
      if let some n := tok.toInt? then
        some (Aexp.const n, rest)
      else if tok ∈ aNames then
        some (Aexp.var tok, rest)
      else
        none
  | [] => none

#eval parseAexp ["x", "y", "z"] ["(", "x", "-", "2", ")"]

/-- Parse a boolean expression from a token list.

Handles, in order:
* Negation `! b`.
* Parenthesised forms `(a = a)`, `(a <= a)` (relational, preferred),
  then `(b && b)`, `(b || b)` (boolean, tried as a fallback if the
  inner tokens don't start with an `Aexp`).
* The literals `true`/`false`.
* Unparenthesised relational forms starting with an `Aexp` (included for
  slightly more permissive inputs).

Returns `(b, remaining_tokens)` on success or `none` otherwise. -/
partial def parseBexp (aNames : List String) :
    List String → Option (Bexp × List String)
  | "!" :: rest => do
      let (b, rest1) ← parseBexp aNames rest
      some (Bexp.neg b, rest1)
  | "(" :: rest => do
      -- First try relational forms: (a = b) or (a <= b)
      match parseAexp aNames rest with
      | some (a, rest1) =>
          match rest1 with
          | "=" :: rest2 =>
              let (b, rest3) ← parseAexp aNames rest2
              match rest3 with
              | ")" :: rest4 => some (Bexp.eq a b, rest4)
              | _ => none
          | "<=" :: rest2 =>
              let (b, rest3) ← parseAexp aNames rest2
              match rest3 with
              | ")" :: rest4 => some (Bexp.le a b, rest4)
              | _ => none
          | _ =>
              -- Fall back to boolean binary forms: (b && c) or (b || c)
              match parseBexp aNames rest with
              | some (b, rest1') =>
                  match rest1' with
                  | "&&" :: rest2 =>
                      let (c, rest3) ← parseBexp aNames rest2
                      match rest3 with
                      | ")" :: rest4 => some (Bexp.and b c, rest4)
                      | _ => none
                  | "||" :: rest2 =>
                      let (c, rest3) ← parseBexp aNames rest2
                      match rest3 with
                      | ")" :: rest4 => some (Bexp.or b c, rest4)
                      | _ => none
                  | _ => none
              | none => none
      | none =>
          -- No arithmetic expression at the start; try boolean binary forms.
          match parseBexp aNames rest with
          | some (b, rest1') =>
              match rest1' with
              | "&&" :: rest2 =>
                  let (c, rest3) ← parseBexp aNames rest2
                  match rest3 with
                  | ")" :: rest4 => some (Bexp.and b c, rest4)
                  | _ => none
              | "||" :: rest2 =>
                  let (c, rest3) ← parseBexp aNames rest2
                  match rest3 with
                  | ")" :: rest4 => some (Bexp.or b c, rest4)
                  | _ => none
              | _ => none
          | none => none
  | aTok :: rest => do
      if aTok = "true" then
        some (Bexp.true, rest)
      else if aTok = "false" then
        some (Bexp.false, rest)
      else
        -- Try to parse "(a = b)" or "(a <= b)" forms.
        match parseAexp aNames (aTok :: rest) with
        | none => none
        | some (a, rest1) =>
            match rest1 with
            | "=" :: rest2 =>
                let (b, rest3) ← parseAexp aNames rest2
                match rest3 with
                | ")" :: rest4 => some (Bexp.eq a b, rest4)
                | _ => none
            | "<=" :: rest2 =>
                let (b, rest3) ← parseAexp aNames rest2
                match rest3 with
                | ")" :: rest4 => some (Bexp.le a b, rest4)
                | _ => none
            | _ => none
  | [] => none

#eval parseBexp ["x", "y", "z"] ["(", "x", "<=", "y", ")"]

/-- Parse an IMP command from a token list.

Recognises:
* `skip` — the no-op.
* `if b then <block-or-com> else <block-or-com>`.
* `while b do <block-or-com>`.
* `x := a` — assignment.

After parsing a statement, `parseSeq` optionally consumes a trailing
`; <com>` and wraps the result in `Com.comp`, giving right-associative
sequencing.

The local `where`-helpers split the work:
* `parseBlockOrCom` — either a braced block `{ ... }` or a single command.
* `parseBlock`      — the body of a `{ ... }`, consuming `;`-separated
  commands until the closing `}`.
* `parseSeq`        — glue a single parsed command onto an optional `; c`.
* `parseSeqBlock`   — same idea inside a block; terminates on `}`.
-/
partial def parseCom (aNames : List String) :
    List String → Option (Com × List String)
  | [] => none
  | "skip" :: rest => some (Com.skip, rest)
  | "if" :: rest => do
      let (b, rest1) ← parseBexp aNames rest
      match rest1 with
      | "then" :: rest2 =>
          let (c, rest3) ← parseBlockOrCom rest2
          match rest3 with
          | "else" :: rest4 =>
              let (d, rest5) ← parseBlockOrCom rest4
              parseSeq (Com.ite b c d) rest5
          | _ => none
      | _ => none
  | "while" :: rest => do
      let (b, rest1) ← parseBexp aNames rest
      match rest1 with
      | "do" :: rest2 =>
          let (c, rest3) ← parseBlockOrCom rest2
          parseSeq (Com.while b c) rest3
      | _ => none
  | x :: ":=" :: rest => do
      let (a, rest1) ← parseAexp aNames rest
      parseSeq (Com.assign x a) rest1
  | _ => none
where
  parseBlockOrCom : List String → Option (Com × List String)
    | "{" :: rest => parseBlock rest
    | rest => parseCom aNames rest
  parseBlock : List String → Option (Com × List String)
    | rest => do
        let (c, rest1) ← parseCom aNames rest
        parseSeqBlock c rest1
  parseSeq (c : Com) : List String → Option (Com × List String)
    | ";" :: rest => do
        let (d, rest1) ← parseCom aNames rest
        some (Com.comp c d, rest1)
    | rest => some (c, rest)
  parseSeqBlock (c : Com) : List String → Option (Com × List String)
    | ";" :: rest => do
        let (d, rest1) ← parseCom aNames rest
        parseSeqBlock (Com.comp c d) rest1
    | "}" :: rest => some (c, rest)
    | _ => none

/-- Run `parseCom` and insist that the entire token list is consumed;
returns `none` if any trailing tokens remain. -/
def parseComAll (aNames : List String) (tokens : List String) : Option Com := do
  let (c, rest) ← parseCom aNames tokens
  if rest.isEmpty then some c else none

/-- Tokenizer helper: split `cs` into the longest prefix whose characters
all satisfy `p`, and the remaining suffix. -/
def tokenizeTakeWhile (p : Char → Bool) (cs : List Char) :
    List Char × List Char :=
  match cs with
  | c :: rest =>
      if p c then
        let (taken, rest') := tokenizeTakeWhile p rest
        (c :: taken, rest')
      else
        ([], cs)
  | [] => ([], [])

/-- Main tokenizer loop. Collects tokens in `acc` in reverse order and
reverses once the input is exhausted. Recognises numbers, identifiers
(`[A-Za-z_][A-Za-z0-9_]*`), the two-character operators `:=`, `<=`, `&&`,
`||`, and the single-character delimiters / operators
`( ) { } ; + - * = !`. Whitespace and unknown characters are skipped. -/
partial def tokenizeGo (cs : List Char) (acc : List String) : List String :=
  match cs with
  | [] => acc.reverse
  | c :: rest =>
      if c.isWhitespace then
        tokenizeGo rest acc
      else if c.isDigit then
        let (more, rest') := tokenizeTakeWhile (fun d => d.isDigit) rest
        tokenizeGo rest' (String.ofList (c :: more) :: acc)
      else if (c.isAlpha || c = '_') then
        let (more, rest') := tokenizeTakeWhile (fun d => d.isAlphanum || d = '_') rest
        tokenizeGo rest' (String.ofList (c :: more) :: acc)
      else
        match c with
        | ':' =>
            match rest with
            | '=' :: rest2 => tokenizeGo rest2 (":=" :: acc)
            | _ => tokenizeGo rest (":" :: acc)
        | '<' =>
            match rest with
            | '=' :: rest2 => tokenizeGo rest2 ("<=" :: acc)
            | _ => tokenizeGo rest ("<" :: acc)
        | '&' =>
            match rest with
            | '&' :: rest2 => tokenizeGo rest2 ("&&" :: acc)
            | _ => tokenizeGo rest ("&" :: acc)
        | '|' =>
            match rest with
            | '|' :: rest2 => tokenizeGo rest2 ("||" :: acc)
            | _ => tokenizeGo rest ("|" :: acc)
        | '(' | ')' | '{' | '}' | ';' | '+' | '-' | '*' | '=' | '!' =>
            tokenizeGo rest (String.singleton c :: acc)
        | _ =>
            tokenizeGo rest acc

/-- Tokenize an IMP source string into a flat list of token strings. -/
def tokenize (s : String) : List String :=
  tokenizeGo s.toList []

/-- End-to-end convenience: tokenize `s`, run `parseComAll`, and fall back
to `Com.skip` on any failure (so the return type can be `Com` rather than
`Option Com`). Intended for `#eval` / example use; real code paths should
prefer `parseComAll`, which surfaces errors. -/
def parseComAllStr (aNames : List String) (s : String) : Com :=
  (parseComAll aNames (tokenize s)).getD Com.skip

#eval parseComAllStr ["x"] "x := 10; while (0 <= x) do x := (x - 1)"

#eval parseComAllStr ["x"] "while true do {skip; skip}"

end Imp

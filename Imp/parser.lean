import Imp.main

open Imp

namespace Imp

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

def parseComAll (aNames : List String) (tokens : List String) : Option Com := do
  let (c, rest) ← parseCom aNames tokens
  if rest.isEmpty then some c else none

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

def tokenize (s : String) : List String :=
  tokenizeGo s.toList []

def parseComAllStr (aNames : List String) (s : String) : Com :=
  (parseComAll aNames (tokenize s)).getD Com.skip

#eval parseComAllStr ["x"] "x := 10; while (0 <= x) do x := (x - 1)"

#eval parseComAllStr ["x"] "while true do {skip; skip}"

end Imp

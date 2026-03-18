import DependentComputability.ParserSample.Extension

syntax "hi" : command

--attribute [run_parser_attribute_hooks] Lean.Parser.Command.declaration

open Lean Parser

@[combinator_parser_sampler _root_.ite, expose, macro_inline]
def ite.parser_sampler {_ : Type} (c : Prop) [Decidable c] (t e : ParserSampler) : ParserSampler :=
  if c then t else e

@[combinator_parser_sampler withCache, expose]
def withCache.parser_sampler (_ : Name) (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler andthen, expose]
def andthen.parser_sampler (p1 p2 : ParserSampler) : ParserSampler := fun ctx =>
  let left := p1 ctx
  let right := p2 ctx
  if left.isEmpty || right.isEmpty then #[] else
  let fstleft := left[0]!
  let fstright := right[0]!
  right.map (fstleft ++ ·) ++ (left.drop 1).map (· ++ fstright)

@[combinator_parser_sampler node, expose]
def node.parser_sampler (n : SyntaxNodeKind) (p : ParserSampler) : ParserSampler := fun ctx =>
  (p ctx).map (#[.node .none n ·])

@[combinator_parser_sampler error, expose]
def error.parser_sampler (_ : String) : ParserSampler := fun _ => #[]

@[combinator_parser_sampler errorAtSavedPos, expose]
def errorAtSavedPos.parser_sampler (_ : String) (_ : Bool) : ParserSampler := fun _ => #[]

@[combinator_parser_sampler checkPrec, expose]
def checkPrec.parser_sampler (_ : Nat) : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler checkLhsPrec, expose]
def checkLhsPrec.parser_sampler (_ : Nat) : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler setLhsPrec, expose]
def setLhsPrec.parser_sampler (_ : Nat) : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler incQuotDepth, expose]
def incQuotDepth.parser_sampler (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler decQuotDepth, expose]
def decQuotDepth.parser_sampler (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler withFn, expose]
def withFn.parser_sampler (_ : ParserFn → ParserFn) (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler suppressInsideQuot, expose]
def suppressInsideQuot.parser_sampler (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler trailingNodeAux, expose]
def trailingNodeAux.parser_sampler (n : SyntaxNodeKind) (p : ParserSampler) : ParserSampler := fun ctx =>
  (p ctx).map (#[.node .none n <| #[.missing] ++ ·])

attribute [run_parser_attribute_hooks] leadingNode trailingNode

@[combinator_parser_sampler orelse, expose]
def orelse.parser_sampler (p1 p2 : ParserSampler) : ParserSampler := fun ctx =>
  p1 ctx ++ p2 ctx

@[combinator_parser_sampler atomic, expose]
def atomic.parser_sampler (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler recover', expose]
def recover'.parser_sampler (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler recover, expose]
def recover.parser_sampler (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler optionalNoAntiquot, expose]
def optionalNoAntiquot.parser_sampler (p : ParserSampler) : ParserSampler := fun ctx =>
  #[#[mkNullNode]] ++ (p ctx).map (fun x => #[mkNullNode x])

@[combinator_parser_sampler lookahead, expose]
def lookahead.parser_sampler (_ : ParserSampler) : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler notFollowedBy, expose]
def notFollowedBy.parser_sampler (_ : ParserSampler) (_ : String) : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler many1NoAntiquot, expose]
def many1NoAntiquot.parser_sampler (p : ParserSampler) : ParserSampler := fun ctx =>
  let res := p ctx
  if res.isEmpty then
    #[]
  else
    let fst := res[0]!
    res.map (fun x => #[mkNullNode x]) |>.push #[mkNullNode (fst ++ fst)]

@[combinator_parser_sampler manyNoAntiquot, expose]
def manyNoAntiquot.parser_sampler (p : ParserSampler) : ParserSampler := fun ctx =>
  #[#[mkNullNode]] ++ many1NoAntiquot.parser_sampler p ctx

@[combinator_parser_sampler sepBy1NoAntiquot, expose]
def sepBy1NoAntiquot.parser_sampler (p sep : ParserSampler) (allowTrailingSep : Bool := false) : ParserSampler := fun ctx =>
  let res := p ctx
  let sepRes := sep ctx
  if res.isEmpty then
    #[]
  else if sepRes.isEmpty then
    res.map (fun x => #[mkNullNode x])
  else
    let fst := res[0]!
    let fstsep := sepRes[0]!
    let res := if allowTrailingSep then res.push (fst ++ fstsep) else res
    let res := res ++ sepRes.map (fst ++ · ++ fst)
    res.map (fun x => #[mkNullNode x])

@[combinator_parser_sampler sepByNoAntiquot, expose]
def sepByNoAntiquot.parser_sampler (p sep : ParserSampler) (allowTrailingSep : Bool := false) : ParserSampler := fun ctx =>
  #[#[mkNullNode]] ++ sepBy1NoAntiquot.parser_sampler p sep allowTrailingSep ctx

@[combinator_parser_sampler withResultOf, expose]
def withResultOf.parser_sampler (p : ParserSampler) (f : Syntax → Syntax) : ParserSampler := fun ctx =>
  (p ctx).map (fun arr => if arr.isEmpty then arr else let back := arr.back!; arr.pop.push (f back))

attribute [run_parser_attribute_hooks] many1Unbox

@[combinator_parser_sampler symbolNoAntiquot, expose]
def symbolNoAntiquot.parser_sampler (sym : String) : ParserSampler := fun _ctx =>
  let sym := sym.trimAscii.copy
  #[#[.atom SourceInfo.none sym]]

@[combinator_parser_sampler nonReservedSymbolNoAntiquot, expose]
def nonReservedSymbolNoAntiquot.parser_sampler (sym : String) : ParserSampler := fun _ctx =>
  let sym := sym.trimAscii.copy
  #[#[.atom SourceInfo.none sym]]

@[combinator_parser_sampler checkWsBefore, expose]
def checkWsBefore.parser_sampler : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler checkLinebreakBefore, expose]
def checkLinebreakBefore.parser_sampler : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler checkNoWsBefore, expose]
def checkNoWsBefore.parser_sampler : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler unicodeSymbolNoAntiquot, expose]
def unicodeSymbolNoAntiquot.parser_sampler (sym asciiSym : String) : ParserSampler := fun _ctx =>
  let sym := sym.trimAscii.copy
  let asciiSym := asciiSym.trimAscii.copy
  #[#[.atom SourceInfo.none sym], #[.atom SourceInfo.none asciiSym]]

@[combinator_parser_sampler numLitNoAntiquot, expose]
def numLitNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[Syntax.mkLit numLitKind "1234"], #[Syntax.mkLit numLitKind "0xffac_1234"]]

@[combinator_parser_sampler hexnumNoAntiquot, expose]
def hexnumNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[Syntax.mkLit hexnumKind "ffac_1234"]]

@[combinator_parser_sampler scientificLitNoAntiquot, expose]
def scientificLitNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[Syntax.mkLit scientificLitKind "3.29e-10"]]

@[combinator_parser_sampler strLitNoAntiquot, expose]
def strLitNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[Syntax.mkLit strLitKind r#""hello""#], #[Syntax.mkLit strLitKind r##"r#"hello"#"##]]

@[combinator_parser_sampler charLitNoAntiquot, expose]
def charLitNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[Syntax.mkLit charLitKind "'A'"], #[Syntax.mkLit charLitKind "'\\u12fa'"]]

@[combinator_parser_sampler nameLitNoAntiquot, expose]
def nameLitNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[Syntax.mkLit nameLitKind "`Lean.Name"]]

@[combinator_parser_sampler identNoAntiquot, expose]
def identNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[mkIdent `myIdent]]

@[combinator_parser_sampler rawIdentNoAntiquot, expose]
def rawIdentNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[mkIdent `myRawIdent]]

@[combinator_parser_sampler hygieneInfoNoAntiquot, expose]
def hygieneInfoNoAntiquot.parser_sampler : ParserSampler := fun _ctx =>
  #[#[mkNode hygieneInfoKind #[mkIdent .anonymous]]]

@[combinator_parser_sampler checkColEq, expose]
def checkColEq.parser_sampler : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler checkColGe, expose]
def checkColGe.parser_sampler : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler checkColGt, expose]
def checkColGt.parser_sampler : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler checkLineEq, expose]
def checkLineEq.parser_sampler : ParserSampler := fun _ => #[#[]]

attribute [run_parser_attribute_hooks] withPosition withPositionAfterLinebreak withoutPosition withForbidden withoutForbidden setExpected

@[combinator_parser_sampler checkNoImmediateColon, expose]
def checkNoImmediateColon.parser_sampler : ParserSampler := fun _ => #[#[]]

@[combinator_parser_sampler pushNone, expose]
def pushNone.parser_sampler : ParserSampler := fun _ => #[#[mkNullNode]]

@[combinator_parser_sampler antiquotExpr, expose]
def antiquotExpr.parser_sampler : ParserSampler := symbolNoAntiquot.parser_sampler "_"

@[combinator_parser_sampler tokenWithAntiquot, expose]
def tokenWithAntiquot.parser_sampler (p : ParserSampler) : ParserSampler := fun ctx =>
  if ctx.includeAntiquots then
    let x := andthen.parser_sampler p (andthen.parser_sampler (symbolNoAntiquot.parser_sampler "%")
      (andthen.parser_sampler (symbolNoAntiquot.parser_sampler "$") antiquotExpr.parser_sampler))
    p ctx ++ node.parser_sampler `token_antiquot x ctx
  else
    p ctx

attribute [run_parser_attribute_hooks] symbol nonReservedSymbol unicodeSymbol

@[combinator_parser_sampler mkAntiquot, expose]
def mkAntiquot.parser_sampler (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := false) : ParserSampler :=
  let kind := kind ++ (if isPseudoKind then `pseudo else .anonymous) ++ `antiquot
  let nameP := node.parser_sampler `antiquotName <| andthen.parser_sampler (symbol.parser_sampler ":") (nonReservedSymbol.parser_sampler name)
  -- if parsing the kind fails and `anonymous` is true, check that we're not ignoring a different
  -- antiquotation kind via `noImmediateColon`
  let nameP := if anonymous then orelse.parser_sampler nameP (andthen.parser_sampler checkNoImmediateColon.parser_sampler pushNone.parser_sampler) else nameP
  -- antiquotations are not part of the "standard" syntax, so hide "expected '$'" on error
  leadingNode.parser_sampler kind maxPrec <| atomic.parser_sampler <|
    andthen.parser_sampler
      (andthen.parser_sampler
        (andthen.parser_sampler
          (setExpected.parser_sampler [] (symbol.parser_sampler "$"))
          (manyNoAntiquot.parser_sampler (symbol.parser_sampler "$")))
        antiquotExpr.parser_sampler)
      nameP

@[combinator_parser_sampler withAntiquot, expose]
def withAntiquot.parser_sampler (antiP p : ParserSampler) : ParserSampler := fun ctx =>
  if ctx.includeAntiquots then
    orelse.parser_sampler p antiP ctx
  else
    p ctx

@[combinator_parser_sampler withoutInfo, expose]
def withoutInfo.parser_sampler (p : ParserSampler) : ParserSampler := p

attribute [run_parser_attribute_hooks] mkAntiquotSplice

@[combinator_parser_sampler withAntiquotSuffixSplice, expose]
def withAntiquotSuffixSplice.parser_sampler (kind : SyntaxNodeKind) (p suffix : ParserSampler) : ParserSampler := fun ctx =>
  let left := p ctx
  if !ctx.includeAntiquots then left else
  if let some x := left.find? (fun x => !x.isEmpty && x.back!.isAntiquots) then
    let right := suffix ctx
    left ++ right.map (fun arr => #[Syntax.node SourceInfo.none (kind ++ `antiquot_suffix_splice) (x ++ arr)])
  else
    left

attribute [run_parser_attribute_hooks] withAntiquotSpliceAndSuffix nodeWithAntiquot sepByElemParser sepBy sepBy1

@[combinator_parser_sampler fieldIdx, expose]
def fieldIdx.parser_sampler : ParserSampler :=
  withAntiquot.parser_sampler (mkAntiquot.parser_sampler "fieldIdx" `fieldIdx) fun _ctx =>
    #[#[Syntax.mkLit fieldIdxKind "14"]]

@[combinator_parser_sampler skip, expose]
def skip.parser_sampler : ParserSampler := fun _ => #[#[]]

set_option hygiene false in
@[combinator_parser_sampler categoryParser, expose]
def categoryParser.parser_sampler (cat : Name) : ParserSampler :=
  withAntiquot.parser_sampler (mkAntiquot.parser_sampler cat.toString cat (isPseudoKind := true)) <|
    match cat with
    | `term => fun _ => #[#[Syntax.mkLit numLitKind "12"]]
    | `command => fun _ => #[#[Unhygienic.run `(#exit)]]
    | `tactic => fun _ => #[#[Unhygienic.run `(tactic| skip)]]
    | `attr => fun _ => #[#[Unhygienic.run `(attr| some_attribute)]]
    | `doElem => fun _ => #[#[Unhygienic.run `(doElem| return)]]
    | _ => fun _ => #[#[]]


#print Term.doAssert
#print evalInsideQuot
attribute [run_parser_attribute_hooks] withCache evalInsideQuot withResetCache withOpen withOpenDecl
  Parser.optional many many1 ident identWithPartialTrailingDot rawIdent hygieneInfo numLit
  hexnum scientificLit strLit charLit nameLit group many1Indent manyIndent sepByIndent
  sepBy1Indent notSymbol patternIgnore ppHardSpace ppSpace ppLine ppRealFill ppRealGroup
  ppIndent ppGroup ppDedent ppAllowUngrouped ppDedentIfGrouped ppHardLineUnlessUngrouped

@[combinator_parser_sampler Doc.Parser.ifVerso, expose]
def ifVerso.parser_sampler (_ifVerso ifNotVerso : ParserSampler) : ParserSampler := ifNotVerso

@[combinator_parser_sampler Doc.Parser.ifVersoModuleDocs, expose]
def ifVersoModuleDocs.parser_sampler (_ifVerso ifNotVerso : ParserSampler) : ParserSampler := ifNotVerso

@[combinator_parser_sampler Doc.Parser.withoutVersoSyntax, expose]
def withoutVersoSyntax.parser_sampler (p : ParserSampler) : ParserSampler := p

@[combinator_parser_sampler Command.versoCommentBody, expose]
def versoCommentBody.parser_sampler : ParserSampler := skip.parser_sampler

@[combinator_parser_sampler Command.commentBody, expose]
def commentBody.parser_sampler : ParserSampler := fun _ => #[#[.atom .none "My doc-string -/"]]

#print ppDedent
attribute [run_parser_attribute_hooks] Term.let Term.match Command.declaration Tactic.simp

def testMe (a : String) : Nat :=
  let b : Nat := ;
  3

#print PrettyPrinter.Formatter.interpretParserDescr
def interpretParserDescr (descr : ParserDescr) : ParserSampler :=
  match descr with
  | ParserDescr.const n                             => getConstAlias parserAliasesRef n
  | ParserDescr.unary n d                           => return (← getUnaryAlias parserAliasesRef n) (← visit d)
  | ParserDescr.binary n d₁ d₂                      => return (← getBinaryAlias parserAliasesRef n) (← visit d₁) (← visit d₂)
  | ParserDescr.node k prec d                       => return leadingNode k prec (← visit d)
  | ParserDescr.nodeWithAntiquot n k d              => return withCache k (nodeWithAntiquot n k (← visit d) (anonymous := true))
  | ParserDescr.sepBy p sep psep trail              => return sepBy (← visit p) sep (← visit psep) trail
  | ParserDescr.sepBy1 p sep psep trail             => return sepBy1 (← visit p) sep (← visit psep) trail
  | ParserDescr.trailingNode k prec lhsPrec d       => return trailingNode k prec lhsPrec (← visit d)
  | ParserDescr.symbol tk                           => return symbol tk
  | ParserDescr.nonReservedSymbol tk includeIdent   => return nonReservedSymbol tk includeIdent
  | ParserDescr.unicodeSymbol tk asciiTk preserve   => return unicodeSymbol tk asciiTk preserve
  | ParserDescr.parser constName                    => do
    let (_, p) ← mkParserOfConstantAux constName visit;
    pure p
  | ParserDescr.cat catName prec                    =>
    match getCategory categories catName with
    | some _ => pure $ categoryParser catName prec
    | none   => IO.ofExcept $ throwUnknownParserCategory catName

#print Term.letDecl
#print Term.letEqnsDecl
#print Term.letIdLhs
set_option pp.rawOnError true in
run_meta
  let stxs : Array (Array Syntax) := Tactic.simp.parser_sampler { env := ← getEnv, includeAntiquots := false }
  for stx in stxs do
    Lean.logInfo stx[0]!

def matchSyntax (stx : Syntax) : MacroM Unit :=
  match stx with
  | `($%$(a)$%$(b)$%$(c)_:term) => pure ()
  | _ => pure ()

#print matchSyntax

abbrev myIdent :=
  12
where (12) := 12

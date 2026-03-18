import Lean

open Lean Parser

structure Context where
  env : Environment
  includeAntiquots : Bool

abbrev ParserSampler := Context → Array (Array Syntax)

unsafe def initParserSampleEverything : IO (KeyedDeclsAttribute ParserSampler × ParserCompiler.CombinatorAttribute) := do
  IO.eprintln "initializing..."
  let parserSampleAttribute ← KeyedDeclsAttribute.init {
    builtinName := `builtin_parser_sampler,
    name := `parser_sampler,
    descr := "Register a parser sampler for a parser.",
    valueTypeName := ``ParserSampler,
    evalKey := fun builtin stx => do
      let env ← getEnv
      let stx ← Attribute.Builtin.getIdent stx
      let id := stx.getId
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a parenthesizer for it immediately, so we just check for a declaration in this case
      unless (builtin && (env.find? id).isSome) || Parser.isValidSyntaxNodeKind env id do
        throwError "Invalid `[parenthesizer]` argument: Unknown syntax kind `{id}`"
      if (← getEnv).contains id then
        recordExtraModUseFromDecl (isMeta := false) id
        if (← Elab.getInfoState).enabled then
          Elab.addConstInfo stx id none
      pure id
  } `parserSampleAttribute
  let combinatorParserSampleAttribute ← ParserCompiler.registerCombinatorAttribute
    `combinator_parser_sampler
    "Register a parser sampler for a parser combinator."
    `combinatorParserSampleAttribute
  Lean.ParserCompiler.registerParserCompiler {
    varName := `parser_sampler
    categoryAttr := parserSampleAttribute
    combinatorAttr := combinatorParserSampleAttribute
  }
  IO.eprintln "done!"
  IO.eprintln s!"name: {parserSampleAttribute.ext.ext.name}"
  return (parserSampleAttribute, combinatorParserSampleAttribute)

@[init initParserSampleEverything]
opaque parserSampleEverything : KeyedDeclsAttribute ParserSampler × ParserCompiler.CombinatorAttribute

def parserSampleAttribute := parserSampleEverything.1
def combinatorParserSampleAttribute := parserSampleEverything.2

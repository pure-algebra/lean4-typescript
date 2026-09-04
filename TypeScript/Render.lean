import TypeScript.Syntax

/-!
# TypeScript.Render

Deterministic fixed-layout rendering for the retained TypeScript target
fragment. Layout is selected by syntax and `Style`, never by a width heuristic,
so equal syntax and style always produce equal bytes.
-/

namespace TypeScript

/-- Declared rendering choices. The fixed-layout renderer consults only these
values and the target syntax tree. -/
structure Style where
  indent : Nat := 2
  quote : Char := '"'
  deriving DecidableEq, Repr

/-- The initial house style, retained from Foldlab's printer. -/
def house0 : Style := {}

namespace Render

def indentOf (style : Style) (depth : Nat) : String :=
  String.ofList (List.replicate (style.indent * depth) ' ')

/-- Escape the delimiter, backslash, and source-line control characters.
Other Unicode characters remain UTF-8 source text. -/
def escapeString (style : Style) (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++
      (if c == style.quote then "\\" ++ String.singleton c
       else if c == '\\' then "\\\\"
       else if c == '\n' then "\\n"
       else if c == '\r' then "\\r"
       else if c == '\t' then "\\t"
       else String.singleton c)

def quoted (style : Style) (s : String) : String :=
  String.singleton style.quote ++ escapeString style s ++
    String.singleton style.quote

/-- One byte of a 64-bit word, counted from the least-significant end. -/
private def byteAt (bits : UInt64) (index : Nat) : Nat :=
  bits.toNat / (256 ^ index) % 256

/-- Reconstruct a JavaScript number from its exact binary64 bytes. `DataView`
fixes big-endian byte order explicitly, so generated values do not depend on
the host's typed-array endianness. -/
def float64Bits (bits : UInt64) : String :=
  let bytes := (List.range 8).reverse.map fun index => toString (byteAt bits index)
  "new DataView(Uint8Array.of(" ++ String.intercalate ", " bytes ++
    ").buffer).getFloat64(0, false)"

private def containsNewline (value : String) : Bool :=
  value.toUTF8.toList.contains 10

mutual

/-- Fixed-layout rendering. Ordinary objects and arrays stay inline exactly
when every rendered member is newline-free. Explicit multiline objects always
render one field per line. -/
def expr (style : Style) (depth : Nat) : Expr → String
  | .ident name => name
  | .str value => quoted style value
  | .int value => toString value
  | .float64Bits bits => float64Bits bits
  | .bool value => if value then "true" else "false"
  | .jsNull => "null"
  | .call fn args => expr style depth fn ++ "(" ++
      String.intercalate ", " (exprs style depth args) ++ ")"
  | .object fields =>
    if fields.isEmpty then "{}"
    else
      let rendered := objectFields style (depth + 1) fields
      if rendered.all (fun field => !containsNewline field.2) then
        "{ " ++
          String.intercalate ", "
            (rendered.map fun (name, value) => name ++ ": " ++ value) ++
          " }"
      else
        "{\n" ++
          String.intercalate "\n"
            (rendered.map fun (name, value) =>
              indentOf style (depth + 1) ++ name ++ ": " ++ value ++ ",") ++
          "\n" ++ indentOf style depth ++ "}"
  | .objectML fields =>
    if fields.isEmpty then "{}"
    else
      "{\n" ++
        String.intercalate "\n"
          ((objectFields style (depth + 1) fields).map fun (name, value) =>
            indentOf style (depth + 1) ++ name ++ ": " ++ value ++ ",") ++
        "\n" ++ indentOf style depth ++ "}"
  | .objectQuoted fields =>
    if fields.isEmpty then "{}"
    else
      let rendered := objectFields style (depth + 1) fields
      if rendered.all (fun field => !containsNewline field.2) then
        "{ " ++
          String.intercalate ", "
            (rendered.map fun (name, value) => quoted style name ++ ": " ++ value) ++
          " }"
      else
        "{\n" ++
          String.intercalate "\n"
            (rendered.map fun (name, value) =>
              indentOf style (depth + 1) ++ quoted style name ++ ": " ++ value ++ ",") ++
          "\n" ++ indentOf style depth ++ "}"
  | .objectQuotedML fields =>
    if fields.isEmpty then "{}"
    else
      "{\n" ++
        String.intercalate "\n"
          ((objectFields style (depth + 1) fields).map fun (name, value) =>
            indentOf style (depth + 1) ++ quoted style name ++ ": " ++ value ++ ",") ++
        "\n" ++ indentOf style depth ++ "}"
  | .objectFromEntries fields =>
      "Object.fromEntries([" ++
        String.intercalate ", "
          ((objectFields style depth fields).map fun (name, value) =>
            "[" ++ quoted style name ++ ", " ++ value ++ "]") ++ "])"
  | .arr items =>
    if items.isEmpty then "[]"
    else
      let rendered := exprs style (depth + 1) items
      if rendered.all (fun item => !containsNewline item) then
        "[" ++ String.intercalate ", " rendered ++ "]"
      else
        "[\n" ++
          String.intercalate "\n"
            (rendered.map fun item =>
              indentOf style (depth + 1) ++ item ++ ",") ++
          "\n" ++ indentOf style depth ++ "]"
  | .arrow returnType body =>
    "()" ++ (match returnType with | none => "" | some type => ": " ++ type) ++
      " => " ++ expr style depth body
  | .generic fn typeArgs =>
    expr style depth fn ++ "<" ++ String.intercalate ", " typeArgs ++ ">"
  | .lambda params body =>
    "(" ++ String.intercalate ", " params ++ ") => " ++ expr style depth body
  | .method target name args =>
    expr style depth target ++ "." ++ name ++ "(" ++
      String.intercalate ", " (exprs style depth args) ++ ")"
  | .member target name =>
    expr style depth target ++ "." ++ name
  | .generator body =>
    "function* () {\n" ++ stmts style (depth + 1) body ++ indentOf style depth ++ "}"
  | .cond test thenBranch elseBranch =>
    expr style depth test ++ " ? " ++ expr style depth thenBranch ++ " : " ++
      expr style depth elseBranch
  | .arrowBlock params body =>
    "(" ++ String.intercalate ", " params ++ ") => {\n" ++
      stmts style (depth + 1) body ++ indentOf style depth ++ "}"

def exprs (style : Style) (depth : Nat) : List Expr → List String
  | [] => []
  | item :: rest => expr style depth item :: exprs style depth rest

def objectFields (style : Style) (depth : Nat) :
    List (String × Expr) → List (String × String)
  | [] => []
  | (name, value) :: rest =>
    (name, expr style depth value) :: objectFields style depth rest

/-- Statements render one per line at their depth; block bodies indent one
level. Every layout choice is a function of the syntax and the style. -/
def stmt (style : Style) (depth : Nat) : Stmt → String
  | .constYield name value =>
    indentOf style depth ++ "const " ++ name ++ " = yield* " ++
      expr style depth value
  | .ret value =>
    indentOf style depth ++ "return " ++ expr style depth value
  | .yieldDiscard value =>
    indentOf style depth ++ "yield* " ++ expr style depth value
  | .letDefinite name type =>
    indentOf style depth ++ "let " ++ name ++ "!: " ++ type
  | .letInit name value =>
    indentOf style depth ++ "let " ++ name ++ " = " ++ expr style depth value
  | .assign name value =>
    indentOf style depth ++ name ++ " = " ++ expr style depth value
  | .whileTrue label body =>
    indentOf style depth ++ (match label with | some l => l ++ ": " | none => "") ++
      "while (true) {\n" ++ stmts style (depth + 1) body ++ indentOf style depth ++ "}"
  | .switch scrutinee cases =>
    indentOf style depth ++ "switch (" ++ expr style depth scrutinee ++ ") {\n" ++
      switchCases style (depth + 1) cases ++ indentOf style depth ++ "}"
  | .ifElse condition thenBranch elseBranch =>
    indentOf style depth ++ "if (" ++ expr style depth condition ++ ") {\n" ++
      stmts style (depth + 1) thenBranch ++ indentOf style depth ++ "}" ++
      (if elseBranch.isEmpty then ""
       else " else {\n" ++ stmts style (depth + 1) elseBranch ++ indentOf style depth ++ "}")
  | .labelled label body =>
    indentOf style depth ++ label ++ ": {\n" ++ stmts style (depth + 1) body ++
      indentOf style depth ++ "}"
  | .scopedGen name body onExit =>
    indentOf style depth ++ "const " ++ name ++
      " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" ++
      stmts style (depth + 1) body ++ indentOf style depth ++ "}), " ++
      expr style depth onExit ++ "))"
  | .scopedGenMasked name body onExit =>
    indentOf style depth ++ "const " ++ name ++
      " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" ++
      stmts style (depth + 1) body ++ indentOf style depth ++ "}), " ++
      expr style depth onExit ++ ")))"
  | .breakTo label =>
    indentOf style depth ++ "break" ++ (match label with | some l => " " ++ l | none => "")
  | .continueTo label =>
    indentOf style depth ++ "continue" ++ (match label with | some l => " " ++ l | none => "")
  | .exprStmt value =>
    indentOf style depth ++ expr style depth value

/-- A statement list, each on its own line. -/
def stmts (style : Style) (depth : Nat) : List Stmt → String
  | [] => ""
  | first :: rest => stmt style depth first ++ "\n" ++ stmts style depth rest

/-- `case n: { body }` per case. -/
def switchCases (style : Style) (depth : Nat) : List (Nat × List Stmt) → String
  | [] => ""
  | (index, body) :: rest =>
    indentOf style depth ++ "case " ++ toString index ++ ": {\n" ++
      stmts style (depth + 1) body ++ indentOf style depth ++ "}\n" ++
      switchCases style depth rest

end

def docBlock (lines : List String) : String :=
  match lines with
  | [] => ""
  | [one] => "/** " ++ one ++ " */\n"
  | first :: rest =>
    "/** " ++ first ++ "\n" ++
      String.intercalate "\n" (rest.map (" * " ++ ·)) ++ " */\n"

def constDecl (style : Style) (declaration : ConstDecl) : String :=
  docBlock declaration.doc ++ "export const " ++ declaration.name ++
    (match declaration.type with | none => "" | some type => ": " ++ type) ++ " = " ++
    expr style 0 declaration.value ++ "\n"

def classDecl (style : Style) (declaration : ClassDecl) : String :=
  docBlock declaration.doc ++ "export class " ++ declaration.name ++
    (match declaration.heritage with
     | none => ""
     | some heritage => " extends " ++ expr style 0 heritage) ++
    (if declaration.members.isEmpty then " {}\n"
     else " {\n" ++
       String.intercalate "\n" (declaration.members.map (indentOf style 1 ++ ·)) ++
       "\n}\n")

def progDecl (style : Style) (declaration : ProgDecl) : String :=
  docBlock declaration.doc ++ "export const " ++ declaration.name ++ " = (" ++
    declaration.paramName ++ ": " ++ declaration.paramType ++ ") =>\n" ++
    indentOf style 1 ++ "Effect.gen(function* () {\n" ++
    String.intercalate "\n" (declaration.stmts.map (stmt style 2)) ++ "\n" ++
    indentOf style 1 ++ "})\n"

/-- Render the checked Effect v4 field combinators. Read and write retain
their own service and error rows; `modify` composes them in effect order. -/
def effectfulFieldDecl (style : Style) (declaration : EffectfulFieldDecl) : String :=
  let field := declaration.fieldName
  let source := declaration.sourceType
  let focus := declaration.fieldType
  let readService := declaration.readService
  let readError := declaration.readError
  let writeService := declaration.writeService
  let writeError := declaration.writeError
  "const " ++ field ++ "Lens = Optic.id<" ++ source ++ ">().key(" ++
    quoted style field ++ ")\n\n" ++
  "export const " ++ field ++ " = {\n" ++
  indentOf style 1 ++ "get: (source: " ++ source ++ "): Effect.Effect<" ++
    focus ++ ", " ++ readError ++ ", " ++ readService ++ "> =>\n" ++
  indentOf style 2 ++ "Effect.gen(function*() {\n" ++
  indentOf style 3 ++ "const service = yield* " ++ readService ++ "\n" ++
  indentOf style 3 ++ "return yield* service." ++ declaration.readMethod ++
    "(source)\n" ++
  indentOf style 2 ++ "}),\n\n" ++
  indentOf style 1 ++ "replace: (value: " ++ focus ++ ", source: " ++ source ++
    "): Effect.Effect<" ++ source ++ ", " ++ writeError ++ ", " ++
    writeService ++ "> =>\n" ++
  indentOf style 2 ++ "Effect.gen(function*() {\n" ++
  indentOf style 3 ++ "const service = yield* " ++ writeService ++ "\n" ++
  indentOf style 3 ++ "yield* service." ++ declaration.writeMethod ++
    "(source, value)\n" ++
  indentOf style 3 ++ "return " ++ field ++ "Lens.replace(value, source)\n" ++
  indentOf style 2 ++ "}),\n\n" ++
  indentOf style 1 ++ "modify: (f: (value: " ++ focus ++ ") => " ++ focus ++
    ", source: " ++ source ++ "): Effect.Effect<\n" ++
  indentOf style 2 ++ source ++ ",\n" ++
  indentOf style 2 ++ readError ++ " | " ++ writeError ++ ",\n" ++
  indentOf style 2 ++ readService ++ " | " ++ writeService ++ "\n" ++
  indentOf style 1 ++ "> => Effect.flatMap(" ++ field ++
    ".get(source), (value) => " ++ field ++ ".replace(f(value), source))\n" ++
  "} as const\n\n" ++
  "export type " ++ field ++ "GetSuccess = Effect.Success<ReturnType<typeof " ++
    field ++ ".get>>\n" ++
  "export type " ++ field ++ "GetError = Effect.Error<ReturnType<typeof " ++
    field ++ ".get>>\n" ++
  "export type " ++ field ++ "GetServices = Effect.Services<ReturnType<typeof " ++
    field ++ ".get>>\n" ++
  "export type " ++ field ++
    "ReplaceSuccess = Effect.Success<ReturnType<typeof " ++ field ++
    ".replace>>\n" ++
  "export type " ++ field ++
    "ReplaceError = Effect.Error<ReturnType<typeof " ++ field ++ ".replace>>\n" ++
  "export type " ++ field ++
    "ReplaceServices = Effect.Services<ReturnType<typeof " ++ field ++
    ".replace>>\n" ++
  "export type " ++ field ++
    "ModifyError = Effect.Error<ReturnType<typeof " ++ field ++ ".modify>>\n" ++
  "export type " ++ field ++
    "ModifyServices = Effect.Services<ReturnType<typeof " ++ field ++ ".modify>>\n"

def decl (style : Style) : Decl → String
  | .const declaration => constDecl style declaration
  | .prog declaration => progDecl style declaration
  | .effectfulField declaration => effectfulFieldDecl style declaration
  | .classDecl declaration => classDecl style declaration
  | .raw text => text ++ "\n"

def import_ (style : Style) : Import → String
  | .all name path =>
    "import * as " ++ name ++ " from " ++ quoted style path ++ "\n"
  | .named names path =>
    "import { " ++ String.intercalate ", " names ++ " } from " ++
      quoted style path ++ "\n"
  | .types names path =>
    "import type { " ++ String.intercalate ", " names ++ " } from " ++
      quoted style path ++ "\n"

/-- Render a complete module with a header block, imports, and one blank line
between declarations. An empty header line renders without trailing space. -/
def module (style : Style) (target : Module) : String :=
  "/**\n" ++ String.intercalate "\n"
      (target.header.map fun line => if line.isEmpty then " *" else " * " ++ line) ++
    "\n */\n" ++
    String.join (target.imports.map (import_ style)) ++ "\n" ++
    String.intercalate "\n" (target.decls.map (decl style))

end Render

end TypeScript

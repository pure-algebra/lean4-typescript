import TypeScript

/-! Structural types and source distinctions required by checked program ingestion.
These are carrier/formatting controls, not a TypeScript typing or execution theorem.
Rendering stays inside guards; structural proofs must not depend on rendering. -/

namespace TypeScriptTest.TypeRef
open TypeScript

def number : TypeRef := .name ["number"] []
def never : TypeRef := .name ["never"] []
def string : TypeRef := .name ["string"] []
def effect : TypeRef := .name ["Effect", "Effect"] [number, never, never]

#guard Render.type house0 effect = "Effect.Effect<number, never, never>"
#guard Render.type house0 (.tuple [number, string] true) = "readonly [number, string]"
#guard Render.type house0 (.tuple [number, string] false) = "[number, string]"
#guard Render.type house0 (.union []) = "never"
#guard Render.type house0 (.literal "a\"b\\c\nλ") = "\"a\\\"b\\\\c\\nλ\""
#guard Render.type house0 (.union [.function [("x", number)] string, number]) =
  "((x: number) => string) | number"
#guard Render.type house0 (.name ["ReadonlyArray"]
    [.union [.tuple [number, string] true, .literal "none"]]) =
  "ReadonlyArray<readonly [number, string] | \"none\">"
#guard Render.type house0 (.object [("get", true, .function [] effect)]) =
  "{ readonly get: () => Effect.Effect<number, never, never> }"
#guard Render.type house0 (.object [("not a name", false, string)]) =
  "{ \"not a name\": string }"
#guard Render.expr house0 0
    (.lambda [{ name := "x", type := some number }] (.ident "x") (some number)) =
  "(x: number): number => x"
#guard Render.stmt house0 0 (.letInit "x" (.int 1) (some number)) = "let x: number = 1"
#guard Render.stmt house0 0 (.constYield "x" (.ident "p") (some number)) =
  "const x: number = yield* p"

-- No annotation, an explicit annotation, and a changed annotation remain distinct.
#guard (Expr.lambda ["x"] (.ident "x") ==
  Expr.lambda [{ name := "x", type := some number }] (.ident "x")) = false
#guard (Expr.lambda [{ name := "x", type := some number }] (.ident "x") ==
  Expr.lambda [{ name := "x", type := some string }] (.ident "x")) = false
#guard (Expr.lambda ["x"] (.ident "x") (some number) ==
  Expr.lambda ["x"] (.ident "x") (some string)) = false
#guard (Expr.arrowBlock ["x"] [] (some number) ==
  Expr.arrowBlock ["x"] [] (some string)) = false
#guard (Stmt.constYield "x" (.ident "p") (some number) ==
  Stmt.constYield "x" (.ident "p") (some string)) = false
#guard (Stmt.letInit "x" (.int 1) (some number) ==
  Stmt.letInit "x" (.int 1) none) = false
#guard (Stmt.letDefinite "x" number == Stmt.letDefinite "x" string) = false

-- Qualified names, generic arguments, and literals are syntax, not raw snippets.
#guard ((.name ["Ref", "Ref"] [number] : TypeRef) ==
  .name ["Ref.Ref<number>"] []) = false
#guard ((.name ["Ref", "Ref"] [number] : TypeRef) ==
  .name ["Ref", "Ref"] [string]) = false
#guard ((.literal "number" : TypeRef) == number) = false
#guard ((.tuple [number] true : TypeRef) == .tuple [number] false) = false
#guard ((.object [("get", true, number)] : TypeRef) ==
  .object [("get", false, number)]) = false
#guard ((.function [("x", number)] string : TypeRef) ==
  .function [("x", string)] string) = false

def declaration : ConstDecl :=
  { doc := [], name := "main", value := .int 1, type := some number }
#guard (declaration == { declaration with exported := false }) = false
#guard (declaration == { declaration with type := some string }) = false
#guard Render.constDecl house0 { declaration with exported := false } =
  "const main: number = 1\n"

-- Type-only imports and aliases survive independently of their package spelling.
#guard (Import.all "Effect" "effect" false == Import.all "Effect" "effect" true) = false
#guard (Import.named [{ imported := "Effect", localName := "E" }] "effect" false ==
  Import.named [{ imported := "Effect", localName := "Effect" }] "effect" false) = false
#guard (Import.named [{ imported := "Effect", localName := "E", typeOnly := true }] "effect" false ==
  Import.named [{ imported := "Effect", localName := "E", typeOnly := false }] "effect" false) = false

#print axioms TypeScript.TypeRef.beq_iff
#print axioms TypeScript.TypeRef.instDecidableEq
#print axioms TypeScript.instBEqExpr.beq
#print axioms TypeScript.instBEqStmt.beq
#print axioms TypeScript.instBEqImport
#print axioms TypeScript.instBEqModule

end TypeScriptTest.TypeRef

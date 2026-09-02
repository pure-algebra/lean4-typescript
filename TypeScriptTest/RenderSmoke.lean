import TypeScript

/-! Executable smoke: byte-exact rendering of the retained fragment. -/

namespace TypeScriptTest
open TypeScript

example : Render.expr house0 0 (.call (.ident "Effect.succeed") [.int 1, .str "a\"b"]) =
    "Effect.succeed(1, \"a\\\"b\")" := by native_decide

example : Render.stmt house0 2 (.constYield "x" (.call (.ident "cell.get") [])) =
    "    const x = yield* cell.get()" := by native_decide

example : targetIdentifier "delete" = false := by native_decide
example : qualifiedIdentifier "Context.Service" = true := by native_decide

end TypeScriptTest

namespace TypeScriptTest
open TypeScript

example : Render.decl house0 (.classDecl
    { doc := [], name := "Cell",
      heritage := some (.call (.call (.generic (.ident "Context.Service") ["Cell", "{ readonly get: () => Effect.Effect<number> }"]) []) [.str "Cell"]) }) =
    "export class Cell extends Context.Service<Cell, { readonly get: () => Effect.Effect<number> }>()(\"Cell\") {}\n" := by
  native_decide

end TypeScriptTest

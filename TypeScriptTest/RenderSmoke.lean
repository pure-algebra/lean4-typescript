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

namespace TypeScriptTest
open TypeScript

/-- The dispatch-loop shape a block graph lowers to. -/
example : Render.stmt house0 1 (.whileTrue none
    [ .switch (.ident "block")
        [ (0, [ .assign "x" (.call (.ident "f") []), .assign "block" (.int 1), .continueTo none ])
        , (1, [ .ifElse (.ident "ok") [ .ret (.ident "x") ] [ .breakTo (some "L") ] ]) ] ]) =
    "  while (true) {\n    switch (block) {\n      case 0: {\n        x = f()\n        block = 1\n        continue\n      }\n      case 1: {\n        if (ok) {\n          return x\n        } else {\n          break L\n        }\n      }\n    }\n  }" := by
  native_decide

example : Render.stmt house0 0 (.letDefinite "b1p0" "number") = "let b1p0!: number" := by native_decide

end TypeScriptTest

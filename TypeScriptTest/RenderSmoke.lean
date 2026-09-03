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

/-- v0.3.0: a named-parameter arrow and a method call. -/
example : Render.expr house0 0 (.lambda ["a", "exit"]
    (.method (.call (.ident "regions.finalizer") [.int 7, .ident "exit"]) "pipe"
      [.call (.ident "Effect.andThen") [.call (.ident "cell.release") [.ident "a"]]])) =
  "(a, exit) => regions.finalizer(7, exit).pipe(Effect.andThen(cell.release(a)))" := by native_decide

/-- v0.3.0: a scoped nested generator whose exit is observed. -/
example : Render.stmt house0 1 (.scopedGen "r7" [.ret (.ident "b2p1")]
    (.lambda ["exit"] (.call (.ident "regions.leave") [.int 7, .ident "exit"]))) =
  "  const r7 = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" ++
  "    return b2p1\n" ++
  "  }), (exit) => regions.leave(7, exit)))" := by native_decide

example : Render.stmt house0 1 (.scopedGenMasked "r7" [.ret (.ident "b2p1")]
    (.lambda ["exit"] (.call (.ident "regions.leave") [.int 7, .ident "exit"]))) =
  "  const r7 = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" ++
  "    return b2p1\n" ++
  "  }), (exit) => regions.leave(7, exit))))" := by native_decide

example : (Stmt.scopedGen "r" [] (.ident "f") == Stmt.scopedGen "r" [] (.ident "f")) = true := by native_decide
example : (Stmt.scopedGenMasked "r" [] (.ident "f") == Stmt.scopedGen "r" [] (.ident "f")) = false := by native_decide
example : (Expr.method (.ident "a") "b" [] == Expr.method (.ident "a") "c" []) = false := by native_decide

end TypeScriptTest

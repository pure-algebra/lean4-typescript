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

/-- v0.4.3: a member of an expression. A generator that binds a `Result` reads
its two edges this way, so the base stays a name the identifier profile can
check and the dot is syntax. -/
example : Render.expr house0 0 (.member (.ident "a4") "success") = "a4.success" := by native_decide

example : Render.expr house0 0 (.member (.ident "a4") "failure") = "a4.failure" := by native_decide

/-- It nests, and it composes with the call and method forms. -/
example : Render.expr house0 0 (.member (.member (.ident "a") "b") "c") = "a.b.c" := by native_decide

example : Render.expr house0 0
    (.call (.ident "Result.isSuccess") [.member (.ident "a4") "success"]) =
  "Result.isSuccess(a4.success)" := by native_decide

example : Render.expr house0 0 (.member (.call (.ident "f") [.int 1]) "value") =
  "f(1).value" := by native_decide

example : Render.stmt house0 0 (.assign "b1p0" (.member (.ident "a4") "success")) =
  "b1p0 = a4.success" := by native_decide

/-- A member is not the method call of the same name, and the field is part of
the identity. -/
example : (Expr.member (.ident "a") "b" == Expr.member (.ident "a") "b") = true := by native_decide
example : (Expr.member (.ident "a") "b" == Expr.member (.ident "a") "c") = false := by native_decide
example : (Expr.member (.ident "a") "b" == Expr.member (.ident "z") "b") = false := by native_decide
example : (Expr.member (.ident "a") "b" == Expr.method (.ident "a") "b" []) = false := by native_decide
example : (Expr.member (.ident "a") "b" == Expr.ident "a.b") = false := by native_decide

end TypeScriptTest

namespace TypeScriptTest
open TypeScript

/-- v0.5.0: a generator expression is what `Effect.gen` takes; its body is the
statement fragment, one statement per line, closed at the caller's depth. -/
example : Render.expr house0 0 (.call (.ident "Effect.gen")
    [.generator [.constYield "a0" (.call (.ident "Ref.get") [.ident "a0"]), .ret (.ident "a0")]]) =
    "Effect.gen(function* () {\n  const a0 = yield* Ref.get(a0)\n  return a0\n})" := by
  native_decide

example : Render.expr house0 0 (.call (.ident "Effect.gen") [.generator []]) =
    "Effect.gen(function* () {\n})" := by native_decide

/-- v0.5.0: a conditional expression. -/
example : Render.expr house0 0 (.cond (.bool true) (.int 1) (.ident "undefined")) =
    "true ? 1 : undefined" := by native_decide

/-- v0.5.0: an arrow with a block body, nested inside an object so the object
goes multiline and every depth is exercised. -/
example : Render.expr house0 0 (.call (.ident "Effect.suspend")
    [ .arrowBlock []
        [ .letInit "a0" (.int 0)
        , .ret (.call (.ident "Effect.whileLoop")
            [ .object
                [ ("while", .arrow none (.ident "a0"))
                , ("step", .arrowBlock ["a1"] [.assign "a0" (.call (.ident "succ") [.ident "a1"])]) ] ]) ] ]) =
    "Effect.suspend(() => {\n  let a0 = 0\n  return Effect.whileLoop({\n    while: () => a0,\n    step: (a1) => {\n      a0 = succ(a1)\n    },\n  })\n})" := by
  native_decide

/-- Equality reaches the new formers. -/
example : (Expr.generator [.ret (.int 1)] == Expr.generator [.ret (.int 1)]) = true := by native_decide
example : (Expr.generator [.ret (.int 1)] == Expr.generator [.ret (.int 2)]) = false := by native_decide
example : (Expr.arrowBlock ["a"] [] == Expr.arrowBlock ["b"] []) = false := by native_decide

end TypeScriptTest

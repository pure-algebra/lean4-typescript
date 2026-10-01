import TypeScript

/-! v0.7.0: the object forms a record-carrying consumer prints. Optional fields on
object types, element access with an expression key, `new`, object literals with
spread entries and computed keys, and a class whose heritage carries type
arguments. Each form has its exact rendered text and its equality twins. These are
carrier and formatting controls, not a TypeScript typing or execution theorem;
rendering stays inside guards, and structural equality never depends on it. -/

namespace TypeScriptTest.ObjectForms
open TypeScript

def number : TypeRef := .name ["number"] []
def string : TypeRef := .name ["string"] []
def undefined : TypeRef := .name ["undefined"] []

/-! ## Optional fields on object types

`optional` is the `?` after the name and nothing else: `{ readonly a?: number }`
is rc.112's `optionalKey`. A field whose type also admits `undefined` (rc.112's
`optional`) is the consumer's union, `{ readonly a?: number | undefined }`, and
those two types are not mutually assignable under `exactOptionalPropertyTypes`. -/

#guard Render.type house0
    (.object [{ name := "a", readonly := true, optional := true, type := number }]) =
  "{ readonly a?: number }"
#guard Render.type house0
    (.object [{ name := "a", readonly := false, optional := true, type := number }]) =
  "{ a?: number }"
#guard Render.type house0
    (.object [{ name := "a", readonly := true, optional := true, type := .union [number, undefined] }]) =
  "{ readonly a?: number | undefined }"
-- A name outside the identifier profile is quoted before the `?`.
#guard Render.type house0
    (.object [{ name := "content-type", readonly := true, optional := true, type := string }]) =
  "{ readonly \"content-type\"?: string }"
-- Required and optional fields keep declaration order.
#guard Render.type house0
    (.object [{ name := "id", readonly := true, type := number },
      { name := "note", readonly := true, optional := true, type := string }]) =
  "{ readonly id: number; readonly note?: string }"

-- A field built without `optional` is required, as every field was before v0.7.0.
#guard ({ name := "a", readonly := true, type := number } : TypeRef.Field).optional == false

-- Red twin in the bytes: a renderer that dropped the flag would equate these.
#guard Render.type house0
    (.object [{ name := "a", readonly := true, optional := true, type := number }]) !=
  Render.type house0 (.object [{ name := "a", readonly := true, type := number }])

-- Red twins: the flag is part of a field's identity, and the flag is not the union.
#guard ((.object [{ name := "a", readonly := true, optional := true, type := number }] : TypeRef) ==
  .object [{ name := "a", readonly := true, type := number }]) = false
#guard ((.object [{ name := "a", readonly := true, optional := true, type := number }] : TypeRef) ==
  .object [{ name := "a", readonly := true, type := .union [number, undefined] }]) = false
#guard ((.object [{ name := "a", readonly := true, optional := true, type := number }] : TypeRef) ==
  .object [{ name := "a", readonly := true, optional := true, type := .union [number, undefined] }]) = false
#guard ((.object [{ name := "a", readonly := true, optional := true, type := number }] : TypeRef) ==
  .object [{ name := "a", readonly := true, optional := true, type := number }]) = true
#guard decide ((.object [{ name := "a", readonly := true, optional := true, type := number }] : TypeRef) =
  .object [{ name := "a", readonly := true, type := number }]) = false

/-! ## Element access with an expression key

A property name outside the identifier profile is read with brackets, `t["a-b"]`; a
tuple position is read at a number, `t[2]`; a map is read at a run-time key, `m[k]`.
The key is an expression, so a string key is data rendered by the one string owner. -/

#guard Render.expr house0 0 (.index (.ident "t") (.str "a-b")) = "t[\"a-b\"]"
#guard Render.expr house0 0 (.index (.ident "t") (.int 2)) = "t[2]"
#guard Render.expr house0 0 (.index (.ident "m") (.ident "k")) = "m[k]"
#guard Render.expr house0 0 (.index (.ident "a0") (.str "a\"b")) = "a0[\"a\\\"b\"]"
#guard Render.expr house0 0 (.index (.ident "a0") (.str "__proto__")) = "a0[\"__proto__\"]"
-- It composes with member access, calls and itself.
#guard Render.expr house0 0 (.member (.index (.ident "t") (.int 0)) "id") = "t[0].id"
#guard Render.expr house0 0 (.index (.index (.ident "t") (.int 0)) (.int 1)) = "t[0][1]"
#guard Render.expr house0 0 (.index (.call (.ident "f") []) (.str "a-b")) = "f()[\"a-b\"]"
#guard Render.expr house0 0 (.call (.ident "pair") [.int 200, .index (.ident "a0") (.str "a-b")]) =
  "pair(200, a0[\"a-b\"])"

-- Red twins: bracket access at a string is not member access at that name, a string key
-- is not a number key or a variable, and target and key are both part of the identity.
#guard (Expr.index (.ident "t") (.str "a") == Expr.member (.ident "t") "a") = false
#guard (Expr.index (.ident "t") (.str "2") == Expr.index (.ident "t") (.int 2)) = false
#guard (Expr.index (.ident "t") (.ident "k") == Expr.index (.ident "t") (.str "k")) = false
#guard (Expr.index (.ident "t") (.str "a") == Expr.index (.ident "u") (.str "a")) = false
#guard (Expr.index (.ident "t") (.str "a") == Expr.index (.ident "t") (.str "a")) = true
#guard Render.expr house0 0 (.index (.ident "t") (.str "a")) !=
  Render.expr house0 0 (.member (.ident "t") "a")

/-! ## `new`

A payload class's value is built with `new`, `new NotFound({ id: 2 })`; the argument
list always renders. -/

#guard Render.expr house0 0 (.new (.ident "NotFound") [.object [("id", .int 2)]]) =
  "new NotFound({ id: 2 })"
#guard Render.expr house0 0 (.new (.ident "Date") []) = "new Date()"
#guard Render.expr house0 0 (.new (.generic (.ident "Box") [number]) [.int 1, .str "a"]) =
  "new Box<number>(1, \"a\")"
#guard Render.expr house0 0 (.new (.member (.ident "Errors") "NotFound") [.object [("id", .int 2)]]) =
  "new Errors.NotFound({ id: 2 })"
#guard Render.stmt house0 1 (.ret (.call (.ident "Effect.fail")
    [.new (.ident "NotFound") [.object [("id", .ident "a0")]]])) =
  "  return Effect.fail(new NotFound({ id: a0 }))"

-- Red twins: `new C()` is not the call `C()`, and callee and arguments are both part of
-- the identity.
#guard (Expr.new (.ident "C") [] == Expr.call (.ident "C") []) = false
#guard (Expr.new (.ident "C") [.int 1] == Expr.new (.ident "C") [.int 2]) = false
#guard (Expr.new (.ident "C") [] == Expr.new (.ident "D") []) = false
#guard (Expr.new (.ident "C") [.int 1] == Expr.new (.ident "C") [.int 1]) = true
#guard Render.expr house0 0 (.new (.ident "C") []) != Render.expr house0 0 (.call (.ident "C") [])

/-! ## Object spread

`objectWith` is an object literal of properties and spreads in written order, its
property names spelled by one `KeyForm` for the whole literal. `{ ...t, b: y }` is the
record update; a later entry overrides an earlier one, so order is meaning. -/

#guard Render.expr house0 0 (.objectWith .plain [.spread (.ident "t"), .property "b" (.ident "y")]) =
  "{ ...t, b: y }"
#guard Render.expr house0 0 (.objectWith .plain [.property "b" (.ident "y"), .spread (.ident "t")]) =
  "{ b: y, ...t }"
#guard Render.expr house0 0 (.objectWith .plain [.spread (.ident "a"), .spread (.ident "b")]) =
  "{ ...a, ...b }"
-- The update at names outside the identifier profile: the quoted form.
#guard Render.expr house0 0 (.objectWith .quoted [.spread (.ident "t"), .property "a-b" (.int 1)]) =
  "{ ...t, \"a-b\": 1 }"
-- The spread operand is any expression.
#guard Render.expr house0 0
    (.objectWith .plain [.spread (.member (.ident "a0") "user"), .property "id" (.int 2)]) =
  "{ ...a0.user, id: 2 }"
#guard Render.expr house0 0 (.objectWith .plain []) = "{}"
-- Multiline exactly when a rendered value has a newline, one entry per line.
#guard Render.expr house0 0 (.objectWith .plain
    [.spread (.ident "t"), .property "step" (.arrowBlock ["a1"] [.ret (.ident "a1")])]) =
  "{\n  ...t,\n  step: (a1) => {\n    return a1\n  },\n}"

-- Without a spread, the plain and quoted forms render as `object` and `objectQuoted` do,
-- inline and multiline: a consumer picks one spelling per shape.
#guard Render.expr house0 0 (.objectWith .plain [.property "a" (.int 1), .property "b" (.str "x")]) =
  Render.expr house0 0 (.object [("a", .int 1), ("b", .str "x")])
#guard Render.expr house0 0 (.objectWith .quoted [.property "a-b" (.int 1), .property "c" (.str "x")]) =
  Render.expr house0 0 (.objectQuoted [("a-b", .int 1), ("c", .str "x")])
#guard Render.expr house0 1 (.objectWith .plain
    [.property "step" (.arrowBlock ["a1"] [.ret (.ident "a1")]), .property "n" (.int 2)]) =
  Render.expr house0 1 (.object [("step", .arrowBlock ["a1"] [.ret (.ident "a1")]), ("n", .int 2)])
#guard Render.expr house0 1 (.objectWith .quoted
    [.property "step" (.arrowBlock ["a1"] [.ret (.ident "a1")]), .property "n" (.int 2)]) =
  Render.expr house0 1 (.objectQuoted [("step", .arrowBlock ["a1"] [.ret (.ident "a1")]), ("n", .int 2)])

-- Red twins: a spread is not a property of the same name, order and key form are part
-- of the identity, and the new former is not the old one.
#guard (Expr.objectWith .plain [.spread (.ident "t")] ==
  Expr.objectWith .plain [.property "t" (.ident "t")]) = false
#guard (Expr.objectWith .plain [.spread (.ident "a"), .spread (.ident "b")] ==
  Expr.objectWith .plain [.spread (.ident "b"), .spread (.ident "a")]) = false
#guard (Expr.objectWith .plain [.property "a" (.int 1)] ==
  Expr.objectWith .quoted [.property "a" (.int 1)]) = false
#guard (Expr.objectWith .plain [.property "a" (.int 1)] == Expr.object [("a", .int 1)]) = false
#guard (Expr.objectWith .plain [.spread (.ident "t"), .property "b" (.ident "y")] ==
  Expr.objectWith .plain [.spread (.ident "t"), .property "b" (.ident "y")]) = true
#guard (ObjectEntry.spread (.ident "t") == ObjectEntry.spread (.ident "u")) = false
#guard Render.expr house0 0 (.objectWith .plain [.spread (.ident "t")]) !=
  Render.expr house0 0 (.objectWith .plain [.property "t" (.ident "t")])
#guard Render.expr house0 0 (.objectWith .plain [.spread (.ident "t"), .property "b" (.ident "y")]) !=
  Render.expr house0 0 (.objectWith .plain [.property "b" (.ident "y"), .spread (.ident "t")])

/-! ## Computed object keys

A plain or quoted `__proto__` key in an object literal sets the prototype and creates
no own property; a computed key `["__proto__"]` defines one. That is the run-time
control behind this form (node v22.23.2, `field-names.cjs` in the type-language
probe's seat R host folder: `plainLiteralOwn` false, `quotedLiteralOwn` false,
`computedOwn` true). The rule is one computed key computes all: the computed form
spells every name `["name"]`, never plain. -/

#guard Render.expr house0 0
    (.objectWith .computed [.property "__proto__" (.ident "v"), .property "a" (.int 1)]) =
  "{ [\"__proto__\"]: v, [\"a\"]: 1 }"
-- Names are data: the one string owner escapes them inside the brackets.
#guard Render.expr house0 0 (.objectWith .computed [.property "a\"b" (.int 1)]) =
  "{ [\"a\\\"b\"]: 1 }"
-- The update at a `__proto__` name: a spread, then the computed key.
#guard Render.expr house0 0
    (.objectWith .computed [.spread (.ident "t"), .property "__proto__" (.str "x")]) =
  "{ ...t, [\"__proto__\"]: \"x\" }"
#guard Render.expr house0 0 (.objectWith .computed
    [.property "__proto__" (.str "x"), .property "step" (.arrowBlock ["a1"] [.ret (.ident "a1")])]) =
  "{\n  [\"__proto__\"]: \"x\",\n  [\"step\"]: (a1) => {\n    return a1\n  },\n}"
-- Every name of a computed literal is computed, whatever its class.
#guard ["__proto__", "a", "a-b", "", "default", "名前"].all fun name =>
  Render.expr house0 0 (.objectWith .computed [.property name (.int 1)]) ==
    "{ [" ++ Render.quoted house0 name ++ "]: 1 }"
-- Quoted keys stay as the package renders them.
#guard Render.expr house0 0 (.objectQuoted [("a-b", .int 1)]) = "{ \"a-b\": 1 }"
#guard Render.expr house0 0 (.objectWith .quoted [.property "a-b" (.int 1)]) = "{ \"a-b\": 1 }"

-- Red twins: the computed spelling is neither the plain nor the quoted one (the two
-- that create no own property), nor `Object.fromEntries` (which does not type at a
-- record type), and the key form is part of the identity.
#guard Render.expr house0 0 (.objectWith .computed [.property "__proto__" (.ident "v")]) !=
  "{ __proto__: v }"
#guard Render.expr house0 0 (.objectWith .computed [.property "__proto__" (.ident "v")]) !=
  Render.expr house0 0 (.objectWith .plain [.property "__proto__" (.ident "v")])
#guard Render.expr house0 0 (.objectWith .computed [.property "__proto__" (.ident "v")]) !=
  Render.expr house0 0 (.objectWith .quoted [.property "__proto__" (.ident "v")])
#guard (Expr.objectWith .computed [.property "a" (.int 1)] ==
  Expr.objectWith .quoted [.property "a" (.int 1)]) = false
#guard (Expr.objectWith .computed [.property "__proto__" (.int 1)] ==
  Expr.objectFromEntries [("__proto__", .int 1)]) = false
#guard (Expr.objectWith .computed [.property "a" (.int 1)] ==
  Expr.objectWith .computed [.property "a" (.int 1)]) = true

/-! ## The class declaration with type arguments on its heritage

`ClassDecl` already says this: the heritage is `generic` over a call, so the type
argument list follows the call. The payload class and the value `new` builds: -/

def payloadType : TypeRef := .object [{ name := "id", readonly := true, type := number }]

def notFound : ClassDecl :=
  { doc := [], name := "NotFound",
    heritage := some (.generic (.call (.ident "Data.TaggedError") [.str "NotFound"]) [payloadType]) }

#guard Render.decl house0 (.classDecl notFound) =
  "export class NotFound extends Data.TaggedError(\"NotFound\")<{ readonly id: number }> {}\n"

-- With an optional payload field, and in a module beside the value `new` builds.
#guard Render.module house0
    { header := ["Payload classes."],
      imports := [.named ["Data", "Effect"] "effect"],
      decls :=
        [ .classDecl
            { notFound with
              heritage := some (.generic (.call (.ident "Data.TaggedError") [.str "NotFound"])
                [.object [{ name := "id", readonly := true, type := number },
                  { name := "note", readonly := true, optional := true, type := string }]]) },
          .const
            { doc := [], name := "missing",
              value := .call (.ident "Effect.fail") [.new (.ident "NotFound") [.object [("id", .int 2)]]] } ] } =
  "/**\n * Payload classes.\n */\nimport { Data, Effect } from \"effect\"\n\n" ++
  "export class NotFound extends Data.TaggedError(\"NotFound\")<{ readonly id: number; readonly note?: string }> {}\n\n" ++
  "export const missing = Effect.fail(new NotFound({ id: 2 }))\n"

-- Red twins: the type arguments belong after the call, not on the callee, and they are
-- part of the declaration's identity.
#guard Render.decl house0 (.classDecl notFound) !=
  Render.decl house0 (.classDecl { notFound with
    heritage := some (.call (.generic (.ident "Data.TaggedError") [payloadType]) [.str "NotFound"]) })
#guard (Decl.classDecl notFound == .classDecl { notFound with
    heritage := some (.call (.ident "Data.TaggedError") [.str "NotFound"]) }) = false
#guard (Decl.classDecl notFound == .classDecl notFound) = true

/-! ## Axioms

Structural equality stays at the ceiling a consumer's semantic gate holds
(`[propext, Quot.sound]` or less); only rendering traverses `String`. -/

/-- info: 'TypeScript.TypeRef.beq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.TypeRef.beq_iff
/-- info: 'TypeScript.TypeRef.instDecidableEq' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.TypeRef.instDecidableEq
/-- info: 'TypeScript.instBEqExpr.beq' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.instBEqExpr.beq
/-- info: 'TypeScript.instBEqObjectEntry.beq' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.instBEqObjectEntry.beq

end TypeScriptTest.ObjectForms

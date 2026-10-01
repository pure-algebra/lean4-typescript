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

/-! ## Axioms

Structural equality stays at the ceiling a consumer's semantic gate holds
(`[propext, Quot.sound]` or less); only rendering traverses `String`. -/

/-- info: 'TypeScript.TypeRef.beq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.TypeRef.beq_iff
/-- info: 'TypeScript.TypeRef.instDecidableEq' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.TypeRef.instDecidableEq
/-- info: 'TypeScript.instBEqExpr.beq' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.instBEqExpr.beq

end TypeScriptTest.ObjectForms

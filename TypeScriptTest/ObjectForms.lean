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

/-- info: 'TypeScript.TypeRef.beq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.TypeRef.beq_iff
/-- info: 'TypeScript.TypeRef.instDecidableEq' depends on axioms: [propext] -/
#guard_msgs in #print axioms TypeScript.TypeRef.instDecidableEq

end TypeScriptTest.ObjectForms

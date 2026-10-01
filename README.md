# TypeScript

TypeScript as a target language for the pure-algebra Lean family: the
first-order syntax fragment generators may emit, a deterministic fixed-layout
renderer, the generated-identifier profile, and host pins. It has no Lake
dependencies and knows nothing about effects. `lean4-effect4` (Effect v4
idioms) and `lean4-whatwg` (web standards) require it by exact commit.

`TypeScript/Syntax.lean` and `TypeScript/Render.lean` started from lean4-effect4's
`Effect4/Target/TypeScript/{Expr,Render}.lean` at `de3e2ec` with the
namespace renamed. `TypeScript/Identifier.lean` lifts `targetIdentifier` from
its Schema generator. `TypeScript/HostPin.lean` is new.

```bash
lake build
```

MIT.

## Structural program types (0.6.0)

`TypeScript.TypeRef` stores qualified name segments and generic arguments,
string literal types, readonly or mutable tuples, unions, object properties,
and function parameters/results as data. It does not store raw type snippets.
`TypeScript.Render.type` alone formats this data as source text. Structural
equality has a compiled equality-reflection proof independent of the renderer.
Rendering does not promise to preserve redundant syntax: an empty union prints
`never`, and a declaration-level type import does not repeat per-binding `type`
markers. Checked consumers must select a grammatical canonical profile before
claiming an exact source round trip.

Program annotations use this carrier: exported constants, expression/block
arrows, explicit generic arguments, initialized or definite local bindings,
yield bindings, and generator parameters. An absent annotation remains absent.
Imports retain imported and local names, declaration-level and per-binding
`type` modifiers; declarations retain whether they are exported. The package
represents those distinctions without claiming that every representable module
is valid TypeScript. A consumer owns admitted grammar, name resolution, binding
hygiene, annotation checks, and target behavior.

This is a breaking carrier migration. There is no implicit string-to-type
conversion. Convenience coercions on parameter and import-binding **names**
create unannotated parameters and unaliased value imports only. The existing
specialized Schema-field and raw-declaration nodes remain outside the checked
program fragment; this release does not claim structured coverage of arbitrary
TypeScript declarations. Consumers must reject unsupported forms explicitly.

The canonical Effect4 reader must reject new annotation fields that its current
printer does not emit. A source validator may accept a broader admitted profile,
but cannot erase its annotations before checking them. Persisted Effect4 row
`typeArgs` are a separate wire contract; this package does not change them.

## Object forms (0.7.0)

Six forms a consumer needs to print records, their updates and their error payloads.

- An object type's field is a record, `TypeRef.Field` (`FieldOf TypeRef`): `name`,
  `readonly`, `optional` and `type`. `optional` defaults to `false`, so a field built without
  it is required, as before. It renders as `?` and nothing else, `{ readonly a?: number }`; a
  field that also admits `undefined` carries that union in its type,
  `{ readonly a?: number | undefined }`.
- `Expr.index target key` renders `target[key]` with an expression key: `t["a-b"]`, `t[2]`,
  `m[k]`. A string key is data, so no identifier rule applies to it.
- `Expr.new callee args` renders `new callee(args)`: `new NotFound({ id: 2 })`.
- `Expr.objectWith keys entries` is an object literal of `ObjectEntry.property` and
  `ObjectEntry.spread` entries in written order, `{ ...t, b: y }`, and one `KeyForm` spells
  every property name of the literal: `plain`, `quoted`, or `computed`,
  `{ ["__proto__"]: v, ["a"]: 1 }`. A plain or quoted `__proto__` key sets the prototype
  and creates no own property; the computed form defines one and never writes a plain key.
  Without a spread, the plain and quoted forms render as `object` and `objectQuoted` do.
- A `ClassDecl` whose heritage is `generic` over a call is a tagged error payload class:
  `export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}`.

This breaks consumers that build or match object-type fields as triples, and every
exhaustive match on `Expr`, which must add arms for `index`, `new` and `objectWith`. The
existing constructors keep their meaning and their bytes. Structural equality covers the new forms
and stays at `[propext]`. `TypeScriptTest/ObjectForms.lean` holds the exact text, the
equality twins and the axiom pins.

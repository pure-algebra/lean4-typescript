# TypeScript

TypeScript as a target language for the pure-algebra Lean family: the
first-order syntax fragment generators may emit, a deterministic fixed-layout
renderer, the generated-identifier profile, and host pins. It has no Lake
dependencies and knows nothing about effects. `lean4-effect4` (Effect v4
idioms) and `lean4-whatwg` (web standards) require it by exact commit.

`TypeScript/Syntax.lean` and `TypeScript/Render.lean` are lean4-effect4's
`Effect4/Target/TypeScript/{Expr,Render}.lean` at `de3e2ec` with the
namespace renamed. `TypeScript/Identifier.lean` lifts `targetIdentifier` from
its Schema generator. `TypeScript/HostPin.lean` is new.

```bash
lake build
```

MIT.

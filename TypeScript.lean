import TypeScript.Syntax
import TypeScript.Render
import TypeScript.Identifier
import TypeScript.HostPin

/-!
# TypeScript

TypeScript as a target language: the retained first-order syntax fragment,
its deterministic fixed-layout renderer, the generated-identifier profile,
and host pins. This package knows nothing about effects; lean4-effect4 and
lean4-whatwg require it and add their own idioms on top. Syntax and renderer
carry their lean4-effect4 history (`Effect4/Target/TypeScript/{Expr,Render}.lean`
at `de3e2ec`); the only edits are the namespace lines.
-/

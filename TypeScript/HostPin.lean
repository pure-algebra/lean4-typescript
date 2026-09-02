/-!
# TypeScript.HostPin

The exact host a generated module was checked against. Generated modules cite
one of these in their header, so a consumer of a published package knows the
compiler, language service, runtime, and library versions the evidence names.
This is data; the checks themselves run outside Lean.
-/

namespace TypeScript

/-- One pinned host profile. Every field is a spelling the host tool prints. -/
structure HostPin where
  /-- `tsc --version` of the unpatched compiler, e.g. `7.0.2`. -/
  typescript : String
  /-- The language-service checker, e.g. `@effect/tsgo@0.38.0`. -/
  languageService : Option String := none
  /-- The JavaScript runtime and flags, e.g. `node 22 --experimental-strip-types`. -/
  runtime : String
  /-- Library pins the module imports, as `name@version` rows. -/
  libraries : List String := []
deriving DecidableEq, Repr

/-- Header lines a renderer prints for a pin. -/
def HostPin.headerLines (pin : HostPin) : List String :=
  [ "Host: typescript " ++ pin.typescript
  , "Runtime: " ++ pin.runtime ] ++
  (match pin.languageService with
   | some service => ["Language service: " ++ service]
   | none => []) ++
  pin.libraries.map ("Library: " ++ ·)

end TypeScript

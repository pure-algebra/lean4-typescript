/-!
# TypeScript.Identifier

The deliberately narrow generated-binding profile: ECMAScript identifier
characters the compiler accepts and no reserved word. Lifted unchanged from
lean4-effect4 `Effect4/Target/TypeScript/Schema.lean` (`targetIdentifier`).
-/

namespace TypeScript

def reservedIdentifiers : List String :=
  [ "await", "break", "case", "catch", "class", "const", "continue"
  , "debugger", "default", "delete", "do", "else", "enum", "export"
  , "extends", "false", "finally", "for", "function", "if", "import"
  , "in", "instanceof", "let", "new", "null", "return", "super"
  , "switch", "this", "throw", "true", "try", "typeof", "var", "void"
  , "while", "with", "yield", "interface", "implements", "package"
  , "private", "protected", "public", "static" ]

private def asciiBetween (lower upper character : UInt8) : Bool :=
  lower <= character && character <= upper

def identifierStart (character : UInt8) : Bool :=
  asciiBetween 65 90 character || asciiBetween 97 122 character ||
    character == 95 || character == 36

def identifierContinue (character : UInt8) : Bool :=
  identifierStart character || asciiBetween 48 57 character

/-- A legal, non-reserved generated binding name. -/
def targetIdentifier (name : String) : Bool :=
  match name.toUTF8.toList with
  | [] => false
  | first :: rest =>
      identifierStart first && rest.all identifierContinue &&
        !(reservedIdentifiers.contains name)

/-- A qualified spelling `A.B.c` whose every segment is a legal identifier. -/
def qualifiedIdentifier (name : String) : Bool :=
  let parts := name.splitOn "."
  !parts.isEmpty && parts.all fun part => targetIdentifier part

end TypeScript

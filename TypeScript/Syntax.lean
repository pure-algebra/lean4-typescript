/-!
# TypeScript.Syntax

The first-order TypeScript syntax retained from Foldlab's target backend.
This module owns syntax only. Deterministic source rendering lives in
`TypeScript.Render`; typing, lowering, decoding, and simulation
remain separate target layers.

The fragment is intentionally small and grows only for an admitted Effect4
consumer. It is target data, never the denotation or identity of an Effect4
program.
-/

namespace TypeScript

/-- Expressions in the retained target fragment. Names and optional type
annotations are target spellings; later typed lowering is responsible for
constructing them from checked Effect4 content. -/
inductive Expr where
  /-- A possibly qualified target reference, such as `Schema.Struct`. -/
  | ident (name : String)
  | str (value : String)
  | int (value : Int)
  /-- A JavaScript number reconstructed from an exact IEEE-754 binary64 bit
  pattern. This avoids lossy decimal formatting in generated raw data. -/
  | float64Bits (bits : UInt64)
  | bool (value : Bool)
  | jsNull
  | call (fn : Expr) (args : List Expr)
  | object (fields : List (String × Expr))
  /-- An object whose multiline layout is an explicit syntax choice. -/
  | objectML (fields : List (String × Expr))
  /-- An object whose property names are data and are therefore always quoted. -/
  | objectQuoted (fields : List (String × Expr))
  /-- A quoted-key object whose multiline layout is explicit syntax. -/
  | objectQuotedML (fields : List (String × Expr))
  /-- A data-keyed object built from retained entries. Used when JavaScript
  object-literal semantics would reinterpret a key such as `__proto__`. -/
  | objectFromEntries (fields : List (String × Expr))
  | arr (items : List Expr)
  /-- A zero-parameter arrow with an optional declared result type. -/
  | arrow (returnType : Option String) (body : Expr)
  /-- A reference applied to explicit type arguments, `fn<T1, T2>`. Type
  arguments are target type spellings. -/
  | generic (fn : Expr) (typeArgs : List String)
  /-- A named-parameter arrow with an expression body, `(a, exit) => body`. -/
  | lambda (params : List String) (body : Expr)
  /-- A method call on an expression, `target.name(args)`. -/
  | method (target : Expr) (name : String) (args : List Expr)
  deriving Inhabited

-- Keep the existing equality API total. Lean's BEq deriving handler uses a
-- partial helper for nested inductives; these four structural recursions
-- traverse the expression and its nested lists without that trust boundary.
mutual
  def instBEqExpr.beq (self other : Expr) : Bool :=
    match self, other with
    | .ident a, .ident b | .str a, .str b => a == b
    | .int a, .int b => a == b
    | .float64Bits a, .float64Bits b => a == b
    | .bool a, .bool b => a == b
    | .jsNull, .jsNull => true
    | .call f xs, .call g ys => instBEqExpr.beq f g && beqExprList xs ys
    | .object xs, .object ys | .objectML xs, .objectML ys
    | .objectQuoted xs, .objectQuoted ys | .objectQuotedML xs, .objectQuotedML ys
    | .objectFromEntries xs, .objectFromEntries ys => beqExprFields xs ys
    | .arr xs, .arr ys => beqExprList xs ys
    | .arrow ty a, .arrow ty' b => ty == ty' && instBEqExpr.beq a b
    | .generic f xs, .generic g ys => instBEqExpr.beq f g && xs == ys
    | .lambda ps a, .lambda qs b => ps == qs && instBEqExpr.beq a b
    | .method t n xs, .method u m ys => instBEqExpr.beq t u && n == m && beqExprList xs ys
    | _, _ => false
  termination_by structural self

  private def beqExprList (self other : List Expr) : Bool :=
    match self, other with
    | [], [] => true
    | a :: xs, b :: ys => instBEqExpr.beq a b && beqExprList xs ys
    | _, _ => false
  termination_by structural self

  private def beqExprFields (self other : List (String × Expr)) : Bool :=
    match self, other with
    | [], [] => true
    | a :: xs, b :: ys => beqExprField a b && beqExprFields xs ys
    | _, _ => false
  termination_by structural self

  private def beqExprField (self other : String × Expr) : Bool :=
    self.1 == other.1 && instBEqExpr.beq self.2 other.2
  termination_by structural self
end

instance instBEqExpr : BEq Expr := ⟨instBEqExpr.beq⟩

/-- One statement in the generator fragment. The first three are the
straight-line forms; the rest carry block graphs: definite-assignment
declarations, assignment, an unconditional loop, a selector switch, a
conditional, and labelled control transfer. -/
inductive Stmt where
  /-- `const name = yield* value`. -/
  | constYield (name : String) (value : Expr)
  /-- `return value`. -/
  | ret (value : Expr)
  /-- `yield* value` with the answer discarded. -/
  | yieldDiscard (value : Expr)
  /-- `let name!: type` — declared, definitely assigned later. -/
  | letDefinite (name : String) (type : String)
  /-- `let name = value`. -/
  | letInit (name : String) (value : Expr)
  /-- `name = value`. -/
  | assign (name : String) (value : Expr)
  /-- `while (true) { body }`, optionally labelled. -/
  | whileTrue (label : Option String) (body : List Stmt)
  /-- `switch (scrutinee) { case n: { body } … }`. -/
  | switch (scrutinee : Expr) (cases : List (Nat × List Stmt))
  /-- `if (condition) { then } else { else }`; an empty else is omitted. -/
  | ifElse (condition : Expr) (thenBranch elseBranch : List Stmt)
  /-- `label: { body }`. -/
  | labelled (label : String) (body : List Stmt)
  /-- `const name = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () { body }), onExit))`:
  a nested generator run in its own scope, its exit observed by `onExit`. -/
  | scopedGen (name : String) (body : List Stmt) (onExit : Expr)
  /-- `break label` or plain `break`. -/
  | breakTo (label : Option String)
  /-- `continue label` or plain `continue`. -/
  | continueTo (label : Option String)
  /-- `value` as a statement. -/
  | exprStmt (value : Expr)

-- `Stmt` is a nested inductive (statement lists inside statements); Lean's
-- `BEq` deriving handler uses a partial helper for it, so equality is a total
-- structural recursion here.
mutual
  def instBEqStmt.beq (self other : Stmt) : Bool :=
    match self, other with
    | .constYield a x, .constYield b y => a == b && x == y
    | .ret x, .ret y | .yieldDiscard x, .yieldDiscard y | .exprStmt x, .exprStmt y => x == y
    | .letDefinite a t, .letDefinite b u => a == b && t == u
    | .letInit a x, .letInit b y | .assign a x, .assign b y => a == b && x == y
    | .whileTrue l xs, .whileTrue m ys => l == m && beqStmtList xs ys
    | .switch x cs, .switch y ds => x == y && beqStmtCases cs ds
    | .ifElse c xs xs', .ifElse d ys ys' => c == d && beqStmtList xs ys && beqStmtList xs' ys'
    | .labelled l xs, .labelled m ys => l == m && beqStmtList xs ys
    | .scopedGen a xs x, .scopedGen b ys y => a == b && beqStmtList xs ys && x == y
    | .breakTo l, .breakTo m | .continueTo l, .continueTo m => l == m
    | _, _ => false
  termination_by structural self

  private def beqStmtList (self other : List Stmt) : Bool :=
    match self, other with
    | [], [] => true
    | a :: xs, b :: ys => instBEqStmt.beq a b && beqStmtList xs ys
    | _, _ => false
  termination_by structural self

  private def beqStmtCases (self other : List (Nat × List Stmt)) : Bool :=
    match self, other with
    | [], [] => true
    | a :: xs, b :: ys => beqStmtCase a b && beqStmtCases xs ys
    | _, _ => false
  termination_by structural self

  private def beqStmtCase (self other : Nat × List Stmt) : Bool :=
    self.1 == other.1 && beqStmtList self.2 other.2
  termination_by structural self
end

instance instBEqStmt : BEq Stmt := ⟨instBEqStmt.beq⟩

/-- An exported constant declaration with an optional target type spelling. -/
structure ConstDecl where
  doc : List String
  name : String
  value : Expr
  type : Option String := none
  deriving BEq

/-- An exported straight-line Effect generator declaration. -/
structure ProgDecl where
  doc : List String
  name : String
  paramName : String
  paramType : String
  stmts : List Stmt
  deriving BEq

/-- One checked effectful Schema field API. This target-only node retains all
directional types needed by the Effect v4 renderer without storing host
functions or falling back to raw source text. -/
structure EffectfulFieldDecl where
  fieldName : String
  sourceType : String
  fieldType : String
  readService : String
  readMethod : String
  readError : String
  writeService : String
  writeMethod : String
  writeError : String
  deriving BEq

/-- An exported class with an optional heritage expression and verbatim
member lines. The heritage is an expression because Effect's service classes
extend a call, `Context.Service<Self, Shape>()("Name")`. -/
structure ClassDecl where
  doc : List String
  name : String
  heritage : Option Expr
  members : List String := []
  deriving BEq

/-- One declaration in a generated TypeScript module. `raw` is retained only
as the Foldlab compatibility escape hatch for generated local helpers. It is
not admitted as checked Effect4 target syntax and receives no lowering rule. -/
inductive Decl where
  | const (decl : ConstDecl)
  | prog (decl : ProgDecl)
  | effectfulField (declaration : EffectfulFieldDecl)
  | classDecl (declaration : ClassDecl)
  | raw (text : String)
  deriving BEq

/-- An import declaration in the retained target fragment. -/
inductive Import where
  | all (name : String) (path : String)
  | named (names : List String) (path : String)
  | types (names : List String) (path : String)

/-- A generated TypeScript module. -/
structure Module where
  header : List String
  imports : List Import
  decls : List Decl

end TypeScript

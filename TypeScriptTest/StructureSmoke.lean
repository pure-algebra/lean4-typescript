import TypeScript.Structure
import TypeScript.Render

/-! Structured control flow on three small graphs: a diamond, a self-loop, and
an irreducible pair. Bodies are one statement per node followed by the
transfers to its successors. -/

namespace TypeScriptTest.StructureSmoke

open TypeScript TypeScript.Structure

def body (g : Graph) (n : Nat) (transfer : Nat → Option (List Stmt)) : Option (List Stmt) := do
  let controls ← (g.succs n).mapM transfer
  pure (Stmt.exprStmt (.ident ("b" ++ toString n)) :: controls.flatten)

/-- 0 → 1, 0 → 2, 1 → 3, 2 → 3: node 3 is a merge. -/
def diamond : Graph :=
  { size := 4, entry := 0, succs := fun n => match n with | 0 => [1, 2] | 1 => [3] | 2 => [3] | _ => [] }

example : rpo diamond = [0, 2, 1, 3] := by native_decide
example : idom diamond 3 = some 0 := by native_decide
example : isMerge diamond 3 = true := by native_decide
example : reducible diamond = true := by native_decide
example : (emitWith diamond {} (body diamond)).map (Render.stmts house0 0) = some
  ("L3: {\n" ++
   "  b0\n" ++
   "  b1\n" ++
   "  break L3\n" ++
   "  b2\n" ++
   "  break L3\n" ++
   "}\n" ++
   "b3\n") := by native_decide

/-- 0 → 1, 1 → 1, 1 → 2: node 1 is a loop header entered from 0. -/
def selfLoop : Graph :=
  { size := 3, entry := 0, succs := fun n => match n with | 0 => [1] | 1 => [1, 2] | _ => [] }

example : isLoopHeader selfLoop 1 = true := by native_decide
example : reducible selfLoop = true := by native_decide
example : (emitWith selfLoop {} (body selfLoop)).map (Render.stmts house0 0) = some
  ("L1: {\n" ++
   "  b0\n" ++
   "  break L1\n" ++
   "}\n" ++
   "W1: while (true) {\n" ++
   "  b1\n" ++
   "  continue W1\n" ++
   "  b2\n" ++
   "}\n") := by native_decide

/-- 0 → 0, 0 → 1: the entry is its own loop header. -/
def entryLoop : Graph :=
  { size := 2, entry := 0, succs := fun n => match n with | 0 => [0, 1] | _ => [] }

example : isLoopHeader entryLoop 0 = true := by native_decide
example : (emitWith entryLoop {} (body entryLoop)).map (Render.stmts house0 0) = some
  ("W0: while (true) {\n" ++
   "  b0\n" ++
   "  continue W0\n" ++
   "  b1\n" ++
   "}\n") := by native_decide

/-- 0 → 1, 0 → 2, 1 → 2, 2 → 1: the cycle is entered at both nodes. -/
def irreducible : Graph :=
  { size := 3, entry := 0, succs := fun n => match n with | 0 => [1, 2] | 1 => [2] | 2 => [1] | _ => [] }

example : reducible irreducible = false := by native_decide
example : emitWith irreducible {} (body irreducible) = none := by native_decide

end TypeScriptTest.StructureSmoke

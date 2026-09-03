import TypeScript.Syntax

/-!
# Structured control flow from a block graph

A block graph (nodes `0 .. size-1`, an entry, successor lists) is turned into
labelled blocks, `while (true)` loops, `break` and `continue`, following the
shape js_of_ocaml gives its generated code (re-derived; the LGPL source is
reference only):

1. Reverse postorder by depth-first search from the entry; an edge is backward
   when its target does not come later in that order.
2. Immediate dominators by the Cooper–Harvey–Kennedy iteration over reverse
   postorder.
3. The graph is *reducible* when every backward edge's target dominates its
   source. Only reducible graphs are structured; the caller falls back to the
   dispatch form otherwise.
4. Emission over the dominator tree. A node's *merge children* (dominator
   children with several predecessors, or loop headers) are laid out after the
   node's own body as labelled blocks wrapping everything emitted before them,
   in reverse postorder, so a transfer to one of them is `break label`. A
   loop header is a labelled `while (true)`; a backward transfer to it is
   `continue label`. Any other successor has exactly one predecessor, is
   dominated by it, and is inlined at its single use.

The caller supplies each node's body as a function of the control transfer it
may use, so block-parameter moves stay the caller's business.
-/

namespace TypeScript

namespace Structure

/-- A block graph over `0 .. size - 1`. -/
structure Graph where
  size : Nat
  entry : Nat
  succs : Nat → List Nat

/-- Depth-first postorder from `entry`, fuel-bounded by the size. -/
def postorder (g : Graph) : List Nat :=
  let rec visit : Nat → List Nat → List Nat → Nat → List Nat × List Nat
    | 0, seen, order, _ => (seen, order)
    | fuel + 1, seen, order, node =>
      if seen.contains node then (seen, order)
      else
        let seen := node :: seen
        let (seen, order) := (g.succs node).foldl
          (fun (acc : List Nat × List Nat) next => visit fuel acc.1 acc.2 next) (seen, order)
        (seen, order ++ [node])
  (visit (g.size + 1) [] [] g.entry).2

/-- Reverse postorder: the entry first, every node after all of its
non-backward predecessors. -/
def rpo (g : Graph) : List Nat := (postorder g).reverse

/-- The position of a node in reverse postorder (`size` for an unreachable node). -/
def index (g : Graph) (node : Nat) : Nat :=
  match (rpo g).findIdx? (· = node) with
  | some i => i
  | none => g.size

def reachable (g : Graph) (node : Nat) : Bool := (rpo g).contains node

/-- An edge is backward when its target does not come later in reverse postorder. -/
def isBackEdge (g : Graph) (source target : Nat) : Bool :=
  index g target ≤ index g source

def preds (g : Graph) (node : Nat) : List Nat :=
  (rpo g).filter fun p => (g.succs p).contains node

/-- Immediate dominators by the Cooper–Harvey–Kennedy iteration; `none` for
the entry and for unreachable nodes. Positions are reverse-postorder indices. -/
def idoms (g : Graph) : List (Option Nat) :=
  let order := rpo g
  let n := order.length
  let idx (node : Nat) : Nat := index g node
  let rec intersect (fuel : Nat) (doms : List (Option Nat)) (a b : Nat) : Nat :=
    match fuel with
    | 0 => a
    | fuel + 1 =>
      if a = b then a
      else if a > b then
        match doms[a]? with
        | some (some a') => intersect fuel doms a' b
        | _ => a
      else
        match doms[b]? with
        | some (some b') => intersect fuel doms a b'
        | _ => a
  let step (doms : List (Option Nat)) : List (Option Nat) :=
    order.foldl (init := doms) fun doms node =>
      let i := idx node
      if i = 0 then doms
      else
        let processed := (preds g node).filterMap fun p =>
          match doms[idx p]? with
          | some (some _) => some (idx p)
          | _ => if idx p = 0 then some 0 else none
        match processed with
        | [] => doms
        | first :: rest =>
            let newIdom := rest.foldl (fun acc p => intersect n doms acc p) first
            doms.set i (some newIdom)
  let start : List (Option Nat) := (List.range n).map fun i => if i = 0 then some 0 else none
  let rec iterate : Nat → List (Option Nat) → List (Option Nat)
    | 0, doms => doms
    | fuel + 1, doms =>
      let next := step doms
      if next == doms then doms else iterate fuel next
  iterate (n + 1) start

/-- The immediate dominator of a node, as a node. -/
def idom (g : Graph) (node : Nat) : Option Nat :=
  if node = g.entry then none
  else
    match (idoms g)[index g node]? with
    | some (some i) => (rpo g)[i]?
    | _ => none

/-- `a` dominates `b`: walk `b`'s dominator chain. -/
def dominates (g : Graph) (a b : Nat) : Bool :=
  let rec walk : Nat → Nat → Bool
    | 0, _ => false
    | fuel + 1, node => if node = a then true else
        match idom g node with
        | some up => walk fuel up
        | none => false
  walk (g.size + 1) b

/-- Every backward edge's target dominates its source, and every node is reachable. -/
def reducible (g : Graph) : Bool :=
  (List.range g.size).all fun node =>
    reachable g node &&
    (g.succs node).all fun next => !isBackEdge g node next || dominates g next node

def isLoopHeader (g : Graph) (node : Nat) : Bool :=
  (preds g node).any fun p => isBackEdge g p node

def isMerge (g : Graph) (node : Nat) : Bool :=
  (preds g node).length ≥ 2

/-- The dominator-tree children of a node, in reverse postorder. -/
def children (g : Graph) (node : Nat) : List Nat :=
  (rpo g).filter fun c => idom g c == some node

/-- The four structured shapes, supplied by the caller so each is one of its
tagged lowering rules: a loop, a merge block, and the two transfers. -/
structure Shapes where
  loop : String → List Stmt → Stmt := fun label body => .whileTrue (some label) body
  merge : String → List Stmt → Stmt := fun label body => .labelled label body
  continueTo : String → Stmt := fun label => .continueTo (some label)
  breakTo : String → Stmt := fun label => .breakTo (some label)

/-- Labels: `L<node>` for a merge block, `W<node>` for a loop. -/
def blockLabel (node : Nat) : String := "L" ++ toString node
def loopLabel (node : Nat) : String := "W" ++ toString node

/-- Emit one node and its dominator subtree. `body node transfer` returns the
node's statements, asking `transfer target` for the control statements of
each successor edge; it fails when a body cannot be lowered or a transfer has
no structured shape. -/
def emitNode (g : Graph) (shapes : Shapes)
    (body : Nat → (Nat → Option (List Stmt)) → Option (List Stmt)) :
    Nat → Nat → Option (List Stmt)
  | 0, _ => none
  | fuel + 1, current => do
    let transfer (target : Nat) : Option (List Stmt) :=
      if isBackEdge g current target && isLoopHeader g target && dominates g target current then
        some [shapes.continueTo (loopLabel target)]
      else if isMerge g target || isLoopHeader g target then
        some [shapes.breakTo (blockLabel target)]
      else if idom g target == some current then
        emitNode g shapes body fuel target
      else none
    let own ← body current transfer
    let merges := (children g current).filter fun c => isMerge g c || isLoopHeader g c
    merges.foldlM (init := own) fun acc m => do
      let inner ← emitNode g shapes body fuel m
      let placed := if isLoopHeader g m then [shapes.loop (loopLabel m) inner] else inner
      pure ([shapes.merge (blockLabel m) acc] ++ placed)

/-- Emit a reducible graph from its entry. -/
def emitWith (g : Graph) (shapes : Shapes)
    (body : Nat → (Nat → Option (List Stmt)) → Option (List Stmt)) : Option (List Stmt) :=
  if reducible g then emitNode g shapes body (g.size + 1) g.entry else none

end Structure

end TypeScript

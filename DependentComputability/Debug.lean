import Std
import Lean

open Lean

structure DebugState where
  inDebug : Bool := false
  breakpointMask : UInt64 := 0 -- fast check based on name hash
  breakpoints : Std.HashSet Name := {}
deriving Inhabited

initialize debugState : IO.Ref DebugState ←
  IO.mkRef {}

local syntax "hash_decl_name%" : term

elab_rules : term | `(hash_decl_name%) => do
  let some declName ← Elab.Term.getDeclName? |
    throwError "invalid `hash_decl_name%` macro, the declaration name is not available"
  let hash := hash declName
  return toExpr ((1 : UInt64) <<< (hash >>> 10 &&& 63))

#check decl_name%

unsafe def withDebugImpl (x : Unit → α) (declName : Name := by exact decl_name%)
    (nameBit : UInt64 := by exact hash_decl_name%) : α :=
  unsafeBaseIO do
    let info ← debugState.get
    let val := x ()

    return val

def withDebug (normal : Unit → α) (debug : Unit → α) (declName : Name := by exact decl_name%)
    (nameBit : UInt64 := by exact hash_decl_name%) : α := normal ()

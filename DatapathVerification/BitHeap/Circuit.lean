namespace BitHeap

inductive Binop
| xor | or | and | nand
deriving Repr, DecidableEq, Inhabited, Hashable

/-- A circuit that describes a logical operation.-/
inductive Circuit
| bit (varIndex : Nat)
| binop (op : Binop) (a b : Circuit)
| const (val : Bool)
deriving Repr, DecidableEq, Inhabited, Hashable

namespace Circuit

/-- The number of variables in a circuit. -/
def numVars (c : Circuit) : Nat :=
  match c with
  | .bit varIndex => varIndex + 1
  | .binop _ a b => max a.numVars b.numVars
  | .const _ => 0

/-- An environment assigns a value to each bit, where bits are given by natural number indexes. -/
def BitEnv := Nat → Bool

/-- Evaluate a circuit under a given environment. -/
def eval (c : Circuit) (env : BitEnv) : Bool :=
  match c with
  | .bit varIndex => env varIndex
  | .binop op a b =>
    let aval := a.eval env
    let bval := b.eval env
    match op with
    | .xor => aval != bval
    | .or => aval || bval
    | .and => aval && bval
    | .nand => !(aval && bval)
  | .const val => val

def atLeastTwo (a b c : Circuit) : Circuit :=
  binop .or (binop .or (binop .and a b) (binop .and a c)) (binop .and b c)

@[simp]
theorem const_false_eval_eq :
  (const false).eval env = false := by simp [eval]

@[simp]
theorem eval_and (a b : Circuit) (env : BitEnv) :
    (binop .and a b).eval env = ((a.eval env) && (b.eval env)) := by
  simp [eval]

@[simp]
theorem eval_xor (a b : Circuit) (env : BitEnv) :
    (binop .xor a b).eval env = ((a.eval env) != (b.eval env)) := by
  simp [eval]

@[simp]
theorem eval_atLeastTwo (a b c : Circuit) (env : BitEnv) :
  (atLeastTwo a b c).eval env = ((a.eval env) && (b.eval env) || (a.eval env) && (c.eval env) || (b.eval env) && (c.eval env)) := by
  simp [eval, atLeastTwo]

end Circuit

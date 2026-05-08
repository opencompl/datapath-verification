namespace BitHeapCircuit

inductive Binop
| xor | or | and | nand
deriving Repr, DecidableEq, Inhabited, Hashable

/-- A circuit that describes a logical operation.-/
inductive Circuit
| bit (varIndex : Nat)
| binop (op : Binop) (a b : Circuit)
| const (val : Bool)
deriving Repr, DecidableEq, Inhabited, Hashable

/-- The number of variables in a circuit. -/
def Circuit.numVars (c : Circuit) : Nat :=
  match c with
  | .bit varIndex => varIndex + 1
  | .binop _ a b => max a.numVars b.numVars
  | .const _ => 0

/-- An environment assigns a value to each bit, where bits are given by natural number indexes. -/
def BitEnv := Nat → Bool

/-- Evaluate a circuit under a given environment. -/
def Circuit.eval (c : Circuit) (env : BitEnv) : Bool :=
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

def Circuit.atLeastTwo (a b c : Circuit) : Circuit :=
  Circuit.binop .or (Circuit.binop .or (Circuit.binop .and a b) (Circuit.binop .and a c)) (Circuit.binop .and b c)

@[simp]
theorem Circuit.const_false_eval_eq :
  (Circuit.const false).eval env = false := by simp [Circuit.eval]

@[simp]
theorem Circuit.eval_and (a b : Circuit) (env : BitEnv) :
    (Circuit.binop .and a b).eval env = ((a.eval env) && (b.eval env)) := by
  simp [Circuit.eval]

@[simp]
theorem Circuit.eval_xor (a b : Circuit) (env : BitEnv) :
    (Circuit.binop .xor a b).eval env = ((a.eval env) != (b.eval env)) := by
  simp [Circuit.eval]

@[simp]
theorem Circuit.eval_atLeastTwo (a b c : Circuit) (env : BitEnv) :
  (Circuit.atLeastTwo a b c).eval env = ((a.eval env) && (b.eval env) || (a.eval env) && (c.eval env) || (b.eval env) && (c.eval env)) := by
  simp [Circuit.eval, Circuit.atLeastTwo]

end BitHeapCircuit

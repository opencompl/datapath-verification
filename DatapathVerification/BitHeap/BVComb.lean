import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.DaddaTree

open BitHeap
namespace Comb

inductive ArithBinopKind
| add
| mul

-- inductive ArithUnopKind
-- | neg

-- inductive BooleanBinopKind
-- | and | or | xor

inductive ArithCircuit
  | var (width : Nat) (varIndex : Nat)
  | arithbinop (kind : ArithBinopKind) (width : Nat) (l r : ArithCircuit)
  -- | arithunop (kind : ArithUnopKind) (width : Nat) (arg : ArithCircuit)
  -- | bvbinop (kind : BooleanBinopKind) (width : Nat) (l r : ArithCircuit)

/--
Convert a bitheap into a new bitheap that has a single row,
by building a Dadda tree of adders to reduce the bitheap to a single row.
-/
def BitHeap.toSingleRow : BitHeap → CircuitVector
  | bh =>
    let (pp1, pp2) := DaddaTree.DaddaTree bh
    -- add pp1 and pp2 to get the final row
    sorry

namespace ArithCircuit
/--
Given a bitvector (x : BV 3), but a bitheap
```
*   *  *
x2 x1 x0
```
-/
def bitheapOfVar (width : Nat) (varIndex : Nat) : BitHeap :=
  --  I want to create a bitheap that has one bit-variable per bit in the bitvector variable.
  -- | We need to know that this index is unique which is a gigantic pain.
  List.range width |>.foldl (fun bh i => bh.addBit i (BitHeap.Circuit.bit (varIndex * width + i))) BitHeap.empty

def toBitHeap (c : ArithCircuit) : BitHeap :=
  match c with
  | .var width varIndex => bitheapOfVar width varIndex
  | .arithbinop kind width l r =>
    match kind with
    | .add => (toBitHeap l).addBitHeap (toBitHeap r)
    | .mul => (toBitHeap l).mulBitHeap (toBitHeap r)
  -- | .arithunop kind width arg =>
  --   match kind with
  --   | .neg => (toBitHeap arg).negBitHeap
  -- | .bvbinop kind width l r =>
  --   match kind with
  --   | .and =>
  --     let lRow := (l.toBitHeap).toSingleRow
  --     let rRow := (r.toBitHeap).toSingleRow
  --     let newRow := Array.zipWith (fun lBit rBit => Circuit.and lBit rBit) lRow rRow
  --     BitHeap.fromRow newRow

def toCircuitVector (c : ArithCircuit) : CircuitVector :=
  let bh := c.toBitHeap
  bh.toSingleRow

end ArithCircuit

end Comb

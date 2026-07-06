import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Compressors.DaddaTree
import DatapathVerification.BitHeap.Compressors.NaiveCompression


open BitHeap
namespace Comb

inductive ArithBinopKind
| add
| mul

-- inductive ArithUnopKind
-- | neg

-- inductive BooleanBinopKind
-- | and | or | xor

inductive ArithCircuit : Nat → Type
  | var (varIndex : Nat) : ArithCircuit w
  | add (args : List (ArithCircuit w)) : ArithCircuit w
  | mul (l r : ArithCircuit w) : ArithCircuit w
  -- | arithunop (kind : ArithUnopKind) (width : Nat) (arg : ArithCircuit)
  -- | bvbinop (kind : BooleanBinopKind) (width : Nat) (l r : ArithCircuit)

/--
Convert a bitheap into a new bitheap that has a single row,
by using the naive compression algorithm.
-/
def BitHeap.toSingleRow (bh : BitHeap w) : CircuitVector :=
    let (pp1, pp2) := NaiveCompression.naiveCompression bh
    sorry

namespace ArithCircuit
/--
Given a bitvector (x : BV 3), but a bitheap
```
*   *  *
x2 x1 x0
```
-/
def bitheapOfVar (varIndex : Nat) : BitHeap w :=
  --  I want to create a bitheap that has one bit-variable per bit in the bitvector variable.
  -- | We need to know that this index is unique which is a gigantic pain.
  List.range w |>.foldl (fun bh i => bh.addBit i (BitHeap.Circuit.bit (varIndex * w + i))) (BitHeap.empty w)

def toBitHeap : ArithCircuit w → BitHeap w
  | .var varIndex => bitheapOfVar varIndex
  | .add args => BitHeap.addBitHeap (args.map toBitHeap)
  | .mul l r => BitHeap.truncate ((toBitHeap l).mulBitHeap (toBitHeap r)) w (by omega)

-- def toBitHeap' (c : ArithCircuit) : BitHeap w :=
--   match c with
--   | .var width varIndex => bitheapOfVar width varIndex
--   | .add width args => BitHeap.addBitHeap (args.map toBitHeap)
--   | .mul width l r => BitHeap.truncate ((toBitHeap l).mulBitHeap (toBitHeap r)) width (by omega)
  -- | .arithunop kind width arg =>`
  --   match kind with
  --   | .neg => (toBitHeap arg).negBitHeap
  -- | .bvbinop kind width l r =>
  --   match kind with
  --   | .and =>
  --     let lRow := (l.toBitHeap).toSingleRow
  --     let rRow := (r.toBitHeap).toSingleRow
  --     let newRow := Array.zipWith (fun lBit rBit => Circuit.and lBit rBit) lRow rRow
  --     BitHeap.fromRow newRow

def toCircuitVector (c : ArithCircuit w) : CircuitVector :=
  let bh := c.toBitHeap
  bh.toSingleRow

end ArithCircuit

end Comb

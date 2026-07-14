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

def BitVecEnv (w : Nat) := Nat → BitVec w

/--
Convert a bitheap into a new bitheap that has a single row,
by using the naive compression algorithm.
-/
def BitHeap.toSingleRow (bh : BitHeap w) : CircuitVector :=
    let (pp1, _) := NaiveCompression.naiveCompression bh
    pp1.columns.toArray.map fun col => col.elems.toList.headD (.const false)

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

def denote (ρ : BitVecEnv w) : ArithCircuit w → BitVec w
  | .var i => ρ i
  | .add args => (args.map (denote ρ)).foldl (· + ·) 0
  | .mul l r => denote ρ l * denote ρ r

def toCircuitVector (c : ArithCircuit w) : CircuitVector :=
  let bh := c.toBitHeap
  BitHeap.toSingleRow bh

end ArithCircuit

end Comb

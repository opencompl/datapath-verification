import DatapathVerification.BitHeap.Netlist

/-!
CLI entry point for the verified datapath synthesis flow.

Usage:
- `datapath-cli mul <width> [<liveA> <liveB>]` — compress a `<width>`-bit
  multiplication of two operands whose live widths are `<liveA>`/`<liveB>`
  (defaulting to `<width>`). Bits above an operand's live width are constant
  0, i.e. the operand is zero-extended from its live width.
- `datapath-cli add <width> <numOperands> [<live0> ... <liveN-1>]` — compress
  a `<width>`-bit addition of `<numOperands>` operands with the given live
  widths (defaulting to `<width>` each).

Prints a gate netlist for the compressed bit heap (see
`DatapathVerification.BitHeap.Netlist` for the format). Exits nonzero and
prints `error: ...` to stderr on failure.
-/

def printResult : Except String (Array String) → IO UInt32
  | .error msg => do
      IO.eprintln s!"error: {msg}"
      return 1
  | .ok lines => do
      let out ← IO.getStdout
      for line in lines do
        out.putStrLn line
      return 0

def usage : IO UInt32 := do
  IO.eprintln
    "usage: datapath-cli mul <width> [<liveA> <liveB>] | add <width> <numOperands> [<live0> ...]"
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "mul" :: wStr :: rest =>
    match wStr.toNat?, rest.mapM (·.toNat?) with
    | some w, some [] => printResult (BitHeap.Netlist.compressMul w w w)
    | some w, some [wa, wb] => printResult (BitHeap.Netlist.compressMul w wa wb)
    | _, _ => usage
  | "add" :: wStr :: nStr :: rest =>
    match wStr.toNat?, nStr.toNat?, rest.mapM (·.toNat?) with
    | some w, some n, some [] =>
        printResult (BitHeap.Netlist.compressAdd w (List.replicate n w))
    | some w, some n, some widths =>
        if widths.length == n then
          printResult (BitHeap.Netlist.compressAdd w widths)
        else usage
    | _, _, _ => usage
  | _ => usage


import DatapathVerification.BitHeap.Netlist

/-!
CLI entry point for the verified datapath synthesis flow.

Usage:
- `datapath-cli mul <width> [<specA> <specB>]` — compress a `<width>`-bit
  multiplication of two operands with the given operand specs (defaulting to
  `<width>` live bits each).
- `datapath-cli add <width> <numOperands> [<spec0> ... <specN-1>]` — compress
  a `<width>`-bit addition of `<numOperands>` operands with the given operand
  specs (defaulting to `<width>` live bits each).

An operand spec is `<live>` or `<live>s`: the operand's low `<live>` bits are
its real bits, and the bits above them are constant 0 (`<live>`, zero
extension) or copies of bit `<live> - 1` (`<live>s`, sign extension).

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

/-- Parse an operand spec: `<live>` (zero-extended) or `<live>s` (sign-extended). -/
def parseSpec (s : String) : Option (Nat × Bool) :=
  if s.endsWith "s" then
    (·, true) <$> (s.dropEnd 1).toNat?
  else
    (·, false) <$> s.toNat?

def usage : IO UInt32 := do
  IO.eprintln
    "usage: datapath-cli mul <width> [<specA> <specB>] | add <width> <numOperands> [<spec0> ...]\n\
     where a spec is <live> (zero-extended) or <live>s (sign-extended)"
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "mul" :: wStr :: rest =>
    match wStr.toNat?, rest.mapM parseSpec with
    | some w, some [] => printResult (BitHeap.Netlist.compressMul w w w false false)
    | some w, some [(wa, sa), (wb, sb)] =>
        printResult (BitHeap.Netlist.compressMul w wa wb sa sb)
    | _, _ => usage
  | "add" :: wStr :: nStr :: rest =>
    match wStr.toNat?, nStr.toNat?, rest.mapM parseSpec with
    | some w, some n, some [] =>
        printResult (BitHeap.Netlist.compressAdd w (List.replicate n (w, false)))
    | some w, some n, some specs =>
        if specs.length == n then
          printResult (BitHeap.Netlist.compressAdd w specs)
        else usage
    | _, _, _ => usage
  | _ => usage


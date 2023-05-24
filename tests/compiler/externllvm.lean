import Lean
import Lean.Compiler.IR.LLVM

open Lean Compiler IR LLVM CodeGeneratedBy

def fooImpl : CodeGenerator := fun _regs => do
  dbg_trace "ahhhhhhhhh"
  return 0


@[extern llvm codeGeneratedBy fooImpl]
def foo (x : UInt32) : UInt32 := x

-- TODO: add tracing option
-- set option trace.compiler.llvm true in
def main : IO Unit := do
  let v := foo 10
  IO.println v
  return ()

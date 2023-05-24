import Lean.Compiler.IR.LLVM

open Lean Compiler IR LLVM CodeGeneratedBy

def fooImpl : CodeGenerator := fun _regs => do
  dbg_trace "ahhhhhhhhh"
  return 0


--@[extern c codeGeneratedBy fooImpl]
def foo (x : UInt32) : UInt32 := x

import Lean.Compiler.IR.LLVM.Pure
import Lean.Compiler.IR.LLVM.CodeGeneratedBy

open Lean Compiler IR LLVM Pure Builder CodeGeneratedBy

def fooImpl : CodeGenerator := fun regs => do
  Ret regs[0]!


@[extern llvm codeGeneratedBy fooImpl]
def foo (x : UInt32) : UInt32 := x

-- TODO: add tracing option
-- set option trace.compiler.llvm true in
def main : IO Unit := do
  let v := foo 10
  IO.println v
  return ()

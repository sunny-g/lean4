/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Siddharth Bhat
-/

import Lean.Data.HashMap
import Lean.Compiler.IR.LLVM.LLVMBindings
import Lean.Compiler.IR.LLVM.Pure
import Lean.Compiler.IR.Basic

namespace Lean.IR.LLVM.Pure

structure InstantiationState (llvmctx : LLVM.Context) where
  llvmmodule : LLVM.Module llvmctx
  llvmbuilder : LLVM.Builder llvmctx
  registerFile : HashMap Reg (LLVM.Value llvmctx) := {}
  basicBlocks : HashMap BBId (LLVM.BasicBlock llvmctx) := {}
  functions : HashMap String (LLVM.Value llvmctx) := {}

abbrev InstantiationM (llvmctx : LLVM.Context) (α : Type) : Type :=
  ReaderT PureBuilderState (StateRefT (InstantiationState llvmctx) IO) α

def getLLVMBuilder : InstantiationM llvmctx (LLVM.Builder llvmctx) :=
  InstantiationState.llvmbuilder <$> get

def getBuilderState : InstantiationM llvmctx PureBuilderState :=
   read

def getModule : InstantiationM llvmctx (LLVM.Module llvmctx) :=
  InstantiationState.llvmmodule <$> get

def getRegisterFile : InstantiationM llvmctx (HashMap Reg (LLVM.Value llvmctx)) :=
  InstantiationState.registerFile <$> get

def getBasicBlocks : InstantiationM llvmctx (HashMap BBId (LLVM.BasicBlock llvmctx)) :=
  InstantiationState.basicBlocks <$> get

def getFunctions : InstantiationM llvmctx (HashMap String (LLVM.Value llvmctx)) :=
  InstantiationState.functions <$> get

partial def Ty.instantiate : Ty → BaseIO (LLVM.LLVMType llvmctx)
| .function args retTy => do LLVM.functionType (← retTy.instantiate) (← args.mapM Ty.instantiate)
| .void => LLVM.voidType llvmctx -- TODO: change function name to `LLVM.voidTypeInContext`
| .int width => LLVM.intTypeInContext llvmctx width
| .opaquePointer addrspace => LLVM.opaquePointerTypeInContext llvmctx addrspace
| .float => LLVM.floatTypeInContext llvmctx
| .double => LLVM.doubleTypeInContext llvmctx
| .array elemty nelem => do LLVM.arrayType (← elemty.instantiate) nelem

def Ty.ofIRType : IRType → Ty
  | .float      => .float
  | .uint8      => .int 8
  | .uint16     => .int 16
  | .uint32     => .int 32
  | .uint64     => .int 64
  | .usize      => .int 64 -- TODO this is imporperly solved in the LLVM bindings as well right now
  | .object     => .opaquePointer
  | .tobject    => .opaquePointer
  | .irrelevant => .opaquePointer
  | .struct _ _ => panic! "dead code"
  | .union _ _  => panic! "dead code"

def FunctionDeclaration.instantiate (decl : FunctionDeclaration) : InstantiationM llvmctx (LLVM.Value llvmctx) := do
  let fnty ← (Ty.function decl.args decl.retty).instantiate
  let fn ← LLVM.getOrAddFunction (← getModule) decl.name fnty
  modify (fun s => { s with functions := s.functions.insert decl.name fn })
  return fn

def Reg.instantiate (reg : Reg) : InstantiationM llvmctx (LLVM.Value llvmctx) := do
  match (← getRegisterFile).find? reg with
  | .none => throw <| .userError s!"unable to find register '{reg}', this is a miscompilation."
  | .some v => return v

def BBId.instantiate (bbid : BBId) : InstantiationM llvmctx (LLVM.BasicBlock llvmctx) := do
  match (← getBasicBlocks).find? bbid with
  | .none => throw <| .userError s!"unable to find basic block '{bbid}', this is a miscompilation."
  | .some v => return v

def IntPredicate.instantiate : IntPredicate → LLVM.IntPredicate
| .eq => LLVM.IntPredicate.EQ
| .ne => LLVM.IntPredicate.NE
| .ugt => LLVM.IntPredicate.UGT
| .uge => LLVM.IntPredicate.UGE
| .ult => LLVM.IntPredicate.ULT
| .ule => LLVM.IntPredicate.ULE
| .sgt => LLVM.IntPredicate.SGT
| .sge => LLVM.IntPredicate.SGE
| .slt => LLVM.IntPredicate.SLT
| .sle => LLVM.IntPredicate.SLE

def Instruction.instantiate : Instruction → InstantiationM llvmctx (LLVM.Value llvmctx)
| .alloca ty name => do
   LLVM.buildAlloca (← getLLVMBuilder) (← ty.instantiate) name
| .load2 ty val name => do
    LLVM.buildLoad2 (← getLLVMBuilder) (← ty.instantiate) (← val.instantiate) name
| .store val pointer => do
    LLVM.buildStore (← getLLVMBuilder) (← val.instantiate) (← pointer.instantiate)
| .gep ty base ixs => do
  LLVM.buildGEP2 (← getLLVMBuilder) (← ty.instantiate) (← base.instantiate) (← ixs.mapM Reg.instantiate)
| .inboundsgep ty base ixs => do
  LLVM.buildInBoundsGEP2 (← getLLVMBuilder) (← ty.instantiate) (← base.instantiate) (← ixs.mapM Reg.instantiate)
| .sext val destTy => do
  LLVM.buildSext (← getLLVMBuilder) (← val.instantiate) (← destTy.instantiate)
| .zext val destTy => do
  LLVM.buildZext (← getLLVMBuilder) (← val.instantiate) (← destTy.instantiate)
| .sext_or_trunc val destTy => do
  LLVM.buildSextOrTrunc (← getLLVMBuilder) (← val.instantiate) (← destTy.instantiate)
| .ptrtoint pointer destTy => do
  LLVM.buildPtrToInt (← getLLVMBuilder) (← pointer.instantiate) (← destTy.instantiate)
| .mul lhs rhs name => do
  LLVM.buildMul (← getLLVMBuilder) (← lhs.instantiate) (← rhs.instantiate) name
| .add lhs rhs name => do
  LLVM.buildAdd (← getLLVMBuilder) (← lhs.instantiate) (← rhs.instantiate) name
| .sub lhs rhs name => do
  LLVM.buildSub (← getLLVMBuilder) (← lhs.instantiate) (← rhs.instantiate) name
| .not arg name => do
  LLVM.buildNot (← getLLVMBuilder) (← arg.instantiate) name
| .icmp pred lhs rhs name => do
  LLVM.buildICmp (← getLLVMBuilder) pred.instantiate (← lhs.instantiate) (← rhs.instantiate) name
| .phi ty bbIdAndVals => do
  let phiNode ← LLVM.buildPhi (← getLLVMBuilder) (← ty.instantiate)
  let vals : Array (LLVM.Value llvmctx) ← bbIdAndVals.mapM (Reg.instantiate ∘ Prod.snd)
  let bbs : Array (LLVM.BasicBlock llvmctx) ← bbIdAndVals.mapM (BBId.instantiate ∘ Prod.fst)
  LLVM.addIncoming phiNode vals bbs
  return phiNode

def reassureUserString : String := "This is a compiler bug."

def findBasicBlock! (bbid : BBId) : InstantiationM llvmctx (LLVM.BasicBlock llvmctx) := do
  let some bb := (← getBasicBlocks).find? bbid
    | throw <| .userError s!"Unable to find LLVM basic block {bbid}. {reassureUserString}"
  return bb

def findReg! (reg : Reg) : InstantiationM llvmctx (LLVM.Value llvmctx) := do
  IO.println s!"{(← getRegisterFile).toList.map Prod.fst}"
  let some v := (← getRegisterFile).find? reg
    | throw <| .userError s!"Unable to find LLVM value {reg}. {reassureUserString}"
  return v

def Terminator.instantiate : Terminator → InstantiationM llvmctx (LLVM.Value llvmctx)
| .default => throw <| .userError s!"should not have default when instantiating terminator. {reassureUserString}"
| .unreachable => do LLVM.buildUnreachable (← getLLVMBuilder)
| .br bbid => do
    LLVM.buildBr (← getLLVMBuilder) (← findBasicBlock! bbid)
| .condbr val then_ else_ => do
    LLVM.buildCondBr (← getLLVMBuilder) (← findReg! val) (← findBasicBlock! then_) (← findBasicBlock! else_)
| .ret val => do LLVM.buildRet (← getLLVMBuilder) (← findReg! val)
| .switch val cases defCase => do
    let switchInstr ← LLVM.buildSwitch (← getLLVMBuilder) (← findReg! val) (← findBasicBlock! defCase)
                    (UInt64.ofNat cases.size)
    cases.forM (fun (val, bb) => do LLVM.addCase switchInstr (← findReg! val) (← findBasicBlock! bb))
    return switchInstr

def FunctionDefinition.instantiate (defn : FunctionDefinition) : InstantiationM llvmctx Unit := do
  let some llvmfn := (← getFunctions).find? defn.name
    | throw <| .userError s!"Unable to find LLVM function declaration for {defn.name}. {reassureUserString}"

  let mut llvmbbs : Array (BasicBlock × LLVM.BasicBlock llvmctx) :=
    Array.mkEmpty defn.body.size
  -- generate basic blocks. Only after generating all the basic blocks
  -- do we fill them in with instructions to allow for mutual dependencies in
  -- the control flow graph.
  IO.println s!"instantiating function {defn.name}"
  for bbid in defn.body do
    IO.println s!"setting up bb {bbid}"
    let some bb := (← getBuilderState).bbs.find? bbid
      | throw <| .userError s!"Unable to find LLVM Basic block {bbid}. {reassureUserString}"
    let llvmbb ← LLVM.appendBasicBlockInContext llvmctx llvmfn bb.name
    llvmbbs := llvmbbs.push (bb, llvmbb)
    modify fun s => { s with basicBlocks := s.basicBlocks.insert bbid llvmbb }

  for (bb, llvmbb) in llvmbbs do
      LLVM.positionBuilderAtEnd (← getLLVMBuilder) llvmbb
      bb.instrs.forM (fun instr => do
        let llvminstr ← Instruction.instantiate instr.value
        if let .assign dest _ := instr then
          modify fun s => { s with registerFile := s.registerFile.insert dest llvminstr }
      )
      -- TODO: should we assert that the terminator is in fact not .default anymore?
      -- should we have Option Terminator without default?
      IO.println s!"Terminator: {repr bb.terminator}"
      let _ ← bb.terminator.instantiate

-- create an LLVM module that maps the pure 'PureBuilderState' into a real LLVM module pointer.
def instantiateToplevel : InstantiationM llvmctx Unit := do
  let state ← getBuilderState
  -- 1. Create all function declarations up-front, to allow for mutual
  --    definitions
  for (_, decl) in (state.functionDecls.toArray) do
    let _ ← decl.instantiate

  for (defnId, defn) in state.functionDefs.toArray do
    IO.println s!"Instantiating defn {defnId}"
    let _ ← defn.toFunctionDeclaration.instantiate
    defn.instantiate

def InstantiationM.run' (m : InstantiationM llvmctx α) (s : PureBuilderState) (instantiationCtx : InstantiationState llvmctx) : IO α :=
  ReaderT.run m s |>.run' instantiationCtx

def PureBuilderState.instantiate (s : PureBuilderState) (llvmmodule : LLVM.Module llvmctx) (llvmbuilder : LLVM.Builder llvmctx) (registerFile : HashMap LLVM.Pure.Reg (LLVM.Value llvmctx)) : IO Unit :=
  let instantiationState : LLVM.Pure.InstantiationState llvmctx := {
    llvmmodule := llvmmodule,
    llvmbuilder := llvmbuilder,
    registerFile := registerFile,
    basicBlocks := {}
    functions := {}
  }
  InstantiationM.run' instantiateToplevel s instantiationState

end Lean.IR.LLVM.Pure

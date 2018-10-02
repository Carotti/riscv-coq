Require Import Coq.ZArith.BinInt.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Minimal.

Section Riscv.

  Context {t: Set}.

  Context {MW: MachineWidth t}.

  Context {Mem: Set}.

  Context {MemIsMem: Memory Mem t}.

  Context {RF: Type}.
  Context {RFI: RegisterFile RF Register t}.

  Inductive LogEvent :=
  | EvLoadWord(addr: Z)(i: Instruction)
  | EvStoreWord(addr: Z)(v: word 32).

  Record RiscvMachineL{Log : Type} := mkRiscvMachineL {
    machine: @RiscvMachine t Mem RF;
    log: Log;
  }.

  Definition with_machine{Log: Type} m (ml : @RiscvMachineL Log) := mkRiscvMachineL Log m ml.(log).
  Definition with_log{Log: Type} (l : Log) (ml : @RiscvMachineL Log) := mkRiscvMachineL Log ml.(machine) l.

  Definition liftL0{B Log: Type}(f: OState RiscvMachine B):  OState RiscvMachineL B :=
    fun (s : @RiscvMachineL Log) => let (ob, ma) := f s.(machine) in (ob, with_machine ma s).

  Definition liftL1{A B Log: Type}(f: A -> OState RiscvMachine B): A -> OState RiscvMachineL B :=
    fun a (s : @RiscvMachineL Log) => let (ob, ma) := f a s.(machine) in (ob, with_machine ma s).

  Definition liftL2{A1 A2 B Log: Type}(f: A1 -> A2 -> OState RiscvMachine B):
    A1 -> A2 -> OState RiscvMachineL B :=
    fun a1 a2 (s : @RiscvMachineL Log) => let (ob, ma) := f a1 a2 s.(machine) in (ob, with_machine ma s).

  Definition RiscvMachineLMinimal := @RiscvMachineL (list LogEvent).

  Instance IsRiscvMachineLMinimal: RiscvProgram (OState RiscvMachineLMinimal) t :=  {|
      getRegister := liftL1 getRegister;
      setRegister := liftL2 setRegister;
      getPC := liftL0 getPC;
      setPC := liftL1 setPC;
      loadByte   := liftL1 loadByte;
      loadHalf   := liftL1 loadHalf;
      loadWord a :=
        m <- get;
        res <- (liftL1 loadWord a);
        put (with_log (m.(log) ++ [EvLoadWord (regToZ_unsigned a) (decode RV64IM (uwordToZ res))]) m);;
        Return res;
      loadDouble := liftL1 loadDouble;
      storeByte   := liftL2 storeByte;
      storeHalf   := liftL2 storeHalf;
      storeWord a v :=
        m <- get;
        put (with_log (m.(log) ++ [EvStoreWord (regToZ_unsigned a) v]) m);;
        liftL2 storeWord a v;
      storeDouble := liftL2 storeDouble;
      step := liftL0 step;
      getCSRField_MTVecBase := liftL0 getCSRField_MTVecBase;
      endCycle A := Return None;
  |}.

  Definition putProgram{Log: Type}(prog: list (word 32))(addr: t)(ma: (@RiscvMachineL Log)): (@RiscvMachineL Log) :=
    with_machine (putProgram prog addr ma.(machine)) ma.

End Riscv.

Existing Instance IsRiscvMachineLMinimal. (* needed because it was defined inside a Section *)

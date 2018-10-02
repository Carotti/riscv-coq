Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Nat.
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

  Record RiscvMachineLog{Log : Type} := mkRiscvMachineLog {
    machine: @RiscvMachine t Mem RF;
    log: Log;
  }.

  Definition with_machine{Log: Type} m (ml : @RiscvMachineLog Log) := mkRiscvMachineLog Log m ml.(log).
  Definition with_log{Log: Type} (l : Log) (ml : @RiscvMachineLog Log) := mkRiscvMachineLog Log ml.(machine) l.

  Definition putProgram{Log : Type}(prog: list (word 32))(addr: t)(ma: @RiscvMachineLog Log): @RiscvMachineLog Log :=
    with_machine (putProgram prog addr ma.(machine)) ma.

  Definition liftL0{B Log: Type}(f: OState RiscvMachine B):  OState RiscvMachineLog B :=
    fun (s : @RiscvMachineLog Log) => let (ob, ma) := f s.(machine) in (ob, with_machine ma s).

  Definition liftL1{A B Log: Type}(f: A -> OState RiscvMachine B): A -> OState RiscvMachineLog B :=
    fun a (s : @RiscvMachineLog Log) => let (ob, ma) := f a s.(machine) in (ob, with_machine ma s).

  Definition liftL2{A1 A2 B Log: Type}(f: A1 -> A2 -> OState RiscvMachine B):
    A1 -> A2 -> OState RiscvMachineLog B :=
    fun a1 a2 (s : @RiscvMachineLog Log) => let (ob, ma) := f a1 a2 s.(machine) in (ob, with_machine ma s).

  Inductive LogEventL :=
  | EvLoadWord(addr: Z)(i: Instruction)
  | EvStoreWord(addr: Z)(v: word 32).

  Definition RiscvMachineL := @RiscvMachineLog (list LogEventL).

  Instance IsRiscvMachineL: RiscvProgram (OState RiscvMachineL) t :=  {|
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

  Record MetricLog := mkMetricLog {
    instructions: nat;
    stores: nat;
    loads: nat; (* Note that this also includes loads of the PC *)
    jumps: nat;
  }.

  Definition EmptyMetricLog := mkMetricLog 0 0 0 0.

  Definition incMetricInstructions (l : MetricLog) : MetricLog :=
    mkMetricLog (S (instructions l)) (stores l) (loads l) (jumps l).

  Definition incMetricStores (l : MetricLog) : MetricLog :=
    mkMetricLog (instructions l) (S (stores l)) (loads l) (jumps l).

  Definition incMetricLoads (l : MetricLog) : MetricLog :=
    mkMetricLog (instructions l) (stores l) (S (loads l)) (jumps l).

  Definition incMetricJumps (l : MetricLog) : MetricLog :=
    mkMetricLog (instructions l) (stores l) (loads l) (S (jumps l)).

  Definition RiscvMachineMetricLog := @RiscvMachineLog MetricLog.

  Definition incLift0 operation incrementer: OState RiscvMachineMetricLog unit :=
    m <- get;
    put (with_log (incrementer m.(log)) m);;
    liftL0 operation.

  Definition incLift1{A r: Type} operation incrementer : A -> OState RiscvMachineMetricLog r :=
    fun x =>
      m <- get;
      put (with_log (incrementer m.(log)) m);;
      liftL1 operation x.

  Definition incLift2{A B r: Type} operation incrementer : A -> B -> OState RiscvMachineMetricLog r :=
    fun x y =>
      m <- get;
      put (with_log (incrementer m.(log)) m);;
      liftL2 operation x y.

  Instance IsRiscvMachineMetricLog: RiscvProgram (OState RiscvMachineMetricLog) t := {|
      getRegister := liftL1 getRegister;
      setRegister := liftL2 setRegister;
      getPC := liftL0 getPC;
      setPC := incLift1 setPC incMetricJumps;
      loadByte := incLift1 loadByte incMetricLoads;
      loadHalf := incLift1 loadHalf incMetricLoads;
      loadWord := incLift1 loadWord incMetricLoads;
      loadDouble := incLift1 loadDouble incMetricLoads;
      storeByte := incLift2 storeByte incMetricStores;
      storeHalf := incLift2 storeHalf incMetricStores;
      storeWord := incLift2 storeWord incMetricStores;
      storeDouble := incLift2 storeDouble incMetricStores;
      step := incLift0 step incMetricInstructions;
      getCSRField_MTVecBase := liftL0 getCSRField_MTVecBase;
      endCycle A := Return None;
  |}.

End Riscv.

(* needed because defined inside of a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance IsRiscvMachineMetricLog.

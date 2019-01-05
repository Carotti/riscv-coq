Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.BinIntDef.
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
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.

Section Riscv.

  Context {t: Set}.

  Context {MW: MachineWidth t}.

  Context {Mem: Set}.

  Context {MemIsMem: Memory Mem t}.

  Context {RF: Type}.
  Context {RFI: RegisterFile RF Register t}.

  Print RiscvMachine.
  Record RiscvMachineLog{Log : Type} := mkRiscvMachineLog {
    machine:> @RiscvMachine t Mem RF;
    log: Log;
  }.

  Definition with_machine{Log: Type} m (ml : @RiscvMachineLog Log) := mkRiscvMachineLog Log m ml.(log).
  Definition with_log{Log: Type} (l : Log) (ml : @RiscvMachineLog Log) := mkRiscvMachineLog Log ml.(machine) l.

  Definition putProgram{Log : Type}(prog: list (word 32))(addr: t)(ma: @RiscvMachineLog Log): @RiscvMachineLog Log :=
    with_machine (putProgram prog addr ma) ma.

  Definition with_registers_log{Log : Type} r (ma: @RiscvMachineLog Log) :=
    (@with_machine Log) (with_registers r ma) ma.
  Definition with_pc_log{Log : Type} p (ma: @RiscvMachineLog Log) :=
    (@with_machine Log) (with_pc p ma) ma.
  Definition with_nextPC_log{Log : Type} npc (ma: @RiscvMachineLog Log) :=
    (@with_machine Log) (with_nextPC npc ma) ma.
  Definition with_exceptionHandlerAddr_log{Log : Type} eh (ma: @RiscvMachineLog Log) :=
    (@with_machine Log) (with_exceptionHandlerAddr eh ma) ma.
  Definition with_machineMem_log{Log : Type} m (ma: @RiscvMachineLog Log) :=
    (@with_machine Log) (with_machineMem m ma) ma.

  Definition liftL0{B Log: Type}(f: OState RiscvMachine B):  OState RiscvMachineLog B :=
    fun (s : @RiscvMachineLog Log) => let (ob, ma) := f s in (ob, with_machine ma s).

  Definition liftL1{A B Log: Type}(f: A -> OState RiscvMachine B): A -> OState RiscvMachineLog B :=
    fun a (s : @RiscvMachineLog Log) => let (ob, ma) := f a s in (ob, with_machine ma s).

  Definition liftL2{A1 A2 B Log: Type}(f: A1 -> A2 -> OState RiscvMachine B):
    A1 -> A2 -> OState RiscvMachineLog B :=
    fun a1 a2 (s : @RiscvMachineLog Log) => let (ob, ma) := f a1 a2 s in (ob, with_machine ma s).

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
    instructions: Z;
    stores: Z;
    loads: Z; (* Note that this also includes loads of the PC *)
    jumps: Z;
  }.

  Definition EmptyMetricLog := mkMetricLog 0 0 0 0.

  Definition withInstructions i log := mkMetricLog i (stores log) (loads log) (jumps log).
  Definition withStores s log := mkMetricLog (instructions log) s (loads log) (jumps log).
  Definition withLoads l log := mkMetricLog (instructions log) (stores log) l (jumps log).
  Definition withJumps j log := mkMetricLog (instructions log) (stores log) (loads log) j.

  Definition addMetricInstructions n log := withInstructions (instructions log + n) log.
  Definition addMetricStores n log := withStores (stores log + n) log.
  Definition addMetricLoads n log := withLoads (loads log + n) log.
  Definition addMetricJumps n log := withJumps (jumps log + n) log.
  
  Definition subMetricInstructions n log := withInstructions (instructions log - n) log.
  Definition subMetricStores n log := withStores (stores log - n) log.
  Definition subMetricLoads n log := withLoads (loads log - n) log.
  Definition subMetricJumps n log := withJumps (jumps log - n) log.

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
      setPC := incLift1 setPC (addMetricJumps 1);
      loadByte := incLift1 loadByte (addMetricLoads 1);
      loadHalf := incLift1 loadHalf (addMetricLoads 1);
      loadWord := incLift1 loadWord (addMetricLoads 1);
      loadDouble := incLift1 loadDouble (addMetricLoads 1);
      storeByte := incLift2 storeByte (addMetricStores 1);
      storeHalf := incLift2 storeHalf (addMetricStores 1);
      storeWord := incLift2 storeWord (addMetricStores 1);
      storeDouble := incLift2 storeDouble (addMetricStores 1);
      step := incLift0 step (addMetricInstructions 1);
      getCSRField_MTVecBase := liftL0 getCSRField_MTVecBase;
      endCycle A := Return None;
  |}.

  End Riscv.

  Hint Unfold
       withInstructions
       withLoads
       withStores
       withJumps
       addMetricInstructions
       addMetricLoads
       addMetricStores
       addMetricJumps
       subMetricInstructions
       subMetricLoads
       subMetricStores
       subMetricJumps
  : unf_metric_log.
  
  Ltac unfold_MetricLog := autounfold with unf_metric_log in *.

  Ltac fold_MetricLog :=
    match goal with
    | _ : _ |- context[?x] =>
      match x with
      | {| instructions := instructions ?y;
           stores := stores ?y;
           loads := loads ?y;
           jumps := jumps ?y; |} => replace x with y by (destruct y; reflexivity)
      end
    end.

  Ltac simpl_MetricLog :=
    cbn [fst snd] in *; (* Unfold logs in tuples *)
    cbn [instructions loads stores jumps] in *.

  Ltac try_equality_MetricLog :=
    repeat match goal with
           | H : MetricLog |- context[{| instructions := ?i; |}] =>
             progress replace i with (instructions H) by omega
           | H : MetricLog |- context[{| stores := ?i; |}] =>
             progress replace i with (stores H) by omega      
           | H : MetricLog |- context[{| loads := ?i; |}] =>
             progress replace i with (loads H) by omega      
           | H : MetricLog |- context[{| jumps := ?i; |}] =>
             progress replace i with (jumps H) by omega
           end.

  Ltac solve_MetricLog :=
    repeat unfold_MetricLog;
    repeat simpl_MetricLog;
    try_equality_MetricLog;
    lia || fold_MetricLog.

(* needed because defined inside of a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance IsRiscvMachineMetricLog.

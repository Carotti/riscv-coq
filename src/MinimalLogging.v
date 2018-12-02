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
Require Import riscv.AxiomaticRiscv.

Section Riscv.

  Context {t: Set}.

  Context {MW: MachineWidth t}.

  Context {Mem: Set}.

  Context {MemIsMem: Memory Mem t}.

  Context {RF: Type}.
  Context {RFI: RegisterFile RF Register t}.

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

  Definition incMetricInstructions (l : MetricLog) : MetricLog :=
    mkMetricLog (1 + (instructions l)) (stores l) (loads l) (jumps l).

  Definition incMetricStores (l : MetricLog) : MetricLog :=
    mkMetricLog (instructions l) (1 + (stores l)) (loads l) (jumps l).

  Definition incMetricLoads (l : MetricLog) : MetricLog :=
    mkMetricLog (instructions l) (stores l) (1 + (loads l)) (jumps l).

  Definition incMetricJumps (l : MetricLog) : MetricLog :=
    mkMetricLog (instructions l) (stores l) (loads l) (1 + (jumps l)).

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
  
   Class AxiomaticRiscvLog :=  mkAxiomaticRiscvLog {
      
      Bind_getRegister0: forall {A: Type} (f: t -> OState RiscvMachineLog A),
        Bind (getRegister Register0) f = f (ZToReg 0);
      
      Bind_getRegister: forall {A: Type} x (f: t -> OState RiscvMachineLog A)
                          (initialL: RiscvMachineLog),
          valid_register x ->
          (Bind (getRegister x) f) initialL =
          (f (getReg initialL.(core).(registers) x)) initialL;

      Bind_setRegister: forall {A: Type} x (v: t)
                          (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          valid_register x ->
          (Bind (setRegister x v) f) initialL =
          (f tt) (with_registers (setReg initialL.(core).(registers) x v) initialL);

      Bind_setRegister0: forall {A: Type} (v: t)
                           (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (setRegister Register0 v) f) initialL =
          (f tt) initialL;

      Bind_loadByte: forall {A: Type} (addr: t) (f: word 8 -> OState RiscvMachine A)
                       (initialL: RiscvMachine),
          (Bind (loadByte addr) f) initialL =
          (f (Memory.loadByte initialL.(machineMem) addr)) initialL;

      Bind_loadHalf: forall {A: Type} (addr: t) (f: word 16 -> OState RiscvMachine A)
                       (initialL: RiscvMachine),
          (Bind (loadHalf addr) f) initialL =
          (f (Memory.loadHalf initialL.(machineMem) addr)) initialL;

      Bind_loadWord: forall {A: Type} (addr: t) (f: word 32 -> OState RiscvMachine A)
                       (initialL: RiscvMachine),
          (Bind (loadWord addr) f) initialL =
          (f (Memory.loadWord initialL.(machineMem) addr)) initialL;
      
      Bind_loadDouble: forall {A: Type} (addr: t) (f: word 64 -> OState RiscvMachine A)
                       (initialL: RiscvMachine),
          (Bind (loadDouble addr) f) initialL =
          (f (Memory.loadDouble initialL.(machineMem) addr)) initialL;

      Bind_storeByte: forall {A: Type} (addr: t) (v: word 8)
                        (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (storeByte addr v) f) initialL =
          (f tt) (with_machineMem (Memory.storeByte initialL.(machineMem) addr v)
                                            initialL);

      Bind_storeHalf: forall {A: Type} (addr: t) (v: word 16)
                        (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (storeHalf addr v) f) initialL =
          (f tt) (with_machineMem (Memory.storeHalf initialL.(machineMem) addr v)
                                            initialL);

      Bind_storeWord: forall {A: Type} (addr: t) (v: word 32)
                        (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (storeWord addr v) f) initialL =
          (f tt) (with_machineMem (Memory.storeWord initialL.(machineMem) addr v)
                                            initialL);

      Bind_storeDouble: forall {A: Type} (addr: t) (v: word 64)
                        (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (storeDouble addr v) f) initialL =
          (f tt) (with_machineMem (Memory.storeDouble initialL.(machineMem) addr v)
                                            initialL);

      Bind_getPC: forall {A: Type} (f: t -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind getPC f) initialL =
          (f initialL.(core).(pc)) initialL;

      Bind_setPC: forall {A: Type} (v: t)
                    (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (setPC v) f) initialL =
          (f tt) (with_nextPC v initialL);
      
      Bind_step: forall {A: Type} (f: unit -> OState RiscvMachine A) m,
          (Bind step f) m =
          (f tt) (with_nextPC (add m.(core).(nextPC) (ZToReg 4)) (with_pc m.(core).(nextPC) m));

      execState_step: forall m,
          step m = (Some tt, with_nextPC_log (add m.(core).(nextPC) (ZToReg 4)) (with_pc_log m.(core).(nextPC) m));
      
      execState_Return: forall {S A} (s: S) (a: A),
          (Return a) s = (Some a, s);

  }.

End Riscv.

(* needed because defined inside of a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance IsRiscvMachineMetricLog.

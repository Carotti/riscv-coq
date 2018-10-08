Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.util.BitWidth32.
Require Import bbv.HexNotationZ.
Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.
Require Import riscv.Memory.
Require Import riscv.Minimal.
Require Import riscv.MinimalLogging.
Require Import riscv.Run.
Require Import riscv.ListMemory.
Require Import riscv.util.Monads.
Require Import riscv.MachineWidth32.

Existing Instance DefaultRiscvState.

Instance FunctionRegisterFile: RegisterFile (Register -> word 32) Register (word 32) := {|
  getReg(rf: Register -> word 32) := rf;
  setReg(rf: Register -> word 32)(r: Register)(v: word 32) :=
    fun r' => if (Z.eqb r' r) then v else rf r';
  initialRegs := fun r => ZToReg 0;
|}.

Definition fib6_riscv: list MachineInt := [ (* TODO should be "word 32", not MachineInt *)
  Ox"00600993";         (* li s3,6 *)
  Ox"00000a13";         (* li s4,0 *)
  Ox"00100913";         (* li s2,1 *)
  Ox"00000493";         (* li s1,0 *)
  Ox"0140006f";         (* j 101e0 <main+0x44> *)
  Ox"012a0ab3";         (* add s5,s4,s2 *)
  Ox"00090a13";         (* mv s4,s2 *)
  Ox"000a8913";         (* mv s2,s5 *)
  Ox"00148493";         (* addi s1,s1,1 *)
  Ox"ff34c8e3"          (* blt s1,s3,101d0 <main+0x34> *)
].

(*
Notation x0 := (WO~0~0~0~0~0)%word.
Notation s1 := (WO~0~1~0~0~1)%word.
Notation s2 := (WO~1~0~0~1~0)%word.
Notation s3 := (WO~1~0~0~1~1)%word.
Notation s4 := (WO~1~0~1~0~0)%word.
Notation s5 := (WO~1~0~1~0~1)%word.
*)

Open Scope Z_scope.

Goal False.
  set (l := map (decode RV32IM) fib6_riscv).
  cbv in l.
  (* decoder seems to work :) *)
Abort.

Definition RiscvMachine := @RiscvMachine (word 32) mem (Register -> word 32).

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachineCore: RiscvMachineCore := {|
  registers := initialRegs;
  pc := ZToReg 0;
  nextPC := ZToReg 4;
  exceptionHandlerAddr := 3;
|}.

Definition zeroedRiscvMachine: RiscvMachine := {|
    core := zeroedRiscvMachineCore;
    machineMem := zero_mem 100;
|}.

(* Load Store logging of fib example *)

Definition zeroedRiscvMachineL: RiscvMachineL := {|
    machine := zeroedRiscvMachine;
    log := nil;
|}.

Definition initialRiscvMachineL(imem: list MachineInt): RiscvMachineL:= 
  putProgram (map (@ZToWord 32) imem) (ZToReg 0) zeroedRiscvMachineL.

Definition runL: nat -> RiscvMachineL -> (option unit) * RiscvMachineL := run.
 (* @run BitWidths32 MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _ _ *)

Definition fib6_L_final(fuel: nat): RiscvMachineL :=
  match runL fuel (initialRiscvMachineL fib6_riscv) with
  | (answer, state) => state
  end.

Definition fib6_L_res(fuel: nat): word XLEN :=
  (fib6_L_final fuel).(machine).(core).(registers) 18.

Definition fib6_L_trace(fuel: nat) :=
  (fib6_L_final fuel).(log).

(* only uncomment this if you're sure there are no admits in the computational parts,
   otherwise this will eat all your memory *)

Eval cbv in (fib6_L_trace 50).

Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = ZToReg 13.
  exists 50%nat.
  reflexivity.
Qed.

(* Opcode logging of fib example *)

Definition zeroedRiscvMachineMetric: RiscvMachineLog := {|
    machine := zeroedRiscvMachine;
    log := EmptyMetricLog;
|}.

Definition runMetric: nat -> RiscvMachineMetricLog -> (option unit) * RiscvMachineMetricLog := run.
 (* @run BitWidths32 MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _ _ *)

Definition initialRiscvMachineMetricLog(imem: list MachineInt): RiscvMachineMetricLog:= 
  putProgram (map (@ZToWord 32) imem) (ZToReg 0) zeroedRiscvMachineMetric.

Definition fib6_metric_final(fuel: nat): RiscvMachineMetricLog :=
  match runMetric fuel (initialRiscvMachineMetricLog fib6_riscv) with
  | (answer, state) => state
  end.

Definition fib6_metric_res(fuel: nat): word XLEN :=
  (fib6_metric_final fuel).(machine).(core).(registers) 18.

Definition fib6_metric_trace(fuel: nat) :=
  (fib6_metric_final fuel).(log).

Eval cbv in (fib6_metric_trace 50).

Lemma fib6_metric_res_is_13_by_running_it: exists fuel, fib6_metric_res fuel = ZToReg 13.
  exists 50%nat.
  reflexivity.
Qed.

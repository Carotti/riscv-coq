Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Export riscv.Platform.RiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.

  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Definition fail_if_None{R}(o: option R): OState RiscvMachine R :=
    match o with
    | Some x => Return x
    | None => fail_hard
    end.

  Definition loadN(n: nat)(kind: SourceType)(a: word): OState RiscvMachine (HList.tuple byte n) :=
    mach <- get;
    v <- fail_if_None (Memory.load_bytes n mach.(getMem) a);
    match kind with
    | Fetch => if isXAddrB a mach.(getXAddrs) then Return v else fail_hard
    | _ => Return v
    end.

  Definition storeN(n: nat)(kind: SourceType)(a: word)(v: HList.tuple byte n) :=
    mach <- get;
    m <- fail_if_None (Memory.store_bytes n mach.(getMem) a v);
    put (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) (withMem m mach)).

  Instance IsRiscvMachine: RiscvProgram (OState RiscvMachine) word :=  {
      getRegister reg :=
        if Z.eq_dec reg Register0 then
          Return (ZToReg 0)
        else
          if (0 <? reg) && (reg <? 32) then
            mach <- get;
            match map.get mach.(getRegs) reg with
            | Some v => Return v
            | None => Return (word.of_Z 0)
            end
          else
            fail_hard;

      setRegister reg v :=
        if Z.eq_dec reg Register0 then
          Return tt
        else
          if (0 <? reg) && (reg <? 32) then
            mach <- get;
            let newRegs := map.put mach.(getRegs) reg v in
            put (withRegs newRegs mach)
          else
            fail_hard;

      getPC := mach <- get; Return mach.(getPc);

      setPC newPC :=
        mach <- get;
        put (withNextPc newPC mach);

      loadByte   := loadN 1;
      loadHalf   := loadN 2;
      loadWord   := loadN 4;
      loadDouble := loadN 8;

      storeByte   := storeN 1;
      storeHalf   := storeN 2;
      storeWord   := storeN 4;
      storeDouble := storeN 8;

      step :=
        m <- get;
        let m' := withPc m.(getNextPc) m in
        let m'' := withNextPc (add m.(getNextPc) (ZToReg 4)) m' in
        put m'';

      (* fail hard if exception is thrown because at the moment, we want to prove that
         code output by the compiler never throws exceptions *)
      raiseExceptionWithInfo{A: Type} _ _ _ := fail_hard;
  }.

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.

  Lemma VirtualMemoryFetchP: forall addr xAddrs,
      VirtualMemory = Fetch -> isXAddr addr xAddrs.
  Proof. intros. discriminate. Qed.

  Lemma ExecuteFetchP: forall addr xAddrs,
      Execute = Fetch -> isXAddr addr xAddrs.
  Proof. intros. discriminate. Qed.

  Ltac t :=
    repeat match goal with
       | |- _ => reflexivity
       | |- _ => progress (
                     unfold computation_satisfies, computation_with_answer_satisfies,
                            IsRiscvMachine,
                            valid_register, Register0,
                            is_initial_register_value,
                            get, put, fail_hard,
                            Memory.loadByte, Memory.storeByte,
                            Memory.loadHalf, Memory.storeHalf,
                            Memory.loadWord, Memory.storeWord,
                            Memory.loadDouble, Memory.storeDouble,
                            fail_if_None, loadN, storeN in *;
                     subst;
                     simpl in *)
       | |- _ => intro
       | |- _ => split
       | |- _ => apply functional_extensionality
       | |- _ => apply propositional_extensionality; split; intros
       | u: unit |- _ => destruct u
       | H: exists x, _ |- _ => destruct H
       | H: {_ : _ | _} |- _ => destruct H
       | H: _ /\ _ |- _ => destruct H
       | p: _ * _ |- _ => destruct p
       | |- context [ let (_, _) := ?p in _ ] => let E := fresh "E" in destruct p eqn: E
       | H: Some _ = Some _ |- _ => inversion H; clear H; subst
       | H: (_, _) = (_, _) |- _ => inversion H; clear H; subst
       | H: _ && _ = true |- _ => apply andb_prop in H
       | H: _ && _ = false |- _ => apply Bool.andb_false_iff in H
       | H: isXAddrB _ _ = false |- _ => apply isXAddrB_not in H
       | H: isXAddrB _ _ = true  |- _ => apply isXAddrB_holds in H
       | H: ?x = ?x -> _ |- _ => specialize (H eq_refl)
       | |- _ * _ => constructor
       | |- option _ => exact None
       | |- _ => discriminate
       | |- _ => congruence
       | |- _ => solve [exfalso; bomega]
       | |- _ => solve [eauto 15 using VirtualMemoryFetchP, ExecuteFetchP]
       | |- _ => progress (rewrite? Z.ltb_nlt in *; rewrite? Z.ltb_lt in *)
       | |- _ => bomega
       | H: context[let (_, _) := ?y in _] |- _ => let E := fresh "E" in destruct y eqn: E
       | E: ?x = Some _, H: context[match ?x with _ => _ end] |- _ => rewrite E in H
       | E: ?x = Some _  |- context[match ?x with _ => _ end]      => rewrite E
       | H: context[match ?x with _ => _ end] |- _ => let E := fresh "E" in destruct x eqn: E
       | |- context[match ?x with _ => _ end]      => let E := fresh "E" in destruct x eqn: E
       | H: _ \/ _ |- _ => destruct H
       | r: RiscvMachine |- _ =>
         destruct r as [regs pc npc m l];
         simpl in *
(*       | H: context[match ?x with _ => _ end] |- _ => let E := fresh in destruct x eqn: E*)
       | o: option _ |- _ => destruct o
       (* introduce evars as late as possible (after all destructs), to make sure everything
          is in their scope*)
       | |- exists (P: ?A -> ?S -> Prop), _ =>
            let a := fresh "a" in evar (a: A);
            let s := fresh "s" in evar (s: S);
            exists (fun a0 s0 => a0 = a /\ s0 = s);
            subst a s
       | |- _ \/ _ => left; solve [t]
       | |- _ \/ _ => right; solve [t]
       end.

  Instance MinimalPrimitivesParams: PrimitivesParams (OState RiscvMachine) RiscvMachine := {
    Primitives.mcomp_sat := @OStateOperations.computation_with_answer_satisfies RiscvMachine;
    Primitives.is_initial_register_value := eq (word.of_Z 0);
    Primitives.nonmem_load n kind addr := fail_hard;
    Primitives.nonmem_store n kind addr v := fail_hard;
  }.

  Instance MinimalSatisfiesPrimitives: Primitives MinimalPrimitivesParams.
  Proof.
    constructor.
    all: try t.
  Qed.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsRiscvMachine.
Existing Instance MinimalSatisfiesPrimitives.

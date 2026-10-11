(*
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

From Stdlib Require Import List Lia Bool Nat NArith.
Set Primitive Projections.
From cheriot Require Import Utils.

Class ISA_params := {
    ISA_LG_CAPSIZE_BYTES : nat;
    ISA_CAPSIZE_BYTES := Nat.pow 2 ISA_LG_CAPSIZE_BYTES;
    ISA_NREGS: nat
  }.

(* Represents basic permissions *)
Module Perm.
  Inductive t :=
  | Exec
  | System
  | Load
  | Store
  | Cap
  | Sealing
  | Unsealing.
  Scheme Equality for t.
End Perm.

Class MachineTypeParams := {
    Byte : Type;
    Key : Type
}.

(** * The abstract machine

    Everything from here to the end of the section is parametric in the instruction-set
    parameters [ISA_params] (the capability size and the register count), the machine type
    parameters [MachineTypeParams] (the types of bytes and of sealing keys) and, from
    [CapEncodeDecode] on, the encoding of capabilities as bytes.  The section defines, in order,
    addresses and capabilities, memory with its tags, the operations on capabilities and the
    reachability relations over a memory, the machine state, the well-formedness conditions on
    instructions, and the step relation over machines and traces.  The CHERIoT ISA is the design
    modeled; where a definition encodes one of its mechanisms, the comment says which. *)
Section Machine.

  (** Both parameter classes are section context: the definitions below that use them take them
      as implicit arguments. *)
  Context [ISA: ISA_params].
  Context {machineTypeParams: MachineTypeParams}.

  (** A memory address.  Addresses are natural numbers with no upper bound; the model fixes no
      word size. *)
  Definition Addr := nat.

  (** The index of a capability slot: an address with its low [ISA_LG_CAPSIZE_BYTES] bits
      dropped, so that one slot holds one capability of [ISA_CAPSIZE_BYTES] bytes.  Tags are kept
      per slot. *)
  Definition CapAddr := nat.

  (** The slot an address falls in. *)
  Definition toCapAddr (a: Addr): CapAddr := Nat.shiftr a ISA_LG_CAPSIZE_BYTES.

  (** The first address of a slot. *)
  Definition fromCapAddr (a: CapAddr): Addr := Nat.shiftl a ISA_LG_CAPSIZE_BYTES.

  (* A cap X can be stored in a cap Y only if X can be stored in a Label that Y provides *)
  (* An example where restricting the label of what can be stored in a cap is useful:
   If a callee fills a cap supplied by the caller, then the callee should not store a cap to its stack into it.
   In CHERIoT, a pointer to its stack is always !GL and can only be stored in SL.
   So to prevent the pointer to the callee's stack from getting stored, the cap supplied by the caller should be !SL
   eventhough the underlying pointer is really in the stack.
   *)

  (** The two store labels.  A capability carries the labels it may store ([capCanStore]) and the
      labels under which it may itself be stored ([capCanBeStored]); among its other conditions,
      [ValidMemCapUpdate] admits a stored capability only where a label of the authorizing
      capability's [capCanStore] is among the stored capability's [capCanBeStored].  In CHERIoT,
      [Local] is the label of a capability without the global bit, which may be stored only
      through a capability with the store-local permission, and [NonLocal] is the label of a
      global one, which may be stored wherever capabilities may be stored. *)
  Inductive Label :=
  | Local
  | NonLocal.
  Scheme Equality for Label.

  (* Represents Call and Return sentries *)

  (** The sentry kinds of the CHERIoT ISA.  A sentry is a sealed code capability: it can be
      jumped to, and its holder can neither unseal it nor use it as a data capability; the only
      change the reachability relation admits to a sealed capability is a narrowing of where it
      may be stored ([RestrictSealed]).  A forward sentry is the target of a call and fixes what
      the call does to the interrupt status: enable, disable, or inherit it ([WfCallSentryInst]).
      A backward sentry is the target of a return and enables or disables interrupts
      ([WfRetSentryInst]). *)
  Inductive Sentry :=
  | CallEnableInterrupt
  | CallDisableInterrupt
  | CallInheritInterrupt
  | RetEnableInterrupt
  | RetDisableInterrupt.

  (** What a sealed capability is sealed with: a sentry kind, for code capabilities, or a key,
      for sealed data capabilities.  Keys are a [MachineTypeParams] parameter. *)
  Definition SealT := (Sentry + Key)%type. (* A sealed cap is either a sentry or a data cap sealed with a key *)

  (** The abstract capability.  Besides its sealing state, permissions and store labels, it
      carries explicitly what the CHERIoT encoding derives: the sealing and unsealing keys it
      holds (as lists of keys rather than an object-type range), its bounds as a list of
      addresses rather than a base and a length, and the permissions and labels that a capability
      loaded through it keeps ([capKeepPerms], [capKeepCanStore], [capKeepCanBeStored], applied
      by [attenuate]).  The last three model the ISA's load-side attenuation, by which a load
      through a capability lacking the load-mutable permission strips the loaded capability's
      store permissions, and one lacking the load-global permission strips its global bit.

      With bounds a list, any finite set of addresses is representable; the constraints the
      encoding imposes are left to [CapEncodeDecode] and to the validation module at the end of
      the file.  The cursor may lie outside the bounds, as the field's comment explains. *)
  Record Cap := {
      capSealed: option SealT;
      capPerms: list Perm.t;
      capCanStore: list Label; (* The labels of caps that this cap can store (SL in CHERIoT) *)
      capCanBeStored: list Label; (* The labels of caps where this cap can be stored in (GL and not GL in CHERIoT) *)
      capSealingKeys: list Key; (* List of sealing keys owned by this cap *)
      capUnsealingKeys: list Key; (* List of unsealing keys owned by this cap *)
      capAddrs: list Addr; (* List of addresses representing this cap's bounds *)
      capKeepPerms: list Perm.t; (* Permissions to be the only ones kept when loading using this cap *)
      capKeepCanStore: list Label; (* Labels-of-caps-that-this-cap-can-store to be the only ones kept
                                      when loading using this cap *)
      capKeepCanBeStored: list Label; (* Labels-of-caps-where-this-cap-can-be-stored to be the only ones kept
                                         when loading using this cap *)
      capCursor: Addr (* The current address of a cap.
                         These cursors can be out of bounds w.r.t. capAddrs.
                         In CHERI these out of bounds cursors are allowed as part of representable region.
                         In the formal model, any address is representable.
                         Notice that when sealing a capability, the cursor is not checked to be inbounds.
                         This mean one has to explicitly check if the sentry capabilities are in-bounds.
                         This creates a problem for return sentries, as they need not be in-bounds;
                         the error has to be handled by the caller compartment on return. *)
    }.

  (** ** Memory

      Memory as a total function from addresses to bytes. *)
  Definition Memory_t := Addr -> Byte.

  (** The tags, one per capability slot, meant to be set exactly when the slot holds a
      capability.  The model does not enforce that reading: a byte write leaves the tag as it was
      ([writeCapOrBytes]), and clearing a tag is a separate kind of update
      ([ValidMemTagRemoval]). *)
  Definition Tag_t := CapAddr -> bool.

  (** Memory and tags together; every operation that may read or write a capability takes both. *)
  Definition FullMemory := (Memory_t * Tag_t)%type.

  (** A byte string. *)
  Definition Bytes := list Byte.

  (** A value as read from memory: a capability, when the tag is set and a whole slot was read,
      or raw bytes. *)
  Definition CapOrBytes := (Cap + Bytes)%type.

  (** The encoding interface: a decoder from bytes to a capability, used only under a set tag and
      a whole slot's bytes ([bytesToCap]); an encoder from a capability to bytes; and decidable
      equality on capabilities and on read values, for the proofs.  No law relating the encoder
      and the decoder is assumed here. *)
  Class CapEncodeDecode := {
    bytesToCapUnsafe: Bytes -> Cap;
    capToBytes: Cap -> Bytes;
    Cap_eqb: Cap -> Cap -> bool;
    Cap_eq_dec: EqDecider Cap_eqb;
    CapOrBytes_eqb: CapOrBytes -> CapOrBytes -> bool;
    CapOrBytes_eq_dec: EqDecider CapOrBytes_eqb
  }.

  (** The encoding is section context from here on. *)
  Context {capEncodeDecode: CapEncodeDecode}.

  (** Decode under the tag: a capability only if the tag is set and exactly one slot's worth of
      bytes was read; otherwise the bytes themselves. *)
  Definition bytesToCap (tag: bool) (bytes: Bytes): CapOrBytes :=
    if tag && (length bytes =? ISA_CAPSIZE_BYTES)
    then inl (bytesToCapUnsafe bytes)
    else inr bytes.

  (** The [sz] bytes from address [a] upward. *)
  Definition readMemBytes (mem: Memory_t) (a: Addr) (sz: nat) : Bytes :=
    map mem (seq a sz).

  (** Read capability slot [capa]: its tag and its bytes, through [bytesToCap]. *)
  Definition readMemTagCap (mem: Memory_t) (tags: Tag_t) (capa: CapAddr) : CapOrBytes :=
    bytesToCap (tags capa) (readMemBytes mem (fromCapAddr capa) ISA_CAPSIZE_BYTES).

  (** Memory with one byte replaced. *)
  Definition writeMemByte (mem: Memory_t) (a: Addr) (byte: Byte) : Memory_t :=
    fun i => if i =? a
             then byte
             else mem i.

  (** Memory with the bytes written consecutively from [a]. *)
  Definition writeMemBytes (mem: Memory_t) (a: Addr) (bytes: Bytes): Memory_t :=
    fst (fold_left (fun '(mem', a') byte => (writeMemByte mem' a' byte, S a')) bytes (mem, a)).

  (** Tags with one slot's tag set to [t]. *)
  Definition writeTagTag (tags: Tag_t) (capa: CapAddr) (t: bool) : Tag_t := (fun i => if i =? capa
                                                                                      then t
                                                                                      else tags i).

  (** Store a capability at slot [capa]: its encoding ([capToBytes]) written from the slot's
      first address, and the slot's tag set.  Nothing in [CapEncodeDecode] fixes the encoding's
      length to one slot; that the bytes stay within the slot is the encoding's business, not
      this definition's. *)
  Definition writeMemTagCap (mem: Memory_t) (tags: Tag_t) (capa: CapAddr) (c: Cap) : FullMemory :=
    let a := fromCapAddr capa in
    (writeMemBytes mem a (capToBytes c), writeTagTag tags capa true).

  (** The same operations on a [FullMemory], memory and tags together. *)

  (** The byte at an address. *)
  Definition readByte (mem: FullMemory) := fst mem.

  (** [readMemBytes] on the memory half. *)
  Definition readBytes (mem: FullMemory) := readMemBytes (fst mem).

  (** A slot's tag. *)
  Definition readTag (mem: FullMemory) := snd mem.

  (** A slot's capability, or its bytes when the tag is clear. *)
  Definition readCap (mem: FullMemory) := readMemTagCap (fst mem) (snd mem).

  (** [writeMemByte] on the memory half; the result is the memory alone. *)
  Definition writeByte (mem: FullMemory) := writeMemByte (fst mem).

  (** [writeMemBytes] on the memory half; the result is the memory alone. *)
  Definition writeBytes (mem: FullMemory) := writeMemBytes (fst mem).

  (** [writeTagTag] on the tag half; the result is the tags alone. *)
  Definition writeTag (mem: FullMemory) := writeTagTag (snd mem).

  (** [writeMemTagCap] on both halves. *)
  Definition writeCap (mem: FullMemory) := writeMemTagCap (fst mem) (snd mem).

  (** Write a read value back at [a]: a capability is written from the first address of the slot
      [a] falls in, with that slot's tag set; bytes go into memory with the tags left as they
      are. *)
  Definition writeCapOrBytes (mem: FullMemory) (a: Addr) (v: CapOrBytes) : FullMemory :=
    match v with
    | inl cap => writeCap mem (toCapAddr a) cap
    | inr bytes => (writeBytes mem a bytes, snd mem)
    end.    

  (** The payload an instruction returns when it raises an exception: bytes, not interpreted by
      the model.  [EXNInfo], later in the section, is the same type under the name the thread
      state uses. *)
  Definition ExnInfo := Bytes.

  (** Operations on a single capability: changing its seal, cursor and bounds; the sentry,
      sealed-data and sealed predicates; and the load-side attenuation that [capKeepPerms],
      [capKeepCanStore] and [capKeepCanBeStored] prescribe. *)
  Section CapHelpers.
    Definition setCapSealed (c: Cap) (seal: option SealT) : Cap :=
      {| capSealed := seal;
         capPerms := c.(capPerms);
         capCanStore := c.(capCanStore);
         capCanBeStored := c.(capCanBeStored);
         capSealingKeys := c.(capSealingKeys);
         capUnsealingKeys := c.(capUnsealingKeys);
         capAddrs := c.(capAddrs);
         capKeepPerms := c.(capKeepPerms);
         capKeepCanStore := c.(capKeepCanStore);
         capKeepCanBeStored := c.(capKeepCanBeStored);
         capCursor := c.(capCursor)
      |}.
    Definition setCapCursor (c: Cap) (cursor: Addr) : Cap :=
      {| capSealed := c.(capSealed);
         capPerms := c.(capPerms);
         capCanStore := c.(capCanStore);
         capCanBeStored := c.(capCanBeStored);
         capSealingKeys := c.(capSealingKeys);
         capUnsealingKeys := c.(capUnsealingKeys);
         capAddrs := c.(capAddrs);
         capKeepPerms := c.(capKeepPerms);
         capKeepCanStore := c.(capKeepCanStore);
         capKeepCanBeStored := c.(capKeepCanBeStored);
         capCursor := cursor
      |}.
    Definition updateCapAddrs (c: Cap) (update: list Addr -> list Addr) : Cap :=
      {| capSealed := c.(capSealed);
         capPerms := c.(capPerms);
         capCanStore := c.(capCanStore);
         capCanBeStored := c.(capCanBeStored);
         capSealingKeys := c.(capSealingKeys);
         capUnsealingKeys := c.(capUnsealingKeys);
         capAddrs := update c.(capAddrs);
         capKeepPerms := c.(capKeepPerms);
         capKeepCanStore := c.(capKeepCanStore);
         capKeepCanBeStored := c.(capKeepCanBeStored);
         capCursor := c.(capCursor) 
      |}.


    Definition updateCapCursor (c: Cap) (fn: Addr -> Addr) : Cap :=
      setCapCursor c (fn c.(capCursor)).


    Definition isSentry (c: Cap) :=
      match c.(capSealed) with
      | Some (inl _) => true
      | _ => false
      end.

    Definition isForwardSentry (c: Cap) :=
      match c.(capSealed) with
      | Some (inl CallEnableInterrupt) => true 
      | Some (inl CallDisableInterrupt) => true
      | Some (inl CallInheritInterrupt) => true
      | _ => false
      end.


    Definition isSealedDataCap (c: Cap) :=
      match c.(capSealed) with
      | Some (inr _) => true
      | _ => false
      end.

    Definition isSealed (c: Cap) :=
      match c.(capSealed) with
      | Some _ => true
      | _ => false
      end.

    Abbreviation PermIntersect perms1 perms2 := (filter (fun p => existsb (Perm.t_beq p) perms2) perms1).
    Abbreviation LabelIntersect labels1 labels2 := (filter (fun p => existsb (Label_beq p) labels2) labels1).

    Definition AttenuatePermsIfNotSealed (sealed: bool) (perms1 perms2: list Perm.t) :=
      if sealed then perms2
      else PermIntersect perms1 perms2.

    Definition AttenuateLabelsIfNotSealed (sealed: bool) (labels1 labels2: list Label) :=
      if sealed then labels2
      else LabelIntersect labels1 labels2.

    Definition attenuate (loadAuthCap: Cap) (loaded: Cap) : Cap :=
      let sealed := isSealed loaded in
      {| capSealed          := loaded.(capSealed);
         capPerms           := AttenuatePermsIfNotSealed  sealed loadAuthCap.(capKeepPerms) loaded.(capPerms);
         capCanStore        := AttenuateLabelsIfNotSealed sealed loadAuthCap.(capKeepCanStore) loaded.(capCanStore);
         (* This is also a quirk of CHERIoT as in the case of restricting caps.
            Ideally, no attenuation (implicit or explicit) must happen under a seal.
          *)
         capCanBeStored     := LabelIntersect loadAuthCap.(capKeepCanBeStored) loaded.(capCanBeStored);
         capSealingKeys     := loaded.(capSealingKeys);
         capUnsealingKeys   := loaded.(capUnsealingKeys);
         capAddrs           := loaded.(capAddrs);
         capKeepPerms       := AttenuatePermsIfNotSealed  sealed loadAuthCap.(capKeepPerms) loaded.(capKeepPerms);
         capKeepCanStore    := AttenuateLabelsIfNotSealed sealed loadAuthCap.(capKeepCanStore) loaded.(capKeepCanStore);
         capKeepCanBeStored := AttenuateLabelsIfNotSealed sealed loadAuthCap.(capKeepCanBeStored) loaded.(capKeepCanBeStored);
         capCursor          := loaded.(capCursor)
      |}.

  End CapHelpers.

  Section CurrMemory.
    Variable mem: FullMemory.

    Section CapStep.
      Variable x: Cap.
      Variable y z: Cap.

      Definition SealEq := z.(capSealed) = y.(capSealed).

      (* NB: capCursor can change arbitrarily for unsealed caps. *)
      Record RestrictUnsealed : Prop := {
          restrictUnsealedEqs: SealEq;
          restrictUnsealedPermsSubset: Subset z.(capPerms) y.(capPerms);
          restrictUnsealedCanStoreSubset: Subset z.(capCanStore) y.(capCanStore);
          restrictUnsealedCanBeStoredSubset: Subset z.(capCanBeStored) y.(capCanBeStored);
          restrictUnsealedSealingKeysSubset: Subset z.(capSealingKeys) y.(capSealingKeys);
          restrictUnsealedUnsealingKeysSubset: Subset z.(capUnsealingKeys) y.(capUnsealingKeys);
          restrictUnsealedAddrsSubset: Subset z.(capAddrs) y.(capAddrs);
          restrictUnsealedKeepPermsSubset: Subset z.(capKeepPerms) y.(capKeepPerms);
          restrictUnsealedKeepCanStoreSubset: Subset z.(capKeepCanStore) y.(capKeepCanStore);
          restrictUnsealedKeepCanBeStoredSubset: Subset z.(capKeepCanBeStored) y.(capKeepCanBeStored) }.

      Record RestrictSealed : Prop := {
          restrictSealedEqs: SealEq;
          restrictSealedPermsEq: EqSet z.(capPerms) y.(capPerms);
          restrictSealedCanStore: EqSet z.(capCanStore) y.(capCanStore);
          (* The following seems to be a quirk of CHERIoT,
           maybe make it equal in CHERIoT ISA if there's no use case for this behavior
           and merge with RestrictUnsealed?
           Here's a concrete example why this is bad:
             I have objects in Global and a set of pointers to these objects also in Global.
             I seal an element of that set (which points to an object) and send to a client.
             Client gets a Global sealed cap, makes it Stack and sends it back to me after finishing processing.
             I unseal it, but I lost my ability to store it back into that set in Global.
             Instead, I need to rederive the Global for the unsealed cap to be able to store into the Global set.
           *)
          restrictSealedCanBeStoredSubset: Subset z.(capCanBeStored) y.(capCanBeStored);
          restrictSealedSealingKeysEq: EqSet z.(capSealingKeys) y.(capSealingKeys);
          restrictSealedUnsealingKeysSubset: EqSet z.(capUnsealingKeys) y.(capUnsealingKeys);
          restrictSealedAddrsEq: EqSet z.(capAddrs) y.(capAddrs);
          restrictSealedKeepPermsSubset: EqSet z.(capKeepPerms) y.(capKeepPerms);
          restrictSealedKeepCanStoreSubset: EqSet z.(capKeepCanStore) y.(capKeepCanStore);
          restrictSealedKeepCanBeStoredSubset: EqSet z.(capKeepCanBeStored) y.(capKeepCanBeStored);
          restrictSealedCursorEq: z.(capCursor) = y.(capCursor) }.

      Definition Restrict : Prop :=
        match y.(capSealed) with
        | None => RestrictUnsealed
        | _ => RestrictSealed
        end.

      Record LoadCap : Prop :=
        { loadAuthUnsealed : x.(capSealed) = None;
          loadAuthPerm: In Perm.Load x.(capPerms) /\ In Perm.Cap x.(capPerms);
          loadFromAuth: exists capa, Subset (seq (fromCapAddr capa) ISA_CAPSIZE_BYTES) x.(capAddrs) /\
                                readCap mem capa = inl y;
          (* When a cap y is loaded using a cap x, then the attentuation of x comes into play to create z *)
          loadAttenuate: z = attenuate x y
        }.

      (* Cap z is the sealed version of cap y using a key in x *)
      Definition Seal : Prop :=
        exists k, In k x.(capSealingKeys) /\
             x.(capSealed) = None /\
             y.(capSealed) = None /\
             z = setCapSealed y (Some (inr k)).

      Definition Unseal : Prop :=
        exists k, In k x.(capUnsealingKeys) /\
             x.(capSealed) = None /\
             y.(capSealed) = Some (inr k) /\
             z = setCapSealed y None.
    End CapStep.

    Section Transitivity.
      Variable origSet: list Cap.

      Inductive ReachableCap: Cap -> Prop :=
      | Refl (c: Cap) (inPf: In c origSet) : ReachableCap c
      | StepRestrict y (yPf: ReachableCap y) z (yz: Restrict y z) : ReachableCap z
      | StepLoadCap x (xPf: ReachableCap x) y z (xyz: LoadCap x y z): ReachableCap z
      | StepSeal x (xPf: ReachableCap x) y (yPf: ReachableCap y) z (xyz: Seal x y z): ReachableCap z
      | StepUnseal x (xPf: ReachableCap x) y (yPf: ReachableCap y) z (xyz: Unseal x y z): ReachableCap z.

      (* Transitively reachable addr listed with permissions, canStore and canBeStored *)
      Inductive ReachableAddr: Addr -> nat -> list Perm.t -> list Label -> list Label -> Prop :=
      | HasAddr c (cPf: ReachableCap c) a sz (ina: Subset (seq a sz) c.(capAddrs)) (notSealed: c.(capSealed) = None)
        : ReachableAddr a sz c.(capPerms) c.(capCanStore) c.(capCanBeStored).

      Definition ReachableCaps newCaps := forall c, In c newCaps -> ReachableCap c.

      Section UpdMem.
        Variable mem': FullMemory.

        Definition StPermForAddr (auth: Cap) (a: Addr) (sz: nat) :=
          ReachableCap auth
          /\ In Perm.Store auth.(capPerms)
          /\ auth.(capSealed) = None
          /\ Subset (seq a sz) auth.(capAddrs).

        Definition StPermForCap (auth: Cap) (capa: CapAddr) :=
          StPermForAddr auth (fromCapAddr capa) ISA_CAPSIZE_BYTES /\
          In Perm.Cap auth.(capPerms).

        Definition ValidMemCapUpdate :=
          forall capa stDataCap, readCap mem capa <> readCap mem' capa ->
                            readCap mem' capa = inl stDataCap ->
                            ReachableCap stDataCap /\
                            exists stAddrCap, StPermForCap stAddrCap capa
                                         /\ (exists l, In l stAddrCap.(capCanStore) /\
                                                 In l stDataCap.(capCanBeStored)
                                           ).

        Definition ValidMemTagRemoval :=
          forall capa, readTag mem capa = true ->
                          readTag mem' capa = false ->
                          exists stAddrCap, StPermForCap stAddrCap capa.

        Definition ValidMemDataUpdate :=
          forall a, readByte mem a <> readByte mem' a ->
                          exists stAddrCap, StPermForAddr stAddrCap a 1.

        Definition ValidMemUpdate := ValidMemCapUpdate /\ ValidMemTagRemoval /\ ValidMemDataUpdate.
      End UpdMem.
    End Transitivity.
  End CurrMemory.

  Section Machine.
    Import ListNotations.
    Abbreviation PCC := Cap (only parsing).
    Abbreviation MEPCC := Cap (only parsing). (* While MEPCC can become invalid architecturally,
                                             it shouldn't if the switcher is correct *)
    Abbreviation MTCC := Cap (only parsing).
    Definition EXNInfo := Bytes.
    Abbreviation RegIdx := nat (only parsing).

    Definition RegisterFile := list CapOrBytes.
    Definition capsOfRf (rf: RegisterFile) := listSumToInl rf.

    (* Given that the spec can switch threads at any time,
       interrupts are disabled only to achieve atomicity of a code sequence in single-core machines. *)
    Inductive InterruptStatus :=
    | InterruptsEnabled
    | InterruptsDisabled.

    Record TrustedStackFrame := {
        trustedStackFrame_CSP : Cap;
        trustedStackFrame_calleeExportTable : Cap;
        trustedStackFrame_errorCounter : nat
        (* trustedStackFrame_compartmentIdx : nat; (* Actually a pointer to the compartment's export table *) *)
      }.

    (* TS denotes TrustedStack everywhere below *)
    Definition capsOfTSFrame tsf := [tsf.(trustedStackFrame_CSP); tsf.(trustedStackFrame_calleeExportTable)].

    (* Note that TrustedStack is a first class entity in our abstraction, and not yet another object in the Memory *)
    (* That is, it is accessed like how a PCC is accessed using a name *)
    (* In CHERIoT, Trusted stack is just another object in Memory accessible through a thread's MTDC *)
    (* This refinement will be done later *)
    Record TrustedStack := {
        (* trustedStack_shadowRegisters : RegisterFile; *)
        trustedStack_frames : list TrustedStackFrame;
    }.
    Definition capsOfTS ts := concat (map capsOfTSFrame ts.(trustedStack_frames)).

    Record UserThreadState :=
      { thread_rf : RegisterFile;
        thread_pcc: PCC
      }.
    Definition capsOfUserTS uts := uts.(thread_pcc) :: capsOfRf uts.(thread_rf).

    Inductive ThreadAliveStatus :=
    | ThreadAlive
    | ThreadDead.

    (* SystemThreadState is a first class entity like TrustedStack.
      In CHERIoT, only MEPCC and MTCC are first class entities; the rest are objects in memory *)
    Record SystemThreadState :=
      { thread_mepcc: MEPCC;
        thread_mtcc:  MTCC;
        thread_exceptionInfo: EXNInfo;
        thread_trustedStack: TrustedStack;
        thread_alive: ThreadAliveStatus
      }.
    Definition capsOfSystemTS sts := sts.(thread_mepcc) :: sts.(thread_mtcc) :: capsOfTS sts.(thread_trustedStack).

    Record Thread := {
        thread_userState : UserThreadState;
        thread_systemState : SystemThreadState;
      }.
    Definition capsOfThread t := capsOfUserTS t.(thread_userState) ++ capsOfSystemTS t.(thread_systemState).

    Record Machine := {
        machine_memory: FullMemory;
        machine_interruptStatus : InterruptStatus;
        machine_threads : list Thread;
        machine_curThreadId : nat;
    }.

    (* The following definitions are defined per thread (obvious, but re-iterating) *)
    Definition UserContext : Type := (UserThreadState * FullMemory).
    Definition SystemContext : Type := (SystemThreadState * InterruptStatus).

    Section ReachableMemSame.
      Variable m1 m2: FullMemory.
      Variable caps: list Cap.
      (* TODO: Check if we can remove checking Load permission *)
      Definition ReachableDataSame :=
        forall a sz p cs cbs, ReachableAddr m1 caps a sz p cs cbs -> In Perm.Load p ->
                              (ReachableAddr m2 caps a sz p cs cbs /\ readByte m1 a = readByte m2 a).

      (* TODO: Check if we can remove checking Load/Cap permission *)
      Definition ReachableTagSame :=
        forall capa p cs cbs, ReachableAddr m1 caps capa ISA_CAPSIZE_BYTES p cs cbs ->
                              In Perm.Load p -> In Perm.Cap p ->
                              (ReachableAddr m2 caps capa ISA_CAPSIZE_BYTES p cs cbs /\
                                 readTag m1 capa = readTag m2 capa).

      Definition ReachableMemSame := ReachableDataSame /\ ReachableTagSame.

      Section UpdatedMemSame.
        Variable m1' m2': FullMemory.
        (* TODO: Are the UpdatedMemSame conditions all wrong?
           Should they be detected a-priori instead of checking equality of updates *)
        Definition UpdatedDataSame :=
          forall a, (readByte m1' a <> readByte m1 a \/ readByte m2' a <> readByte m2 a) ->
                    readByte m1' a = readByte m2' a.

        Definition UpdatedTagSame :=
          forall capa, (readTag m1' capa <> readTag m1 capa \/ readTag m2' capa <> readTag m2 capa) ->
                       readTag m1' capa = readTag m2' capa.

        Definition UpdatedMemSame := UpdatedDataSame /\ UpdatedTagSame.
      End UpdatedMemSame.
    End ReachableMemSame.

    Section ValidState.
      Definition ValidRf (rf: RegisterFile) : Prop :=
        length rf = ISA_NREGS.
    End ValidState.

    Section NormalInst.
      Variable normalInst: UserContext -> Result ExnInfo UserContext.

      Definition FuncNormal :=
        forall rf pcc m1 m2,
          ReachableMemSame m1 m2 (pcc :: capsOfRf rf) ->
          match normalInst (Build_UserThreadState rf pcc, m1),
                normalInst (Build_UserThreadState rf pcc, m2) with
          | Ok (uts1, m1'), Ok (uts2, m2') =>
              uts1 = uts2 /\ UpdatedMemSame m1 m2 m1' m2'
          | Exn e1, Exn e2 => e1 = e2
          | _, _ => False
          end.

      (* TODO: We might need some provable predicates on all ExnInfo as well
         (for instance, if NO_EXEC_PERMISSION, then MEPCC tag would still be valid) *)
      Definition WfNormalInst := forall rf pcc mem,
          ValidRf rf ->
          FuncNormal /\
          match normalInst (Build_UserThreadState rf pcc, mem) with
          | Ok (Build_UserThreadState rf' pcc', mem') =>
            let caps := pcc :: capsOfRf rf in
            let caps' := pcc' :: capsOfRf rf' in
            In Perm.Exec pcc.(capPerms)
            /\ ValidMemUpdate mem caps mem'
            /\ ReachableCaps mem caps caps'
            /\ In Perm.Exec pcc'.(capPerms)
            /\ ValidRf rf'
          | Exn _ => True
          end.
    End NormalInst.

    Section SystemInst.
      Variable systemInst: UserContext -> SystemContext -> Result ExnInfo (UserContext * SystemContext).

      Definition FuncSystem := forall rf pcc mepcc mtcc exnInfo ts stat ints m1 m2,
          ReachableMemSame m1 m2 ((pcc :: capsOfRf rf) ++ (mepcc :: mtcc :: capsOfTS ts)) ->
          match systemInst (Build_UserThreadState rf pcc, m1)
                  (Build_SystemThreadState mepcc mtcc exnInfo ts stat, ints),
                systemInst (Build_UserThreadState rf pcc, m2)
                                       (Build_SystemThreadState mepcc mtcc exnInfo ts stat, ints) with
          | Ok ((uts1, m1'), sc1), Ok ((uts2, m2'), sc2) =>
              uts1 = uts2 /\ sc1 = sc2 /\ UpdatedMemSame m1 m2 m1' m2'
          | Exn e1, Exn e2 => e1 = e2
          | _, _ => False
          end.

      Definition WfSystemInst pcc := forall rf mem mepcc mtcc exnInfo ts stat ints,
          ValidRf rf ->
          FuncSystem /\
          match systemInst (Build_UserThreadState rf pcc, mem) (Build_SystemThreadState mepcc mtcc exnInfo ts stat, ints) with
          | Ok ((Build_UserThreadState rf' pcc', mem'),
                  (Build_SystemThreadState mepcc' mtcc' exnInfo' ts' stat', ints')) =>
            let caps := (pcc :: capsOfRf rf) ++ (mepcc :: mtcc :: capsOfTS ts) in
            let caps' := (pcc' :: capsOfRf rf') ++ (mepcc' :: mtcc' :: capsOfTS ts') in
            In Perm.Exec pcc.(capPerms)
            /\ In Perm.System pcc.(capPerms)
            /\ ValidMemUpdate mem caps mem'
            /\ ReachableCaps mem caps caps'
            /\ In Perm.Exec pcc'.(capPerms)
            /\ ValidRf rf'
          | Exn _ => True
          end.
    End SystemInst.

    Section GeneralInstruction.
      Variable generalInst: UserContext -> SystemContext -> Result ExnInfo (UserContext * SystemContext).

      (* If the pcc does not have system permissions, the instruction should behave as a function of user state. *)
      Definition WfGeneralInst :=
        (exists normalInst,
           WfNormalInst normalInst /\
           (forall rf pcc mem sysCtx,
              ~ In Perm.System pcc.(capPerms) ->
              match generalInst (Build_UserThreadState rf pcc, mem) sysCtx,
                    normalInst (Build_UserThreadState rf pcc, mem)  with
              | Ok (userCtx', sysCtx'), Ok (nuserCtx') =>
                  userCtx' = nuserCtx' /\ sysCtx = sysCtx'
              | Exn e1, Exn e2 =>
                  e1 = e2
              | _, _ => False
              end)) /\
        (forall pcc,
          In Perm.System pcc.(capPerms) ->
          WfSystemInst generalInst pcc).
    End GeneralInstruction.

    Section CallSentryInst.
      Variable callSentryInst: UserContext -> InterruptStatus ->
                               Result ExnInfo (PCC * RegisterFile * InterruptStatus).

      Definition FuncCallSentry :=
        forall rf pcc ints m1 m2,
          ReachableMemSame m1 m2 (pcc :: capsOfRf rf) ->
          match callSentryInst (Build_UserThreadState rf pcc, m1) ints,
                callSentryInst (Build_UserThreadState rf pcc, m2) ints  with
          | Ok (pcc1', l1, ints1'), Ok (pcc2', l2, ints2') =>
              pcc1' = pcc2' /\ l1 = l2 /\ ints1' = ints2'
          | Exn e1, Exn e2 =>
              e1 = e2
          | _, _ => False
          end.
      Definition WfCallSentryInst (src: RegIdx) (optLink: option RegIdx):= forall rf pcc ints mem,
          ValidRf rf ->
          src < ISA_NREGS /\
          (forall link, optLink = Some link -> link < ISA_NREGS) /\
          FuncCallSentry /\
          match callSentryInst (Build_UserThreadState rf pcc, mem) ints with
          | Ok (pcc', rf', ints') =>
            let caps := pcc :: capsOfRf rf in
            In Perm.Exec pcc.(capPerms) /\
            (exists src_cap,
               nth_error rf src = Some (inl src_cap) /\
               In Perm.Exec src_cap.(capPerms) /\
               match src_cap.(capSealed) with
               | Some (inl CallEnableInterrupt) => ints' = InterruptsEnabled
               | Some (inl CallDisableInterrupt) => ints' = InterruptsDisabled
               | Some (inl CallInheritInterrupt) => ints' = ints
               | None => ints' = ints (* TODO: Does this handle unsealed? *)
               | _ => False
               end /\
             pcc' = setCapSealed src_cap None) /\
             match optLink with
             | Some link =>
                 (forall idx, idx <> link -> nth_error rf' idx = nth_error rf idx)
                 /\ (exists linkCap,
                        nth_error rf' link = Some (inl linkCap)
                        /\ RestrictUnsealed pcc (setCapSealed linkCap None) (* TODO: Check correctness *)
                        /\ linkCap.(capSealed) = Some (inl (if ints is InterruptsEnabled
                                                            then RetEnableInterrupt
                                                            else RetDisableInterrupt))
                        /\ In Perm.Exec linkCap.(capPerms))
             | None => rf' = rf
             end
          | Exn _ => True
          end.
    End CallSentryInst.

    Section RetSentryInst.
      Variable retSentryInst: UserContext -> Result ExnInfo (PCC * InterruptStatus).

      Definition FuncRetSentry :=
        forall rf pcc m1 m2,
          ReachableMemSame m1 m2 (pcc :: capsOfRf rf) ->
          match retSentryInst (Build_UserThreadState rf pcc, m1),
                retSentryInst (Build_UserThreadState rf pcc, m2) with
          | Ok (pcc1', ints1'), Ok (pcc2', ints2') =>
              pcc1' = pcc2' /\ ints1' = ints2'
          | Exn e1, Exn e2 => e1 = e2
          | _, _ => False
          end.

      Definition WfRetSentryInst (src_idx: RegIdx):= forall rf pcc mem,
          ValidRf rf ->
          FuncRetSentry /\
          (src_idx < ISA_NREGS) /\
          match retSentryInst (Build_UserThreadState rf pcc, mem) with
          | Ok (pcc', ints') =>
            In Perm.Exec pcc.(capPerms) /\
            (exists src_cap,
                nth_error rf src_idx = Some (inl src_cap) /\
                In Perm.Exec src_cap.(capPerms) /\
                match src_cap.(capSealed) with
                | Some (inl RetEnableInterrupt) => ints' = InterruptsEnabled
                | Some (inl RetDisableInterrupt) => ints' = InterruptsDisabled
                | _ => False (* TODO: if we want to support unsealed returns, how do we do it (we don't have ints)? *)
                end /\
                pcc' = setCapSealed src_cap None)
          | Exn e => True
          end.
    End RetSentryInst.

    (* TODO: This might be needed for ECall; or can we move ECall to normal instruction decode? *)
    Section ExnInst.
      Variable exnInst: UserContext -> EXNInfo.

      Definition FuncExn :=
        forall rf pcc m1 m2,
          ReachableMemSame m1 m2 (pcc :: capsOfRf rf) ->
          let exn1 := exnInst (Build_UserThreadState rf pcc, m1) in
          let exn2 := exnInst (Build_UserThreadState rf pcc, m2) in
          exn1 = exn2.

      Definition WfExnInst := forall rf pcc mem,
          let exn := exnInst (Build_UserThreadState rf pcc, mem) in
          let caps := pcc :: capsOfRf rf in
          FuncExn.
    End ExnInst.

    (** ** Instructions, events and traces

        An instruction as the decoder delivers it: one of four kinds, each carrying its semantics
        as a function and a proof that the function is well formed.  A general instruction
        ([Inst_General]) acts on the user and system contexts under [WfGeneralInst], which
        includes the per-instruction monotonicity of reachable capabilities; a call ([Inst_Call])
        jumps through the capability in register [srcReg], a forward sentry or, as
        [WfCallSentryInst] stands (its own comment marks the question), an unsealed code
        capability, leaving a backward sentry to the caller in the link register when [optLink]
        names one; a return ([Inst_Ret]) jumps through the backward sentry in [srcReg] under
        [WfRetSentryInst]; an exception instruction ([Inst_Exn]) traps, with the payload
        [exnInst] computes when the fetch is permitted, under [WfExnInst].  Because the proof
        travels with the instruction, whoever builds an [Inst] discharges its well-formedness:
        nothing in this file proves it, and no concrete instruction set is given here. *)
    Inductive Inst :=
    | Inst_General generalInst (wf: WfGeneralInst generalInst)
    | Inst_Call (srcReg: RegIdx) (optLink: option RegIdx) callSentryInst
                (wf: WfCallSentryInst callSentryInst srcReg optLink)
    | Inst_Ret (srcReg: RegIdx) retSentryInst (wf: WfRetSentryInst retSentryInst srcReg)
    | Inst_Exn exnInst (wf: WfExnInst exnInst).

    (* WIP *)
    Abbreviation ThreadIdx := nat (only parsing).

    (** What a step of the current thread reports: a trap ([Ev_Exception]); a call, with the PCC,
        register file and interrupt status it installs; a return, with the same; or a general
        instruction ([Ev_General]).  The properties module treats [Ev_General], together with
        thread switches, as the same-domain events, and the other three as crossings between
        protection domains. *)
    Inductive SameThreadEvent :=
    | Ev_Exception
    | Ev_Call (pcc: PCC) (rf: RegisterFile) (ints: InterruptStatus)
    | Ev_Ret (pcc: PCC) (rf: RegisterFile) (ints: InterruptStatus)
    | Ev_General.

    (** A machine event: a switch of the current thread to index [idx], or an event of thread
        [idx]. *)
    Inductive Event :=
    | Ev_SwitchThreads (idx: nat)
    | Ev_SameThread (idx: ThreadIdx) (ev: SameThreadEvent).

    (** The events of an execution, most recent first: [MachineStep] conses each new event onto
        the front. *)
    Definition Trace := list Event.

    (** ** Fetch, decode, execute

        The step relation, parametric in how an instruction is fetched ([fetchAddrs]: the
        addresses read for a program counter), how the fetched bytes are decoded ([decode]), and
        the payload a fetch that fails the PCC check traps with ([pccNotInBounds]; the check,
        [fetchAddrsInBounds], covers bounds, sealing and execute permission). *)
    Section FetchDecodeExecute.

      (** Which addresses a fetch at a program counter reads, given the memory. *)
      Variable fetchAddrs: FullMemory -> Addr -> list Addr.
      (* Addresses fetched should not depend on arbitrary memory regions. *)

      (** A fetch that depends on nothing but the bytes at addresses fixed by the program
          counter: some function of the counter alone gives addresses such that two memories
          agreeing on their bytes give the same fetch.  Declared as context just below; none of
          the definitions of this section refer to it, so it is not a parameter of [MachineStep]. *)
      Definition FetchAddrsOk :=
        exists (fn: Addr -> list Addr),
        forall mem1 mem2 addr,
          (forall a, In a (fn addr) -> readByte mem1 a = readByte mem2 a
          (* TODO: Do we need tags to be the same? *)
          (* /\ readTag mem1 (toCapAddr a) = readTag mem2 (toCapAddr a) *) ) ->
          fetchAddrs mem1 addr = fetchAddrs mem2 addr.
      Context {fetchAddrsOk: FetchAddrsOk}.

      (** The decoder, from the fetched bytes to an [Inst], and the trap payload for a fetch that
          fails the PCC check: the name says bounds, but [ThreadStep] uses it whenever
          [fetchAddrsInBounds] fails, so also for a sealed PCC or one without execute permission. *)
      Variable decode : list Byte -> Inst.
      Variable pccNotInBounds: EXNInfo.

      (** Fix one thread's full context [fc]: the user context (register file, PCC and memory)
          and the system context (system thread state and interrupt status).  The nine
          projections name its parts, and the step is defined over them. *)
      Section WithContext.
        Variable fc: UserContext * SystemContext.

        (** The user context. *)
        Definition uc := fst fc.

        (** The memory. *)
        Definition mem : FullMemory := snd uc.

        (** The program-counter capability. *)
        Definition pcc := (fst uc).(thread_pcc).

        (** The register file. *)
        Definition rf := (fst uc).(thread_rf).

        (** The system context. *)
        Definition sc := snd fc.

        (** The system thread state. *)
        Definition sts := fst sc.

        (** The interrupt status. *)
        Definition ints := snd sc.

        (** The exception program-counter capability, where a trap saves the faulting PCC. *)
        Definition mepcc := (fst sc).(thread_mepcc).

        (** The trap-vector capability, where a trap continues. *)
        Definition mtcc := (fst sc).(thread_mtcc).

        (** The context after a trap with payload [exnInfo]: execution continues at [mtcc] with
            the register file unchanged, the new system state's MEPCC field holds the faulting
            [pcc] (the old [mepcc] is discarded), the payload is recorded, and the trusted stack,
            liveness, memory and interrupt status are as before.  The event is [Ev_Exception]. *)
        Definition exceptionState (exnInfo: EXNInfo): (UserContext * SystemContext) * SameThreadEvent :=
          (((Build_UserThreadState rf mtcc, mem),
             (Build_SystemThreadState pcc mtcc exnInfo sts.(thread_trustedStack) sts.(thread_alive), ints)
           ), Ev_Exception).

        (** One step of the thread when the PCC check holds.  The bytes at the addresses that
            [fetchAddrs] returns for the PCC's cursor are decoded, and the instruction's function
            runs: a general instruction yields new user and system contexts ([Ev_General]); a
            call yields the new PCC, register file and interrupt status, with the system thread
            state and memory unchanged ([Ev_Call]); a return yields the new PCC and interrupt
            status, with the register file, system thread state and memory unchanged ([Ev_Ret]);
            an exception instruction traps with its payload, and so does any instruction whose
            function returns [Exn]. *)
        Definition threadStepFunction: (UserContext * SystemContext) * SameThreadEvent :=
          match decode (map (readByte mem) (fetchAddrs mem pcc.(capCursor))) with
          | Inst_General generalInst wf =>
              match generalInst uc sc with
              | Ok (uc', sc') => ((uc', sc'), Ev_General)
              | Exn e => exceptionState e
              end
          | Inst_Call src optLinkReg callSentryInst wf =>
              match callSentryInst uc ints with
              | Ok (pcc', rf', ints') =>
                   (((Build_UserThreadState rf' pcc', mem), (sts, ints')), Ev_Call pcc' rf' ints')
              | Exn e => exceptionState e
              end
          | Inst_Ret srcReg retSentryInst wf =>
              match retSentryInst uc with
              | Ok (pcc', ints') =>
                  (((Build_UserThreadState rf pcc', mem), (sts, ints')), Ev_Ret pcc' rf ints')
              | Exn e => exceptionState e
              end
          | Inst_Exn exnInst wf =>
              exceptionState (exnInst uc)
          end.

        (** The fetch is permitted: every address read lies within the PCC's bounds, so does the
            cursor, the PCC is unsealed, and it carries execute permission. *)
        Definition fetchAddrsInBounds := Subset (fetchAddrs mem pcc.(capCursor)) pcc.(capAddrs)
                                         /\ In pcc.(capCursor) pcc.(capAddrs)
                                         /\ isSealed pcc = false
                                         /\ In Perm.Exec pcc.(capPerms).                                                            


        (** The thread-step relation on the context: if the PCC check [fetchAddrsInBounds] holds
            the step is [threadStepFunction]; if not, it is the trap [pccNotInBounds].  The two
            cases exclude each other, and together they cover every context classically:
            [fetchAddrsInBounds] is a proposition with no decision procedure here. *)
        Inductive ThreadStep : ((UserContext * SystemContext) * SameThreadEvent) -> Prop :=
        | GoodThreadStep (inBounds: fetchAddrsInBounds) : ThreadStep threadStepFunction
        | BadUserFetch (notInBounds: ~ fetchAddrsInBounds) : ThreadStep (exceptionState pccNotInBounds).
      End WithContext.

      (** The machine with [tid] as its current thread and nothing else changed. *)
      Definition setMachineThread (m: Machine) (tid: nat): Machine :=
        {| machine_memory := m.(machine_memory);
           machine_interruptStatus := m.(machine_interruptStatus);
           machine_threads := m.(machine_threads);
           machine_curThreadId := tid
        |}.

      (* TODO: Can we just have a single MachineStep constructor,
         where if interrupts are disabled, the thread has to match the previous step's?
         Would such a change create a problem when it comes to implementing the thread switcher? *)

      (** A step of the current thread of [m1] that produces [m2]: the current thread index is
          the same in both; every other thread is unchanged; the current thread is alive and
          takes a [ThreadStep] from its context in [m1], with [m1]'s memory and interrupt status,
          to its context in [m2], with [m2]'s; and [m2] holds the resulting thread state at that
          index.  The event names the thread. *)
      Inductive SameThreadStep : Machine -> Machine -> Event -> Prop :=
      | SameThreadStepOk :
        forall m1 m2 ev
          (threadIdEq: m2.(machine_curThreadId) = m1.(machine_curThreadId))
          (idleThreadsEq: forall n, n <> m1.(machine_curThreadId) ->
                            nth_error m2.(machine_threads) n = nth_error m1.(machine_threads) n)
          (stepOk: exists thread userSt' sysSt',
              nth_error m1.(machine_threads) m1.(machine_curThreadId) = Some thread /\
              (* Only live threads can take a step. *)
              thread.(thread_systemState).(thread_alive) = ThreadAlive /\ 
              ThreadStep ((thread.(thread_userState), m1.(machine_memory)),
                          (thread.(thread_systemState), m1.(machine_interruptStatus)))
                         ((userSt', m2.(machine_memory)), (sysSt', m2.(machine_interruptStatus)), ev) /\
                   nth_error m2.(machine_threads) m2.(machine_curThreadId) = Some (Build_Thread userSt' sysSt')),
          SameThreadStep m1 m2 (Ev_SameThread m2.(machine_curThreadId) ev).

      (** The step relation over a machine and its trace.  Either a thread switch
          ([Step_SwitchThreads]): allowed only with interrupts enabled, to any index below the
          thread count, the current one included, and nothing but the current thread index
          changes; or the current thread takes a [SameThreadStep].  Each step conses its event
          onto the trace.  The properties module states what holds of every reachable state as an
          invariant over this relation. *)
      Inductive MachineStep : Machine * Trace -> Machine * Trace -> Prop :=
      | Step_SwitchThreads m tr tid'
          (iEnabled: m.(machine_interruptStatus) = InterruptsEnabled)
          (tidOk: tid' < List.length m.(machine_threads)):
        MachineStep (m, tr) ((setMachineThread m tid'),((Ev_SwitchThreads tid')::tr))
      | Step_SameThread m1 m2 tr ev
          (stepOk:SameThreadStep m1 m2 ev):
        MachineStep (m1, tr) (m2, ev::tr) .

    End FetchDecodeExecute.
  End Machine.
End Machine.

Module CHERIoTValidation.
  Import ListNotations.
  Local Open Scope N_scope.
  Inductive CompressedPerm :=
  | MemCapRW (GL: bool) (SL: bool) (LM: bool) (LG: bool) (* Implicit: LD, MC, SD *)
  | MemCapRO (GL: bool) (LM: bool) (LG: bool) (* Implicit: LD, MC *)
  | MemCapWO (GL: bool) (* Implicit: SD, MC *)
  | MemDataOnly (GL: bool) (LD: bool) (SD: bool) (* Implicit: None *)
  | Executable (GL: bool) (SR: bool) (LM: bool) (LG: bool) (* Implicit: EX, LD, MC *)
  | Sealing (GL: bool) (U0: bool) (SE: bool) (US: bool) (* Implicit: None *).

  Instance machineTypeParams : MachineTypeParams :=
    { Byte := N;
      Key := N
    }.
  Record cheriot_cap :=
  { reserved: bool;
    permissions: CompressedPerm;
    otype: N; (* < 8 *)
    base: N;
    length: N;
    addr: N;
    addrInBounds: base <= addr < base + length
    (* This is needed because of compressed caps. See comment in definition of Cap above *)
  }.

  Record Perm :=
    {
      EX : bool; (* PERMIT_EXECUTE *)
      GL : bool; (* GLOBAL *)
      LD : bool; (* PERMIT_LOAD *)
      SD : bool; (* PERMIT_STORE *)
      SL : bool; (* PERMIT_STORE_LOCAL_CAPABILITY *)
      SR : bool; (* PERMIT_ACCESS_SYSTEM_REGISTERS *)
      SE : bool; (* PERMIT_SEAL *)
      US : bool; (* PERMIT_UNSEAL *)
      U0 : bool; (* USER_PERM0 *)
      LM : bool; (* PERMIT_LOAD_MUTABLE *)
      LG : bool; (* PERMIT_LOAD_GLOBAL *)
      MC : bool; (* PERMIT_LOAD_STORE_CAPABILITY *)
    }.

  Definition decompress_perm (p: CompressedPerm) : Perm :=
    match p with
    | MemCapRW gl sl lm lg =>
        {| EX := false;
           GL := gl;
           LD := true;
           SD := true;
           SL := sl;
           SR := false;
           SE := false;
           US := false;
           U0 := false;
           LM := lm;
           LG := lg;
           MC := true
        |}
    | MemCapRO gl lm lg =>
        {| EX := false;
           GL := gl;
           LD := true;
           SD := false;
           SL := false;
           SR := false;
           SE := false;
           US := false;
           U0 := false;
           LM := lm;
           LG := lg;
           MC := true
        |}
    | MemCapWO gl =>
        {| EX := false;
           GL := gl;
           LD := false;
           SD := true;
           SL := false;
           SR := false;
           SE := false;
           US := false;
           U0 := false;
           LM := false;
           LG := false;
           MC := true
        |}
    | MemDataOnly gl ld sd =>
        {| EX := false;
           GL := gl;
           LD := ld;
           SD := sd;
           SL := false;
           SR := false;
           SE := false;
           US := false;
           U0 := false;
           LM := false;
           LG := false;
           MC := false
        |}
    | Executable gl sr lm lg =>
        {| EX := true;
           GL := gl;
           LD := true;
           SD := false;
           SL := false;
           SR := sr;
           SE := false;
           US := false;
           U0 := false;
           LM := lm;
           LG := lg;
           MC := true
        |}
    | Sealing gl u0 se us =>
        {| EX := false;
           GL := gl;
           LD := false;
           SD := false;
           SL := false;
           SR := false;
           SE := se;
           US := us;
           U0 := u0;
           LM := false;
           LG := false;
           MC := false
        |}
    end.

  Definition mk_abstract_cap (c: cheriot_cap) : Cap :=
    let d := decompress_perm c.(permissions) in
    {|capSealed := if d.(EX)
                   then match c.(otype) with
                        | 0 => None
                        | 1 => Some (inl CallInheritInterrupt)
                        | 2 => Some (inl CallDisableInterrupt)
                        | 3 => Some (inl CallEnableInterrupt)
                        | 4 => Some (inl RetDisableInterrupt)
                        | 5 => Some (inl RetEnableInterrupt)
                        | (* 6 & 7 *) _ => None (* TODO: capSentry ⊆ capSealed *)
                        end
                   else match c.(otype) with
                        | 0 => None
                        | _ => Some (inr c.(otype))
                        end;
      capPerms := filter (fun p => match p with
                                   | Perm.Exec => d.(EX)
                                   | Perm.System => d.(SR)
                                   | Perm.Load => d.(LD)
                                   | Perm.Store => d.(SD)
                                   | Perm.Cap => d.(MC)
                                   | Perm.Sealing => d.(SE)
                                   | Perm.Unsealing => d.(US)
                                   end)
                    [Perm.Exec;Perm.System;Perm.Load;Perm.Cap;Perm.Sealing;Perm.Unsealing];
      capCanStore := if d.(SL) then [Local;NonLocal] else [NonLocal];
      capCanBeStored := if d.(GL) then [Local;NonLocal] else [Local];
      capSealingKeys := [c.(addr)];
      capUnsealingKeys := [c.(addr)];
      capAddrs := seq (N.to_nat c.(base)) (N.to_nat c.(length));
      capKeepPerms := filter (fun p => match p with
                                       | Perm.Exec => true
                                       | Perm.System => true
                                       | Perm.Load => true
                                       | Perm.Store => d.(LM)
                                       | Perm.Cap => true
                                       | Perm.Sealing => true
                                       | Perm.Unsealing => true
                                       end)
                        [Perm.Exec;Perm.System;Perm.Load;Perm.Cap;Perm.Sealing;Perm.Unsealing];
      capKeepCanStore := [Local;NonLocal];
      capKeepCanBeStored := if d.(LG) then [Local;NonLocal] else [Local];
      capCursor := N.to_nat c.(addr) |}.
End CHERIoTValidation.

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

(*! Lemmas derived from the Spec *)
From Stdlib Require Import List Lia Bool Nat NArith.
Set Primitive Projections.
From cheriot Require Import Spec Utils Tactics.

Create HintDb invariants.
Import ListNotations.
Create HintDb ReachableCap.

Set Nested Proofs Allowed.

(** * Lemmas about the model

    What [Spec] lets one prove without any configuration: the addresses reachable with a given
    permission and the disjointness predicates ([ReachabilityDefs]); properties of the one-step
    relations on capabilities ([CapStepLemmas]); how reachability behaves under larger source
    sets and under valid memory updates ([ReachableCapLemmas], [MemUpdateLemmas]); that a memory
    update authorized by capabilities disjoint from a set leaves that set's reach unchanged
    ([SeparationLemmas]); what a well-formed instruction preserves ([WFInstructionLemmas]); and
    what a same-thread step keeps ([Step]).  All of it under the parameters of [Spec], bound
    once in [WithContext]. *)

(** The parameters of [Spec] (the ISA parameters, the byte and key types, the capability
    encoding), bound for every lemma below. *)
Section WithContext.
  Context [ISA: ISA_params].
  Context {machineTypeParams: MachineTypeParams}.
  Context {capEncodeDecode: @CapEncodeDecode machineTypeParams}.
  (* Notation FullMemory := (@FullMemory Byte). *)
  (* Notation Cap := (@Cap Key). *)
  (* Notation CapOrBytes := (@CapOrBytes Byte Key). *)
  (* Notation Machine := (@Machine Byte Key). *)
  (* Notation AddrOffset := nat (only parsing). *)
  (* Notation PCC := Cap (only parsing). *)
  (* Notation RegisterFile := (@RegisterFile Byte Key). *)
  (* Notation Thread := (@Thread Byte Key). *)

  (** The capability size is positive. *)
  Section ISA_params.

    (** [ISA_CAPSIZE_BYTES] is [2 ^ ISA_LG_CAPSIZE_BYTES], hence positive. *)
    Lemma ISA_CAPSIZE_BYTES_NONZERO:
      ISA_CAPSIZE_BYTES > 0.
    Proof.
      unfold ISA_CAPSIZE_BYTES.
      pose proof (PeanoNat.Nat.pow_nonzero 2 ISA_LG_CAPSIZE_BYTES). lia.
    Qed.
  End ISA_params.

  (** Addresses reachable with a given permission, and the disjointness and inclusion predicates
      the properties are stated with.  Each is built on [ReachableAddr] ([Spec]), which reaches
      an address through some capability reachable from [caps] in [mem]. *)
  Section ReachabilityDefs.
  (* Addresses reachable with load permission. *)

    (** Reachable through a capability with the load permission. *)
    Definition ReachableReadAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      exists p cs cbs ,
        ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Load p).

    (* Addresses reachable with write permission. *)

    (** Reachable through a capability with the store permission. *)
    Definition ReachableWriteAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      exists p cs cbs ,
        ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Store p).

    (* Addresses reachable with execute permission. *)

    (** Reachable through a capability with the execute permission. *)
    Definition ReachableExecAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      exists p cs cbs ,
        ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Exec p).

    (* Addresses reachable with read or write permission. *)

    (** Reachable with load or with store permission. *)
    Definition ReachableRWAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      ReachableReadAddr mem caps a \/
        ReachableWriteAddr mem caps a.

    (* Addresses reachable with read, write, or execute permission. *)

    (** Reachable with load, store or execute permission; the footprint condition of a well-formed
        compartment ([WFCompartment] in [Properties]) is stated with it. *)
    Definition ReachableRWXAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      exists p cs cbs,
        ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Load p \/ In Perm.Store p \/ In Perm.Exec p).

    (** No address is reachable with load or store permission from both [c1] and [c2]: the
        isolation of two threads' capabilities ([IsolatedThreads] in [Properties]). *)
    Definition RWAddressesDisjoint (mem: FullMemory) (c1 c2: list Cap) : Prop :=
      forall a,
        ReachableRWAddr mem c1 a ->
        ReachableRWAddr mem c2 a ->
        False.

    (** Everything reachable from [caps_cur] in [m_cur] was reachable from [caps_init] in [m_init]:
        the per-thread monotonicity the main theorem establishes. *)
    Definition ReachableCapSubset (m_init m_cur: FullMemory) (caps_init caps_cur: list Cap) : Prop :=
      forall caps,
        ReachableCaps m_cur caps_cur caps ->
        ReachableCaps m_init caps_init caps.

    (** No address writable through [c1] is readable through [c2]; the one-directional form of
        [RWAddressesDisjoint] that the separation lemmas take. *)
    Definition WriteReadDisjoint (mem: FullMemory) (c1 c2: list Cap) : Prop :=
      forall a,
        ReachableWriteAddr mem c1 a ->
        ReachableReadAddr mem c2 a ->
        False.
  End ReachabilityDefs.

  (** Properties of the one-step relations on capabilities: [Restrict] is a preorder that
      shrinks keys and bounds and keeps the sealing state, [attenuate] yields a restriction, and
      [RestrictUnsealed] on an unsealed capability is a [Restrict]. *)
  Section CapStepLemmas.
    (* Attenuate is monotonic. *)

    (** Loading [y] through [x] yields a restriction of [y]. *)
    Lemma AttenuateRestrict:
      forall (x y: Cap),
        Restrict y (attenuate x y).
    Proof.
      cbv [attenuate Restrict].
      intros.
      case_match; constructor; cbn; cbv[SealEq isSealed]; cbn; repeat simpl_match; cbn.
      all: repeat match goal with
           | |- EqSet ?x ?x => cbv[EqSet]; reflexivity
           | |- Subset (filter _ _) _ => apply SubsetFilter1
           | |- _ => progress (simplify_Subset || auto)
           end.
      all: by (apply internal_Label_dec_bl || apply Perm.internal_t_dec_bl).
    Qed.

    (** A restriction holds no sealing key the original lacks. *)
    Lemma RestrictCapSealingKeysSubset:
      forall (c c': Cap),
      Restrict c c' ->
      Subset c'.(capSealingKeys) c.(capSealingKeys).
    Proof.
      cbv[Restrict]. intros. case_match;
        destruct H; cbv[EqSet Subset] in *; auto.
      intros. rewrite<-restrictSealedSealingKeysEq; auto.
    Qed.

    (** A restriction holds no unsealing key the original lacks. *)
    Lemma RestrictCapUnsealingKeysSubset:
      forall (c c': Cap),
      Restrict c c' ->
      Subset c'.(capUnsealingKeys) c.(capUnsealingKeys).
    Proof.
      cbv[Restrict]. intros. case_match;
        destruct H; cbv[EqSet Subset] in *; auto.
      intros. rewrite<-restrictSealedUnsealingKeysSubset; auto.
    Qed.

    (** A restriction keeps the sealing state. *)
    Lemma RestrictSealedEq:
      forall (c c': Cap),
      Restrict c c' ->
      c.(capSealed) = c'.(capSealed).      
    Proof.
      cbv[Restrict]. intros. case_match;
        destruct H; cbv[SealEq] in *; rewrite_solve.
    Qed.

    (** A restriction's bounds lie within the original's. *)
    Lemma RestrictCapAddrsSubset:
      forall (c c': Cap),
      Restrict c c' ->
      Subset c'.(capAddrs) c.(capAddrs).
    Proof.
      cbv[Restrict]. intros. case_match;
        destruct H; cbv[EqSet Subset] in *; auto.
      intros. rewrite<-restrictSealedAddrsEq; auto.
    Qed.

    (** [Restrict] is preserved by unsealing both sides. *)
    Lemma RestrictSetCapUnsealed:
      forall (y z: Cap),            
        Restrict y z ->
        Restrict (setCapSealed y None) (setCapSealed z None).
    Proof.
      intros. cbv[Restrict] in *. cbv[setCapSealed]. cbn.
      case_match; inv H; constructor; cbv[SealEq]; cbn; auto.
      all: cbv [EqSet Subset] in *; intros *; 
                 try match goal with
                 | H: _ |- _ => rewrite H 
                 end; auto.
    Qed.

    (** [Restrict] is reflexive. *)
    Lemma RestrictRefl: forall (x: Cap), Restrict x x.
    Proof.
      intros. cbv[Restrict].
      case_match; constructor; cbv[EqSet Subset SealEq]; auto.
      all: reflexivity.
    Qed.

    (** [Restrict] is transitive. *)
    Lemma RestrictTrans:
      forall (x y z: Cap),
        Restrict x y -> Restrict y z -> Restrict x z.
    Proof.
      cbv[Restrict]. intros. repeat case_match;
      repeat match goal with
      | H: RestrictSealed _ _ |- _ => destruct H
      | H: RestrictUnsealed _ _ |- _ => destruct H
        end; constructor; cbv[EqSet SealEq Subset] in *; auto; try rewrite_solve.
      all: intros *;
           try match goal with
           | H: _ |- _ => rewrite H 
           end; auto.
      all: repeat match goal with
           | _ => progress option_simpl 
           | H: _ = Some _ |- _ => rewrite H in *
           | H: _ = None |- _ => rewrite H in *
             end.
    Qed.

    (** On an unsealed capability, [RestrictUnsealed] is [Restrict]. *)
    Lemma RestrictUnsealedOk:
      forall (c1 c2: Cap),
        RestrictUnsealed c1 c2 ->
        isSealed c1 = false ->
        Restrict c1 c2.
    Proof.
      cbv[Restrict isSealed]. intros. by case_match. 
    Qed.

    (** Unsealing an unsealed capability changes nothing. *)
    Lemma setCapSealedNoneEq:
      forall (c: Cap), capSealed c = None -> setCapSealed c None = c.
    Proof.
      cbv[setCapSealed]. destruct c; intros; cbn in *; subst; auto.
    Qed.

    (** Setting the sealing state twice keeps the last. *)
    Lemma setCapSealed_inv:
      forall (x: Cap) (optSeal optSeal': option SealT),
        setCapSealed (setCapSealed x optSeal) optSeal' = setCapSealed x optSeal'.
    Proof.
      reflexivity.
    Qed.

  End CapStepLemmas.

  (** Reachability grows with the source set and composes along [ReachableCapSubset]. *)
  Section ReachableCapLemmas.

    (** A capability reachable from [caps] is reachable from any superset. *)
    Lemma ReachableCapIncrease:
      forall mem caps capss caps',
        ReachableCap mem caps caps' ->
        Subset caps capss ->
        ReachableCap mem capss caps'.
    Proof.
      cbv[Subset].
      induction 1; intros hsubset.
      - apply Refl; auto.
      - eapply StepRestrict; eauto.
      - eapply StepLoadCap; eauto.
      - apply StepSeal with (x := x) (y := y); auto.
      - apply StepUnseal with (x := x) (y := y); auto.
    Qed.

    (** Reachability of a list is preserved by appending the same capabilities to both sides. *)
    Lemma ReachableCaps_app:
      forall mem c1 c2 cs,
        ReachableCaps mem c1 c2 ->
        ReachableCaps mem (c1 ++ cs) (c2 ++ cs).
    Proof.
      cbv[ReachableCaps].
      intros * Hin * Hin2.
      apply in_app_or in Hin2.
      destruct_or! Hin2.
      - eapply ReachableCapIncrease; eauto. apply Subset_app.
      - constructor. apply in_app_iff; auto.
    Qed.

    (** Through a [ReachableCapSubset], a capability reachable in the current state is reachable
        in the initial one. *)
    Lemma ReachableCapSubsetImpliesReachableCap:
      forall mem mem1 cs cs1 c,
      ReachableCapSubset mem mem1 cs cs1 ->
      ReachableCap mem1 cs1 c ->
      ReachableCap mem cs c.
    Proof.
      cbv[ReachableCapSubset].
      intros. eapply H with (caps := [c]); cbv[ReachableCaps]; intuition eauto.
      - repeat destruct H1; subst; auto.
      - constructor; auto.
    Qed.


  End ReachableCapLemmas.

  (** How reachability behaves across a valid memory update ([ValidMemUpdate] and its three
      parts): nothing becomes reachable in the new memory that was not reachable in the old one
      from the capabilities that authorized the update, and the update conditions are monotonic
      in the authorizing set. *)
  Section MemUpdateLemmas.
    (* After a valid memory update, if a cap can be loaded from the new memory
       then it must have been reachable from the old memory. *)

    (** A capability loaded in the new memory through a capability reachable in the old one was
        reachable in the old one, when the capability stores were valid. *)
    Lemma LoadCapUpdate:
      forall mem mem' x y z caps,
      ReachableCap mem caps x ->
      LoadCap mem' x y z ->
      ValidMemCapUpdate mem caps mem' ->
      ReachableCap mem caps z.
    Proof.
      cbv [ValidMemCapUpdate].
      intros * hauth hload hupdate.
      inv hload. destruct_products.
      specialize (hupdate capa). rewrite loadFromAuthr in *.
      destruct (CapOrBytes_eq_dec (readCap mem capa) (inl y) ) as [Heq | Hneq].
      - eapply StepLoadCap with (y := y); eauto.
        constructor; eauto.
      - propositional.
        specialize hupdate with (1 := Hneq) (2 := eq_refl).
        destruct_products.
        eapply StepRestrict; eauto.
        eapply AttenuateRestrict; eauto.
    Qed.

    (** The same under the whole [ValidMemUpdate]. *)
    Lemma LoadCapUpdate':
      forall mem mem' x y z caps,
      ReachableCap mem caps x ->
      LoadCap mem' x y z ->
      ValidMemUpdate mem caps mem' ->
      ReachableCap mem caps z.
    Proof.
      cbv[ValidMemUpdate].
      intros; eapply LoadCapUpdate; destruct_products; eauto.
    Qed.

    (** What is reachable in the new memory from capabilities reachable in the old one was
        reachable in the old one: the one-capability form. *)
    Lemma ReachableCap_ValidUpdate:
      forall mem mem' (caps caps': list Cap) c,
        ReachableCap mem' caps' c ->
        ValidMemUpdate mem caps mem' ->
        ReachableCaps mem caps caps' ->
        ReachableCap mem caps c.
    Proof.
      cbv [ReachableCaps].
      induction 1; intros * hupdate hcaps'; propositional.
      - auto.
      - eapply StepRestrict; eauto.
      - eapply LoadCapUpdate'; eauto.
      - eapply StepSeal with (3 := xyz); auto.
      - eapply StepUnseal with (3 := xyz); auto.
    Qed.

    (** The same for a reachable address, with its size, permissions and labels. *)
    Lemma ReachableAddr_ValidUpdate:
      forall mem mem' caps caps' a sz p cs cbs,
        ReachableAddr mem' caps' a sz p cs cbs ->
        ValidMemUpdate mem caps mem' ->
        ReachableCaps mem caps caps' ->
        ReachableAddr mem caps a sz p cs cbs.
    Proof.
      intros. inv H. constructor; eauto. eapply ReachableCap_ValidUpdate; eauto.
    Qed.

    (** The same for a readable address. *)
    Lemma ReachableReadAddr_ValidUpdate:
      forall mem mem' caps caps' a,
        ReachableReadAddr mem' caps' a ->
        ValidMemUpdate mem caps mem' ->
        ReachableCaps mem caps caps' ->
        ReachableReadAddr mem caps a .
    Proof.
      cbv[ReachableReadAddr]. intros; destruct_products.
      do 3 eexists; split; eauto. by (eapply ReachableAddr_ValidUpdate).
    Qed.

    (** The same for a writable address. *)
    Lemma ReachableWriteAddr_ValidUpdate:
      forall mem mem' caps caps' a,
        ReachableWriteAddr mem' caps' a ->
        ValidMemUpdate mem caps mem' ->
        ReachableCaps mem caps caps' ->
        ReachableWriteAddr mem caps a .
    Proof.
      cbv[ReachableWriteAddr]. intros; destruct_products.
      do 3 eexists; split; eauto. by (eapply ReachableAddr_ValidUpdate).
    Qed.

    (** The same for an address readable or writable. *)
    Lemma ReachableRWAddr_ValidUpdate:
      forall mem mem' caps caps' a,
        ReachableRWAddr mem' caps' a ->
        ValidMemUpdate mem caps mem' ->
        ReachableCaps mem caps caps' ->
        ReachableRWAddr mem caps a .
    Proof.
      cbv[ReachableRWAddr]. intros; destruct_products.
      destruct H; [ left; by (eapply ReachableReadAddr_ValidUpdate) | right; by (eapply ReachableWriteAddr_ValidUpdate) ].
    Qed.

    (** A reachable address stays reachable from a larger source set. *)
    Lemma ReachableAddrSubset:
      forall caps' mem addr sz p cs cbs caps,
        ReachableAddr mem caps' addr sz p cs cbs ->
        Subset caps' caps ->
        ReachableAddr mem caps addr sz p cs cbs.
    Proof.
      cbv[Subset].
      intros. inv H.
      constructor; auto.
      eapply ReachableCapIncrease; eauto.
    Qed.

      (** The same for [ReachableRWXAddr]. *)
      Lemma ReachableRWXAddrSubset:
        forall mem caps addr caps',
          ReachableRWXAddr mem caps' addr ->
          Subset caps' caps ->
          ReachableRWXAddr mem caps addr.
      Proof.
        cbv[ReachableRWXAddr]. 
        intros. destruct_products.
        do 3 eexists; split; eauto; eapply ReachableAddrSubset; eauto.
      Qed.

    (** The list form of [ReachableCap_ValidUpdate]. *)
    Lemma ReachableCaps_ValidUpdate:
      forall mem mem' caps caps' cs,
      ValidMemUpdate mem caps mem' ->
      ReachableCaps mem caps caps' ->
      ReachableCaps mem' caps' cs ->
      ReachableCaps mem caps cs.
    Proof.
      cbv[ReachableCaps].
      intros * hupdate hcaps hcaps' * hcaps0.
      pose proof (hcaps' _ hcaps0) as hc'.
      eapply ReachableCap_ValidUpdate; eauto.
    Qed.

    (** [ReachableCapSubset] is preserved by a valid update of the current memory authorized by
        the current capabilities, when the new capabilities are reachable from them: the
        monotonicity step for the running thread. *)
    Lemma ReachableCapSubset_ValidUpdate:
      forall mem0 mem mem' caps0 caps caps',
      ReachableCapSubset mem0 mem caps0 caps ->
      ValidMemUpdate mem caps mem' ->
      ReachableCaps mem caps caps' ->
      ReachableCapSubset mem0 mem' caps0 caps'.
    Proof.
      cbv[ReachableCapSubset].
      intros * hinit hmem hcaps.
      pose proof (hinit _ hcaps) as hcaps0'.
      intros * hcaps'.
      specialize ReachableCaps_ValidUpdate with (1 := hmem) (2 := hcaps) (3 := hcaps'); auto.
    Qed.

    (** Store permission for an address is monotonic in the authorizing set. *)
    Lemma StPermForAddrSubset:
      forall mem caps caps' capa a size ,
        StPermForAddr mem caps capa a size ->
        Subset caps caps' ->
        StPermForAddr mem caps' capa a size.
    Proof.
      cbv[StPermForAddr].
      intros. destruct_products.
      split_and!; auto.
      eapply ReachableCapIncrease; eauto.
    Qed.

    (** Store permission for a capability is monotonic in the authorizing set. *)
    Lemma StPermForCapSubset:
      forall mem caps caps' addr capa,
        StPermForCap mem caps addr capa ->
        Subset caps caps' ->
        StPermForCap mem caps' addr capa.
    Proof.
      cbv[StPermForCap].
      intros. destruct_products. split; auto.
      eapply StPermForAddrSubset; eauto.
    Qed.

    (** A valid tag removal stays valid for a larger authorizing set. *)
    Lemma ValidMemTagRemovalSubset:
      forall mem mem' caps caps',
        ValidMemTagRemoval mem caps mem' ->
        Subset caps caps' ->
        ValidMemTagRemoval mem caps' mem'.
    Proof.
      cbv[ValidMemTagRemoval].
      intros. specialize H with (1 := H1) (2 := H2). destruct_products.
      eexists. eapply StPermForCapSubset; eauto.
    Qed.

    (** A valid data update stays valid for a larger authorizing set. *)
    Lemma ValidMemDataUpdateSubset:
      forall mem mem' caps caps',
        ValidMemDataUpdate mem caps mem' ->
        Subset caps caps' ->
        ValidMemDataUpdate mem caps' mem'.
    Proof.
      cbv[ValidMemDataUpdate].
      intros. specialize H with (1 := H1). destruct_products.
      eexists. eapply StPermForAddrSubset; eauto.
    Qed.

    (** A valid capability update stays valid for a larger authorizing set. *)
    Lemma ValidMemCapUpdateSubset:
      forall mem mem' caps caps',
        ValidMemCapUpdate mem caps mem' ->
        Subset caps caps' ->
        ValidMemCapUpdate mem caps' mem'.
    Proof.
      cbv[ValidMemCapUpdate].
      intros * hupdate subset * hcap htag.
      specialize hupdate with (1 := hcap) (2 := htag).
      destruct_products. split; eauto.
      - eapply ReachableCapIncrease; eauto.
      - eexists; split; eauto.
        eapply StPermForCapSubset; eauto.
    Qed.

    (** A valid memory update stays valid for a larger authorizing set. *)
    Lemma ValidMemUpdateSubset:
      forall mem mem' caps caps',
        ValidMemUpdate mem caps mem' ->
        Subset caps caps' ->
        ValidMemUpdate mem caps' mem'.
    Proof.
      cbv[ValidMemUpdate].
      intros * hsubset hupdate. destruct_products.
      split_and!; by (eapply ValidMemCapUpdateSubset || eapply ValidMemTagRemovalSubset || eapply ValidMemDataUpdateSubset).
    Qed.

    (** A slot that reads as a capability has its tag set. *)
    Lemma readCapImpliesTag:
      forall mem capa cap,
        readCap mem capa = inl cap ->
        readTag mem capa = true.
    Proof.
      cbv[readCap readTag readMemTagCap bytesToCap].
      intros *. case_match; try congruence.
      rewrite andb_true_iff in *. destruct_products; auto.
    Qed.

  End MemUpdateLemmas.

  (** A memory update authorized by capabilities whose writable addresses are disjoint from the
      readable addresses of a set [t] makes nothing new reachable from [t]: everything reachable
      from [t] afterwards was reachable before.  This is the new-to-old direction only; tag
      removal may remove old paths, so the converse is not claimed.  These lemmas are what makes
      one thread's step harmless to the others in the main theorem. *)
  Section SeparationLemmas.

    (** [RWAddressesDisjoint] is symmetric. *)
    Lemma RWAddressDisjointUpdate_symmetry:
      forall mem xi xj,
      RWAddressesDisjoint mem xi xj <->
      RWAddressesDisjoint mem xj xi.
    Proof.
      cbv[RWAddressesDisjoint].
      intuition eauto.
    Qed.

    (** Read/write disjointness implies write/read disjointness. *)
    Lemma RWAddressesDisjointImpliesWriteReadDisjoint:
      forall mem xi xj,
      RWAddressesDisjoint mem xi xj ->
      WriteReadDisjoint mem xi xj.
    Proof.
      cbv[RWAddressesDisjoint WriteReadDisjoint ReachableRWAddr].
      intros. eapply H; eauto.
    Qed.

    (** Under [WriteReadDisjoint], no address is both in the bounds of an unsealed storing
        capability reachable from [caps] and in those of an unsealed loading capability reachable
        from [caps']. *)
    Lemma WriteReadDisjointImpliesFalse:
      forall mem caps caps' x y a,
      WriteReadDisjoint mem caps caps' ->
      ReachableCap mem caps x ->
      ReachableCap mem caps' y ->
      capSealed x = None ->
      capSealed y = None ->
      In Perm.Store (capPerms x) ->
      In Perm.Load (capPerms y) ->
      In a (capAddrs x) ->
      In a (capAddrs y) ->
      False.
    Proof.
      cbv [WriteReadDisjoint ReachableWriteAddr ReachableReadAddr].
      intros * hdisjoint hx hy hsealx hsealy hstorex hloady hax hay.
      specialize (hdisjoint a).
      apply hdisjoint;
        repeat eexists; eauto;
        unfold Subset; cbn; intuition; subst; auto.
    Qed.

    (** A load through [x] in the updated memory was the same load in the old memory, when the
        update was authorized by capabilities whose writes are disjoint from [t]'s reads. *)
    Lemma LoadCapUpdateDisjointUnchanged:
      forall mem caps mem' x y z t,
        ReachableCap mem' t x ->
        LoadCap mem' x y z ->
        ValidMemCapUpdate mem caps mem' ->
        WriteReadDisjoint mem caps t ->
        ReachableCap mem t x ->
        LoadCap mem x y z.
    Proof.
      intros * hauth' hload hupdate hdisjoint hauth.
      inv hload. destruct_products. constructor; eauto.
      eexists; split; eauto.
      unfold ValidMemCapUpdate in *.
      specialize hupdate with (capa := capa) (stDataCap := y) (2 := loadFromAuthr).
      destruct (CapOrBytes_eq_dec (readCap mem capa) (inl y) ) as [Heq | Hneq]; auto.
      exfalso.
      rewrite loadFromAuthr in *. propositional.
      destruct_products.
      consider StPermForCap. consider StPermForAddr. destruct_products.
      pose proof ISA_CAPSIZE_BYTES_NONZERO.
      destruct ISA_CAPSIZE_BYTES eqn:?; [lia | ].
      eapply WriteReadDisjointImpliesFalse with (x := stAddrCap) (y := x) (a := (fromCapAddr capa));eauto.
      all: match goal with
      | H: Subset _ ?x |- In _ ?x =>
          eapply H
      end; constructor; auto.
    Qed.

    (** A capability reachable from [t] in the updated memory was reachable from [t] before. *)
    Lemma ReachableCapDisjointUnchanged':
      forall mem caps mem' t c,
        ReachableCap mem' t c ->
        ValidMemCapUpdate mem caps mem' ->
        WriteReadDisjoint mem caps t ->
        ReachableCap mem t c.
    Proof.
      induction 1; intros * hupdate hdisjoint; propositional.
      - apply Refl; auto.
      - eapply StepRestrict; eauto.
      - eapply StepLoadCap; eauto.
        eapply LoadCapUpdateDisjointUnchanged with (mem' := mem') (mem := mem); eauto.
      - eapply StepSeal with (3:= xyz); auto.
      - eapply StepUnseal with (3:= xyz); auto.
    Qed.

    (** The same for a reachable address. *)
    Lemma ReachableAddrDisjointUnchanged:
      forall mem caps mem' t a sz p cs cbs,
        ReachableAddr mem' t a sz p cs cbs ->
        ValidMemCapUpdate mem caps mem' ->
        WriteReadDisjoint mem caps t ->
        ReachableAddr mem t a sz p cs cbs.
    Proof.
      intros * haddr hupdate hdisjoint.
      inv haddr. constructor; auto.
      eapply ReachableCapDisjointUnchanged'; eauto.
    Qed.

    (** The same for a readable address. *)
    Lemma ReachableReadAddrDisjointUnchanged:
      forall mem caps mem' t a,
        ReachableReadAddr mem' t a  ->
        ValidMemCapUpdate mem caps mem' ->
        WriteReadDisjoint mem caps t ->
        ReachableReadAddr mem t a.
    Proof.
      cbv[ReachableReadAddr].
      intros. destruct_products. do 3 eexists; split; eauto.
      eapply ReachableAddrDisjointUnchanged; eauto.
    Qed.

    (** The same for a writable address. *)
    Lemma ReachableWriteAddrDisjointUnchanged:
      forall mem caps mem' t a,
        ReachableWriteAddr mem' t a  ->
        ValidMemCapUpdate mem caps mem' ->
        WriteReadDisjoint mem caps t ->
        ReachableWriteAddr mem t a.
    Proof.
      cbv[ReachableWriteAddr].
      intros. destruct_products. do 3 eexists; split; eauto.
      eapply ReachableAddrDisjointUnchanged; eauto.
    Qed.

    (** The same for an address readable or writable. *)
    Lemma ReachableRWAddrDisjointUnchanged:
      forall mem caps mem' t a,
        ReachableRWAddr mem' t a  ->
        ValidMemCapUpdate mem caps mem' ->
        WriteReadDisjoint mem caps t ->
        ReachableRWAddr mem t a.
    Proof.
      cbv[ReachableRWAddr].
      intros * haddr hupdate hdisjoint.
      destruct haddr.
      - left. eapply ReachableReadAddrDisjointUnchanged; eauto.
      - right. eapply ReachableWriteAddrDisjointUnchanged; eauto.
    Qed.

    (** Read/write disjointness between the updating set and another is preserved by a valid
        update, for the updater's new capabilities. *)
    Lemma RWAddressDisjointUpdate:
      forall mem mem' xi xi' xj,
      ValidMemUpdate mem xi mem' ->
      ReachableCaps mem xi xi' ->
      RWAddressesDisjoint mem xi xj ->
      RWAddressesDisjoint mem' xi' xj.
    Proof.
      intros * hmem hreachable hdisjoint.
      destruct_products.
      cbv[RWAddressesDisjoint].
      intros * hcapi hcapj.
      eapply hdisjoint.
      - eapply ReachableRWAddr_ValidUpdate with (3 := hreachable) (2 := hmem); eauto.
      - unfold ValidMemUpdate in *. destruct_products.
        eapply ReachableRWAddrDisjointUnchanged with (mem := mem) (mem' := mem') (t:= xj); eauto.
        eapply RWAddressesDisjointImpliesWriteReadDisjoint; eauto.
    Qed.

    (** Read/write disjointness between two sets is preserved by a valid update authorized by a
        third set disjoint from both. *)
    Lemma RWAddressDisjointUpdateUnchanged:
      forall mem mem' xi xj xk,
      ValidMemUpdate mem xk mem' ->
      RWAddressesDisjoint mem xi xj ->
      RWAddressesDisjoint mem xi xk ->
      RWAddressesDisjoint mem xj xk ->
      RWAddressesDisjoint mem' xi xj.
    Proof.
      cbv[ValidMemUpdate].
      intros * hmem hdisjointij hdisjointik hdisjointjk. destruct_products.
      intros a hcapi hcapj.
      eapply ReachableRWAddrDisjointUnchanged with (mem := mem) (mem' := mem') (t:= xj) in hcapj; eauto.
      eapply ReachableRWAddrDisjointUnchanged with (mem := mem) (mem' := mem') (t:= xi) in hcapi; eauto.
      all: rewrite RWAddressDisjointUpdate_symmetry in *;
           try solve[eapply RWAddressesDisjointImpliesWriteReadDisjoint; eauto].
    Qed.

    (** [ReachableCapSubset] for a set [t] survives a valid update (tag removal and capability
        stores) authorized by capabilities whose writes are disjoint from [t]'s reads. *)
    Lemma ReachableCapSubsetDisjointUnchanged':
      forall mem0 mem mem' t0 t caps,
      ReachableCapSubset mem0 mem t0 t ->
      ValidMemTagRemoval mem caps mem' ->
      ValidMemCapUpdate mem caps mem' ->
      WriteReadDisjoint mem caps t ->
      ReachableCapSubset mem0 mem' t0 t.
    Proof.
      cbv[ReachableCapSubset ReachableCaps].
      intros * hinit htag hupdate hdisjoint.
      intros * hcapsIn * hin.
      eapply ReachableCapSubsetImpliesReachableCap; eauto.
      specialize hcapsIn with (1 := hin).
      eapply ReachableCapDisjointUnchanged'; eauto.
    Qed.

    (** The same under the whole [ValidMemUpdate]: the monotonicity step for an idle thread. *)
    Lemma ReachableCapSubsetUpdateDisjointUnchanged:
      forall mem0 mem mem' t0 t caps,
      ReachableCapSubset mem0 mem t0 t ->
      ValidMemUpdate mem caps mem' ->
      WriteReadDisjoint mem caps t ->
      ReachableCapSubset mem0 mem' t0 t.
    Proof.
      cbv[ValidMemUpdate].
      intros; destruct_products; by (eapply ReachableCapSubsetDisjointUnchanged').
    Qed.

    (** The same as [RWAddressesDisjointImpliesWriteReadDisjoint]. *)
    Lemma RWDisjointImpliesWriteReadDisjoint:
      forall m xi xj,
      RWAddressesDisjoint m xi xj ->
      WriteReadDisjoint m xi xj.
    Proof.
      cbv [RWAddressesDisjoint WriteReadDisjoint ReachableRWAddr].
      intros. eapply H; eauto.
    Qed.
  End SeparationLemmas.

  (** A thread's user-state capabilities are among its capabilities. *)
  Section CapsOf.

    (** The PCC and the register file's capabilities are among what [capsOfThread] lists. *)
    Lemma SubsetCapsOfUserTS:
      forall (thread: Thread), 
        Subset (capsOfUserTS (thread_userState thread)) (capsOfThread thread).
    Proof.
      cbv[Subset capsOfThread].
      intros. rewrite in_app_iff. auto. 
    Qed.          

  End CapsOf.


  (** What the well-formedness of an instruction ([Spec]) gives for a successful execution. *)
  Section WFInstructionLemmas.

    (** A register file updated at one in-range index with a value stays valid. *)
    Lemma ValidRfUpdate:
      forall rf rf' v idx,
        ValidRf rf ->
        (forall n, n <> idx -> nth_error rf' n = nth_error rf n) ->
        idx < length rf ->
        nth_error rf' idx = Some v ->
        ValidRf rf'.
    Proof.
      cbv[ValidRf]. intros * hrf hsame hlen hsome.
      rewrite<-hrf. symmetry.
      eapply listUpdate_length; eauto.
    Qed.

    (** A well-formed general instruction that succeeds performs a valid memory update, keeps its
        capabilities reachable from the ones it started with (user and system state together),
        runs and ends with an executable PCC, and keeps the register file valid. *)
    Lemma generalInstOkCommon:
      forall userSt mem sysSt istatus userSt' mem' sysSt' istatus' generalInst,
        WfGeneralInst generalInst ->
        generalInst (userSt, mem) (sysSt, istatus) = Ok (userSt', mem', (sysSt', istatus')) ->
        ValidRf (thread_rf userSt) ->
        let caps := (capsOfUserTS userSt ++ capsOfSystemTS sysSt) in
        let caps' := (capsOfUserTS userSt' ++ capsOfSystemTS sysSt') in
        ValidMemUpdate mem caps mem' /\
          ReachableCaps mem caps caps' /\
          In Perm.Exec (thread_pcc userSt).(capPerms) /\
          In Perm.Exec (thread_pcc userSt').(capPerms) /\
          ValidRf (thread_rf userSt').
    Proof.
      cbv[WfGeneralInst WfSystemInst WfNormalInst].
      intros * [hwf_user hwf_sys] hinst hpre.
      destruct (in_dec Perm.t_eq_dec Perm.System (capPerms (thread_pcc userSt)));
        [ clear hwf_user; rename i into hmode| clear hwf_sys].
      - specialize hwf_sys with (1 := hmode) (2 := hpre) (mem := mem)
                                (mepcc := thread_mepcc sysSt)
                                (mtcc := thread_mtcc sysSt)
                                (exnInfo := thread_exceptionInfo sysSt)
                                (ts := thread_trustedStack sysSt) (ints := istatus)
                                (stat := thread_alive sysSt).
        setoid_rewrite hinst in hwf_sys. destruct_products. auto.
      - cbv[capsOfUserTS capsOfSystemTS]. destruct_products.
        specialize hwf_userl with (1 := hpre) (pcc := thread_pcc userSt) (mem := mem).
        specialize hwf_userr with (1 := n) (rf := thread_rf userSt) (mem := mem) (sysCtx := (sysSt, istatus)).
        destruct userSt. cbv [Spec.thread_rf Spec.thread_pcc] in *.
        rewrite hinst in hwf_userr.
        simplify_Result. destruct_products; simplify_eq.
        split_and!; auto.
        + eapply ValidMemUpdateSubset; eauto. simplify_Subset.
        + apply ReachableCaps_app. auto.
    Qed.

    (** A well-formed call that succeeds keeps the register file valid and installs an executable
        PCC. *)
    Lemma callSentryOkCommon:
      forall callSentryInst srcReg optLink userSt mem istatus pcc' rf' istatus',
        WfCallSentryInst callSentryInst srcReg optLink ->
        callSentryInst (userSt, mem) istatus = Ok (pcc', rf', istatus') ->
        ValidRf (thread_rf userSt) ->
        ValidRf rf' /\
        In Perm.Exec pcc'.(capPerms).
    Proof.
      cbv[WfCallSentryInst].
      intros * hwf hinst hpre.
      specialize hwf with (1 := hpre) (pcc := thread_pcc userSt) (ints := istatus) (mem := mem).
      setoid_rewrite hinst in hwf.
      destruct_products. simplify_eq.
      split; auto.
      destruct optLink eqn:?; simplify_eq; auto.
      destruct_products.
      eapply ValidRfUpdate with (idx := n) (1 := hpre); eauto.
      rewrite hpre. auto.
    Qed.

  End WFInstructionLemmas.

  (** What a same-thread step keeps, under the fetch, decode and trap parameters of
      [MachineStep]. *)
  Section Step.
    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> @Inst _ _ capEncodeDecode}.
    Context {pccNotInBounds : EXNInfo}.
    Abbreviation MachineStep := (MachineStep fetchAddrs decode pccNotInBounds).
    Abbreviation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
    Abbreviation ThreadStep := (ThreadStep fetchAddrs decode pccNotInBounds).

    (** A same-thread step keeps the number of threads, when the current index is in range. *)
    Lemma SameThreadStep_lengthThreads:
      forall m1 m2 ev,
        machine_curThreadId m1 < length (machine_threads m1) ->
        SameThreadStep m1 m2 ev ->
        length (machine_threads m1) = length (machine_threads m2).
    Proof.
      intros * hlen hstep.
      inv hstep. destruct_products.
      eapply listUpdate_length; eauto.
      rewrite<-threadIdEq. eauto.
    Qed.

    (** A same-thread step from a machine whose current index is in range leaves it in range. *)
    Lemma SameThreadStep_curId:
      forall m1 m2 ev,
        machine_curThreadId m1 < length (machine_threads m1) ->
        SameThreadStep m1 m2 ev ->
        machine_curThreadId m2 < length (machine_threads m2).
    Proof.
      intros * hlen hstep.
      pose proof (SameThreadStep_lengthThreads _ _ _ hlen hstep) as hlen'.
      inv hstep; destruct_products.
      rewrite threadIdEq. lia.
    Qed.
  End Step.
End WithContext.

Hint Resolve RestrictSetCapUnsealed: ReachableCap.


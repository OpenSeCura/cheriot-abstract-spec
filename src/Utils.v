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

(*! Utils *)
From Stdlib Require Import List Lia Bool Nat NArith.
From cheriot Require Import Tactics.
Import ListNotations.

(** * Utilities

    General definitions, lemmas and tactics the other files use: the temporal combinators
    [always] and [until], equality and inclusion of lists as sets, the [Result] type of an
    instruction's outcome, lemmas on [option], [Forall] and [Forall2], on list updates and on
    [listSumToInl], and the separation predicates of [Separation]. *)

(** [EqDecider f] says that [f] decides equality on its type: [f x y] reflects [x = y].  The
    capability and memory-value equality tests of [CapEncodeDecode] ([Spec]) are required to be
    deciders. *)
Abbreviation EqDecider f := (forall x y, BoolSpec (x = y) (x <> y) (f x y)).

(** ** Temporal combinators

    Two proof shapes over an arbitrary step relation, used to state the results of
    [Properties]: [always], the inductive-invariant shape of the main theorem, and [until], the
    shape of the switcher contracts. *)
Module Combinators.

  (** Binds the step relation the two combinators are defined over. *)
  Section __.
    Context [State : Type] (step: State -> State -> Prop).

    (** [P] holds in every state reachable from [initial] by [step].  The only way to prove it is
        by an invariant: it holds initially ([Establish]), every step preserves it ([Preserve]),
        and it implies [P] ([Use]).  [ThreadIsolatedMonotonicity] in [Properties] is stated with
        it. *)
    Inductive always(P: State -> Prop)(initial: State): Prop :=
    | mk_always
        (invariant: State -> Prop)
        (Establish: invariant initial)
        (Preserve: forall s t, invariant s -> step s t -> invariant t)
        (Use: forall s, invariant s -> P s).

    (* P until Q *)

    (** [P] holds until [Q] does, along every path of [step] from [initial]: either [Q] holds now
        ([until_done]), or [P] holds now and every successor satisfies [until] again
        ([until_step]).  Because the definition is inductive, a proof is a finite derivation, so
        [until P Q initial] also says that every maximal path from [initial] reaches a [Q]-state,
        or a state satisfying [P] with no successor, after finitely many steps.  The switcher
        contracts in [Properties] are stated with it: in system mode under an invariant until
        back in user mode with the postcondition.  A commented-out [eventually] follows. *)
    Inductive until (P: State -> Prop) (Q: State -> Prop) (initial: State) : Prop :=
    | until_done:
      Q initial ->
      until P Q initial
    | until_step:
      P initial ->
      (forall mid, step initial mid -> until P Q mid) ->
      until P Q initial.

    (* Inductive eventually(P: State -> Prop)(initial: State): Prop := *)
    (* | eventually_done: *)
    (*       P initial -> *)
    (*       eventually P initial *)
    (* | eventually_step: *)
    (*       (forall mid, step initial mid -> eventually P mid) -> *)
    (*       eventually P initial. *)
  End __.
End Combinators.




(** Equality and inclusion of two lists seen as sets. *)
Section EqSet.
  Context [A: Type].
  Variable l1 l2: list A.

  (** The two lists have the same members. *)
  Definition EqSet := forall x, In x l1 <-> In x l2.

  (** Equal lists are equal as sets. *)
  Theorem Eq_imp_EqSet: l1 = l2 -> EqSet.
  Proof.
    unfold EqSet; intros; subst; tauto.
  Qed.

  (** Every member of [l1] is a member of [l2].  Permission, label, key and address lists are
      compared with it throughout. *)
  Definition Subset := forall x, In x l1 -> In x l2.

End EqSet.

(** What an instruction's semantic function returns: a result ([Ok]) or an exception payload
    ([Exn]; [ExnInfo] in [Spec]).  [Result e t] takes the exception and result types
    explicitly. *)
Inductive Result {e t} :=
| Ok : t -> Result
| Exn : e -> Result.
Arguments Result : clear implicits.

(** Case on a [Result] scrutinee whose [Exn] branch is [False], keeping the [Ok] case. *)
Ltac simplify_Result :=
  repeat match goal with
  | H: match ?x with | Ok _ => _ | Exn _ => False end |- _ =>
      let Ht := fresh H "Ok" in
      destruct x eqn:Ht; [ | contradiction]
  end.

(** Lemmas and helpers on [option]. *)
Section Option.

  (** Whether an option holds a value. *)
  Definition is_some [A] (a: option A) : bool :=
    match a with
    | Some _ => true
    | _ => false
    end.


  (** [Some] is injective. *)
  Lemma Some_inj :
    forall A (x y:A),
    Some x = Some y ->
    x = y.
  Proof.
    intros. inversion H. auto.
  Qed.

  (** An [option_map] that yields [Some b] was applied to [Some a] with [f a = b]. *)
  Lemma option_map_Some:
    forall {A B} (f: A -> B) xs b,
    option_map f xs = Some b ->
    exists a, xs = Some a /\ f a = b.
  Proof.
    cbv[option_map]. intros *. destruct xs; intros;
      repeat match goal with
      | H : Some ?x = Some _ |- _ => apply Some_inj in H; simplify_eq
      | H : None = Some _ |- _ => clear - H; discriminate
      end; eauto.
  Qed.

  (** An option equal to [Some a] is not [None]. *)
  Lemma Some_not_None :
    forall A (a: A) x,
      x = Some a ->
      x <> None.
  Proof.
    destruct x; congruence.
  Qed.

  (** Apply [f] to the value of an option, or return the default [y]. *)
  Definition from_option {A B} (f : A -> B) (y : B) (mx : option A) : B :=
    match mx with None => y | Some x => f x end.

End Option.

(** Resolve equalities between [Some] and [None] in the hypotheses: inject, rewrite,
    discriminate. *)
Ltac option_simpl :=
  repeat match goal with
  | H : Some ?x = Some _ |- _ => apply Some_inj in H; simplify_eq
  | H : ?x = Some ?y, H1 : ?x = Some ?z |- _ => rewrite H in H1; apply Some_inj in H1; try subst y; try subst z
  | H : None = Some _ |- _ => clear - H; discriminate
  | H : Some _ = None  |- _ => clear - H; discriminate
  end.

(** Lemmas on [Forall] and [Forall2], indexed access in particular. *)
Section Forall.

  (** [Forall] over a singleton. *)
  Lemma Forall_one:
    forall {T} (x: T) P,
    Forall P [x] ->
    P x.
  Proof.
    inversion 1. auto.
  Qed.

  (** A reflexive relation holds pointwise between a list and itself. *)
  Lemma Forall2_refl {A: Type} (R: A -> A -> Prop) :
    forall xs,
    (forall a, R a a) ->
    Forall2 R xs xs.
  Proof.
    induction xs; auto.
  Qed.

  (** Two lists of the same length related at every index are [Forall2]-related. *)
  Lemma Forall2_nth_error1 : forall A B (R: A -> B -> Prop) xs ys,
      length xs = length ys ->
      (forall idx x y, nth_error xs idx = Some x ->
                  nth_error ys idx = Some y ->
                  R x y) ->
      Forall2 R xs ys.
  Proof.
    induction xs.
    - destruct ys; try discriminate; auto.
    - destruct ys; try discriminate.
      intros; constructor; eauto.
      + eapply H0 with (idx := 0); eauto.
      + eapply IHxs; eauto.
        intros; eapply H0 with (idx := S idx); auto.
  Qed.

  (** [Forall2]-related lists are related at every index. *)
  Lemma Forall2_nth_error2 : forall A B (R: A -> B -> Prop) xs ys,
      Forall2 R xs ys ->
      forall idx x y,
      nth_error xs idx = Some x ->
      nth_error ys idx = Some y ->
      R x y.
  Proof.
    induction 1.
    - intros *; rewrite nth_error_nil. discriminate.
    - destruct idx; cbn; intros;
        repeat match goal with
        | H: Some _ = Some _ |- _ => apply Some_inj in H; subst
        end; eauto.
  Qed.

  (** The existence form of the previous lemma: at an index below the length, both elements
      exist and are related. *)
  Lemma Forall2_nth_error2' : forall A B (R: A -> B -> Prop) xs ys idx,
      Forall2 R xs ys ->
      idx < length xs ->
      exists x y,
      nth_error xs idx = Some x /\
      nth_error ys idx = Some y /\
      R x y.
  Proof.
    intros.
    destruct (nth_error xs idx) eqn:?.
    destruct (nth_error ys idx) eqn:?.
    - exists a; exists b; repeat split; auto.
      eapply Forall2_nth_error2; eauto.
    - apply nth_error_None in Heqo0. rewrite Forall2_length with (1 := H) in H0. lia.
    - apply nth_error_None in Heqo. lia.
  Qed.
End Forall.

(** Split [Forall] over an append and over a singleton in the hypotheses. *)
Ltac simplify_Forall :=
  repeat match goal with
  | H : Forall _ (_ ++ _ ) |- _ =>
      apply Forall_app in H;
      let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | H : Forall _ [_] |- _ =>
      apply Forall_one in H
  end.


(** Lemmas on [Subset]. *)
Section Subset.

  (** Filtering [ys] by membership in [xs], through a sound equality test, yields a subset of
      [xs]. *)
  Lemma SubsetFilter1:
    forall {A} (xs ys: list A) eqb,
    (forall p q, eqb p q = true -> p = q) ->
    Subset (filter (fun p => existsb (eqb p) xs) ys) xs.
  Proof.
    cbv[Subset]. intros * eqb *.
    rewrite filter_In, existsb_exists.
    intros; destruct_products; eauto.
    apply eqb in Hrr. subst; auto.
  Qed.

  (** A list is a subset of itself extended on the right. *)
  Lemma Subset_app:
    forall {A} (xs ys: list A),
      Subset xs (xs ++ ys).
  Proof.
    cbv[Subset].
    intros. apply in_or_app. auto.
  Qed.

  (** [Subset] is reflexive. *)
  Lemma Subset_refl :
    forall {A} (xs: list A),
      Subset xs xs.
  Proof.
    cbv[Subset]. auto.
  Qed.
End Subset.

(** Close [Subset] goals of the two shapes above. *)
Ltac simplify_Subset :=
  repeat match goal with
    | |- Subset ?x (?x ++ _) =>
        apply Subset_app
    | |- Subset ?x ?x =>
        apply Subset_refl
    end.

(** A list updated at one index keeps its length. *)
Section ListUpdate.

  (** If [ys] agrees with [xs] everywhere except at [idx], where [xs] is defined and [ys] holds a
      value, the two lists have the same length. *)
  Lemma listUpdate_length:
    forall A (xs ys: list A) idx a,
      (forall n, n <> idx -> nth_error ys n = nth_error xs n) ->
      idx < length xs ->
      nth_error ys idx = Some a ->
      length xs = length ys.
  Proof.
    intros * herror hlen hsome.
    destruct (PeanoNat.Nat.eq_dec (length xs) (length ys)); auto.
    exfalso.
    assert (length xs < length ys \/ length ys < length xs) as Hcase by lia.
    destruct_or! Hcase; exfalso.
    - rewrite<-nth_error_Some in Hcase.
      rewrite herror in Hcase by lia.
      rewrite nth_error_Some in Hcase. lia.
    - destruct_with_eqn (Nat.ltb idx (length ys)).
      + rewrite PeanoNat.Nat.ltb_lt in *.
        rewrite<-nth_error_Some in Hcase.
        rewrite<-herror in Hcase by lia.
        rewrite nth_error_Some in Hcase. lia.
      + rewrite PeanoNat.Nat.ltb_nlt in *.
        apply Some_not_None in hsome.
        apply nth_error_Some in hsome. lia.
  Qed.
End ListUpdate.

(** An index at which [nth_error] succeeds is below the length. *)
Lemma nth_error_Some' :
  forall [A: Type] (l: list A) (n: nat) (a: A),
    nth_error l n = Some a ->
    n < length l.
Proof.
  intros. eapply nth_error_Some. by eapply Some_not_None.
Qed.

(** Add to the context what every [nth_error ... = Some] and every [Forall2] hypothesis
    implies: the index bound, membership, and equal lengths. *)
Ltac saturate_list:=
  repeat match goal with
  | H: nth_error ?xs ?idx = Some _ |- _ =>
      let H' := fresh H "len" in 
      learn_hyp (nth_error_Some' _ _ _ H) as H'
  | H: nth_error ?xs ?idx = Some _ |- _ =>
      let H' := fresh H "In" in 
      learn_hyp (nth_error_In _ _ H) as H'
  | H: Forall2 _ _ _ |- _ =>
      let H' := fresh H "len" in 
      learn_hyp (Forall2_length H) as H'
    end.

(** [saturate_list], then an [nth_error] witness for every membership hypothesis that has
    none; "unsafe" because the new index is existential and may not be the one a proof needs. *)
Ltac unsafe_saturate_list :=
  saturate_list;
  repeat match goal with
  | H: In ?xs ?x |- _ =>
      lazymatch goal with
      | H': nth_error xs _ = Some x |- _ => fail 1
      | |- _ =>
          let H' := fresh H "nth_error" in
          learn_hyp (In_nth_error _ _ H) as H'
      end
  end.


(** The [inl] members of a list of sums, in order.  [capsOfRf] in [Spec] uses it to pick the
    capabilities out of a register file, whose entries are capabilities or bytes. *)
Fixpoint listSumToInl [A B: Type] (l: list (A+B)) : list A :=
  match l with
  | nil => nil
  | x :: xs => match x with
               | inl y => y :: listSumToInl xs
               | _ => listSumToInl xs
               end
  end.

(** An [inl] member of the list is a member of its [listSumToInl]. *)
Lemma In_listSumToInl:
  forall A B (xs: list (A+B)) x,
  In (inl x) xs ->
  In x (listSumToInl xs).
Proof.
  induction xs; cbn; auto.
  intros * H. inv H; subst; auto.
  - constructor. auto.
  - apply IHxs in H0. case_match; [right | ]; auto.
Qed.

(** The converse: a member of [listSumToInl xs] is an [inl] member of [xs]. *)
Lemma listSumToInl_In:
  forall A B (xs: list (A+B)) x,
  In x (listSumToInl xs) ->
  In (inl x) xs.
Proof.
  induction xs; cbn; auto.
  intros. case_match; subst.
  - inv H; auto.
  - apply IHxs in H. auto.
Qed.

(** The two directions as an equivalence. *)
Lemma listSumToInl_iff:
  forall A B (xs: list (A+B)) x,
  In x (listSumToInl xs) <->
  In (inl x) xs.
Proof.
  split.
  - apply listSumToInl_In.
  - apply In_listSumToInl.
Qed.

(** A number [v] with [b <= v < b + n] is a member of [seq b n]. *)
Theorem seqInBounds n: forall b v,
    b <= v < b + n -> In v (seq b n).
Proof.
  induction n; simpl; intros.
  - lia.
  - destruct (PeanoNat.Nat.eq_dec b v); [auto|right].
    apply IHn.
    lia.
Qed.

(** Turn [Nat.ltb] facts into [<] facts, then [lia]. *)
Ltac simplify_nat :=
  repeat match goal with
  | H: (_ <? _) = true |- _ => rewrite PeanoNat.Nat.ltb_lt in H
  | H: (_ <? _) = false |- _ => rewrite PeanoNat.Nat.ltb_nlt in H
  | _ => lia                                                                       
  end.

(** ** Separation

    Disjointness of lists, and pairwise disjointness over a list of lists.  The isolation
    hypotheses of [Properties] (compartment footprints, threads' reachable addresses) are
    stated with [Separated] and [Pairwise]. *)
Module Separation.

  (** No element in common. *)
  Definition Disjoint {T: Type} (xs ys: list T) : Prop :=
    forall t, In t xs -> In t ys -> False.

  (** [P] holds between the elements at any two distinct indices. *)
  Definition Pairwise {T: Type} (P: T -> T -> Prop) (xss: list T) : Prop :=
    forall i j xi xj,
      i <> j ->
      nth_error xss i = Some xi ->
      nth_error xss j = Some xj ->
      P xi xj.

  (** The members of [xss] are pairwise disjoint. *)
  Definition Separated {T: Type} (xss: list (list T)) : Prop :=
    Pairwise Disjoint xss.

End Separation.

(** Close a goal from a [Separated] hypothesis contradicted by an element shared between two of
    its members at distinct indices. *)
Ltac finish_Separated :=
  match goal with
  | H: Separation.Separated ?xs,
    H1: nth_error ?xs ?t1 = Some ?s1,
    H2: nth_error ?xs ?t2 = Some ?s2,
    H3: In ?addr ?s1,
    H4: In ?addr ?s2,
    H5: ?t1 <> ?t2 |- _ =>
      exfalso; eapply H with (2 := H1) (3 := H2) (4 := H3) (5 := H4);
      solve[option_simpl; auto; lia]
  | _ => progress(option_simpl; lia)
  end.

(** Before [finish_Separated]: when an element is in the members at two indices, case on
    whether the indices are equal. *)
Ltac prepare_Separated :=
  try match goal with
      | H1: nth_error ?xs ?t1 = Some ?s1,
        H2: nth_error ?xs ?t2 = Some ?s2,
        H3: In ?addr ?s1,
        H4: In ?addr ?s2
        |- _ =>
        let Heq := fresh in   
        assert_fresh (t1 = t2) as Heq;
        [ destruct (PeanoNat.Nat.eq_dec t1 t2); [ by auto | ]  | subst ]
    end.

(** [prepare_Separated], then [finish_Separated]. *)
Ltac simplify_Separated :=
  prepare_Separated; try solve[finish_Separated].

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

From Stdlib Require Import String List Lia Bool Nat NArith.

(** * Tactics

    Proof automation used throughout.  Nothing here is specific to the model: hypotheses are
    learned once ([learn_hyp]), equalities simplified ([simplify_eq], [simplify_tuples], [inv]),
    matches, products and disjunctions taken apart ([simpl_match], [case_match],
    [destruct_products], [destruct_or]), conjunctions split ([split_and]), and goals closed
    ([done], [by], [fast_done]).  [mark] records progress in a proof by a [MkMark] hypothesis. *)

(** Add [p] to the context under the name [H'], unless a hypothesis of its type is already there. *)
Tactic Notation "learn_hyp" constr(p) "as" ident(H') :=
  let P := type of p in
  match goal with
  | H : P |- _ => fail 1
  | _ => pose proof p as H'
  end.

(** [learn_hyp] with a fresh name. *)
Tactic Notation "learn_hyp" constr(p) :=
  let H := fresh in learn_hyp p as H.

(** Equal pairs have equal components. *)
Lemma simple_tuple_inversion:
  forall {A} {B} (a: A) (b: B) x y,
  (a,b) = (x,y) ->
  a = x /\ b = y.
Proof.
  intros. inversion H. auto.
Qed.

(** Substitute every equation one side of which is a variable that [subst] accepts, split pair
    equations, and close on [False]. *)
Tactic Notation "simplify_eq" := repeat
  match goal with
  | H : False |- _ => contradiction
  | H : ?x = _ |- _ => subst x
  | H: _ = ?x |- _ => subst x
  | [ H: (_,_) = (_,_) |- _ ] =>
    apply simple_tuple_inversion in H;
    let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  end.

(** Invert [H], clear it, and simplify the equalities it yields. *)
Tactic Notation "inv" ident(H) :=
  inversion H; clear H; simplify_eq.

(** Rewrite the scrutinee of a [match], in the goal or a hypothesis, with an equation from the
    context, so that the match reduces. *)
Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
      repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
      repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
      repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
      repl_match_hyp H d d'
  end.

(** Take apart pairs, conjunctions, existentials and [let '(_, _) :=] patterns in the context
    and the goal. *)
Ltac destruct_products :=
  repeat match goal with
  | p: _ * _  |- _ => destruct p
  | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
  | H: context[let '(_,_) := ?x in _] |- _ =>
    destruct x eqn:?
  | |- context[let '(_,_) := ?x in _] =>
    destruct x eqn:?
  end.

(** Case on the innermost [match] scrutinee of the term [e]. *)
Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in d
  | _ =>
      destruct e eqn:?
  end.

(** The same on the innermost scrutinee of the type of [H]; without a [match] it tries to
    destruct the type of [H] itself, which fails unless that type is an inductive value. *)
Ltac destruct_matches_in_hyp H :=
  lazymatch type of H with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in d
  | ?v =>
      let H1 := fresh H in
      destruct v eqn:H1
  end.

(** Case on the first [match] scrutinee found in a hypothesis or the goal, naming the
    equation. *)
Tactic Notation "case_match" "eqn" ":" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.

(** [case_match] with a fresh equation name. *)
Ltac case_match :=
  let H := fresh in case_match eqn:H.

(** Turn a [Nat.eqb] fact into an equality or a disequality. *)
Ltac simplify_nats :=
  match goal with
  | H: Nat.eqb _ _ = true |- _ =>
      rewrite PeanoNat.Nat.eqb_eq in H
  | H: Nat.eqb _ _ = false |- _ =>
      rewrite PeanoNat.Nat.eqb_neq in H
  end.

(** Close the goal by an assumption, its symmetric form, or reflexivity. *)
Ltac fast_done :=
  solve
    [ eassumption
    | symmetry; eassumption
    | reflexivity ].

(** Run [tac], then [fast_done]. *)
Tactic Notation "fast_by" tactic(tac) :=
  tac; fast_done.

(** Close the goal by the cheap means, repeated: [fast_done], [trivial], introduction,
    [discriminate], [contradiction], splitting. *)
Ltac done :=
  solve
  [ repeat first
    [ fast_done
    | solve [trivial]
    | progress intros
    | solve [symmetry; trivial]
    | discriminate
    | contradiction
    | split
    ]
  ].

(** Run [tac], then [done]. *)
Tactic Notation "by" tactic(tac) :=
  tac; done.

(** Split the disjunctions of [H] into cases, and close the [False] ones. *)
Tactic Notation "destruct_or" "?" ident(H) :=
  repeat match type of H with
  | False => destruct H
  | _ \/ _ => destruct H as [H|H]
  end.

(** [destruct_or?] after unfolding the head of [H], and only if it makes progress. *)
Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

(** [destruct_or?] on every hypothesis. *)
Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.

(** The progress-requiring form over every hypothesis. *)
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.

(** Split a conjunction goal once. *)
Tactic Notation "split_and" :=
  match goal with
  | |- _/\ _ => split
  end.

(** Split conjunction goals repeatedly. *)
Tactic Notation "split_and" "?" := repeat split_and.

(** The same as [split_and?]. *)
Ltac split_ands := repeat split_and.

(** Unfold the head of the goal, then split it and its conjuncts. *)
Tactic Notation "split_and" "!" := hnf; split_and; split_and?.

(** The four [destruct_or] forms above, defined a second time, identically. *)
Tactic Notation "destruct_or" "?" ident(H) :=
  repeat match type of H with
  | False => destruct H
  | _ \/ _ => destruct H as [H|H]
  end.
Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.

(** Unfold [X] everywhere. *)
Ltac consider X :=
  unfold X in *.

(** Discharge the premises of implications in the context from hypotheses that match them. *)
Ltac propositional :=
  repeat match goal with
  | H1: ?x -> _, H2: ?x |- _ =>
      specialize H1 with (1 := H2)
  end.

(** Assert the premise of the implication [H] as a new goal, then specialize [H] with it. *)
Ltac assert_pre_and_specialize H :=
  match type of H with
  | ?x -> _ => let Hx := fresh in assert x as Hx; [ | specialize H with (1 := Hx); clear Hx]
  end.

(** Close the goal by rewriting with some hypothesis, then [congruence] if that closes it, then
    [auto]; the first hypothesis that works is taken. *)
Ltac rewrite_solve :=
  match goal with
  | [ H: _ |- _ ] => solve[rewrite H; try congruence; auto]
  end.

(** Split every pair equation in the context into its component equations. *)
Ltac simplify_tuples :=
  repeat match goal with
  | [ H: (_,_) = (_,_) |- _ ] =>
    apply simple_tuple_inversion in H; destruct H
  end.

(** [simplify_tuples], then substitute. *)
Ltac simplify_tupless := simplify_tuples; subst.

(** Case on every [match] in [H], simplify [H], split the pair equations and substitute, and
    close by [congruence] where possible. *)
Ltac bash_destruct H :=
  repeat destruct_matches_in_hyp H; simpl in H; simplify_tupless; try congruence.

(** Destruct a copy of [H], keeping [H] itself. *)
Ltac destruct_and_save H :=
  let H' := fresh H in
  pose proof H as H';
  destruct H'.

(** A marker type indexed by a string, so that [mark], given [MkMark s], can leave a named,
    otherwise inert hypothesis in the context. *)
Inductive MARK : string -> Type :=
| MkMark : forall s, MARK s.

(** Record [p] in the context as a [Mark] hypothesis, once. *)
Tactic Notation "mark" constr(p) :=
  let H := fresh "Mark" in
  learn_hyp p as H.

(** Assert [P] as [H'] unless a hypothesis of that statement already exists. *)
Tactic Notation "assert_fresh" constr(P) "as" ident(H') :=
  match goal with
  | H : P |- _ => fail 1
  | _ => assert P as H'
  end.

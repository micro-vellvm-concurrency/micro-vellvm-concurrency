From Coq Require Import
     NArith.

From ExtLib Require Import
     Structures.Monads
.

From ITree Require Import
     Basics.CategoryOps
     Core.Subevent
.
From CTree Require Import
     CTree
     Interp.Fold
     Interp.FoldStateT.

From Mem Require Import Utils Events.

Import MonadNotation.


Definition handle_sched_round_robin {E C} :
  SchedC ~> Monads.stateT nat (ctree E (B01 +' C)) :=
  fun _ e s =>
  match e with
  | Sched l => let next := if Nat.eqb s (fold_left max l O) then O else S s in
    ret (next, s)
  end.

Definition handle_sched_random {E C} :
  SchedC ~> Monads.stateT N (ctree E (B01 +' C)) :=
  fun _ e seed =>
  match e with
  | Sched l =>
    let '(seed, rd) := rand seed (N.of_nat (length l)) in
    let next := nth (N.to_nat rd) l O in
    ret (seed, next)
  end.

Section InterpSched.

  Context {E C : Type -> Type}.
  Context {S : Type}.
  Variable handler : SchedC ~> Monads.stateT S (ctree E (B01 +' C)).

  Definition B01_branch b : B01 ~> Monads.stateT S (ctree E (B01 +' C)) :=
    fun _ c m => r <- branch b c ;; ret (m, r).
  Definition C_branch b : C ~> Monads.stateT S (ctree E (B01 +' C)) :=
    fun _ c m => r <- branch b c ;; ret (m, r).

  Definition interp_sched_h b :
    (B01 +' (SchedC +' C)) ~>
    Monads.stateT S (ctree E (B01 +' C)) :=
    case_ (B01_branch b) (case_ handler (C_branch b)).

  Definition interp_sched :
    ctree E (B01 +' (SchedC +' C)) ~> Monads.stateT S (ctree E (B01 +' C)) :=
    refine interp_sched_h.

End InterpSched.

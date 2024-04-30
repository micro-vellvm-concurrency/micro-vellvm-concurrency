From Coq Require Import
     NArith
     ZArith
     String.

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


Definition freeze {E C} `{PickC -< C} v : ctree E C value :=
  match v with
  | Some v => Ret v
  | None => branchD Pick
  end.

Definition force_def {E C T} `{PickC -< C} `{ExceptC T -< C} v (msg: string) (err: T) : ctree E C value :=
  match v with
  | Some v => Ret v
  | None => cthrow err msg
  end.

Definition handle_pick_random {E C} :
  PickC ~> Monads.stateT N (ctree E (B01 +' C)) :=
  fun _ e seed =>
  match e with
  | Pick =>
    let '(seed, rd) := rand seed (N.of_nat 2000) in
    ret (seed, (Z.of_N rd - 1000)%Z)
  end.

Section InterpPick.

  Context {E C : Type -> Type}.
  Context {S : Type}.
  Variable handler : PickC ~> Monads.stateT S (ctree E (B01 +' C)).

  Definition B01_branch b : B01 ~> Monads.stateT S (ctree E (B01 +' C)) :=
    fun _ c m => r <- branch b c ;; ret (m, r).
  Definition C_branch b : C ~> Monads.stateT S (ctree E (B01 +' C)) :=
    fun _ c m => r <- branch b c ;; ret (m, r).

  Definition interp_pick_h b :
    (B01 +' (PickC +' C)) ~>
    Monads.stateT S (ctree E (B01 +' C)) :=
    case_ (B01_branch b) (case_ handler (C_branch b)).

  Definition interp_pick :
    ctree E (B01 +' (PickC +' C)) ~> Monads.stateT S (ctree E (B01 +' C)) :=
    refine interp_pick_h.

End InterpPick.

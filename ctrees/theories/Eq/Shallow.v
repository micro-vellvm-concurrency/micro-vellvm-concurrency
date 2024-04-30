(** * Shallow equivalence *)

(** Equality under [observe]:

[[
  observing eq t1 t2 <-> t1.(observe) = t2.(observe)
]]

  We actually define a more general relation transformer
  [observing] to lift arbitrary relations through [observe].
 *)

(* begin hide *)
From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree.

From Coq Require Import
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations
     JMeq.

Set Implicit Arguments.
(* end hide *)

Definition eqeq {A : Type} (P : A -> Type) {a1 a2 : A} (p : a1 = a2) : P a1 -> P a2 -> Prop :=
  match p with
  | eq_refl => eq
  end.

Definition pweqeq {R1 R2} (RR : R1 -> R2 -> Prop) {X1 X2 : Type} (p : X1 = X2)
  : (X1 -> R1) -> (X2 -> R2) -> Prop :=
  match p with
  | eq_refl => fun k1 k2 => forall x, RR (k1 x) (k2 x)
  end.

Lemma pweqeq_mon {R1 R2} (RR1 RR2 : R1 -> R2 -> Prop) X1 X2 (p : X1 = X2) k1 k2
  : (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) -> pweqeq RR1 p k1 k2 -> pweqeq RR2 p k1 k2.
Proof.
  destruct p; cbn; auto.
Qed.

(** ** [observing]: Lift relations through [observe]. *)
Record observing {E B R1 R2}
           (eq_ : ctree' E B R1 -> ctree' E B R2 -> Prop)
           (t1 : ctree E B R1) (t2 : ctree E B R2) : Prop :=
  observing_intros
  { observing_observe : eq_ (observe t1) (observe t2) }.
#[global] Hint Constructors observing: core.

Section observing_relations.

Context {E B : Type -> Type} {R : Type}.
Variable (eq_ : ctree' E B R -> ctree' E B R -> Prop).

#[global] Instance observing_observe_ :
  Proper (observing eq_ ==> eq_) (@observe E B R).
Proof. intros ? ? []; cbv; auto. Qed.

#[global] Instance observing_go : Proper (eq_ ==> observing eq_) (@go E B R).
Proof. cbv; auto. Qed.

#[global] Instance monotonic_observing eq_' :
  subrelation eq_ eq_' ->
  subrelation (observing eq_) (observing eq_').
Proof. intros ? ? ? []; cbv; eauto. Qed.

#[global] Instance Equivalence_observing :
  Equivalence eq_ -> Equivalence (observing eq_).
Proof.
  intros []; split; cbv; auto.
  - intros ? ? []; auto.
  - intros ? ? ? [] []; eauto.
Qed.

End observing_relations.

(** ** Unfolding lemmas for [bind] *)

#[global] Instance observing_bind {E B R S} :
  Proper (observing eq ==> eq ==> observing eq) (@CTree.bind E B R S).
Proof.
  repeat intro; subst. constructor. unfold observe. cbn.
  rewrite (observing_observe H). reflexivity.
Qed.

Lemma bind_ret_ {E B R S} (r : R) (k : R -> ctree E B S) :
  observing eq (CTree.bind (Ret r) k) (k r).
Proof. constructor; reflexivity. Qed.

Lemma bind_Guard_ {E B R} `{B1 -< B} U t (k: U -> ctree E B R) :
  observing eq (CTree.bind (Guard t) k) (Guard (CTree.bind t k)).
Proof. constructor; reflexivity. Qed.

Lemma bind_vis_ {E B R U V} (e: E V) (ek: V -> ctree E B U) (k: U -> ctree E B R) :
  observing eq
    (CTree.bind (Vis e ek) k)
    (Vis e (fun x => CTree.bind (ek x) k)).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [aloop]. There is also a variant [unfold_aloop]
    without [Tau]. *)
Lemma unfold_aloop_ {E B X Y} `{B1 -< B} (f : X -> ctree E B (X + Y)) (x : X) :
  observing eq
    (CTree.iter f x)
    (CTree.bind (f x) (fun lr => CTree.on_left lr l (Guard (CTree.iter f l)))).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [forever]. *)
Lemma unfold_forever_ {E B R} `{B1 -< B} (k: R -> ctree E B R) (i: R):
  observing eq (@CTree.forever B _ _ R k i) (CTree.bind (k i) (fun i => Guard (CTree.forever k i))).
Proof. constructor; reflexivity. Qed.

(** ** [going]: Lift relations through [go]. *)

Inductive going {E B R1 R2} (r : ctree E B R1 -> ctree E B R2 -> Prop)
          (ot1 : ctree' E B R1) (ot2 : ctree' E B R2) : Prop :=
| going_intros : r (go ot1) (go ot2) -> going r ot1 ot2.
#[global] Hint Constructors going: core.

Lemma observing_going {E B R1 R2} (eq_ : ctree' E B R1 -> ctree' E B R2 -> Prop) ot1 ot2 :
  going (observing eq_) ot1 ot2 <-> eq_ ot1 ot2.
Proof.
  split; auto.
  intros [[]]; auto.
Qed.

Section going_relations.

Context {E B : Type -> Type} {R : Type}.
Variable (eq_ : ctree E B R -> ctree E B R -> Prop).

#[global] Instance going_go : Proper (going eq_ ==> eq_) (@go E B R).
Proof. intros ? ? []; auto. Qed.

#[global] Instance monotonic_going eq_' :
  subrelation eq_ eq_' ->
  subrelation (going eq_) (going eq_').
Proof. intros ? ? ? []; eauto. Qed.

#[global] Instance Equivalence_going :
  Equivalence eq_ -> Equivalence (going eq_).
Proof.
  intros []; constructor; cbv; eauto.
  - intros ? ? []; auto.
  - intros ? ? ? [] []; eauto.
Qed.

End going_relations.

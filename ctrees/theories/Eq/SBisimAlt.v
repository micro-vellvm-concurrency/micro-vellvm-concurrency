From Coq Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq
     Eq.Epsilon
     Eq.SSimAlt
     Misc.Pure.

From RelationAlgebra Require Export
     rel srel.

Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section StrongBisimAlt.
(*|
An alternative definition [sb'] of strong bisimulation.
The simulation challenge does not involve an inductive transition relation,
thus simplifying proofs.
|*)
  Program Definition sb' {E F C D : Type -> Type} {X Y : Type}
    `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
    (L : rel (@label E) (@label F)) :
    mon (bool -> ctree E C X -> ctree F D Y -> Prop) :=
    {| body R side t u :=
      (side = true -> ss'_gen L (fun t u => forall side, R side t u) (R true) t u) /\
      (side = false -> ss'_gen (flip L) (fun u t => forall side, R side t u) (flip (R false)) u t)
    |}.
  Next Obligation.
    split; intro; subst; [specialize (H0 eq_refl); clear H1 | specialize (H1 eq_refl); clear H0].
    all: eapply ss'_gen_mon; try eassumption; eauto.
    all: cbn; intuition.
  Qed.

End StrongBisimAlt.

Section Symmetry.

  Program Definition sb'l {E F C D X Y} `{HasB0: B0 -< C} `{HasB0': B0 -< D} L :
    mon (bool -> rel (ctree E C X) (ctree F D Y)) :=
    {| body R side t u := side = true -> sb' L R side t u |}.
  Next Obligation.
      eapply (Hbody (sb' L)).
      2: { specialize (H0 eq_refl). apply H0. }
      cbn. apply H.
  Qed.

  Program Definition converse_neg {A : Type} : mon (bool -> relation A) :=
  {| body := fun (R : bool -> rel A A) b (x y : A) => R (negb b) y x |}.

  #[global] Instance converse_neg_invol {A} : Involution (@converse_neg A).
  Proof.
    cbn. intros.
    now rewrite Bool.negb_involutive.
  Qed.

  #[global] Instance sbisim'_sym {E C X L} `{B0 -< C} :
    `{Symmetric L} ->
    Sym_from converse_neg (@sb' E E C C X X _ _ L) (sb'l L).
  Proof.
    intros SYM.
    assert (HL: L == flip L). { cbn. intuition. }
    eapply weq_ss'_gen in HL.
    cbn -[sb']. split; intros.
    - split; cbn -[sb']; intro.
      + apply H0.
      + intros. apply Bool.negb_true_iff in H1. subst.
        destruct H0 as [_ ?].
        specialize (H0 eq_refl).
        apply HL in H0.
        split; intros; subst; try discriminate.
        eapply ss'_gen_mon. 3: now apply H0.
        * cbn. intros. apply H2.
        * cbn. intros. apply H2.
    - split; intros; subst.
      + now apply H0.
      + intros.
        apply HL.
        eapply ss'_gen_mon. 3: now apply H0.
        * cbn. intros.
          specialize (H1 (negb side)).
          rewrite Bool.negb_involutive in H1. apply H1.
        * cbn. intros. apply H1.
  Qed.

End Symmetry.

Lemma sb'_flip {E F C D X Y L} `{HasB0: B0 -< C} `{HasB0': B0 -< D}
    side (t: ctree E C X) (u: ctree F D Y) R :
  sb' (flip L) (fun b => flip (R (negb b))) (negb side) u t ->
  sb' L R side t u.
Proof.
  split; intros; subst; destruct H; cbn in H.
  - specialize (H0 eq_refl).
    cbn -[ss'_gen] in H0. unfold flip in H0.
    eapply (ss'_gen_mon (x := fun t u => forall side, R (negb side) t u)).
    { cbn. intros. specialize (H1 (negb side)). rewrite Bool.negb_involutive in H1. apply H1. }
    { cbn. intros. apply H1. }
    apply H0.
  - specialize (H eq_refl).
    cbn -[ss'_gen] in H.
    eapply (ss'_gen_mon (x := fun t u => forall side, R (negb side) u t)).
      { cbn. intros. specialize (H1 (negb side)). rewrite Bool.negb_involutive in H1. apply H1. }
      { cbn. intros. apply H1. }
      apply H.
Qed.

Definition sbisim' {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L t u :=
  forall side, gfp (@sb' E F C D X Y _ _ L) side t u.

Program Definition lift_rel3 {A B} : mon (rel A B) -> mon (bool -> rel A B) :=
    fun f => {| body R side t u := f (R side) t u |}.
Next Obligation.
  destruct f. cbn. cbn in H0. eapply Hbody in H0. 2: { cbn. apply H. } apply H0.
Qed.

Lemma unary_sym3 {A} (f : A -> A) : compat converse_neg (lift_rel3 (unary_ctx f)).
Proof.
  intros R b. apply leq_unary_ctx.
  intros. now apply in_unary_ctx.
Qed.

Lemma binary_sym3 {A} (f : A -> A -> A) : compat converse_neg (lift_rel3 (binary_ctx f)).
Proof.
  intros R b. apply leq_binary_ctx.
  intros. now apply in_binary_ctx.
Qed.

Section sbisim'_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

(*|
   Strong bisimulation up-to [equ] is valid
   ----------------------------------------
|*)
  #[global] Instance equ_clos3_equ (R : bool -> rel (ctree E C X) (ctree F D Y)) :
  Proper (eq ==> equ eq ==> equ eq ==> impl) (lift_rel3 equ_clos R).
  Proof.
    cbn. intros. destruct H2. econstructor; subs. 2: subst; eassumption.
    now rewrite H0. assumption.
  Qed.

  Lemma equ_clos3_leq (R : bool -> rel (ctree E C X) (ctree F D Y)) :
  R <= lift_rel3 equ_clos R.
  Proof.
    cbn. intros. econstructor. reflexivity. eassumption. reflexivity.
  Qed.

  Lemma equ_clos_st' : lift_rel3 equ_clos <= (t (@sb' E F C D X Y _ _ L)).
  Proof.
    apply leq_t; cbn.
    intros R side x y [x' y' x'' y'' EQ' EQ''].
    split; [destruct EQ'' as [EQ'' _] | destruct EQ'' as [_ EQ'']];
        intros; subst; specialize (EQ'' eq_refl); subs.
    - eapply ss'_gen_mon. 3: apply EQ''.
      all: econstructor; eauto.
    - eapply ss'_gen_mon. 3: apply EQ''.
      all: econstructor; eauto.
  Qed.

  #[global] Instance equ_clos_gfp_sb'_goal : forall side, Proper (equ eq ==> equ eq ==> flip impl) (gfp (@sb' E F C D X Y _ _ L) side).
  Proof.
    cbn; intros ? ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st'); econstructor; try eassumption.
    now symmetry.
  Qed.

  #[global] Instance equ_clos_gfp_sb'_ctx : forall side, Proper (equ eq ==> equ eq ==> impl) (gfp (@sb' E F C D X Y _ _ L) side).
  Proof.
    cbn; intros ? ? ? eq1 ? ? eq2 H. now subs.
  Qed.

  #[global] Instance equ_clos_sbisim'_goal : Proper (equ eq ==> equ eq ==> flip impl) (@sbisim' E F C D X Y _ _ L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    intro. now subs.
  Qed.

  #[global] Instance equ_clos_sbisim'_ctx : Proper (equ eq ==> equ eq ==> impl) (@sbisim' E F C D X Y _ _ L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H. now subs.
  Qed.

End sbisim'_theory.

Module SBisim'Notations.

  Notation st' L := (t (sb' L)).
  Notation sbt' L := (bt (sb' L)).
  Notation sT' L := (T (sb' L)).
  Notation sbT' L := (bT (sb' L)).

End SBisim'Notations.

Import SBisim'Notations.

(* TODO check *)
Ltac fold_sbisim' :=
  repeat
    match goal with
    | h: context[gfp (@sb' ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => try fold (@sbisim' E F C D X Y _ _ L) in h
    | |- context[gfp (@sb' ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => try fold (@sbisim' E F C D X Y _ _ L)
    end.

Ltac __coinduction_sbisim' R H :=
  (try unfold sbisim');
  apply_coinduction; fold_sbisim'; intros R H.

Tactic Notation "__step_sbisim'" :=
  match goal with
  | |- context[@sbisim' ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold sbisim';
      intro; step
  end.

#[local] Tactic Notation "step" := __step_sbisim' || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim' R H || coinduction R H.

Ltac __step_in_sbisim' H :=
  match type of H with
  | context[@sbisim' ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold sbisim' in H;
      let Hl := fresh H "l" in
      let Hr := fresh H "r" in
      pose proof (Hl : H true);
      pose proof (Hr : H false);
      step in Hl; step in Hr;
      try fold (@sbisim' E F C D X Y _ _ L) in Hl;
      try fold (@sbisim' E F C D X Y _ _ L) in Hr
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim' H || step in H.

Import CTreeNotations.
Import EquNotations.
Section sbisim'_homogenous_theory.
  Context {E C: Type -> Type} {X: Type}
          {L: relation (@label E)}
          {HasStuck1: B0 -< C}.

  Notation sb' := (@sb' E E C C X X _ _).
  Notation sbisim' := (@sbisim' E E C C X X _ _).
  Notation st' L := (coinduction.t (sb' L)).
  Notation sbt' L := (coinduction.bt (sb' L)).
  Notation sT' L := (coinduction.T (sb' L)).

  (*|
    Various results on reflexivity and transitivity.
  |*)
  Lemma refl_st' `{Reflexive _ L}: lift_rel3 (const seq) <= (st' L).
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H0. subst. split; intros; subst; split; intros.
    - eexists _, _. eauto.
    - eexists. split; [| auto]. subs. eright. now left.
    - eexists _, _. cbn. eauto.
    - eexists. split; [| auto]. subs. eright. now left.
  Qed.

  (*| Reflexivity |*)
  #[global] Instance Reflexive_st' R `{Reflexive _ L}: forall b, Reflexive (st' L R b).
  Proof.
    intros. apply build_reflexive.
    cbn. intros.
    pose proof (ft_t refl_st'). cbn in H1. auto.
  Qed.

  Corollary Reflexive_sbisim' `{Reflexive _ L}: Reflexive (sbisim' L).
  Proof. cbn. intros ? ?. now apply Reflexive_st'. Qed.

  #[global] Instance Reflexive_sbt' R `{Reflexive _ L}:
    forall b, Reflexive (sbt' L R b).
  Proof.
    intros. apply build_reflexive.
    cbn. intros.
    pose proof (fbt_bt refl_st'). cbn in H1. auto.
  Qed.

  #[global] Instance Reflexive_sT' f R `{Reflexive _ L}:
    forall b, Reflexive (sT' L f R b).
  Proof.
    intros. apply build_reflexive.
    cbn. intros.
    pose proof (fT_T refl_st'). cbn in H1. auto.
  Qed.

  Lemma converse_st' `{SL: Symmetric _ L}: converse_neg <= st' L.
  Proof.
    apply leq_t. cbn -[sb']. intros.
    split; intros; subst.
    - destruct H as [_ ?]. specialize (H eq_refl).
      eapply (weq_ss'_gen (x := L)) in H. 2: { split; apply SL. }
      eapply ss'_gen_mon with (x := fun t u => forall side, a side u t).
      { cbn. intros. apply H0. }
      { cbn. intros. apply H0. }
      apply H.
    - destruct H as [? _]. specialize (H eq_refl).
      eapply (weq_ss'_gen (x := L)). { split; apply SL. }
      eapply ss'_gen_mon with (x := fun t u => forall side, a side t u).
      { cbn. intros. apply H0. }
      { cbn. intros. apply H0. }
      apply H.
  Qed.

  Lemma st'_flip `{SL: Symmetric _ L} R :
    forall b t u,
    st' L R b t u <-> st' L R (negb b) u t.
  Proof.
    split; intro; apply (ft_t converse_st'); auto.
    cbn. now rewrite Bool.negb_involutive.
  Qed.

  Lemma sbt'_flip `{SL: Symmetric _ L} R :
    forall b t u,
    sbt' L R b t u <-> sbt' L R (negb b) u t.
  Proof.
    split; intro; apply (fbt_bt converse_st'); auto.
    cbn. now rewrite Bool.negb_involutive.
  Qed.

End sbisim'_homogenous_theory.

Lemma split_st' : forall {E B X R L} `{SL: Symmetric _ L} `{HasB0: B0 -< B} (t u : ctree E B X),
  (forall side, st' L R side t u) <->
  st' L R true t u /\ st' L R true u t.
Proof.
  intros. split; intros.
  - split; auto.
    apply st'_flip. apply H.
  - destruct side; [apply H |].
    now apply st'_flip.
Qed.

Lemma split_st'_eq : forall {E B X R} `{HasB0: B0 -< B} (t u : ctree E B X),
  (forall side, st' eq R side t u) <->
  st' eq R true t u /\ st' eq R true u t.
Proof.
  intros. apply split_st'.
Qed.

Lemma split_sbt' : forall {E B X R L} `{SL: Symmetric _ L} `{HasB0: B0 -< B} (t u : ctree E B X),
  (forall side, sbt' L R side t u) <->
  sbt' L R true t u /\ sbt' L R true u t.
Proof.
  intros. split; intros.
  - split; auto.
    apply sbt'_flip. apply H.
  - destruct side; [apply H |].
    now apply sbt'_flip.
Qed.

Lemma split_sbt'_eq : forall {E B X R} `{HasB0: B0 -< B} (t u : ctree E B X),
  (forall side, sbt' eq R side t u) <->
  sbt' eq R true t u /\ sbt' eq R true u t.
Proof.
  intros. apply split_sbt'.
Qed.

Section sbisim'_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

  Notation sb' := (@sb' E F C D X Y _ _).
  Notation sbisim'  := (@sbisim' E F C D X Y _ _).
  Notation st' L := (coinduction.t (sb' L)).
  Notation sbt' L := (coinduction.bt (sb' L)).
  Notation sT' L := (coinduction.T (sb' L)).

  #[global] Instance equ_sb'_goal {RR} :
    forall b, Proper (equ eq ==> equ eq ==> flip impl) (sb' L RR b).
  Proof.
    intros. split; intros; subst.
    - subs. now apply H1.
    - subs. now apply H1.
  Qed.

  #[global] Instance equ_sb'_ctx {RR} :
    Proper (eq ==> equ eq ==> equ eq ==> impl) (sb' L RR).
  Proof.
    do 6 red. intros. subst. now rewrite <- H0, <- H1.
  Qed.

  #[global] Instance equ_clos_st'_goal {RR} :
    Proper (eq ==> equ eq ==> equ eq ==> flip impl) (st' L RR).
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    apply (ft_t equ_clos_st'); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_st'_ctx {RR} :
    Proper (eq ==> equ eq ==> equ eq ==> impl) (st' L RR).
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    now rewrite <- eq1, <- eq2.
  Qed.

  #[global] Instance equ_sbt'_closed_goal {r} :
    Proper (eq ==> equ eq ==> equ eq ==> flip impl) (sbt' L r).
  Proof.
    cbn. intros. subst.
    apply (fbt_bt equ_clos_st'); econstructor; eauto.
    now symmetry.
  Qed.

  #[global] Instance equ_sbt'_closed_ctx {r} :
    Proper (eq ==> equ eq ==> equ eq ==> impl) (sbt' L r).
  Proof.
    cbn; intros. subst.
    now rewrite H0, H1 in H2.
  Qed.

  #[global] Instance equ_clos_sT'_goal RR f :
    Proper (eq ==> equ eq ==> equ eq ==> flip impl) (sT' L f RR).
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    apply (fT_T equ_clos_st'); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sT'_ctx RR f :
    Proper (eq ==> equ eq ==> equ eq ==> impl) (sT' L f RR).
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    now rewrite <- eq1, <- eq2.
  Qed.

  Lemma sb'_true_ss' R :
    forall (t : ctree E C X) (u : ctree F D Y),
    sb' L R true t u <-> ss'_gen L (fun t u => forall side, R side t u) (R true) t u.
  Proof.
    split; intros.
    - now apply H.
    - split; intros; try discriminate. apply H.
  Qed.

  Lemma sb'_false_ss' R :
    forall (t : ctree E C X) (u : ctree F D Y),
    sb' L R false t u <-> ss'_gen (flip L) (fun u t => forall side, R side t u) (flip (R false)) u t.
  Proof.
    split; intros.
    - now apply H.
    - split; intros; try discriminate. apply H.
  Qed.

  Lemma sb'_true_stuck R :
    forall b (u : ctree F D Y) k,
    sb' L R true (go (@BrF E C X _ b void (subevent _ branch0) k)) u.
  Proof.
    intros. apply sb'_true_ss'.
    apply ss'_stuck.
  Qed.

End sbisim'_heterogenous_theory.

Lemma sb'_stuck {E F C D X Y L} {HasStuck1: B0 -< C} {HasStuck2: B0 -< D} R :
  forall side b b' k k',
  sb' L R side
    (go (@BrF E C X _ b void (subevent _ branch0) k))
    (go (@BrF F D Y _ b' void (subevent _ branch0) k')).
Proof.
  intros. destruct side.
  - apply sb'_true_stuck.
  - apply sb'_flip. cbn -[sb']. apply sb'_true_stuck.
Qed.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E F C D: Type -> Type}
          {X Y: Type}
          {HasStuck: B0 -< C}
          {HasStuck': B0 -< D}
          {L : rel (@label E) (@label F)}
          {R : bool -> rel (ctree E C X) (ctree F D Y)}
          {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}.

  Lemma step_sb'_ret :
    forall {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}
    x y,
    L (val x) (val y) ->
    (forall side, R side stuckD stuckD) ->
    forall side, sb' L R side (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    clear R HR.
    intros R HR x y Rstuck PROP Lval. split; intros; subst.
    - unshelve eapply step_ss'_ret; auto.
      cbn. intros. rewrite <- H. specialize (H1 side). now subs.
    - unshelve eapply step_ss'_ret; auto.
      cbn. intros. specialize (H1 side). now subs.
  Qed.

  Lemma step_sbt'_ret x y :
    L (val x) (val y) ->
    forall side, sbt' L R side (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros. apply step_sb'_ret.
    - exact H.
    - intros. step. apply sb'_stuck.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_sb'_vis {Z Z'} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall x, exists y, (forall side, R side (k x) (k' y)) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, (forall side, R side (k x) (k' y)) /\ L (obs e x) (obs f y)) ->
    forall side, sb' L R side (Vis e k) (Vis f k').
  Proof.
    intros. split; intro; subst; unshelve eapply step_ss'_vis; auto.
    - cbn. intros. specialize (H3 side). now subs.
    - cbn. intros. specialize (H3 side). now subs.
  Qed.

  Lemma step_sb'_vis_id {Z} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
    (forall x, (forall side, R side (k x) (k' x)) /\ L (obs e x) (obs f x)) ->
    forall side, sb' L R side (Vis e k) (Vis f k').
  Proof.
    intros. apply step_sb'_vis; eauto.
  Qed.

  Lemma step_sb'_vis_l {Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    (forall x, exists l' u', trans l' u u' /\ (forall side, R side (k x) u') /\ L (obs e x) l') ->
    sb' L R true (Vis e k) u.
  Proof.
    split; intros; subst; try discriminate.
    unshelve eapply step_ss'_vis_l.
    - cbn. intros. specialize (H3 side). now subs.
    - apply H.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
    |*)
  Lemma step_sb'_brS {Z Z'} (c : C Z) (d : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall x, exists y, forall side, R side (k x) (k' y)) ->
    (forall y, exists x, forall side, R side (k x) (k' y)) ->
    L tau tau ->
    forall side, sb' L R side (BrS c k) (BrS d k').
  Proof.
    split; intros; subst; unshelve eapply step_ss'_brS; auto.
    all: cbn; intros; specialize (H4 side); now subs.
  Qed.

  Lemma step_sb'_brS_id {Z} (c : C Z) (d: D Z)
    (k: Z -> ctree E C X) (k': Z -> ctree F D Y) :
    L tau tau ->
    (forall x side, R side (k x) (k' x)) ->
    forall side, sb' L R side (BrS c k) (BrS d k').
  Proof.
    intros; apply step_sb'_brS; eauto.
  Qed.

  Lemma step_sb'_brS_l {Z} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    (forall x, exists l' u', trans l' u u' /\ (forall side, R side (k x) u') /\ L tau l') ->
    sb' L R true (BrS c k) u.
  Proof.
    split; intros; subst; try discriminate.
    unshelve eapply step_ss'_brS_l.
    - cbn. intros. specialize (H3 side). now subs.
    - apply H.
  Qed.

  (*|
    Same goes for visible tau nodes.
    |*)
  Lemma step_sb'_step `{HasTau: B1 -< C} `{HasTau': B1 -< D}
    (t : ctree E C X) (t': ctree F D Y) :
    L tau tau ->
    (forall side, R side t t') ->
    forall side, sb' L R side (Step t) (Step t').
  Proof.
    intros. apply step_sb'_brS_id; auto.
  Qed.

  (*|
    With this definition [sb'] of bisimulation, delayed nodes allow to perform a coinductive step.
    |*)
  Lemma step_sb'_brD {Z Z'} (a: C Z) (b: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) side :
    (forall x, exists y, R side (k x) (k' y)) ->
    (forall y, exists x, R side (k x) (k' y)) ->
    sb' L R side (BrD a k) (BrD b k').
  Proof.
    split; intros; subst; apply step_ss'_brD.
    - intros. destruct (H x). eauto.
    - intros. destruct (H0 x). cbn. eauto.
  Qed.

  Lemma step_sb'_brD_id {Z} (c: C Z) (d: D Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) side :
    (forall x, R side (k x) (k' x)) ->
    sb' L R side (BrD c k) (BrD d k').
  Proof.
    intros. apply step_sb'_brD; eauto.
  Qed.

  Lemma step_sb'_brD_l {Z} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    (forall x, st' L R true (k x) u) ->
    sbt' L R true (BrD c k) u.
  Proof.
    split; intros; subst; try discriminate.
    now apply step_ss'_brD_l.
  Qed.

  Lemma step_sb'_guard `{HasTau: B1 -< C} `{HasTau': B1 -< D}
    (t: ctree E C X) (t': ctree F D Y) side :
    R side t t' ->
    sb' L R side (Guard t) (Guard t').
  Proof.
    intros. apply step_sb'_brD_id; auto.
  Qed.

  Lemma step_sb'_guard_l `{HasTau: B1 -< C}
        (t: ctree E C X) (t': ctree F D Y) side :
    sbt' L R side t t' ->
    sbt' L R side (Guard t) t'.
  Proof.
    split; intros; subst.
    - apply step_ss'_guard_l. step. apply H.
    - apply step_ss'_brD_r; auto. now apply H.
  Qed.

  Lemma step_sb'_guard_r `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) side :
    sbt' L R side t t' ->
    sbt' L R side t (Guard t').
  Proof.
    split; intros; subst.
    - apply step_ss'_brD_r; auto. now apply H.
    - apply step_ss'_guard_l. step. apply H.
  Qed.

  Lemma step_sb'_br {Z Z'} (vis: bool) (c: C Z) (d: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    L tau tau ->
    (forall x, exists y, forall side, R side (k x) (k' y)) ->
    (forall y, exists x, forall side, R side (k x) (k' y)) ->
    forall side, sb' L R side (Br vis c k) (Br vis d k').
  Proof.
    intros. destruct vis; [apply step_sb'_brS | apply step_sb'_brD];
      eauto.
    intro x. destruct (H0 x). eauto.
    intro x. destruct (H1 x). eauto.
  Qed.

  Lemma step_sb'_br_id {Z} (vis: bool) (c: C Z) (d: D Z)
    (k : Z -> ctree E C X) (k': Z -> ctree F D Y) :
    L tau tau ->
    (forall x side, R side (k x) (k' x)) ->
    forall side, sb' L R side (Br vis c k) (Br vis d k').
  Proof.
    intros. apply step_sb'_br; eauto.
  Qed.

End Proof_Rules.

Section Inversion_Rules.

  Context {E F C D: Type -> Type}
          {X Y: Type}
          {HasStuck: B0 -< C}
          {HasStuck': B0 -< D}.
  Variable (L : rel (@label E) (@label F)).

  (* Lemmas to exploit sb' and sbisim' hypotheses *)
  (* TODO incomplete *)

  Lemma sb'_true_vis_inv {Z Z' R} :
    forall (e : E Z) (f : F Z') (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y),
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    sb' L R true (Vis e k) (Vis f k') ->
    forall x, exists y, (forall side, R side (k x) (k' y)) /\ L (obs e x) (obs f y).
  Proof.
    intros.
    pose proof (trans_vis e x k).
    apply H0 in H1; etrans.
    destruct H1 as (? & ? & ? & ? & ?). inv_trans. subst.
    setoid_rewrite EQ in H2. etrans.
  Qed.

  Lemma sb'_true_vis_l_inv {Z R} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    sb' L R true (Vis e k) u ->
    exists l' u', trans l' u u' /\ (forall side, R side (k x) u') /\ L (obs e x) l'.
  Proof.
    intros. apply sb'_true_ss' in H.
    now apply ss'_vis_l_inv with (x := x) in H.
  Qed.

  Lemma sb'_true_brS_inv {Z Z' R} :
    forall (c : C Z) (c' : D Z') (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y),
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    sb' L R true (BrS c k) (BrS c' k') ->
    forall x, exists y, forall side, R side (k x) (k' y).
  Proof.
    intros.
    pose proof (trans_brS c k x).
    apply H0 in H1; etrans.
    destruct H1 as (? & ? & ? & ? & ?). inv_trans. subst.
    setoid_rewrite EQ in H2. etrans.
  Qed.

  Lemma sb'_true_brS_l_inv {Z R} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    sb' L R true (BrS c k) u ->
    exists l' u', trans l' u u' /\ (forall side, R side (k x) u') /\ L tau l'.
  Proof.
    intros. apply sb'_true_ss' in H.
    now apply ss'_brS_l_inv with (x := x) in H.
  Qed.

  Lemma sb'_eq_vis_invT {Z Z' R} :
    forall side (e : E Z) (f : E Z') (k : Z -> ctree E C X) (k' : Z' -> ctree E D Y),
    sb' eq R side (Vis e k) (Vis f k') ->
    forall (x : Z) (x' : Z'), Z = Z'.
  Proof.
    intros. destruct side.
    + pose proof (trans_vis e x k).
      apply H in H0; etrans.
      destruct H0 as (? & ? & ? & ? & ?). inv_trans. subst.
      now apply obs_eq_invT in H2 as ?.
    + pose proof (trans_vis f x' k').
      apply H in H0; etrans.
      destruct H0 as (? & ? & ? & ? & ?). inv_trans. subst.
      now apply obs_eq_invT in H2 as ?.
  Qed.

  Lemma sb'_eq_vis_inv {Z R} :
    forall side (e f : E Z) (k : Z -> ctree E C X) (k' : Z -> ctree E D Y),
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    sb' eq R side (Vis e k) (Vis f k') ->
    forall x, e = f /\ forall side, R side (k x) (k' x).
  Proof.
    intros. destruct side.
    + pose proof (trans_vis e x k).
      apply H0 in H1; etrans.
      destruct H1 as (? & ? & ? & ? & ?). inv_trans. subst.
      setoid_rewrite EQ in H2. apply obs_eq_inv in H3 as [<- <-]. auto.
    + pose proof (trans_vis f x k').
      apply H0 in H1; etrans.
      destruct H1 as (? & ? & ? & ? & ?). inv_trans. subst.
      setoid_rewrite EQ in H2. apply obs_eq_inv in H3 as [<- <-]. auto.
  Qed.

  Lemma sb'_true_vis_l_inv' {Z R} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    Respects_val L ->
    Respects_tau L ->
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    sb' L R true (Vis e k) u ->
    forall x, exists Z' (f : F Z') k' x',
      epsilon u (Vis f k') /\
      L (obs e x) (obs f x') /\
      forall side, R side (k x) (k' x').
  Proof.
    intros * RV RT ? SIM x.
    pose proof (TR := trans_vis e x k).
    apply SIM in TR; etrans.
    destruct TR as (l' & u' & TR & ? & ?).
    destruct l'.
    - apply RT in H1; intuition; discriminate.
    - apply trans_obs_epsilon in TR as (k' & EPS & EQ).
      setoid_rewrite EQ in H0.
      eauto 7 with trans.
    - apply RV in H1 as [_ ?].
      pose proof (H1 (Is_val _)). inversion H2.
  Qed.

  Lemma sb'_true_brS_l_inv' {Z R} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    Respects_tau L ->
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    sb' L R true (BrS c k) u ->
    forall x, exists Z' (c' : D Z') k' x',
      epsilon u (BrS c' k') /\
      forall side, R side (k x) (k' x').
  Proof.
    intros * RT ? SIM x.
    pose proof (TR := trans_brS c k x).
    apply SIM in TR; etrans.
    destruct TR as (l' & u' & TR & ? & ?).
    destruct l'.
    - apply trans_tau_epsilon in TR as (Z' & c' & k' & x' & EPS & EQ).
      setoid_rewrite EQ in H0.
      eauto 6 with trans.
    - apply RT in H1; intuition; discriminate.
    - apply RT in H1; intuition; discriminate.
  Qed.

  Lemma sb'_true_brD_l_inv {Z R} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    sb' L R true (BrD c k) u ->
    forall x, exists u', epsilon u u' /\ R true (k x) u'.
  Proof.
    intros.
    pose proof (proj1 H eq_refl).
    destruct H0 as [_ ?]. etrans.
  Qed.

  Lemma sb'_false_brD_l_inv {Z R} :
    forall (t : ctree E C X) (c : D Z) (k : Z -> ctree F D Y),
    sb' L R false t (BrD c k) ->
    forall x, exists t', epsilon t t' /\ R false t' (k x).
  Proof.
    intros.
    pose proof (proj2 H eq_refl).
    destruct H0 as [_ ?]. etrans.
  Qed.

  Lemma sbisim'_brD_l_inv {Z} c x (k : Z -> ctree E C X) (t' : ctree F D Y) :
    gfp (sb' L) true (BrD c k) t' ->
    gfp (sb' L) true (k x) t'.
  Proof.
    intros. step in H.
    eapply sb'_true_brD_l_inv with (x := x) in H as (? & ? & ?).
    step. split; intros; try discriminate.
    eapply step_ss'_epsilon_r; [| apply H].
    step in H0. now apply H0.
  Qed.

  Lemma sbisim'_brD_r_inv {Z} c x (k : Z -> ctree F D Y) (t : ctree E C X) :
    gfp (sb' L) false t (BrD c k) ->
    gfp (sb' L) false t (k x).
  Proof.
    intros. step in H.
    eapply sb'_false_brD_l_inv with (x := x) in H as (? & ? & ?).
    step. split; intros; try discriminate.
    eapply step_ss'_epsilon_r; [| apply H].
    step in H0. now apply H0.
  Qed.

End Inversion_Rules.

Definition guard_ctx {E C X} `{HasB1: B1 -< C} (R : ctree E C X -> Prop)
  (t : ctree E C X) :=
  exists t', t ≅ Guard t' /\ R t'.

Section upto.
  Context {E F C D: Type -> Type} {X Y: Type}
          `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
          `{HasB1 : B1 -< C} `{HasB1' : B1 -< D}
          (L : hrel (@label E) (@label F)).

  Program Definition ss_ctx3_l : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := b = true /\ ss L (fun t u => forall side, R side t u) t u |}.
  Next Obligation.
    split; auto. intros. apply H1 in H0 as (? & ? & ? & ? & ?). eauto 6.
  Qed.

  Lemma ss_st'_l : ss_ctx3_l <= t (@sb' E F C D X Y _ _ L).
  Proof.
    intro. apply Coinduction. cbn -[ss sb']. intros. destruct H as [-> ?].
    apply sb'_true_ss'. split; intros.
    - apply H in H1 as (? & ? & ? & ? & ?).
      exists x, x0. split; auto. split; auto.
      intros. apply (b_T (sb' L)). apply H2.
    - exists a3. split; auto.
      apply (fTf_Tf (sb' L)). cbn -[sb']. split; auto. intros.
      eapply trans_brD in H1; auto. rewrite <- H0 in H1.
      apply H in H1 as (? & ? & ? & ? & ?).
      exists x0, x1. split; auto. split; auto. intros.
      apply (b_T (sb' L)). apply H2.
  Qed.

  (* Up-to guard *)

  Program Definition guard_ctx3_l : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := guard_ctx (fun t => R b t u) t |}.
  Next Obligation.
    destruct H0 as (? & ? & ?). red. eauto.
  Qed.

  Program Definition guard_ctx3_r : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := guard_ctx (fun u => R b t u) u |}.
  Next Obligation.
    destruct H0 as (? & ? & ?). red. eauto.
  Qed.

  Lemma guard_ctx3_l_sbisim' :
    guard_ctx3_l <= t (@sb' E F C D X Y _ _ L).
  Proof.
    apply Coinduction. cbn -[sb']. intros.
    destruct H as (? & ? & ?). subs.
    split; intros; subst; subs.
    - apply step_ss'_guard_l.
      apply (b_T (sb' L)). apply H0.
    - apply step_ss'_guard_r.
      eapply ss'_gen_mon. 3: apply H0; auto.
      + intros ????. apply (id_T (sb' L)). apply H.
      + intros ???. apply (id_T (sb' L)). apply H.
  Qed.

  Lemma guard_ctx3_r_sbisim' :
    guard_ctx3_r <= t (@sb' E F C D X Y _ _ L).
  Proof.
    apply Coinduction. repeat red. intros.
    destruct H as (? & ? & ?).
    split; intros; subst; subs.
    - apply step_ss'_guard_r.
      eapply ss'_gen_mon. 3: apply H0; auto.
      + intros ????. apply (id_T (sb' L)). apply H.
      + intros ???. apply (id_T (sb' L)). apply H.
    - apply step_ss'_guard_l.
      apply (b_T (sb' L)). apply H0.
  Qed.

  (* Up-to epsilon *)

  Program Definition epsilon_det_ctx3_l : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := b = true /\ epsilon_det_ctx (fun t => R b t u) t |}.
  Next Obligation.
    destruct H1 as (? & ? & ?). split; auto. red. eauto.
  Qed.

  Lemma epsilon_det_ctx3_l_sbisim' :
    epsilon_det_ctx3_l <= t (@sb' E F C D X Y _ _ L).
  Proof.
    apply Coinduction. repeat red. intros.
    destruct H as (? & ? & ? & ?). subst.
    split; intros; try discriminate.
    induction H0.
    - apply sb'_true_ss' in H1. subs.
      eapply ss'_gen_mon. 3: apply H1.
      + cbn. intros. apply (id_T (sb' L)). apply H0.
      + apply (id_T (sb' L)).
    - subs. apply step_ss'_guard_l.
      step. do 3 red. apply sb'_true_ss'. now apply IHepsilon_det.
  Qed.

  Definition pure_bind_ctx {E C X X0} `{HasB0: B0 -< C} `{HasB1: B1 -< C} (P : X0 -> Prop) (R : ctree E C X -> Prop)
    (t : ctree E C X) :=
    exists (t0 : ctree E C X0) k0,
      t ≅ CTree.bind t0 k0 /\
      (forall l t', trans l t0 t' -> exists v, l = val v /\ P v) /\
      forall x, P x -> R (k0 x).

  Program Definition pure_bind_ctx3_l {X0} (P : X0 -> Prop) : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := b = true /\ pure_bind_ctx P (fun t => R b t u) t |}.
  Next Obligation.
    split; auto. destruct H1 as (? & ? & ? & ? & ?).
    red. eauto 7.
  Qed.

  Program Definition epsilon_ctx3_r : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := b = true /\ epsilon_ctx (fun u => R b t u) u |}.
  Next Obligation.
    destruct H1 as (? & ? & ?). split; auto. red. eauto.
  Qed.

  Lemma pure_bind_ctx3_l_sbisim' {X0} (P : X0 -> Prop) :
    pure_bind_ctx3_l P <= t (@sb' E F C D X Y _ _ L).
  Proof.
    apply Coinduction. cbn -[sb']. intros R side t u PURE.
    destruct PURE as (-> & PURE). apply sb'_true_ss'.
    red in PURE. destruct PURE as (t0 & k & EQ0 & Ht0 & Hk). subs.
    split.
    - intros PROD l t' TR.
      apply trans_bind_inv in TR as [(VAL & t'0 & TR0 & EQ) | (v & TR0 & TRk)].
      + apply Ht0 in TR0 as (v & -> & _). exfalso; etrans.
      + apply Ht0 in TR0 as ?. destruct H as (? & ? & Hv). apply val_eq_inv in H as <-.
        apply Hk in TRk as (l' & u' & TRu & SIM & EQl); auto. 2: {
          apply trans_val_epsilon in TR0 as [? _].
          apply productive_epsilon in H1; [| now apply productive_bind in PROD].
          now rewrite H1, bind_ret_l in PROD.
        }
        eexists _, _. repeat split; eauto. intros. apply (id_T (sb' L)). apply SIM.
    - intros Z c k0 EQ z.
      apply br_equ_bind in EQ as ?. destruct H as [(v & EQt0) | (k1 & EQt0 & EQk0)].
      + rewrite EQt0, bind_ret_l in EQ. specialize (Hk v). rewrite EQ in Hk.
        setoid_rewrite EQt0 in Ht0. clear t0 EQt0.
        destruct (Ht0 _ _ (trans_ret v)) as (? & ? & Hv). apply val_eq_inv in H as <-.
        specialize (Hk Hv).
        apply sb'_true_brD_l_inv with (x := z) in Hk as (u' & EPS & SIM).
        exists u'. split; auto. apply (id_T (sb' L)). apply SIM.
      + exists u. split; auto.
        eapply (fTf_Tf (sb' L)). cbn.
        split; auto. red. exists (k1 z), k.
        split; auto. split. {
          intros ?? TR. eapply trans_brD in TR; [| reflexivity].
          rewrite <- EQt0 in TR. now apply Ht0 in TR.
        }
        intros. apply (b_T (sb' L)). now apply Hk.
  Qed.

  Lemma epsilon_ctx3_r_sbisim' :
    epsilon_ctx3_r <= t (@sb' E F C D X Y _ _ L).
  Proof.
    apply Coinduction. repeat red. intros.
    destruct H as (? & ? & ? & ?). subst.
    split; intros; try discriminate.
    eapply step_ss'_epsilon_r; [| eassumption].
    destruct H1 as [? _]. specialize (H1 eq_refl).
    eapply ss'_gen_mon. 3: apply H1; auto.
    + intros ????. apply (id_T (sb' L)). apply H2.
    + intros ???. apply (id_T (sb' L)). apply H2.
  Qed.

  #[global] Instance epsilon_det_st' : forall (R : bool -> rel (ctree E C X) (ctree F D Y)),
    Proper (epsilon_det ==> epsilon_det ==> flip impl) (st' L R true).
  Proof.
    cbn. intros. subst.
    apply (ft_t (epsilon_det_ctx3_l_sbisim')). cbn.
    split; auto. exists y. split; auto.
    apply (ft_t (epsilon_ctx3_r_sbisim')). cbn.
    split; auto. exists y0. split; auto. now apply epsilon_det_epsilon.
  Qed.

  #[global] Instance epsilon_det_sbt' : forall (R : bool -> rel (ctree E C X) (ctree F D Y)),
    Proper (epsilon_det ==> epsilon_det ==> flip impl) (sbt' L R true).
  Proof.
    cbn. intros. subst.
    apply (fbt_bt (epsilon_det_ctx3_l_sbisim')). cbn.
    split; auto. exists y. split; auto.
    apply (fbt_bt (epsilon_ctx3_r_sbisim')). cbn.
    split; auto. exists y0. split; auto. now apply epsilon_det_epsilon.
  Qed.

End upto.

Section bind.
  Arguments label: clear implicits.
  Obligation Tactic := idtac.

  Context {E F C D: Type -> Type} {X X' Y Y': Type}
          `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
          (L : hrel (@label E) (@label F)) (R0 : rel X X').

(*|
Specialization of [bind_ctx] to a function acting with [sbisim'] on the bound value,
and with the argument (pointwise) on the continuation.
|*)

  Definition bind_ctx3
             (R: bool -> rel (ctree E C X) (ctree F D X'))
             (S: rel (X -> ctree E C Y) (X' -> ctree F D Y')):
    bool -> rel (ctree E C Y) (ctree F D Y') := fun b => bind_ctx (R b) S.

  Lemma leq_bind_ctx3 :
    forall R S S', bind_ctx3 R S <= S' <->
    (forall b x x', R b x x' -> forall k k', S k k' -> S' b (bind x k) (bind x' k')).
  Proof.
    split; intros.
    - apply H. now apply in_bind_ctx.
    - intro. apply leq_bind_ctx. auto.
  Qed.

  Program Definition bind_ctx_sbisim' L0 : mon (bool -> rel (ctree E C Y) (ctree F D Y')) :=
    {| body := fun R => bind_ctx3 (gfp (sb' L0)) (pointwise R0 (fun x y => forall b, R b x y)) |}.
  Next Obligation.
    intros ?? ? H. apply leq_bind_ctx3. intros.
    apply in_bind_ctx; auto. red. intros. apply H. now apply H1.
  Qed.

(*|
    The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_sbisim'_t L0 :
    is_update_val_rel L R0 L0 -> bind_ctx_sbisim' L0 <= t (sb' L).
  Proof.
    intro HL0. apply Coinduction.
    red. red. red. intros.
    apply leq_bind_ctx3.
    intros b t1 t2 tt k1 k2 kk.
    split; intros; subst; split.
    - simpl; intros PROD l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)].
      step in tt.
      apply tt in STEP as (l' & u' & STEP & EQ' & ?); auto.
      2: { now apply productive_bind in PROD. }
      do 2 eexists. split; [| split].
      apply trans_bind_l; eauto.
      + intro Hl. destruct Hl.
        apply HL0 in H0; etrans.
        inversion H0; subst. apply H. constructor. apply H2. constructor.
      + intro. apply (fT_T equ_clos_st').
          econstructor; [exact EQ | | reflexivity].
          apply (fTf_Tf (sb' L)). Opaque bind_ctx. cbn.
          apply in_bind_ctx; auto.
          intros ? ? ? ?.
          apply (b_T (sb' L)).
          red in kk; apply kk. eassumption.
      + apply HL0 in H0; etrans.
        destruct H0. exfalso. apply H. constructor. apply H2.
      + assert (t1 ≅ Ret v).
        { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
          now apply productive_epsilon. } subs.
        step in tt.
        apply tt in STEPres as (l' & u' & STEPres & EQ' & ?); auto.
        2: now eapply prod_ret.
        apply HL0 in H; etrans.
        dependent destruction H. 2: { exfalso. apply H. constructor. }
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v2 H true).
        rewrite bind_ret_l in PROD.
        apply kk in STEP as (? & u''' & STEP & EQ'' & ?); auto.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        intros. eapply (id_T (sb' L)). apply EQ''.
    - intros Z c k EQ z.
      apply br_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ') | (k0 & EQ' & EQ'')].
      + subs. step in tt. destruct tt as [tt _]. specialize (tt eq_refl). destruct tt as [tt _].
        edestruct tt as (l & t'' & STEPres & _ & ?); etrans.
        apply HL0 in H; etrans.
        apply update_val_rel_val_l in H as (v' & -> & EQ').
        rewrite bind_ret_l in EQ.
        specialize (kk v v' EQ' true).
        apply kk with (x := z) in EQ; auto. destruct EQ as (u' & EPS & EQ).
        exists u'.
        apply trans_val_epsilon in STEPres as [? _]. split.
        * eapply epsilon_bind; eassumption.
        * now apply (id_T (sb' L)).
      + subs. setoid_rewrite EQ''. clear k EQ EQ''.
        eexists. split. reflexivity.
        apply (fTf_Tf (sb' L)). apply in_bind_ctx.
        step. split; [| intros; discriminate].
        intros _. simple apply sbisim'_brD_l_inv with (x := z) in tt.
        step in tt. now apply tt.
        red. intros. apply (b_T (sb' L)). now apply kk.
    - simpl; intros PROD l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)].
      step in tt.
      apply tt in STEP as (l' & u' & STEP & EQ' & ?); auto.
      2: { now apply productive_bind in PROD. }
      do 2 eexists. split; [| split].
      apply trans_bind_l; eauto.
      + intro Hl. destruct Hl.
        apply HL0 in H0; etrans.
        inversion H0; subst. apply H. constructor. apply H1. constructor.
      + intro. apply (fT_T equ_clos_st').
          econstructor; [reflexivity | | now rewrite EQ].
          apply (fTf_Tf (sb' L)). Opaque bind_ctx. cbn.
          apply in_bind_ctx; auto.
          intros ? ? ? ?.
          apply (b_T (sb' L)).
          red in kk; apply kk. eassumption.
      + apply HL0 in H0; etrans.
        destruct H0. exfalso. apply H. constructor. apply H2.
      + assert (t2 ≅ Ret v).
        { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
          now apply productive_epsilon. } subs.
        step in tt.
        apply tt in STEPres as (l' & u' & STEPres & EQ' & ?); auto.
        2: now eapply prod_ret.
        apply HL0 in H; etrans.
        dependent destruction H. 2: { exfalso. apply H0. constructor. }
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v1 v H false).
        rewrite bind_ret_l in PROD.
        apply kk in STEP as (? & u''' & STEP & EQ'' & ?); auto.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        intros. eapply (id_T (sb' L)). apply EQ''.
    - intros Z c k EQ z.
      apply br_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ') | (k0 & EQ' & EQ'')].
      + subs. step in tt. destruct tt as [_ tt]. specialize (tt eq_refl). destruct tt as [tt _].
        edestruct tt as (l & t'' & STEPres & _ & ?); etrans.
        apply HL0 in H; etrans.
        apply update_val_rel_val_r in H as (v' & -> & EQ').
        rewrite bind_ret_l in EQ.
        specialize (kk v' v EQ' false).
        apply kk with (x := z) in EQ; auto. destruct EQ as (u' & EPS & EQ).
        exists u'.
        apply trans_val_epsilon in STEPres as [? _]. split.
        * eapply epsilon_bind; eassumption.
        * now apply (id_T (sb' L)).
      + subs. setoid_rewrite EQ''. clear k EQ EQ''.
        eexists. split. reflexivity.
        apply (fTf_Tf (sb' L)). apply in_bind_ctx.
        step. split; [intros; discriminate |].
        intros _. apply sbisim'_brD_r_inv with (x := z) in tt.
        step in tt. now apply tt.
        red. intros. apply (b_T (sb' L)). now apply kk.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma st'_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      R0 L0 b
      (t1 : ctree E C X) (t2: ctree F D X')
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR:
  gfp (sb' L0) b t1 t2 ->
  (forall x y, R0 x y -> forall b, st' L RR b (k1 x) (k2 y)) ->
  st' L RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_sbisim'_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma st'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) b
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  gfp (sb' (update_val_rel L R0)) b t1 t2 ->
  (forall x y, R0 x y -> forall b, st' L RR b (k1 x) (k2 y)) ->
  st' L RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply st'_clo_bind_gen; eauto. apply update_val_rel_correct.
Qed.

Lemma st'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      b (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') RR:
  gfp (sb' eq) b t1 t2 ->
  (forall x b, st' eq RR b (k1 x) (k2 x)) ->
  st' eq RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply st'_clo_bind_gen.
  - apply update_val_rel_eq.
  - apply H.
  - intros. now subst.
Qed.

Lemma sbt'_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      R0 L0 b
      (t1 : ctree E C X) (t2: ctree F D X')
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR:
  gfp (sb' L0) b t1 t2 ->
  (forall x y, R0 x y -> forall b, (sbt' L RR) b (k1 x) (k2 y)) ->
  sbt' L RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (fbt_bt (@bind_ctx_sbisim'_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma sbt'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) b
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  gfp (sb' (update_val_rel L R0)) b t1 t2 ->
  (forall x y, R0 x y -> forall b, sbt' L RR b (k1 x) (k2 y)) ->
  sbt' L RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbt'_clo_bind_gen; eauto. apply update_val_rel_correct.
Qed.

Lemma sbt'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      b (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') RR:
  gfp (sb' eq) b t1 t2 ->
  (forall x b, sbt' eq RR b (k1 x) (k2 x)) ->
  sbt' eq RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbt'_clo_bind_gen.
  - apply update_val_rel_eq.
  - apply H.
  - intros. now subst.
Qed.

Lemma sbT'_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      R0 L0 b
      (t1 : ctree E C X) (t2: ctree F D X')
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') f RR:
  gfp (sb' L0) b t1 t2 ->
  (forall x y, R0 x y -> forall b, (sbT' L f RR) b (k1 x) (k2 y)) ->
  sbT' L f RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (fbT_bT (@bind_ctx_sbisim'_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma sbT'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) b
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') f RR:
  gfp (sb' (update_val_rel L R0)) b t1 t2 ->
  (forall x y, R0 x y -> forall b, sbT' L f RR b (k1 x) (k2 y)) ->
  sbT' L f RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbT'_clo_bind_gen; eauto. apply update_val_rel_correct.
Qed.

Lemma sbT'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      b (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') f RR:
  gfp (sb' eq) b t1 t2 ->
  (forall x b, sbT' eq f RR b (k1 x) (k2 x)) ->
  sbT' eq f RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbT'_clo_bind_gen.
  - apply update_val_rel_eq.
  - apply H.
  - intros. now subst.
Qed.

Lemma step_sb'_guard_l' {E F C D X Y L}
  `{HasB0: B0 -< C} `{HasB0': B0 -< D} `{HasB1: B1 -< C}
  (t: ctree E C X) (t': ctree F D Y) R :
  (forall side, st' L R side t t') ->
  forall side, st' L R side (Guard t) t'.
Proof.
  intros.
  apply (ft_t (guard_ctx3_l_sbisim' L)).
  eexists; eauto.
Qed.

Lemma step_sb'_guard_r' {E F C D X Y L}
  `{HasB0: B0 -< C} `{HasB0': B0 -< D} `{HasB1: B1 -< D}
  (t: ctree E C X) (t': ctree F D Y) R :
  (forall side, st' L R side t t') ->
  forall side, st' L R side t (Guard t').
Proof.
  intros.
  apply (ft_t (guard_ctx3_r_sbisim' L)).
  eexists; eauto.
Qed.

Lemma sbisim'_epsilon_l {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} L :
  forall (t t' : ctree E C X) (u : ctree F D Y),
  gfp (sb' L) true t u ->
  epsilon t t' ->
  gfp (sb' L) true t' u.
Proof.
  intros. step. split; intro; [| discriminate].
  eapply ss'_gen_epsilon_l.
  - cbn. intros. step in H2. now apply H2.
  - step in H. now apply H.
  - apply H0.
Qed.

Lemma sbisim'_epsilon_r {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} L :
  forall (t : ctree E C X) (u u' : ctree F D Y),
  gfp (sb' L) false t u ->
  epsilon u u' ->
  gfp (sb' L) false t u'.
Proof.
  intros. step. split; intro; [discriminate |].
  eapply ss'_gen_epsilon_l.
  - cbn. intros. step in H2. now apply H2.
  - step in H. now apply H.
  - apply H0.
Qed.

Theorem gfp_sb'_ss_sbisim {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} :
  forall L (t : ctree E C X) (u : ctree F D Y),
  (ss L (sbisim L) t u -> gfp (sb' L) true t u) /\
  (ss (flip L) (flip (sbisim L)) u t -> gfp (sb' L) false t u).
Proof.
    intros. revert t u. coinduction R CH. intros. split; split.
    2, 3: intros; discriminate. all: intros _; split; intros.
    + apply H in H1. destruct H1 as (? & ? & ? & ? & ?).
      eexists _, _. split; [apply H1 |]. split; [| apply H3].
      step in H2. intro. destruct side; apply CH; apply H2.
    + subs. apply ss_brD_l_inv with (x := x) in H.
      exists u. split; [now left |]. now apply CH.
    + apply H in H1. destruct H1 as (? & ? & ? & ? & ?).
      eexists _, _. split; [apply H1 |]. split; [| apply H3].
      step in H2. destruct side; apply CH; apply H2.
    + subs. apply ss_brD_l_inv with (x := x) in H.
      exists t. split; [now left |]. now apply CH.
Qed.

Lemma gfp_sb'_true_ss_sbisim {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} :
  forall L (t : ctree E C X) (u : ctree F D Y),
  ss L (sbisim L) t u -> gfp (sb' L) true t u.
Proof.
  apply gfp_sb'_ss_sbisim.
Qed.

Theorem sbisim_sbisim' {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} :
  forall L (t : ctree E C X) (t' : ctree F D Y), sbisim L t t' <-> sbisim' L t t'.
Proof.
  split; intro.
  - intros [].
    + eapply (proj1 (gfp_sb'_ss_sbisim _ _ _)). step in H. apply H.
    + eapply (proj2 (gfp_sb'_ss_sbisim _ _ _)). step in H. apply H.
  - revert t t' H.
    coinduction R CH. intros. split; intros.
    + cbn. intros. apply trans_epsilon in H0 as (? & ? & ? & ?).
      apply sbisim'_epsilon_l with (t' := x) in H; auto.
      step in H. apply (proj1 H) in H2 as (? & ? & ? & ? & ?); auto. eauto 6.
    + cbn. intros. apply trans_epsilon in H0 as (? & ? & ? & ?).
      apply sbisim'_epsilon_r with (u' := x) in H; auto.
      step in H. apply (proj2 H) in H2 as (? & ? & ? & ? & ?); auto. eauto 6.
Qed.

Corollary sbisim_gfp_sb' {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} :
  forall L side (t : ctree E C X) (t' : ctree F D Y), sbisim L t t' -> gfp (sb' L) side t t'.
Proof.
  intros. apply sbisim_sbisim' in H. apply H.
Qed.

(*
Tactic Notation "__upto_bind_sbisim'" uconstr(R0) := TODO
Tactic Notation "__upto_bind_eq_sbisim'" uconstr(R0) := TODO
*)

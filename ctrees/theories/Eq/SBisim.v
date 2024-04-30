(*|
=========================================
Strong and Weak Bisimulations over ctrees
=========================================
The [equ] relation provides [ctree]s with a suitable notion of equality.
It is however much too fine to properly capture any notion of behavioral
equivalence that we could want to capture over computations modelled as
[ctree]s.
If we draw a parallel with [itree]s, [equ] maps directly to [eq_itree],
while [eutt] was introduced to characterize computations that exhibit the
same external observations, but may disagree finitely on the amount of
internal steps occuring between any two observations.
While the only consideration over [itree]s was to be insensitive to the
amount of fuel needed to run, things are richer over [ctree]s.
We essentially want to capture three intuitive things:
- to be insensitive to the particular branches chosen at non-deterministic
nodes -- in particular, we want [br t u ~~ br u t];
- to always be insensitive to how many _invisible_ br nodes are crawled
through -- they really are a generalization of [Tau] in [itree]s;
- to have the flexibility to be sensible or not to the amount of _visible_
br nodes encountered -- they really are a generalization of CCS's tau
steps. This last fact, whether we observe or not these nodes, will constrain
the distinction between the weak and strong bisimulations we define.

In contrast with [equ], as well as the relations in [itree]s, we do not
define the functions generating the relations directly structurally on
the trees. Instead, we follow a definition closely following the style
developed for process calculi, essentially stating that diagrams of this
shape can be closed.
t  R  u
|     |
l     l
v     v
t' R  u'
The transition relations that we use to this end are defined in the [Trans]
module:
- strong bisimulation is defined as a symmetric games over [trans];
- weak bisimulation is defined as an asymmetric game in which [trans] get
answered by [wtrans].

.. coq::none
|*)
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
     Eq.Equ
     Eq.Shallow
     Eq.Trans
     Eq.SSim
     Eq.CSSim.

From RelationAlgebra Require Export
     rel srel.

Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

(*|
Strong Bisimulation
-------------------
Relation relaxing [equ] to become insensitive to:
- the amount of _invisible_ brs taken;
- the particular branches taken during (any kind of) brs.
|*)

Section StrongBisim.
  Context {E F C D : Type -> Type} {X Y : Type} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}.
  Notation S := (ctree E C X).
  Notation S' := (ctree F D Y).

(*|
In the heterogeneous case, the relation is not symmetric.
|*)
  Program Definition sb L : mon (S -> S' -> Prop) :=
    {| body R t u := ss L R t u /\ ss (flip L) (flip R) u t |}.
  Next Obligation.
    split; intros; [edestruct H0 as (? & ? & ?) | edestruct H1 as (? & ? & ?)]; eauto; eexists; eexists; intuition; eauto.
  Qed.

  #[global] Instance Lequiv_sb_goal :
    Proper (Lequiv X Y ==> leq) sb.
  Proof.
    cbn -[sb]. split.
    - destruct H0 as [? _]. eapply Lequiv_ss_goal. apply H. apply H0.
    - destruct H0 as [_ ?]. eapply Lequiv_ss_goal with (x := flip x).
      red. cbn. intros. now apply H. apply H0.
  Qed.

  #[global] Instance weq_sb :
    Proper (weq ==> weq) sb.
  Proof.
    cbn -[weq]. split; intro.
    - eapply Lequiv_sb_goal. apply weq_Lequiv. apply H. auto.
    - eapply Lequiv_sb_goal. apply weq_Lequiv. symmetry. apply H. auto.
  Qed.

End StrongBisim.

Definition sbisim {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck': B0 -< D} L :=
  (gfp (@sb E F C D X Y _ _ L) : hrel _ _).

#[global] Instance Lequiv_sbisim : forall {E F C D X Y} `{B0 -< C} `{B0 -< D},
  Proper (Lequiv X Y ==> leq) (@sbisim E F C D X Y _ _).
Proof.
  cbn. intros.
  - unfold sbisim.
    epose proof (gfp_leq (x := sb x) (y := sb y)). lapply H3.
    + intro. red in H4. cbn in H4. apply H4. unfold sbisim in H2. apply H2.
    + now rewrite H1.
Qed.

#[global] Instance weq_sbisim : forall {E F C D X Y} `{B0 -< C} `{B0 -< D},
  Proper (weq ==> weq) (@sbisim E F C D X Y _ _).
Proof.
  cbn -[ss weq]. intros. apply gfp_weq. now apply weq_sb.
Qed.

(* This instance allows to use the symmetric tactic from coq-coinduction
   for homogeneous bisimulations *)
#[global] Instance sbisim_sym {E C X L} `{HasStuck : B0 -< C} :
  Symmetric L ->
  Sym_from converse (@sb E E C C X X _ _ L) (@ss E E C C X X _ _ L).
Proof.
  intros SYM. split; intro.
  - destruct H. split.
    + apply H.
    + cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?). apply SYM in H3. eauto.
  - destruct H. split.
    + apply H.
    + cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?). apply SYM in H3. eauto.
Qed.

Module SBisimNotations.

(*|
sb (bisimulation) notation
|*)
  Notation st L := (t (sb L)).
  Notation sT L := (T (sb L)).
  Notation sbt L := (bt (sb L)).
  Notation sbT L := (bT (sb L)).
  Notation "t ~ u" := (sbisim eq t u) (at level 70).
  Notation "t (~ L ) u" := (sbisim L t u) (at level 70).
  Notation "t [~ L] u" := (st L _ t u) (at level 79).
  Notation "t [~] u" := (st eq _ t u) (at level 79).
  Notation "t {~ L } u" := (sbt L _ t u) (at level 79).
  Notation "t {~} u" := (sbt eq _ t u) (at level 79).
  Notation "t {{ ~ L }} u" := (sb L _ t u) (at level 79).
  Notation "t {{~}} u" := (sb eq _ t u) (at level 79).

End SBisimNotations.

Import SBisimNotations.

Ltac fold_sbisim :=
  repeat
    match goal with
    | h: context[gfp (@sb ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _  => fold (@sbisim E F C D X Y _ _ L) in h
    | |- context[gfp (@sb ?E ?F ?C ?D ?X ?Y _ _ ?L)]       => fold (@sbisim E F C D X Y _ _ L)
    end.

Ltac __coinduction_sbisim R H :=
  (try unfold sbisim);
  apply_coinduction; fold_sbisim; intros R H.

Tactic Notation "__step_sbisim" :=
  match goal with
  | |- context[@sbisim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold sbisim;
      step;
      fold (@sbisim E F C D X Y _ _ L)
           (* TODO double check that this second match made no sense, I'm confused *)
  (* | |- context[@sb ?E ?F ?C ?D ?X ?Y _ _ ?LR] => *)
  (*     unfold sb; *)
  (*     step; *)
  (*     fold (@sb E F C D X Y _ _ L) *)
  end.

#[local] Tactic Notation "step" := __step_sbisim || __step_ssim || __step_cssim || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || __coinduction_ssim R H || __coinduction_cssim R H || coinduction R H.

Ltac __step_in_sbisim H :=
  match type of H with
  | context [@sbisim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E F C D X Y _ _ L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

(*|
  This section should describe lemmas proved for the
  heterogenous version of `css`, parametric on
  - Return types X, Y
  - Label types E, F
  - Branch effects C, D
|*)
Section sbisim_heterogenous_theory.

  Arguments label: clear implicits.
  Context {E F C D : Type -> Type} {X Y : Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

  Notation sb := (@sb E F C D X Y _ _).
  Notation sbisim := (@sbisim E F C D X Y _ _).
  Notation st L := (coinduction.t (sb L)).
  Notation sbt L := (coinduction.bt (sb L)).
  Notation sT  L := (coinduction.T (sb L)).

(*|
Strong bisimulation up-to [equ] is valid
----------------------------------------
|*)
  Lemma equ_clos_st : @equ_clos E F C D X Y <= (st L).
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' [Fwd Back] EQ'']; split.
    - intros l z x'z.
      rewrite EQ' in x'z.
      apply Fwd in x'z.
      destruct x'z as (? & ? & ? & ? & ?).
      do 2 eexists; intuition.
      rewrite <- EQ''; eauto.
      eapply (f_Tf (sb L)).
      econstructor; eauto.
      assumption.
    - intros l z y'z.
      rewrite <- EQ'' in y'z.
      apply Back in y'z.
      destruct y'z as (? & ? & ? & ? & ?).
      do 2 eexists; intuition.
      rewrite EQ'; eauto.
      eapply (f_Tf (sb L)).
      econstructor; eauto.
      eauto.
  Qed.

(*|
    Aggressively providing instances for rewriting [equ] under all [sb]-related
    contexts.
|*)
  #[global] Instance equ_clos_st_goal RR :
    Proper (@equ E C X X eq ==> @equ F D Y Y eq ==> flip impl) (st L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_st_ctx RR :
    Proper (@equ E C X X eq ==> @equ F D Y Y eq ==> impl) (st L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sT_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (sT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sT_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (sT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sbisim_goal :
    Proper (equ eq ==> equ eq ==> flip impl) (sbisim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sbisim_ctx :
    Proper (equ eq ==> equ eq ==> impl) (sbisim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_sb_closed_goal {r} : Proper (@equ E C X X eq ==> @equ F D Y Y eq ==> flip impl) (sb L r).
  Proof.
    intros t t' tt' u u' uu'.
    split; subs; apply H.
  Qed.

  #[global] Instance equ_sb_closed_ctx {r} : Proper (@equ E C X X eq ==> @equ F D Y Y eq ==> impl) (sb L r).
  Proof.
    cbn -[sb]. intros. now subs.
  Qed.

(*|
Up-to-bisimulation enhancing function
|*)
  Variant sbisim_clos_body {LE LF}
          (R : rel (ctree E C X) (ctree F D Y)) : (rel (ctree E C X) (ctree F D Y)) :=
    | Sbisim_clos : forall t t' u' u
                      (Sbisimt : t (~ LE) t')
                      (HR : R t' u')
                      (Sbisimu : u' (~ LF) u),
        @sbisim_clos_body LE LF R t u.

  Program Definition sbisim_clos {LE LF} : mon (rel (ctree E C X) (ctree F D Y)) :=
    {| body := @sbisim_clos_body LE LF |}.
  Next Obligation.
    destruct H0.
    econstructor; eauto.
  Qed.

(*|
stuck ctrees can be simulated by anything.
|*)
  Lemma is_stuck_sb (R : rel _ _) (t : ctree E C X) (t': ctree F D Y):
    is_stuck t -> is_stuck t' -> sb L R t t'.
  Proof.
    split; repeat intro.
    - now apply H in H1.
    - now apply H0 in H1.
  Qed.

  Theorem sbisim_clos_upto R: @sbisim_clos eq eq R <= st L R.
  Proof.
    apply leq_t.
    intros S t u HRel.
    split; cbn; intros ? ? TR.
    - inv HRel.
      step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis & <-).
      apply HR in TR; destruct TR as (? & ? & TR & Sbis' & HL).
      step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis'' & <-).
      do 2 eexists; repeat split; eauto.
      econstructor.
      apply Sbis.
      eauto.
      apply Sbis''.
    - inv HRel.
      step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis & <-).
      apply HR in TR; destruct TR as (? & ? & TR & Sbis' & HL).
      step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis'' & <-).
      do 2 eexists; repeat split; eauto.
      econstructor.
      apply Sbis''.
      eauto.
      apply Sbis.
  Qed.

End sbisim_heterogenous_theory.

Section sbisim_homogenous_theory.
  Context {E C: Type -> Type} {X: Type} `{HasStuck: B0 -< C}
          (L: relation (@label E)).

  Notation sb  := (@sb E E C C X X _ _).
  Notation sbisim := (@sbisim E E C C X X _ _).
  Notation st L := (coinduction.t (sb L)).
  Notation sbt L := (coinduction.bt (sb L)).
  Notation sT  L := (coinduction.T (sb L)).

(*|
This is just a hack suggested by Damien Pous to avoid a
universe inconsistency when using both the relational algebra
and coinduction libraries (we fix the type at which we'll use [eq]).
|*)
  Definition seq: relation (ctree E C X) := eq.
  Arguments seq/.

  Lemma refl_st {RL: Reflexive L} : const seq <= (st L).
  Proof.
    apply leq_t.
    split; intros; cbn*; intros; inv H; subst;
      exists l, t'; split; eauto.
  Qed.

(*|
[converse] is compatible
i.e. validity of up-to symmetry
|*)
  Lemma converse_st `{SL: Symmetric _ L}: converse <= (st L).
  Proof.
    apply leq_t; cbn.
    intros R ? ? [H1 H2]; split; intros.
    - destruct (H2 _ _ H) as (? & ? & ? & ? & ?); subst; symmetry in H4; eauto.
    - destruct (H1 _ _ H) as (? & ? & ? & ? & ?); subst; symmetry in H4; eauto.
  Qed.

(*|
[square] is compatible
i.e. validity of up-to transivitiy
|*)
  Lemma square_st `{TR: Transitive _ L}: square <= (st L).
  Proof.
    apply Coinduction; cbn.
    intros R x z [y [xy yx] [yz zy]].
    split.
     - intros ?l x' xx'.
      destruct (xy _ _ xx') as (?l & y' & yy' & ? & EQ).
      destruct (yz _ _ yy') as (?l & z' & zz' & ? & EQ').
      do 2 eexists; repeat split.
      eauto.
      apply (f_Tf (sb L)).
      eexists; eauto.
      transitivity l0; assumption.
    - intros ?l z' zz'.
      destruct (zy _ _ zz') as (?l & y' & yy' & ? & EQ).
      destruct (yx _ _ yy') as (?l & x' & xx' & ? & EQ').
      do 2 eexists; repeat split.
      eauto.
      apply (f_Tf (sb L)).
      eexists; eauto.
      transitivity l0; assumption.
  Qed.

(*|
Reflexivity
|*)
  #[global] Instance Reflexive_st R `{Reflexive _ L}: Reflexive (st L R).
  Proof. apply build_reflexive; apply ft_t; apply refl_st. Qed.

  Corollary Reflexive_sbisim `{Reflexive _ L}: Reflexive (sbisim L).
  Proof. now apply Reflexive_st. Qed.

  #[global] Instance Reflexive_sbt R `{Reflexive _ L}: Reflexive (sbt L R).
  Proof. apply build_reflexive; apply fbt_bt; apply refl_st. Qed.

  #[global] Instance Reflexive_sT f R `{Reflexive _ L}: Reflexive (sT L f R).
  Proof. apply build_reflexive; apply fT_T; apply refl_st. Qed.

(*|
Transitivity
|*)
  #[global] Instance Transitive_st R `{Transitive _ L}: Transitive (st L R).
  Proof. apply build_transitive; apply ft_t; apply (square_st). Qed.

  Corollary Transitive_sbisim `{Transitive _ L}: Transitive (sbisim L).
  Proof. now apply Transitive_st. Qed.

  #[global] Instance Transitive_sbt R `{Transitive _ L}: Transitive (sbt L R).
  Proof. apply build_transitive; apply fbt_bt; apply square_st. Qed.

  #[global] Instance Transitive_sT f R `{Transitive _ L}: Transitive (sT L f R).
  Proof. apply build_transitive; apply fT_T; apply square_st. Qed.

(*|
Symmetry
|*)
  #[global] Instance Symmetric_st R `{Symmetric _ L}: Symmetric (st L R).
  Proof. apply build_symmetric; apply ft_t; apply (converse_st). Qed.

  Corollary Symmetric_sbisim `{Symmetric _ L}: Symmetric (sbisim L).
  Proof. now apply Symmetric_st. Qed.

  #[global] Instance Symmetric_sbt R `{Symmetric _ L}: Symmetric (sbt L R).
  Proof. apply build_symmetric; apply fbt_bt; apply converse_st. Qed.

  #[global] Instance Symmetric_sT f R `{Symmetric _ L}: Symmetric (sT L f R).
  Proof. apply build_symmetric; apply fT_T; apply converse_st. Qed.

(*|
Thus bisimilarity and [t R] are always equivalence relations.
|*)
  #[global] Instance Equivalence_st `{Equivalence _ L} R: Equivalence (st L R).
  Proof. split; typeclasses eauto. Qed.

  Corollary Equivalence_bisim `{Equivalence _ L}: Equivalence (sbisim L).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance Equivalence_sbt `{Equivalence _ L} R: Equivalence (sbt L R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance Equivalence_sT `{Equivalence _ L} f R: Equivalence ((T (sb L)) f R).
  Proof. split; typeclasses eauto. Qed.

(*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under all [sb]-related contexts (consequence of the transitivity
of the companion).
|*)
  #[global] Instance sbisim_sbisim_closed_goal `{Transitive _ L} `{Symmetric _ L} :
    Proper (sbisim L ==> sbisim L ==> flip impl) (sbisim L).
  Proof.
    repeat intro.
    etransitivity; [etransitivity; eauto | symmetry; eassumption].
  Qed.

  #[global] Instance sbisim_sbisim_closed_ctx `{Transitive _ L} `{Symmetric _ L} :
    Proper (sbisim L ==> sbisim L ==> impl) (sbisim L).
  Proof.
    repeat intro.
    etransitivity; [symmetry; eassumption | etransitivity; eauto].
  Qed.

  #[global] Instance sbisim_clos_st_goal `{Equivalence _ L} R:
    Proper (sbisim L ==> sbisim L ==> flip impl) (st L R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_st_ctx `{Equivalence _ L} R :
    Proper (sbisim L ==> sbisim L ==> impl) (st L R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sT_goal `{Equivalence _ L} R f :
    Proper (sbisim L ==> sbisim L ==> flip impl) (sT L f R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sT_ctx `{Equivalence _ L} R f :
    Proper (sbisim L ==> sbisim L ==> impl) (sT L f R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance equ_sbt_closed_goal `{EqL: Equivalence _ L} R:
    Proper (equ eq ==> equ eq ==> flip impl) (sbt L R).
  Proof.
    repeat intro. pose proof (gfp_bt (sb L) R).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

  #[global] Instance equ_sbt_closed_ctx `{EqL: Equivalence _ L} {R} :
    Proper (equ eq ==> equ eq ==> impl) (sbt L R).
  Proof.
    repeat intro. pose proof (gfp_bt (sb L) R).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

(*|
Hence [equ eq] is a included in [sbisim]
|*)
  #[global] Instance equ_sbisim_subrelation `{EqL: Equivalence _ L} : subrelation (equ eq) (sbisim L).
  Proof.
    red; intros.
    rewrite H; reflexivity.
  Qed.

  #[global] Instance is_stuck_sbisim : Proper (sbisim L ==> flip impl) is_stuck.
  Proof.
    cbn. intros ???????.
    step in H. destruct H as [? _].
    apply H in H1 as (? & ? & ? & ? & ?). now apply H0 in H1.
  Qed.

End sbisim_homogenous_theory.

(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

Section bind.
  Obligation Tactic := trivial.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X X' Y Y': Type}
          `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
          {L: rel (label E) (label F)} (R0 : rel X Y).

  Program Definition bind_ctx_sbisim L0 : mon (rel (ctree E C X') (ctree F D Y')) :=
    {|body := fun R => @bind_ctx E F C D X Y X' Y' (sbisim L0)
                              (pointwise R0 R) |}.
  Next Obligation.
    intros ??? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_sbisim_t L0 :
    is_update_val_rel L R0 L0 -> bind_ctx_sbisim L0 <= st L.
  Proof.
    intros HL0. apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt; split; simpl;  intros l u STEP.
    - apply trans_bind_inv in STEP as [(VAL & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      + apply tt in STEP as (l' & u' & STEP & SIM & LBL).
        apply HL0 in LBL; etrans.
        apply update_val_rel_nonval_l in LBL as [VAL' LBL]; auto.
        do 2 eexists. split.
        apply trans_bind_l; eauto.
        split; auto.
        apply (fT_T equ_clos_st).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf (sb L)).
        apply in_bind_ctx; auto.
        intros ? ? ?.
        apply (b_T (sb L)).
        red in kk; now apply kk.
      + apply tt in STEPres as (l' & u' & STEPres & SIM & LBL).
        apply HL0 in LBL; etrans.
        apply update_val_rel_val_l in LBL as (v' & -> & ?).
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v' H).
        apply kk in STEP as (l' & u'' & STEP & EQ'' & ?); cbn in *.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        eapply (id_T (sb L)); auto.

    - apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      + apply tt in STEP as (l' & u' & STEP & EQ' & LBL).
        apply HL0 in LBL; etrans.
        apply update_val_rel_nonval_r in LBL as [VAL' LBL]; auto.
        do 2 eexists; split.
        apply trans_bind_l; eauto.
        split; auto.
        apply (fT_T equ_clos_st).
        symmetry in EQ.
        econstructor; [reflexivity | | exact EQ].
        apply (fTf_Tf (sb L)).
        apply in_bind_ctx; auto.
        intros ? ? ?.
        apply (b_T (sb L)).
        red in kk; now apply kk.
      + apply tt in STEPres as (l' & u' & STEPres & EQ' & LBL).
        apply HL0 in LBL; etrans.
        apply update_val_rel_val_r in LBL as (v' & -> & ?).
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v' v H).
        apply kk in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        eapply (id_T (sb L)); auto.
  Qed.

End bind.

Import CTree.
Import CTreeNotations.
Import EquNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
This principle is unusable for most [L], see https://github.com/vellvm/ctrees/issues/21
|*)
Lemma st_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (t1 : ctree E C X) (t2: ctree F D Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (~L0) t2 ->
  (forall x y, R0 x y -> (st L RR) (k1 x) (k2 y)) ->
  st L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_sbisim_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma st_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (~update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (st L RR) (k1 x) (k2 y)) ->
  st L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply st_clo_bind_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma st_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') RR:
  t1 ~ t2 ->
  (forall x, st eq RR (k1 x) (k2 x)) ->
  st eq RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply st_clo_bind_gen.
  - apply update_val_rel_eq.
  - assumption.
  - intros. now subst.
Qed.

Lemma sbt_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (t1 : ctree E C X) (t2: ctree F D Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (~L0) t2 ->
  (forall x y, R0 x y -> (sbt L RR) (k1 x) (k2 y)) ->
  sbt L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (fbt_bt (@bind_ctx_sbisim_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma sbt_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (~update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (sbt L RR) (k1 x) (k2 y)) ->
  sbt L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbt_clo_bind_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma sbt_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') RR:
  t1 ~ t2 ->
  (forall x, sbt eq RR (k1 x) (k2 x)) ->
  sbt eq RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbt_clo_bind_gen.
  - apply update_val_rel_eq.
  - assumption.
  - intros. now subst.
Qed.

Lemma sbisim_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (t1 : ctree E C X) (t2: ctree F D Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') :
  t1 (~L0) t2 ->
  (forall x y, R0 x y -> k1 x (~L) k2 y) ->
  t1 >>= k1 (~L) t2 >>= k2.
Proof.
  now apply st_clo_bind_gen.
Qed.

Lemma sbisim_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') :
  t1 (~update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> k1 x (~L) k2 y) ->
  t1 >>= k1 (~L) t2 >>= k2.
Proof.
  now apply st_clo_bind.
Qed.

Lemma sbisim_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') :
  t1 ~ t2 ->
  (forall x, k1 x ~ k2 x) ->
  t1 >>= k1 ~ t2 >>= k2.
Proof.
  now apply st_clo_bind_eq.
Qed.

(*#[global] Instance bind_sbisim_cong_gen {E C X X'} (RR: relation (ctree E C X')) `{HasStuck: B0 -< C}
      {L: relation (@label E)} {RL: Reflexive L}:
  Proper (sbisim eq ==> (fun f g => forall x, st L RR (f x) (g x)) ==> st L RR) (@bind E C X X').
Proof.
  repeat red; intros. eapply st_clo_bind_gen. 2: apply H.
  (* is_update_val_rel is too strong, eq is just a subrelation here *)
Abort.*)

(*|
And in particular, we get the proper instance justifying rewriting [~] to the left of a [bind].
|*)
#[global] Instance bind_sbisim_cong_gen {E C X X'} (RR: relation (ctree E C X')) `{HasStuck: B0 -< C}:
  Proper (sbisim eq ==> pointwise_relation X (st eq RR) ==> st eq RR) (@bind E C X X').
Proof.
  repeat red; intros. now apply st_clo_bind_eq.
Qed.

Ltac __upto_bind_sbisim :=
  match goal with
    |- @sbisim ?E ?F ?C ?D ?X ?Y _ _ ?L
              (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) => apply sbisim_clo_bind_eq
  | |- body (t (@sb ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R
           (CTree.bind (T := ?X') _ _) (CTree.bind (T := ?X') _ _) =>
      apply st_clo_bind_eq
  | |- body (bt (@sb ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R
           (CTree.bind (T := ?X') _ _) (CTree.bind (T := ?X') _ _) =>
      apply sbt_clo_bind_eq
  end.

Ltac __upto_bind_eq_sbisim :=
  match goal with
  | |- @sbisim ?E ?F ?C ?D ?X ?Y _ _ eq (CTree.bind (T := ?Z) _ _) (CTree.bind (T := ?Z) _ _) =>
      __upto_bind_sbisim; [reflexivity | intros ?]
  | _ =>
      __upto_bind_sbisim; [reflexivity | intros ? ? EQl]
  end.

(* Ltac __upto_bind_sbisim := *)
(*   match goal with *)
(*     |- @sbisim ?E ?F ?C ?D ?X ?Y _ _ ?L *)
(*               (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) => apply sbisim_clo_bind *)
(*   | |- body (t (@sb ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R *)
(*            (CTree.bind (T := ?X') _ _) (CTree.bind (T := ?Y') _ _) => *)
(*       apply (ft_t (@bind_ctx_sbisim_t E F C D X' X Y' Y _ _ L _)), in_bind_ctx *)
(*   | |- body (bt (@sb ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R *)
(*            (CTree.bind (T := ?X') _ _) (CTree.bind (T := ?Y') _ _) => *)
(*       apply (fbt_bt (@bind_ctx_sbisim_t E F C D X' X Y' Y _ _ L _)), in_bind_ctx *)
(*   end. *)

(* Ltac __upto_bind_eq_sbisim := *)
(*   match goal with *)
(*   | |- @sbisim ?E ?F ?C ?D ?X ?Y _ _ eq (CTree.bind (T := ?Z) _ _) (CTree.bind (T := ?Z) _ _) => *)
(*       __upto_bind_sbisim; [reflexivity | intros ?] *)
(*   | _ => *)
(*       __upto_bind_sbisim; [reflexivity | intros ? ? EQl] *)
(*   end. *)

Section Ctx.

  Context {E F C D: Type -> Type} {X X' Y Y': Type}.

  Definition vis_ctx (e : E X) (f: F Y)
             (R: rel (X -> ctree E C X') (Y -> ctree F D Y')):
    rel (ctree E C X') (ctree F D Y') :=
    sup_all (fun k => sup (R k) (fun k' => pairH (Vis e k) (Vis f k'))).

  Lemma leq_vis_ctx e f:
    forall R R', vis_ctx e f R <= R' <->
              (forall k k', R k k' -> R' (Vis e k) (Vis f k')).
  Proof.
    intros.
    unfold vis_ctx.
    setoid_rewrite sup_all_spec.
    setoid_rewrite sup_spec.
    setoid_rewrite <-leq_pairH.
    firstorder.
  Qed.

  Lemma in_vis_ctx e f (R :rel _ _) x x' :
    R x x' -> vis_ctx e f R (Vis e x) (Vis f x').
  Proof. intros. now apply ->leq_vis_ctx. Qed.
  #[global] Opaque vis_ctx.

End Ctx.

Section sb_vis_ctx.
  Arguments label: clear implicits.
  Obligation Tactic := idtac.

  Section Gen.
    Context {E F C D: Type -> Type} {X Y X' Y': Type}.
    Context `{HasFailC: B0 -< C} `{HasFailD: B0 -< D}.

    Program Definition vis_ctx_sbisim_gen (e : E X) (f: F Y) (right : X -> Y) (left : Y -> X) :
      mon (rel (ctree E C X') (ctree F D Y')) :=
      {|body := fun R =>
                  @vis_ctx E F C D X X' Y Y' e f
                    (fun ff gg =>
                       (forall x, R (ff x) (gg (right x))) /\
                         (forall y, R (ff (left y)) (gg y)))
      |}.
    Next Obligation.
      intros e f Rf Rg ? ? ? . apply leq_vis_ctx. intros k k' [H1 H2].
      apply in_vis_ctx; split; intros.
      eapply H in H1; eapply H1.
      eapply H in H2; eapply H2.
    Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma vis_ctx_sbisim_gen_t {L: rel (label E) (label F)} (e : E X) (f: F Y) right left :
      (forall x, L (obs e x) (obs f (right x))) ->
      (forall y, L (obs e (left y)) (obs f y)) ->
      vis_ctx_sbisim_gen e f right left <= (st L).
    Proof.
      intros HT HF.
      apply Coinduction.
      intros R.
      apply leq_vis_ctx.
      intros k k' kk'.
      cbn.
      split; intros ? ? TR; inv_trans; subst; cbn.
      - do 2 eexists; split; etrans; split; auto.
        rewrite EQ; now eapply (b_T (sb L)).
      - do 2 eexists; split; etrans; split; auto.
        rewrite EQ; now eapply (b_T (sb L)).
    Qed.

  End Gen.

  Section Specialized.

    Context {E C: Type -> Type} {X X': Type}.
    Context `{HasFailC: B0 -< C}.

    Program Definition vis_ctx_sbisim (e : E X) :
      mon (rel (ctree E C X') (ctree E C X')) :=
      {|body := fun R =>
                  @vis_ctx E E C C X X' X X' e e
                    (fun ff gg => forall x, R (ff x) (gg x))
      |}.
    Next Obligation.
      intros e ? ? ?. apply leq_vis_ctx. intros k k' H0.
      apply in_vis_ctx; intros.
      eapply H in H0; eapply H0.
    Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma vis_ctx_sbisim_t (e : E X) :
      vis_ctx_sbisim e <= (st eq).
    Proof.
      apply Coinduction.
      intros R.
      apply leq_vis_ctx.
      intros k k' kk'.
      cbn.
      split; intros ? ? TR; inv_trans; subst; cbn.
      - do 2 eexists; split; etrans; split; auto.
        rewrite EQ; now eapply (b_T (sb eq)).
      - do 2 eexists; split; etrans; split; auto.
        rewrite EQ; now eapply (b_T (sb eq)).
    Qed.

  End Specialized.

End sb_vis_ctx.

Arguments vis_ctx_sbisim_t {E C X X' _} e.

Ltac __upto_vis_sbisim :=
  match goal with
    |- @sbisim ?E ?F ?C _ ?X _ _ _ ?RR (Vis ?e _) (Vis ?e _) =>
      apply (ft_t (vis_ctx_sbisim_t e)), in_vis_ctx; intros ?
  | |- body (t (@sb ?E ?F ?C _ ?X _ _ ?R _)) ?RR (Vis ?e _) (Vis ?f _) =>
      apply (ft_t (vis_ctx_sbisim_t e)), in_vis_ctx; intros ?
  | |- body (bt (@sb ?E ?F ?C _ ?X _ _ ?R _)) ?RR (Vis ?e _) (Vis ?f _) =>
      apply (fbt_bt (vis_ctx_sbisim_t e)), in_vis_ctx; intros ?
  end.

#[local] Tactic Notation "upto_vis" := __upto_vis_sbisim.

Ltac __play_sbisim := step; split; cbn; intros ? ? ?TR.

Ltac __playL_sbisim H :=
  step in H;
  let Hf := fresh "Hf" in
  destruct H as [Hf _];
  cbn in Hf; edestruct Hf as (? & ? & ?TR & ?EQ & ?);
  clear Hf; subst; [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E _ ?C _ ?X _ _ _ ?RR _ _ |- _ =>
      __playL_sbisim h
  end.

Ltac __playR_sbisim H :=
  step in H;
  let Hb := fresh "Hb" in
  destruct H as [_ Hb];
  cbn in Hb; edestruct Hb as (? & ? & ?TR & ?EQ & ?);
  clear Hb; subst; [etrans |].

Ltac __eplayR_sbisim :=
  match goal with
  | h : @sbisim ?E ?C ?X _ _ _ |- _ =>
      __playR_sbisim h
  end.

#[local] Tactic Notation "play" := __play_sbisim.
#[local] Tactic Notation "playL" "in" ident(H) := __playL_sbisim H.
#[local] Tactic Notation "playR" "in" ident(H) := __playR_sbisim H.
#[local] Tactic Notation "eplayL" := __eplayL_sbisim.
#[local] Tactic Notation "eplayR" := __eplayR_sbisim.


(*|
Proof rules for [~]
-------------------
Naive bisimulations proofs naturally degenerate into exponential proofs,
splitting into two goals at each step.
The following proof rules avoid this issue in particular cases.

Be sure to notice that contrary to equations such that [sb_guard] or
up-to principles such that [upto_vis], (most of) these rules consume a [sb].

TODO: need to think more about this --- do we want more proof rules?
Do we actually need them on [sb (st R)], or something else?
|*)
Section Proof_Rules.

  Arguments label : clear implicits.
  Context {E F C D : Type -> Type} {X Y: Type} {L : rel (label E) (label F)}
          `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}.

  Lemma step_sb_ret_gen
        (x: X) (y: Y) (R : rel (ctree E C X) (ctree F D Y)) :
    R stuckD stuckD ->
    L (val x) (val y) ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    sb L R (Ret x) (Ret y).
  Proof.
    intros Rstuck ValRefl PROP.
    split; apply step_ss_ret_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_ret
        (x: X) (y: Y) (R : rel (ctree E C X) (ctree F D Y)) :
    L (val x) (val y) ->
    sbt L R (Ret x) (Ret y).
  Proof.
    intros LH; subst.
    apply step_sb_ret_gen; eauto.
    - step; split;
      apply is_stuck_sb; apply stuckD_is_stuck.
    - typeclasses eauto.
  Qed.

  (*|
    The vis nodes are deterministic from the perspective of the labeled transition system,
    stepping is hence symmetric and we can just recover the itree-style rule.
  |*)
  Lemma step_sb_vis_gen {X' Y'} (e: E X') (f: F Y')
        (k: X' -> ctree E C X) (k': Y' -> ctree F D Y) {R : rel _ _}:
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    sb L R (Vis e k) (Vis f k').
  Proof.
    intros PR EQs EQs'.
    split; apply step_ss_vis_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_vis {X' Y'}
        (e: E X') (f: F Y') (k: X' -> ctree E C X) (k': Y' -> ctree F D Y) {R : rel _ _}:
    (forall x, exists y, st L R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, st L R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    sbt L R (Vis e k) (Vis f k').
  Proof.
    intros EQs EQs'.
    apply step_sb_vis_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_vis_id_gen {X'}
        (e: E X') (f: F X') (k: X' -> ctree E C X) (k': X' -> ctree F D Y) {R : rel _ _}:
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    sb L R (Vis e k) (Vis f k').
  Proof.
    intros PR EQs.
    split; apply step_ss_vis_id_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_vis_id {X'}
        (e: E X') (f: F X') (k: X' -> ctree E C X) (k': X' -> ctree F D Y) {R : rel _ _}:
    (forall x, st L R (k x) (k' x)) ->
    (forall x, L (obs e x) (obs f x)) ->
    sbt L R (Vis e k) (Vis f k').
  Proof.
    intros.
    eapply step_sb_vis_id_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    Same goes for visible tau nodes.
  |*)
  Lemma step_sb_step_gen `{HasTau: B1 -< C}
        `{HasTau': B1 -< D} (t : ctree E C X) (t' : ctree F D Y) (R: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (R t t') ->
    sb L R (Step t) (Step t').
  Proof.
    intros. split; apply step_ss_step_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_step `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t : ctree E C X) (t' : ctree F D Y) (R: rel _ _) :
    L tau tau ->
    (st L R t t') ->
    sbt L R (Step t) (Step t').
  Proof.
    apply step_sb_step_gen.
    typeclasses eauto.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right, and reciprocally.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
    |*)
  Lemma step_sb_brS_gen {X' Y'} (c : C X') (c' : D Y')
        (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y) (R : rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall x, exists y, R (k x) (k' y)) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb L R (BrS c k) (BrS c' k').
  Proof.
    intros PROP ? EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 x) as [y HR].
      do 2 eexists. intuition.
      etrans.
      rewrite EQ; eauto.
    - destruct (EQs2 x) as [y HR].
      do 2 eexists. intuition.
      etrans.
      cbn; rewrite EQ; eauto.
  Qed.

  Lemma step_sb_brS {Z Z'} (c : C Z) (c' : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R : rel _ _):
    L tau tau ->
    (forall x, exists y, st L R (k x) (k' y)) ->
    (forall y, exists x, st L R (k x) (k' y)) ->
    sbt L R (BrS c k) (BrS c' k').
  Proof.
    intros EQs1 EQs2.
    apply step_sb_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_brS_id_gen {Z} (c : C Z) (d : D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall x, R (k x) (k' x)) ->
    sb L R (BrS c k) (BrS d k').
  Proof.
    intros PROP ? EQs.
    split; apply step_ss_brS_id_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_brS_id {Z} (c : C Z) (d : D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R : rel _ _):
    L tau tau ->
    (forall x, st L R (k x) (k' x)) ->
    sbt L R (BrS c k) (BrS d k').
  Proof.
    apply step_sb_brS_id_gen.
    typeclasses eauto.
  Qed.

  (*|
    For invisible nodes, the situation is different: we may kill them, but that execution
    cannot act as going under the guard.
  |*)
  Lemma step_sb_guard_gen `{B1 -< C} `{B1 -< D}
        (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    sb L R t t' ->
    sb L R (Guard t) (Guard t').
  Proof.
    intros EQ.
    split; apply step_ss_guard_gen; apply EQ.
  Qed.

  Lemma step_sb_guard `{B1 -< D} `{B1 -< C}
        (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    sbt L R t t' ->
    sbt L R (Guard t) (Guard t').
  Proof.
    now apply step_sb_guard_gen.
  Qed.

  Lemma step_sb_brD_gen {X' Y'} (c : C X') (d: D Y')
        (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y) (R : rel _ _) :
    (forall x, exists y, sb L R (k x) (k' y)) ->
    (forall y, exists x, sb L R (k x) (k' y)) ->
    sb L R (BrD c k) (BrD d k').
  Proof.
    intros EQs1 EQs2.
    split; apply step_ss_brD_gen; intros.
    - destruct (EQs1 x) as [z [FW _]]. eauto.
    - destruct (EQs2 x) as [z [_ BA]]. eauto.
  Qed.

  Lemma step_sb_brD {X' Y'} (c : C X') (d: D Y')
        (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y) (R : rel _ _) :
    (forall x, exists y, sbt L R (k x) (k' y)) ->
    (forall y, exists x, sbt L R (k x) (k' y)) ->
    sbt L R (BrD c k) (BrD d k').
  Proof.
    now apply step_sb_brD_gen.
  Qed.

  Lemma step_sb_brD_id_gen {Z} (c : C Z) (d: D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R : rel _ _) :
    (forall x, sb L R (k x) (k' x)) ->
    sb L R (BrD c k) (BrD d k').
  Proof.
    intros. split; apply step_ss_brD_id_gen; apply H.
  Qed.

  Lemma step_sb_brD_id {Z} (c : C Z) (d : D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R : rel _ _) :
    (forall x, sbt L R (k x) (k' x)) ->
    sbt L R (BrD c k) (BrD d k').
  Proof.
    now apply step_sb_brD_id_gen.
  Qed.

  Lemma step_sb_brD_l_gen {Z R}
    (c : C Z) (z : Z) (k : Z -> ctree E C X) (t : ctree F D Y) :
    (forall x, sb L R (k x) t) ->
    sb L R (BrD c k) t.
  Proof.
    split.
    - apply step_ss_brD_l_gen.
      apply H.
    - apply step_ss_brD_r_gen with (x := z).
      apply H.
  Qed.

  Lemma step_sb_brD_l {Z R}
    (c : C Z) (z : Z) (k : Z -> ctree E C X) (t : ctree F D Y) :
    (forall x, sbt L R (k x) t) ->
    sbt L R (BrD c k) t.
  Proof.
    now apply step_sb_brD_l_gen.
  Qed.

End Proof_Rules.

(*|
Proof system for [~]
--------------------

While the proof rules from the previous section are useful for performing full on
coinductive proofs, lifting these at the level of [sbisim] can allow for completely
avoiding any coinduction when combined with a pre-established equational theory.
|*)
Section Sb_Proof_System.
  Arguments label: clear implicits.
  Context {E C: Type -> Type} {X: Type}
          `{B0 -< C}.

  Lemma sb_ret : forall x y,
      x = y ->
      (Ret x: ctree E C X) ~ (Ret y: ctree E C X).
  Proof.
    intros * EQ; step.
    now apply step_sb_ret; subst.
  Qed.

  Lemma sb_vis {Y}: forall (e: E X) (k k': X -> ctree E C Y),
      (forall x, k x ~ k' x) ->
      Vis e k ~ Vis e k'.
  Proof.
    intros.
    upto_vis.
    apply H0.
  Qed.

  (*|
    Visible vs. Invisible Taus
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
    Invisible taus can be stripped-out w.r.t. to [sbisim], but not visible ones
  |*)
  Lemma sb_guard `{B1 -< C}: forall (t : ctree E C X),
      Guard t ~ t.
  Proof.
    intros t; play.
    - inv_trans; etrans.
    - eauto 6 with trans.
  Qed.

 Lemma sb_guard_l `{B1 -< C}: forall (t u : ctree E C X),
      t ~ u ->
      Guard t ~ u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_r `{B1 -< C}: forall (t u : ctree E C X),
      t ~ u ->
      t ~ Guard u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_lr `{B1 -< C}: forall (t u : ctree E C X),
      t ~ u ->
      Guard t ~ Guard u.
  Proof.
    intros * EQ; now rewrite !sb_guard.
  Qed.

  Lemma sb_step `{B1 -< C}: forall (t u : ctree E C X),
      t ~ u ->
      Step t ~ Step u.
  Proof.
    intros * EQ; step.
    apply step_sb_step; auto.
  Qed.

  (* TODO: Double check that this is needed, it should be taus in all contexts I can think of *)
  Lemma sb_brD1 (c1: C (fin 1)): forall (k : fin 1 -> ctree E C X),
      BrD c1 k ~ k F1.
  Proof.
    intros; step; econstructor.
    - intros ? ? ?. inv H0.
      apply Eqdep.EqdepTheory.inj_pair2 in H4, H5; subst.
      dependent destruction x; exists l, t'; etrans; auto.
      inversion x.
    - intros ? ? ?; cbn.
      eauto 6 with trans.
  Qed.

  Lemma sb_brS I J (ci : C I) (cj : C J)
        (k : I -> ctree E C X) (k' : J -> ctree E C X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    BrS ci k ~ BrS cj k'.
  Proof.
    intros * EQs1 EQs2; step.
    apply @step_sb_brS; auto.
  Qed.

  Lemma sb_brS_id I (c : C I)
        (k k' : I -> ctree E C X) :
    (forall x, k x ~ k' x) ->
    BrS c k ~ BrS c k'.
  Proof.
    intros * EQs; step.
    apply @step_sb_brS_id; auto.
  Qed.

  Lemma sb_brD I J (ci : C I) (cj : C J)
        (k : I -> ctree E C X) (k' : J -> ctree E C X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    BrD ci k ~ BrD cj k'.
  Proof.
    intros; step.
    eapply @step_sb_brD; auto.
    intros x; destruct (H0 x) as (y & EQ).
    exists y; now step in EQ.
    intros y; destruct (H1 y) as (x & EQ).
    exists x; now step in EQ.
  Qed.

  Lemma sb_brD_id I (c : C I)
        (k k' : I -> ctree E C X) :
    (forall x, k x ~ k' x) ->
    BrD c k ~ BrD c k'.
  Proof.
    intros; step.
    apply @step_sb_brD_id; intros x.
    specialize (H0 x).
    now step in H0.
  Qed.

  Lemma sb_brD_idempotent {Y} `{B1 -< C} c (y : Y) (k: Y -> ctree E C X) (t: ctree E C X):
      (forall x, k x ~ t) ->
      BrD c k ~ t.
  Proof.
    intros * EQ. step.
    apply step_sb_brD_l_gen; auto.
    intros. specialize (EQ x).
    now step in EQ.
  Qed.

  Lemma sb_brDn_idempotent `{B1 -< C} {HasFin : Bn -< C} n (k: fin (S n) -> ctree E C X) (t: ctree E C X):
      (forall x, k x ~ t) ->
      brDn k ~ t.
  Proof.
    intros * EQ.
    apply sb_brD_idempotent.
    apply F1.
    apply EQ.
  Qed.

  Lemma sb_unfold_forever {HasTau: B1 -< C}: forall (k: X -> ctree E C X)(i: X),
      forever k i ~ r <- k i ;; forever k r.
  Proof.
    intros k i.
    rewrite (ctree_eta (forever k i)).
    rewrite unfold_forever_.
    rewrite <- ctree_eta.
    __upto_bind_eq_sbisim.
    apply sb_guard.
  Qed.
End Sb_Proof_System.

(* TODO: tactics!
   Should it be the same to step at both levels or two different sets?

Ltac bsret  := apply step_sb_ret.
Ltac bsvis  := apply step_sb_vis.
Ltac bstauv := apply step_sb_tauV.
Ltac bsstep := bsret || bsvis || bstauv.

Ltac sret  := apply sb_ret.
Ltac svis  := apply sb_vis.
Ltac stauv := apply sb_tauV.
Ltac sstep := sret || svis || stauv.


 *)

Section WithParams.

  Context {E C : Type -> Type}.
  Context {HasStuck : B0 -< C}.
  Context {HasTau : B1 -< C}.
  Context {HasC2 : B2 -< C}.
  Context {HasC3 : B3 -< C}.


(*|
Sanity checks
=============
- invisible n-ary spins are strongly bisimilar
- non-empty visible n-ary spins are strongly bisimilar
- Binary invisible br is:
  + associative
  + commutative
  + merges into a ternary invisible br
  + admits any stuckD computation as a unit

Note: binary visible br are not associative up-to [sbisim].
They aren't even up-to [wbisim].
|*)

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)

  Lemma spinS_gen_nonempty : forall {Z X Y} (c: C X) (c': C Y) (x: X) (y: Y),
      @spinS_gen E C Z X c ~ @spinS_gen E C Z Y c'.
  Proof.
    intros R.
    coinduction S CIH. symmetric.
    intros ** L t' TR;
    rewrite ctree_eta in TR; cbn in TR;
    apply trans_brS_inv in TR as (_ & EQ & ->);
    eexists; eexists;
    rewrite ctree_eta; cbn.
    split; [econstructor|].
    - exact y.
    - reflexivity.
    - rewrite EQ; eauto.
  Qed.

  Lemma spinD_gen_bisim : forall {Z X Y} (c: C X) (c': C Y),
      @spinD_gen E C Z X c ~ @spinD_gen E C Z Y c'.
  Proof.
    intros R.
    coinduction S _; split; cbn;
      intros * TR; exfalso; eapply spinD_gen_is_stuck, TR.
  Qed.

  (*|
    BrD2 is associative, commutative, idempotent, merges into BrD3, and admits _a lot_ of units.
    |*)
  Lemma brD2_assoc X : forall (t u v : ctree E C X),
	    brD2 (brD2 t u) v ~ brD2 t (brD2 u v).
  Proof.
    intros.
    play; inv_trans; eauto 7 with trans.
  Qed.

  Lemma brD2_commut {X} : forall (t u : ctree E C X),
	    brD2 t u ~ brD2 u t.
  Proof.
    intros.
    play; inv_trans; eauto 6 with trans.
  Qed.

  Lemma brD2_idem {X} : forall (t : ctree E C X),
	    brD2 t t ~ t.
  Proof.
    intros.
    play; inv_trans; eauto 6 with trans.
  Qed.

  Lemma brD2_merge {X} : forall (t u v : ctree E C X),
	    brD2 (brD2 t u) v ~ brD3 t u v.
  Proof.
    intros.
    play; inv_trans; eauto 7 with trans.
  Qed.

  Lemma brD2_is_stuck {X} : forall (u v : ctree E C X),
      is_stuck u ->
	    brD2 u v ~ v.
  Proof.
    intros * ST.
    play.
    - inv_trans.
      exfalso; eapply ST, TR. (* automate stuck transition trying to step? *)
      exists l, t'; eauto.             (* automate trivial case *)
    - eauto 6 with trans.
  Qed.

  Lemma brD2_stuckS_l {X} : forall (t : ctree E C X),
	    brD2 stuckS t ~ t.
  Proof.
    intros; apply brD2_is_stuck, stuckS_is_stuck.
  Qed.

  Lemma brD2_stuckD_l {X} : forall (t : ctree E C X),
	    brD2 stuckD t ~ t.
  Proof.
    intros; apply brD2_is_stuck, stuckD_is_stuck.
  Qed.

  Lemma brD2_stuckS_r {X} : forall (t : ctree E C X),
	    brD2 t stuckS ~ t.
  Proof.
    intros; rewrite brD2_commut; apply brD2_stuckS_l.
  Qed.

  Lemma brD2_stuckD_r {X} : forall (t : ctree E C X),
	    brD2 t stuckD ~ t.
  Proof.
    intros; rewrite brD2_commut; apply brD2_stuckD_l.
  Qed.

  Lemma brD2_spinD_l {X} : forall (t : ctree E C X),
	    brD2 spinD t ~ t.
  Proof.
    intros; apply brD2_is_stuck, spinD_is_stuck.
  Qed.

  Lemma brD2_spinD_r {X} : forall (t : ctree E C X),
	    brD2 t spinD ~ t.
  Proof.
    intros; rewrite brD2_commut; apply brD2_is_stuck, spinD_is_stuck.
  Qed.

(*|
BrS2 is commutative and "almost" idempotent
|*)
  Lemma brS2_commut : forall X (t u : ctree E C X),
	    brS2 t u ~ brS2 u t.
  Proof.
    intros.
    play; inv_trans; subst.
    all: do 2 eexists; split; [| split; [rewrite EQ; reflexivity| reflexivity]]; etrans.
  Qed.

  Lemma brS2_idem : forall X (t : ctree E C X),
	    brS2 t t ~ Step t.
  Proof.
    intros.
    play; inv_trans; subst.
    all: do 2 eexists; split; [| split; [rewrite EQ; reflexivity| reflexivity]]; etrans.
  Qed.

(*|
Inversion principles
--------------------
|*)
  Lemma sbisim_ret_inv X (r1 r2 : X) :
    (Ret r1 : ctree E C X) ~ (Ret r2 : ctree E C X) -> r1 = r2.
  Proof.
    intro.
    eplayL.
    now inv_trans.
  Qed.

(*|
 For the next few lemmas, we need to know that [X] is inhabited in order to
 take a step
|*)
  Lemma sbisim_vis_invT {X X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E C X) (x : X1):
    Vis e1 k1 ~ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplayL.
    inv TR; auto.
    Unshelve. auto.
  Qed.

  Lemma sbisim_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) :
    Vis e1 k1 ~ Vis e2 k2 ->
    e1 = e2 /\ forall x, k1 x ~ k2 x.
  Proof.
    intros.
    split.
    - eplayL.
      etrans.
      inv_trans; eauto.
    - intros.
      clear x.
      eplayL.
      inv_trans.
      subst. eauto.
      Unshelve. auto.
  Qed.

  Lemma sbisim_BrS_inv {X Y Z}
        c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree E C Z) :
    BrS c1 k1 ~ BrS c2 k2 ->
    (forall i1, exists i2, k1 i1 ~ k2 i2).
  Proof.
    intros EQ i1.
    eplayL.
    inv_trans.
    eexists; eauto.
  Qed.

  (*|
    Annoying case: [Vis e k ~ BrS c k'] is true if [e : E void] and [c : C void].
    We rule out this case in this definition.
    |*)
  Definition are_bisim_incompat {X} (t u : ctree E C X) : Type :=
    match observe t, observe u with
    | RetF _, RetF _
    | VisF _ _, VisF _ _
    | BrF true _ _, BrF true _ _
    | BrF false _ _, _
    | _, BrF false _ _ => False
    | BrF true n _, RetF _ => True
    | RetF _,  BrF true n _ => True
    | @BrF _ _ _ _ true X _ _, @VisF _ _ _ _ Y _ _ =>
        inhabited X + inhabited Y
    | @VisF _ _ _ _ Y _ _, @BrF _ _ _ _ true X _ _ =>
        inhabited X + inhabited Y
    | _, _ => True
    end.

  Lemma sbisim_absurd {X} (t u : ctree E C X) :
    are_bisim_incompat t u ->
    t ~ u ->
    False.
  Proof.
    intros * IC EQ.
    unfold are_bisim_incompat in IC.
    setoid_rewrite ctree_eta in EQ.
    genobs t ot. genobs u ou.
    destruct ot, ou;
      (try now inv IC); (try destruct vis); (try destruct vis0);
      try now inv IC.
    - playL in EQ. inv_trans.
    - playL in EQ. inv_trans.
    - playR in EQ. inv_trans.
    - destruct IC as [[] | []]; [ playR in EQ | playL in EQ ]; inv_trans.
    - playR in EQ. inv_trans.
    - destruct IC as [[] | []]; [ playL in EQ | playR in EQ ]; inv_trans.
    Unshelve. all: auto.
  Qed.

  Ltac sb_abs h :=
    eapply sbisim_absurd; [| eassumption]; cbn; try reflexivity.

  Lemma sbisim_ret_vis_inv {X Y}(r : Y) (e : E X) (k : X -> ctree E C Y) :
    (Ret r : ctree E C _) ~ Vis e k -> False.
  Proof.
    intros * abs. sb_abs abs.
  Qed.

  Lemma sbisim_ret_BrS_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    (Ret r : ctree E C _) ~ BrS c k -> False.
  Proof.
    intros * abs; sb_abs abs.
  Qed.

  (*|
    For this to be absurd, we need one of the return types to be inhabited.
    |*)
  Lemma sbisim_vis_BrS_inv {X Y Z}
        (e : E X) (k1 : X -> ctree E C Z) (c : C Y) (k2: Y -> ctree E C Z) (y : Y) :
    Vis e k1 ~ BrS c k2 -> False.
  Proof.
    intros * abs.
    sb_abs abs. eauto.
  Qed.

  Lemma sbisim_vis_BrS_inv' {X Y Z}
        (e : E X) (k1 : X -> ctree E C Z) (c : C Y) (k2: Y -> ctree E C Z) (x : X) :
    Vis e k1 ~ BrS c k2 -> False.
  Proof.
    intros * abs.
    sb_abs abs. eauto.
  Qed.

(*|
Not fond of these two, need to give some thoughts about them
|*)
  Lemma sbisim_ret_BrD_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    (Ret r : ctree E C _) ~ BrD c k ->
    exists x, (Ret r : ctree E C _) ~ k x.
  Proof.
    intro. step in H. destruct H as [Hf Hb]. cbn in *.
    edestruct Hf as (x & ? & Ht & Hs & ?); [apply trans_ret |].
    apply trans_brD_inv in Ht.
    destruct Ht as [i Ht]. exists i.
    step. split.
    - repeat intro. inv H0. exists (val r), x0. split; intuition. rewrite <- Hs.
      rewrite ctree_eta. rewrite <- H4. rewrite br0_always_stuck. reflexivity.
    - repeat intro. eapply trans_brD in H0; eauto.
  Qed.

  Lemma sbisim_BrD_1_inv X (c1: C (fin 1)) (k : fin 1 -> ctree E C X) (t: ctree E C X) i :
    BrD c1 k ~ t ->
    k i ~ t.
  Proof.
    intro. step in H. step. destruct H. cbn in *. split; repeat intro.
    - apply H. econstructor; apply H1.
    - edestruct H0. apply H1. exists x; auto.
      destruct H2 as (? & ? & ? & ?); subst.
      destruct (trans_brD_inv H2) as (j & ?).
      assert (i = j).
      {
        remember 1%nat.
        destruct i.
        - dependent destruction j; auto.
          inv Heqn. inv j.
        - inv Heqn. inv i.
      }
      subst. eauto.
  Qed.

End WithParams.

Section StrongSimulations.

  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

  Notation ss := (@ss E F C D X Y _ _).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssim  := (@ssim E F C D X Y _ _).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

  Lemma sbisim_clos_ss : @sbisim_clos E F C D X Y _ _ eq eq <= (sst L).
  Proof.
    intro R1. apply Coinduction.
    cbn; intros Rs x y [z x' y' z' SBzx' x'y' SBy'z'].
    - intros l t zt.
      step in SBzx'.
      apply SBzx' in zt as (l' & t' & x't' & ? & ?); subst.
      destruct (x'y' _ _ x't') as (l'' & t'' & y't'' & ? & ?).

      step in SBy'z'.
      apply SBy'z' in y't'' as (ll & tt & z'tt & ? & ?); subst.
      exists ll, tt; split; trivial.
      + split; trivial.
        apply (f_Tf (ss L)).
        econstructor; eauto.
  Qed.

(*|
    Instances for rewriting [sbisim] under all [ss]-related contexts
|*)
  #[global] Instance sbisim_eq_clos_ssim_goal:
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (ssim L).
  Proof.
    cbn.
    coinduction R CH. intros * EQ1 * EQ2 SIM.
    do 2 red; cbn; intros * TR.
    symmetry in EQ2.
    step in EQ1; apply EQ1 in TR as (? & ? & ? & ? & ?).
    step in SIM; apply SIM in H as (? & ? & ? & ? & ?).
    step in EQ2; apply EQ2 in H as (? & ? & ? & ? & ?); subst.
    do 2 eexists.
    split; [eassumption |].
    split; [| eassumption].
    symmetry in H4. eapply CH; eassumption.
  Qed.

  #[global] Instance sbisim_eq_clos_ssim_ctx :
    Proper (sbisim eq ==> sbisim eq ==> impl) (ssim L).
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_eq_clos_ssim_goal; eauto.
  Qed.

  #[global] Instance sbisim_eq_clos_sst_goal RR :
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t sbisim_clos_ss). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_eq_clos_sst_ctx RR :
    Proper (sbisim eq ==> sbisim eq ==> impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_eq_clos_ssT_goal RR f :
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T sbisim_clos_ss). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_eq_clos_ssT_ctx RR f :
    Proper (sbisim eq ==> sbisim eq ==> impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

End StrongSimulations.

Section CompleteStrongSimulations.

  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

  Notation css := (@css E F C D X Y _ _).
  Notation csst L := (coinduction.t (css L)).
  Notation cssim  := (@cssim E F C D X Y _ _).
  Notation cssbt L := (coinduction.bt (css L)).
  Notation cssT L := (coinduction.T (css L)).


(*|
A bisimulation trivially gives a simulation.
|*)
  Lemma sb_css : forall RR (t : ctree E C X) (t' : ctree F D Y),
      sb L RR t t' -> css L RR t t'.
  Proof.
    intros; split.
    - apply H.
    - intros. apply H in H0 as (? & ? & ? & ? & ?). eauto.
  Qed.

  (* TODO MOVE to CSim *)
  Lemma cssim_ssim : forall (t : ctree E C X) (t' : ctree F D Y),
      cssim L t t' -> ssim L t t'.
  Proof.
    coinduction R CH. simpl. intros.
    step in H.
    apply H in H0 as (? & ? & ? & ? & ?).
    apply CH in H1.
    exists x, x0; eauto.
  Qed.

  Lemma sbisim_cssim : forall (t : ctree E C X) (t' : ctree F D Y),
      sbisim L t t' -> cssim L t t'.
  Proof.
    coinduction R CH. simpl. intros.
    split; step in H; intros;
      apply H in H0 as (? & ? & ? & ? & ?);
      exists x, x0; auto.
  Qed.

(*|
Various results on reflexivity and transitivity.
|*)
  Lemma sbisim_clos_css : @sbisim_clos E F C D X Y _ _ eq eq <= (csst L).
  Proof.
    intro R1. apply Coinduction.
    cbn; intros Rs x y [z x' y' z' SBzx' [x'y' y'x'] SBy'z']; split.
    - intros l t zt.
      step in SBzx'.
      apply SBzx' in zt as (l' & t' & x't' & ? & ?); subst.
      destruct (x'y' _ _ x't') as (l'' & t'' & y't'' & ? & ?).

      step in SBy'z'.
      apply SBy'z' in y't'' as (ll & tt & z'tt & ? & ?); subst.
      exists ll, tt; split; trivial.
      + split; trivial.
        apply (f_Tf (css L)).
        econstructor; eauto.
    - intros l t z't.
      step in SBy'z'.
      symmetry in SBy'z'.
      apply SBy'z' in z't as (l' & t' & y't' & ? & ?); subst.
      destruct (y'x' _ _ y't') as (l'' & t'' & y't'').
      step in SBzx'.
      apply SBzx' in y't'' as (ll & tt & ztt & ?); subst.
      exists ll, tt; trivial.
  Qed.

(*|
    Aggressively providing instances for rewriting hopefully faster
    [sbisim] under all [ss1]-related contexts (consequence of the transitivity
    of the companion).
|*)
  #[global] Instance sbisim_clos_cssim_goal:
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (cssim L).
  Proof.
    cbn.
    coinduction R CH. intros * EQ1 * EQ2 SIM.
    do 2 red; cbn; split; intros * TR.
    - symmetry in EQ2.
      step in EQ1; apply EQ1 in TR as (? & ? & ? & ? & ?).
      step in SIM; apply SIM in H as (? & ? & ? & ? & ?).
      step in EQ2; apply EQ2 in H as (? & ? & ? & ? & ?); subst.
      do 2 eexists.
      split; [eassumption |].
      split; [| eassumption].
      symmetry in H4. eapply CH; eassumption.
    - step in EQ2; apply EQ2 in TR as (? & ? & ? & ? & ?).
      step in SIM. apply SIM in H as (? & ? & ?).
      step in EQ1. apply EQ1 in H as (? & ? & ? & ?); simpl in *; subst.
      do 2 eexists.
      eauto.
  Qed.

  #[global] Instance sbisim_clos_cssim_ctx :
    Proper (sbisim eq ==> sbisim eq ==> impl) (cssim L).
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_clos_cssim_goal; eauto.
  Qed.

  #[global] Instance sbisim_clos_csst_goal RR :
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (csst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t sbisim_clos_css). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_clos_csst_ctx RR :
    Proper (sbisim eq ==> sbisim eq ==> impl) (csst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_cssT_goal RR f :
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (cssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T sbisim_clos_css). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_clos_ccssT_ctx RR f :
    Proper (sbisim eq ==> sbisim eq ==> impl) (cssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow choices with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary choice.
|*)

  Lemma css_sb : forall RR (t : ctree E C X) (t' : ctree F D Y),
      css L RR t t' ->
      CSSim.css (flip L) (flip RR) t' t ->
      sb L RR t t'.
  Proof.
    split; cbn; intros.
    - apply H in H1 as (? & ? & ? & ? & ?); eauto.
    - apply H0 in H1 as (? & ? & ? & ? & ?); eauto.
  Qed.

  (* TODO MOVE To Trans *)
  Lemma ctree_B01_trans_det : forall {E X} l (t t' t'' : ctree E B01 X),
      trans l t t' -> trans l t t'' -> t' ≅ t''.
  Proof.
    intros. do 3 red in H.
    rewrite ctree_eta in H0.
    genobs t ot. genobs t' ot'. rewrite ctree_eta, <- Heqot'.
    clear t t' Heqot Heqot'. revert t'' H0.
    dependent induction H; intros; inv_trans.
    - eapply IHtrans_; cbn.
      rewrite <- ctree_eta.
      destruct c, b, x0, x; intuition.
    - rewrite <- ctree_eta. destruct c, b, x, x0.
      now rewrite H.
    - subst. rewrite <- ctree_eta. now rewrite H.
    - apply br0_always_stuck.
  Qed.
  
  Lemma trans_val_sbisim : forall (t t' u: ctree E C X) (x: X),
      trans (val x) t t' ->
      t ~ u ->
      exists s, s ≅ stuckD /\ trans (val x) u s.
  Proof.
    intros * TR EQ.
    step in EQ.
    destruct EQ as [Fwd _].
    apply Fwd in TR as (? & s & ? & ? & <-).
    exists s; split; auto.
    exact (trans_val_inv H).
  Qed.

End CompleteStrongSimulations.

Section StrongSimulations.

  Section Heterogeneous.
    Context {E F C D: Type -> Type} {X Y: Type}
      {L: rel (@label E) (@label F)}
      {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.
    Notation ss := (@ss E F C D X Y _ _).
    Notation sst L := (coinduction.t (ss L)).
    Notation ssim  := (@ssim E F C D X Y _ _).
    Notation ssbt L := (coinduction.bt (ss L)).
    Notation ssT L := (coinduction.T (ss L)).

    Lemma sbisim_ssim : forall (t : ctree E C X) (t' : ctree F D Y),
        sbisim L t t' -> ssim L t t'.
    Proof.
      intros. apply cssim_ssim. now apply sbisim_cssim.
    Qed.

  End Heterogeneous.

  Section Homogeneous.
    Context {E C: Type -> Type} {X: Type}
      {L: rel (@label E) (@label E)}
      {HasStuck1: B0 -< C}.
    Notation ss := (@ss E E C C X X _ _).
    Notation sst L := (coinduction.t (ss L)).
    Notation ssim  := (@ssim E E C C X X _ _).
    Notation ssbt L := (coinduction.bt (ss L)).
    Notation ssT L := (coinduction.T (ss L)).

(*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under all [ss1]-related contexts (consequence of the transitivity
of the companion).
|*)
  #[global] Instance sbisim_clos_ssim_goal `{Symmetric _ L} `{Transitive _ L} :
    Proper (sbisim L ==> sbisim L ==> flip impl) (ssim L).
  Proof.
    repeat intro.
    transitivity y0. transitivity y.
    - now apply sbisim_ssim in H1.
    - now exact H3.
    - symmetry in H2; now apply sbisim_ssim in H2.
  Qed.

  #[global] Instance sbisim_clos_ssim_ctx `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> impl) (ssim L).
  Proof.
    repeat intro. symmetry in H0, H1. eapply sbisim_clos_ssim_goal; eauto.
  Qed.

  #[global] Instance sbisim_clos_sst_goal RR `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H0.
    symmetry in eq2. apply sbisim_ssim in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sst_ctx RR `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_goal RR f `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> flip impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    symmetry in eq2. apply sbisim_ssim in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_ctx RR f `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow brs with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary br.
|*)

  End Homogeneous.

  Lemma ss_sb : forall {E F B C X Y} `{B0 -< B} `{B0 -< C} {L} {R : rel (ctree E B X) (ctree F C Y)} t t',
    sb L R t t' ->
    ss L R t t'.
  Proof.
    intros. apply H1.
  Qed.

  Lemma split_sb_eq : forall {E C X} RR {HasStuck: B0 -< C}
                  (t t' : ctree E C X),
      ss eq RR t t' ->
      ss eq (flip RR) t' t ->
      sb eq RR t t'.
  Proof.
    intros.
    split; eauto.
    simpl in *; intros.
    destruct (H0 _ _ H1) as (? & ? & ? & ? & ?).
    destruct (H _ _ H2) as (? & ? & ? & ? & ?).
    subst; eauto.
  Qed.

  Lemma split_sbt_eq : forall {E B X R} `{HasB0: B0 -< B} (t u : ctree E B X), sbt eq R t u <->
    ss eq (st eq R) t u /\ ss eq (st eq R) u t.
  Proof.
    split; intro.
    - split; [apply H |].
      symmetry in H. apply H.
    - apply split_sb_eq. { apply H. }
      destruct H as [_ H].
      cbn. intros. apply H in H0 as (? & ? & ? & ? & ?).
      unfold flip in H1, H2. symmetry in H1. etrans.
  Qed.

  Lemma split_sbisim_eq : forall {E B X} `{HasB0: B0 -< B} (t u : ctree E B X),
    t ~ u <->
    ss eq (sbisim eq) t u /\ ss eq (sbisim eq) u t.
  Proof.
    split; intro.
    - step in H. split; [apply H |].
      symmetry in H. apply H.
    - step. split; [apply H |].
      destruct H as [_ ?].
      eapply weq_ss with (y := eq). { cbn. split; auto. }
      eapply (Hbody (ss eq)). 2: apply H.
      cbn. intros. now symmetry.
  Qed.

  #[local] Definition t1 : ctree void1 (B0 +' B1 +' B2) unit :=
    Step (Ret tt).

  #[local] Definition t2 : ctree void1 (B0 +' B1 +' B2) unit :=
    brS2 (Ret tt) (stuckD).

  Lemma ssim_sbisim_nequiv :
    ssim eq t1 t2 /\ ssim eq t2 t1 /\ ~ sbisim eq t1 t2.
  Proof.
    unfold t1, t2. intuition.
    - step.
      apply step_ss_brS; auto.
      intros _. exists true. reflexivity.
    - step. apply step_ss_brS; auto.
      intros [|]; exists tt.
      + reflexivity.
      + step. apply stuckD_ss.
    - step in H. cbn in H. destruct H as [_ ?].
      specialize (H tau stuckD). lapply H; [| etrans].
      intros. destruct H0 as (? & ? & ? & ? & ?).
      inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
      specialize (H0 (val tt) stuckD). lapply H0.
      2: subst; etrans.
      intro; destruct H1 as (? & ? & ? & ? & ?).
      now apply stuckD_is_stuck in H1.
  Qed.

End StrongSimulations.

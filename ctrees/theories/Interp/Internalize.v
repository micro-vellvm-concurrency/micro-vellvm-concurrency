From CTree Require Import
     CTree Eq Interp.Fold Interp.FoldCTree.

Set Implicit Arguments.
Set Contextual Implicit.

Import CTreeNotations.

Section Internalize.
  Variable E C : Type -> Type.
  Variable ExtChoice : Type -> Type.
  Context `{B1 -< C}.

  Definition internalize_h : ExtChoice ~> ctree E (B01 +' C +' ExtChoice) :=
    fun _ e => branch true e.

  Definition internalize_h' : ExtChoice +' E ~> ctree E (B01 +' C +' ExtChoice) :=
    fun _ e => match e with
            | inl1 e => internalize_h e
            | inr1 e => trigger e
            end.

  Definition internalize : ctree (ExtChoice +' E) (B01 +' C) ~> ctree E (B01 +' C +' ExtChoice) :=
    interp internalize_h'.

  Lemma internalize_ret {R} (r : R) : internalize (Ret r) ≅ Ret r.
  Proof.
    unfold internalize.
    rewrite interp_ret.
    reflexivity.
  Qed.

  Lemma internalize_bind {R S} (t : ctree _ _ R) (k : R -> ctree _ _ S) :
    internalize (t >>= k) ≅ internalize t >>= (fun x => internalize (k x)).
  Proof.
    unfold internalize.
    rewrite interp_bind.
    reflexivity.
  Qed.

End Internalize.

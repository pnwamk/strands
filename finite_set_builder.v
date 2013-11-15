
Require Import Ensembles Finite_sets Finite_sets_facts.
Require Import List ListSet.
Require Import util set_rep_equiv strandlib.
Require Import LibTactics.

Open Scope list_scope.

Section set_builder.

Variable X : Type.
 Hypothesis Xeq_dec : forall x y : X, {x=y}+{x<>y}.

Variable P: X -> Prop.
 Hypothesis Pdec : forall x, {P x}+{~P x}.

Lemma nodup_filter : forall (s: set X) f,
NoDup s ->
NoDup (filter f s).
Proof.
  intros s f nodup.
  induction s.
  simpl. constructor.
  simpl. destruct (f a).
  constructor. intros contra.
  inversion nodup; subst.
  destruct (filter_In f a s). apply H in contra.
  destruct contra; contradiction.
  apply IHs. inversion nodup; auto.
  apply IHs. inversion nodup; auto.
Qed.  

Lemma ex_filter_set : forall s,
exists s', subset s' s /\
forall x, set_In x s' <-> set_In x s /\ P x.
Proof.
  intros s.
  induction s.
  exists (nil : list X).
  split. intros x y. tryfalse.
  split. intros xIn. tryfalse.
  intros [xIn Px]. tryfalse.
  destruct IHs as [s' [Hsub HallP]].
  destruct (Pdec a).
  exists (a :: s').
  split. intros x Hin.
  destruct Hin. subst. left; reflexivity.
  right. eauto.
  split.
  intros Hin.
  destruct Hin. subst. split; auto. left. auto.
  split. right. auto. apply HallP. auto.
  intros H.
  destruct H. destruct H. subst. left. reflexivity.
  right. apply HallP. auto.
  exists s'. split.
  right. auto.
  split; intros.
  split. right. apply HallP. auto. apply HallP. auto.
  destruct H. destruct H. subst. tryfalse.
  apply HallP. auto.
Qed. 

Lemma ex_filter_ensemble : forall (E: Ensemble X),
Finite X E ->
exists E', Included X E' E 
/\ (forall e, Ensembles.In X E' e -> Ensembles.In X E e /\ P e)
/\ (forall e, Ensembles.In X E e /\ P e ->  Ensembles.In X E' e).
Proof.
  intros E Efin.
  destruct (ensemble_imp_set X Xeq_dec E Efin) 
    as [s [allIn [nodup [n [lenn cardn]]]]].
  remember (fun x => if Pdec x then true else false) as Pbool.
  remember (filter_In Pbool) as filterP.
  remember (filter Pbool s) as s'.
  assert (NoDup (filter Pbool s)) as nodups'.
    apply nodup_filter. exact nodup.
  rewrite <- Heqs' in nodups'.
  destruct (set_imp_ensemble X Xeq_dec s' nodups') 
    as [E' [allIn' [n' [ len' card']]]].
  exists E'.
  split.
  intros e eIn. apply allIn' in eIn. rewrite Heqs' in eIn.
  apply filterP in eIn. destruct eIn as [eIn Pbtrue].
  apply allIn in eIn. exact eIn.
  split.
  intros x eIn. split.
  apply allIn. apply filterP. rewrite <- Heqs'. apply allIn'.
  exact eIn.
  assert (Pbool x = true) as Pet. eapply (filterP x s).
  rewrite <- Heqs'. apply allIn'. exact eIn.
  rewrite HeqPbool in Pet.
  destruct (Pdec x). exact p. inversion Pet. 
  intros x [xIn Px].
  apply allIn'. rewrite Heqs'. apply filterP.
  split. apply allIn. exact xIn.
  rewrite HeqPbool.
  remember (Pdec x) as popts. destruct popts. reflexivity.
  contradiction.
Qed.

End set_builder.

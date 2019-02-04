Require Import SetoidClass.
Require Import Permutation.
Require Import List.
Require Import ListSet.
Import ListNotations.

Class Eq_Dec (A : Type) : Type := {
  eq_dec  : forall (x y : A), {x = y} + {x <> y}
}.

Definition dec2bool {A B : Type} (P : A -> B -> Prop) (p_dec : forall x y, {P x y} + {~P x y}) : A -> B -> bool := fun x y => if p_dec x y then true else false.

Lemma dec2decidable {A B : Type} (P : A -> B -> Prop) (p_dec : forall x y, {P x y} + {~P x y}) : forall x y, P x y \/ ~P x y.
Proof.
  intros x y.
  destruct (p_dec x y); intuition.
Qed.

Lemma Nodup_idemp {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y}) : forall l, NoDup l -> nodup eq_dec l = l.
Proof.
  induction l; intros.
  trivial.
  unfold nodup.
  case (in_dec eq_dec a l); intros.
  inversion H; contradiction.
  fold (nodup eq_dec l); rewrite IHl; trivial.
  apply NoDup_cons_iff in H; intuition.
Qed.

Ltac antisymmetry := apply (partial_order_antisym _).

Section Permutations.

Context {A : Type}.
Context {D : Eq_Dec A}.

Fixpoint findIndex_aux (x : A) (l : list A) (n : nat) : option nat :=
  match l with
    | [] => None
    | (y::ys) => if eq_dec x y then Some n else findIndex_aux x ys (S n)
  end.

Lemma findIndex_aux1 : forall (x : A) (l : list A) (n : nat), findIndex_aux x (x::l) n = Some n.
Proof.
  intros x l n.
  unfold findIndex_aux.
  case (eq_dec x x); [ trivial | contradiction ].
Qed.

Lemma findIndex_aux2 : forall (x a : A) (l : list A) (n : nat), x <> a -> findIndex_aux x (a::l) n = findIndex_aux x l (S n).
Proof.
  intros x a l n H.
  unfold findIndex_aux. 
  case (eq_dec x a); [ contradiction | trivial ].
Qed.

Lemma findIndex_aux3 : forall x l m n, findIndex_aux x l m = Some n -> m <= n.
Proof.
  intro x; induction l; intros m n H.
  inversion H.
  case (eq_dec x a); intros.
  rewrite e, findIndex_aux1 in H; inversion H; reflexivity.
  rewrite (findIndex_aux2 _ _ _ _ n0) in H.
  apply IHl in H.
  rewrite <- H.
  apply PeanoNat.Nat.le_succ_diag_r.
Qed.

Lemma findIndex_aux4 : forall (x a : A) (l : list A) (n : nat), findIndex_aux x (a::l) n = Some n -> x = a.
Proof.
  intros x a l n.
  case (eq_dec x a); intros; [ trivial |].
  rewrite (findIndex_aux2 _ _ _ _ n0) in H.
  apply findIndex_aux3 in H.
  apply PeanoNat.Nat.nle_succ_diag_l in H; contradiction.
Qed.

Lemma findIndex_aux5 : forall (x : A) (l : list A) (n m : nat), findIndex_aux x l (S n) = Some (S m) -> findIndex_aux x l n = Some m.
Proof.
  intro x; induction l; intros m n H.
  inversion H.
  case_eq (eq_dec x a); intros.
  rewrite e in H; rewrite findIndex_aux1 in H; inversion H; rewrite e; apply findIndex_aux1.
  rewrite (findIndex_aux2 _ _ _ _ n0) in H; rewrite (findIndex_aux2 _ _ _ _ n0).
  apply (IHl _ _ H).
Qed.

Lemma findIndex_aux6 : forall (x : A) (l : list A) (n : nat), findIndex_aux x l (S n) = None -> findIndex_aux x l n = None.
Proof.
  intro x; induction l; intros n H.
  trivial.
  case_eq (eq_dec x a); intros.
  rewrite e, findIndex_aux1 in H; inversion H.
  rewrite (findIndex_aux2 _ _ _ _ n0) in H; rewrite (findIndex_aux2 _ _ _ _ n0).
  apply (IHl _ H).
Qed.

Definition findIndex (x : A) (l : list A) : option nat := findIndex_aux x l 0.

Lemma findIndex1 :  forall n x l, findIndex x l = Some n -> l = firstn n l ++ x::skipn (S n) l.
Proof.
  induction n; intros x l H.
  case_eq l; intros.
  rewrite H0 in H; inversion H.
  rewrite H0 in H. 
  unfold findIndex in H; apply (findIndex_aux4) in H; rewrite H; trivial.
  case_eq l; intros.
  rewrite H0 in H; inversion H.
  simpl; replace (match l0 with | [] => []  | _ :: l1 => skipn n l1 end) with (skipn (S n) l0) by trivial.
  rewrite <- IHn; [ trivial |].
  rewrite H0 in H.
  unfold findIndex in H.
  case_eq (eq_dec x a); intros.
  rewrite e, findIndex_aux1 in H; inversion H.
  rewrite (findIndex_aux2 _ _ _ _ n0) in H.
  apply (findIndex_aux5 _ _ _ _ H).
Qed.

Lemma findIndex2 : forall x l, findIndex x l = None -> ~In x l.
Proof.
  intros x l H.
  induction l; intros.
  apply in_nil.
  unfold findIndex in H.
  case_eq (eq_dec x a); intros.
  rewrite e, findIndex_aux1 in H; inversion H.
  rewrite (findIndex_aux2 _ _ _ _ n) in H.
  apply not_in_cons; split; [ assumption |].
  apply IHl.
  unfold findIndex; apply (findIndex_aux6 _ _ 0 H).
Qed.

Lemma Permutation_middle_iff : forall (a : A) l l1 l2, Permutation l (l1 ++ l2) <-> Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  intros; split; intros.
  apply (perm_skip a) in H.
  apply (Permutation_trans H), Permutation_middle.
  apply (fun H => Permutation_trans H (Permutation_sym (Permutation_middle l1 l2 a))) in H.
  apply (Permutation_cons_inv H).
Qed.

Lemma perm_dec : forall (l1 l2:list A), {Permutation l1 l2} + {~Permutation l1 l2}.
Proof.
  induction l1; intro l2.
  case l2.
  left; apply perm_nil.
  right; apply Permutation_nil_cons.
  case_eq (findIndex a l2); intros.
  apply findIndex1 in H; rewrite H.
  specialize IHl1 with (firstn n l2 ++ skipn (S n) l2).
  destruct IHl1.
  left; apply Permutation_middle_iff; assumption.
  right; contradict n0; apply Permutation_middle_iff in n0; assumption.
  right; apply findIndex2 in H; contradict H.
  apply (Permutation_in a H (in_eq a l1)).
Qed.

End Permutations.

Section Sets1.

Context {A : Type}.
Context {D : Eq_Dec A}.

Definition FSet A : Type := { l : list A | NoDup l }.

Definition fromList (l : list A) : FSet A := exist _ (nodup eq_dec l) (NoDup_nodup eq_dec l).

Definition empty_set : FSet A := fromList [].

Definition elem_set (x : A) (s : FSet A) : Prop := In x (proj1_sig s).

Definition incl_set (s1 s2 : FSet A) : Prop := forall x, elem_set x s1 -> elem_set x s2.

End Sets1.

Notation "'Ø'" := (empty_set).
Notation "'❴' x '❵'" := (fromList [x]).
Notation "'❴' x ',' y ',' .. ',' z '❵'" := (fromList (cons x (cons y .. (cons z nil) ..))).
Infix "∈" := (elem_set) (at level 70).
Notation "x ∉ s" := (~elem_set x s) (at level 70).
Infix "⊆" := (incl_set) (at level 75).

Section Sets2.

Context {A : Type}.
Context {D : Eq_Dec A}.

Global Instance SetSetoid : Setoid (FSet A)  := {|
  equiv := fun s1 s2 => Permutation (proj1_sig s1) (proj1_sig s2)
|}.
Proof.
  split.
  unfold Reflexive; intro s; apply Permutation_refl.
  unfold Symmetric; intros s1 s2; apply Permutation_sym.
  unfold Transitive; intros s1 s2 s3; apply Permutation_trans.
Defined.

Global Instance ElemProper : Proper (eq ==> equiv ==> iff) elem_set.
Proof.
  unfold Proper, "==>"; intros x y H s1 s2 H0.
  rewrite <- H; destruct s1 as [l1 p1], s2 as [l2 p2]; unfold elem_set; simpl in *.
  split; apply Permutation_in; [ | apply Permutation_sym ]; assumption.
Qed.

Lemma fset_exten : forall (s1 s2 : FSet A), s1 == s2 <-> (forall x, x ∈ s1 <-> x ∈ s2).
Proof.
  intros s1 s2; split; intros.
  rewrite H; reflexivity.
  destruct s1 as [l1 p1], s2 as [l2 p2]; unfold elem_set in H; simpl in *.
  apply (NoDup_Permutation p1 p2 H).
Qed.

Global Instance incl_PreOrder : PreOrder (@incl_set A).
Proof.
  split.
  unfold Reflexive; intros s x; trivial.
  unfold Transitive; intros s1 s2 s3 H H0 x; intuition.
Defined.

Global Instance incl_PartialOrder : PartialOrder (@equiv _ SetSetoid) (@incl_set A).
Proof.
  intros s1 s2; split; unfold incl_set, Basics.flip, relation_conjunction, predicate_intersection, pointwise_extension.
  intros H; split; intro x; rewrite fset_exten in H; specialize H with x; intuition.
  rewrite fset_exten; intros H x; destruct H; specialize H with x; specialize H0 with x; intuition.
Defined.

Global Instance elem_incl_proper (x : A) : Proper (@incl_set A ==> Basics.impl) (elem_set x).
Proof.
  unfold Proper, "==>"; intros s1 s2 H H0.
  unfold incl_set in H.
  apply H in H0; assumption.
Defined.

Definition toList (s : FSet A) : list A := proj1_sig s.

Definition union_set (s1 s2 : FSet A) : FSet A := 
  exist _ (set_union eq_dec (proj1_sig s1) (proj1_sig s2))
          (set_union_nodup eq_dec (proj2_sig s1) (proj2_sig s2)).

Global Instance UnionProper : Proper (equiv ==> equiv ==> equiv) union_set.
Proof.
  unfold Proper, "==>".
  intros s1 s1' H s2 s2' H0; destruct s1 as [l1 p1], s1' as [l1' p1'], s2 as [l2 p2], s2' as [l2' p2']; simpl in *.
  apply NoDup_Permutation; [ apply (set_union_nodup _ p1 p2)  | apply (set_union_nodup _ p1' p2') |].
  intro x.
  rewrite 2?set_union_iff; split; intros; destruct H1.
  left; apply (Permutation_in _ H H1).
  right; apply (Permutation_in _ H0 H1).
  left; apply (Permutation_in _ (Permutation_sym H) H1).
  right; apply (Permutation_in _ (Permutation_sym H0) H1).
Defined.

Definition inter_set (s1 s2 : FSet A) : FSet A := 
  exist _ (set_inter eq_dec (proj1_sig s1) (proj1_sig s2))
          (set_inter_nodup eq_dec (proj2_sig s1) (proj2_sig s2)).

Global Instance InterProper : Proper (equiv ==> equiv ==> equiv) inter_set.
Proof.
  unfold Proper, "==>". 
  intros s1 s1' H s2 s2' H0; destruct s1 as [l1 p1], s1' as [l1' p1'], s2 as [l2 p2], s2' as [l2' p2']; simpl in *.
  apply NoDup_Permutation; [ apply (set_inter_nodup _ p1 p2)  | apply (set_inter_nodup _ p1' p2') |].
  intro x.
  rewrite 2?set_inter_iff; split; intros; destruct H1; split.
  apply (Permutation_in _ H H1).
  apply (Permutation_in _ H0 H2).
  apply (Permutation_in _ (Permutation_sym H) H1).
  apply (Permutation_in _ (Permutation_sym H0) H2).
Defined.

Definition diff_set (s1 s2 : FSet A) : FSet A := 
  exist _ (set_diff eq_dec (proj1_sig s1) (proj1_sig s2))
          (set_diff_nodup eq_dec (proj2_sig s1) (proj2_sig s2)).

Global Instance DiffProper : Proper (equiv ==> equiv ==> equiv) diff_set.
Proof.
  unfold Proper, "==>". 
  intros s1 s1' H s2 s2' H0; destruct s1 as [l1 p1], s1' as [l1' p1'], s2 as [l2 p2], s2' as [l2' p2']; simpl in *.
  apply NoDup_Permutation; [ apply (set_diff_nodup _ p1 p2)  | apply (set_diff_nodup _ p1' p2') |].
  intro x.
  rewrite 2?set_diff_iff; split; intros; destruct H1; split.
  apply (Permutation_in _ H H1).
  intro; apply (Permutation_in _ (Permutation_sym H0)) in H3; contradiction.
  apply (Permutation_in _ (Permutation_sym H) H1).
  intro; apply (Permutation_in _ H0) in H3; contradiction.
Defined.

End Sets2.

Infix "∪" := (union_set) (at level 50, left associativity).
Infix "∩" := (inter_set) (at level 50, left associativity).
Infix "∖" := (diff_set) (at level 50, no associativity).

Section Sets3.

Context {A : Type}.
Context {D : Eq_Dec A}.

Lemma toFromList : forall (s : FSet A), fromList (toList s) == s.
Proof.
  intro s.
  destruct s as [l p]; simpl.
  rewrite (Nodup_idemp _ _ p); apply Permutation_refl.
Qed.

Lemma fromToList : forall (l : list A), toList (fromList l) = nodup eq_dec l.
Proof.
  intro l.
  unfold fromList, toList; trivial.
Qed.

Lemma fromList_in : forall x l, In x l <-> x ∈ fromList l.
Proof.
  intros x l.
  unfold fromList, elem_set; symmetry; apply nodup_In.
Qed.

Lemma toList_in : forall x (s : FSet A), x ∈ s <-> In x (toList s).
Proof.
  intros x s.
  rewrite <- toFromList at 1.
  symmetry; apply fromList_in.
Qed.

Definition elem_dec : forall (x : A) (s : FSet A), {x ∈ s} + {x ∉ s} := fun x s => in_dec eq_dec x (proj1_sig s).

Definition elem : A -> FSet A -> bool := dec2bool _ elem_dec.

Definition fset_equiv_dec : forall (s1 s2 : FSet A), {s1 == s2} + {s1 =/= s2} := fun s1 s2 : FSet A => perm_dec (proj1_sig s1) (proj1_sig s2).

(* Extras *)

Lemma elem_Prop : forall x s, elem x s = true <-> elem_set x s.
Proof.
  split; intros.
  destruct s as [l p]; simpl.
  unfold elem, dec2bool in H.
  destruct (elem_dec x (exist (fun l : list A => NoDup l) l p)).
  trivial.
  inversion H.
  unfold elem, dec2bool.
  destruct (elem_dec x s).
  trivial.
  contradiction.
Qed.

Lemma not_elem_Prop : forall x s, elem x s = false <-> ~elem_set x s.
Proof.
  split; intros.
  unfold elem, dec2bool in H; destruct (elem_dec x s).
  inversion H.
  trivial.
  unfold elem, dec2bool.
  destruct (elem_dec x s).
  contradiction.
  trivial.
Qed.

Lemma elem_singleton : forall x y, x ∈ ❴y❵ <-> x = y.
Proof.
  intros.
  unfold elem_set, fromList; simpl; intuition.
Qed.

(* End of extras *)

Lemma elem_empty : forall (x : A), x ∉ Ø.
Proof.
  intros x H.
  unfold elem_set, empty_set in H; simpl in H; contradiction.
Qed.

Lemma elem_union_iff : forall x s1 s2, x ∈ s1 ∪ s2 <-> x ∈ s1 \/ x ∈ s2.
Proof.
  intros x s1 s2.
  destruct s1 as [l1 p1], s2 as [l2 p2]; unfold union_set, elem_set; simpl.
  apply set_union_iff.
Qed.

Lemma union_idemp : forall (s : FSet A), s ∪ s == s.
Proof.
  intro s.
  apply fset_exten; intro x; rewrite elem_union_iff; intuition.
Qed.

Lemma union_empty_r : forall (s : FSet A), s ∪ Ø == s.
Proof.
  intro s.
  apply fset_exten; intro x; rewrite elem_union_iff; intuition.
Qed.

Lemma union_comm : forall s1 s2, s1 ∪ s2 == s2 ∪ s1.
Proof.
  intros s1 s2.
  apply fset_exten; intro x; rewrite 2?elem_union_iff; intuition.
Qed.

Lemma union_empty_l : forall (s : FSet A), Ø ∪ s == s.
Proof.
  intro s.
  rewrite union_comm; apply union_empty_r.
Qed.

Lemma union_assoc : forall s1 s2 s3, (s1 ∪ s2) ∪ s3 == s1 ∪ (s2 ∪ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite 4?elem_union_iff; intuition.
Qed.

Global Instance union_mono : Proper (incl_set ==> incl_set ==> incl_set) union_set.
Proof.
  unfold Proper, "==>".
  intros s1 s1' H s2 s2' H0.
  unfold incl_set; intro x; rewrite 2?elem_union_iff; intuition.
Defined.

Lemma union_exp_l : forall s1 s2, s1 ⊆ s1 ∪ s2.
Proof.
  intros s1 s2.
  unfold incl_set; intro x; rewrite elem_union_iff; intuition.
Qed.

Lemma union_exp_r : forall s1 s2, s2 ⊆ s1 ∪ s2.
Proof.
  intros s1 s2; rewrite union_comm; apply union_exp_l.
Qed.

Lemma union_glb : forall s s1 s2, s1 ∪ s2 ⊆ s <-> s1 ⊆ s /\ s2 ⊆ s.
Proof.
  intros s s1 s2; split; intros; [ split |].
  rewrite <- H; apply union_exp_l.
  rewrite <- H; apply union_exp_r.
  destruct H; rewrite H, H0, union_idemp; reflexivity.
Qed.

Lemma union_incl : forall s1 s2, s1 ⊆ s2 <-> s1 ∪ s2 == s2.
Proof.
  intros s1 s2; split; intro.
  antisymmetry.
  rewrite H; rewrite union_idemp; reflexivity.
  apply union_exp_r.
  rewrite <- H; apply union_exp_l.
Qed.

Lemma union_empty: forall (s1 s2 : FSet A), s1 ∪ s2 == Ø <-> s1 == Ø /\ s2 == Ø.
Proof.
  intros s1 s2.
  split; intros; [| destruct H ]. 
  rewrite 2?fset_exten; split; intro x; split; intros.
  rewrite <- H, elem_union_iff; intuition.
  contradiction.
  rewrite <- H, elem_union_iff; intuition.
  contradiction.
  rewrite H, H0; apply union_empty_r.
Qed.

Lemma elem_inter_iff : forall x s1 s2, x ∈ s1 ∩ s2 <-> x ∈ s1 /\ x ∈ s2.
Proof.
  intros x s1 s2.
  destruct s1 as [l1 p1], s2 as [l2 p2]; unfold inter_set, elem_set; simpl.
  apply set_inter_iff.
Qed.

Lemma inter_idemp : forall (s : FSet A), s ∩ s == s.
Proof.
  intro s.
  apply fset_exten; intro x; rewrite elem_inter_iff; intuition.
Qed.

Lemma inter_empty_r : forall (s : FSet A), s ∩ Ø == Ø.
Proof.
  intro s.
  apply fset_exten; intro x; rewrite elem_inter_iff; intuition.
Qed.

Lemma inter_comm : forall s1 s2, s1 ∩ s2 == s2 ∩ s1.
Proof.
  intros s1 s2.
  apply fset_exten; intro x; rewrite 2?elem_inter_iff; intuition.
Qed.

Lemma inter_empty_l : forall (s : FSet A), Ø ∩ s == Ø.
Proof.
  intro s.
  rewrite inter_comm; apply inter_empty_r.
Qed.

Lemma inter_assoc : forall s1 s2 s3, (s1 ∩ s2) ∩ s3 == s1 ∩ (s2 ∩ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite 4?elem_inter_iff; intuition.
Qed.

Global Instance inter_mono : Proper (incl_set ==> incl_set ==> incl_set) inter_set.
Proof.
  unfold Proper, "==>".
  intros s1 s1' H s2 s2' H0.
  unfold incl_set; intro x; rewrite 2?elem_inter_iff; intuition.
Defined.

Lemma inter_contr_l : forall s1 s2, s1 ∩ s2 ⊆ s1.
Proof.
  intros s1 s2.
  unfold incl_set; intro x; rewrite elem_inter_iff; intuition.
Qed.

Lemma inter_contr_r : forall s1 s2, s1 ∩ s2 ⊆ s2.
Proof.
  intros s1 s2; rewrite inter_comm; apply inter_contr_l.
Qed.

Lemma inter_lub : forall s s1 s2, s ⊆ s1 ∩ s2 <-> s ⊆ s1 /\ s ⊆ s2.
Proof.
  intros s s1 s2; split; intros; [ split |].
  rewrite H; apply inter_contr_l.
  rewrite H; apply inter_contr_r.
  destruct H; rewrite <- H, <- H0, inter_idemp; reflexivity.
Qed.

Lemma inter_incl : forall s1 s2, s1 ⊆ s2 <-> s1 ∩ s2 == s1.
Proof.
  intros s1 s2; split; intro.
  antisymmetry.
  apply inter_contr_l.
  rewrite <- H; rewrite inter_idemp; reflexivity.
  rewrite <- H; apply inter_contr_r.
Qed.

Lemma inter_union_distr : forall s1 s2 s3, s1 ∩ (s2 ∪ s3) == (s1 ∩ s2) ∪ (s1 ∩ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite elem_inter_iff, 2?elem_union_iff, 2?elem_inter_iff; intuition.
Qed.

Lemma union_inter_distr : forall s1 s2 s3, s1 ∪ (s2 ∩ s3) == (s1 ∪ s2) ∩ (s1 ∪ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite elem_union_iff, 2?elem_inter_iff, 2?elem_union_iff; intuition.
Qed.

Lemma elem_diff_iff : forall x s1 s2, x ∈ s1 ∖ s2 <-> x ∈ s1 /\ x ∉ s2.
Proof.
  intros x s1 s2.
  destruct s1 as [l1 p1], s2 as [l2 p2]; unfold diff_set, elem_set; simpl.
  apply set_diff_iff.
Qed.

Lemma diff_empty_l : forall s, Ø ∖ s == Ø.
Proof.
  intro s.
  apply fset_exten; intro x; rewrite elem_diff_iff; intuition.
Qed.

Lemma diff_empty_r : forall s, s ∖ Ø == s.
Proof.
  intro s.
  apply fset_exten; intro x; rewrite elem_diff_iff; intuition.
Qed.

Lemma diff_equal : forall s, s ∖ s == Ø.
Proof.
  intro s.
  apply fset_exten; intro x; rewrite elem_diff_iff; intuition.
Qed.

Lemma diff_union_l : forall s1 s2 s3, (s1 ∪ s2) ∖ s3 ==  (s1 ∖ s3) ∪ (s2 ∖ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite elem_union_iff, 3?elem_diff_iff, elem_union_iff; intuition.
Qed.

Lemma diff_union_r : forall s1 s2 s3, s1 ∖ (s2 ∪ s3) == (s1 ∖ s2) ∩ (s1 ∖ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite elem_inter_iff, 3?elem_diff_iff, elem_union_iff; intuition.
Qed.

Lemma diff_union_diff : forall s1 s2 s3, s1 ∖ (s2 ∪ s3) == (s1 ∖ s2) ∖ s3.
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite 3?elem_diff_iff, elem_union_iff; intuition.
Qed.

Lemma diff_diff : forall s1 s2 s3, s1 ∖ (s2 ∖ s3) == (s1 ∖ s2) ∪ (s1 ∩ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite elem_union_iff, 3?elem_diff_iff, elem_inter_iff. 
  split; [| intuition ]; intro; destruct H.
  apply (Decidable.not_and _ _ (dec2decidable _ elem_dec _ _)) in H0; destruct H0.
  left; intuition.
  right; apply (Decidable.not_not _ (dec2decidable _ elem_dec _ _)) in H0; intuition.
Qed.

Lemma diff_exchange : forall s1 s2 s3, (s1 ∖ s2) ∖ s3 == (s1 ∖ s3) ∖ s2.
Proof.
  intros s1 s2 s3.
  rewrite <- 2?diff_union_diff.
  rewrite union_comm.
  reflexivity.
Qed.

Lemma diff_inter_l : forall s1 s2 s3, (s1 ∩ s2) ∖ s3 ==  (s1 ∖ s3) ∩ (s2 ∖ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite elem_inter_iff, 3?elem_diff_iff, elem_inter_iff; intuition. 
Qed.

Lemma diff_inter_r : forall s1 s2 s3, s1 ∖ (s2 ∩ s3) == (s1 ∖ s2) ∪ (s1 ∖ s3).
Proof.
  intros s1 s2 s3.
  apply fset_exten; intro x; rewrite elem_union_iff, 3?elem_diff_iff, elem_inter_iff. 
  split; intros; [| intuition]; destruct H.
  apply (Decidable.not_and _ _ (dec2decidable _ elem_dec _ _)) in H0; destruct H0.
  left; intuition.
  right; intuition. 
Qed.

Global Instance diff_anti_mono : Proper (incl_set ==> incl_set --> incl_set) diff_set.
Proof.
  unfold Proper, "==>", Basics.flip.
  intros s1 s1' H s2 s2' H0.
  unfold incl_set; intro x; rewrite 2?elem_diff_iff; intuition.
Defined.

Lemma diff_exp_l : forall s1 s2, s1 ∖ s2 ⊆ s1.
Proof.
  intros s1 s2.
  unfold incl_set; intro x; rewrite elem_diff_iff; intuition.
Qed.

Lemma diff_empty : forall s1 s2, s1 ∖ s2 == Ø <-> s1 ⊆ s2.
Proof.
  intros s1 s2; unfold incl_set; rewrite fset_exten; split; intros H x.
  intro H0; specialize H with x; rewrite elem_diff_iff in H; destruct H.
  case (elem_dec x s2); intro.
  assumption.
  assert (H2 := H (conj H0 n)); contradiction.
  split; intro.
  rewrite elem_diff_iff in H0; destruct H0; apply H in H0; contradiction.
  contradiction.
Qed.

Lemma union_fromList : forall l1 l2, fromList l1 ∪ fromList l2 == fromList (l1 ++ l2).
Proof.
  intros.
  apply fset_exten; intros.
  rewrite elem_union_iff, <- 3?fromList_in.
  symmetry; apply in_app_iff.
Qed.

End Sets3.
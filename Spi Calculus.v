(*********************************************************************************************************************************************************************)
(*
  Spi Calculus Implementation in Coq
  MSc. Thesis
  Adam Tonet, Brock University Computer Science
*)

(* TABLE OF CONTENTS
Sections can be found with Ctrl+F using the shortened identifier in parentheses.

1 IMPORTS           (IMPR1)
2 BASIC DEFINITIONS (BSC2)
3 SYNTAX            (SYN3)
  3.1 TERMS           (TERM3.1)
  3.2 PROCESSES       (PROC3.2)
  3.3 AGENTS          (AGENT3.3)
4 LEMMAS            (LEM4)
5 RULES             (RULE5)
6 EQUIVALENCES      (EQUIV6)
7 MORPHISMS         (MORPH7)
8 PROOFS            (PROOF8)
9 PROPOSITIONS      (PROP9)

*)

(*IMPR1**********************************************************************IMPORTS**********************************************************************************)

(* Coq library packages. *)
Require Import List. (* For nice lists. *)
  Import ListNotations. (* Same as above. *)
Require Import String. (* For use as the inner data of a name or variable. *)
Require Import Relations. (* For the relation definition and related definitions. *)
Require Import Setoid. (* For parametric relations and morphisms. *)
Require Import SetoidClass. (* To declare Setoid equivalence classes. *)
Require Import Sorting. (* For the Permutations module. *)
  Import Permutation. (* See previous. *)

(* Non-library packages. *)
Require Import Sets. (* Definitions for the creation and use of sets. *)
Require Import NewVar. (* Definitions for creating unique identifiers based on a context. *)

(*BSC2*******************************************************************BASIC DEFINITIONS****************************************************************************)
(* Work begins here; basic definitions and functions dealing with names and variables. *)

Instance set_dec : Eq_Dec string := {|
  eq_dec := string_dec
|}.

Definition Name := string.

Inductive Action : Type :=
  | ActName : Name -> Action
  | τ       : Action.

Definition Var := string.

(* Returns the converse of relation R. *)
Definition Converse {A: Type} (R: relation A) : relation A := fun (x y: A) => R y x.

(* Definition of the reflexive transitive closure from the Coq library adjusted with implicit type parameter and Setoid consideration. *)
Inductive rtc {A: Type} {S: Setoid A} (R: relation A) : A -> A -> Prop :=
  | rtc_refl : forall x y z, y == x -> z == x -> rtc R y z
  | rtc_trans : forall x y z v w, v == x -> w == z -> R x y -> rtc R y z -> rtc R v w.

(* Definitions relating to equality of terms, processes and agents. *)

Definition swap {A B : Type} (p : A * B) : B * A := (snd p, fst p).

Fixpoint zipper {A B C : Type} (l1 : list (A * B)) (l2 : list (B * C)) : list (A * C) :=
  match l1,l2 with
    | ((a,_)::l1'),((_,c)::l2') => (a,c)::zipper l1' l2'
    | _,_ => []
  end.

Inductive ProperZipperPair {A B C : Type} {D : Eq_Dec B} : list (A * B) -> list (B * C) -> Prop :=
  | EmptyPZP : ProperZipperPair [] []
  | ConsPZP    : forall a b c l1' l2', ProperZipperPair l1' l2' -> ProperZipperPair ((a,b)::l1') ((b,c)::l2').

Lemma zipper1 {A B C : Type} {D : Eq_Dec B} : forall (l1 : list (A * B)) (l2 : list (B * C)), ProperZipperPair l1 l2 -> zipper l1 l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros.
  case_eq l1; case_eq l2; intros.
  split; trivial.
  rewrite H1, H2 in H; inversion H.
  rewrite H1, H2 in H; inversion H.
  rewrite H1, H2 in H0. 
 destruct p, p0; simpl in H0; inversion H0.
Qed.

Lemma zipper2 {A B C : Type} {D : Eq_Dec B} : forall (l1 : list (A * B)) (l2 : list (B * C)) s1 s3 l, ProperZipperPair l1 l2 -> zipper l1 l2 = (s1,s3)::l -> exists s2 l1' l2', l1 = (s1,s2)::l1'  /\ l2 = (s2,s3)::l2' /\ l = zipper l1' l2'.
Proof.
  intros.
  case_eq l1; case_eq l2; intros.
  rewrite H1, H2 in H0; inversion H0.
  rewrite H1, H2 in H0; inversion H0.
  rewrite H1, H2 in H0; destruct p; simpl in H0; inversion H0.

  destruct p as [s4 s5], p0 as [s6 s7].
  rewrite H2, H1 in H, H0.
  inversion H0.
  inversion H.
  exists s7, l3, l0.
  rewrite H10; intuition.
Qed.

Notation "s1 =s s2" := (if string_dec s1 s2 then true else false) (at level 50).

Lemma bool2Prop_s : forall s1 s2, s1 =s s2 = true <-> s1 = s2.
Proof.
  split; intros; destruct (string_dec s1 s2); subst.
  trivial.
  inversion H.
  trivial.
  contradiction.
Qed.

Lemma bool2Prop_s_neq : forall s1 s2, s1 =s s2 = false <-> s1 <> s2.
Proof.
  intros; split; intros.
  case_eq (string_dec s1 s2); intros.
  rewrite H0 in H; inversion H.
  trivial.
  case_eq (string_dec s1 s2); intros.
  contradiction.
  trivial.
Qed.

(* Checks whether two identifiers are equal based on a context of equal bound identifiers. *)
Fixpoint checkVars (s1 s2 : string) (l : list (string * string)) : bool := 
  match l with 
    | [] => s1 =s s2
    | (s3,s4)::l' => match s1 =s s3, s2 =s s4 with
                       | true, true => true 
                       | false, false => checkVars s1 s2 l'
                       | _,_ => false
                     end
  end.

(* Lemmas regarding checkVars. *)

Lemma checkVars1 : forall s l, (forall s1 s2, In (s1,s2) l -> s1 = s2) -> checkVars s s l = true.
Proof.
  induction l; intro H.
  simpl; case (string_dec s s); intros; [trivial | contradiction ].
  destruct a; simpl; case (string_dec s s0); case (string_dec s s1); intros. 
  trivial.
  rewrite e in n. 
  assert (H0 := H s0 s1 (in_eq (s0,s1) l)).
  contradiction.
  rewrite e in n. 
  assert (H0 := H s0 s1 (in_eq (s0,s1) l)).
  symmetry in H0.
  contradiction.
  apply IHl.
  intros.
  apply H.
  apply in_cons; assumption.
Qed.

Lemma checkVars2 : forall s1 s2 l, checkVars s1 s2 l = checkVars s2 s1 (map swap l).
Proof.
  induction l.
  simpl; case (string_dec s1 s2), (string_dec s2 s1); intros.
  trivial.
  rewrite e in n; contradiction.
  rewrite e in n; contradiction.
  trivial.
  destruct a as [s3 s4]; simpl.
  case (string_dec s1 s3), (string_dec s2 s4); intros; trivial.
Qed.

Lemma checkVars3 : forall s1 s2 s3 l1 l2,  ProperZipperPair l1 l2 -> checkVars s1 s2 l1 = true -> checkVars s2 s3 l2 = true -> checkVars s1 s3 (zipper l1 l2) = true.
Proof.
  cut (forall l s1 s2 s3 l1 l2,  l = zipper l1 l2 -> ProperZipperPair l1 l2 -> checkVars s1 s2 l1 = true -> checkVars s2 s3 l2 = true -> checkVars s1 s3 l = true); [ intros;  apply (H (zipper l1 l2) s1 s2 s3 l1 l2); trivial |].
  induction l; intros.
  symmetry in H.
  apply (zipper1 _ _ H0) in H; destruct H.
  rewrite H in H1; rewrite H3 in H2; apply bool2Prop_s; apply bool2Prop_s in H1; apply bool2Prop_s in H2.
  rewrite H1; assumption.
  destruct a as [s4 s5].
  symmetry in H.
  apply (zipper2 _ _ _ _ _ H0) in H.
  destruct H as [s6 H], H as [l1' H], H as [l2' H], H as [H3 H], H as [H H4].
  rewrite H3 in H1; rewrite H in H2.
  simpl in *.
  case_eq (s1 =s s4); intros; rewrite H5 in H1.
  case_eq (s2 =s s6); intros.
  rewrite H6 in H2; assumption.
  rewrite H6 in H1; inversion H1.
  case_eq (s2 =s s6); intros.
  rewrite H6 in H1; inversion H1.
  rewrite H6 in H2.
  case_eq (s3 =s s5); intros.
  rewrite H7 in H2; inversion H2.
  rewrite H6 in H1; rewrite H7 in H2.
  rewrite H3, H in H0; simpl in H0; inversion H0.
  apply (IHl s1 s2 s3 l1' l2' H4 H9 H1 H2).
Defined.

Lemma checkVars4 : forall s1 s2 l, checkVars s1 s2 l = true -> In (s1,s2) l \/ ~In s1 (map fst l) /\ ~In s2 (map snd l) /\ s1 = s2.
Proof.
  intros.
  induction l; simpl in *.
  right; split; [ intuition |]; split; [ intuition |].
  apply bool2Prop_s; assumption.

  destruct a.
  case_eq (s1 =s s); intros; rewrite H0 in H; case_eq (s2 =s s0); intros; rewrite H1 in H; try inversion H.
  rewrite bool2Prop_s in H0; rewrite bool2Prop_s in H1; left; left; rewrite H0, H1; trivial.
  apply bool2Prop_s_neq in H0; apply bool2Prop_s_neq in H1.
  apply IHl in H3; destruct H3.
  left; right; assumption.
  destruct H2; destruct H3.
  simpl; right; split; [| split ]; [ intro | intro | assumption ]; destruct H5.
  symmetry in H5; contradiction.
  contradiction.
  symmetry in H5; contradiction.
  contradiction.
Qed.

Lemma checkVars5 : forall s s1 s2 l, checkVars s1 s2 l = true -> checkVars s1 s2 (l++[(s,s)]) = true.
Proof.
  intros.
  induction l; simpl in *.

  apply bool2Prop_s in H.
  case_eq (s1 =s s); intros; case_eq (s2 =s s); intros.
  trivial.
  apply bool2Prop_s in H0.
  apply bool2Prop_s_neq in H1.
  rewrite H0 in H; symmetry in H; contradiction.
  apply bool2Prop_s_neq in H0.
  apply bool2Prop_s in H1.
  rewrite H1 in H; contradiction.
  apply bool2Prop_s; assumption.

  destruct a.
  case_eq (s1 =s s0); intros; case_eq (s2 =s s3); intros; rewrite H0, H1 in H; inversion H.
  trivial.
  rewrite H.
  apply (IHl H).
Qed.

(* Definitions used for addressing agent side conditions. *)

(* Replaces all instances of the left element of a pair with the right element in a list. *)
Fixpoint singleReplace (l: list string) (r: string * string) : list string := let '(n,n') := r in
  match l with
    | []    => []
    | x::xs => if string_dec x n then n'::(singleReplace xs r) else x::(singleReplace xs r)
  end.

(* Within a list of strings, replaces all instances of a given right element with the left element of a list of pairs. *)
Fixpoint replace (l: list string) (q: list (string * string)) : list string :=
  match q with
    | []    => l
    | x::xs => replace (singleReplace l x) xs
  end.

(* Produces a renaming-ready list of identifier pairs with the left element being the new and the right being the old. *)
(* Takes in a list of elements that need new identifiers and a context of existing identifiers. *)
Fixpoint newVars (l l': list string) : list (string * string) :=
  match l with
    | []    => []
    | n::ns => (n, newVar n l')::(newVars ns (l' ++ [newVar n l']))
  end.

(*SYN3***********************************************************************SYNTAX***********************************************************************************)
(* Spi calculus syntax definitions. *)

(* TERMS3.1 Term definitions. *)

(* Inductive structure for a spi calculus term. *)
Inductive Term : Type :=
  | TName      : Name -> Term
  | Pair       : Term -> Term -> Term
  | Zero       : Term
  | Suc        : Term -> Term
  | TVar       : Var -> Term
  | Encryption : Term -> Term -> Term. (* Encrypt first Term using second Term. *) (* Shared-key encryption *)

(* Returns a set of the free names within T. *)
Fixpoint fnt (T: Term) : FSet Name :=
  match T with
    | TName n        => ❴n❵
    | Pair M N       => fnt M ∪ fnt N
    | Zero           => Ø
    | Suc M          => fnt M
    | TVar _         => Ø
    | Encryption M N => fnt M ∪ fnt N
  end.

(* Returns a set of the free variables within T. *)
Fixpoint fvt (T: Term) : FSet Var :=
  match T with
    | TName _        => Ø
    | Pair M N       => fvt M ∪ fvt N
    | Zero           => Ø
    | Suc M          => fvt M
    | TVar x         => ❴x❵
    | Encryption M N => fvt M ∪ fvt N
  end.

(* Equality of terms based on lists of pairs (names and variables) indicating which identifiers should be equal. *)
(* Note: Only used in the context of eqP; terms are otherwise not considered equal up to bound identifiers. *)
Fixpoint eqT_aux (t1 t2: Term) (ln: list (Name * Name)) (lv : list (Var * Var)) : bool :=
  match t1, t2 with
    | TName n, TName m                 => checkVars n m ln
    | Pair M N, Pair M' N'             => eqT_aux M M' ln lv && eqT_aux N N' ln lv
    | Zero, Zero                       => true
    | Suc M, Suc N                     => eqT_aux M N ln lv
    | TVar x, TVar y                   => checkVars x y lv
    | Encryption M N, Encryption M' N' => eqT_aux M M' ln lv && eqT_aux N N' ln lv
    | _, _                             => false
  end.

(* Reflexivity of term equality. *)
Lemma eqT_aux_refl : forall t ln lv, (forall s1 s2 : string, In (s1, s2) ln -> s1 = s2) -> (forall s1 s2 : string, In (s1, s2) lv -> s1 = s2) -> eqT_aux t t ln lv = true.
Proof.
  induction t; intros.
  apply (checkVars1 _ _ H).
  simpl; rewrite IHt1, IHt2; trivial.
  simpl; trivial.
  simpl; rewrite IHt; trivial.
  apply (checkVars1 _ _ H0).
  simpl; rewrite IHt1, IHt2; trivial.
Defined.

(* Symmetry of term equality. *)
Lemma eqT_aux_sym : forall t1 t2 ln lv, eqT_aux t1 t2 ln lv = eqT_aux t2 t1 (map swap ln) (map swap lv).
Proof.
  induction t1; intros; case t2; intros; try trivial.
  apply checkVars2.
  simpl; rewrite IHt1_1, IHt1_2; trivial.
  apply IHt1.
  apply checkVars2.
  simpl; rewrite IHt1_1, IHt1_2; trivial.
Defined.

(* Transitivity of term equality. *)
Lemma eqT_aux_trans : forall t1 t2 t3 ln1 ln2 lv1 lv2, ProperZipperPair ln1 ln2 -> ProperZipperPair lv1 lv2 -> eqT_aux t1 t2 ln1 lv1 = true -> eqT_aux t2 t3 ln2 lv2 = true -> eqT_aux t1 t3 (zipper ln1 ln2) (zipper lv1 lv2) = true.
Proof.
  induction t1; intros; case_eq t2; intros; rewrite H3 in H2, H1; try (inversion H1); case_eq t3; intros; rewrite H4 in H2; try (inversion H2).
  simpl in *; rewrite H1; unfold Name; rewrite (checkVars3 _ _ _ _ _ H H1 H2); trivial.
  rewrite Bool.andb_true_iff in H5; destruct H5.
  rewrite Bool.andb_true_iff in H7; destruct H7.
  assert (H9 := IHt1_1 t t1 ln1 ln2 lv1 lv2 H H0 H5 H7); simpl in H9.
  assert (H10 := IHt1_2 t0 t4 ln1 ln2 lv1 lv2 H H0 H6 H8); simpl in H10.
  simpl; rewrite H9, H10, H5, H6; trivial.
  simpl; trivial.
  assert (H8 := IHt1 t t0 ln1 ln2 lv1 lv2 H H0 H5 H7); simpl in H8.
  simpl; rewrite H8, H5; trivial.
  simpl in *; rewrite H1; unfold Var; rewrite (checkVars3 _ _ _ _ _ H0 H1 H2); trivial.
  rewrite Bool.andb_true_iff in H5; destruct H5.
  rewrite Bool.andb_true_iff in H7; destruct H7.
  assert (H9 := IHt1_1 t t1 ln1 ln2 lv1 lv2 H H0 H5); simpl in H9.
  assert (H10 := IHt1_2 t0 t4 ln1 ln2 lv1 lv2 H H0 H6); simpl in H10.
  simpl; rewrite H9, H10, H5, H6; trivial.
Defined.

(* Allows the adding of a reflexive pair to a bound name equality context. *)
Lemma eqT_aux_add_n : forall t1 t2 s ln lv, eqT_aux t1 t2 ln lv = true -> eqT_aux t1 t2 (ln ++ [(s,s)]) lv = true.
Proof.
  induction t1; intros; trivial; case_eq t2; intros; rewrite H0 in H; inversion H; rewrite H2.
  apply (checkVars5 s _ _ _ H2).
  simpl; apply Bool.andb_true_iff in H2; destruct H2.
  apply Bool.andb_true_iff; split.
  apply (IHt1_1 _ _ _ _ H1).
  apply (IHt1_2 _ _ _ _ H2).
  simpl; apply (IHt1 _ _ _ _ H2).
  simpl; apply Bool.andb_true_iff in H2; destruct H2.
  apply Bool.andb_true_iff; split.
  apply (IHt1_1 _ _ _ _ H1).
  apply (IHt1_2 _ _ _ _ H2).
Qed.

(* Allows the adding of a reflexive pair to a bound variable equality context. *)
Lemma eqT_aux_add_v : forall t1 t2 s ln lv, eqT_aux t1 t2 ln lv = true -> eqT_aux t1 t2 ln (lv ++ [(s,s)]) = true.
Proof.
  induction t1; intros; trivial; case_eq t2; intros; rewrite H0 in H; inversion H; rewrite H2.
  simpl; apply Bool.andb_true_iff in H2; destruct H2.
  apply Bool.andb_true_iff; split.
  apply (IHt1_1 _ _ _ _ H1).
  apply (IHt1_2 _ _ _ _ H2).
  simpl; apply (IHt1 _ _ _ _ H2).
  apply (checkVars5 s _ _ _ H2).
  simpl; apply Bool.andb_true_iff in H2; destruct H2.
  apply Bool.andb_true_iff; split.
  apply (IHt1_1 _ _ _ _ H1).
  apply (IHt1_2 _ _ _ _ H2).
Qed.

(* Definitions regarding term substitution. *)

(* Does a lookup based on a list of pairs, returning the right element if the left is found and a default element otherwise. *)
Fixpoint lookupDefault {A B : Type} {D : Eq_Dec A} (x : A) (l : list (A * B)) (d : B) : B :=
  match l with
     | [] => d
     | ((y,b)::l') => if eq_dec x y then b else lookupDefault x l' d
  end.

Definition allFNT (l : list (string * Term)) : FSet string := fold_right (fun p s => fnt (snd p) ∪ s) Ø l.
Definition allFVT (l : list (string * Term)) : FSet string := fold_right (fun p s => fvt (snd p) ∪ s) Ø l.
Definition allVars {A: Type} (l : list (string * A)) : FSet string := fold_right (fun p s => ❴fst p❵ ∪ s) Ø l.

(* Sublemmas for fnt_TSub_aux and fvt_TSub_aux. *)

Lemma allFNTProp : forall s1 s2 l, s2 ∉ allFNT l -> allFNT ((s1,TName s2)::l) ∖ ❴s2❵ == allFNT l.
Proof.
  intros.
  apply fset_exten; intros.
  rewrite elem_diff_iff; simpl; rewrite elem_union_iff.
  split; intros.
  do 2 destruct H0; [ contradiction | assumption ].
  split.
  right; assumption.
  destruct (dec2decidable _ elem_dec x ❴s2❵).
  rewrite elem_singleton in H1; rewrite H1 in H0; contradiction.
  assumption.
Qed.

Lemma allFVTProp : forall s1 s2 l, s2 ∉ allFVT l -> allFVT ((s1,TVar s2)::l) ∖ ❴s2❵ == allFVT l.
Proof.
  intros.
  apply fset_exten; intros.
  rewrite elem_diff_iff; simpl; rewrite elem_union_iff.
  split; intros.
  do 2 destruct H0; [ contradiction | assumption ].
  split.
  right; assumption.
  destruct (dec2decidable _ elem_dec x ❴s2❵).
  rewrite elem_singleton in H1; rewrite H1 in H0; contradiction.
  assumption.
Qed.

Lemma lookupDefaultProp1 : forall {A: Type} s (l: list (string * A)) d, s ∉ allVars l -> lookupDefault s l d = d.
Proof.
  induction l; intros.
  reflexivity.
  destruct a as [s1 t1]. 
  replace (lookupDefault s ((s1, t1) :: l) d) with (if string_dec s s1 then t1 else lookupDefault s l d) by trivial.
  simpl in H.
  rewrite elem_union_iff in H.
  apply Decidable.not_or in H; destruct H.
  case_eq (string_dec s s1); intros.
  rewrite elem_singleton in H; contradiction.
  apply (IHl _ H0).
Qed.

Lemma lookupDefaultProp2 : forall s (l: list (string * Term)) d, s ∈ allVars l -> fvt (lookupDefault s l d) ⊆ (allFVT l).
Proof.
  induction l; intros.
  simpl in H; apply elem_empty in H; contradiction.
  destruct a as [s1 t1]. 
  replace (lookupDefault s ((s1, t1) :: l) d) with (if string_dec s s1 then t1 else lookupDefault s l d) by trivial.
  case_eq (string_dec s s1); intros.
  apply union_exp_l.
  simpl; rewrite <- union_exp_r.
  simpl in H; rewrite elem_union_iff in H; destruct H.
  apply elem_singleton in H; contradiction.
  apply (IHl _ H).
Qed.

(* Substitution of a 'queue' of var/Term pairs within a Term. *)
Fixpoint TSub_aux (t : Term) (l : list (string * Term)) : Term := 
  match t with 
    | TName n        => TName n
    | Pair M N       => Pair (TSub_aux M l) (TSub_aux N l)
    | Zero           => Zero
    | Suc M          => Suc (TSub_aux M l)
    | TVar y         => lookupDefault y l t
    | Encryption M N => Encryption (TSub_aux M l) (TSub_aux N l)
  end.

(* Sublemma for fnt_TSub_aux. *)
Lemma fnt_lookup_var : forall x v l, x ∈ fnt (lookupDefault v l (TVar v)) -> x ∈ allFNT l.
Proof.
  induction l; intros; simpl in *.
  assumption.
  rewrite elem_union_iff.
  destruct a.
  destruct (string_dec v v0); simpl in *.
  left; assumption.
  apply IHl in H; right; assumption.
Qed.

(* The free names of a term substitution will be a subset of all the names present in the term and terms to substitute beforehand. *)
(* General list version. *)
Lemma fnt_TSub_aux : forall t l, fnt (TSub_aux t l) ⊆ (fnt t ∪ allFNT l).
Proof.
  induction t; intros l.
  simpl; unfold incl_set; intros; rewrite elem_union_iff; left; assumption.
  replace (fnt (TSub_aux (Pair t1 t2) l)) with (fnt (TSub_aux t1 l) ∪ fnt (TSub_aux t2 l)) by trivial.
  replace (fnt (Pair t1 t2)) with (fnt t1 ∪ fnt t2) by trivial.
  rewrite IHt1, IHt2.
  rewrite union_assoc, (union_comm (allFNT l)), (union_assoc (fnt t2) (allFNT l) (allFNT l)), union_idemp, <- union_assoc; reflexivity.
  simpl; unfold incl_set; intros; contradiction.
  replace (fnt (TSub_aux (Suc t) l)) with (fnt (TSub_aux t l)) by trivial.
  replace (fnt (Suc t)) with (fnt t) by trivial.
  rewrite IHt.
  reflexivity.
  simpl; unfold incl_set; intros; apply fnt_lookup_var in H; rewrite elem_union_iff; right; assumption.
  replace (fnt (TSub_aux (Encryption t1 t2) l)) with (fnt (TSub_aux t1 l) ∪ fnt (TSub_aux t2 l)) by trivial.
  replace (fnt (Encryption t1 t2)) with (fnt t1 ∪ fnt t2) by trivial.
  rewrite IHt1, IHt2.
  rewrite union_assoc, (union_comm (allFNT l)), (union_assoc (fnt t2) (allFNT l) (allFNT l)), union_idemp, <- union_assoc; reflexivity.
Qed.

(* The free variables of a term substitution will be a subset of all the variables present in the term without the targets, and the terms to substitute beforehand. *)
(* General list version. *)
Lemma fvt_TSub_aux : forall t l, fvt (TSub_aux t l) ⊆ (fvt t ∖ allVars l) ∪ allFVT l.
Proof.
  induction t; intros l.
  simpl; unfold incl_set; intros; contradiction.
  replace (fvt (TSub_aux (Pair t1 t2) l)) with (fvt (TSub_aux t1 l) ∪ fvt (TSub_aux t2 l)) by trivial.
  replace (fvt (Pair t1 t2)) with (fvt t1 ∪ fvt t2) by trivial.
  rewrite IHt1, IHt2.
  rewrite union_assoc, (union_comm (allFVT l)), union_assoc, union_idemp, <- union_assoc, diff_union_l; reflexivity.
  simpl; unfold incl_set; intros; contradiction.
  replace (fvt (TSub_aux (Suc t) l)) with (fvt (TSub_aux t l)) by trivial.
  replace (fvt (Suc t)) with (fvt t) by trivial.
  rewrite IHt.
  reflexivity.
  simpl; case_eq (elem v (allVars l)); intros.
  apply elem_Prop in H.
  rewrite <- union_exp_r.
  apply (lookupDefaultProp2 _ _ _ H).
  apply not_elem_Prop in H.
  rewrite (lookupDefaultProp1 _ _ _ H); simpl.
  rewrite <- union_exp_l.
  intros x H0.
  rewrite elem_diff_iff; split; [ assumption |].
  rewrite elem_singleton in H0; rewrite H0; assumption.
  replace (fvt (TSub_aux (Encryption t1 t2) l)) with (fvt (TSub_aux t1 l) ∪ fvt (TSub_aux t2 l)) by trivial.
  replace (fvt (Encryption t1 t2)) with (fvt t1 ∪ fvt t2) by trivial.
  rewrite IHt1, IHt2.
  rewrite union_assoc, (union_comm (allFVT l)), union_assoc, union_idemp, <- union_assoc, diff_union_l; reflexivity.
Qed.

(* Single term substitution. *)
Definition TSub (t1 t2 : Term) (x : string) : Term := TSub_aux t1 [(x,t2)].

(* The free names of a term substitution will be a subset of all the names present in the term and terms to substitute beforehand. *)
Lemma fnt_TSub : forall t1 t2 x, fnt (TSub t1 t2 x) ⊆ (fnt t1 ∪ fnt t2).
Proof.
  intros.
  apply fnt_TSub_aux.
Qed.

(* The free variables of a term substitution will be a subset of all the variables present in the term without the targets, and the terms to substitute beforehand. *)
Lemma fvt_TSub : forall t1 t2 x, fvt (TSub t1 t2 x) ⊆ (fvt t1 ∖ ❴x❵) ∪ fvt t2.
Proof.
  intros.
  apply fvt_TSub_aux.
Qed.

(* Definition of a closed term. *)
Definition ClosedTerm : Type := { T: Term | fvt T == Ø}.
Definition getTerm (T: ClosedTerm) : Term := proj1_sig T.

(* General alias of the right projection of a sigma type. *)
Definition getProof {A: Type} {P: A -> Prop} := @proj2_sig A P.

(* Equivalence relation on closed terms that ignores the accompanying proof. *)
Instance ClosedTermSetoid : Setoid ClosedTerm := {|
  equiv := fun M N => getTerm M = getTerm N |}.
Proof.
  split.
  unfold Reflexive.
  intros M.
  destruct M.
  simpl.
  reflexivity.
  unfold Symmetric.
  intros M N.
  destruct M; destruct N.
  simpl; intros.
  symmetry; assumption.
  unfold Transitive.
  intros M N T.
  destruct M; destruct N; destruct T.
  simpl; intros.
  transitivity x0; assumption.
Defined.

Lemma PairClosed (M N: Term) (prf1: fvt M == Ø) (prf2: fvt N == Ø) : fvt (Pair M N) == Ø.
Proof.
  simpl fvt; rewrite prf1, prf2, union_idemp; reflexivity.
Qed.

(* Proofs that each of the term constructors preserve closedness. Also function as closed versions of term constructors. *)
Definition CTName (n: Name) : ClosedTerm.
Proof.
  apply (exist _ (TName n)).
  simpl; trivial.
Defined.

Definition CPair (T1 T2: ClosedTerm) : ClosedTerm.
Proof.
  apply (exist _ (Pair (getTerm T1) (getTerm T2))).
  destruct T1 as (T1 & prf1), T2 as (T2 & prf2); simpl fvt.
  rewrite prf1, prf2, union_idemp; reflexivity.
Defined.

Definition CZero : ClosedTerm.
Proof.
  apply (exist _ Zero).
  simpl; trivial.
Defined.

Definition CSuc (T: ClosedTerm) : ClosedTerm.
Proof.
  apply (exist _ (Suc (getTerm T))).
  destruct T as (T & prf); simpl fvt; trivial.
Defined.

Definition CEncryption (T1 T2: ClosedTerm) : ClosedTerm.
Proof.
  apply (exist _ (Encryption (getTerm T1) (getTerm T2))).
  destruct T1 as (T1 & prf1), T2 as (T2 & prf2); simpl fvt.
  rewrite prf1, prf2, union_idemp; reflexivity.
Defined.

(* Closed term notations, and TVar notation (cannot be closed). *)
Notation "'❴' n '❵N'" := (CTName n).
Notation "'❴' v '❵V'" := (TVar v).
Notation "'❨' x ',' y '❩'" := (CPair x y).
Notation "'Encrypt' M 'using' N" := (CEncryption M N) (at level 0).

Lemma bool2Prop_t : forall M N, eqT_aux M N [] [] = true <-> M = N.
Proof.
  intros M; induction M; split; intros; destruct N; simpl in H; try inversion H; subst.
  rewrite bool2Prop_s in H; subst; trivial.
  apply eqT_aux_refl; intros; contradiction.
  apply andb_prop in H; destruct H.
  apply IHM1 in H; apply IHM2 in H0; subst; trivial.
  apply eqT_aux_refl; intros; contradiction.
  trivial.
  apply eqT_aux_refl; intros; contradiction.
  apply IHM in H; subst; trivial.
  apply eqT_aux_refl; intros; contradiction.
  rewrite bool2Prop_s in H; subst; trivial.
  apply eqT_aux_refl; intros; contradiction.
  apply andb_prop in H; destruct H.
  apply IHM1 in H; apply IHM2 in H0; subst; trivial.
  apply eqT_aux_refl; intros; contradiction.
Qed.

(* PROC3.2 Process definitions. *)

(* Inductive structure for a spi calculus process. *)
Inductive Process : Type :=
  | Output      : Term -> Term -> Process -> Process
  | Input       : Term -> Var -> Process -> Process 
  | Composition : Process -> Process -> Process
  | Restriction : Name -> Process -> Process
  | Replication : Process -> Process
  | Match       : Term -> Term -> Process -> Process
  | Nil         : Process
  | Split       : Term (* Pair (N,L), actual data *) -> Var -> Var (* x and y, variables to replace *)-> Process (* in P *) -> Process (* let (x, y) = M in P behaves as P[N/x][L/y] if term M is the pair (N, L). Do I need a pair construct? Kind of a chicken and egg thing here if I want to use PairSplit as a constructor and have SpiPair be involved. *)
  | Case        : Term (* M, value to check *) -> Process (* P *) -> Var (* x *) -> Process (* Q *) -> Process (* should this and decrypt be rolled into one? An integer case process case M of 0: P suc(x) : Q behaves as P if term M is 0, as Q[N/x] if M is suc(N). Otherwise, the process is stuck. *)
  | Decryption  : Term -> Term -> Var -> Process -> Process. (* Decrypt first Term using second Term, if success then run Process with decryption result replacing Var in the process. *)

(* Allows for the restriction of a process using a name 'vector', or list of names. *)
(* Note: Since it is only intended for internal use (ie. within an interaction), this function
   only takes in a list of names (since it should be guaranteed to have no duplicates. *)
Fixpoint MultiRestriction (l: list Name) (P: Process) : Process :=
  match l with
    | []    => P
    | x::xs => Restriction x (MultiRestriction xs P)
  end.

(* Equality of processes based on two lists of pairs (names and variables) indicating which identifiers should be equal. *)
Fixpoint eqP_aux (p1 p2 : Process) (ln: list (Name * Name)) (lv: list (Var * Var)) : bool :=
  match p1, p2 with
    | Output M N P', Output M' N' Q'             => eqT_aux M M' ln lv && eqT_aux N N' ln lv && eqP_aux P' Q' ln lv
    | Input M x P', Input N y Q'                 => eqT_aux M N ln lv && eqP_aux P' Q' ln ((x,y)::lv)
    | Composition P' Q', Composition P'' Q''     => eqP_aux P' P'' ln lv && eqP_aux Q' Q'' ln lv
    | Restriction n P', Restriction m Q'         => eqP_aux P' Q' ((n,m)::ln) lv
    | Replication P', Replication Q'             => eqP_aux P' Q' ln lv
    | Match M N P', Match M' N' Q'               => eqT_aux M M' ln lv && eqT_aux N N' ln lv && eqP_aux P' Q' ln lv
    | Nil, Nil                                   => true
    | Split M x y P', Split N x' y' Q'           => eqT_aux M N ln lv && eqP_aux P' Q' ln ((x,x')::(y,y')::lv)
    | Case M P' x Q', Case N P'' y Q''           => eqT_aux M N ln lv && eqP_aux P' P'' ln lv && eqP_aux Q' Q'' ln ((x,y)::lv)
    | Decryption M N x P', Decryption M' N' y Q' => eqT_aux M M' ln lv && eqT_aux N N' ln lv && eqP_aux P' Q' ln ((x,y)::lv)
    | _, _                                       => false
  end.

(* Process equality is transitive. *)
Lemma eqP_aux_refl : forall p ln lv, (forall s1 s2 : string, In (s1, s2) ln -> s1 = s2) -> (forall s1 s2 : string, In (s1, s2) lv -> s1 = s2) -> eqP_aux p p ln lv = true.
Proof.
  induction p; intros.
  simpl; rewrite 2?eqT_aux_refl, IHp; trivial.
  simpl; rewrite eqT_aux_refl, IHp; trivial.
  intros; apply in_inv in H1; destruct H1; [inversion H1; trivial | apply H0; assumption].
  simpl; rewrite IHp1, IHp2; trivial.
  simpl; rewrite IHp; trivial.
  intros.
  apply in_inv in H1; destruct H1; [inversion H1; trivial | apply H; assumption].
  simpl; rewrite IHp; trivial.
  simpl; rewrite 2?eqT_aux_refl, IHp; trivial.
  trivial.
  simpl; rewrite eqT_aux_refl, 2?IHp; trivial.
  intros; apply in_inv in H1; destruct H1; [inversion H1; trivial | ].
  simpl in H1; destruct H1; [inversion H1; trivial | apply H0; assumption].
  simpl; rewrite eqT_aux_refl, IHp1, IHp2; trivial.
  intros; apply in_inv in H1; destruct H1; [inversion H1; trivial | apply H0; assumption].
  simpl; rewrite 2?eqT_aux_refl, IHp; trivial.
  intros; apply in_inv in H1; destruct H1; [inversion H1; trivial | apply H0; assumption].
Defined.

(* Process equality is symmetric. *)
Lemma eqP_aux_sym : forall p1 p2 ln lv, eqP_aux p1 p2 ln lv = eqP_aux p2 p1 (map swap ln) (map swap lv).
Proof.
  induction p1; intros; case p2; intros; try trivial.
  simpl; rewrite <- 2?eqT_aux_sym, IHp1; trivial.
  simpl; rewrite <- eqT_aux_sym, IHp1; trivial.
  simpl; rewrite IHp1_1, IHp1_2; trivial.
  simpl; rewrite IHp1; trivial.
  simpl; rewrite IHp1; trivial.
  simpl; rewrite <- 2?eqT_aux_sym, IHp1; trivial.
  simpl; rewrite <- eqT_aux_sym, IHp1; trivial.
  simpl; rewrite <- eqT_aux_sym, IHp1_1, IHp1_2; trivial.
  simpl; rewrite <- 2?eqT_aux_sym, IHp1; trivial.
Defined.

(* Process equality is transitive. *)
Lemma eqP_aux_trans : forall p1 p2 p3 ln1 ln2 lv1 lv2, ProperZipperPair ln1 ln2 -> ProperZipperPair lv1 lv2 -> eqP_aux p1 p2 ln1 lv1 = true -> eqP_aux p2 p3 ln2 lv2 = true -> eqP_aux p1 p3 (zipper ln1 ln2) (zipper lv1 lv2) = true.
Proof.
  induction p1; intros; case_eq p2; intros; rewrite H3 in H1, H2; try (inversion H1); case_eq p3; intros; rewrite H4 in H2; try (inversion H2).
  do 2 (rewrite Bool.andb_true_iff in H5; destruct H5).
  do 2 (rewrite Bool.andb_true_iff in H7; destruct H7).
  simpl.  assert (Lem := IHp1 p p0 ln1 ln2 lv1 lv2 H H0 H6 H9); simpl in Lem.
  rewrite (eqT_aux_trans _ t1), (eqT_aux_trans _ t2), Lem, H5, H8, H6; trivial.
  rewrite Bool.andb_true_iff in H5; destruct H5.
  rewrite Bool.andb_true_iff in H7; destruct H7.
  simpl.
  assert (PZP := ConsPZP v v0 v1 _ _ H0).
  assert (Lem := IHp1 p p0 ln1 ln2 ((v, v0) :: lv1) ((v0, v1) :: lv2) H PZP H6 H8); simpl in Lem.
  rewrite (eqT_aux_trans _ t0), H5, H6; trivial.
  rewrite Bool.andb_true_iff in H5; destruct H5.
  rewrite Bool.andb_true_iff in H7; destruct H7.
  simpl.
  assert (Lem1 := IHp1_1 p p1 ln1 ln2 lv1 lv2 H H0 H5 H7); simpl in Lem1.
  assert (Lem2 := IHp1_2 p0 p4 ln1 ln2 lv1 lv2 H H0 H6 H8); simpl in Lem2.
  rewrite H5, H6, Lem1, Lem2; trivial.
  simpl.
  assert (PZP := ConsPZP n n0 n1 _ _ H).
  assert (Lem := IHp1 p p0 ((n, n0) :: ln1) ((n0, n1) :: ln2) lv1 lv2 PZP H0 H5 H7); simpl in Lem.
  rewrite H5; trivial.
  simpl.
  assert (Lem := IHp1 p p0 ln1 ln2 lv1 lv2 H H0 H5 H7); simpl in Lem.
  rewrite H5; trivial.
  do 2 (rewrite Bool.andb_true_iff in H5; destruct H5).
  do 2 (rewrite Bool.andb_true_iff in H7; destruct H7).
  simpl.
  assert (Lem := IHp1 p p0 ln1 ln2 lv1 lv2 H H0 H6 H9); simpl in Lem.
  rewrite (eqT_aux_trans _ t1), (eqT_aux_trans _ t2), Lem, H5, H8, H6; trivial.
  trivial.
  rewrite Bool.andb_true_iff in H5; destruct H5.
  rewrite Bool.andb_true_iff in H7; destruct H7.
  simpl.
  assert (PZP1 := ConsPZP v0 v2 v4 _ _ H0).
  assert (PZP2 := ConsPZP v v1 v3 _ _ PZP1).
  assert (Lem := IHp1 p p0 ln1 ln2 ((v, v1) :: (v0, v2) :: lv1) ((v1, v3) :: (v2, v4) :: lv2) H PZP2 H6 H8); simpl in Lem.
  rewrite (eqT_aux_trans _ t0), H5, H6; trivial.
  do 2 (rewrite Bool.andb_true_iff in H5; destruct H5).
  do 2 (rewrite Bool.andb_true_iff in H7; destruct H7).
  simpl.
  assert (PZP := ConsPZP v v0 v1 _ _ H0).
  assert (Lem1 := IHp1_1 p p1 ln1 ln2 lv1 lv2 H H0 H8 H10); simpl in Lem1.
  assert (Lem2 := IHp1_2 p0 p4 ln1 ln2 ((v, v0) :: lv1) ((v0, v1) :: lv2) H PZP H6 H9); simpl in Lem2.
  rewrite (eqT_aux_trans _ t0), H5, H8, H6, Lem1; trivial.
  do 2 (rewrite Bool.andb_true_iff in H5; destruct H5).
  do 2 (rewrite Bool.andb_true_iff in H7; destruct H7).
  simpl.
  assert (PZP := ConsPZP v v0 v1 _ _ H0).
  assert (Lem := IHp1 p p0 ln1 ln2 ((v, v0) :: lv1) ((v0, v1) :: lv2) H PZP H6 H9); simpl in Lem.
  rewrite (eqT_aux_trans _ t1), (eqT_aux_trans _ t2), H5, H8, H6; trivial.
Defined.

(* We can add a reflexive pair of names to the name context of a process equality without changing the truth of it. *)
Lemma eqP_aux_add_n : forall p1 p2 s ln lv, eqP_aux p1 p2 ln lv = true -> eqP_aux p1 p2 (ln ++ [(s,s)]) lv = true.
Proof.
  induction p1; intros; trivial; case_eq p2; intros; rewrite H0 in H; inversion H.
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite Bool.andb_true_iff in H1; destruct H1.
  rewrite 2?eqT_aux_add_n, IHp1, H1, H2, H3; trivial.
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite eqT_aux_add_n, H1, H2; simpl; trivial.
  apply (IHp1 _ _ _ _ H2).
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite H1, H2, IHp1_1, IHp1_2; trivial.
  rewrite H2; apply (IHp1 _ _ _ _ H2).
  rewrite H2; apply (IHp1 _ _ _ _ H2).
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite Bool.andb_true_iff in H1; destruct H1.
  rewrite 2?eqT_aux_add_n, IHp1, H1, H2, H3; trivial.
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite eqT_aux_add_n, H1, H2; simpl; trivial.
  apply (IHp1 _ _ _ _ H2).
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite Bool.andb_true_iff in H1; destruct H1.
  rewrite eqT_aux_add_n, IHp1_1, H1, H2, H3; simpl; trivial.
  apply (IHp1_2 _ _ _ _ H2).
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite Bool.andb_true_iff in H1; destruct H1.
  rewrite 2?eqT_aux_add_n, H1, H2, H3; trivial.
  apply (IHp1 _ _ _ _ H2).
Qed.

(* We can add a reflexive pair of variables to the variable context of a process equality without changing the truth of it. *)
Lemma eqP_aux_add_v : forall p1 p2 s ln lv, eqP_aux p1 p2 ln lv = true -> eqP_aux p1 p2 ln (lv ++ [(s,s)]) = true.
Proof.
  induction p1; intros; trivial; case_eq p2; intros; rewrite H0 in H; inversion H.
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite Bool.andb_true_iff in H1; destruct H1.
  rewrite 2?eqT_aux_add_v, IHp1, H1, H2, H3; trivial.
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite eqT_aux_add_v, H1, H2; simpl; trivial.
  apply (IHp1 _ _ _ _ H2).
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite H1, H2, IHp1_1, IHp1_2; trivial.
  rewrite H2; apply (IHp1 _ _ _ _ H2).
  rewrite H2; apply (IHp1 _ _ _ _ H2).
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite Bool.andb_true_iff in H1; destruct H1.
  rewrite 2?eqT_aux_add_v, IHp1, H1, H2, H3; trivial.
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite eqT_aux_add_v, H1, H2; simpl; trivial.
  apply (IHp1 _ _ _ _ H2).
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite Bool.andb_true_iff in H1; destruct H1.
  rewrite eqT_aux_add_v, IHp1_1, H1, H2, H3; simpl; trivial.
  apply (IHp1_2 _ _ _ _ H2).
  simpl; rewrite Bool.andb_true_iff in H2; destruct H2.
  rewrite Bool.andb_true_iff in H1; destruct H1.
  rewrite 2?eqT_aux_add_v, H1, H2, H3; trivial.
  apply (IHp1 _ _ _ _ H2).
Qed.

(* Bootstrap version of process equality. *)
Definition eqP (p1 p2 : Process) : bool := eqP_aux p1 p2 [] [].

(* Process equality is an equivalence relation. *)
Instance ProcessSetoid : Setoid Process := {|
  equiv := fun p1 p2 => Bool.Is_true (eqP p1 p2)
|}.
Proof.
  split.
  unfold Reflexive; intro t; unfold Bool.Is_true, eqP; rewrite eqP_aux_refl; [ trivial | intros; contradiction | intros; contradiction].
  unfold Symmetric; unfold Bool.Is_true, eqP; intros p1 p2 H; rewrite eqP_aux_sym; assumption.
  unfold Transitive; unfold Bool.Is_true, eqP; intros p1 p2 p3 H H0.
  case_eq (eqP_aux p1 p2 [] []); case_eq (eqP_aux p2 p3 [] []); intros.
  replace [] with (@zipper Name Name Name [] []) by trivial.
  replace [] with (@zipper Var Var Var [] []) by trivial.
  rewrite (eqP_aux_trans _ _ _ _ _ _ _ EmptyPZP EmptyPZP H2 H1); trivial.
  rewrite H1 in H0; contradiction.
  rewrite H2 in H; contradiction.
  rewrite H1 in H0; contradiction.
Defined.

Infix "=p" := (eqP) (at level 0).

(* Proofs allowing rewriting of equivalent terms and processes within recursive constructors. *)

Instance OutputProper : Proper (eq ==> eq ==> equiv ==> equiv) Output.
Proof.
  unfold Proper, "==>"; intros t1 t1' H t2 t2' H0 p q H1.
  rewrite H, H0.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H1; unfold Bool.Is_true, eqP in H1.
  case_eq (eqP_aux p q [] []); intros; rewrite H2 in H1; [| contradiction ].
  rewrite 2?eqT_aux_refl; try contradiction.
  simpl; trivial.
Defined.

Instance InputProper : Proper (eq ==> eq ==> equiv ==> equiv) Input.
Proof.
  unfold Proper, "==>"; intros t t' H x y H0 p q H1.
  rewrite H, H0.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H1; unfold Bool.Is_true, eqP in H1.
  case_eq (eqP_aux p q [] []); intros; rewrite H2 in H1; [| contradiction ].
  apply (eqP_aux_add_v _ _ (y:Var) _) in H2; simpl in H2.
  rewrite eqT_aux_refl; try contradiction.
  rewrite H2.
  simpl; trivial.
Defined.

Lemma InputProper' : forall (M N: Term) (H: M = N) (x y: Var) (P Q: Process), eqP_aux P Q [] [(x,y)] = true -> Input M x P == Input N y Q.
Proof.
  intros; subst.
  simpl; unfold Bool.Is_true, "=p"; simpl.
  rewrite eqT_aux_refl; intros; try contradiction; simpl.
  rewrite H0; trivial.
Qed.

Instance CompositionProper : Proper (equiv ==> equiv ==> equiv) Composition.
Proof.
  unfold Proper, "==>"; intros p p' H q q' H0.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H; unfold Bool.Is_true, eqP in H.
  case_eq (eqP_aux p p' [] []); intros; rewrite H1 in H; [| contradiction ].
  simpl in H0; unfold Bool.Is_true, eqP in H0.
  case_eq (eqP_aux q q' [] []); intros; rewrite H2 in H0; [| contradiction ].
  simpl; trivial.
Defined.

Instance RestrictionProper : Proper (eq ==> equiv ==> equiv) Restriction.
Proof.
  unfold Proper, "==>"; intros n m H p q H0.
  rewrite H.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H0; unfold Bool.Is_true, eqP in H0.
  case_eq (eqP_aux p q [] []); intros; rewrite H1 in H0; [| contradiction ].
  apply (eqP_aux_add_n _ _ m _) in H1; simpl in H1.
  rewrite H1.
  simpl; trivial.
Defined.

Lemma RestrictionProper' : forall (n m: Name) (P Q: Process), eqP_aux P Q [(n,m)] [] = true -> Restriction n P == Restriction m Q.
Proof.
  intros; subst.
  simpl; unfold Bool.Is_true, "=p"; simpl.
  rewrite H; trivial.
Qed.

Instance ReplicationProper : Proper (equiv ==> equiv) Replication.
Proof.
  unfold Proper, "==>"; intros p q H.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H; unfold Bool.Is_true, eqP in H.
  case_eq (eqP_aux p q [] []); intros; rewrite H0 in H; [| contradiction ].
  simpl; trivial.
Defined.

Instance MatchProper : Proper (eq ==> eq ==> equiv ==> equiv) Match.
Proof.
  unfold Proper, "==>"; intros t1 t1' H t2 t2' H0 p q H1.
  rewrite H, H0.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H1; unfold Bool.Is_true, eqP in H1.
  case_eq (eqP_aux p q [] []); intros; rewrite H2 in H1; [| contradiction ].
  rewrite 2?eqT_aux_refl; try contradiction.
  simpl; trivial.
Defined.

Instance SplitProper : Proper (eq ==> eq ==> eq ==> equiv ==> equiv) Split.
Proof.
  unfold Proper, "==>"; intros t t' H x x' H0 y y' H1 p q H2.
  rewrite H, H0, H1.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H2; unfold Bool.Is_true, eqP in H2.
  case_eq (eqP_aux p q [] []); intros; rewrite H3 in H2; [| contradiction ].
  apply (eqP_aux_add_v _ _ x' _) in H3; simpl in H3.
  apply (eqP_aux_add_v _ _ y' _) in H3; simpl in H3.
  rewrite eqT_aux_refl; try contradiction.
  rewrite H3.
  simpl; trivial.
Defined.

Lemma SplitProper' : forall (M N: Term) (H: M = N) (x x' y y': Var) (P Q: Process), eqP_aux P Q [] [(x,x');(y,y')] = true -> Split M x y P == Split N x' y' Q.
Proof.
  intros; subst.
  simpl in *; unfold Bool.Is_true, "=p" in *; simpl in *.
  rewrite eqT_aux_refl; intros; try contradiction; simpl.
  rewrite H0; trivial.
Qed.

Instance CaseProper : Proper (eq ==> equiv ==> eq ==> equiv ==> equiv) Case.
Proof.
  unfold Proper, "==>"; intros t t' H p p' H0 x y H1 q q' H2.
  rewrite H, H1.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H0; unfold Bool.Is_true, eqP in H0.
  case_eq (eqP_aux p p' [] []); intros; rewrite H3 in H0; [| contradiction ].
  simpl in H2; unfold Bool.Is_true, eqP in H2.
  case_eq (eqP_aux q q' [] []); intros; rewrite H4 in H2; [| contradiction ].
  apply (eqP_aux_add_v _ _ y _) in H4; simpl in H4.
  rewrite eqT_aux_refl; try contradiction.
  rewrite H4.
  simpl; trivial.
Defined.

Lemma CaseProper' : forall (M N: Term) (H: M = N) (x y: Var) (P P' Q Q': Process) (H0: P == P'), eqP_aux Q Q' [] [(x,y)] = true -> Case M P x Q == Case N P' y Q'.
Proof.
  intros; subst.
  simpl in *; unfold Bool.Is_true, "=p" in *; simpl in *.
  rewrite eqT_aux_refl; intros; try contradiction; simpl.
  case_eq (eqP_aux P P' [] []); intros; rewrite H in H0; try contradiction.
  rewrite H1; trivial.
Qed.

Instance DecryptionProper : Proper (eq ==> eq ==> eq ==> equiv ==> equiv) Decryption.
Proof.
  unfold Proper, "==>"; intros t1 t1' H t2 t2' H0 x y H1 p q H2.
  rewrite H, H0, H1.
  simpl; unfold Bool.Is_true, eqP; simpl.
  simpl in H2; unfold Bool.Is_true, eqP in H2.
  case_eq (eqP_aux p q [] []); intros; rewrite H3 in H2; [| contradiction ].
  apply (eqP_aux_add_v _ _ y _) in H3; simpl in H3.
  rewrite 2?eqT_aux_refl; try contradiction.
  rewrite H3.
  simpl; trivial.
Defined.

Lemma DecryptionProper' : forall (M M' N N': Term) (H: M = M') (H0: N = N') (x y: Var) (P Q: Process), eqP_aux P Q [] [(x,y)] = true -> Decryption M N x P == Decryption M' N' y Q.
Proof.
  intros; subst.
  simpl in *; unfold Bool.Is_true, "=p" in *; simpl in *.
  rewrite 2?eqT_aux_refl; intros; try contradiction; simpl.
  rewrite H1; trivial.
Qed.

(* Returns a set of all free names in P. *)
Fixpoint fn (P: Process) : FSet Name :=
  match P with
    | Output M N P'       => fnt M ∪ fnt N ∪ fn P'
    | Input M x P'        => fnt M ∪ fn P'
    | Composition Q R     => fn Q ∪ fn R
    | Restriction n P'    => fn P' ∖ ❴n❵
    | Replication P'      => fn P'
    | Match M N P'        => fnt M ∪ fnt N ∪ fn P'
    | Nil                 => Ø
    | Split M x y P'      => fnt M ∪ fn P'
    | Case M Q x R        => fnt M ∪ fn Q ∪ fn R
    | Decryption M N x P' => fnt M ∪ fnt N ∪ fn P'
  end.

(* Returns a set of all free variables in P. *)
Fixpoint fv (P: Process) : FSet Var :=
  match P with
    | Output M N P'       => fvt M ∪ fvt N ∪ fv P'
    | Input M x P'        => fvt M ∪ (fv P' ∖ ❴x❵)
    | Composition Q R     => fv Q ∪ fv R
    | Restriction n P'    => fv P'
    | Replication P'      => fv P'
    | Match M N P'        => fvt M ∪ fvt N ∪ fv P'
    | Nil                 => Ø
    | Split M x y P'      => fvt M ∪ ((fv P' ∖ ❴x❵) ∖ ❴y❵)
    | Case M Q x R        => fvt M ∪ fv Q ∪ (fv R ∖ ❴x❵)
    | Decryption M N x P' => fvt M ∪ fvt N ∪ (fv P' ∖ ❴x❵)
  end.

(* Definitions and lemmas related to process substitution. *)

Fixpoint removeByL {A: Type} (x: string) (l: list (string * A)) : list (string * A) :=
  match l with
    | []        => []
    | (x',a)::ls => if string_dec x' x then removeByL x ls else (x',a)::removeByL x ls
  end.

Fixpoint Sub_aux (p : Process) (l : list (string * Term)) : Process :=
  match p with
    | Output M N P'       => Output (TSub_aux M l) (TSub_aux N l) (Sub_aux P' l)
    | Input M x P'        => if elem x (allFVT l) then
                               let x' := newVar x (toList (fv P' ∪ allFVT (removeByL x l))) in
                                 Input (TSub_aux M l) x' (Sub_aux P' ((x,TVar x')::removeByL x l))
                             else
                               Input (TSub_aux M l) x (Sub_aux P' (removeByL x l))
    | Composition Q R     => Composition (Sub_aux Q l) (Sub_aux R l)
    | Restriction n P'    => Restriction n (Sub_aux P' l)
    | Replication P'      => Replication (Sub_aux P' l)
    | Match M N P'        => Match (TSub_aux M l) (TSub_aux N l) (Sub_aux P' l)
    | Nil                 => Nil
    | Split M x y P'      => let l' := removeByL y (removeByL x l) in
                               if elem x (allFVT l) then
                                 let x' := newVar x (toList (fv P' ∪ allFVT l')) in
                                   if elem y (allFVT l) then
                                     let y' := newVar y (x'::toList (fv P' ∪ allFVT l')) in
                                       Split (TSub_aux M l) x' y' (Sub_aux P' ((x,TVar x')::(y,TVar y')::l'))
                                   else
                                     Split (TSub_aux M l) x' y (Sub_aux P' ((x,TVar x')::l'))
                               else
                                 if elem y (allFVT l) then
                                   let y' := newVar y (toList (fv P' ∪ allFVT l')) in
                                     Split (TSub_aux M l) x y' (Sub_aux P' ((y,TVar y')::l'))
                                 else
                                   Split (TSub_aux M l) x y (Sub_aux P' l')
    | Case M Q x R        => if elem x (allFVT l) then
                               let x' := newVar x (toList (fv R ∪ allFVT (removeByL x l))) in
                                 Case (TSub_aux M l) (Sub_aux Q l) x' (Sub_aux R ((x,TVar x')::removeByL x l))
                             else
                               Case (TSub_aux M l) (Sub_aux Q l) x (Sub_aux R (removeByL x l))
    | Decryption M N x P' => if elem x (allFVT l) then
                               let x' := newVar x (toList (fv P' ∪ allFVT (removeByL x l))) in
                                 Decryption (TSub_aux M l) (TSub_aux N l) x' (Sub_aux P' ((x,TVar x')::removeByL x l))
                             else
                               Decryption (TSub_aux M l) (TSub_aux N l) x (Sub_aux P' (removeByL x l))
  end.

(* Renames names within a term based on a list of name pairs (replace left name w/right). *)
Fixpoint TRename_aux (T: Term) (l: list (Name * Name)) : Term :=
  match T with
    | TName n        => TName (lookupDefault n l n)
    | Pair M N       => Pair (TRename_aux M l) (TRename_aux N l)
    | Zero           => Zero
    | Suc M          => Suc (TRename_aux M l)
    | TVar x         => TVar x
    | Encryption M N => Encryption (TRename_aux M l) (TRename_aux N l)
  end.

(* Performs a single replacement of all instances of m with n within T. *)
Definition TRename (T: Term) (n m: Name) : Term := TRename_aux T [(m, n)].

(* Renames names within a process based on a list of name pairs (replace left name w/right). *)
Fixpoint Rename_aux (P: Process) (l: list (Name * Name)) : Process :=
  match P with
    | Output M N P'       => Output (TRename_aux M l) (TRename_aux N l) (Rename_aux P' l)
    | Input M x P'        => Input (TRename_aux M l) x (Rename_aux P' l)
    | Composition Q R     => Composition (Rename_aux Q l) (Rename_aux R l)
    | Restriction n P'    => if elem n (allVars l) then
                               let n' := newVar n (toList (fn P') ++ map snd (removeByL n l)) in
                               Restriction n (Rename_aux P' ((n, n')::removeByL n l))
                             else
                               Restriction n (Rename_aux P' (removeByL n l))
    | Replication P'      => Replication (Rename_aux P' l)
    | Match M N P'        => Match (TRename_aux M l) (TRename_aux N l) (Rename_aux P' l)
    | Nil                 => Nil
    | Split M x y P'      => Split (TRename_aux M l) x y (Rename_aux P' l)
    | Case M Q x R        => Case (TRename_aux M l) (Rename_aux Q l) x (Rename_aux R l)
    | Decryption M N x P' => Decryption (TRename_aux M l) (TRename_aux N l) x (Rename_aux P' l)
  end.

(* Performs a single replacement of all instances of m with n within P. *)
Definition Rename (P: Process) (n m: Name) : Process := Rename_aux P [(m, n)].

Lemma TRename_aux_empty : forall T, TRename_aux T [] = T.
Proof.
  intros.
  induction T; simpl; rewrite 1?IHT1, 1?IHT2, 1?IHT; trivial.
Qed.

Lemma Rename_aux_empty : forall P, Rename_aux P [] = P.
Proof.
  intros.
  induction P; simpl; unfold Name in *; rewrite 2?TRename_aux_empty, 1?IHP1, 1?IHP2, 1?IHP; trivial.
Qed.

(* A term renaming is irrelevant to a free variable check.  General list version. *)
Lemma fvt_TRename_aux : forall T l, fvt (TRename_aux T l) == fvt T.
Proof.
  intros.
  induction T; simpl fvt; trivial.
  simpl; trivial.
  rewrite IHT1, IHT2; simpl; trivial.
  simpl; trivial.
  simpl; trivial.
  rewrite IHT1, IHT2; simpl; trivial.
Qed.

(* A term renaming is irrelevant to a free variable check. *)
Lemma fvt_TRename : forall T n m, fvt (TRename T n m) == fvt T.
Proof.
  intros; apply fvt_TRename_aux.
Qed.

(* A process renaming is irrelevant to a free variable check.  General list version. *)
Lemma fv_Rename_aux : forall P l, fv (Rename_aux P l) == fv P.
Proof.
  assert (Lem := fvt_TRename_aux).
  induction P; intros; simpl fv in *; trivial.
  do 2 rewrite Lem; rewrite IHP; simpl; trivial.
  rewrite Lem, IHP; simpl; trivial.
  rewrite IHP1, IHP2; simpl; trivial.
  destruct (elem n (allVars l)); simpl fv; rewrite IHP; simpl; trivial.
  do 2 rewrite Lem; rewrite IHP; simpl; trivial.
  simpl; trivial.
  rewrite Lem; rewrite IHP; simpl; trivial.
  rewrite Lem; rewrite IHP1, IHP2; simpl; trivial.
  do 2 rewrite Lem; rewrite IHP; simpl; trivial.
Qed.

(* A process renaming is irrelevant to a free variable check. *)
Lemma fv_Rename : forall P n m, fv (Rename P n m) == fv P.
Proof.
  intros; apply fv_Rename_aux.
Qed.

(* Sublemma for fn_Sub_aux. *)
Lemma removeByL_redundant : forall s (l: list (string * Term)), ❴ s ❵ ∪ allVars (removeByL s l) == ❴ s ❵ ∪ allVars l.
Proof.
  intros; induction l.
  simpl; apply Permutation_refl.
  simpl allVars; destruct a, (string_dec s0 s); subst.
  rewrite IHl; simpl fst; rewrite <- union_assoc, union_idemp.
  reflexivity.
  simpl allVars; simpl fst.
  rewrite <- 2?union_assoc, (union_comm ❴ s ❵ ❴ s0 ❵), union_assoc, IHl, <- union_assoc.
  reflexivity.
Qed.

(* Sublemma for fn_Sub_aux. *)
Lemma allFNT_remove_subset : forall v l, allFNT (removeByL v l) ⊆ allFNT l.
Proof.
  intros; induction l; simpl.
  reflexivity.
  destruct a, (string_dec s v); simpl; rewrite IHl.
  unfold incl_set; intros; rewrite elem_union_iff; right; assumption.
  reflexivity.
Qed.

(* The free names of a substitution will be a subset of all the names present in the processes and terms that existed before. *)
Lemma fn_Sub_aux : forall p l, fn (Sub_aux p l) ⊆ (fn p ∪ allFNT l).
Proof.
  induction p; intros l; simpl.
  (* Output *)
  rewrite 2?fnt_TSub_aux, IHp.
  rewrite 3?union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT l)), (union_assoc (fn p) (allFNT l) (allFNT l)), union_idemp, (union_comm (allFNT l) (fnt t0 ∪ (fn p ∪ allFNT l))), 4?union_assoc, union_idemp.
  reflexivity.
  (* Input *)
  destruct (elem v (allFVT l)); simpl; rewrite fnt_TSub_aux, IHp.
  simpl; rewrite union_empty_l.
  rewrite union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT (removeByL v l))), (union_assoc (fn p) (allFNT (removeByL v l)) (allFNT l)), allFNT_remove_subset, union_idemp, <- union_assoc.
  reflexivity.
  rewrite union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT (removeByL v l))), (union_assoc (fn p) (allFNT (removeByL v l)) (allFNT l)), allFNT_remove_subset, union_idemp, <- union_assoc.
  reflexivity.
  (* Composition *)
  rewrite IHp1, IHp2.
  rewrite union_assoc, (union_comm (allFNT l) (fn p2 ∪ allFNT l)), (union_assoc (fn p2) (allFNT l) (allFNT l)), union_idemp, <- union_assoc.
  reflexivity.
  (* Restriction. *)
  rewrite IHp.
  rewrite diff_union_l.
  unfold incl_set; intros.
  rewrite elem_union_iff in H; rewrite elem_union_iff.
  destruct H.
  left; assumption.
  right; rewrite elem_diff_iff in H; destruct H; assumption.
  (* Replication *)
  rewrite IHp.
  reflexivity.
  (* Match *)
  rewrite 2?fnt_TSub_aux, IHp.
  rewrite 3?union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT l)), (union_assoc (fn p) (allFNT l) (allFNT l)), union_idemp, (union_comm (allFNT l) (fnt t0 ∪ (fn p ∪ allFNT l))), 4?union_assoc, union_idemp.
  reflexivity.
  (* Nil *)
  unfold incl_set; intros; contradiction.
  (* Split *)
  destruct (elem v (allFVT l)); destruct (elem v0 (allFVT l)); simpl; rewrite fnt_TSub_aux, IHp.
  simpl; rewrite 2?union_empty_l.
  rewrite union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT (removeByL v0 (removeByL v l)))), (union_assoc (fn p) (allFNT (removeByL v0 (removeByL v l))) (allFNT l)), 2?allFNT_remove_subset, union_idemp, <- union_assoc.
  reflexivity.
  simpl; rewrite union_empty_l.
  rewrite union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT (removeByL v0 (removeByL v l)))), (union_assoc (fn p) (allFNT (removeByL v0 (removeByL v l))) (allFNT l)), 2?allFNT_remove_subset, union_idemp, <- union_assoc.
  reflexivity.
  simpl; rewrite union_empty_l.
  rewrite union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT (removeByL v0 (removeByL v l)))), (union_assoc (fn p) (allFNT (removeByL v0 (removeByL v l))) (allFNT l)), 2?allFNT_remove_subset, union_idemp, <- union_assoc.
  reflexivity.
  rewrite union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT (removeByL v0 (removeByL v l)))), (union_assoc (fn p) (allFNT (removeByL v0 (removeByL v l))) (allFNT l)), 2?allFNT_remove_subset, union_idemp, <- union_assoc.
  reflexivity.
  (* Case *)
  destruct (elem v (allFVT l)); simpl; rewrite fnt_TSub_aux, IHp1, IHp2.
  simpl; rewrite union_empty_l.
  rewrite 3?union_assoc, (union_comm (allFNT l) (fn p2 ∪ allFNT (removeByL v l))), (union_assoc (fn p2) (allFNT (removeByL v l)) (allFNT l)), allFNT_remove_subset, union_idemp, (union_comm (allFNT l) (fn p1 ∪ (fn p2 ∪ allFNT l))), 4?union_assoc, union_idemp.
  reflexivity.
  rewrite 3?union_assoc, (union_comm (allFNT l) (fn p2 ∪ allFNT (removeByL v l))), (union_assoc (fn p2) (allFNT (removeByL v l)) (allFNT l)), allFNT_remove_subset, union_idemp, (union_comm (allFNT l) (fn p1 ∪ (fn p2 ∪ allFNT l))), 4?union_assoc, union_idemp.
  reflexivity.
  (* Decryption *)
  destruct (elem v (allFVT l)); simpl; rewrite 2?fnt_TSub_aux, IHp.
  simpl; rewrite union_empty_l.
  rewrite 3?union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT (removeByL v l))), (union_assoc (fn p) (allFNT (removeByL v l)) (allFNT l)), allFNT_remove_subset, union_idemp, (union_comm (allFNT l) (fnt t0 ∪ (fn p ∪ allFNT l))), 4?union_assoc, union_idemp.
  reflexivity.
  rewrite 3?union_assoc, (union_comm (allFNT l) (fn p ∪ allFNT (removeByL v l))), (union_assoc (fn p) (allFNT (removeByL v l)) (allFNT l)), allFNT_remove_subset, union_idemp, (union_comm (allFNT l) (fnt t0 ∪ (fn p ∪ allFNT l))), 4?union_assoc, union_idemp.
  reflexivity.
Qed.

(* Sublemma for fv_Sub_aux. *)
Lemma allFVT_remove_subset : forall v l, allFVT (removeByL v l) ⊆ allFVT l.
Proof.
  intros; induction l; simpl.
  reflexivity.
  destruct a, (string_dec s v); simpl; rewrite IHl.
  unfold incl_set; intros; rewrite elem_union_iff; right; assumption.
  reflexivity.
Qed.

(* Similar in purpose to removeByL_redundant, but was more convenient at the time. *)
Lemma allVars_not_in : forall x v (l: list (string * Term)), x ∉ allVars (removeByL v l) -> x ∉ ❴ v ❵ -> x ∉ allVars l.
Proof.
  intros; induction l; simpl in *.
  assumption.
  rewrite elem_union_iff; intro.
  destruct a, (string_dec s v); simpl in H1; subst.
  destruct H1; [contradiction | apply IHl in H; contradiction].
  simpl in H; rewrite elem_union_iff in H; apply Decidable.not_or in H.
  destruct H, H1; [contradiction | apply IHl in H2; contradiction].
Qed.

Lemma fv_Sub_aux : forall p l, fv (Sub_aux p l) ⊆ (fv p ∖ allVars l) ∪ allFVT l.
Proof.
  induction p; intros l; simpl.
  (* Output *)
  rewrite 2?fvt_TSub_aux, IHp.
  unfold incl_set; intros.
  rewrite elem_union_iff; rewrite 2?elem_union_iff in H.
  destruct H; [destruct H | ].
  rewrite elem_union_iff in H; destruct H; [rewrite elem_diff_iff in H; destruct H; left; rewrite elem_diff_iff, elem_union_iff; split; trivial | right; assumption].
  rewrite elem_union_iff; left; left; assumption.
  rewrite elem_union_iff in H; destruct H; [rewrite elem_diff_iff in H; destruct H; left; rewrite elem_diff_iff, elem_union_iff; split; trivial | right; assumption].
  rewrite elem_union_iff; left; right; assumption.
  rewrite elem_union_iff in H; destruct H; [rewrite elem_diff_iff in H; destruct H; left; rewrite elem_diff_iff, elem_union_iff; split; trivial | right; assumption].
  rewrite elem_union_iff; right; assumption.
  (* Input (renaming) *)
  destruct (elem v (allFVT l)); simpl; rewrite fvt_TSub_aux, IHp; simpl.
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff; rewrite 2?elem_union_iff, elem_diff_iff in H.
  destruct H; [destruct H | ].
  destruct H.
  left; split; trivial.
  rewrite elem_union_iff; left; assumption.
  right; assumption.
  rewrite elem_diff_iff in H; destruct H.
  rewrite elem_union_iff in H; destruct H.
  rewrite elem_diff_iff in H; destruct H.
  rewrite removeByL_redundant in H1.
  rewrite elem_union_iff in H1; apply Decidable.not_or in H1; destruct H1.
  left; split; trivial.
  rewrite elem_union_iff; right; rewrite elem_diff_iff; split; trivial.
  rewrite elem_union_iff in H; destruct H.
  contradiction.
  right; apply allFVT_remove_subset in H; trivial.
  (* Input (no renaming) *)
  rewrite allFVT_remove_subset.
  unfold incl_set; intros.
  rewrite 2?elem_union_iff, 2?elem_diff_iff, elem_union_iff, elem_diff_iff in H; rewrite elem_union_iff, elem_diff_iff, elem_union_iff.
  destruct H; [destruct H; [destruct H; left; split; trivial; left; assumption | right; assumption] | ].
  destruct H; destruct H; [destruct H | ].
  left; split.
  right; rewrite elem_diff_iff; split; trivial.
  apply (allVars_not_in _ v); trivial.
  right; assumption.
  (* Composition *)
  rewrite IHp1, IHp2.
  unfold incl_set; intros.
  rewrite 3?elem_union_iff, 2?elem_diff_iff in H.
  rewrite elem_union_iff, 2?elem_diff_iff, elem_union_iff.
  destruct H; destruct H.
  destruct H; left; split; trivial; left; assumption.
  right; assumption.
  destruct H; left; split; trivial; right; assumption.
  right; assumption.
  (* Restriction *)
  rewrite IHp; reflexivity.
  (* Replication *)
  rewrite IHp; reflexivity.
  (* Match *)
  rewrite 2?fvt_TSub_aux, IHp.
  unfold incl_set; intros.
  rewrite elem_union_iff; rewrite 2?elem_union_iff in H.
  destruct H; [destruct H | ].
  rewrite elem_union_iff in H; destruct H; [rewrite elem_diff_iff in H; destruct H; left; rewrite elem_diff_iff, elem_union_iff; split; trivial | right; assumption].
  rewrite elem_union_iff; left; left; assumption.
  rewrite elem_union_iff in H; destruct H; [rewrite elem_diff_iff in H; destruct H; left; rewrite elem_diff_iff, elem_union_iff; split; trivial | right; assumption].
  rewrite elem_union_iff; left; right; assumption.
  rewrite elem_union_iff in H; destruct H; [rewrite elem_diff_iff in H; destruct H; left; rewrite elem_diff_iff, elem_union_iff; split; trivial | right; assumption].
  rewrite elem_union_iff; right; assumption.
  (* Nil *)
  unfold incl_set; intros; contradiction.
  (* Split *)
  destruct (elem v (allFVT l)); destruct (elem v0 (allFVT l)); simpl; rewrite fvt_TSub_aux, IHp; simpl.
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff, elem_union_iff, 2?elem_diff_iff.
  rewrite 2?elem_union_iff, 3?elem_diff_iff, 3?elem_union_iff, 2?elem_diff_iff in H.
  destruct H; [destruct H | ].
  destruct H.
  left; split; trivial.
  left; assumption.
  right; assumption.
  destruct H; destruct H; destruct H.
  rewrite 2?elem_diff_iff in H; destruct H.
  rewrite removeByL_redundant, (union_comm ❴ v0 ❵ (allVars (removeByL v l))), <- union_assoc, removeByL_redundant, 2?elem_union_iff in H2; apply Decidable.not_or in H2; destruct H2; apply Decidable.not_or in H2; destruct H2.
  left; split; trivial; right; split; trivial; split; trivial.
  do 2 (destruct H; [contradiction | ]).
  right; apply allFVT_remove_subset in H; apply allFVT_remove_subset in H; assumption.
  (* Split (cont'd) *)
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff, elem_union_iff, 2?elem_diff_iff.
  rewrite 2?elem_union_iff, 3?elem_diff_iff, 3?elem_union_iff, 2?elem_diff_iff in H.
  destruct H; [destruct H | ].
  destruct H.
  left; split; trivial.
  left; assumption.
  right; assumption.
  destruct H; destruct H; destruct H.
  rewrite 2?elem_diff_iff in H; destruct H.
  rewrite elem_union_iff in H2; apply Decidable.not_or in H2; destruct H2.
  apply allVars_not_in in H3; trivial; apply allVars_not_in in H3; trivial.
  left; split; trivial; right; split; trivial; split; trivial.
  destruct H; [contradiction | ].
  right; apply allFVT_remove_subset in H; apply allFVT_remove_subset in H; assumption.
  (* Split (cont'd) *)
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff, elem_union_iff, 2?elem_diff_iff.
  rewrite 2?elem_union_iff, 3?elem_diff_iff, 3?elem_union_iff, 2?elem_diff_iff in H.
  destruct H; [destruct H | ].
  destruct H.
  left; split; trivial.
  left; assumption.
  right; assumption.
  destruct H; destruct H; destruct H.
  rewrite 2?elem_diff_iff in H; destruct H.
  rewrite elem_union_iff in H2; apply Decidable.not_or in H2; destruct H2.
  apply allVars_not_in in H3; trivial; apply allVars_not_in in H3; trivial.
  left; split; trivial; right; split; trivial; split; trivial.
  destruct H; [contradiction | ].
  right; apply allFVT_remove_subset in H; apply allFVT_remove_subset in H; assumption.
  (* Split (cont'd) *)
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff, elem_union_iff, 2?elem_diff_iff.
  rewrite 2?elem_union_iff, 3?elem_diff_iff, 3?elem_union_iff, 2?elem_diff_iff in H.
  destruct H; [destruct H | ].
  destruct H.
  left; split; trivial.
  left; assumption.
  right; assumption.
  destruct H; destruct H; destruct H.
  rewrite 2?elem_diff_iff in H; destruct H.
  apply allVars_not_in in H2; trivial; apply allVars_not_in in H2; trivial.
  left; split; trivial; right; split; trivial; split; trivial.
  right; apply allFVT_remove_subset in H; apply allFVT_remove_subset in H; assumption.
  (* Case (renaming) *)
  destruct (elem v (allFVT l)); simpl; rewrite fvt_TSub_aux, IHp1, IHp2; simpl.
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff, 2?elem_union_iff, 2?elem_diff_iff.
  rewrite 2?elem_union_iff, 3?elem_diff_iff, 3?elem_union_iff, 2?elem_diff_iff in H.
  destruct H; destruct H.
  destruct H; [destruct H | right; assumption].
  left; split; trivial.
  left; left; trivial.
  destruct H; [destruct H | right; assumption].
  left; split; trivial.
  left; right; trivial.
  rewrite removeByL_redundant, elem_diff_iff, 2?elem_union_iff in H.
  destruct H; [destruct H | ].
  apply Decidable.not_or in H1; destruct H1.
  left; split; trivial.
  right; split; trivial.
  destruct H.
  contradiction.
  right; apply allFVT_remove_subset in H; trivial.
  (* Case (no renaming *)
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff, 2?elem_union_iff, 2?elem_diff_iff.
  rewrite 2?elem_union_iff, 3?elem_diff_iff, 3?elem_union_iff, 2?elem_diff_iff in H.
  destruct H; destruct H.
  destruct H; [destruct H | right; assumption].
  left; split; trivial.
  left; left; assumption.
  destruct H; [destruct H | right; assumption].
  left; split; trivial; left; right; trivial.
  rewrite elem_diff_iff in H.
  destruct H; [destruct H | ].
  apply allVars_not_in in H1; trivial.
  left; split; trivial; right; split; trivial; split; trivial.
  right; apply allFVT_remove_subset in H; trivial.
  (* Decryption (renaming) *)
  destruct (elem v (allFVT l)); simpl; rewrite 2?fvt_TSub_aux, IHp; simpl.
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff, 2?elem_union_iff, 2?elem_diff_iff.
  rewrite 2?elem_union_iff, 3?elem_diff_iff, 3?elem_union_iff, 2?elem_diff_iff in H.
  destruct H; destruct H.
  destruct H; [destruct H | right; assumption].
  left; split; trivial.
  left; left; trivial.
  destruct H; [destruct H | right; assumption].
  left; split; trivial.
  left; right; trivial.
  rewrite removeByL_redundant, elem_diff_iff, 2?elem_union_iff in H.
  destruct H; [destruct H | ].
  apply Decidable.not_or in H1; destruct H1.
  left; split; trivial.
  right; split; trivial.
  destruct H.
  contradiction.
  right; apply allFVT_remove_subset in H; trivial.
  (* Decryption (no renaming) *)
  unfold incl_set; intros.
  rewrite elem_union_iff, elem_diff_iff, 2?elem_union_iff, 2?elem_diff_iff.
  rewrite 2?elem_union_iff, 3?elem_diff_iff, 3?elem_union_iff, 2?elem_diff_iff in H.
  destruct H; destruct H.
  destruct H; [destruct H | right; assumption].
  left; split; trivial.
  left; left; assumption.
  destruct H; [destruct H | right; assumption].
  left; split; trivial; left; right; trivial.
  rewrite elem_diff_iff in H.
  destruct H; [destruct H | ].
  apply allVars_not_in in H1; trivial.
  left; split; trivial; right; split; trivial; split; trivial.
  right; apply allFVT_remove_subset in H; trivial.
Qed.

(* Single term substitution into a process. *)
Definition Sub (p: Process) (t: Term) (x : Var) : Process := Sub_aux p [(x,t)].

Notation "p '〚' t '∕' x '〛'" := (Sub p t x) (at level 90).

(* Single term version of fn_Sub_aux. *)
Lemma fn_Sub : forall p t x, fn (p〚t∕x〛) ⊆ (fn p ∪ fnt t).
Proof.
  intros.
  apply fn_Sub_aux.
Qed.

(* Single term version of fv_Sub_aux. *)
Lemma fv_Sub : forall p t x, fv (p〚t∕x〛) ⊆ (fv p ∖ ❴ x ❵ ∪ fvt t).
Proof.
  intros.
  apply fv_Sub_aux.
Qed.

(* Replacing a variable with a new one within a term does not affect closedness.  General list version. *)
Lemma newVar_term_closed_aux : forall T x x', fvt T ∖ ❴ x ❵ == Ø -> fvt (TSub_aux T [(x, TVar x')]) ∖ ❴ x' ❵ == Ø.
Proof.
  intros.
  induction T; simpl fvt in *; simpl TSub_aux; trivial.
  rewrite diff_union_l.
  rewrite diff_union_l, union_empty in H; destruct H.
  apply IHT1 in H; apply IHT2 in H0; rewrite H, H0; simpl; trivial.
  apply IHT in H; trivial.
  destruct (string_dec v x); subst; simpl fvt.
  rewrite diff_equal; simpl; trivial.
  simpl in H; destruct (string_dec v x); [ | apply Permutation_sym in H; assert (H0 := Permutation_nil_cons); specialize H0 with _ [] v]; contradiction.
  rewrite diff_union_l.
  rewrite diff_union_l, union_empty in H; destruct H.
  apply IHT1 in H; apply IHT2 in H0; rewrite H, H0; simpl; trivial.
Qed.

(* Replacing a variable with a new one within a term does not affect closedness. *)
Lemma newVar_term_closed : forall T x x', fvt T ∖ ❴ x ❵ == Ø -> fvt (TSub T (TVar x') x) ∖ ❴ x' ❵ == Ø.
Proof.
  intros.
  apply newVar_term_closed_aux; trivial.
Qed.

(* Sublemmas for newVar_proc_closed_aux. *)

Lemma TSub_empty_aux : forall T, TSub_aux T [] = T.
Proof.
  intros.
  induction T; simpl; rewrite 1?IHT, 1?IHT1, 1?IHT2; trivial.
Qed.

Lemma Sub_empty_aux : forall P, Sub_aux P [] = P.
Proof.
  intros.
  induction P; simpl; rewrite 2?TSub_empty_aux, 1?IHP, 1?IHP1, 1?IHP2; trivial.
Qed.

(* Replacing a variable with a new one within a process does not affect closedness.  General list version. *)
Lemma newVar_proc_closed_aux : forall P x x', fv P ∖ ❴ x ❵ == Ø -> fv (Sub_aux P [(x, TVar x')]) ∖ ❴ x' ❵ == Ø.
Proof.
  assert (Lem := newVar_term_closed).
  induction P; intros; simpl fv in *; unfold TSub; simpl TSub_aux; unfold Sub; simpl Sub_aux; try rewrite diff_union_l; try rewrite diff_union_l.
  (* Output *)
  do 2 rewrite diff_union_l, union_empty in H; do 2 destruct H.
  apply (Lem _ _ x') in H; apply (Lem _ _ x') in H1; apply (IHP _ x') in H0.
  rewrite H, H0, H1; simpl; trivial.
  (* Input *)
  rewrite diff_union_l, union_empty in H; destruct H.
  apply (Lem _ _ x') in H.
  destruct (elem v (❴ x' ❵ ∪ Ø)).
  destruct (string_dec x v); subst; simpl fv.
  rewrite <- diff_union_diff in H0; rewrite union_idemp in H0.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux.
  simpl allVars; simpl allFVT.
  rewrite 2?union_empty_r, H0, union_empty_l, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite <- diff_union_diff in H0.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux.
  simpl allVars; simpl allFVT.
  rewrite 2?union_empty_r, H0, union_empty_l.
  rewrite diff_union_l, diff_equal, union_empty_l, diff_exchange, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  destruct (string_dec x v); subst; simpl fv.
  rewrite <- diff_union_diff in H0; rewrite union_idemp in H0.
  rewrite diff_union_l, H, Sub_empty_aux, H0, 2?diff_empty_l, union_idemp; reflexivity.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl allVars; simpl allFVT; rewrite 2?union_empty_r, 2?diff_union_l.
  rewrite diff_exchange in H0.
  rewrite H0, diff_empty_l, union_empty_l, diff_exchange, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  (* Composition *)
  rewrite diff_union_l, union_empty in H; destruct H.
  apply (IHP1 _ x') in H; apply (IHP2 _ x') in H0.
  rewrite H, H0, union_idemp; reflexivity.
  (* Restriction *)
  apply IHP; rewrite H; reflexivity.
  (* Replication *)
  apply IHP; rewrite H; reflexivity.
  (* Match *)
  do 2 rewrite diff_union_l, union_empty in H; do 2 destruct H.
  apply (Lem _ _ x') in H; apply (Lem _ _ x') in H1; apply (IHP _ x') in H0.
  rewrite H, H0, H1; simpl; trivial.
  (* Nil *)
  rewrite diff_empty_l; reflexivity.
  (* Split *)
  rewrite diff_union_l, union_empty in H; destruct H.
  apply (Lem _ _ x') in H.
  destruct (elem v (❴ x' ❵ ∪ Ø)); destruct (elem v0 (❴ x' ❵ ∪ Ø)); destruct (string_dec x v); subst; simpl fv.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl allVars; simpl allFVT.
  rewrite <- diff_union_diff, union_comm, diff_union_diff in H0.
  rewrite <- (diff_union_diff (fv P) ❴ v ❵ ❴ v ❵), union_idemp in H0.
  rewrite 2?union_empty_r, diff_union_diff, H0, union_empty_l.
  rewrite diff_union_l, diff_equal, union_empty_l.
  rewrite (diff_exchange ❴ newVar v0 (newVar v (proj1_sig (fv P)) :: proj1_sig (fv P)) ❵ ❴ newVar v (proj1_sig (fv P)) ❵ ❴ newVar v0 (newVar v (proj1_sig (fv P)) :: proj1_sig (fv P)) ❵), diff_equal, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  destruct (string_dec x v0); subst; simpl fv.
  rewrite <- diff_union_diff, union_idemp in H0.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl allVars; simpl allFVT.
  rewrite 2?union_empty_r, diff_union_diff, H0, union_empty_l.
  rewrite diff_union_l, diff_equal, union_empty_l.
  rewrite (diff_exchange ❴ newVar v0 (newVar v (proj1_sig (fv P)) :: proj1_sig (fv P)) ❵ ❴ newVar v (proj1_sig (fv P)) ❵ ❴ newVar v0 (newVar v (proj1_sig (fv P)) :: proj1_sig (fv P)) ❵), diff_equal, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl allVars; simpl allFVT.
  rewrite <- 2?diff_union_diff in H0.
  rewrite 2?union_empty_r, H0, union_empty_l.
  rewrite diff_union_l, diff_equal, union_empty_l.
  rewrite 2?diff_union_l.
  rewrite (diff_exchange ❴ newVar v0 (newVar v (ListSet.set_add string_dec x' (proj1_sig (fv P))) :: ListSet.set_add string_dec x' (proj1_sig (fv P))) ❵
                         ❴ newVar v (ListSet.set_union string_dec (proj1_sig (fv P)) (proj1_sig (❴ x' ❵ ∪ Ø))) ❵
                         ❴ newVar v0 (newVar v (ListSet.set_union string_dec (proj1_sig (fv P)) (proj1_sig (❴ x' ❵ ∪ Ø))):: ListSet.set_union string_dec (proj1_sig (fv P)) (proj1_sig (❴ x' ❵ ∪ Ø))) ❵).
  rewrite diff_equal, diff_empty_l, union_empty_l.
  rewrite diff_exchange.
  rewrite (diff_exchange (❴ x' ❵ ∪ Ø) ❴ newVar v (ListSet.set_union string_dec (proj1_sig (fv P)) (proj1_sig (❴ x' ❵ ∪ Ø))) ❵ ❴ x' ❵).
  rewrite diff_union_l, diff_equal, diff_empty_l, union_idemp, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite diff_exchange, <- (diff_union_diff (fv P) ❴ v ❵ ❴ v ❵), union_idemp in H0.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r.
  rewrite diff_union_l, diff_equal, union_empty_r, (diff_exchange (fv P ∖ ❴ v ❵) ❴ newVar v (proj1_sig (fv P)) ❵ ❴ v0 ❵), H0, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  destruct (string_dec x v0); subst; simpl fv.
  rewrite <- diff_union_diff, union_idemp in H0.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r.
  rewrite diff_union_l, diff_equal, union_empty_r.
  rewrite (diff_exchange (fv P ∖ ❴ v ❵) ❴ newVar v (proj1_sig (fv P)) ❵ ❴ v0 ❵), H0, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r, (diff_exchange (fv P ∖ (❴ v ❵ ∪ ❴ x ❵) ∪ (❴ newVar v (ListSet.set_add string_dec x' (proj1_sig (fv P))) ❵ ∪ ❴ x' ❵)) ❴ newVar v (ListSet.set_add string_dec x' (proj1_sig (fv P))) ❵ ❴ v0 ❵).
  rewrite diff_union_l, diff_union_diff, (diff_exchange (fv P ∖ ❴ v ❵) ❴ x ❵ ❴ v0 ❵), H0.
  rewrite union_empty_l.
  rewrite 2?diff_union_l, (diff_exchange), diff_equal, 2?diff_empty_l, union_empty_l, diff_exchange, (diff_exchange ❴ x' ❵ ❴ v0 ❵ ❴ x' ❵), diff_equal, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite diff_exchange, <- (diff_union_diff (fv P) ❴ v ❵ ❴ v ❵), union_idemp in H0.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r, diff_union_l, (diff_exchange (fv P) ❴ v0 ❵ ❴ v ❵), H0, union_empty_l.
  rewrite (diff_exchange ❴ newVar v0 (proj1_sig (fv P)) ❵ ❴ v ❵ ❴ newVar v0 (proj1_sig (fv P)) ❵), diff_equal, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  destruct (string_dec x v0); subst; simpl fv.
  rewrite <- diff_union_diff, union_idemp in H0.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r.
  rewrite diff_union_l, (diff_exchange (fv P) ❴ v0 ❵ ❴ v ❵), H0, union_empty_l.
  rewrite (diff_exchange ❴ newVar v0 (proj1_sig (fv P)) ❵ ❴ v ❵ ❴ newVar v0 (proj1_sig (fv P)) ❵), diff_equal, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r, diff_union_l, (diff_union_diff (fv P) ❴ v0 ❵ ❴ x ❵), (diff_exchange (fv P ∖ ❴ v0 ❵) ❴ x ❵ ❴ v ❵), (diff_exchange (fv P) ❴ v0 ❵ ❴ v ❵), H0, union_empty_l.
  rewrite 2?diff_union_l, (diff_exchange ❴ newVar v0 (ListSet.set_add string_dec x' (proj1_sig (fv P))) ❵ ❴ v ❵ ❴ newVar v0 (ListSet.set_add string_dec x' (proj1_sig (fv P))) ❵), diff_equal, diff_empty_l, union_empty_l.
  rewrite (diff_exchange (❴ x' ❵ ∖ ❴ v ❵) ❴ newVar v0 (ListSet.set_add string_dec x' (proj1_sig (fv P))) ❵ ❴ x' ❵).
  rewrite (diff_exchange ❴ x' ❵ ❴ v ❵ ❴ x' ❵), diff_equal, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite diff_exchange, <- (diff_union_diff (fv P) ❴ v ❵ ❴ v ❵), union_idemp in H0.
  rewrite diff_union_l, H, union_empty_l, Sub_empty_aux, H0, diff_empty_l; reflexivity.
  destruct (string_dec x v0); subst.
  rewrite <- diff_union_diff, union_idemp in H0.
  rewrite diff_union_l, H, union_empty_l, Sub_empty_aux, H0, diff_empty_l; reflexivity.
  rewrite diff_union_l, H, union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r, 2?diff_union_l, (diff_exchange (fv P) ❴ x ❵ ❴ v ❵), (diff_exchange (fv P ∖ ❴ v ❵) ❴ x ❵ ❴ v0 ❵), H0, union_empty_l.
  rewrite diff_exchange, (diff_exchange ❴ x' ❵ ❴ v ❵ ❴ x' ❵), diff_equal, 2?diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  (* Case *)
  rewrite diff_union_l, union_empty in H; destruct H.
  rewrite diff_union_l, union_empty in H; destruct H.
  apply (Lem _ _ x') in H; apply (IHP1 _ x') in H1.
  destruct (elem v (❴ x' ❵ ∪ Ø)).
  destruct (string_dec x v); subst; simpl fv.
  rewrite <- diff_union_diff in H0; rewrite union_idemp in H0.
  rewrite 2?diff_union_l, H, H1, 2?union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r, H0, union_empty_l, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite 2?diff_union_l, H, H1, 2?union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite <- diff_union_diff in H0.
  rewrite 2?union_empty_r, H0, union_empty_l. rewrite diff_union_l, diff_equal, union_empty_l, diff_exchange, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  destruct (string_dec x v); subst; simpl fv.
  rewrite <- diff_union_diff in H0; rewrite union_idemp in H0.
  rewrite 2?diff_union_l, H, H1, Sub_empty_aux, H0, 2?diff_empty_l, 2?union_idemp; reflexivity.
  rewrite 2?diff_union_l, H, H1, 2?union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl allVars; simpl allFVT; rewrite 2?union_empty_r, 2?diff_union_l.
  rewrite diff_exchange in H0.
  rewrite H0, diff_empty_l, union_empty_l, diff_exchange, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  (* Decryption *)
  rewrite diff_union_l, union_empty in H; destruct H.
  rewrite diff_union_l, union_empty in H; destruct H.
  apply (Lem _ _ x') in H; apply (Lem _ _ x') in H1.
  destruct (elem v (❴ x' ❵ ∪ Ø)).
  destruct (string_dec x v); subst; simpl fv.
  rewrite <- diff_union_diff in H0; rewrite union_idemp in H0.
  rewrite 2?diff_union_l, H, H1, 2?union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r, H0, union_empty_l, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  rewrite <- diff_union_diff in H0.
  rewrite 2?diff_union_l, H, H1, 2?union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl.
  rewrite 2?union_empty_r, H0, union_empty_l.
  rewrite diff_union_l, diff_equal, union_empty_l, diff_exchange, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
  destruct (string_dec x v); subst; simpl fv.
  rewrite <- diff_union_diff in H0; rewrite union_idemp in H0.
  rewrite 2?diff_union_l, H, H1, Sub_empty_aux, H0, 2?diff_empty_l, 2?union_idemp; reflexivity.
  rewrite 2?diff_union_l, H, H1, 2?union_empty_l.
  antisymmetry.
  rewrite fv_Sub_aux; simpl allVars; simpl allFVT; rewrite 2?union_empty_r, 2?diff_union_l.
  rewrite diff_exchange in H0.
  rewrite H0, diff_empty_l, union_empty_l, diff_exchange, diff_equal, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
Qed.

(* Replacing a variable with a new one within a term does not affect closedness. *)
Lemma newVar_proc_closed : forall P x x', fv P ∖ ❴ x ❵ == Ø -> fv (Sub P (TVar x') x) ∖ ❴ x' ❵ == Ø.
Proof.
  intros.
  apply newVar_proc_closed_aux; trivial.
Qed.

(* Definition of a closed process and getter functions for one. *)
Definition ClosedProcess : Type := { P: Process | fv P == Ø}.
Definition getProc (P: ClosedProcess) : Process := proj1_sig P.

(* Equivalence relation on closed processes that ignores the accompanying proof. *)
Instance ClosedProcessSetoid : Setoid ClosedProcess := {|
  equiv := fun P Q => getProc P == getProc Q |}.
Proof.
  split.
  unfold Reflexive.
  intros P; reflexivity.
  unfold Symmetric; intros P Q H.
  symmetry; assumption.
  unfold Transitive.
  intros P Q R H H0.
  transitivity (getProc Q); assumption.
Defined.

(* Lemma allowing replacement of a closed process equivalence with the corresponding notion of equivalence. *)
(* Normally the system oversimplifies this transformation. *)
Lemma unfoldCPEquiv : forall (P Q: ClosedProcess), P == Q <-> getProc P == getProc Q.
Proof.
  intros; simpl; reflexivity.
Qed.

(* Proofs that each of the process constructors preserves closedness. *)

Lemma OutputClosed : forall (T1 T2: Term) (P: Process) (prf1: fv P == Ø) (prf2: fvt T1 == Ø) (prf3: fvt T2 == Ø), fv (Output T1 T2 P) == Ø.
Proof.
  intros.
  unfold fv.
  rewrite prf1; rewrite prf2; rewrite prf3.
  do 2 rewrite union_empty_r.
  simpl; trivial.
Qed.

Lemma InputClosed : forall (T: Term) (x: Var) (P: Process) (prf1: fv P ∖ ❴x❵ == Ø) (prf2: fvt T == Ø), fv (Input T x P) == Ø.
Proof.
  intros.
  unfold fv.
  rewrite prf1; rewrite prf2.
  rewrite union_empty_r.
  simpl; trivial.
Qed.

Lemma CompositionClosed : forall (P Q: Process) (prf1: fv P == Ø) (prf2: fv Q == Ø), fv (Composition P Q) == Ø.
Proof.
  intros.
  unfold fv.
  rewrite prf1; rewrite prf2.
  rewrite union_empty_r.
  simpl; trivial.
Qed.

Lemma RestrictionClosed : forall (n: Name) (P: Process) (prf: fv P == Ø), fv (Restriction n P) == Ø.
Proof.
  intros.
  unfold fv; rewrite prf.
  simpl; trivial.
Qed.

Lemma MultiRestrictionClosed : forall (l: list Name) (P: Process) (prf: fv P == Ø), fv (MultiRestriction l P) == Ø.
Proof.
  intros.
  induction l; simpl in *; trivial.
Qed.

Lemma ReplicationClosed : forall (P: Process) (prf: fv P == Ø), fv (Replication P) == Ø.
Proof.
  intros.
  unfold fv.
  rewrite prf.
  simpl; trivial.
Qed.

Lemma MatchClosed : forall (T1 T2: Term) (P: Process) (prf1: fv P == Ø) (prf2: fvt T1 == Ø) (prf3: fvt T2 == Ø), fv (Match T1 T2 P) == Ø.
Proof.
  intros.
  unfold fv.
  rewrite prf1; rewrite prf2; rewrite prf3.
  do 2 rewrite union_empty_r.
  simpl; trivial.
Qed.

Lemma NilClosed : fv Nil == Ø.
Proof.
  simpl; trivial.
Qed.

Lemma SplitClosed : forall (T: Term) (x1 x2: Var) (P: Process) (prf1: (fv P ∖ ❴x1❵) ∖ ❴x2❵ == Ø) (prf2: fvt T == Ø), fv (Split T x1 x2 P) == Ø.
Proof.
  intros.
  unfold fv.
  rewrite prf1; rewrite prf2.
  rewrite union_empty_r.
  simpl; trivial.
Qed.

Lemma CaseClosed : forall (T: Term) (Q R: Process) (x: Var) (prf1: fv Q == Ø) (prf2: fv R ∖ ❴x❵ == Ø) (prf3: fvt T == Ø), fv (Case T Q x R) == Ø.
Proof.
  intros.
  unfold fv.
  rewrite prf1; rewrite prf2; rewrite prf3.
  do 2 rewrite union_empty_r.
  simpl; trivial.
  Qed.

Lemma DecryptionClosed : forall (T1 T2: Term) (x: Var) (P: Process) (prf1: fv P ∖ ❴x❵ == Ø) (prf2: fvt T1 == Ø) (prf3: fvt T2 == Ø), fv (Decryption T1 T2 x P) == Ø.
Proof.
  intros.
  unfold fv.
  rewrite prf1; rewrite prf2; rewrite prf3.
  do 2 rewrite union_empty_r.
  simpl; trivial.
Qed.

(* Sub for the only free variable in a process results in a closed process. *)
Lemma SubClosed : forall (P: Process) (T: Term) (x: Var) (p1: fv P ∖ ❴ x ❵ == Ø) (p2: fvt T == Ø), fv (Sub P T x) == Ø.
Proof.
  intros.
  antisymmetry.
  rewrite fv_Sub, p1, p2, union_idemp; reflexivity.
  unfold incl_set; intros; contradiction.
Qed.

(* Closed versions of spi calculus process constructors. *)

Definition COutput (T1 T2: ClosedTerm) (P: ClosedProcess) : ClosedProcess.
Proof.
  apply (exist _ (Output (getTerm T1) (getTerm T2) (getProc P))).
  destruct T1 as (T1 & prfT1), T2 as (T2 & prfT2), P as (P & prfP); simpl fv.
  rewrite prfT1, prfT2, prfP, 2?union_idemp; reflexivity.
Defined.

Definition CInput (T: ClosedTerm) (x: Var) (P: Process) (prf: fv P ∖ ❴x❵ == Ø) : ClosedProcess.
Proof.
  apply (exist _ (Input (getTerm T) x P)).
  destruct T as (T & prfT); simpl fv.
  rewrite prfT, prf, union_idemp; reflexivity.
Defined.

Definition CComposition (P Q: ClosedProcess) : ClosedProcess.
Proof.
  apply (exist _ (Composition (getProc P) (getProc Q))).
  destruct P as (P & prfP), Q as (Q & prfQ); simpl fv.
  rewrite prfP, prfQ, union_idemp; reflexivity.
Defined.

Definition CRestriction (n: Name) (P: ClosedProcess) : ClosedProcess.
Proof.
  apply (exist _ (Restriction n (getProc P))).
  destruct P as (P & prfP); simpl fv; assumption.
Defined.

Definition CReplication (P: ClosedProcess) : ClosedProcess.
Proof.
  apply (exist _ (Replication (getProc P))).
  destruct P as (P & prfP); simpl fv; assumption.
Defined.

Definition CMatch (T1 T2: ClosedTerm) (P: ClosedProcess) : ClosedProcess.
Proof.
  apply (exist _ (Match (getTerm T1) (getTerm T2) (getProc P))).
  destruct T1 as (T1 & prfT1), T2 as (T2 & prfT2), P as (P & prfP); simpl fv.
  rewrite prfT1, prfT2, prfP, 2?union_idemp; reflexivity.
Defined.

Definition CNil : ClosedProcess.
Proof.
  apply (exist _ Nil).
  simpl fv; reflexivity.
Defined.

Definition CSplit (T: ClosedTerm) (x1 x2: Var) (P: Process) (prf: (fv P ∖ ❴x1❵) ∖ ❴x2❵ == Ø) : ClosedProcess.
Proof.
  apply (exist _ (Split (getTerm T) x1 x2 P)).
  destruct T as (T & prfT); simpl fv.
  rewrite prfT, prf, union_idemp; reflexivity.
Defined.

Definition CCase (T: ClosedTerm) (Q: ClosedProcess) (x: Var) (R: Process) (prf: fv R ∖ ❴x❵ == Ø) : ClosedProcess.
Proof.
  apply (exist _ (Case (getTerm T) (getProc Q) x R)).
  destruct T as (T & prfT), Q as (Q & prfQ); simpl fv.
  rewrite prfT, prfQ, prf, 2?union_idemp; reflexivity.
Defined.

Definition CDecryption (T1 T2: ClosedTerm) (x: Var) (P: Process) (prf: fv P ∖ ❴x❵ == Ø) : ClosedProcess.
Proof.
  apply (exist _ (Decryption (getTerm T1) (getTerm T2) x P)).
  destruct T1 as (T1 & prfT1), T2 as (T2 & prfT2); simpl fv.
  rewrite prfT1, prfT2, prf, 2?union_idemp; reflexivity.
Defined.

Fixpoint CMultiRestriction (l: list Name) (P: ClosedProcess) : ClosedProcess :=
  match l with
    | [] => P
    | x::xs => CRestriction x (CMultiRestriction xs P)
  end.

(* Sub of a closed term into a process for its one free variable, resulting in a closed process. *)
Definition CSub (P: Process) (T: ClosedTerm) (x: Var) (p: fv P ∖ ❴ x ❵ == Ø) : ClosedProcess.
Proof.
  apply (exist _ (Sub P (getTerm T) x)).
  antisymmetry.
  destruct T as (T & prfT); simpl getTerm; rewrite fv_Sub, p, prfT, union_idemp; reflexivity.
  unfold incl_set; intros; contradiction.
Defined.

(* Renaming of a name for another name within a term, resulting in a closed term. *)
(* General list version. *)
Definition CTRename_aux (T: ClosedTerm) (l: list (Name * Name)) : ClosedTerm.
Proof.
  apply (exist _ (TRename_aux (getTerm T) l)).
  destruct T as (T & prfT); simpl fvt.
  rewrite fvt_TRename_aux; assumption.
Defined.

(* Renaming of a name for another name within a term, resulting in a closed term. *)
Definition CTRename (T: ClosedTerm) (n m: Name) : ClosedTerm.
Proof.
  apply (exist _ (TRename (getTerm T) n m)).
  destruct T as (T & prfT); simpl fvt.
  rewrite fvt_TRename; assumption.
Defined.

(* Renaming of a name for another name within a process, resulting in a closed process. *)
(* General list version. *)
Definition CRename_aux (P: ClosedProcess) (l: list (Name * Name)) : ClosedProcess.
Proof.
  apply (exist _ (Rename_aux (getProc P) l)).
  destruct P as (P & prfP); simpl fv.
  rewrite fv_Rename_aux; assumption.
Defined.

(* Renaming of a name for another name within a process, resulting in a closed process. *)
Definition CRename (P: ClosedProcess) (n m: Name) : ClosedProcess.
Proof.
  apply (exist _ (Rename (getProc P) n m)).
  destruct P as (P & prfP); simpl fv.
  rewrite fv_Rename; assumption.
Defined.

Notation "P '【' n '∕' m '】'" := (CRename P n m) (at level 90).

(* Closed process notations. *)
Notation "a '⟨' M '⟩,' P" := (COutput a M P) (at level 50).
Notation "a '﹙' x '﹚,' P" := (CInput a x P) (at level 50).
Infix "⎪" := (CComposition) (at level 50).
Notation "'new' n 'in' P" := (CRestriction n P) (at level 50).
Notation "'new' 'names' l 'in' P" := (CMultiRestriction l P) (at level 50).
Notation "! P" := (CReplication P) (at level 50).
Notation "':[' M 'is' N ']:' P" := (CMatch M N P) (at level 50).
Notation "0" := (CNil).
Notation "'Let' '(' x ',' y ')' 'be' M 'in' P" := (CSplit M x y P) (at level 50).
Notation "'Check' M 'of' 'zero:' P 'suc' x ':' Q" := (CCase M P x Q) (at level 50).
Notation "'Decrypt' M 'using' N 'into' x 'in' P" := (CDecryption M N x P) (at level 50).

(* (* Old process notations *)
Notation "a '<' M '>,' P" := (COutput a M P) (at level 50).
Notation "a ':(' x '):,' P" := (CInput a x P) (at level 50).
Infix ":|:" := (CComposition) (at level 50).
Notation "'new' n 'in' P" := (CRestriction n P) (at level 50).
Notation "'new' 'names' l 'in' P" := (CMultiRestriction l P) (at level 50).
Notation "! P" := (CReplication P) (at level 50).
Notation "':[' M 'is' N ']:' P" := (CMatch M N P) (at level 50).
Notation "0" := (CNil).
Notation "'Let' '(' x ',' y ')' 'be' M 'in' P" := (CSplit M x y P) (at level 50).
Notation "'Check' M 'for' 'zero:' P 'or' 'suc' x ':' Q" := (CCase M P x Q) (at level 50).
Notation "'Decrypt' L 'into' x 'in' P 'using' N" := (CDecryption L N x P) (at level 50). *)

(* AGENT3.3 Agent definitions. *)

Inductive Abstraction : Type := Abs : Var -> Process -> Abstraction.
Inductive Concretion : Type := Con : list Name -> Term -> Process -> Concretion.

(* Instantiates the abstraction A with the given term M at all instances of the abstraction's attached variable. *)
Definition Instantiate (F: Abstraction) (M: Term) : Process := let '(Abs x P) := F in Sub P M x.

(* Free name functions for abstractions and concretions. *)
Definition fnAbs (F: Abstraction) : FSet Name :=
  match F with
    | Abs x P => fn P
  end.
Definition fnCon (C: Concretion) : FSet Name :=
  match C with
    | Con l M P => (fnt M ∪ fn P) ∖ (fromList l)
  end.

(* Free variable functions for abstractions and concretions. *)
Definition fvAbs (F: Abstraction) : FSet Var :=
  match F with
    | Abs x P => fv P ∖ ❴x❵
  end.
Definition fvCon (C: Concretion) : FSet Var :=
  match C with
    | Con l M P => fvt M ∪ fv P
  end.

(* Definition of closed abstractions and concretions and getter functions for them. *)
Definition ClosedAbstraction := { F: Abstraction | fvAbs F == Ø }.
Definition getAbs (F: ClosedAbstraction) := proj1_sig F.

(* Closed version of an instantiation. *)
Definition CInstantiate (F: ClosedAbstraction) (M: ClosedTerm) : ClosedProcess.
Proof.
  destruct F as (F & prfF), M as (M & prfM).
  apply (exist _ (Instantiate F M)); destruct F.
  simpl fvAbs in prfF; unfold Instantiate; antisymmetry.
  rewrite fv_Sub, prfF, prfM, union_idemp; reflexivity.
  unfold incl_set; intros; contradiction.
Defined.

Definition ClosedConcretion := { C: Concretion | fvCon C == Ø }.
Definition getCon (C: ClosedConcretion) := proj1_sig C.

(* Closed versions of abstraction and concretion constructors. *)

Definition CAbs (x: Var) (P: Process) (prf: fv P ∖ ❴x❵ == Ø) : ClosedAbstraction.
Proof.
  apply (exist _ (Abs x P)).
  simpl fvAbs; rewrite prf; reflexivity.
Defined.

Definition CCon (l: list Name) (M: ClosedTerm) (P: ClosedProcess) : ClosedConcretion.
Proof.
  apply (exist _ (Con l (getTerm M) (getProc P))).
  destruct M as (M & prfM), P as (P & prfP); simpl fvCon.
  rewrite prfM, prfP, union_idemp; reflexivity.
Defined.

(* Inductive structure for a spi calculus agent. *)
Inductive Agent : Type :=
  | AAbs  : Abstraction -> Agent
  | ACon  : Concretion -> Agent
  | AProc : Process -> Agent.

(* Returns a list of all free names in A. *)
Definition fna (A: Agent) : FSet Name :=
  match A with
    | AAbs F  => fnAbs F
    | ACon C   => fnCon C
    | AProc P      => fn P
  end.

(* Returns a list of all free variables in A. *)
Fixpoint fva (A: Agent) : FSet Var :=
  match A with
    | AAbs F => fvAbs F
    | ACon C  => fvCon C
    | AProc P     => fv P
  end.

(* Definition of a closed agent and getter functions for one. *)
Definition ClosedAgent := { A: Agent | fva A == Ø }.
Definition getAgent (A: ClosedAgent) := proj1_sig A.

(* Equivalence relation on closed agents that ignores the accompanying proof. *)
Instance ClosedAgentSetoid : Setoid ClosedAgent := {|
  equiv := fun A B => getAgent A = getAgent B |}.
Proof.
  split.
  unfold Reflexive.
  intros A.
  destruct A.
  simpl.
  reflexivity.
  unfold Symmetric.
  intros A B.
  destruct A; destruct B.
  simpl; intros.
  symmetry; assumption.
  unfold Transitive.
  intros A B C.
  destruct A; destruct B; destruct C.
  simpl; intros.
  transitivity x0; assumption.
Defined.

(* Closed versions of agent constructors. *)

Definition CAAbs (F: ClosedAbstraction) : ClosedAgent.
Proof.
  apply (exist _ (AAbs (getAbs F))).
  destruct F as (F & prfF); simpl fva; assumption.
Defined.

Definition CACon (C: ClosedConcretion) : ClosedAgent.
Proof.
  apply (exist _ (ACon (getCon C))).
  destruct C as (C & prfC); simpl fva; assumption.
Defined.

Definition CAProc (P: ClosedProcess) : ClosedAgent.
Proof.
  apply (exist _ (AProc (getProc P))).
  destruct P as (P & prfP); simpl fva; assumption.
Defined.

(* The subprocess of an AProc is also closed. *)
Lemma AProc_proc_closed : forall (P: Process) (H: fva (AProc P) == Ø), fv P == Ø.
Proof.
  intros; simpl fva in H; trivial.
Qed.

(* The subprocess of an AAbs's abstraction is also closed ONLY when doing a substitution for the abstracted variable. *)
Lemma AAbs_proc_closed : forall (x: Var) (P: Process) (M: Term) (prf1: fva (AAbs (Abs x P)) == Ø) (prf2: fvt M == Ø), fv (Sub P M x) == Ø.
Proof.
  intros; simpl fva in prf1.
  antisymmetry; [rewrite fv_Sub, prf1, prf2, union_idemp; reflexivity | unfold incl_set; intros; contradiction].
Qed.

(* The subprocess of an ACon's concretion is closed. *)
Lemma ACon_proc_closed : forall (l: list Name) (M: Term) (P: Process) (prf: fva (ACon (Con l M P)) == Ø), fv P == Ø.
Proof.
  intros; simpl fva in prf; rewrite union_empty in prf; destruct prf; trivial.
Qed.

(* The renamed subprocess of an ACon's concretion is closed. *)
Lemma ACon_proc_rename_closed : forall (l: list Name) l' (M: Term) (P: Process) (prf: fva (ACon (Con l M P)) == Ø), fv (Rename_aux P l') == Ø.
Proof.
  intros; simpl fva in prf; rewrite union_empty in prf; destruct prf; rewrite fv_Rename_aux; trivial.
Qed.

(* Closed agent notations. *)
Notation "'﹙' x '﹚' P" := (CAbs x P) (at level 55).
Notation "'﹙ν' l '﹚⟨' M '⟩' P" := (CCon l M P) (at level 55).
Notation "'❴' F '❵Abs'" := (CAAbs F).
Notation "'❴' C '❵Con'" := (CACon C).
Notation "'❴' P '❵Proc'" := (CAProc P).

(* Returns the union of relations R and S. *)
Definition Union {A: Type} (R S: relation A) : relation A := fun x y => R x y \/ S x y.

(* Takes a list of process pairs and returns them in the form of a relation. *)
Fixpoint MakeRelation  (l: list (ClosedProcess * ClosedProcess)) : relation ClosedProcess :=
  match l with
    | []         => fun x y => False
    | (P, Q)::xs => Union (fun x y => x == P /\ y == Q) (MakeRelation xs)
  end.

(* Checks whether the given process is stuck at its current state. *)
Fixpoint Stuck (P: Process) : Prop := 
  match P with
    | Output t1 t2 P'       => False
    | Input t v P'          => False
    | Composition Q R       => Stuck Q /\ Stuck R
    | Restriction n P'      => False
    | Replication P'        => False
    | Match t1 t2 P'        => t1 <> t2
    | Nil                   => True
    | Split t v1 v2 P'      => match t with
                                 | Pair _ _ => False
                                 | _        => True
                               end
    | Case t Q v R          => match t with
                                 | Zero  => False
                                 | Suc _ => False
                                 | _     => True
                               end
    | Decryption t1 t2 v P' => match t1 with
                                 | Encryption M K => t2 <> K
                                 | _              => True
                               end
  end.

(*LEM4***********************************************************************LEMMAS********************************************************************************)
(* General lemmas regarding basic definitions. *)

(* Lemmas to allow reasoning akin to an inversion on these equivalent processes. *)

Lemma OutputInversion : forall M M' N N' P Q, Output M N P == Output M' N' Q -> M = M' /\ N = N' /\ P == Q.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqT_aux M M' [] [] && eqT_aux N N' [] [] && eqP_aux P Q [] []); intros; rewrite H0 in H; try contradiction.
  do 2 (apply andb_prop in H0; destruct H0).
  rewrite bool2Prop_t in H0, H2; subst.
  repeat split.
  simpl; unfold Bool.Is_true, "=p"; rewrite H1; trivial.
Qed.

Lemma InputInversion : forall M N x y P Q, Input M x P == Input N y Q -> M = N /\ eqP_aux P Q [] [(x,y)] = true.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqT_aux M N [] [] && eqP_aux P Q [] [(x,y)]); intros; rewrite H0 in H; try contradiction.
  apply andb_prop in H0; destruct H0.
  rewrite bool2Prop_t in H0; subst.
  repeat split.
  assumption.
Qed.

Lemma CompositionInversion : forall P P' Q Q', Composition P Q == Composition P' Q' -> P == P' /\ Q == Q'.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqP_aux P P' [] [] && eqP_aux Q Q' [] []); intros; rewrite H0 in H; try contradiction.
  apply andb_prop in H0; destruct H0.
  split; simpl; unfold Bool.Is_true, "=p"; [rewrite H0 | rewrite H1]; trivial.
Qed.

Lemma RestrictionInversion : forall n m P Q, Restriction n P == Restriction m Q -> eqP_aux P Q [(n,m)] [] = true.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqP_aux P Q [(n,m)] []); intros; rewrite H0 in H; try contradiction.
  trivial.
Qed.

Lemma ReplicationInversion : forall P Q, Replication P == Replication Q -> P == Q.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqP_aux P Q [] []); intros; rewrite H0 in H; try contradiction; trivial.
  simpl; unfold Bool.Is_true, "=p"; rewrite H0; trivial.
Qed.

Lemma MatchInversion : forall M M' N N' P Q, Match M N P == Match M' N' Q -> M = M' /\ N = N' /\ P == Q.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqT_aux M M' [] [] && eqT_aux N N' [] [] && eqP_aux P Q [] []); intros; rewrite H0 in H; try contradiction.
  do 2 (apply andb_prop in H0; destruct H0).
  rewrite bool2Prop_t in H0, H2; subst.
  repeat split.
  simpl; unfold Bool.Is_true, "=p"; rewrite H1; trivial.
Qed.

Lemma SplitInversion : forall M N x x' y y' P Q, Split M x y P == Split N x' y' Q -> M = N /\ eqP_aux P Q [] [(x,x');(y,y')] = true.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqT_aux M N [] [] && eqP_aux P Q [] [(x,x');(y,y')]); intros; rewrite H0 in H; try contradiction.
  apply andb_prop in H0; destruct H0.
  rewrite bool2Prop_t in H0; subst.
  repeat split.
  assumption.
Qed.

Lemma CaseInversion : forall M N x y P P' Q Q', Case M P x Q == Case N P' y Q' -> M = N /\ P == P' /\ eqP_aux Q Q' [] [(x,y)] = true.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqT_aux M N [] [] && eqP_aux P P' [] [] && eqP_aux Q Q' [] [(x,y)]); intros; rewrite H0 in H; try contradiction.
  do 2 (apply andb_prop in H0; destruct H0).
  rewrite bool2Prop_t in H0; subst.
  repeat split.
  simpl; unfold Bool.Is_true, "=p"; rewrite H2; trivial.
  assumption.
Qed.

Lemma DecryptionInversion : forall M M' N N' x y P Q, Decryption M N x P == Decryption M' N' y Q -> M = M' /\ N = N' /\ eqP_aux P Q [] [(x,y)] = true.
Proof.
  intros.
  simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H.
  case_eq (eqT_aux M M' [] [] && eqT_aux N N' [] [] && eqP_aux P Q [] [(x,y)]); intros; rewrite H0 in H; try contradiction.
  do 2 (apply andb_prop in H0; destruct H0).
  rewrite bool2Prop_t in H0, H2; subst.
  repeat split.
  assumption.
Qed.

(* A multirestriction can be ignored when considering free variables. *)
Lemma fv_multirestrict_drop : forall P l, fv (MultiRestriction l P) == fv P.
Proof.
  intros.
  induction l.
  unfold MultiRestriction.
  simpl; trivial.
  unfold MultiRestriction in *.
  rewrite IHl.
  simpl; trivial.
Qed.

(* A closed multirestriction simplifies to an unclosed internal multirestriction. *)
Lemma multires_getProc_simpl : forall l p, getProc (CMultiRestriction l p) = MultiRestriction l (getProc p).
Proof.
  intros.
  induction l; simpl.
  trivial.
  rewrite IHl.
  reflexivity.
Qed.

(* If a pair splitting process is closed, substituting the left and right elements for x and y in the subprocess results in a closed process. *)
Lemma LetSubClosed : forall (P: Process) (M N: Term) x y (H: fv (Split (Pair M N) x y P) == Ø), fv (Sub (Sub P M x) N y) == Ø.
Proof.
  intros.
  simpl fv in H.
  rewrite union_empty in H; destruct H.
  rewrite union_empty in H; destruct H.
  antisymmetry.
  rewrite 2?fv_Sub, H, H1, 2?union_empty_r, H0; reflexivity.
  unfold incl_set; intros; contradiction.
Qed.

(* If the terms and subprocess are closed, a case matching to a successor is closed. *)
Lemma CaseSucClosed : forall (M: Term) (P Q: Process) (x: Var) (prf1: fv P == Ø) (prf2: fv Q ∖ ❴ x ❵ == Ø) (prf3: fvt M == Ø), fv (Case (Suc M) P x Q) == Ø.
Proof.
  intros.
  simpl fv.
  rewrite prf1; rewrite prf2; rewrite prf3.
  simpl; trivial.
Qed.

(* If a case matching successor process is closed, substituting the subterm for x in the subprocess results in a closed process. *)
Lemma CaseSucSubClosed : forall (M: Term) (P Q: Process) (x: Var) (H: fv (Case (Suc M) P x Q) == Ø), fv (Sub Q M x) == Ø.
Proof.
  intros.
  simpl fv in H.
  rewrite union_empty in H; destruct H.
  rewrite union_empty in H; destruct H.
  antisymmetry.
  rewrite fv_Sub, H, H0, union_idemp; reflexivity.
  unfold incl_set; intros; contradiction.
Qed.

(* If the terms and subprocess are closed and the keys match, a decryption is closed. *)
Lemma DecryptionValidClosed : forall (M N: Term) (x: Var) (P: Process) (prf1: fv P ∖ ❴ x ❵ == Ø) (prf2: fvt M == Ø) (prf3: fvt N == Ø), fv (Decryption (Encryption M N) N x P) == Ø.
Proof.
  intros.
  simpl fv.
  rewrite prf1; rewrite prf2; rewrite prf3.
  simpl; trivial.
Qed.

(* If a decryption process is closed and the keys match, substituting the decrypted term for x in the subprocess results in a closed process. *)
Lemma DecryptionSubClosed : forall (P: Process) (M N: Term) (x: Var) (H: fv (Decryption (Encryption M N) N x P) == Ø), fv (Sub P M x) == Ø.
Proof.
  intros.
  simpl fv in H.
  rewrite union_empty in H; destruct H.
  rewrite union_empty in H; destruct H.
  rewrite union_empty in H; destruct H.
  antisymmetry.
  rewrite fv_Sub, H, union_empty_r, H0; reflexivity.
  unfold incl_set; intros; contradiction.
Qed.

(* The process structure necessary for ReactInter is closed if its parts are all closed. *)
Lemma ReactInterClosed : forall P Q m N x (p1: fv P == Ø) (p2: fv Q ∖ ❴ x ❵ == Ø) (p3: fvt N == Ø), fv (Composition (Output (TName m) N P) (Input (TName m) x Q)) == Ø.
Proof.
  intros.
  simpl fv.
  rewrite p1; rewrite p2; rewrite p3.
  simpl; trivial.
Qed.

(* If a process capable of applying ReactInter is closed, the result of the ReactInter is also closed. *)
Lemma ReactInterSubClosed:
  forall P Q m N x (H: fv (Composition (Output (TName m) N P) (Input (TName m) x Q)) == Ø), fv (Composition P (Sub Q N x)) == Ø.
Proof.
  intros.
  simpl fv in *.
  rewrite union_empty in H; destruct H.
  rewrite union_empty in H; destruct H.
  rewrite union_empty_l in H, H0.
  rewrite H1, union_empty_l.
  antisymmetry.
  rewrite fv_Sub, H, union_empty_r, H0; reflexivity.
  unfold incl_set; intros; contradiction.
Qed.

(*RULE5**********************************************************************RULES*********************************************************************************)
(* Implementation of spi calculus rules. *)

(* Reduction rules *)
Inductive Reduction : ClosedProcess -> ClosedProcess -> Prop :=
  | RedRepl     : forall P Q R, Q == CReplication P -> R == CComposition P (CReplication P) -> Reduction Q R
  | RedMatch    : forall P M Q R, Q == CMatch M M P -> R == P -> Reduction Q R
  | RedLet      : forall P M N x y prf Q R, Q == CSplit (CPair M N) x y P prf -> R == exist _ (Sub (Sub P (getTerm M) x) (getTerm N) y) (LetSubClosed _ _ _ _ _ (SplitClosed _ _ _ _ prf (PairClosed _ _ (getProof M) (getProof N)))) -> Reduction Q R
  | RedZero     : forall P Q x prf R S, R == CCase CZero P Q x prf -> S == P -> Reduction R S
  | RedSuc      : forall P Q M x prf R S, R == CCase (CSuc M) P x Q prf -> S == exist _ (Sub Q (getTerm M) x) (CaseSucSubClosed _ _ _ _ (CaseSucClosed (getTerm M) (getProc P) Q x (getProof P) prf (getProof M))) -> Reduction R S
  | RedDecrypt  : forall P M N x prf Q R, Q == CDecryption (CEncryption M N) N x P prf -> R == exist _ (Sub P (getTerm M) x) (DecryptionSubClosed _ _ _ _ (DecryptionValidClosed _ _ _ _ prf (getProof M) (getProof N))) -> Reduction Q R.

(* Reduction respects process equivalence. *)
Lemma RedProper : forall P Q R S, R == P -> S == Q -> Reduction P Q -> Reduction R S.
Proof.
  intros.
  induction H1.
  apply (RedRepl P); [rewrite H | rewrite H0]; assumption.
  apply (RedMatch P M); [rewrite H | rewrite H0]; assumption.
  apply (RedLet P M N x y prf); [rewrite H | rewrite H0]; assumption.
  apply (RedZero P Q x prf); [rewrite H | rewrite H0]; assumption.
  apply (RedSuc P Q M x prf); [rewrite H | rewrite H0]; assumption.
  apply (RedDecrypt P M N x prf); [rewrite H | rewrite H0]; assumption.
Qed.

(* Structural equivalence rules *)
Inductive Structural : ClosedProcess -> ClosedProcess -> Prop :=
  | StructNil       : forall P Q R, Q == CComposition P CNil -> R == P -> Structural Q R
  | StructComm      : forall P Q R S, R == CComposition P Q -> S == CComposition Q P -> Structural R S
  | StructAssoc     : forall P Q R S T, S == CComposition P (CComposition Q R) -> T == CComposition (CComposition P Q) R -> Structural S T
  | StructSwitch    : forall P m n Q R, Q == CRestriction m (CRestriction n P) -> R == CRestriction n (CRestriction m P) -> Structural Q R
  | StructDrop      : forall n P Q, P == CRestriction n CNil -> Q == CNil -> Structural P Q
  | StructExtrusion : forall P Q n R S, R == CRestriction n (CComposition P Q) -> S == CComposition P (CRestriction n Q) -> ~ elem_set n (fn (getProc P)) -> Structural R S
  | StructRed       : forall P Q R S, R == P -> S == Q -> Reduction P Q -> Structural R S
  | StructRefl      : forall P P' Q R, Q == P -> R == P' -> P == P' -> Structural Q R
  | StructSymm      : forall P Q R S, R == Q -> S == P -> Structural P Q -> Structural R S
  | StructTrans     : forall P Q R S T, S == P -> T == R -> Structural P Q -> Structural Q R -> Structural S T
  | StructPar       : forall P P' Q R S, R == CComposition P Q -> S == CComposition P' Q -> Structural P P' -> Structural R S
  | StructRes       : forall P P' m Q R, Q == CRestriction m P -> R == CRestriction m P' -> Structural P P' -> Structural Q R.

(* Structural equivalence respects process equivalence. *)
Lemma StructProper : forall P Q R S, R == P -> S == Q -> Structural P Q -> Structural R S.
Proof.
  intros.
  induction H1.
  apply (StructNil P); [rewrite H | rewrite H0]; assumption.
  apply (StructComm P Q); [rewrite H | rewrite H0]; assumption.
  apply (StructAssoc P Q R0); [rewrite H | rewrite H0]; assumption.
  apply (StructSwitch P m n); [rewrite H | rewrite H0]; assumption.
  apply (StructDrop n); [rewrite H | rewrite H0]; assumption.
  apply (StructExtrusion P Q n); [ rewrite H | rewrite H0 | ]; assumption.
  apply (StructRed P Q); [rewrite H | rewrite H0 | ]; assumption.
  apply (StructRefl P P'); [rewrite H | rewrite H0 | ]; assumption.
  apply (StructSymm P Q); [rewrite H | rewrite H0 | ]; assumption.
  apply (StructTrans P Q R0); [rewrite H | rewrite H0 | | ]; assumption.
  apply (StructPar P P' Q); [rewrite H | rewrite H0 | ]; assumption.
  apply (StructRes P P' m); [rewrite H | rewrite H0 | ]; assumption.
Qed.

(* Reaction rules. *)
Inductive Reaction : ClosedProcess -> ClosedProcess -> Prop :=
  | ReactInter  : forall P Q m N x prf R S, R == CComposition (COutput (CTName m) N P) (CInput (CTName m) x Q prf) -> S == exist _ (Composition (getProc P) (Sub Q (getTerm N) x)) (ReactInterSubClosed _ _ _ _ _ (ReactInterClosed _ _ m _ _ (getProof P) prf (getProof N))) -> Reaction R S
  | ReactStruct : forall P P' Q Q' R S, R == P -> S == Q -> Structural P P' -> Reaction P' Q' -> Structural Q' Q -> Reaction R S
  | ReactPar    : forall P P' Q R S, R == CComposition P Q -> S == CComposition P' Q -> Reaction P P' -> Reaction R S
  | ReactRes    : forall P P' n Q R, Q == CRestriction n P -> R == CRestriction n P' -> Reaction P P' -> Reaction Q R.

(* Reaction respects process equivalence. *)
Lemma ReactProper : forall P Q R S, R == P -> S == Q -> Reaction P Q -> Reaction R S.
Proof.
  intros.
  induction H1.
  apply (ReactInter P Q m N x prf); [rewrite H | rewrite H0]; assumption.
  apply (ReactStruct P P' Q Q'); [rewrite H | rewrite H0 | | | ]; assumption.
  apply (ReactPar P P' Q); [rewrite H | rewrite H0 | ]; assumption.
  apply (ReactRes P P' n); [rewrite H | rewrite H0 | ]; assumption.
Qed.

(* Barb rules. *)
Inductive Barb : ClosedProcess -> Name -> Prop :=
  | BarbIn      : forall P m x prf Q, Q == CInput (CTName m) x P prf -> Barb Q m
  | BarbOut     : forall P m M Q, Q == COutput (CTName m) M P -> Barb Q m
  | BarbPar     : forall P Q β R, R == CComposition P Q -> Barb P β -> Barb R β
  | BarbRes     : forall P β m Q, β <> m -> Q == CRestriction m P -> Barb P β -> Barb Q β
  | BarbStruct  : forall P Q β R, R == P -> Structural P Q -> Barb Q β -> Barb R β.

(* Barb respects process equivalence. *)
Lemma BarbProper' : forall P β Q, Q == P -> Barb P β -> Barb Q β.
Proof.
  intros.
  induction H0.
  apply (BarbIn P m x prf); rewrite H; assumption.
  apply (BarbOut P m M); rewrite H; assumption.
  apply (BarbPar P Q0 β); [rewrite H | ]; assumption.
  apply (BarbRes P β m); [ | rewrite H | ]; assumption.
  apply (BarbStruct P Q0 β); [rewrite H | | ]; assumption.
Qed.

(* Basic barb that avoids direct use of BarbStruct. *)
Inductive BBarb : Process -> Name -> Prop :=
  | BBarbIn      : forall P m x, BBarb (Input (TName m) x P) m
  | BBarbOut     : forall P m M, BBarb (Output (TName m) M P) m
  | BBarbParL    : forall P Q β, BBarb P β -> BBarb (Composition P Q) β
  | BBarbParR    : forall P Q β, BBarb Q β -> BBarb (Composition P Q) β
  | BBarbRes     : forall P β m, β <> m -> BBarb P β -> BBarb (Restriction m P) β
  | BBarbRepl    : forall P β, BBarb P β -> BBarb (Replication P) β
  | BBarbMatch   : forall P β M, BBarb P β -> BBarb (Match M M P) β
  | BBarbLet     : forall P β M N x y, BBarb (Sub (Sub P M x) N y) β -> BBarb (Split (Pair M N) x y P) β
  | BBarbZero    : forall P Q β x, BBarb P β -> BBarb (Case Zero P x Q) β
  | BBarbSuc     : forall P Q β M x, BBarb (Sub Q M x) β -> BBarb (Case (Suc M) P x Q) β
  | BBarbDecrypt : forall P β M N x, BBarb (Sub P M x) β -> BBarb (Decryption (Encryption M N) N x P) β.

(* Basic barb including BarbStruct. *)
Inductive Barb' : ClosedProcess -> Name -> Prop :=
  | BarbStruct'  : forall P Q β, Structural P Q -> BBarb (getProc Q) β -> Barb' P β.

(* Convergence rules. *)
Inductive Convergence : ClosedProcess -> Name -> Prop :=
  | ConvBarb  : forall P β Q, Q == P -> Barb P β -> Convergence Q β
  | ConvReact : forall P Q β R, R == P -> Reaction P Q -> Convergence Q β -> Convergence R β.

(* Convergence respects process equivalence. *)
Lemma ConvProper : forall P Q β, Q == P -> Convergence P β -> Convergence Q β.
Proof.
  intros.
  induction H0.
  apply (ConvBarb P β); [rewrite H | ]; assumption.
  apply (ConvReact P Q0 β); [rewrite H | | ]; assumption.
Qed.

Infix ">" := (Reduction).
Infix "≡" := (Structural) (at level 55).
Infix "--->" := (Reaction) (at level 55).
Infix "~>" := (Barb) (at level 55).
Infix "~~>" := (Convergence) (at level 55).

Infix "--->*" := (rtc Reaction) (at level 55).

(* Agent semantics *)

(* Restriction of an agent. *)
(* Side condition from paper: for concretions, m should not be in n *)
(* Side condition is ignored because restricting a name twice doesn't matter. *)
Definition ARestriction (m: Name) (A: Agent) : Agent :=
  match A with
    | AAbs (Abs x P)  => AAbs (Abs x (Restriction m P))
    | ACon (Con n M P) => ACon (Con (if elem m (fnt M) then n ++ [m] else n) M (if elem m (fnt M) then P else Restriction m P))
    | AProc P              => AProc (Restriction m P)
  end.

(* Closed version of ARestriction. *)
Definition CARestriction (n: Name) (A: ClosedAgent) : ClosedAgent.
Proof.
  apply (exist _ (ARestriction n (getAgent A))).
  destruct A as (A & prfA); simpl fva.
  destruct A; [destruct a | destruct c | ]; simpl fva in *.
  trivial.
  destruct (elem n (fnt t)); simpl fv; trivial.
  trivial.
Defined.

(* Side conditions for agent composition: *)
(* Abstraction: ~In x (fv R) *)
(* Handled by replacing all instances of x with a new variable not present in the free variables of P and R. *)
(* Concretion: n ∩ fn R is empty set *)
(* Handled by renaming all names bound by n with a new name not present in the free names of P and R. *)

(* Composition of an agent with a process from the right. *)
Definition ACompositionR (A: Agent) (R: Process) : Agent :=
  match A with
    | AAbs (Abs x P)   => let x' := newVar x (proj1_sig (fv P ∪ fv R)) in
        if elem x (fv R) then AAbs (Abs x' (Composition (Sub P (TVar x') x) R)) else AAbs (Abs x (Composition P R))
    | ACon (Con n M P) => let n' := newVars (proj1_sig ((fromList n) ∩ fn R)) (proj1_sig (fnt M ∪ fn P ∪ fn R)) in
        ACon (Con (replace n n') (TRename_aux M n') (Composition (Rename_aux P n') R))
    | AProc P          => AProc (Composition P R)
  end.

(* Composition of an agent with a process from the left. *)
Definition ACompositionL (R: Process) (A: Agent) : Agent :=
  match A with
    | AAbs (Abs x P)   => let x' := newVar x (proj1_sig (fv P ∪ fv R)) in
        if elem x (fv R) then AAbs (Abs x' (Composition R (Sub P (TVar x') x))) else AAbs (Abs x (Composition R P))
    | ACon (Con n M P) => let n' := newVars (proj1_sig ((fromList n) ∩ fn R)) (proj1_sig (fnt M ∪ fn P ∪ fn R)) in
        ACon (Con (replace n n') (TRename_aux M n') (Composition R (Rename_aux P n')))
    | AProc P          => AProc (Composition R P)
  end.

(* Closed version of ACompositionR. *)
Definition CACompositionR (A: ClosedAgent) (R: ClosedProcess) : ClosedAgent.
Proof.
  apply (exist _ (ACompositionR (getAgent A) (getProc R))).
  destruct A as (A & prfA), R as (R & prfR); simpl fva.
  destruct A; [destruct a | destruct c | ]; simpl fva in *.
  destruct (elem v (fv R)); simpl fva.
  apply (newVar_proc_closed _ _ (newVar v (ListSet.set_union string_dec (proj1_sig (fv p)) (proj1_sig (fv R))))) in prfA.
  rewrite diff_union_l, union_empty; split.
  rewrite prfA; simpl; trivial.
  rewrite prfR at 1; rewrite diff_empty_l; simpl; trivial.
  rewrite prfR, union_empty_r, prfA; reflexivity.
  rewrite union_empty in prfA; destruct prfA.
  rewrite fvt_TRename_aux, fv_Rename_aux, H, H0, prfR; simpl; trivial.
  rewrite union_empty; split; trivial.
Defined.

(* Closed version of ACompositionL. *)
Definition CACompositionL (R: ClosedProcess) (A: ClosedAgent) : ClosedAgent.
Proof.
  apply (exist _ (ACompositionL (getProc R) (getAgent A))).
  destruct A as (A & prfA), R as (R & prfR); simpl fva.
  destruct A; [destruct a | destruct c | ]; simpl fva in *.
  destruct (elem v (fv R)); simpl fva.
  apply (newVar_proc_closed _ _ (newVar v (ListSet.set_union string_dec (proj1_sig (fv p)) (proj1_sig (fv R))))) in prfA.
  rewrite diff_union_l.
  rewrite prfA; rewrite prfR at 1; rewrite diff_empty_l; simpl; trivial.
  rewrite prfR, union_empty_l, prfA; reflexivity.
  rewrite union_empty in prfA; destruct prfA.
  rewrite fvt_TRename_aux, fv_Rename_aux, H, H0, prfR; simpl; trivial.
  rewrite union_empty; split; trivial.
Defined.

(* Interaction side condition: n intersect (fn P) = empty set *)
(* The side condition is always met by renaming the bound names of the concretion to not conflict with fn P. *)

(* Interaction of an abstraction and a concretion. *)
Definition InteractionL (F: Abstraction) (C: Concretion) : Process := let '(Abs x P) := F in let '(Con n M Q) := C in
  MultiRestriction (replace n (newVars (proj1_sig ((fromList n) ∩ fn P)) (proj1_sig (fn P))))
    (Composition (Sub P M x) (Rename_aux Q (newVars (proj1_sig ((fromList n) ∩ fn P)) (proj1_sig (fn P))))).

(* Interaction of a concretion and an abstraction. *)
Definition InteractionR (C: Concretion) (F: Abstraction) : Process := let '(Con n M Q) := C in let '(Abs x P) := F in
  MultiRestriction (replace n (newVars (proj1_sig ((fromList n) ∩ fn P)) (proj1_sig (fn P))))
    (Composition (Rename_aux Q (newVars (proj1_sig ((fromList n) ∩ fn P)) (proj1_sig (fn P)))) (Sub P M x)).

(* Closed versions of interaction. *)

Definition CInteractionL (F: ClosedAbstraction) (C: ClosedConcretion) : ClosedProcess.
Proof.
  apply (exist _ (InteractionL (getAbs F) (getCon C))).
  destruct F as (F & prfF), C as (C & prfC), F, C; simpl fv.
  simpl fvAbs in prfF; simpl fvCon in prfC; simpl fv.
  rewrite fv_multirestrict_drop; simpl fv.
  rewrite union_empty in prfC; destruct prfC.
  antisymmetry.
  rewrite fv_Sub, fv_Rename_aux, prfF, H, H0, 2?union_idemp; reflexivity.
  unfold incl_set; intros; contradiction.
Defined.

Definition CInteractionR (C: ClosedConcretion) (F: ClosedAbstraction) : ClosedProcess.
Proof.
  apply (exist _ (InteractionR (getCon C) (getAbs F))).
  destruct F as (F & prfF), C as (C & prfC), F, C; simpl fv.
  simpl fvCon in prfC; simpl fvAbs in prfF; simpl fv.
  rewrite fv_multirestrict_drop; simpl fv.
  rewrite union_empty in prfC; destruct prfC.
  antisymmetry.
  rewrite fv_Sub, fv_Rename_aux, prfF, H, H0, 2?union_idemp; reflexivity.
  unfold incl_set; intros; contradiction.
Defined.

(* Closed agent operation notations. *)
Infix "⎪L" := (CACompositionL) (at level 55).
Infix "⎪R" := (CACompositionR) (at level 55).
Notation "'ARes' n 'in' A" := (CARestriction n A) (at level 55).
Notation "F '@L' C" := (CInteractionL F C) (at level 55).
Notation "C '@R' F" := (CInteractionR C F) (at level 55).

(* Commitment rules *)
Inductive Commitment : ClosedProcess -> ClosedAgent -> Action -> Prop :=
  | CommIn     : forall P m x prf Q A, Q == CInput (CTName m) x P prf -> A == CAAbs (CAbs x P prf) -> Commitment Q A (ActName m)
  | CommOut    : forall P M m Q A, Q == COutput (CTName m) M P -> A == CACon (CCon [] M P) -> Commitment Q A (ActName m)
  | CommInter1 : forall P Q m F C R A,
                  R == CComposition P Q -> A == CAProc (CInteractionL F C) -> Commitment P (CAAbs F) (ActName m) -> Commitment Q (CACon C) (ActName m) -> Commitment R A τ
  | CommInter2 : forall P Q m C F R A,
                  R == CComposition P Q -> A == CAProc (CInteractionR C F) -> Commitment P (CACon C) (ActName m) -> Commitment Q (CAAbs F) (ActName m) -> Commitment R A τ
  | CommPar1   : forall P Q A α R B, R == CComposition P Q -> B == CACompositionR A Q -> Commitment P A α -> Commitment R B α
  | CommPar2   : forall P Q A α R B, R == CComposition P Q -> B == CACompositionL P A -> Commitment Q A α -> Commitment R B α
  | CommRes    : forall P A α m Q B, Q == CRestriction m P -> B == CARestriction m A -> Commitment P A α -> α <> (ActName m) -> Commitment Q B α
  | CommRed    : forall P Q A α R B, R == P -> B == A -> Reduction P Q -> Commitment Q A α -> Commitment R B α.

(* Commitment respects process equivalence. *)
Lemma CommProper : forall P A Q B a, Q == P -> B == A -> Commitment P A a -> Commitment Q B a.
Proof.
  intros.
  induction H1.
  apply (CommIn P m x prf); [rewrite H | rewrite H0]; assumption.
  apply (CommOut P M m); [rewrite H | rewrite H0]; assumption.
  apply (CommInter1 P Q0 m F C); [rewrite H | rewrite H0 | | ]; assumption.
  apply (CommInter2 P Q0 m C F); [rewrite H | rewrite H0 | | ]; assumption.
  apply (CommPar1 P Q0 A _); [rewrite H | rewrite H0 | ]; assumption.
  apply (CommPar2 P Q0 A _); [rewrite H | rewrite H0 | ]; assumption.
  apply (CommRes P A _ m); [rewrite H | rewrite H0 | | ]; assumption.
  apply (CommRed P Q0 A _); [rewrite H | rewrite H0 | | ]; assumption.
Qed.

Definition Comm_tau (P Q: ClosedProcess) : Prop := Commitment P (CAProc Q) τ.

Notation "P '--->' A 'via' c" := (Commitment P A c) (at level 55).
Infix "--->τ" := (Comm_tau) (at level 55).
Infix "--->τ*" := (rtc Comm_tau) (at level 55).

Ltac spitrivial := try (simpl; trivial; unfold Bool.Is_true, "=p"; rewrite eqP_aux_refl; try contradiction; trivial).

(* End of semantics *)

(*EQUIV6***********************************************************************EQUIVALENCES***************************************************************************)
(* Definitions on equivalences in the calculus. *)

(* Testing equivalence definitions. *)

(* A test (R, β) takes a process as a parameter and returns as true if the process can communicate immediately on channel β while in parallel with R. *)
Definition Test (R: ClosedProcess) (β: Name) : ClosedProcess -> Prop := fun P => Convergence (CComposition P R) β.

(* Unidirectional version of testing equivalence. *)
Definition TestingPreorder (P Q: ClosedProcess) : Prop := forall R β, (Test R β) P -> (Test R β) Q.

(* Main notion of spi calculus process equivalence. *)
Definition TestingEquivalence (P Q: ClosedProcess): Prop := (TestingPreorder P Q) /\ (TestingPreorder Q P).

(* Returns a list of pairs of names between two terms that should be the same. *)
(* Returns None if they are not the same structure. *)
Fixpoint term_names (M N: Term) : option (list (Name * Name)) :=
  match M, N with
    | TName m, TName n                 => Some [(m,n)]
    | Pair M N, Pair M' N'             => match term_names M M', term_names N N' with
                                            | None, _          => None
                                            | _, None          => None
                                            | Some l1, Some l2 => Some (l1 ++ l2)
                                          end
    | Zero, Zero                       => Some []
    | Suc M, Suc N                     => term_names M N
    | TVar x, TVar y                   => Some []
    | Encryption M N, Encryption M' N' => match term_names M M', term_names N N' with
                                            | None, _          => None
                                            | _, None          => None
                                            | Some l1, Some l2 => Some (l1 ++ l2)
                                          end
    | _, _                             => None
  end.

(* Notes on ARelation: *)
(* We need to consider the possibility that the agents are equivalent up to renaming of bound identifiers. *)
(* To do this, we get all the identifiers from the terms that should be equal and replace the names in one list. *)
(* Now the lists should be permutations of each other if they are related. *)
(* Should we be affecting the process in the same manner or just allowing the relation to perform the check on the *)
(* original processes? *)

(* Converts a relation on closed processes into a relation on closed agents. *)
Definition ARelation (R: relation ClosedProcess) : relation ClosedAgent := fun X Y => 
  match X, Y with
    | exist _ (AAbs (Abs x P)) prf1, exist _ (AAbs (Abs y Q)) prf2 =>
        forall (M: ClosedTerm),
          R (exist _ (Sub P (getTerm M) x) (AAbs_proc_closed x P (getTerm M) prf1 (getProof M)))
            (exist _ (Sub Q (getTerm M) y) (AAbs_proc_closed y Q (getTerm M) prf2 (getProof M)))
    | exist _ (ACon (Con n M P)) prf1, exist _ (ACon (Con m N Q)) prf2 =>
        match term_names M N with
          | Some l => Permutation (replace n l) m /\
                      R (exist _ (Rename_aux P l) (ACon_proc_rename_closed n l M P prf1))
                        (exist _ Q (ACon_proc_closed m N Q prf2))
          | None   => False
        end
    | exist _ (AProc P) prf1, exist _ (AProc Q) prf2 => R (exist _ P (AProc_proc_closed P prf1))
                                                          (exist _ Q (AProc_proc_closed Q prf2))
    | _,_ => False
  end.

(* Predicate indicating whether R is a simulation relation. *)
Definition Simulation (R: relation ClosedProcess) : Prop :=
  forall (P Q: ClosedProcess) (A: ClosedAgent) (α: Action), R P Q -> Commitment P A α -> exists B, (Commitment Q B α /\ ARelation R A B).

(* Predicate indicating whether R is a bisimulation relation. *)
Definition StrongBisimulation (R: relation ClosedProcess) : Prop := Simulation R /\ Simulation (Converse R).

(* Relation indicating that a strong bisimulation exists that relates P and Q. *)
Definition StrongBisimilarity (P Q: ClosedProcess) : Prop := exists R, StrongBisimulation R /\ R P Q.

(* 'Up to' relation, denoting that two elements x and y are related by R if they are both related to other elements 
    x' and y' respectively by S, and x' and y' are related by R. *)
Definition UpTo {A: Type} (R S: relation A) (x y: A) : Prop := exists (x' y': A), R x' y' /\ S x x' /\ S y y'.

(* Predicate indicating whether R is a barbed simulation relation. *)
Definition BarbedSimulation (R: relation ClosedProcess) : Prop :=
  forall (P Q: ClosedProcess), R P Q -> (forall β, Barb P β -> Barb Q β) /\ (forall P', Reaction P P' -> (exists Q', Reaction Q Q' /\ UpTo R Structural P' Q')).

(* Predicate indicating whether R is a barbed bisimulation relation. *)
Definition BarbedBisimulation (R: relation ClosedProcess) : Prop := BarbedSimulation R /\ BarbedSimulation (Converse R).

(* Relation indicating that a barbed bisimulation exists that relates P and Q. *)
Definition BarbedEquivalence (P Q: ClosedProcess) : Prop := exists R, BarbedBisimulation R /\ R P Q.

(* Definitions relating to barbed equivalence. *)

Definition BarbedSimulationUpToBarbedEquivalence (R: relation ClosedProcess) : Prop :=
  forall (P Q: ClosedProcess), R P Q -> (forall β, Barb P β -> Barb Q β) /\ (forall P', Reaction P P' -> (exists Q', Reaction Q Q' /\ UpTo R BarbedEquivalence P' Q')).

Definition BarbedBisimulationUpToBarbedEquivalence (R: relation ClosedProcess) : Prop :=
  BarbedSimulationUpToBarbedEquivalence R /\ BarbedSimulationUpToBarbedEquivalence (Converse R).

Definition UpToWithRestriction (R S: relation ClosedProcess) (P Q: ClosedProcess) : Prop :=
  exists P' Q' (nl: list Name), R P' Q' /\ S P (CMultiRestriction nl P') /\ S Q (CMultiRestriction nl Q').

Definition BarbedSimulationUpToBarbedEquivalenceAndRestriction (R: relation ClosedProcess) : Prop :=
  forall (P Q: ClosedProcess), R P Q -> (forall β, Barb P β -> Barb Q β) /\
    (forall P', Reaction P P' -> (exists Q', Reaction Q Q' /\ UpToWithRestriction R BarbedEquivalence P' Q')).

Definition BarbedBisimulationUpToBarbedEquivalenceAndRestriction (R: relation ClosedProcess) : Prop :=
  BarbedSimulationUpToBarbedEquivalenceAndRestriction R /\ BarbedSimulationUpToBarbedEquivalenceAndRestriction (Converse R).

(* Relation that checks barbed equivalence of two processes in parallel with a common third process. *)
Definition BarbedCongruence (P Q: ClosedProcess) : Prop := forall R, BarbedEquivalence (CComposition P R) (CComposition Q R).

(* Infix "[=" := (TestingPreorder) (at level 55). TODO Using this notation is visually weird (square bracket is the issue), may need a different character. *)
Infix "~=" := (TestingEquivalence) (at level 70).
(* Notation "'{{' R A B '}}'" := (ARelation R A B) (at level 0). *)
Infix "~s" := (StrongBisimilarity) (at level 55).
Notation "R x y 'upto' S" := (UpTo R S x y) (at level 55).
Infix "~•" := (BarbedEquivalence) (at level 55).
Infix "~" := (BarbedCongruence) (at level 55).

(*MORPH7**********************************************************************MORPHISMS*******************************************************************************)
(* Proofs for allowing rewriting of certain relations in the calculus, as well as proofs that some relations are equivalences. *)

(* Closed term constructor instances. *)

Instance CPairProper : Proper (equiv ==> equiv ==> equiv) CPair.
Proof.
  unfold Proper, "==>".
  intros M M' H N N' H0.
  destruct M, M', N, N'; simpl in *; subst; trivial.
Qed.

Instance CSucProper : Proper (equiv ==> equiv) CSuc.
Proof.
  unfold Proper, "==>".
  intros M N H.
  destruct M, N; simpl in *; subst; trivial.
Qed.

Instance CEncryptionProper : Proper (equiv ==> equiv ==> equiv) CEncryption.
Proof.
  unfold Proper, "==>".
  intros M M' H N N' H0.
  destruct M, M', N, N'; simpl in *; subst; trivial.
Qed.

(* Closed process constructor instances. *)
(* Due to the nature of closed process constructors with bound variables, we cannot prove instances of Proper. *)
(* We instead prove equivalent lemmas that can be used in place of rewrite. *)

Instance COutputProper : Proper (equiv ==> equiv ==> equiv ==> equiv) COutput.
Proof.
  unfold Proper, "==>".
  intros M M' H N N' H0 P P' H1.
  destruct M, M', N, N', P, P'.
  simpl in H, H0, H1; simpl; subst.
  unfold Bool.Is_true, "=p" in H1.
  unfold Bool.Is_true, "=p"; simpl.
  rewrite 2?eqT_aux_refl; try contradiction; simpl.
  assumption.
Qed.

Lemma CInputProper : forall M N x P Q (prfP : fv P ∖ ❴x❵ == Ø) (prfQ : fv Q ∖ ❴x❵ == Ø), M == N -> P == Q -> CInput M x P prfP == CInput N x Q prfQ.
Proof.
  intros.
  simpl; rewrite H.
  simpl in H0; unfold Bool.Is_true, "=p" in H0.
  unfold Bool.Is_true, "=p"; simpl.
  rewrite eqT_aux_refl; try contradiction; simpl.
  case_eq (eqP_aux P Q [] []); intros; rewrite H1 in H0; try contradiction.
  apply (eqP_aux_add_v _ _ x) in H1; simpl in H1; rewrite H1; trivial.
Qed.

Instance CCompositionProper : Proper (equiv ==> equiv ==> equiv) CComposition.
Proof.
  unfold Proper, "==>".
  intros P Q H P' Q' H0.
  destruct P, P', Q, Q'.
  simpl in H, H0; simpl.
  unfold Bool.Is_true, "=p" in H, H0.
  unfold Bool.Is_true, "=p"; simpl.
  destruct (eqP_aux x x1 [] []); try contradiction.
  destruct (eqP_aux x0 x2 [] []); try contradiction.
  trivial.
Qed.

Instance CRestrictionProper : Proper (eq ==> equiv ==> equiv) CRestriction.
Proof.
  unfold Proper, "==>".
  intros n m H P Q H0.
  destruct P, Q.
  simpl in H0; simpl; subst.
  unfold Bool.Is_true, "=p" in H0.
  unfold Bool.Is_true, "=p"; simpl.
  case_eq (eqP_aux x x0 [] []); intros; rewrite H in H0; try contradiction.
  apply (eqP_aux_add_n _ _ m) in H; simpl in H; rewrite H; trivial.
Qed.

Instance CMultiRestrictionProper : Proper (eq ==> equiv ==> equiv) CMultiRestriction.
Proof.
  unfold Proper, "==>".
  intros n m H P Q H0.
  destruct P, Q; simpl in H0; simpl; subst.
  unfold Bool.Is_true, "=p" in H0.
  unfold Bool.Is_true, "=p"; simpl.
  rewrite 2?multires_getProc_simpl.
  induction m; simpl; trivial.
  simpl in IHm.
  case_eq (eqP_aux (MultiRestriction m x) (MultiRestriction m x0) [] []); intros; rewrite H in IHm; try contradiction.
  apply (eqP_aux_add_n _ _ a) in H; simpl in H.
  rewrite H; trivial.
Qed.

Instance CReplicationProper : Proper (equiv ==> equiv) CReplication.
Proof.
  unfold Proper, "==>".
  intros P Q H.
  destruct P, Q.
  simpl in H; simpl.
  unfold Bool.Is_true, "=p" in H.
  unfold Bool.Is_true, "=p"; simpl; trivial.
Qed.

Instance CMatchProper : Proper (equiv ==> equiv ==> equiv ==> equiv) CMatch.
Proof.
  unfold Proper, "==>".
  intros M M' H N N' H0 P P' H1.
  destruct M, M', N, N', P, P'.
  simpl in H; simpl in H0; simpl in H1; subst; simpl.
  unfold Bool.Is_true, "=p" in H1.
  unfold Bool.Is_true, "=p"; simpl.
  rewrite 2?eqT_aux_refl; try contradiction; simpl.
  assumption.
Qed.

Lemma CSplitProper : forall M N x y P Q (prfP : fv P ∖ ❴x❵ ∖ ❴y❵ == Ø) (prfQ : fv Q ∖ ❴x❵ ∖ ❴y❵ == Ø), M == N -> P == Q -> CSplit M x y P prfP == CSplit N x y Q prfQ.
Proof.
  intros.
  simpl; rewrite H.
  simpl in H0; unfold Bool.Is_true, "=p" in H0.
  unfold Bool.Is_true, "=p"; simpl.
  rewrite eqT_aux_refl; try contradiction; simpl.
  case_eq (eqP_aux P Q [] []); intros; rewrite H1 in H0; try contradiction.
  apply (eqP_aux_add_v _ _ x) in H1; apply (eqP_aux_add_v _ _ y) in H1; simpl in H1; rewrite H1; trivial.
Qed.

Lemma CCaseProper : forall M N x P Q P' Q' (prfQ : fv Q ∖ ❴x❵ == Ø) (prfQ' : fv Q' ∖ ❴x❵ == Ø), M == N -> P == P' -> Q == Q' -> CCase M P x Q prfQ == CCase N P' x Q' prfQ'.
Proof.
  intros.
  destruct P, P'.
  simpl; rewrite H.
  simpl in H0, H1; unfold Bool.Is_true, "=p" in H0, H1.
  unfold Bool.Is_true, "=p"; simpl.
  rewrite eqT_aux_refl; try contradiction; simpl.
  case_eq (eqP_aux x0 x1 [] []); intros; rewrite H2 in H0; try contradiction.
  case_eq (eqP_aux Q Q' [] []); intros; rewrite H3 in H1; try contradiction.
  apply (eqP_aux_add_v _ _ x) in H3; simpl in H3; rewrite H3; trivial.
Qed.

Lemma CDecryptionProper : forall M N M' N' x P Q (prfP : fv P ∖ ❴x❵ == Ø) (prfQ : fv Q ∖ ❴x❵ == Ø), M == M' -> N == N' -> P == Q -> CDecryption M N x P prfP == CDecryption M' N' x Q prfQ.
Proof.
  intros.
  simpl; rewrite H, H0.
  simpl in H1; unfold Bool.Is_true, "=p" in H1.
  unfold Bool.Is_true, "=p"; simpl.
  rewrite 2?eqT_aux_refl; try contradiction; simpl.
  case_eq (eqP_aux P Q [] []); intros; rewrite H2 in H1; try contradiction.
  apply (eqP_aux_add_v _ _ x) in H2; simpl in H2; rewrite H2; trivial.
Qed.

(* Morphisms to allow rewriting of relations with equivalent closed elements. *)

Instance ReductionProper : Proper (equiv ==> equiv ==> iff) Reduction.
Proof.
  unfold Proper, "==>".
  intros P P' H Q Q' H0.
  split; intros.
  apply (RedProper P Q); [symmetry; assumption | symmetry; assumption | assumption].
  apply (RedProper P' Q'); assumption.
Qed.

Instance StructuralProper : Proper (equiv ==> equiv ==> iff) Structural.
Proof.
  unfold Proper, "==>".
  intros P P' H Q Q' H0.
  split; intros.
  apply (StructProper P Q); [symmetry; assumption | symmetry; assumption | assumption].
  apply (StructProper P' Q'); assumption.
Qed.

Instance AStructuralProper : Proper (equiv ==> equiv ==> iff) (ARelation Structural).
Proof.
  unfold Proper, "==>".
  intros A A' H B B' H0.
  destruct A as (A & prfA), B as (B & prfB), A' as (A' & prfA'), B' as (B' & prfB').
  simpl in H, H0.
  subst.
  destruct A', B'; simpl in *; try destruct a; try destruct a0; try destruct c; try destruct c0; try reflexivity.
  split; intros; specialize H with M; trivial.
  apply (StructProper (exist _ (Sub p (getTerm M) v) (AAbs_proc_closed v p (getTerm M) prfA (getProof M)))
                      (exist _ (Sub p0 (getTerm M) v0) (AAbs_proc_closed v0 p0 (getTerm M) prfB (getProof M)))); spitrivial.
  apply (StructProper (exist _ (Sub p (getTerm M) v) (AAbs_proc_closed v p (getTerm M) prfA' (getProof M)))
                      (exist _ (Sub p0 (getTerm M) v0) (AAbs_proc_closed v0 p0 (getTerm M) prfB' (getProof M)))); spitrivial.
  destruct (term_names t t0); [ | reflexivity].
  split; intros; destruct H; split; trivial.
  apply (StructProper (exist _ (Rename_aux p l1) (ACon_proc_rename_closed l l1 t p prfA))
                      (exist _ p0 (ACon_proc_closed l0 t0 p0 prfB))); spitrivial.
  apply (StructProper (exist _ (Rename_aux p l1) (ACon_proc_rename_closed l l1 t p prfA'))
                      (exist _ p0 (ACon_proc_closed l0 t0 p0 prfB'))); spitrivial.
  split; intros.
  apply (StructProper (exist _ p (AProc_proc_closed p prfA))
                      (exist _ p0 (AProc_proc_closed p0 prfB))); spitrivial.
  apply (StructProper (exist _ p (AProc_proc_closed p prfA'))
                      (exist _ p0 (AProc_proc_closed p0 prfB'))); spitrivial.
Qed.

Instance ReactionProper : Proper (equiv ==> equiv ==> iff) Reaction.
Proof.
  unfold Proper, "==>".
  intros P P' H Q Q' H0.
  split; intros.
  apply (ReactProper P Q); [symmetry; assumption | symmetry; assumption | assumption].
  apply (ReactProper P' Q'); assumption.
Qed.

Instance BarbProper : Proper (equiv ==> eq ==> iff) Barb.
Proof.
  unfold Proper, "==>".
  intros P P' H n m H0; subst.
  split; intros.
  apply (BarbProper' P); [symmetry; assumption | assumption].
  apply (BarbProper' P'); assumption.
Qed.

(* Instance BBarbProper : Proper (equiv ==> eq ==> Basics.impl) BBarb.
Proof.
  unfold Proper, "==>", Basics.impl.
  intros P; induction P; intros Q H n0 n1 H0 H1; subst; simpl in H; unfold Bool.Is_true, "=p" in H; simpl in H; destruct Q; try inversion H.
  assert (Lem := OutputInversion).
  simpl in Lem; unfold Bool.Is_true, "=p" in Lem; simpl in Lem.
  apply Lem in H; destruct H, H0; subst.
  inversion H1; subst.
  apply BBarbOut.
  assert (Lem := InputInversion).
  simpl in Lem; unfold Bool.Is_true, "=p" in Lem; simpl in Lem.
  apply Lem in H; destruct H, H0; subst.
  inversion H1; subst.
  apply BBarbIn.
  assert (Lem := CompositionInversion).
  unfold equiv at 1, ProcessSetoid at 1, Bool.Is_true at 1, "=p" at 1 in Lem.
  apply Lem in H; destruct H; subst.
  inversion H1; subst.
  apply BBarbParL; apply (IHP1 _ H n1); trivial.
  apply BBarbParR; apply (IHP2 _ H0 n1); trivial.
  assert (Lem := RestrictionInversion).
  unfold equiv at 1, ProcessSetoid at 1, Bool.Is_true at 1, "=p" at 1 in Lem.
  apply Lem in H.
  inversion H1; subst.
  admit.
  assert (Lem := ReplicationInversion).
  unfold equiv at 1, ProcessSetoid at 1, Bool.Is_true at 1, "=p" at 1 in Lem.
  apply Lem in H.
  inversion H1; subst.
  apply BBarbRepl.
  apply (IHP _ H n1); trivial.
  assert (Lem := MatchInversion).
  simpl in Lem; unfold Bool.Is_true, "=p" in Lem; simpl in Lem.
  apply Lem in H; destruct H, H0; subst.
  inversion H1; subst.
  apply BBarbMatch.
  apply (IHP _ H2 n1); trivial.
  trivial.
  assert (Lem := SplitInversion).
  simpl in Lem; unfold Bool.Is_true, "=p" in Lem; simpl in Lem.
  apply Lem in H; destruct H; subst.
  inversion H1; subst.
  apply BBarbLet.
  Admitted.
  (* apply (IHP _ H0 n1); trivial.
Qed. *) *)

Instance ConvergenceProper : Proper (equiv ==> eq ==> iff) Convergence.
Proof.
  unfold Proper, "==>".
  intros P P' H n m H0; subst.
  split; intros.
  apply (ConvProper P); [symmetry; assumption | assumption].
  apply (ConvProper P'); assumption.
Qed.

Instance CommitmentProper : Proper (equiv ==> equiv ==> eq ==> iff) Commitment.
Proof.
  unfold Proper, "==>".
  intros P P' H Q Q' H0 a a' H1; subst.
  split; intros.
  apply (CommProper P Q); [symmetry; assumption | symmetry; assumption | assumption].
  apply (CommProper P' Q'); assumption.
Qed.

(* Testing equivalence is reflexive. *)
Lemma test_eq_refl : forall (P: ClosedProcess), TestingEquivalence P P.
Proof.
  split; unfold TestingPreorder; intros; assumption.
Qed.

(* Testing equivalence is symmetric. *)
Lemma test_eq_sym : forall (P Q: ClosedProcess), TestingEquivalence P Q -> TestingEquivalence Q P.
Proof.
  intros; unfold TestingEquivalence, TestingPreorder; split; intros; destruct H.
  apply H1 in H0; assumption.
  apply H in H0; assumption.
Qed.

(* Testing equivalence is transitive. *)
Lemma test_eq_trans : forall (P Q R: ClosedProcess), TestingEquivalence P Q -> TestingEquivalence Q R -> TestingEquivalence P R.
Proof.
  split; destruct H; destruct H0; unfold TestingEquivalence, TestingPreorder in *; intros.
  apply H in H3; apply H0 in H3; assumption.
  apply H2 in H3; apply H1 in H3; assumption.
Qed.

(* Testing equivalence is an equivalence relation. *)
Instance TestingEquiv : Equivalence TestingEquivalence.
Proof.
  split.
  unfold Reflexive; apply test_eq_refl.
  unfold Symmetric; apply test_eq_sym.
  unfold Transitive; apply test_eq_trans.
Qed.

(* Structural equivalence is reflexive. *)
Lemma structeq_refl : forall P, Structural P P.
Proof.
  intros P; apply (StructRefl P P); reflexivity.
Qed.

(* Structural equivalence is symmetric. *)
Lemma structeq_sym : forall P Q, Structural P Q -> Structural Q P.
Proof.
  intros P Q H.
  apply (StructSymm P Q); spitrivial.
Qed.

(* Structural equivalence is transitive. *)
Lemma structeq_trans : forall P Q R, Structural P Q -> Structural Q R -> Structural P R.
Proof.
  intros P Q R H H0.
  apply (StructTrans P Q R); spitrivial.
Qed.

(* Structural equivalence is an equivalence relation. *)
Instance StructuralEquiv : Equivalence Structural.
Proof.
  split.
  unfold Reflexive; apply structeq_refl.
  unfold Symmetric; apply structeq_sym.
  unfold Transitive; apply structeq_trans.
Qed.

(* Structural equivalence holds under Reduction. *)
Instance StructuralRedProper : Proper (Reduction ==> Reduction ==> iff) Structural.
Proof.
  unfold Proper, "==>".
  intros P P' H Q Q' H0.
  apply (StructRed _ _ P P') in H; spitrivial.
  apply (StructRed _ _ Q Q') in H0; spitrivial.
  rewrite <- H, <- H0; reflexivity.
Qed.

(* Reaction holds under structural equivalence. *)
Instance ReactionStructProper : Proper (Structural ==> Structural ==> iff) Reaction.
Proof.
  unfold Proper, "==>".
  intros P P' H Q Q' H0.
  split; intros.
  apply (ReactStruct P' P Q' Q); spitrivial.
  symmetry; assumption.
  apply (ReactStruct P P' Q Q'); spitrivial.
  symmetry; assumption.
Qed.

(* Barb holds under structural equivalence. *)
Instance BarbStructProper : Proper (Structural ==> eq ==> iff) Barb.
Proof.
  unfold Proper, "==>".
  intros P Q H m n H0; subst.
  split; intros.
  apply (BarbStruct Q P); spitrivial.
  symmetry; assumption.
  apply (BarbStruct P Q); spitrivial.
Qed.

(* Convergence holds under reaction. *)
Instance ConvergenceReactProper : Proper (Reaction --> eq ==> Basics.impl) Convergence.
Proof.
  unfold Proper, "==>", Basics.flip, Basics.impl.
  intros P Q H n m H0 H1; subst.
  apply (ConvReact Q P); spitrivial.
Qed.

(* Closed composition holds under structural equivalence. *)
Instance CCompositionStructProper : Proper (Structural ==> Structural ==> Structural) CComposition.
Proof.
  unfold Proper, "==>".
  intros P P' H Q Q' H0.
  rewrite (StructPar P P' Q (CComposition P Q) (CComposition P' Q)); spitrivial.
  rewrite (StructComm P' Q (CComposition P' Q) (CComposition Q P')); spitrivial.
  rewrite (StructComm P' Q' (CComposition P' Q') (CComposition Q' P')); spitrivial.
  apply (StructPar Q Q' P'); spitrivial.
Qed.

(* Closed restriction holds under structural equivalence. *)
Instance CRestrictionStructProper : Proper (eq ==> Structural ==> Structural) CRestriction.
Proof.
  unfold Proper, "==>".
  intros n m H P Q H0; subst.
  apply (StructRes P Q m); spitrivial.
Qed.

(* MultiRestriction versions of restriction-related structural rules. *)
(* Need to be here as they require a Proper instance for simpler proof, and are required for a Proper instance proof. *)

(* If the processes are structurally equivalent with the same list of names, the sequential restriction is also equivalent. *)
(* Acts as a multi-name version of StructRes. *)
Lemma StructMultiRes : forall P Q l R S, R == CMultiRestriction l P -> S == CMultiRestriction l Q -> Structural P Q -> Structural R S.
Proof.
  intros.
  rewrite H, H0; clear H; clear H0. (* Must remove these assumptions to get the correct induction hypothesis. *)
  induction l; simpl; trivial.
  apply (StructRes (CMultiRestriction l P) (CMultiRestriction l Q) a); spitrivial.
Qed.

(* MultiRestriction version of StructDrop. *)
Lemma StructMultiDrop : forall l P Q, P == CMultiRestriction l CNil -> Q == CNil -> Structural P Q.
Proof.
  intros.
  rewrite H, H0; clear H; clear H0. (* Must remove these assumptions to get the correct induction hypothesis. *)
  induction l; simpl.
  reflexivity.
  rewrite IHl; apply (StructDrop a); spitrivial.
Qed.

(* MultiRestriction version of StructExtrusion. *)
Lemma StructMultiExtrusion : forall P Q l R S, R == CMultiRestriction l (CComposition P Q) -> S == CComposition P (CMultiRestriction l Q) -> (forall n, In n l -> ~elem_set n (fn (getProc P))) -> Structural R S.
Proof.
  intros.
  rewrite H, H0; clear H; clear H0. (* Must remove these assumptions to get the correct induction hypothesis. *)
  induction l; simpl.
  reflexivity.
  assert (~elem_set a (fn (getProc P))).
  specialize H1 with a; simpl in H1.
  destruct P as (P & prfP), Q as (Q & prfQ), R as (R & prfR); simpl in *.
  assert (a = a \/ In a l <-> True).
  split; intros; trivial.
  left; trivial.
  rewrite H in H1; assert (True); trivial; apply H1; trivial.
  assert (Structural (CRestriction a (CComposition P (CMultiRestriction l Q))) (CComposition P (CRestriction a (CMultiRestriction l Q)))).
  apply (StructExtrusion P (CMultiRestriction l Q) a); spitrivial.
  rewrite <- H0; apply (StructRes (CMultiRestriction l (CComposition P Q)) (CComposition P (CMultiRestriction l Q)) a); spitrivial.
  apply IHl; intros.
  apply H1; simpl; right; trivial.
Qed.

(* Closed multirestriction holds under structural equivalence. *)
Instance CMultiRestrictionStructProper : Proper (eq ==> Structural ==> Structural) CMultiRestriction.
Proof.
  unfold Proper, "==>".
  intros l l' H P Q H0; subst.
  apply (StructMultiRes P Q l'); spitrivial.
Qed.

(* Barbed equivalence is reflexive. *)
Lemma barbed_eq_refl : forall (P: ClosedProcess), BarbedEquivalence P P.
Proof.
  intros P.
  exists eq; split; trivial.
  repeat split; intros; unfold Converse in *; subst; trivial.
  exists P'; split; trivial.
  unfold "upto"; exists P', P'; repeat split; reflexivity.
  exists P'; split; trivial.
  unfold "upto"; exists P', P'; repeat split; reflexivity.
Qed.

(* Barbed equivalence is symmetric. *)
Lemma barbed_eq_sym : forall (P Q: ClosedProcess), BarbedEquivalence P Q -> BarbedEquivalence Q P.
Proof.
  intros P Q H.
  destruct H as (Rel & H); destruct H; destruct H.
  exists (Converse Rel); unfold Converse.
  repeat split; intros; trivial.
  apply H1 in H2; destruct H2; apply H2 in H3; assumption.
  apply H1 in H2; destruct H2; apply H4 in H3.
  destruct H3 as (Q' & H3); destruct H3.
  exists Q'; split; assumption.
  apply H in H2; destruct H2; apply H2 in H3; assumption.
  apply H in H2; destruct H2; apply H4 in H3.
  destruct H3 as (Q' & H3); destruct H3.
  exists Q'; split; assumption.
Qed.

(* Barbed equivalence is transitive. *)
Lemma barbed_eq_trans : forall (P Q R: ClosedProcess), BarbedEquivalence P Q -> BarbedEquivalence Q R -> BarbedEquivalence P R.
Proof.
  intros P Q R H H0.
  destruct H as (Rel & H); destruct H; destruct H.
  destruct H0 as (Rel' & H0); destruct H0; destruct H0.
  exists (fun x z => exists y y', Rel x y /\ Rel' y' z /\ y ≡ y').
  repeat split; intros.
  destruct H5 as (R0 & R1 & H5); destruct H5; destruct H7.
  apply H in H5; destruct H5; apply H0 in H7; destruct H7; apply H5 in H6.
  rewrite H8 in H6; apply H7 in H6; assumption.
  destruct H5 as (R0 & R1 & H5); destruct H5; destruct H7.
  apply H in H5; destruct H5; apply H9 in H6; destruct H6 as (Q1 & H6); destruct H6; apply H0 in H7; destruct H7.
  rewrite H8 in H6; apply H11 in H6; destruct H6 as (Q2 & H6); destruct H6.
  exists Q2; split; [assumption | unfold "upto" in *].
  destruct H10 as (P2 & Q3 & H10); destruct H10; destruct H13.
  destruct H12 as (Q4 & Q5 & H12); destruct H12; destruct H15.
  exists P2, Q5.
  repeat split; [ | assumption | assumption].
  exists Q3, Q4.
  repeat split; [assumption | assumption | rewrite <- H15; symmetry; assumption].
  destruct H5 as (R0 & R1 & H5); destruct H5; destruct H7.
  apply H2 in H5; destruct H5; apply H4 in H7; destruct H7; apply H7 in H6.
  rewrite <- H8 in H6; apply H5 in H6; assumption.
  destruct H5 as (R0 & R1 & H5); destruct H5; destruct H7.
  apply H4 in H7; destruct H7; apply H9 in H6; destruct H6 as (Q' & H6); destruct H6; apply H2 in H5; destruct H5.
  rewrite <- H8 in H6; apply H11 in H6; destruct H6 as (Q2 & H6); destruct H6.
  exists Q2; split; [assumption | unfold "upto" in *].
  destruct H10 as (P2 & Q3 & H10); destruct H10; destruct H13.
  destruct H12 as (Q4 & Q5 & H12); destruct H12; destruct H15.
  exists P2, Q5.
  repeat split; [ | assumption | assumption].
  exists Q4, Q3.
  repeat split; [assumption | assumption | rewrite <- H15; assumption].
  exists Q, Q.
  repeat split; [assumption | assumption | reflexivity].
Qed.

(* Barbed equivalence is an equivalence relation. *)
Instance BarbedEquiv : Equivalence BarbedEquivalence.
Proof.
  split.
  unfold Reflexive; apply barbed_eq_refl.
  unfold Symmetric; apply barbed_eq_sym.
  unfold Transitive; apply barbed_eq_trans.
Qed.

(* Barbed congruence is reflexive. *)
Lemma barbed_congruence_refl : forall (P: ClosedProcess), BarbedCongruence P P.
Proof.
  unfold BarbedCongruence; reflexivity.
Qed.

(* Barbed congruence is symmetric. *)
Lemma barbed_congruence_sym : forall (P Q: ClosedProcess), BarbedCongruence P Q -> BarbedCongruence Q P.
Proof.
  unfold BarbedCongruence; intros.
  symmetry.
  specialize H with R.
  assumption.
Qed.

(* Barbed congruence is transitive. *)
Lemma barbed_congruence_trans : forall (P Q R: ClosedProcess), BarbedCongruence P Q -> BarbedCongruence Q R -> BarbedCongruence P R.
Proof.
  unfold BarbedCongruence; intros.
  specialize H with R0.
  specialize H0 with R0.
  transitivity (CComposition Q R0); assumption.
Qed.

(* Barbed congruence is an equivalence relation. *)
Instance BarbedConEquiv : Equivalence BarbedCongruence.
Proof.
  split.
  unfold Reflexive; apply barbed_congruence_refl.
  unfold Symmetric; apply barbed_congruence_sym.
  unfold Transitive; apply barbed_congruence_trans.
Qed.

(*PROOF8*************************************************************************PROOFS*******************************************************************************)
(* Proofs of various properties important to the calculus, and sublemmas relating to those proofs. *)

(* If P exhibits basic barb β then β is in the free names of P. *)
Lemma barb_fn : forall (P: Process) (β: Name), BBarb P β -> β ∈ fn P.
Proof.
  intros.
  induction H; simpl; try rewrite elem_union_iff; try rewrite elem_union_iff; try rewrite elem_union_iff.
  (* BBarbIn *)
  left; rewrite elem_singleton; trivial.
  (* BBarbOut *)
  left; left; rewrite elem_singleton; trivial.
  (* BBarbParL *)
  left; assumption.
  (* BBarbParR *)
  right; assumption.
  (* BBarbRes *)
  rewrite elem_diff_iff; split; trivial.
  unfold elem_set; simpl; intro; destruct H1; [symmetry in H1 | ]; contradiction.
  (* BBarbRepl *)
  assumption.
  (* BBarbMatch *)
  right; assumption.
  (* BBarbLet *)
  rewrite 2?fn_Sub, 2?elem_union_iff in IHBBarb; destruct IHBBarb.
  destruct H0.
  right; assumption.
  left; left; assumption.
  left; right; assumption.
  (* BBarbZero *)
  left; right; assumption.
  (* BBarbSuc *)
  rewrite fn_Sub, elem_union_iff in IHBBarb; destruct IHBBarb.
  right; assumption.
  left; left; assumption.
  (* BBarbDecrypt *)
  rewrite fn_Sub, elem_union_iff in IHBBarb; destruct IHBBarb.
  right; assumption.
  left; left; left; assumption.
Qed.

(* Barb and Barb' are equivalent. *)
Lemma barb_equiv : forall P β, Barb P β <-> Barb' P β.
Proof.
  intros; split; intros.
  (* -> *)
  induction H.
  (* BarbIn *)
  apply (BarbStruct' _ (CInput (CTName m) x P prf)).
  apply (StructRefl Q ((CTName m ﹙ x ﹚, P) prf)); trivial; reflexivity.
  apply BBarbIn.
  (* BarbOut *)
  apply (BarbStruct' _ (COutput (CTName m) M P)).
  apply (StructRefl Q (CTName m ⟨ M ⟩, P)); trivial; reflexivity.
  apply BBarbOut.
  (* BarbPar *)
  inversion IHBarb; subst.
  apply (BarbStruct' _ (CComposition Q0 Q)).
  rewrite <- H1.
  apply (StructRefl R (P ⎪ Q)); trivial; try reflexivity.
  apply BBarbParL; assumption.
  (* BarbRes *)
  inversion IHBarb; subst.
  apply (BarbStruct' _ (CRestriction m Q0)).
  apply (StructRefl Q (CRestriction m P) Q (CRestriction m P)) in H0; try reflexivity.
  rewrite H0, H2.
  reflexivity.
  apply BBarbRes; assumption.
  (* BarbStruct *)
  inversion IHBarb; subst.
  apply (BarbStruct' _ Q0); trivial.
  apply (StructTrans P Q Q0); try assumption; try reflexivity.
  (* <- *)
  (* First the following lemma *)
  assert (Lem : forall P β prf, BBarb P β -> Barb (exist _ P prf) β).
  intros.
  induction H0.
  (* BBarbIn *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty_l in prf'.
  apply (BarbIn P0 _ x prf'); spitrivial.
  (* BBarbOut *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty in prf'; destruct prf'; rewrite union_empty_l in H0.
  apply (BarbOut (exist _ P0 H1) _ (exist _ M H0) _); spitrivial.
  (* BBarbParL *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty in prf'; destruct prf'.
  apply (BarbPar (exist _ P0 H1) (exist _ Q H2) β0 _); spitrivial.
  (* BBarbParR *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty in prf'; destruct prf'.
  rewrite (StructComm (exist _ P0 H1) (exist _ Q H2) (exist _ (Composition P0 Q) prf) (exist _ (Composition Q P0) (CompositionClosed Q P0 H2 H1))); spitrivial.
  apply (BarbPar (exist _ Q H2) (exist _ P0 H1) β0 _); spitrivial.
  (* BBarbRes *)
  assert (prf' := prf); simpl fv in prf'.
  apply (BarbRes (exist _ P0 prf') β0 m _ H0); spitrivial.
  (* BBarbRepl *)
  assert (prf' := prf); simpl fv in prf'.
  assert (prf2: fv (Composition P0 (Replication P0)) == Ø).
  simpl fv; rewrite prf'; simpl; trivial.
  specialize IHBBarb with prf'.
  apply (BarbStruct (exist _ (Replication P0) prf) (exist _ (Composition P0 (Replication P0)) prf2) β0); spitrivial.
  apply (StructRed (exist _ (Replication P0) prf) (exist _ (Composition P0 (Replication P0)) prf2)); spitrivial.
  apply (RedRepl (exist _ P0 prf') _ _); spitrivial.
  apply (BarbPar (exist _ P0 prf') (CReplication (exist _ P0 prf'))); spitrivial.
  (* BBarbMatch *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty in prf'; destruct prf'.
  rewrite union_empty in H1; destruct H1.
  apply (BarbStruct (exist _ (Match M M P0) prf) (exist _ P0 H2) β0); spitrivial.
  apply (StructRed (exist _ (Match M M P0) prf) (exist _ P0 H2)); spitrivial.
  apply (RedMatch (exist _ P0 H2) (exist _ M H1) _ _); spitrivial.
  (* BBarbLet *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty in prf'; destruct prf'.
  rewrite union_empty in H1; destruct H1.
  assert (H4 : fv ((P0 〚 M ∕ x 〛) 〚 N ∕ y 〛) == Ø).
  antisymmetry.
  rewrite 2?fv_Sub, H1, H3, 2?union_empty_r, H2; reflexivity.
  unfold incl_set; intros; contradiction.
  specialize IHBBarb with H4.
  apply (BarbStruct (exist _ (Split (Pair M N) x y P0) prf) (exist _ (Sub (Sub P0 M x) N y) H4) _); spitrivial.
  apply (StructRed (exist _ (Split (Pair M N) x y P0) prf) (exist _ (Sub (Sub P0 M x) N y) H4)); spitrivial.
  apply (RedLet P0 (exist _ M H1) (exist _ N H3) x y H2 _ _); spitrivial.
  (* BBarbZero *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty in prf'; destruct prf'.
  rewrite union_empty in H1; destruct H1.
  specialize IHBBarb with H3.
  apply (BarbStruct (exist _ (Case Zero P0 x Q) prf) (exist _ P0 H3) _); spitrivial.
  apply (StructRed (exist _ (Case Zero P0 x Q) prf) (exist _ P0 H3)); spitrivial.
  apply (RedZero (exist _ P0 H3) x Q H2 _ _); spitrivial.
  (* BBarbSuc *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty in prf'; destruct prf'.
  rewrite union_empty in H1; destruct H1.
  assert (H4 : fv (Q 〚 M ∕ x 〛) == Ø).
  antisymmetry.
  rewrite fv_Sub, H1, union_empty_r, H2; reflexivity.
  unfold incl_set; intros; contradiction.
  specialize IHBBarb with H4.
  apply (BarbStruct (exist _ (Case (Suc M) P0 x Q) prf) (exist _ (Sub Q M x) H4) _); spitrivial.
  apply (StructRed (exist _ (Case (Suc M) P0 x Q) prf) (exist _ (Sub Q M x) H4)); spitrivial.
  apply (RedSuc (exist _ P0 H3) Q (exist _ M H1) x H2 _ _); spitrivial.
  (* BBarbDecrypt *)
  assert (prf' := prf); simpl fv in prf'; rewrite union_empty in prf'; destruct prf'.
  rewrite union_empty in H1; destruct H1.
  rewrite union_empty in H1; destruct H1.
  assert (H5 : fv (P0 〚 M ∕ x 〛) == Ø).
  antisymmetry.
  rewrite fv_Sub, H1, union_empty_r, H2; reflexivity.
  unfold incl_set; intros; contradiction.
  specialize IHBBarb with H5.
  apply (BarbStruct (exist _ (Decryption (Encryption M N) N x P0) prf) (exist _ (Sub P0 M x) H5) _); spitrivial.
  apply (StructRed (exist _ (Decryption (Encryption M N) N x P0) prf) (exist _ (Sub P0 M x) H5)); spitrivial.
  apply (RedDecrypt P0 (exist _ M H1) (exist _ N H3) x H2 _ _); spitrivial.
  (* Now the proof of <- *)
  inversion H.
  apply (BarbStruct P Q _ P); try reflexivity; try assumption.
  destruct Q as (Q & prf).
  apply Lem; assumption.
Qed.

(* Lemma eq_barb : forall P Q x, P == Q -> (BBarb (getProc P) x <-> BBarb (getProc Q) x).
Proof.
  intros.
  destruct P as (P & prfP), Q as (Q & prfQ); simpl in *.
  unfold Bool.Is_true, "=p" in H.
  destruct (eqP_aux x0 x1 [] []); try contradiction.
  reflexivity.
Qed. *)

(* The reflexive transitive closure of reaction holds under closed process equivalence. *)
Instance RTCReactionProper : Proper (equiv ==> equiv ==> iff) (rtc Reaction).
Proof.
  unfold Proper, "==>"; split; intros.
  induction H1.
  apply (rtc_refl _ x); [rewrite <- H | rewrite <- H0]; assumption.
  apply (rtc_trans _ y y1 z); [reflexivity | rewrite <- H0 | rewrite <- H, H1 | ]; assumption.
  induction H1.
  apply (rtc_refl _ x1); [rewrite H | rewrite H0]; assumption.
  apply (rtc_trans _ v y z); [ | rewrite H0 | rewrite H1 | ]; assumption.
Qed.

(* Convergence is equivalent to the existence of some process Q relating via the RTC of Reaction to P, and Barb Q beta. *)
Lemma conv_barb_equiv : forall P β, P ~~> β <-> exists Q, rtc Reaction P Q /\ Q ~> β.
Proof.
  split; intros.
  unfold Test in H; simpl.
  induction H.
  exists P; split.
  rewrite H; apply (rtc_refl _ P); reflexivity.
  assumption.
  destruct IHConvergence as (Q' & IH); destruct IH.
  exists Q'; split.
  rewrite H; apply (rtc_trans _ P Q Q'); spitrivial.
  assumption.
  destruct H as (Q & H); destruct H.
  induction H.
  apply (ConvBarb x); trivial.
  rewrite H1 in H0; assumption.
  rewrite H1 in H0; apply IHrtc in H0; rewrite H; apply (ConvReact x y); try reflexivity; assumption.
Qed.

(******************************************************************END OF BASE CALCULUS****************************************************************************)

(***************************************************EXAMPLES*****************************************************************************)
(* Example definitions and proofs from the paper. *)

Open Scope string_scope.

(* Basic protocol from section 2.3.1 of the paper. *)

Definition BasicA (M: ClosedTerm) := COutput (CTName "c") M CNil.

Definition BasicB' (F: ClosedAbstraction) := Input (TName "c") "x" (Instantiate (getAbs F) (TVar "x")).

Lemma BasicBClosed (F: ClosedAbstraction) : fv (BasicB' F) == Ø.
Proof.
  unfold BasicB', Instantiate; destruct F as (F & prfF), F; simpl fv; simpl fvAbs in prfF.
  antisymmetry.
  rewrite fv_Sub, prfF; simpl.
  rewrite 2?union_empty_l, diff_equal; reflexivity.
  unfold incl_set; intros; contradiction.
Qed.

Definition BasicB (F: ClosedAbstraction) : ClosedProcess := exist _ (BasicB' F) (BasicBClosed F).

Definition BasicBspec' (F: ClosedAbstraction) (M: ClosedTerm) := Input (TName "c") "x" (Instantiate (getAbs F) (getTerm M)).

Lemma BasicBspecClosed (F: ClosedAbstraction) (M: ClosedTerm) : fv (BasicBspec' F M) == Ø.
Proof.
  unfold BasicBspec', Instantiate; destruct F as (F & prfF), M as (M & prfM), F; simpl fv; simpl fvAbs in prfF.
  antisymmetry.
  rewrite fv_Sub, prfF, prfM; simpl.
  rewrite union_idemp, 2?union_empty_l, diff_empty_l; reflexivity.
  unfold incl_set; intros; contradiction.
Qed.

Definition BasicBspec (F: ClosedAbstraction) (M: ClosedTerm) : ClosedProcess := exist _ (BasicBspec' F M) (BasicBspecClosed F M).

Definition Basic (F: ClosedAbstraction) (M: ClosedTerm) := CRestriction "c" (CComposition (BasicA M) (BasicB F)).

Definition Basicspec (F: ClosedAbstraction) (M: ClosedTerm) := CRestriction "c" (CComposition (BasicA M) (BasicBspec F M)).

Definition BasicRel (F: ClosedAbstraction) (M: ClosedTerm) : relation ClosedProcess := MakeRelation [(Basic F M, Basicspec F M);
                        (new "c" in (0 ⎪ CInstantiate F M), new "c" in (0 ⎪ CInstantiate F M))].

(* Version of composition inversion that works on closed processes and keeps them as closed processes. *)
Lemma CCompositionInversion : forall P P' Q Q', CComposition P Q == CComposition P' Q' -> P == P' /\ Q == Q'.
Proof.
  intros.
  apply CompositionInversion in H.
  simpl in *; assumption.
Qed.

(* Version of restriction inversion that works on closed processes and keeps them as closed processes. *)
(* Lemma CRestrictionInversion : forall n m P Q, CRestriction n P == CRestriction m Q -> .
Proof.
  intros.
  apply RestrictionInversion in H.
  simpl in *; assumption.
Qed. *)

Lemma CRenameComposition_aux : forall P Q l, CRename_aux (CComposition P Q) l == CComposition (CRename_aux P l) (CRename_aux Q l).
Proof.
  intros.
  destruct P as (P & prfP), Q as (Q & prfQ); simpl.
  unfold Bool.Is_true, "=p"; simpl.
  rewrite 2?eqP_aux_refl; try contradiction; simpl; trivial.
Qed.

Lemma getProcComp : forall P Q, getProc (P ⎪ Q) = Composition (getProc P) (getProc Q).
Proof.
  intros.
  destruct P, Q; simpl; trivial.
Qed.

Lemma BasicAuthenticityNil : forall M, Basic (CAbs "x" Nil NilClosed) M ~s Basicspec (CAbs "x" Nil NilClosed) M.
Proof.
  intros M.
  unfold "~s".
  exists (BasicRel (CAbs "x" Nil NilClosed) M).
  split.
  split.
  unfold Simulation; intros.
  destruct H as [Pair | Pair].
  destruct Pair as [PH QH].
  rewrite PH in H0.
  inversion H0; subst; [inversion H | inversion H | inversion H | inversion H | inversion H | inversion H | | rewrite <- H in H2; inversion H2; subst; inversion H4].
  inversion H2; subst; rewrite H4 in H; [inversion H | inversion H | | | | | inversion H | ].
  (* First possible case: CommInter1.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc (BasicA M)) (getProc (BasicB F))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc (BasicA M)) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (BasicB F)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  destruct t, x; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m); simpl in H; try discriminate; subst.
  rewrite Bool.andb_true_r in H.
  (* Breaking down BasicB *)
  destruct Q0, x; simpl in H8; try discriminate.
  destruct t; try (rewrite Bool.andb_false_r in H8; discriminate); try (rewrite Bool.andb_false_l in H8; discriminate).
  destruct (string_dec n m); simpl in H8; try discriminate; subst.
  inversion H6; [inversion H10 | inversion H13 | inversion H9 | inversion H9 | inversion H9 | rewrite <- H9 in H11; inversion H11; inversion H16].
  (* Second possible case: CommInter2.  This is the case that works. *)
  destruct C as (C & prfC), F as (F & prfF), C, F.
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc (BasicA M)) (getProc (BasicB (CAbs "x" Nil NilClosed)))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc (BasicA M)) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (BasicB (CAbs "x" Nil NilClosed))) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  destruct t0, x; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m); simpl in H; try discriminate; subst.
  rewrite Bool.andb_true_r in H.
  (* Breaking down BasicB *)
  destruct Q0, x; simpl in H8; try discriminate.
  destruct t0; try (rewrite Bool.andb_false_r in H8; discriminate); try (rewrite Bool.andb_false_l in H8; discriminate).
  destruct (string_dec n m), x; simpl in H8; try discriminate; subst.
  (* Need to break down C and F0 as well. *)
  inversion H6; [inversion H13 | | inversion H9 | inversion H9 | inversion H9 | rewrite <- H9 in H11; inversion H11; inversion H16].
  inversion H7; [ | inversion H15 | inversion H14 | inversion H14 | inversion H14 | rewrite <- H14 in H16; inversion H16; inversion H21].
  subst.
  (* Need to provide the agent we commit to in the goal. *)
  exists (CARestriction "c" (CAProc ((CCon [] M 0) @R (CAbs "x" (Instantiate (Abs "x" Nil) (getTerm M)) NilClosed)))).
  split.
  apply (CommRes (CComposition (BasicA M) (BasicBspec (CAbs "x" Nil NilClosed) M)) (CAProc ((CCon [] M 0)  @R (CAbs "x" Nil NilClosed))) _ "c"); spitrivial.
  apply (CommInter2 (BasicA M) (BasicBspec (CAbs "x" Nil NilClosed) M) "c" (CCon [] M 0) (CAbs "x" Nil NilClosed)); spitrivial.
  unfold BasicA.
  apply (CommOut CNil M); spitrivial.
  unfold BasicBspec.
  apply (CommIn Nil _ "x" NilClosed); spitrivial.
  discriminate.
  (* Show they are related by BasicRel. *)
  (* We want to break everything down as much as possible. *)
  destruct A, A0; simpl in H1, H5; rewrite H5 in H1; subst.
  simpl ARestriction.
  destruct M as (M & prfM), M0 as (M0 & prfM0); simpl getAbs; simpl getTerm.
  right; left; split; simpl.
  simpl in H13, H18.
  inversion H13; inversion H18; subst; simpl.
  apply OutputInversion in H10; destruct H10.
  destruct H5, P1; simpl in H9.
  unfold Bool.Is_true, "=p" in H9.
  simpl in H9; destruct x0; try contradiction; simpl.
  apply InputInversion in H15; destruct H15.
  simpl in H10; inversion H10; subst.
  simpl in H11; destruct P2; try discriminate.
  trivial.
  trivial.
  (* Third possible case: CommPar1.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc (BasicA M)) (getProc (BasicB (CAbs "x" Nil NilClosed)))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc (BasicA M)) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (BasicB (CAbs "x" Nil NilClosed))) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  destruct t, x; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m); simpl in H; try discriminate; subst.
  rewrite Bool.andb_true_r in H.
  (* Breaking down BasicB *)
  destruct Q0, x; simpl in H7; try discriminate.
  destruct t; try (rewrite Bool.andb_false_r in H7; discriminate); try (rewrite Bool.andb_false_l in H7; discriminate).
  destruct (string_dec n m); simpl in H7; try discriminate; subst.
  (* Only possible case is CommOut; we determine this by inversion. *)
  inversion H6; [inversion H8 | | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | rewrite <- H8 in H10; inversion H10; inversion H15].
  apply OutputInversion in H8; destruct H8.
  (* The restriction makes this case impossible. *)
  inversion H8; subst; contradiction.
  (* Fourth possible case: CommPar2.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc (BasicA M)) (getProc (BasicB (CAbs "x" Nil NilClosed)))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc (BasicA M)) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (BasicB (CAbs "x" Nil NilClosed))) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  destruct t, x; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m); simpl in H; try discriminate; subst.
  rewrite Bool.andb_true_r in H.
  (* Breaking down BasicB *)
  destruct Q0, x; simpl in H7; try discriminate.
  destruct t; try (rewrite Bool.andb_false_r in H7; discriminate); try (rewrite Bool.andb_false_l in H7; discriminate).
  destruct (string_dec n m); simpl in H7; try discriminate; subst.
  (* CommIn is the only possible case here. *)
  inversion H6; [ | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | rewrite <- H8 in H10; inversion H10; inversion H15].
  apply InputInversion in H8; destruct H8.
  (* A solo commitment by m is impossible here due to the restriction. *)
  inversion H8; subst; contradiction.
  (* Last possible case: CommRed.  This case is not possible. *)
  unfold Basic in H.
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  destruct P1, x; simpl in H; try discriminate.
  destruct x1, x2; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct t, x1; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct t1; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m), (string_dec n0 m); simpl in H; try (rewrite Bool.andb_false_r in H; discriminate); try discriminate; subst.
  inversion H6; inversion H8.
  (* Next step of forward simulation proof. *)
  (* Further state examination.  May need an assumption that F contains no possible commitments. *)
  destruct Pair as [Pair | H].
  destruct Pair as [PH QH].
  rewrite PH in H0.
  inversion H0; subst; [inversion H | inversion H | inversion H | inversion H | inversion H | inversion H | | rewrite <- H in H2; inversion H2; subst; inversion H4].
  inversion H2; subst; rewrite H4 in H; [inversion H | inversion H | | | | | inversion H | ].
  (* First possible case: CommInter1.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc 0) (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc 0) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  (* Breaking down BasicB *)
  destruct M as (M & prfM); simpl in H8.
  destruct Q0, x; simpl in H8; try discriminate.
  inversion H6; [inversion H10 | inversion H13 | inversion H9 | inversion H9 | inversion H9 | rewrite <- H9 in H11; inversion H11; inversion H16].
  (* Second possible case: CommInter2.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc 0) (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc 0) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  (* Breaking down BasicB *)
  destruct M as (M & prfM); simpl in H8.
  destruct Q0, x; simpl in H8; try discriminate.
  inversion H6; [inversion H10 | inversion H10 | inversion H9 | inversion H9 | inversion H9 | rewrite <- H9 in H11; inversion H11; inversion H16].
  (* Third possible case: CommPar1.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc 0) (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc 0) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  (* Breaking down BasicB *)
  destruct M as (M & prfM); simpl in H7.
  destruct Q0, x; simpl in H7; try discriminate.
  inversion H6; [inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | rewrite <- H8 in H10; inversion H10; inversion H15].
  (* Fourth possible case: CommPar2.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc 0) (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc 0) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  (* Breaking down BasicB *)
  destruct M as (M & prfM); simpl in H7.
  destruct Q0, x; simpl in H7; try discriminate.
  inversion H6; [inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | rewrite <- H8 in H10; inversion H10; inversion H15].
  (* Last possible case: CommRed.  This case is not possible. *)
  unfold Basic in H.
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  destruct M as (M & prfM); simpl in H.
  destruct P1, x; simpl in H; try discriminate.
  destruct x1, x2; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  inversion H6; inversion H8.
  (* Case in which the two processes are not related; obvious contradiction. *)
  simpl in H; contradiction.
  (* Converse proof; should be mostly the same as the forward proof. *)
  unfold Simulation; intros.
  destruct H as [Pair | Pair].
  destruct Pair as [QH PH].
  rewrite PH in H0.
  inversion H0; subst; [inversion H | inversion H | inversion H | inversion H | inversion H | inversion H | | rewrite <- H in H2; inversion H2; subst; inversion H4].
  inversion H2; subst; rewrite H4 in H; [inversion H | inversion H | | | | | inversion H | ].
  (* First possible case: CommInter1.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc (BasicA M)) (getProc (BasicB F))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc (BasicA M)) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (BasicB F)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  destruct t, x; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m); simpl in H; try discriminate; subst.
  rewrite Bool.andb_true_r in H.
  (* Breaking down BasicB *)
  destruct Q0, x; simpl in H8; try discriminate.
  destruct t; try (rewrite Bool.andb_false_r in H8; discriminate); try (rewrite Bool.andb_false_l in H8; discriminate).
  destruct (string_dec n m); simpl in H8; try discriminate; subst.
  inversion H6; [inversion H10 | inversion H13 | inversion H9 | inversion H9 | inversion H9 | rewrite <- H9 in H11; inversion H11; inversion H16].
  (* Second possible case: CommInter2.  This is the case that works. *)
  destruct C as (C & prfC), F as (F & prfF), C, F.
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc (BasicA M)) (getProc (BasicB (CAbs "x" Nil NilClosed)))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc (BasicA M)) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (BasicB (CAbs "x" Nil NilClosed))) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  destruct t0, x; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m); simpl in H; try discriminate; subst.
  rewrite Bool.andb_true_r in H.
  (* Breaking down BasicB *)
  destruct Q0, x; simpl in H8; try discriminate.
  destruct t0; try (rewrite Bool.andb_false_r in H8; discriminate); try (rewrite Bool.andb_false_l in H8; discriminate).
  destruct (string_dec n m), x; simpl in H8; try discriminate; subst.
  (* Need to break down C and F0 as well. *)
  inversion H6; [inversion H13 | | inversion H9 | inversion H9 | inversion H9 | rewrite <- H9 in H11; inversion H11; inversion H16].
  inversion H7; [ | inversion H15 | inversion H14 | inversion H14 | inversion H14 | rewrite <- H14 in H16; inversion H16; inversion H21].
  subst.
  (* Need to provide the agent we commit to in the goal. *)
  exists (CARestriction "c" (CAProc ((CCon [] M 0) @R (CAbs "x" Nil NilClosed)))).
  split.
  apply (CommRes (CComposition (BasicA M) (BasicBspec (CAbs "x" Nil NilClosed) M)) (CAProc ((CCon [] M 0)  @R (CAbs "x" Nil NilClosed))) _ "c"); spitrivial.
  apply (CommInter2 (BasicA M) (BasicBspec (CAbs "x" Nil NilClosed) M) "c" (CCon [] M 0) (CAbs "x" Nil NilClosed)); spitrivial.
  unfold BasicA.
  apply (CommOut CNil M); spitrivial.
  unfold BasicBspec.
  apply (CommIn Nil _ "x" NilClosed); spitrivial.
  discriminate.
  (* Show they are related by BasicRel. *)
  (* As it is, should be able to resolve A's internal process as equivalent to BasicRel's pair. *)
  destruct A, A0; simpl in H1, H5; rewrite H5 in H1; subst.
  simpl ARestriction.
  (* Need to resolve the interaction by getting to the internal interaction instead of the closed interaction *)
  destruct M as (M & prfM), M0 as (M0 & prfM0); simpl getAbs; simpl getTerm.
  right; left; split; simpl.
  trivial.
  simpl in H13, H18.
  inversion H13; inversion H18; subst.
  simpl.
  rewrite Rename_aux_empty.
  apply OutputInversion in H10; destruct H10.
  destruct H5.
  destruct P1; simpl in H9.
  unfold Bool.Is_true, "=p" in H9.
  simpl in H9; destruct x0; try contradiction.
  simpl.
  apply InputInversion in H15; destruct H15.
  simpl in H10; inversion H10; subst.
  simpl in H11; destruct P2; try discriminate.
  trivial.
  (* Third possible case: CommPar1.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc (BasicA M)) (getProc (BasicB (CAbs "x" Nil NilClosed)))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc (BasicA M)) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (BasicB (CAbs "x" Nil NilClosed))) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  destruct t, x; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m); simpl in H; try discriminate; subst.
  rewrite Bool.andb_true_r in H.
  (* Breaking down BasicB *)
  destruct Q0, x; simpl in H7; try discriminate.
  destruct t; try (rewrite Bool.andb_false_r in H7; discriminate); try (rewrite Bool.andb_false_l in H7; discriminate).
  destruct (string_dec n m); simpl in H7; try discriminate; subst.
  (* Only possible case is CommOut; we determine this by inversion. *)
  inversion H6; [inversion H8 | | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | rewrite <- H8 in H10; inversion H10; inversion H15].
  apply OutputInversion in H8; destruct H8.
  (* The restriction makes this case impossible. *)
  inversion H8; subst; contradiction.
  (* Fourth possible case: CommPar2.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc (BasicA M)) (getProc (BasicB (CAbs "x" Nil NilClosed)))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc (BasicA M)) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (BasicB (CAbs "x" Nil NilClosed))) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  destruct t, x; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m); simpl in H; try discriminate; subst.
  rewrite Bool.andb_true_r in H.
  (* Breaking down BasicB *)
  destruct Q0, x; simpl in H7; try discriminate.
  destruct t; try (rewrite Bool.andb_false_r in H7; discriminate); try (rewrite Bool.andb_false_l in H7; discriminate).
  destruct (string_dec n m); simpl in H7; try discriminate; subst.
  (* CommIn is the only possible case here. *)
  inversion H6; [ | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | rewrite <- H8 in H10; inversion H10; inversion H15].
  apply InputInversion in H8; destruct H8.
  (* A solo commitment by m is impossible here due to the restriction. *)
  inversion H8; subst; contradiction.
  (* Last possible case: CommRed.  This case is not possible. *)
  unfold Basic in H.
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  destruct P1, x; simpl in H; try discriminate.
  destruct x1, x2; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct t, x1; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct t1; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  destruct (string_dec n m), (string_dec n0 m); simpl in H; try (rewrite Bool.andb_false_r in H; discriminate); try discriminate; subst.
  inversion H6; inversion H8.
  (* Next step of forward simulation proof. *)
  (* Further state examination.  May need an assumption that F contains no possible commitments. *)
  destruct Pair as [Pair | H].
  destruct Pair as [QH PH].
  rewrite PH in H0.
  inversion H0; subst; [inversion H | inversion H | inversion H | inversion H | inversion H | inversion H | | rewrite <- H in H2; inversion H2; subst; inversion H4].
  inversion H2; subst; rewrite H4 in H; [inversion H | inversion H | | | | | inversion H | ].
  (* First possible case: CommInter1.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc 0) (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc 0) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  (* Breaking down BasicB *)
  destruct M as (M & prfM); simpl in H8.
  destruct Q0, x; simpl in H8; try discriminate.
  inversion H6; [inversion H10 | inversion H13 | inversion H9 | inversion H9 | inversion H9 | rewrite <- H9 in H11; inversion H11; inversion H16].
  (* Second possible case: CommInter2.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc 0) (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc 0) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  (* Breaking down BasicB *)
  destruct M as (M & prfM); simpl in H8.
  destruct Q0, x; simpl in H8; try discriminate.
  inversion H6; [inversion H10 | inversion H10 | inversion H9 | inversion H9 | inversion H9 | rewrite <- H9 in H11; inversion H11; inversion H16].
  (* Third possible case: CommPar1.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc 0) (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc 0) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  (* Breaking down BasicB *)
  destruct M as (M & prfM); simpl in H7.
  destruct Q0, x; simpl in H7; try discriminate.
  inversion H6; [inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | rewrite <- H8 in H10; inversion H10; inversion H15].
  (* Fourth possible case: CommPar2.  This case is not possible. *)
  (* Breaking down H to infer process equivalences. *)
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  replace (eqP_aux (Composition (getProc 0) (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M))) (Composition (getProc P1) (getProc Q0)) [("c":Name, m)] []) with
  (eqP_aux (getProc 0) (getProc P1) [("c":Name, m)] [] && eqP_aux (getProc (CInstantiate ((﹙ "x" ﹚ Nil) NilClosed) M)) (getProc Q0) [("c":Name, m)] [])  in H by trivial.
  apply Bool.andb_true_iff in H; destruct H.
  (* Breaking down BasicA *)
  destruct P1, x; simpl in H; try discriminate.
  (* Breaking down BasicB *)
  destruct M as (M & prfM); simpl in H7.
  destruct Q0, x; simpl in H7; try discriminate.
  inversion H6; [inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | inversion H8 | rewrite <- H8 in H10; inversion H10; inversion H15].
  (* Last possible case: CommRed.  This case is not possible. *)
  unfold Basic in H.
  apply RestrictionInversion in H.
  rewrite 2?getProcComp in H.
  destruct M as (M & prfM); simpl in H.
  destruct P1, x; simpl in H; try discriminate.
  destruct x1, x2; try (rewrite Bool.andb_false_r in H; discriminate); try (rewrite Bool.andb_false_l in H; discriminate).
  inversion H6; inversion H8.
  (* Case in which the two processes are not related; obvious contradiction. *)
  simpl in H; contradiction.
  (* Show that Basic and Basicspec are related. *)
  simpl; unfold Union; left; split; spitrivial.
Qed.
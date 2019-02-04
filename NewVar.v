Require Import Ascii.
Require Import String.
Require Import Omega.
Require Import List.
Import ListNotations.
Require Import FinFun.
Require Import Permutation.

(*
    First two basic properties about strings that seems to be missing in the library. Strings are not lists of ascii in coq so that the
    list properties do not apply.
*)

(* Module NewVar. *)

Open Scope string_scope.

Lemma string_app_nil_r : forall s, s ++ "" = s.
Proof.
  induction s; simpl; intros.
  trivial.
  rewrite IHs; trivial.
Qed.

Lemma string_app_inv_head : forall (s s1 s2 : string), s ++ s1 = s ++ s2 -> s1 = s2.
Proof.
  intros.
  induction s; simpl in H; intros.
  assumption.
  apply IHs; inversion H; trivial.
Qed.

Close Scope string_scope.

(*
    Now some additional properties that we will need later.
*)

Section PermutationProps.

Variable b : Type.
Variable f : nat -> b.

Lemma permutatedSequence : forall m n, Permutation (f n :: map f (seq (S n) m)) (f (m+n) :: map f (seq n m)).
Proof.
induction m; simpl; intros.
trivial.
apply (Permutation_trans (perm_skip (f n) (IHm (S n)))).
rewrite Nat.add_succ_r.
apply perm_swap.
Qed.

Lemma indexedElementsPermutated (inj : Injective f) : forall l, (forall n, n < length l -> In (f n) l) -> Permutation (map f (seq 0 (length l))) l.
Proof.
cut (forall m l, length l = m -> (forall n : nat, n < m -> In (f n) l) -> Permutation (map f (seq 0 m)) l).
intros; apply H; [ trivial | assumption ].
induction m; intros; simpl.
apply length_zero_iff_nil in H; rewrite H; trivial.
case_eq l; intros.
rewrite H1 in H; simpl in H; apply Nat.neq_0_succ in H; contradiction.
apply (Permutation_trans (permutatedSequence m 0)).
rewrite Nat.add_0_r.
rewrite H1 in H0; simpl in H0.
assert (H2 := H0 m (Nat.lt_succ_diag_r m)); destruct H2.
rewrite H2.
apply perm_skip.
apply IHm; intros.
rewrite H1 in H; simpl in H.
apply Nat.succ_inj; assumption.
assert (H4 := H0 n (Nat.lt_lt_succ_r _ _ H3)); destruct H4.
rewrite H4 in H2; apply inj in H2; rewrite H2 in H3.
apply Nat.lt_irrefl in H3; contradiction.
assumption.
apply in_split in H2; destruct H2 as [l1 H2], H2 as [l2 H2].
rewrite H2.
apply Permutation_sym, (Permutation_trans (Permutation_sym (Permutation_middle (b0::l1) l2 (f m)))), perm_skip, Permutation_sym.
apply IHm; simpl.
rewrite H1 in H; simpl in H; apply Nat.succ_inj in H.
rewrite H2 in H; rewrite app_length in H; simpl in H; rewrite Nat.add_succ_r in H.
rewrite app_length; assumption.
intros.
assert (H4 := H0 n (Nat.lt_lt_succ_r _ _ H3)); destruct H4.
left; assumption.
right; apply in_app_iff.
rewrite H2 in H4.
apply in_app_iff in H4; simpl in H4.
destruct H4.
left; assumption.
destruct H4.
apply inj in H4; rewrite H4 in H3; apply Nat.lt_irrefl in H3; contradiction.
right; assumption.
Qed.

Lemma in_map_injective (inj : Injective f) : forall n l, In (f n) (map f l) <-> In n l.
Proof.
intros.
induction l; simpl.
reflexivity.
split; intros; destruct H.
apply inj in H; left; assumption.
apply IHl in H; right; assumption.
rewrite H; left; trivial.
apply IHl in H; right; assumption.
Qed.

End PermutationProps.

(* 
    The first part about reading and printing numbers is taken from
    http://poleiro.info/posts/2013-03-31-reading-and-writing-numbers-in-coq.html
*)

Open Scope char_scope.

Definition digitToNat (c : ascii) : option nat :=
  match c with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | _ => None
  end.

Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Theorem digitToNatNatToDigit : forall n : nat, n < 10 -> digitToNat (natToDigit n) = Some n.
Proof.
  intros n H.
  repeat match goal with
          | n : nat |- _ =>
            destruct n; [reflexivity|try omega]
         end.
Qed.

Theorem digitToNatNatToDigitMod : forall n : nat, digitToNat (natToDigit (n mod 10)) = Some (n mod 10).
Proof.
  intros n. 
  apply digitToNatNatToDigit.
  apply Nat.mod_upper_bound.
  congruence.
Qed.

Close Scope char_scope.

Open Scope string_scope.

Fixpoint readNatAux (s : string) (acc : nat) : option nat :=
  match s with
    | "" => Some acc
    | String c s' =>
      match digitToNat c with
        | Some n => readNatAux s' (10 * acc + n)
        | None => None
      end
  end.

Definition readNat (s : string) : option nat := readNatAux s 0.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition writeNat (n : nat) : string :=  writeNatAux n n "".

Theorem readNatWriteNat' : (forall time n acc,  n <= time -> readNatAux (writeNatAux time n acc) 0 = readNatAux acc n) -> forall n, readNat (writeNat n) = Some n.
Proof.
  intros H n.
  unfold readNat, writeNat.
  rewrite H; trivial.
Qed.

Lemma div_10_le : forall n time, n <= S time -> n / 10 <= time.
Proof.
  intros [|n] time H. simpl. omega.
  assert (S n / 10 < S n); try omega.
  apply Nat.div_lt; omega.
Qed.

Lemma readNatAuxWriteNatAux : forall time n acc,  n <= time -> readNatAux (writeNatAux time n acc) 0 = readNatAux acc n.
Proof.
  intros time.
  induction time as [|time' IHtime]; intros n acc H.
  simpl; inversion H; reflexivity.
  apply div_10_le in H; unfold writeNatAux.
  destruct (n / 10) as [|n'] eqn:En';[|rewrite IHtime; auto]; unfold readNatAux; try rewrite digitToNatNatToDigitMod; try rewrite (Nat.div_mod n 10) at 2; try omega; congruence.
Qed.

Theorem readNatWriteNat :  forall n, readNat (writeNat n) = Some n.
Proof.
  apply readNatWriteNat'.
  apply readNatAuxWriteNatAux.
Qed.

(* 
   The following theorems are new and not on the web page mentioned above.
*)

Theorem writeNatInjective : Injective writeNat.
Proof.
  unfold Injective; intros m n H.
  apply (f_equal readNat) in H.
  rewrite 2?readNatWriteNat in H.
  inversion H; trivial.
Qed.

Close Scope string_scope.

Open Scope char_scope.

Lemma writeNatAuxFirstChar : forall time n acc, n <= time -> exists a s m, writeNatAux time n acc = String a s /\ digitToNat a = Some m.
Proof.
  induction time; intros.
  inversion H; simpl.
  exists "0",  acc, 0; intuition.
  unfold writeNatAux.
  destruct (n / 10) as [|n'] eqn:En'.
  exists (natToDigit (n mod 10)), acc, (n mod 10).
  rewrite digitToNatNatToDigit; [| apply Nat.mod_upper_bound ]; intuition.
  fold (writeNatAux time n acc).
  apply IHtime.
  case_eq (n <? 10); intros.
  apply Nat.ltb_lt in H0.
  rewrite (Nat.div_small _ _ H0) in En'; inversion En'.
  apply Nat.ltb_ge in H0.
  rewrite <- En'.
  rewrite (Nat.div_le_mono n (S time)); [|intuition|assumption].
  apply Nat.div_le_upper_bound; [intuition|].
  rewrite H in H0.
  assert (H1 : forall m, m > 0 -> S m <= 10 * m).
  induction m; intros.
  inversion H1.
  case_eq (m =? 0); intros.
  apply Nat.eqb_eq in H2.
  rewrite H2; intuition.
  apply Nat.eqb_neq in H2.
  replace (10 * S m) with (S (10 * m + 9)) by intuition.
  rewrite <- Nat.succ_le_mono, IHm; intuition.
  apply H1; intuition.
Qed.

Close Scope char_scope.

Lemma writeNatFirstChar : forall n, exists a s m, writeNat n = String a s /\ digitToNat a = Some m.
Proof.
  intros.
  unfold writeNat.
  apply writeNatAuxFirstChar; reflexivity.
Qed.

(*
    In the following section we define a function findNumAux m n l that finds a number p so that the following two properties
    are true:
    1) For all q with  m-n <= q < p the values f q : b are in the list l.
    2) f q is either not in l or f q = m.
    The variable n is used for the recursion. With the appropriate initializations of m and n, i.e. using length l, we will later define
     the function findNum.
*)

Section FindNum.

Variable b : Type.
Variable eq_dec : forall x y : b, {x = y} + {x <> y}.
Variable f : nat -> b.

Fixpoint findNumAux (m n : nat) (l : list b) : nat :=
  match n with
   | 0 => m
   | S n' => if in_dec eq_dec (f (m-n)) l then findNumAux m n' l else m-n
 end.

Lemma findNumAuxUpperBound : forall m n l, findNumAux m n l <= m.
Proof.
  intros; induction n; simpl.
  reflexivity.
  case (in_dec eq_dec (f (m - S n)) l); intros.
  assumption.
  apply Nat.le_sub_l.
Qed.

Lemma findNumAuxProp1 : forall m n q l, m-n <= q < findNumAux m n l -> In (f q) l.
Proof.
  intros.
  induction n; simpl.
  rewrite Nat.sub_0_r in H; destruct H.
  rewrite <- (findNumAuxUpperBound m 0 l) in H.
  apply (Nat.le_lt_trans _ _ _ H), Nat.lt_irrefl in H0; contradiction.
  destruct H.
  assert (H1 : q = m - S n \/ m - n <= q). 
  rewrite Nat.sub_succ_r, Nat.le_pred_le_succ, Nat.le_succ_r in H.
  destruct H.
  right; assumption.
  left.
  rewrite Nat.sub_succ_r.
  apply f_equal_pred in H.
  rewrite Nat.pred_succ in H.
  symmetry; assumption.
  simpl in H0.
  case_eq (in_dec eq_dec (f (m - S n)) l); intros.
  rewrite H2 in H0.
  destruct H1.
  rewrite H1; assumption.
  apply (IHn (conj H1 H0)); split; assumption.
  rewrite H2 in H0.
  destruct H1.
  rewrite H1 in H0; apply Nat.lt_irrefl in H0; contradiction.
  apply (Nat.le_lt_trans _ _ _ H) in H0; apply Nat.lt_irrefl in H0; contradiction.
Qed.

Lemma findNumAuxProp2 : forall m n l, ~In (f (findNumAux m n l)) l \/ findNumAux m n l = m.
Proof.
intros.
induction n; simpl.
right; trivial.
case (in_dec eq_dec (f (m - S n)) l); intros; [|left]; assumption.
Qed.

(*
    Now we define findNum by using findNumAux.
*)

Definition findNum (l : list b) : nat := findNumAux (length l) (length l) l.

Theorem findNumProp1 (inj : Injective f): forall l, ~In (f (findNum l)) l.
Proof.
intros l H.
unfold findNum in H.
assert (H0 := findNumAuxProp2 (length l) (length l) l).
destruct H0.
contradiction.
assert (H1 : forall q, q < length l -> In (f q) l).
intros.
apply (findNumAuxProp1 (length l) (length l)).
rewrite Nat.sub_diag.
split; [apply Nat.le_0_l | rewrite H0; assumption].
unfold findNum in H; rewrite H0 in H.
apply (indexedElementsPermutated _ _ inj) in H1.
apply Permutation_sym in H1.
apply (Permutation_in _ H1) in H.
apply (in_map_injective _ _ inj) in H.
apply in_seq in H.
destruct H.
simpl in H2.
apply Nat.lt_irrefl in H2; contradiction.
Qed.

End FindNum.

(*
     Now, we define a function to remove digits at the end of a string and prove two properties about it.
 *)

Open Scope string_scope.

Fixpoint removeNums (s : string) : string :=
  match s with
    | "" => ""
    | String c s' => 
      match (digitToNat c) with
         | Some _ => ""
        |  None  => String c (removeNums s')
     end
end.

Lemma removeNumsProp1 : forall s1 s2, removeNums (removeNums s1 ++ s2) = removeNums s1 ++ removeNums s2.
Proof.
  intros.
  induction s1; simpl; intros.
  trivial.
  case_eq (digitToNat a); simpl; intros.
  trivial.
  rewrite H, IHs1; trivial.
Qed.

Lemma removeNumsProp2 : forall n, removeNums (writeNat n) = "".
Proof.
  intros.
  assert (H := writeNatFirstChar n).
  do 4 destruct H.
  rewrite H; simpl; rewrite H0; trivial.
Qed.

(*
    Finally, we define the function newVar based on findNum and removeNums and show the two main properties.
*)

Definition newVar (s : string) (l : list string) : string := 
  let s' := removeNums s in
  let f := fun n => s' ++ writeNat n in
  f (findNum _ string_dec f l).

Theorem newVarProp1 : forall s l, removeNums s = removeNums (newVar s l).
Proof.
  intros.
  unfold newVar; simpl.
  rewrite removeNumsProp1.
  rewrite removeNumsProp2.
 rewrite string_app_nil_r; trivial.
Qed.

Theorem newVarProp2 : forall s l, ~In (newVar s l) l.
Proof.
intros.
unfold newVar.
apply (findNumProp1 _ string_dec (fun n : nat => removeNums s ++ writeNat n)).
unfold Injective; intros.
apply string_app_inv_head, writeNatInjective in H; assumption.
Qed.

Close Scope string_scope.

(* Some Example *)

Open Scope string_scope.

Eval compute in newVar "x1" ["x1";"y";"x0";"x3"].
Eval compute in newVar "x" ["x0";"x1";"y"].
Eval compute in newVar "x0" ["x1";"x0"].

Close Scope string_scope.

(* End NewVar. *)

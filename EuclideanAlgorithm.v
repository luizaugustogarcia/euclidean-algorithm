Require Import Arith.
Require Import Coq.Program.Wf.
Require Import Compare_dec.
Require Import EqNat.
Require Import Peano_dec.
Require Import Le.
Require Import Div2.
Require Import Lia.
Require Import Even.
Require Import Modulo.
Require Import Arithmetic.

Section euclidean_algorithm.

(* Returns the ith remainder of the process of computing the greatest common divisor between two numbers a and b *)
Fixpoint ith_r (a b i:nat) {struct i} : nat :=
match i with
| 0 => match b with
       | 0 => 0
       | S b' => modulo a b
       end
| S i' => match b with
          | 0 => 0
	  | S b' => ith_r b (modulo a b) i'
	  end
end.

Fixpoint quotient (a b: nat) : nat := 
match a with
| 0 => 0
| S n => match b with
         | 0 => 0
         | S m => if (le_gt_dec m n) then
                     S (quotient (n - m) (S m)) 
                  else
		     0
         end
end.

(* ith quotient *)
Definition ith_q (a b i:nat) : nat :=
match i with 
| 0 => quotient a b
| S k => match k with
		   | 0 => quotient b (ith_r a b 0)
		   | S l => quotient (ith_r a b l) (ith_r a b k)
		 end
end.

Theorem quotient_zero: forall a b, quotient a b = 0 -> a = 0 \/ b = 0 \/ b > a.
Proof.
   intros a b. induction a; auto.
   induction b; auto.
   simpl. case (le_gt_dec b a). intros.
   assert (forall n, ~ S n = 0).
   auto with arith. apply H0 in H; contradiction.
   intros. right. right. auto with arith.
Qed.

(* r_i = r_(i+1) * q_(i+2) + r_(i+2) *) 
Hypothesis equation: forall a b i, ith_r a b i = ith_r a b (S i) * ith_q a b (S (S i)) + ith_r a b (S (S i)).

(* If r_{i} > 0 we can conclude that the next quotient q_{i+1} = 1 and there 
   will be an r_{i+1} > 0 or q_{i+1} > 1 (in this case we cannot say anything 
   about r_{i}, which can be greater than or equal to zero). This conclusion 
   comes from the fact that q_{i+1} = floor(q_{i-1}/q_{i}) *) 
Hypothesis ith_r_ith_q: forall a b i, ith_r a b (S i) > 0 -> (ith_q a b (S (S i)) = 1 /\ ith_r a b (S (S i)) > 0) \/ ith_q a b (S (S i)) > 1.

(* r_(i+1) > 0 -> r_(i+2) < r_(i+1) *) 
Theorem inequality_aux: forall a b i, ith_r a b (S i) > 0 -> ith_r a b (S i) < ith_r a b i.
Proof.
   intros a b i H. generalize (equation a b i).
   intro eq. rewrite eq. clear eq.
   generalize H. apply ith_r_ith_q in H. elim H.
   intros. clear H. generalize H0.
   apply proj1 in H0. intros.
   apply proj2 in H2. rewrite H0.
   lia. intros.
   apply mult_plus_2; assumption.
Qed.

Theorem inequality: forall a b i, ith_r a b (S i) <= ith_r a b i.
Proof.
  intros a b i; case (zerop (ith_r a b (S i))).
  intro H; rewrite H. auto with arith.
  assert (H := inequality_aux a b i).
  intro H1.
  apply lt_le_weak in H.
  assumption. assumption.
Qed.

Theorem ith_q_zero: forall a b i, ith_q a b (S (S i)) = 0 -> ith_r a b i = 0 \/ ith_r a b (S i) = 0. 
Proof.
   intros a b i. unfold ith_q.
   intro H; apply quotient_zero in H. elim H.
   auto. intro H0; elim H0. auto.
   intro H1. assert (H2 := inequality a b i).
   lia.
Qed.

Theorem quotient_b_gt_a_0: forall a b, b > a -> quotient a b = 0.
Proof.
   intros. induction a. simpl.
   reflexivity. induction b. simpl.
   reflexivity. simpl. apply gt_S_n in H.
   case (le_gt_dec b a). intros.
   generalize (gt_not_le b a).
   intros. apply H0 in H. contradiction.
   trivial.
Qed.

Theorem a_gt_b_double_b_gt_a_quotient_1: forall a b, a > b -> 2 * b > a -> quotient a b = 1.
Proof.
  intros a b H.
  (* cases where a = 0 and b = 0 contradict the premises *)
  induction a. apply lt_n_O in H.
  contradiction. induction b. 
  simpl. intro. apply lt_n_O in H0. contradiction. 
  (* cases where a >= 1 and b >= 1 *)
  unfold double. intros.
  assert ((S b) > (a - b)).
  lia. simpl. apply lt_S_n in H.
  case (le_gt_dec b a).
  intros.
  (* from the premises we know that (S b) > (a - b), 
     so (quotient (a - b) (S b)) = 0 *)
  replace (quotient (a - b) (S b)) with 0.
  reflexivity. Focus 2. intros. apply gt_asym in g.
  unfold gt in g. contradiction. symmetry.
  apply quotient_b_gt_a_0.
  assumption.
Qed.

(* Main theorem *)
Theorem euclidean_algorithm_log_min_a_b: forall a b i, 2 * ith_r a b (S (S i)) <= ith_r a b i.
Proof.
  intros a b i; elim (le_gt_dec (2 * ith_r a b (S i)) (ith_r a b i)).
  (* Caso 2 * ith_r a b (S i) <= ith_r a b i *)
  intro H; apply le_trans with (2 * ith_r a b (S i)).
  apply mult_le_compat_l. 
  apply inequality. assumption.
  (* Caso 2 * ith_r a b (S i) > ith_r a b i *)
  intro H. case (lt_eq_lt_dec  (ith_q a b (S (S i))) 1).
  intro H1. destruct H1.
  (* ith_q a b (S (S i)) < 1 *)
  apply lt_1_eq_0 in l.
  assert (eq := equation a b i).
  apply mult_plus_0 in eq.
  rewrite <- eq.
  elim (ith_q_zero a b i).
  intro H0. rewrite H0. lia.
  intro H0. rewrite H0 in H. 
  apply lt_n_O in H. contradiction.
  assumption. assumption.
  (* ith_q a b (S (S i)) = 1 *)
  replace (ith_r a b i) with (2 * ith_r a b i - ith_r a b i).
  assert (eq := (equation a b i)). rewrite e in eq.
  rewrite mult_1_r in eq.
  replace (ith_r a b (S (S i))) with (ith_r a b i - ith_r a b (S i)).
  rewrite mult_minus_distr_l. lia.
  lia. lia.
  (* ith_q a b (S (S i)) > 1 *)
  intro H1. 
  assert (2 * ith_r a b (S i) <= ith_r a b i).
  apply le_trans 
  with (2 * ith_r a b (S i) + ith_r a b (S (S i))).
  apply le_plus_l.
  assert (eq := (equation a b i)). 
  rewrite eq. rewrite mult_comm at 1.
  apply mult_plus_leq. auto with arith.
  apply False_ind.
  apply not_gt_and_leq 
  with (n:=(2 * ith_r a b (S i)))
       (p:=(ith_r a b i));
  assumption.
Qed.

End euclidean_algorithm.

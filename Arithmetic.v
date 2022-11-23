Require Import Arith.
Require Import Lia.
Require Import Even.
Require Import Div2.

Theorem mult_plus_gt_0: forall a b c, a > 0 -> b > 0 -> a * b + c > 0.
Proof.
   intros. induction a. 
   apply gt_irrefl in H; contradiction.
   induction b. apply gt_irrefl in H0; contradiction.
   induction c; simpl; apply gt_Sn_O.
Qed.

Theorem mult_plus: forall a b c, a > 0 -> b > 0 -> c > 0 -> a < a * b + c.
Proof.
   intros. inversion H0. lia.
   apply lt_plus_trans.
   rewrite <- mult_1_l with (n:=a).
   replace (1 * a * S m) with ((S m) * a).
   apply mult_lt_compat_r. lia.
   assumption. induction a.
   apply gt_irrefl in H. 
   contradiction. rewrite mult_comm. 
   auto with arith.
Qed.

Theorem mult_plus_2: forall a b c, a > 0 -> b > 1 -> a < a * b + c.
Proof.
   intros. inversion H0. lia.
   apply lt_plus_trans.
   rewrite <- mult_1_l with (n:=a).
   replace (1 * a * S m) with ((S m) * a).
   apply mult_lt_compat_r. lia.
   assumption. induction a.
   apply gt_irrefl in H. 
   contradiction. rewrite mult_comm. 
   auto with arith.
Qed.


Theorem double_eveness: forall n m, n = m + m -> odd n -> False.
Proof.
   intros n m.
   case (even_plus_aux m m).
   intros. elim H. clear H.
   intros. symmetry in H1.
   rewrite H1 in H. 
   generalize H2. apply H in H2.
   clear H. intros. elim H2;
   intros; generalize H; apply proj1 in H;
   intros; generalize H; apply proj2 in H5;
   intros; apply not_even_and_odd with m;
   assumption.
Qed.

Theorem double_gt_div2: forall a b, a > div2 b -> double a > b.
Proof.
   unfold gt.
   intros. elim (even_or_odd b). 
   (* the case when b is even *)
   intros.
   generalize (plus_lt_compat_l (div2 b) a a).
   generalize H. intros. apply H2 in H1. clear H2.
   unfold double. apply lt_trans with (div2 b + a).
   generalize (plus_lt_compat_l (div2 b) a (div2 b)).
   intros. generalize H. apply H2 in H. clear H2.
   intros. generalize (even_double b). intros.
   generalize H0. apply H3 in H0. clear H3. intros.
   symmetry in H0. unfold double in H0. rewrite H0 in H.
   assumption. lia.
   (* the case when b is odd *)
   intros. generalize (plus_lt_compat_l (div2 b) a 1).
   intros. simpl in H1. rewrite odd_div2 in H1.
   generalize H. apply H1 in H. clear H1. intros. 
   generalize (plus_lt_compat_l (div2 b) a (div2 (S b))).
   intros. generalize H1. apply H2 in H1. clear H2.
   intros. generalize (plus_lt_compat_l (div2 (S b)) (S a) a).
   intros. generalize H. apply H3 in H. clear H3.
   intros. generalize (odd_double b).
   intros. generalize H0. apply H4 in H0. clear H4.
   intros. unfold double in H0. symmetry in H0.
   assert (div2 (S b) + div2 b = S (div2 b + div2 b)).
   generalize (odd_div2 b).
   intros. generalize H4. apply H5 in H4.
   clear H5. intros. symmetry in H4.
   rewrite H4. reflexivity. 
   rewrite H5 in H1. clear H5.
   rewrite H0 in H1. clear H0.
   generalize (lt_trans b (div2 (S b) + a) (a + S a)).
   intros. generalize H2. apply H0 in H1.
   intros. clear H5.
   Focus 2. lia. Focus 2. assumption.
   (* so far we have concluded that b < (a + S a), then b < (a + a) *)
   assert (a + S a = S (a + a)).
   auto with arith. rewrite H5 in H1.
   apply lt_n_Sm_le in H1. clear H5.
   apply le_lt_or_eq in H1.
   elim H1. unfold double. trivial.
   (* or b = (a + a) (contradiction, since the premise is that b is odd) *)
   intros. apply double_eveness in H5.
   contradiction. assumption.
Qed.

Theorem lt_1_eq_0: forall n, n < 1 -> n = 0.
  intros. induction n.
  reflexivity. apply lt_S_n in H.
  apply lt_n_O in H. contradiction.
Qed.

Theorem mult_plus_0: forall n m r s, n = m * r + s -> r = 0 -> n = s.
  intros. rewrite H0 in H. rewrite mult_0_r in H.
  rewrite plus_0_l in H. assumption.
Qed.

Theorem not_gt_and_leq: 
forall n p, n > p -> n <= p -> False.
Proof.
  intros.
  lia. 
Qed.

Theorem mult_plus_leq: forall n m p q, p >= m -> n * m + q <= n * p + q.
Proof.
  intros.
  apply plus_le_compat_r.
  apply mult_le_compat_l.
  auto with arith.
Qed.

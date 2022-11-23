Require Import Arith.

Fixpoint mod_ (n m1 m2 p r: nat) {struct n}: nat :=
match m1 with
   | O => match p with
             | O => 0
             | S p1 => match n with
                          | 0 => 0
                          | S n1 => (mod_ n1 m2 m2 p1 p)
                       end
          end
   | S m => match p with
               | O => r
               | S p1 => match n with
                            | 0 => 0
                            | S n1 => mod_ n1 m m2 p1 r
                         end
            end
end.

Definition modulo n m := 
match m with
   | O => O 
   | S m1 => mod_ n m m1 n n 
end.

(* Auxiliary theorem stating that any number modulo m (m > 0) is less than the number m *)
Theorem mod__lt: forall n m1 m2 p r, p <= n -> m1 <= S m2 -> r + m1 = p + S m2 -> mod_ n m1 m2 p r < (S m2).
Proof.
  intros n; elim n; simpl; auto.
  intros m1 m2 p r; case p.
  intros _; case m1; auto with arith.
  intros m _ H; rewrite plus_0_l in H; rewrite <- H; auto with arith.
  apply le_lt_trans with (r + 0); auto with arith.
  intros n1 H; contradict H; auto with arith.
  intros n1 Rec m1 m2 p; case m1; case p;
   repeat (rewrite mult_1_l || rewrite plus_0_l || rewrite plus_0_r);
   auto with arith.
  intros p1 r H1 H2 H3; apply Rec; auto with arith.
  rewrite <- plus_n_Sm; auto.
  intros m r _ _ H; rewrite <- H; auto with arith.
  apply le_lt_trans with (r + 0); auto with arith.
  intros p1 m r H H1 H2.
  apply Rec; auto with arith.
  apply eq_add_S.
  rewrite plus_n_Sm; auto.
Qed.

Theorem mod_lt: forall n m, 0 < m -> modulo n m < m.
Proof.
  intros n m; case m; simpl; auto with arith.
  intros m1 H; apply mod__lt; auto with arith.
Qed.

Theorem mod_gt_0: forall a b, modulo a b > 0 -> 0 < b.
Proof.
   intros a b. 
   destruct b; auto with arith.
Qed.

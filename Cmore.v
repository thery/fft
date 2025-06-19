From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Reals  Psatz.
From Coquelicot Require Import Coquelicot.
Require Import Rmore.

Open Scope C_scope.

Definition C0 := RtoC 0.

(* Addition to complex *)

Lemma RtoC_conj x : Cconj (RtoC x) = RtoC x.
Proof. by congr (_, _); rewrite /= Rsimp01. Qed.

Lemma Cminus_0_r c : c - 0 = c.
Proof. by ring. Qed.

Lemma Cdiv_0_l c : 0 / c = 0.
Proof. by rewrite /Cdiv Cmult_0_l. Qed.

Lemma Ci_neq_0 : Ci <> 0.
Proof. by intros H; inversion H; lra. Qed.

Lemma Copp_neq_0 (c : C) : c <> 0 -> - c <> 0.
Proof. by move=> c_neq0 Nc_eq0; case: c_neq0; ring [Nc_eq0]. Qed.

Fact cmodz (a b : R) : Cmod ((a + Ci * b) * (a + Ci * b)) = (Rsqr a + Rsqr b)%R.
Proof. rewrite Cmod_mult /Cmod sqrt_sqrt /Rsqr /=; nra. Qed.

Lemma Cmod_Ci : Cmod Ci = 1.
Proof. by rewrite -sqrt_1; congr (sqrt _); rewrite /Ci /=; lra. Qed.

Lemma Cinv_0 : / 0 = 0.
Proof.
  by congr (_,_); rewrite /= Rmult_0_l Rplus_0_r /Rdiv ?Rinv_0 Rmult_0_r.
Qed.

Lemma Cdiv_0_r z : z / 0 = 0.
Proof. by rewrite /Cdiv Cinv_0 Cmult_0_r. Qed.

Lemma Cmod_sqr z : (Cmod z * Cmod z =  z.1 * z.1 + z.2 * z.2)%R.
Proof. by rewrite sqrt_sqrt //=; nra. Qed.

Lemma Cmod_minus z1 z2 : (Cmod z1 - Cmod z2)%R <= Cmod (z1 + z2)%C.
Proof.
have := Cmod_triangle (z1 + z2)%C (- z2)%C.
have-> : (z1 + z2 + - z2)%C = z1 by ring.
rewrite Cmod_opp; lra.
Qed.

Lemma CmodJ z  : Cmod (/ z) = (/ (Cmod z))%R.
Proof.
apply: eq_sqrt; first by apply: Cmod_ge_0.
  by apply: Rinv_0_le_compat; apply: Cmod_ge_0.
rewrite -Rinv_mult !Cmod_sqr.
case: z => x y /=; rewrite !Rmult_1_r.
have [->|Hprod] := Req_dec (x * x + y * y) 0.
  by rewrite /Rdiv Rinv_0; lra.
by field.
Qed.

Lemma Cmod_conj (z : C) : Cmod (Cconj z) = Cmod z.
Proof. by case: z => x y; rewrite /Cmod /= !Rmult_1_r Rmult_opp_opp. Qed.

Lemma Cmult_opp_opp z1 z2 : (-z1 * -z2)%C = (z1 * z2)%C.
Proof. by ring. Qed.

Lemma Cmod_abs_l (z : C) t : Cmod z <= t -> Rabs (z.1) <= t.
Proof.
move=> H; apply: Rle_trans H; apply: Rle_trans (Rmax_Cmod _).
by rewrite /Rmax; case: Rle_dec; lra.
Qed.

Lemma Cmod_abs_r (z : C) t : Cmod z <= t -> Rabs (z.2) <= t.
Proof.
move=> H; apply: Rle_trans H; apply: Rle_trans (Rmax_Cmod _).
by rewrite /Rmax; case: Rle_dec; lra.
Qed.

Lemma Copp_mult_distr_l z1 z2 : - (z1 * z2) = - z1 * z2.
Proof. by ring. Qed.

Lemma Copp_mult_distr_r z1 z2 : - (z1 * z2) = z1 * -z2.
Proof. by ring. Qed.

Lemma Copp_plus_distr z1 z2 : - (z1 + z2) = - z1 + - z2.
Proof. by ring. Qed.

Lemma Cmult_minus_distr_r z1 z2 z3 : (z1 - z2) * z3 = z1 * z3 - z2 * z3.
Proof. by ring. Qed.

Lemma Cmult_minus_distr_l (z1 z2 z3 : C) : 
  (z1 * (z2 - z3))%C = (z1 * z2 - z1 * z3)%C.
Proof. by ring. Qed.

Lemma Cconj_i : Cconj (Ci) = - Ci.
Proof. by congr (_, _) => /=; lra. Qed.

Lemma Cdiv_1_l x : 1 / x = / x.
Proof. by rewrite [(_ / _)%C]Cmult_1_l. Qed.

Lemma Cinv_1 : / 1 = 1.
Proof. by congr (_, _) => /=; lra. Qed.

Lemma Cdiv_1_r x : x / 1 = x.
Proof. by rewrite /Cdiv Cinv_1 Cmult_1_r. Qed.

Lemma Cminus_0_l x : x - 0 = x.
Proof. by ring. Qed.

Lemma Cminus_x_x x : x - x = 0.
Proof. by ring. Qed.

Lemma Cmult_N1_l c : (-1 * c = -c).
Proof. by ring. Qed.

Lemma Cmult_N1_r c : (c * -1 = -c).
Proof. by ring. Qed.

Definition Csimp01 := (Cmult_0_l, Cmult_0_r, Cmult_1_l, Cmult_1_r,
                       Cminus_0_l, Cminus_0_r, Cplus_0_l, Cplus_0_r, Copp_0,
                       Cminus_x_x, Cmult_N1_r, Cmult_N1_l,
                       Cinv_0, Cdiv_0_l, Cdiv_0_r, Cmod_0,
                       Cinv_1, Cdiv_1_l, Cdiv_1_r, Cmod_1).

Lemma Copp_involutive c : (- - c = c)%C.
Proof. by ring. Qed.

Lemma Cpow2_eq1_inv c : (c ^ 2 = 1)%C -> (c = 1 \/ c = -1).
Proof.
move/Ceq_minus => Hc.
have H : ((c - (-1)) * (c - 1) = 0)%C by rewrite -Hc; ring.
case: (Ceq_dec (c - 1) 0) => // Hc1; first by left; apply/Ceq_minus.
case: (Ceq_dec (c - (-1)) 0) => // Hc2; first by right; apply/Ceq_minus.
by case (Cmult_neq_0 _ _ Hc2 Hc1).
Qed.

Lemma Cpow4_eq1_inv c : (c ^ 4 = 1 -> [\/ c = 1, c = -1, c = Ci | c = - Ci])%C.
Proof.
move/Ceq_minus => Hc.
have F : ((c - 1) * (c - (-1)) * (c - Ci) * (c - (- Ci)) = 0)%C.
  have F : (Ci * Ci = -1)%C by congr (_, _) => /=; ring.
  rewrite -Hc; ring[F].
case: (Ceq_dec  ((c - 1)) 0) => // Hc1; first by apply/Or41/Ceq_minus.
case: (Ceq_dec  ((c - -1)) 0) => // Hc2; first by apply/Or42/Ceq_minus.
case: (Ceq_dec  ((c - Ci)) 0) => // Hc3; first by apply/Or43/Ceq_minus.
case: (Ceq_dec  ((c - - Ci)) 0) => // Hc4; first by apply/Or44/Ceq_minus.
have F2 := Cmult_neq_0 _ _ Hc1 Hc2.
have F3 := Cmult_neq_0 _ _ F2 Hc3.
by have [] := Cmult_neq_0 _ _ F3 Hc4.
Qed.

Lemma Cconj0 : Cconj 0 = 0.
Proof. by congr (_, _); rewrite Ropp_0. Qed.

Definition Cexpi a : C := (cos a, sin a).

Lemma Cexpi0 : Cexpi 0 = 1.
Proof. by apply: injective_projections; rewrite /= (sin_0, cos_0). Qed.

Lemma CexpiPI : Cexpi PI = - 1.
Proof. by apply: injective_projections; rewrite /= (sin_PI, cos_PI). Qed.

Lemma Cexpi2PI : Cexpi (2 * PI) = 1.
Proof. by apply: injective_projections; rewrite /= (sin_2PI, cos_2PI). Qed.

Lemma Cexpi_plus a b : Cexpi (a + b) = Cexpi a * Cexpi b.
Proof.
apply: injective_projections; [apply: cos_plus|rewrite /=].
by rewrite sin_plus Rplus_comm.
Qed.

Lemma Cexpi_ntimes (n : nat) a : Cexpi (INR n * a) = (Cexpi a) ^ n.
Proof.
elim: n => [/=|n IH]; first by rewrite Rmult_0_l Cexpi0.
by rewrite S_INR /= -IH -Cexpi_plus; congr (Cexpi _); lra.
Qed.

Definition Croot n := Cexpi (2 * PI / INR n).

Lemma Croot0 : Croot 0 = 1.
Proof. by rewrite /Croot /Rdiv INR_0 Rinv_0 Rmult_0_r Cexpi0. Qed.

Lemma Croot_expn (n : nat) : (Croot n) ^ n = 1.
Proof.
case: n => [//|n].
rewrite -Cexpi_ntimes -Cexpi2PI; congr (Cexpi _).
by field; apply: not_0_INR; lia.
Qed.

Lemma Croot_expn_eq1 n m : (0 < m <= n)%nat -> (Croot n) ^ m = 1 -> m = n.
Proof.
move=> mB; rewrite -Cexpi_ntimes => Hc.
have PI2_1 := PI2_1.
have m_pos : 0 < INR m.
  by rewrite -INR_0; apply/lt_INR/ltP; case/andP: mB.
have n_pos : 0 < INR n.
  by rewrite -INR_0; apply/lt_INR/ltP/(leq_trans _ (_ : m <= n)%nat); 
     case/andP: mB.
have /sin_eq_0_0 [k Hk] : sin  (INR m * (2 * PI / INR n)) = 0 by case: Hc.
case: k Hk => [|mk|mk].
- rewrite Rmult_0_l => /Rmult_integral[]; first by lra.
  move/Rmult_integral=> []; first by lra.
  by have := Rinv_neq_0_compat (INR n); lra.
- have -> : IZR (Z.pos mk) = INR (Pos.to_nat mk).
    by rewrite INR_IZR_INZ Znat.positive_nat_Z.
  have mk_pos : 0 < INR (Pos.to_nat mk).
    by rewrite -INR_0; apply/lt_INR/Pos2Nat.is_pos.
  move=> Hmk; apply/eqP; rewrite eqn_leq.
  case/andP: mB => _ -> /=.
  have H1mk : (INR m * 2 / INR n)%R = INR (Pos.to_nat mk) by nra.
  have H2mk : (m * 2 = (Pos.to_nat mk * n))%nat.
    apply: INR_eq; rewrite mult_INR -[INR 2]/(IZR 2).
    apply: (Rdiv_eq_reg_r (INR n)); last by lra.
    by rewrite mult_INR H1mk Rmult_div_l //; lra.
  suff : (n * 2 <= m * 2)%nat by rewrite leq_mul2r.
  have /orP[/eqP mkE| mk_gt1] :
    (Pos.to_nat mk == 1%nat) || (1 < Pos.to_nat mk)%nat.
  - by have/ltP := Pos2Nat.is_pos mk; case: Pos.to_nat => //= [] [].
  - rewrite mkE mul1n in H2mk.
    have Hf : (INR m * (2 * PI / INR n) = PI)%R.
      rewrite -2!Rmult_assoc -(mult_INR _ 2) multE H2mk.
      by apply: Rmult_div_r; lra.
    rewrite Hf CexpiPI in Hc.
    by have := RtoC_inj _ _ Hc; lra.
  by rewrite H2mk mulnC leq_mul2r mk_gt1 orbT.
have -> : IZR (Z.neg mk) = (- INR (Pos.to_nat mk))%R.
  by rewrite (opp_IZR (Z.pos mk)) INR_IZR_INZ Znat.positive_nat_Z.
move=> Hmk.
suff : (0 < - INR (Pos.to_nat mk) * PI)%R.
  suff : (0 < INR (Pos.to_nat mk))%R by nra.
  by rewrite -INR_0; apply/lt_INR/Pos2Nat.is_pos.
rewrite -Hmk.
apply: Rmult_lt_0_compat => //.
by apply: Rlt_mult_inv_pos; lra.
Qed.

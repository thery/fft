(* Copyright (c)  Inria. All rights reserved. *)

Require Import Reals  Psatz.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
Require Import kahan_mult.
Require Import Rmore Cmore Fmore.

(* This is a formalisation of                                                   
   Richard P. Brent, Colin Percival, Paul Zimmermann.                          
   Error Bounds on Complex Floating-Point Multiplication.                     *)

Section Brent.

Variables  p: Z.
Variable beta : radix.
Hypothesis beta_le : (2 <= beta)%Z.
Hypothesis Hp2: Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Open Scope R_scope.

Notation u := (u p beta).
Notation u_gt_0 := (u_gt_0 p beta).

Hypothesis u_le : 2 ^ 5 * u <= 1.

Variable choice : Z -> bool.
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation iformat := (generic_formatC beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RN := (round beta fexp (Znearest choice)).
Local Notation RNC := (roundC beta fexp (Znearest choice)).
Local Notation ulp := (ulp beta fexp).

Definition normw_error2 (f ff: C -> C -> C) (z1 z2 : C) : R := 
 Cmod (((ff z1 z2) - f z1 z2) / (f z1 z2))%C.

Definition brent_imult (z1 z2 : C) : C := 
  let (x1, y1) := z1 in 
  let (x2, y2) := z2 in
  (RN (RN(x1 * x2) - RN(y1 * y2)), RN (RN (x1 * y2) + RN (y1 * x2))).

Lemma brent_imult_0_l z : brent_imult 0 z = 0.
Proof. by case: z => x y => /=; rewrite !(round_0, Rsimp01). Qed.

Lemma brent_imult_0_r z : brent_imult z 0 = 0.
Proof. by case: z => x y => /=; rewrite !(round_0, Rsimp01). Qed.

Lemma brent_imult_1_r z : brent_imult z 1 = RNC z.
Proof.
case: z => x y.
by rewrite /brent_imult /= !Rsimp01 round_0 !Rsimp01; congr (_, _);
   rewrite round_generic //; 
   apply: generic_format_round.
Qed.

Lemma brent_imult_1_l z : brent_imult 1 z = RNC z.
Proof.
case: z => x y.
by rewrite /brent_imult /= !Rsimp01 round_0 !Rsimp01; congr (_, _);
   rewrite round_generic //; 
   apply: generic_format_round.
Qed.

Lemma brent_imult_N1_r z : brent_imult z (-1) = (- RNC z)%C.
Proof.
case: z => x y.
by rewrite /brent_imult /= !Rsimp01 round_0 !Rsimp01; congr (_, _);
   rewrite -?[_ * (-1)]Ropp_mult_distr_r !RN_sym //
           ?Rsimp01 // round_generic //; apply: generic_format_round.
Qed.

Lemma brent_imult_N1_l z : brent_imult (-1) z = (- RNC z)%C.
Proof.
case: z => x y.
by rewrite /brent_imult /= !Rsimp01 round_0 !Rsimp01; congr (_, _);
   rewrite -?[(-1) * _]Ropp_mult_distr_l !RN_sym //
           ?Rsimp01 // round_generic //; apply: generic_format_round.
Qed.

Lemma brent_imult_i_r z : brent_imult z Ci = (RNC z * Ci)%C.
Proof.
case: z => x y.
by rewrite /brent_imult /= !Rsimp01 round_0 !Rsimp01; congr (_, _);
   rewrite /= !Rsimp01 ?RN_sym // round_generic //; 
   apply: generic_format_round.
Qed.

Lemma brent_imult_i_l z : brent_imult Ci z = (Ci * RNC z)%C.
Proof.
case: z => x y.
by rewrite /brent_imult /= !Rsimp01 round_0 !Rsimp01; congr (_, _);
   rewrite /= !Rsimp01 ?RN_sym // round_generic //; 
   apply: generic_format_round.
Qed.

Lemma brent_imult_Ni_r z : brent_imult z (- Ci) = (RNC z * - Ci)%C.
Proof.
case: z => x y.
   rewrite /brent_imult /= !Rsimp01 round_0 !Rsimp01; congr (_, _);
   rewrite -?[_ * (-_)]Ropp_mult_distr_r !RN_sym //
           ?Rsimp01 // round_generic //=;
            apply: generic_format_round.
Qed.

Lemma brent_imult_Ni_l z : brent_imult (-Ci) z = ((- Ci) * RNC z)%C.
Proof.
case: z => x y.
by rewrite /brent_imult /= !Rsimp01 round_0 !Rsimp01; congr (_, _);
   rewrite -?[(-_) * _]Ropp_mult_distr_l !RN_sym //
           ?Rsimp01 // round_generic //; apply: generic_format_round.
Qed.

Lemma brent_imult_pow41_l z1 z2 : 
  (z1 ^ 4 = 1 -> brent_imult z1 z2 = z1 * RNC z2)%C.
Proof.
case/Cpow4_eq1_inv => ->; first by rewrite brent_imult_1_l Csimp01.
- by rewrite brent_imult_N1_l; ring.
- by rewrite brent_imult_i_l; ring.
rewrite brent_imult_Ni_l; ring.
Qed.

Lemma brent_imult_pow41_r z1 z2 :
  (z2 ^ 4 = 1 -> brent_imult z1 z2 = RNC z1 * z2)%C.
Proof.
case/Cpow4_eq1_inv => ->; first by rewrite brent_imult_1_r Csimp01.
- by rewrite brent_imult_N1_r; ring.
- by rewrite brent_imult_i_r; ring.
rewrite brent_imult_Ni_r; ring.
Qed.

Lemma ulp_lt_half x y : ulp x < ulp y -> 2 * ulp x <= ulp y.
Proof.
have [->|x_neq_0] := Req_dec x 0; first by rewrite ulp_FLX_0; lra.
have [->|y_neq_0] := Req_dec y 0; first by rewrite ulp_FLX_0; lra.
rewrite !ulp_neq_0 //= => /lt_bpow H.
apply: Rle_trans (_ : IZR beta * pow (cexp x) <= _).
   suff : 2 <= IZR beta by have := bpow_ge_0 beta (cexp x); nra.
   by apply: IZR_le.
by rewrite -bpow_1 -bpow_plus; apply: bpow_le; lia.
Qed.

Notation relative_error_le := (relative_error_le beta Hp2 choice).

Lemma normw_errror2_brent_imult_pos x1 x2 y1 y2 :
  0 <= x1 -> 0 <= y1 -> 0 <= x2 -> 0 <= y2 -> y1 * y2 <= x1 * x2 ->
  normw_error2 Cmult brent_imult (x1, y1) (x2, y2) < sqrt 5 * u.
Proof.
move=> x1_pos y1_pos x2_pos y2_pos x1x2Ly1y2.
rewrite /normw_error2.
have sqrt_pos : 0 < sqrt 5 by apply: sqrt_lt_R0; lra.
have u_pos := u_gt_0.
have [/Cmod_eq_0[-> ->]|Cmod_x1y1_neq_0] := Req_dec (Cmod (x1, y1)) 0.
  by rewrite brent_imult_0_l !Csimp01; nra.
have [/Cmod_eq_0[-> ->]|Cmod_x2y2_neq_0] := Req_dec (Cmod (x2, y2)) 0.
  by rewrite brent_imult_0_r !Csimp01; nra.
rewrite Cmod_mult CmodJ /=.
set v := (_ - _)%C.
have [->|prod_neq0] := Ceq_dec ((x1, y1) * (x2, y2)) 0.
  by rewrite !(Cmod_0, Rsimp01); have := u_gt_0; nra.
apply/Rlt_div_l; first by apply/Rlt_gt/Cmod_gt_0.
set Cnz1z2 := Cmod (_ * _).
have Cnz1z2_pos : 0 < Cnz1z2.
  rewrite /Cnz1z2 Cmod_mult.
  have := Cmod_ge_0 (x1, y1); have := Cmod_ge_0 (x2, y2); nra.
have Hv : Rabs v.2 <=
   Rabs (RN (x1 * y2) - x1 * y2) + Rabs (RN (y1 * x2) - y1 * x2)
  + Rabs (RN(RN(x1 * y2) + RN (y1 * x2)) - (RN (x1 * y2) + RN (y1 * x2))).
  rewrite [X in X <= _]/=; split_Rabs; lra.
pose fx := x1 * y2 + y1 * x2; set gx := RN _ + _ in Hv.
have fx_pos : 0 <= fx by rewrite /fx; nra.
have gx_pos : 0 <= gx.
  have: 0 <= RN (x1 * y2) by apply: RN_ge_0 => //; nra.
  have: 0 <= RN (y1 * x2) by apply: RN_ge_0 => //; nra.
  by rewrite /gx; lra.
have F1 : Rabs (RN gx - gx) <= u * fx.
  have [Hle|Hlt] := Rle_lt_dec (ulp gx) (ulp fx); last first.
    have [k Hk] : exists k, Rabs fx < pow k <= Rabs gx.
      exists (mag beta gx - 1)%Z.
      have gx_neq0 : gx <> 0.
        move=> g_eq0; rewrite g_eq0 ulp_FLX_0 in Hlt.
        by have := ulp_ge_0 beta fexp fx; lra.
      have := lt_mag_ulp _ Hp2 _ _ Hlt.
      by have := bpow_mag_le beta gx gx_neq0; lra.
    rewrite !Rabs_right // in Hk; try lra.
    have F1 : Rabs (gx - pow k) <= u * fx.
      rewrite Rabs_right; try lra.
      have F2 := relative_error_le (x1 * y2).
      have F3 := relative_error_le (y1 * x2).
      by rewrite /fx /gx {Hv}// in Hk *; split_Rabs; try nra.
    apply: Rle_trans F1.
    rewrite -[X in _ <= X]Rabs_Ropp Ropp_minus_distr.
    have [_ ] := round_N_pt beta fexp choice gx.
    apply.
    by apply: generic_format_bpow; rewrite /fexp; lia.
  apply: Rle_trans (_ : /2 * ulp gx <= _).
    by apply: error_le_half_ulp.
  apply: Rle_trans (_ : /2 * ulp fx <= _); first by lra.
  have : ulp fx <= Rabs fx * pow (1 - p) by apply: ulp_FLX_le.
  by rewrite /u Rabs_right; lra.
have F2 : Rabs v.2 <= 2 * u * fx.
  have F2 := relative_error_le (x1 * y2).
  rewrite [X in _ <= _ * X]Rabs_right in F2; last by nra.
  have F3 := relative_error_le (y1 * x2).
  rewrite [X in _ <= _ * X]Rabs_right in F3; last by nra.
  by rewrite /fx in F1 *; lra.
have F3 : ulp (y1 * y2) <= ulp (x1 * x2) by apply: ulp_le_pos; nra.
have [CR1|CR1] := Rle_lt_dec (ulp (x1 * x2)) (ulp (RN(x1 * x2) - RN(y1 * y2))).
  (* In the paper this is wrongly < *)
  pose (fy := x1 * x2 - y1 * y2); pose (fz := x1 * x2 + y1 * y2).
  have F4 : RN (x1 * x2) - RN (y1 * y2) <= fy + u * fz.
    rewrite /fx /fy /fz.
    have F5 := relative_error_le (x1 * x2).
    rewrite [in X in _ <= X]Rabs_right in F5; last by nra.
    have F6 := relative_error_le (y1 * y2).
    rewrite [in X in _ <= X]Rabs_right in F6; last by nra.
    have := u_gt_0.
    by rewrite /fx {F1 F2 Hv}//; split_Rabs; nra.
  have F5 : RN (y1 * y2) <= RN (x1 * x2) by apply: round_le; lra.
  pose ft := 2 * x1 * x2 - y1 * y2.
  have F6 : Rabs v.1 <= u * ft + 2 * u * u * fz.
    rewrite /v [X in X <= _]/= /ft /fz.
    apply: Rle_trans (_ : 
      Rabs (RN (x1 * x2) - x1 * x2) + 
      Rabs (RN (y1 * y2) - y1 * y2) + 
      Rabs (RN(RN(x1 * x2) - RN (y1 * y2)) -
        (RN (x1 * x2) - RN (y1 * y2))) <= _).
      by split_Rabs; lra.
    apply: Rle_trans (_ : 
      /2 * ulp (x1 * x2) + /2 * ulp (y1 * y2) + 
      /2 * ulp (RN (x1 * x2) - RN (y1 * y2))
       <= _).
      by repeat apply: Rplus_le_compat; apply: error_le_half_ulp.
    apply: Rle_trans (_ : 
      /2 * ulp (y1 * y2) + ulp (RN (x1 * x2) - RN (y1 * y2)) <= _).
      by lra.
    apply: Rle_trans (_ : 
      u * (y1 * y2) + 2 * u * (RN (x1 * x2) - RN (y1 * y2)) <= _).
      have := ulp_2u beta Hp2 (y1 * y2).
      have := ulp_2u beta Hp2 (RN (x1 * x2) - RN (y1 * y2)).
      rewrite Rabs_right; last by lra.
      rewrite Rabs_right; last by nra.
      by split_Rabs; lra.
    rewrite /fz /fy in F4.
    by nra.
  apply: Rle_lt_trans 
     (_ : u * sqrt (ft * ft  + 4 *fx * fx) + 2 * u * u * fz < _).
    rewrite /Cmod.
    set xx := u * _ in F6; set zz := _ * _ in F6.
    set yy := _ * _ in F2.
    have xx_pos : 0 <= xx by rewrite /xx /ft; apply: Rmult_le_pos; nra.
    have yy_pos : 0 <= yy by apply: Rmult_le_pos; nra.
    have zz_pos : 0 <= zz by rewrite /zz /fz; apply: Rmult_le_pos; try nra.
    apply: Rle_trans
        (_ : sqrt((xx + zz) * (xx + zz) + yy * yy) <= _).
      apply: sqrt_le_1; first by nra.
        by set uu := (xx + zz); nra.
      apply: Rplus_le_compat; rewrite pow2_mult.
        apply: Rsqr_le_abs_1; try lra.
        by rewrite [X in _ <= X]Rabs_right //; lra.
      apply: Rsqr_le_abs_1; try lra.
      by rewrite [X in _ <= X]Rabs_right //; lra.
    apply: Rle_trans (sqrt_triangle_sum3 _ _ _ zz_pos) _.
    apply: Rplus_le_compat; last by rewrite -/zz; lra.
    rewrite -[u]sqrt_square; last by lra.
    rewrite -sqrt_mult; [|nra|nra].
    apply: sqrt_le_1_alt.
    by rewrite /xx /yy -/fx; lra.
  apply: Rle_lt_trans (_ : 
    u * sqrt (32/7 * (Cnz1z2 * Cnz1z2)
               - 4/7 * (x1 * y2 - x2 * y1) * (x1 * y2 - x2 * y1) 
               - /7 * (2 * x1 * x2 - 5 * y1 * y2) * (2 * x1 * x2 - 5 * y1 * y2))
   + 2 * u * u * Cnz1z2 < _).
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat; try (rewrite /fz; nra).
      apply: leq_sqrt; try lra.
      suff-> : Cnz1z2 * Cnz1z2 = fz * fz + (x1 * y2 - x2 * y1)^2.
        by set (V := _ - _); nra. 
      rewrite Cmod_sqr /fz /=; lra.
    set X1 := (_ + _); set X2 := (_ - _).
    suff -> : X1 = X2 by lra.
    rewrite /X1 /X2 /ft /fz /fy /fx Cmod_sqr /=.
    lra.
  apply: Rle_lt_trans (_ : 
    u * sqrt (32/7 * (Cnz1z2 * Cnz1z2)) + 2 * u * u * Cnz1z2 < _).
    apply: Rplus_le_compat; last by lra.
    apply: Rmult_le_compat; [lra | by apply: sqrt_ge_0| lra |].
    apply: sqrt_le_1_alt.
    set V1 := (x1 * _ - _ * _); set V2 := (_ * _ * _ - _ * _).
    by nra.
  rewrite sqrt_mult // ?sqrt_square; try nra.
  suff : sqrt (32 / 7) + 2 * u < sqrt 5.
    suff : 0 < u * Cnz1z2 by nra.
    by nra.
  suff : 2 ^ 4 * sqrt (32 / 7) + 2^5 * u < 2^4 * sqrt 5 by lra.
  have : sqrt(32 / 7) < 214 /100.
    apply: ltr_sqrt; first by lra.
    by rewrite sqrt_sqrt; lra.
  have : 223/100 < sqrt(5).
    apply: ltr_sqrt; first by lra.
    by rewrite sqrt_sqrt; lra.
  lra.
have [CR2|CR2] := Rle_lt_dec (ulp (RN(x1 * x2) - RN(y1 * y2))) (ulp (y1 * y2));
    last first.
  have F4 : Rabs (v.1) <= u * (7/4 * x1 * x2).
    rewrite /v /=.
    apply: Rle_trans (_ : 
      Rabs (RN (x1 * x2) - x1 * x2) + 
      Rabs (RN (y1 * y2) - y1 * y2) + 
      Rabs (RN(RN(x1 * x2) - RN (y1 * y2)) -
        (RN (x1 * x2) - RN (y1 * y2))) <= _).
      by split_Rabs; lra.
    apply: Rle_trans (_ : 
      /2 * ulp (x1 * x2) + /2 * ulp (y1 * y2) + /2 * 
        ulp (RN (x1 * x2) - RN (y1 * y2)) <= _).
      by repeat apply: Rplus_le_compat; apply: error_le_half_ulp.
    apply: Rle_trans (_ : 7/8 * ulp (x1 * x2) <= _).
      have := ulp_lt_half _ _ CR1.
      by have := ulp_lt_half _ _ CR2; lra.
    by have := ulp_2u beta Hp2 (x1 * x2); rewrite Rabs_right; nra.
  rewrite {1}/Cmod pow2_mult.
  apply: Rle_lt_trans (_ : 
    u * sqrt((7 / 4 * x1 * x2) * (7 / 4 * x1 * x2) + 4 * (fx * fx)) < _).
    rewrite -[u]sqrt_square; try lra.
    rewrite -sqrt_mult_alt; try nra.
    apply: sqrt_le_1_alt.
    rewrite Rmult_plus_distr_l; apply: Rplus_le_compat.
      rewrite -(Rabs_sqr v.1).
      have : 0 <= Rabs v.1 by apply: Rabs_pos.
      set V := _ * _ * x2 in F4 *; nra.
    rewrite pow2_mult -(Rabs_sqr v.2).
    have : 0 <= Rabs v.2 by apply: Rabs_pos.
    by nra.
  set X := _ + _.
  have->: X = 1024/207 * (Cnz1z2 * Cnz1z2) - 
              196/207 * (x1 * y2 - y1 * x2) * (x1 * y2 - y1 * x2) -
              /3312 * (79 * x1 * x2 - 128 * y1 * y2) * 
                      (79 * x1 * x2 - 128 * y1 * y2).
    by rewrite /X Cmod_sqr /fx /=; lra.
  apply: Rle_lt_trans (_ : u * sqrt(1024 / 207 * (Cnz1z2 * Cnz1z2)) < _).
    apply: Rmult_le_compat; [lra | by apply: sqrt_ge_0| lra |].
    apply: sqrt_le_1_alt.
    set V1 := (x1 * _ - _ * _); set V2 := (_ * _ * _ - _ * _).
    by nra.
  rewrite sqrt_mult; try nra.
  rewrite sqrt_square; try lra.
  have : sqrt (1024 / 207) < 2225/1000.
    apply: ltr_sqrt; first by lra.
    by rewrite sqrt_sqrt; lra.
  have : 223 /100  < sqrt (5).
    apply: ltr_sqrt; first by lra.
    by rewrite sqrt_sqrt; lra.
  have: 0 < u * Cnz1z2 by nra.
  by nra.
have F4 : RN(RN (x1 * x2) - RN (y1 * y2)) = RN (x1 * x2) - RN (y1 * y2).
  apply: RN_minus_ulp_le => //; try lra; try apply: generic_format_round.
    apply: Rle_trans (Rlt_le _ _ CR1) _.
    by apply: RN_ulp_le => //; nra.
  apply: Rle_trans CR2 _.
  by apply: RN_ulp_le => //; nra.
have F5 : Rabs (v.1) <=  u * (x1 * x2 + y1 * y2).
  rewrite Rmult_plus_distr_l.
  apply: Rle_trans (_ : 
    Rabs (RN (x1 * x2) - x1 * x2) + 
    Rabs (RN (y1 * y2) - y1 * y2) + 
    Rabs (RN(RN(x1 * x2) - RN (y1 * y2)) -
        (RN (x1 * x2) - RN (y1 * y2))) <= _).
    by rewrite /v /=; split_Rabs; lra.
  rewrite F4 Rminus_eq_0 !Rsimp01.
  by apply: Rplus_le_compat; rewrite -[X in _ <= _ X]Rabs_right //; try nra;
     apply: relative_error_le.
have F6 :
  x1 * x2 <> 0 \/ y1 * y2 <> 0 -> Rabs (v.1) <  u * (x1 * x2 + y1 * y2).
  move=> Hx.
  rewrite Rmult_plus_distr_l.
  apply: Rle_lt_trans (_ : 
    Rabs (RN (x1 * x2) - x1 * x2) + 
    Rabs (RN (y1 * y2) - y1 * y2) + 
    Rabs (RN(RN(x1 * x2) - RN (y1 * y2)) -
        (RN (x1 * x2) - RN (y1 * y2))) < _).
    by rewrite /v /=; split_Rabs; lra.
  rewrite F4 Rminus_eq_0 !Rsimp01.
  case: Hx => Hx.
    apply: Rplus_lt_le_compat. 
      by rewrite -[X in _ < _ X]Rabs_right; try nra;
         apply: relative_error_lt.
    by rewrite -[X in _ <= _ X]Rabs_right; try nra;
       apply: relative_error_le.
  apply: Rplus_le_lt_compat.
    by rewrite -[X in _ <= _ X]Rabs_right; try nra;
       apply: relative_error_le.
  by rewrite -[X in _ < _ X]Rabs_right; try nra;
      apply: relative_error_lt.
have [Heq | Hneq] := Req_dec (x1 * y2 - y1 * x2) 0.
  apply: Rlt_le_trans (_ : 
    u * sqrt ((x1 * x2 + y1 * y2) * (x1 * x2 + y1 * y2) + 
             4 * fx * fx) <= _).
    rewrite -[u]sqrt_square; try lra.
    rewrite -sqrt_mult; [|nra|set V := (x1 * _ + _); nra].
    rewrite Rmult_plus_distr_l.
    apply/sqrt_lt_1_alt; split; first by nra.
    apply: Rplus_lt_le_compat; rewrite pow2_mult.
      rewrite -(Rabs_sqr v.1).
      have : 0 <= Rabs v.1 by apply: Rabs_pos.
      suff /F6: x1 * x2 <> 0 \/ y1 * y2 <> 0 by nra.
      have CF z1 z2 : Cmod (z1, z2) <> 0 -> (z1 <> 0) \/ (z2 <> 0).
        have [->|z1_neq_0] := Req_dec z1 0;
        have [->|z2_neq_0] := Req_dec z2 0; try ((by left) || by right).
        by rewrite Cmod_0.
      have CF1 : (x1 <> 0 \/ y1 <> 0) by apply: CF.
      have CF2 : (x2 <> 0 \/ y2 <> 0) by apply: CF.
      have [x1_eq_0|x1_neq_0]:= Req_dec x1 0; first by nra.
      by have [x2_eq_0|x2_neq_0]:= Req_dec x2 0; nra.  
    rewrite -(Rabs_sqr v.2).
    have : 0 <= Rabs v.2 by apply: Rabs_pos.
    by nra.
  set X := _ + _.
  have-> : X = 5 * (Cnz1z2 * Cnz1z2) - 
            (x1 * y2 - y1 * x2) * (x1 * y2 - y1 * x2) -
            4 * (x1 * x2 - y1 * y2) * (x1 * x2 - y1 * y2).
    by rewrite /X Cmod_sqr /fx /=; lra.
  apply: Rle_trans (_ : u * sqrt(5 * (Cnz1z2 * Cnz1z2)) <= _).
    apply: Rmult_le_compat; [lra | by apply: sqrt_ge_0| lra |].
    apply: sqrt_le_1_alt.
    set V1 := (x1 * _ - _ * _); set V2 := (x1 * _ - _ * _).
    by nra.
  rewrite sqrt_mult; try nra.
  by rewrite sqrt_square; try lra.
apply: Rle_lt_trans (_ : 
    u * sqrt ((x1 * x2 + y1 * y2) * (x1 * x2 + y1 * y2) + 
             4 * fx * fx) < _).
  rewrite -[u]sqrt_square; try lra.
  rewrite -sqrt_mult; [|nra|set V := (x1 * _ + _); nra].
  rewrite Rmult_plus_distr_l.
  apply/sqrt_le_1_alt/Rplus_le_compat; rewrite pow2_mult.
    rewrite -(Rabs_sqr v.1).
    have : 0 <= Rabs v.1 by apply: Rabs_pos.
    by nra.
  rewrite -(Rabs_sqr v.2).
  have : 0 <= Rabs v.2 by apply: Rabs_pos.
  by nra.
set X := _ + _.
have: 0 <=  X by rewrite /X; set XX := (x1 * _ + _); nra.
have-> : X = 5 * (Cnz1z2 * Cnz1z2) - 
          (x1 * y2 - y1 * x2) * (x1 * y2 - y1 * x2) -
          4 * (x1 * x2 - y1 * y2) * (x1 * x2 - y1 * y2).
  by rewrite /X Cmod_sqr /fx /=; lra.
move=> Hx.
apply: Rlt_le_trans (_ : u * sqrt(5 * (Cnz1z2 * Cnz1z2)) <= _).
  apply: Rmult_lt_compat_l; try by lra.
  apply: sqrt_lt_1_alt; split => //.
  set V1 := (x1 * _ - _ * _) in Hneq *; set V2 := (x1 * _ - _ * _).
  by nra.
rewrite sqrt_mult; try nra.
by rewrite sqrt_square; try lra.
Qed.

Lemma normw_erroyr2_brent_imult z1 z2 :
  normw_error2 Cmult brent_imult z1 z2 < sqrt 5 * u.
Proof.
case: z1 => x1 y1; case: z2 => x2 y2.
wlog x1_pos : x1 y1 x2 y2 / 0 <= x1 => [Hx1|].
  case: (Rle_dec 0 x1) => [// | x1_neg]; first by apply: Hx1.
  suff-> : normw_error2 Cmult brent_imult (x1, y1) (x2, y2) =
           normw_error2 Cmult brent_imult (-(x1, y1))%C  (-(x2, y2))%C.
    by  apply: Hx1 => /=; lra.
  rewrite /normw_error2 /= !(Cmod_mult, CmodJ, Cmod_opp); congr (_ / _).
  by rewrite !Rmult_opp_opp Cmult_opp_opp.
wlog y1_pos : x1 y1 x2 y2 x1_pos / 0 <= y1 => [Hy1|].
  case: (Rle_dec 0 y1) => [// | y1_neg]; first by apply: Hy1.
  suff-> : normw_error2 Cmult brent_imult (x1, y1) (x2, y2) =
           normw_error2 Cmult brent_imult (Ci * (x1, y1))%C  (Ci * (x2, y2))%C.
    apply: Hy1 => /=; lra.
  rewrite /normw_error2 /= !Rsimp01.
  rewrite !(Cmod_mult, CmodJ, Cmod_opp, Cmod_Ci); congr (_ / _); last first.
    by ring.
  rewrite Rmult_opp_opp -!(Ropp_mult_distr_l, Ropp_mult_distr_r) //.
  rewrite !RN_sym // -Ropp_plus_distr.
  rewrite -[in LHS]Cmod_opp Ropp_plus_distr Copp_plus_distr.
  congr (Cmod ((_, _) - _)) => /=.
  - by rewrite -RN_sym //; congr (RN _); lra.
  - rewrite -RN_sym //; congr (RN _); lra.
  suff Hci : (Ci * Ci = -1)%C by ring[Hci].
  by congr (_, _) => /=; lra.
wlog x2_pos : x1 y1 x2 y2 x1_pos y1_pos / 0 <= x2 => [Hx2|].
  case: (Rle_dec 0 x2) => [// | x2_neg]; first by apply: Hx2.
  suff-> : normw_error2 Cmult brent_imult (x1, y1) (x2, y2) =
           normw_error2 Cmult brent_imult (x1, y1) (-(x2, y2)).
    by  apply: Hx2 => /=; lra.
  rewrite /normw_error2 /= !(Cmod_mult, CmodJ, Cmod_opp); congr (_ / _).
  rewrite -!(Ropp_mult_distr_r, Ropp_mult_distr_l) !RN_sym //.
  rewrite -Ropp_plus_distr -[- _ - - _]Ropp_plus_distr  !RN_sym //.
  set u1 := RN _; set u2 := RN _.
  rewrite /Cminus.
  have -> : (((- u1)%R, (- u2)%R) = - (u1, u2))%C by [].
  by rewrite -Copp_plus_distr -Copp_mult_distr_r Cmod_opp.
wlog y2_pos : x1 y1 x2 y2 x1_pos y1_pos x2_pos / 0 <= y2 => [Hy2|].
  case: (Rle_dec 0 y2) => [// | y2_neg]; first by apply: Hy2.
  suff-> : normw_error2 Cmult brent_imult (x1, y1) (x2, y2) =
           normw_error2 Cmult brent_imult (x1, y1)  (Ci * (x2, y2)).
    by apply: Hy2 => //=; lra.
  rewrite /normw_error2 /= !(Cmod_mult, CmodJ, Cmod_opp).
  congr (_ / _); last first.
    by rewrite Cmod_Ci Rmult_1_l.
  rewrite !Rsimp01.
  rewrite -!Ropp_mult_distr_r !RN_sym // -Ropp_plus_minus_distr RN_sym //.
  set u1 := RN _; set u2 := RN _.
  have->: (((- u2)%R, u1) = (u1, u2) * Ci :> C)%C by congr (_, _) => /=; lra.
  have->: ((x1, y1) * (Ci * (x2, y2)) = ((x1, y1) * (x2, y2)) * Ci)%C by ring.
  by rewrite -Cmult_minus_distr_r Cmod_mult Cmod_Ci Rmult_1_r.
wlog prod_pos :
     x1 y1 x2 y2 x1_pos y1_pos x2_pos y2_pos / y1 * y2 <= x1 * x2 => [Hp|].
  case: (Rle_dec (y1 * y2) (x1 * x2)) => [// | p_neg]; first by apply: Hp.
  suff-> : normw_error2 Cmult brent_imult (x1, y1) (x2, y2) =
           normw_error2 Cmult brent_imult (Cconj ((- Ci) * (x1, y1)))
                                          (Cconj ((- Ci) * (x2, y2))).
    by apply: Hp => //=; lra.
  rewrite /normw_error2 /= !(Cmod_mult, CmodJ, Cmod_opp, Cmod_conj, Cmod_Ci, 
                             Rsimp01); congr (_ / _).
  rewrite -!Ropp_mult_distr_l !Ropp_involutive.
  set u1 : C := (RN _, _); set u2 : C := (RN _, _).
  have -> : u2 = (- Cconj u1)%C.
    congr (_, _) => /=.
      by rewrite -[RHS]RN_sym //; congr (RN _); lra.
    by rewrite Rplus_comm Ropp_involutive.
  rewrite !(Cmult_conj, Copp_conj, Cconj_i).
  have -> : (- - Ci * Cconj (x1, y1) * (- - Ci * Cconj (x2, y2)) = 
               - (Cconj((x1, y1) * (x2, y2))))%C.
    have F : (Ci * Ci = -1)%C by congr (_, _) => /=; lra.
    by rewrite Cmult_conj; ring [F].
  rewrite -[(- _ - _)%C]Copp_plus_distr -Copp_conj -Cplus_conj.
  by rewrite Cmod_opp Cmod_conj.
by apply: normw_errror2_brent_imult_pos.
Qed.

Lemma error_brent_imult_lt z1 z2 :
  (z1 * z2 <> 0)%C ->
  Cmod (brent_imult z1 z2 - z1 * z2) < sqrt 5 * u * Cmod (z1 * z2).
Proof.
move=> z1_z2_neq0.
have C_neq_0 : 0 < Cmod (z1 * z2) by apply/Cmod_gt_0.
apply/Rlt_div_l => //.
rewrite -Cmod_div //.
by apply: normw_erroyr2_brent_imult.
Qed.

Lemma error_brent_imult z1 z2 :
  Cmod (brent_imult z1 z2 - z1 * z2) <=  sqrt 5 * u * Cmod (z1 * z2).
Proof.
have [->|z1_neq0] := Ceq_dec z1 0.
  by rewrite brent_imult_0_l !Csimp01; lra.
have [->|z2_neq0] := Ceq_dec z2 0.
  by rewrite brent_imult_0_r !Csimp01; lra.
apply/Rlt_le/error_brent_imult_lt.
by apply: Cmult_neq_0.
Qed.

End Brent.

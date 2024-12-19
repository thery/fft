(* Copyright (c)  Inria. All rights reserved. *)

Require Import Reals  Psatz.
From Flocq Require Import Core Relative Sterbenz Operations.
From Flocq Require Import Mult_error.
From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
Require Import Rmore Fmore.

Set Implicit Arguments.

Open Scope R_scope.

Section KahanMult.

Variables  p: Z.
Variable beta: radix.
Hypothesis Hbeta2: Z.lt 1 beta.
Hypothesis Hbeta_even : Z.even beta.
Hypothesis Hp2: Z.lt 1 p.
Variable choice : Z -> bool.
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RN := (round beta fexp (Znearest choice)).
Local Notation ulp := (ulp beta fexp).
Local Notation u := (u p beta).
Local Notation pow := (bpow beta).

Local Notation u_gt_0 := (u_gt_0 p beta).
Local Notation RN_pow := (@RN_pow  _ beta Hp2 choice).
Local Notation RN_abs := (@RN_abs _ beta Hp2 choice choice_sym).
Local Notation FLX_format_Rabs_Fnum := (@FLX_format_Rabs_Fnum p beta Hp2).
Local Notation beta_ge_2 := (beta_ge_2 beta Hbeta2).
Local Notation ulp_FLX_gt :=  (@ulp_FLX_gt p beta).

Definition kahan a b c d := 
  let w := RN (b * c) in
  let e := RN (w - b * c) in
  let f := RN (a * d - w) in
  RN (f + e).

(* Prop 1.1 *)
Lemma error_bound_ulp_u t : Rabs (RN t - t) <= /2 * ulp t <= u * Rabs t.
Proof. by apply: error_bound_ulp_u. Qed.

Lemma RN_E t : exists d, RN t = t * (1 + d) /\ Rabs d <= u.
Proof. by apply: RN_E. Qed.

Variable a b c d : R.
Hypothesis Fa : format a.
Hypothesis Fb : format b.
Hypothesis Fc : format c.
Hypothesis Fd : format d.

Definition w' := RN (b * c).

Lemma Fw' : format w'.
Proof. apply: generic_format_round. Qed.

Definition e := w' - b * c.

Lemma Fe : format e.
Proof. by apply: mult_error_FLX. Qed.

Definition f := a * d - w'.
Definition f' := RN f.

Lemma Ff : format f'.
Proof. apply: generic_format_round. Qed.

Definition x := a * d - b * c.

Definition x' := RN (f' + e).

Lemma Fx' : format x'.
Proof. apply: generic_format_round. Qed.

Lemma eE : e = w' - b * c.
Proof. by []. Qed.

Lemma xE : x = f + e.
Proof. by rewrite eE /f /x; lra. Qed.

(* 2.2 *)
Definition eps1 := f' - f.
Definition eps2 := x' - (f' + e).

(* 2.3 *)
Lemma x'BxE : x' - x = eps1 + eps2.
Proof. by rewrite /eps2 /eps1 /x'; rewrite xE; lra. Qed.

(* 2.4 *)
Lemma eps1_bound : Rabs eps1 <= /2 * ulp(f).
Proof. by rewrite /eps1 /f'; have := error_bound_ulp_u f; lra. Qed.
Lemma eps2_bound : Rabs eps2 <= /2 * ulp(f' + e).
Proof. rewrite /eps2 /x'; have := error_bound_ulp_u (f' + e); lra. Qed.

 (* 2.6 *)
Lemma error_x_x :
  Rabs (x' - x) <= (2 * u + u ^ 2) * Rabs x + (u + u ^ 2) * Rabs e.
Proof.
have [x_eq_0 |x_neg0] := Req_dec x 0.
  rewrite x_eq_0 Rminus_0_r /x' /f' /f.
  have -> : a * d = b * c by rewrite /x in x_eq_0; lra.
  rewrite -Ropp_minus_distr RN_sym // -/e.
  rewrite [RN e](round_generic _ _ _ _ Fe).
  have -> : - e + e = 0 by lra.
  rewrite round_0.
  by have := u_gt_0; split_Rabs; nra.
have [delta1] := RN_E f; rewrite -/f' => [] [f'E delta1_bound].
have [delta2] := RN_E (f' + e); rewrite -/x' => [] [x'E delta2_bound].
have x'E1 : x' = (f * (1 + delta1) + e) * (1 + delta2) by nra.
have x'BxE : x' - x = x * (delta1 + delta2 + delta1 * delta2 ) 
                      - e * delta1 * (1 + delta2).
  have xE := xE.
  by rewrite x'E1 (_ : f = x - e); try lra.
rewrite x'BxE.
apply: Rle_trans (Rabs_triang _ _) _.
apply: Rplus_le_compat.
  rewrite Rabs_mult Rmult_comm.
  apply: Rmult_le_compat_r; first by split_Rabs; lra.
  apply: Rle_trans (Rabs_triang _ _) _.
  apply: Rplus_le_compat.
    by apply: Rle_trans (Rabs_triang _ _) _; lra.
  rewrite Rabs_mult.
  by apply: Rmult_le_compat; try lra; split_Rabs; lra.
rewrite Rabs_Ropp 2!Rabs_mult Rmult_assoc Rmult_comm.
by apply: Rmult_le_compat; try (split_Rabs; nra).
Qed.

(* 2.5 *)
Lemma error_x_j (J := 2 * u + u ^ 2 + (u + u ^ 2) * u * Rabs (b * c) / Rabs x) :
  Rabs (x' - x) <= J * Rabs x.
Proof.
have [x_eq_0 |x_neg0] := Req_dec x 0.
  rewrite x_eq_0 Rminus_0_r /x' /f' /f.
  have -> : a * d = b * c by rewrite /x in x_eq_0; lra.
  rewrite -Ropp_minus_distr RN_sym // -/e.
  rewrite [RN e](round_generic _ _ _ _ Fe).
  have -> : - e + e = 0 by lra.
  by rewrite round_0 !Rabs_R0; lra.
have e_bound : Rabs e <= u * Rabs (b * c).
  by rewrite eE /w'; have := error_bound_ulp_u (b * c); lra.
apply: Rle_trans error_x_x _.
apply: Rle_trans (_ : (2 * u + u ^ 2) * Rabs x + (u + u ^ 2) * 
                                                 (u * Rabs (b * c)) <= _).
  have u_gt0 := u_gt_0; nra.
rewrite /J.
have: forall a b, a = b -> a <= b by move=> *; lra.
by apply; field; split_Rabs; lra.
Qed.
  
(* Property 2.1 *)
Lemma format_bc_x'_RN_x : format (b * c) -> x' = RN x.
Proof.
move=> Fbc.
have e0 : e = 0 by rewrite eE /w' round_generic; try lra.
rewrite /x' /f' xE e0 !Rplus_0_r round_generic //.
apply: generic_format_round.
Qed.

Lemma format_f_x'_RN_x : format f -> x' = RN x.
Proof. by move=> Ff; rewrite /x' /f' [RN f]round_generic // xE. Qed.

Let C := ~ format (b * c) /\ ~ format f.

Lemma C_case:  C \/ (format (b * c) \/ format f).
Proof. by rewrite /C /format; lra. Qed.

(* Prop 2.2 *)
Lemma C_imp_abcd_neq_0 : C -> a * b * c * d <> 0.
Proof.
move=> [Fbc Ff] abcd_eq_0.
have [ad_eq_0 | ad_neq_0] := Req_dec (a * d) 0.
  case: Ff.
  have -> : f = -w' by rewrite /f; lra.
  by apply/generic_format_opp/Fw'.
case: Fbc.
have ->: b * c = 0 by nra.
by apply: generic_format_0.
Qed.

(* Prop 2.2 *)
Lemma C_imp_x_neq_0 : C -> x <> 0.
Proof.
move=> [Fbc Ff] x_eq_0.
have adE : a * d = b * c by rewrite /x in x_eq_0; lra.
have fE : f = - e by rewrite /f adE eE; lra.
by case: Ff; rewrite fE; apply/generic_format_opp/Fe.
Qed.

Let ma := mant a.
Local Notation mA := (Ztrunc (mant a)).

Lemma maE : ma = IZR mA.
Proof. by rewrite -scaled_mantissa_generic. Qed.

Lemma aE : a = ma * pow (cexp a).
Proof. by rewrite maE [LHS]Fa. Qed.

Let mb := mant b.
Local Notation  mB := (Ztrunc (mant b)).

Lemma mbE : mb = IZR mB.
Proof. by rewrite -scaled_mantissa_generic. Qed.

Lemma bE : b = mb * pow (cexp b).
Proof. by rewrite mbE [LHS]Fb. Qed.

Let mc := mant c.
Local Notation mC := (Ztrunc (mant c)).

Lemma mcE : mc = IZR mC.
Proof. by rewrite -scaled_mantissa_generic. Qed.

Lemma cE : c = mc * pow (cexp c).
Proof. by rewrite mcE [LHS]Fc. Qed.

Let md := mant d.
Local Notation mD :=( Ztrunc (mant d)).

Lemma mdE : md = IZR mD.
Proof. by rewrite -scaled_mantissa_generic. Qed.

Lemma dE : d = md * pow (cexp d).
Proof. by rewrite mdE [LHS]Fd. Qed.

Definition sigma := (cexp a + cexp d - cexp b - cexp c)%Z.

Let iRN := iRN p beta choice.
Let iRNE := iRNE beta Hp2 choice.

Definition mW' := iRN (mB * mC).
Let mw' := IZR mW'.

Definition mE := (if Z_le_dec 0 sigma then mW' - mB * mC else 
                  (mW' - mB * mC) * Z.pow beta (- sigma))%Z.
Let me := IZR mE.

Definition mF := (if Z_le_dec 0 sigma then mA * mD * Z.pow beta sigma - mW' else 
                  mA * mD - mW' * Z.pow beta (- sigma))%Z.
Let mf := IZR mF.

Definition mF' := iRN mF.
Let mf' := IZR mF'.

Definition mX := (mF + mE)%Z.
Let mx := IZR mX.

Definition mX' := iRN (mF' + mE).
Let mx' := IZR mX'.

(* Prop 2.3 *)
Lemma mu_def : 
   exists mu, [/\ 
       e = me * pow mu, f = mf * pow mu, f' = mf' * pow mu, x = mx * pow mu &
       x' = mx' * pow mu].
Proof.
pose mu := Z.min (cexp a + cexp d) (cexp b + cexp c).
have [sigma_pos|sigma_neg] := Z_le_dec 0 sigma.
  have Hl : is_left (Z_le_dec 0 sigma) by case: Z_le_dec=> //; lia.
  have mxE : mx = ma * md * pow sigma - mb * mc.
    rewrite /mx plus_IZR /mF /mE Hl 2!minus_IZR 3!mult_IZR.
    by rewrite -maE -mdE -mbE -mcE IZR_Zpower //; lra.
  have muE : mu = (cexp b + cexp c)%Z.
    by rewrite /mu /sigma in sigma_pos *; lia.
  have powE : pow sigma * pow mu = pow (cexp a) * pow (cexp d).
    rewrite muE !(bpow_plus, bpow_opp).
    by field; repeat split; apply: pow_neq_0.
  have mfE : f = mf * pow mu.
    rewrite /mf /mF Hl minus_IZR !mult_IZR -maE -mdE IZR_Zpower //.
    rewrite Rmult_minus_distr_r Rmult_assoc powE.
    rewrite /mw' /mW' -iRNE mult_IZR -mbE -mcE.
    rewrite -RN_mult_pow muE bpow_plus.
    congr (_ - RN _); first by rewrite [in LHS]aE [in LHS]dE; lra.
    by rewrite [in LHS]bE [in LHS]cE; lra.
  have mxE1 : x = mx * pow mu.
   rewrite mxE Rmult_minus_distr_r Rmult_assoc powE muE bpow_plus.
    rewrite /x [in LHS]aE [in LHS]dE [in LHS]bE [in LHS]cE.
    by lra.
  have meE : e = me * pow mu.
    have -> : me = mx - mf by rewrite /mx plus_IZR -/mf -/me; lra.
    by rewrite Rmult_minus_distr_r -mxE1 -mfE xE; lra.
  have mf'E : f' = mf' * pow mu by rewrite /mf' -iRNE -RN_mult_pow -mfE.
  exists mu; split => //.
  rewrite /mx' -iRNE -RN_mult_pow plus_IZR Rmult_plus_distr_r.
  by rewrite -mf'E -meE.
have Hr : is_left (Z_le_dec 0 sigma) = false by case: Z_le_dec=> //; lia.
have mxE : mx = ma * md - mb * mc * pow (- sigma).
  rewrite /mx plus_IZR /mF /mE Hr minus_IZR !mult_IZR minus_IZR mult_IZR.
  rewrite -maE -mdE -mbE -mcE !IZR_Zpower //; last by lia.
  by lra.
have muE : mu = (cexp a + cexp d)%Z.
  by rewrite /mu /sigma in sigma_neg *; lia.
have powE : pow (- sigma) * pow mu = pow (cexp b) * pow (cexp c).
  rewrite muE !(bpow_plus, bpow_opp).
  by field; repeat split; apply: pow_neq_0.
have mfE : f = mf * pow mu.
  rewrite /mf /mF Hr minus_IZR !mult_IZR -maE -mdE IZR_Zpower //; try lia.
  rewrite Rmult_minus_distr_r.
  rewrite /mw' /mW' -iRNE mult_IZR -mbE -mcE.
  rewrite -!RN_mult_pow muE bpow_plus.
  congr (_ - RN _); first by rewrite [in LHS]aE [in LHS]dE; lra.
  rewrite Rmult_assoc -!bpow_plus.
  have -> : (-sigma + (cexp a + cexp d) = cexp b + cexp c)%Z
    by rewrite /sigma; lia.
  by rewrite [in LHS]bE [in LHS]cE bpow_plus; lra.
have mxE1 : x = mx * pow mu.
  rewrite mxE Rmult_minus_distr_r [_ * pow _ * pow _]Rmult_assoc powE.
  rewrite  muE bpow_plus.
  rewrite /x [in LHS]aE [in LHS]dE [in LHS]bE [in LHS]cE.
  by lra.
have meE : e = me * pow mu.
  have -> : me = mx - mf by rewrite /mx plus_IZR -/mf -/me; lra.
  by rewrite Rmult_minus_distr_r -mfE -mxE1 xE; lra.
have mf'E : f' = mf' * pow mu.
  by rewrite /mf' -iRNE -/mf -RN_mult_pow -mfE.
exists mu; split => //.
rewrite /mx' -iRNE plus_IZR -RN_mult_pow Rmult_plus_distr_r.
by rewrite -/mf' -mf'E -/me -meE.
Qed.

Let mant_bound_le := @mant_bound_le _ beta Hp2.

(* 2.10 a *)
Lemma ad_bound : 
  C -> pow (2 * p - 2) <= Rabs (ma * md) <= pow (2 * p) - 2 * pow p + 1.
Proof.
move=> Hc.
have a_neq_0 : a <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have d_neq_0 : d <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have ba := mant_bound_le Fa a_neq_0; rewrite -/ma in ba.
have bd := mant_bound_le Fd d_neq_0; rewrite -/md in bd.
rewrite Rabs_mult.
have -> : (2 * p - 2 = (p - 1) + (p - 1))%Z by lia.
rewrite bpow_plus.
have -> : (2 * p = p + p)%Z by lia.
rewrite [pow (_ + _)]bpow_plus.
have := bpow_gt_0 beta (p - 1).
by nra.
Qed.

Lemma bc_bound : 
  C -> pow (2 * p - 2) <= Rabs (mb * mc) <= pow (2 * p) - 2 * pow p + 1.
Proof.
move=> Hc.
have b_neq_0 : b <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have c_neq_0 : c <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have bb := mant_bound_le Fb b_neq_0; rewrite -/mb in bb.
have bc := mant_bound_le Fc c_neq_0; rewrite -/mc in bc.
rewrite Rabs_mult.
have -> : (2 * p - 2 = (p - 1) + (p - 1))%Z by lia.
rewrite bpow_plus.
have -> : (2 * p = p + p)%Z by lia.
rewrite [pow (_ + _)]bpow_plus.
have := bpow_gt_0 beta (p - 1).
by nra.
Qed.

(* 2.10 b *)

Lemma ulp_mbc_lt : 
  C -> Rabs (mb * mc) < pow (2 * p - 1) -> ulp (mb * mc) = pow (p - 1).
Proof.
move=> Hc mbcLp.
apply: ulp_in_binade.
have -> : (p - 1 + p - 1 = 2 * p - 2)%Z by lia.
have -> : (p - 1 + p = 2 * p - 1)%Z by lia.
by have := bc_bound Hc; lra.
Qed.

Lemma ulp_mbc_ge : 
  C -> pow (2 * p - 1) <= Rabs (mb * mc) -> ulp (mb * mc) = pow p.
Proof.
move=> Hc mbcLp.
apply: ulp_in_binade.
have -> : (p + p - 1 = 2 * p - 1)%Z by lia.
have -> : (p + p = 2 * p)%Z by lia.
have := bc_bound Hc.
suff : 1 < pow p by lra.
by apply: (bpow_lt _ 0); lia.
Qed.

Lemma ulp_mbc_le : C -> ulp (mb * mc) <= pow p.
Proof.
move=> Hc.
have [F|F] := Rle_dec (pow (2 * p - 1)) (Rabs (mb * mc)).
  by rewrite ulp_mbc_ge //; lra.
rewrite ulp_mbc_lt //; try lra.
by apply: bpow_le; lia.
Qed.

(* 2.10c *)
Lemma ulp_mw'_ge : 
  C -> pow (2 * p - 2) <= Rabs mw' <= pow (2 * p) - pow p.
Proof.
move=> Hc.
rewrite -RN_pow.
have -> : pow (2 * p) - pow p = RN (pow (2 * p) - pow p).
  rewrite round_generic //.
  apply: generic_format_FLX.
  have -> : (2 * p = p + p)%Z by lia.
  apply: (FLX_spec beta p _ (Float beta (Z.pow beta p - 1) p)).
    by rewrite bpow_plus /F2R /= plus_IZR IZR_Zpower /=; (lia || lra).
  by rewrite /f /=; lia.
have Fb1 := bc_bound Hc.
have Fb2 : 1 < pow p by apply: (bpow_lt _ 0); lia.
by rewrite /mw' -iRNE -RN_abs mult_IZR -mbE -mcE; split; apply: round_le; lra.
Qed.

Lemma F_bound : C -> pow p < Rabs mf.
Proof.
move=> [_ Hf]; case: (Rle_dec (Rabs mf) (pow p)) => Hf1; try lra.
have [mu [_ fE _ _ _]] := mu_def.
pose f1 := Float beta mF mu.
have /FLX_format_Rabs_Fnum : f = F2R f1 by rewrite /F2R /= -/mf.
by rewrite /= -/mf => /(_  Hf1).
Qed.

Lemma mb_ge : C -> pow (p - 1) + 1 <= Rabs mb.
Proof.
move=> Hc.
suff :  pow (p - 1) < Rabs mb.
  rewrite mbE Rabs_Zabs -IZR_Zpower -?(plus_IZR _ 1); last by lia.
  by move=> /lt_IZR H; apply: IZR_le; lia.
have b_neq_0 : b <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have c_neq_0 : c <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have B_ge : pow (p - 1) <= Rabs mb <= pow p.
  by have := mant_bound Fb b_neq_0; rewrite -/mb; lra.
have C_ge : pow (p - 1) <= Rabs mc <= pow p.
  by have := mant_bound Fc c_neq_0; rewrite -/mc; lra.
suff : pow (p - 1) <> Rabs mb by lra.
move=> mb_pow; have [[]] := Hc; rewrite bE cE.
move: mb_pow; rewrite /Rabs; split_case_Rabs => mb_pow.
  pose f1 := Float beta (- mC) (p - 1 + cexp b + cexp c).
  apply: (@FLX_format_Rabs_Fnum _ f1) => /=.
    by rewrite /F2R /= opp_IZR -mcE 2!bpow_plus mb_pow; lra.
  by rewrite opp_IZR -mcE Rabs_Ropp; lra.
pose f1 := Float beta mC (p - 1 + cexp b + cexp c).
  apply: (@FLX_format_Rabs_Fnum _ f1) => /=.
  by rewrite /F2R /= -mcE 2!bpow_plus mb_pow; lra.
by rewrite -mcE; lra.
Qed.

Lemma mb_ge_powp1 : C -> pow (p - 1) + 1 <= Rabs mb.
Proof.
move=> Hc.
suff :  pow (p - 1) < Rabs mb.
  rewrite mbE Rabs_Zabs -IZR_Zpower -?(plus_IZR _ 1); last by lia.
  by move=> /lt_IZR H; apply: IZR_le; lia.
have b_neq_0 : b <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have c_neq_0 : c <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have B_ge : pow (p - 1) <= Rabs mb <= pow p.
  by have := mant_bound Fb b_neq_0; rewrite -/mb; lra.
have C_ge : pow (p - 1) <= Rabs mc <= pow p.
  by have := mant_bound Fc c_neq_0; rewrite -/mc; lra.
suff : pow (p - 1) <> Rabs mb by lra.
move=> mb_pow; have [[]] := Hc; rewrite bE cE.
move: mb_pow; rewrite /Rabs; split_case_Rabs => mb_pow.
  pose f1 := Float beta (- mC) (p - 1 + cexp b + cexp c).
  apply: (@FLX_format_Rabs_Fnum _ f1) => /=.
    by rewrite /F2R /= opp_IZR -mcE 2!bpow_plus mb_pow; lra.
  by rewrite opp_IZR -mcE Rabs_Ropp; lra.
pose f1 := Float beta mC (p - 1 + cexp b + cexp c).
  apply: (@FLX_format_Rabs_Fnum _ f1) => /=.
  by rewrite /F2R /= -mcE 2!bpow_plus mb_pow; lra.
by rewrite -mcE; lra.
Qed.

Lemma mc_ge_powp1 : C -> pow (p - 1) + 1 <= Rabs mc.
Proof.
move=> Hc.
suff :  pow (p - 1) < Rabs mc.
  rewrite mcE Rabs_Zabs -IZR_Zpower -?(plus_IZR _ 1); last by lia.
  by move=> /lt_IZR H; apply: IZR_le; lia.
have b_neq_0 : b <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have c_neq_0 : c <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
have B_ge : pow (p - 1) <= Rabs mb <= pow p.
  by have := mant_bound Fb b_neq_0; rewrite -/mb; lra.
have C_ge : pow (p - 1) <= Rabs mc <= pow p.
  by have := mant_bound Fc c_neq_0; rewrite -/mc; lra.
suff : pow (p - 1) <> Rabs mc by lra.
move=> mc_pow; have [[]] := Hc; rewrite bE cE.
move: mc_pow; rewrite /Rabs; split_case_Rabs => mb_pow.
  pose f1 := Float beta (- mB) (p - 1 + cexp b + cexp c).
  apply: (@FLX_format_Rabs_Fnum _ f1) => /=.
    by rewrite /F2R /= opp_IZR -mbE 2!bpow_plus mb_pow; lra.
  by rewrite opp_IZR -mbE Rabs_Ropp; lra.
pose f1 := Float beta mB (p - 1 + cexp b + cexp c).
  apply: (@FLX_format_Rabs_Fnum _ f1) => /=.
  by rewrite /F2R /= -mbE 2!bpow_plus mb_pow; lra.
by rewrite -mbE; lra.
Qed.

Lemma me_le_y_le_mx (i :=(- sigma)%Z)
  (y :=  pow (p - 2) + 2 * pow (-1) - (pow p - 2) * pow (- i)) :
  C -> (2 <= i)%Z -> 
   Rabs me <= /2 * pow (p + i) /\ pow (p + i) * y <= Rabs mx.
Proof.
move=> Hc iL2.
have Hr : is_left (Z_le_dec 0 sigma) = false by case: Z_le_dec=> //; lia.
have me_le : Rabs me <= /2 * pow (p + i).
  rewrite /me /mE Hr mult_IZR IZR_Zpower -/i; try lia.
  rewrite bpow_plus Rabs_mult Rabs_pow -Rmult_assoc.
  apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
  apply: Rle_trans (_ : /2 * ulp (mb * mc) <= _).
    rewrite /mW' minus_IZR -iRNE mult_IZR -mbE -mcE.
    by have := error_bound_ulp_u (mb * mc); lra.
  apply: Rmult_le_compat_l; try lra.
  by apply: ulp_mbc_le.
split => //.
have mx_ge : (pow (p - 1) + 1) ^ 2 * pow i - (pow p - 1) ^ 2 <=  Rabs mx.
  have -> : mx = ma * md - (mb * mc) * pow i.
    rewrite /mx plus_IZR /mF /mE Hr minus_IZR !mult_IZR minus_IZR mult_IZR.
    rewrite -maE -mdE -mbE -mcE -/i !IZR_Zpower //; last by lia.
    by lra.
  apply: Rle_trans (_ : Rabs (mb * mc * pow i) - Rabs (ma * md) <= _);
      last by split_Rabs; lra.
  suff : (pow (p - 1) + 1) ^ 2  * pow i <= Rabs (mb * mc * pow i).
    by have := ad_bound Hc; rewrite pow2M; lra.
  rewrite Rabs_mult Rabs_pow.
  apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
  rewrite Rabs_mult.
  have mb_ge := mb_ge_powp1 Hc; have mc_ge := mc_ge_powp1 Hc. 
  by apply: Rmult_le_compat; have := bpow_gt_0 beta (p - 1); lra.
rewrite Rmult_minus_distr_l.
set vu := _ - _ in mx_ge; set vv := _ - _.
suff : vv <= vu by lra.
have : vu - vv = pow i - 1.
  rewrite /vu /vv 3!bpow_plus (_ : -(2) = 2 * -1)%Z; last by lia.
  rewrite pow2M bpow_opp bpow_opp.
  by field; split; apply: pow_neq_0.
suff : 1 <= pow i by lra.
by apply: (bpow_le _ 0); lia.
Qed.

(* Prop 3.1 *)
Lemma me_div_mx_le : C -> Rabs e / Rabs x <= IZR beta - 1.
Proof.
move=> Hc.
have [mu [-> _ _ mxE _]] :=  mu_def.
have mx_neq_0 : mx <> 0.
  by move=> F1; case:  C_imp_x_neq_0 => //; rewrite mxE F1; lra.
rewrite mxE !Rabs_mult [in X in _ / X]Rmult_comm.
rewrite /Rdiv Rinv_mult.
(* - by have := bpow_gt_0 beta mu; split_Rabs; lra. *)
(* - by split_Rabs; lra. *)
rewrite Rmult_assoc -[Rabs (pow mu) * _]Rmult_assoc Rinv_r; last first.
  by have := bpow_gt_0 beta mu; split_Rabs; lra.
rewrite Rmult_1_l.
apply/Rle_div_l; first by split_Rabs; lra.
have [sigma_pos | [sigma_N1 | sigma_leN2]] :
   (0 <= sigma \/ (sigma = -1 \/ sigma <= -2))%Z by lia.
- have Hl : is_left (Z_le_dec 0 sigma) by case: Z_le_dec=> //; lia.
  apply: Rle_trans (_ : Rabs mx <= _); last first.
    have := beta_ge_2.
    have : IZR beta <= pow p.
      have ->: IZR beta = pow 1 by congr IZR; lia.
      by apply: (bpow_le _ 1); lia.
    by split_Rabs; nra.
  have F : Rabs me <= /2 * pow p.
    apply: Rle_trans (_ : /2 * ulp (mb * mc) <= _).
      have := error_bound_ulp_u (mb * mc).
      rewrite /me /mE Hl minus_IZR mult_IZR /mW' -iRNE mult_IZR -mbE -mcE.
      by lra.
    by have := ulp_mbc_le Hc; lra.
  apply: Rle_trans (F) _.
  apply: Rle_trans (_ : Rabs mf - Rabs me <= _); last first.
    rewrite /mx /mX plus_IZR -/mf -/me; split_Rabs; lra.
  by have := F_bound Hc; lra.
- have Hr : is_left (Z_le_dec 0 sigma) = false by case: Z_le_dec=> //; lia.
  have [bcLp1|p2Lbc] := Rle_dec (Rabs (mb * mc)) (pow (2 * p - 1)).
    apply: Rle_trans (_ : Rabs mx <= _); last first.
      have := beta_ge_2.
      have : IZR beta <= pow p.
        have ->: IZR beta = pow 1 by congr IZR; lia.
        by apply: (bpow_le _ 1); lia.
      by split_Rabs; nra.
    have F : Rabs me <= /2 * pow p.
      have [F1|F1] :=  Req_dec (pow (2 * p - 1)) (Rabs (mb * mc)).
        rewrite /me /mE Hr /mW' mult_IZR minus_IZR -iRNE round_generic.
          by have := bpow_gt_0 beta p; split_Rabs; lra.
        rewrite mult_IZR -mbE -mcE.
        split_Rabs; last first.
          by rewrite -F1; apply: generic_format_bpow'; rewrite /fexp; lia.
        rewrite -[_ * _]Ropp_involutive -F1.
        by apply/generic_format_opp/generic_format_bpow'; rewrite /fexp; lia.
      rewrite /me /mE Hr mult_IZR IZR_Zpower sigma_N1 // bpow_1
              Rabs_mult Rabs_beta.
      have pE : p = (p - 1 + 1)%Z by lia.
      rewrite [in X in _ <= X]pE bpow_plus bpow_1 -Rmult_assoc.  
      apply: Rmult_le_compat_r; first by apply: IZR_le; lia.
      rewrite -ulp_mbc_lt //; try lra.
      rewrite /mW' minus_IZR -iRNE mult_IZR -mbE -mcE.
      by  have := error_bound_ulp_u (mb * mc); lra.
    apply: Rle_trans (_ : Rabs mf - Rabs me <= _); last first.
      by rewrite /mx /mX plus_IZR -/mf -/me; split_Rabs; lra.
    by have := F_bound Hc; lra.
  have mx_bound : 2 * pow p <= Rabs mx.
    suff : 2 * pow p - 1 < Rabs mx.
      have -> : 2 * pow p = IZR (2 * beta ^ p)
        by rewrite mult_IZR IZR_Zpower //; lia.
      rewrite /mx Rabs_Zabs -minus_IZR => /lt_IZR H.
      by apply: IZR_le; lia.
    apply: Rlt_le_trans (_ : Rabs(mb * mc) * IZR beta - Rabs (ma * md) <= _); 
          last first.
      have -> : mx = ma * md - mb * mc * IZR beta.
        rewrite /mx /mX /mF /mE Hr plus_IZR minus_IZR !mult_IZR minus_IZR.
        rewrite mult_IZR -maE -mdE -mbE -mcE sigma_N1 Z.pow_1_r; lra.
      by split_Rabs; lra.
    have -> : 2 * pow p - 1 = IZR beta * pow (2 * p - 1) -  
                             (pow (2 * p) - 2 * pow p + 1).
      rewrite [in pow (2 * _)](_ : 2 * p = 2 * p - 1 + 1)%Z; try lia.
      by rewrite bpow_plus pow1E; lra.
    have := ad_bound Hc.
    suff : IZR beta * pow (2 * p - 1) < Rabs (mb * mc) * IZR beta by lra.
    rewrite Rmult_comm.
    by apply: Rmult_lt_compat_r; [apply: radix_pos|lra].
  have F : Rabs me <= /2 * pow (p + 1).
    rewrite /me /mE Hr mult_IZR IZR_Zpower sigma_N1 // bpow_1
            Rabs_mult Rabs_beta bpow_plus bpow_1 -Rmult_assoc.  
    apply: Rmult_le_compat_r; first by apply: IZR_le; lia.
    rewrite -ulp_mbc_ge //; try lra.
    rewrite /mW' minus_IZR -iRNE mult_IZR -mbE -mcE.
    by  have := error_bound_ulp_u (mb * mc); lra.
  apply: Rle_trans F _.
  apply: Rle_trans (_ : (IZR beta - 1) *  (2 * pow p) <= _).
    rewrite bpow_plus pow1E.
    have : IZR beta <= pow p by rewrite -pow1E; apply: bpow_le; lia.
    by have := beta_ge_2; nra.
  apply: Rmult_le_compat_l => //.
  have : IZR beta <= pow p by rewrite -pow1E; apply: bpow_le; lia.
  have : 1 < IZR beta by apply: IZR_lt; lia.
  by lra.
pose i := (- sigma)%Z.
have i_ge : (2 <= i)%Z by lia.
have Hr : is_left (Z_le_dec 0 sigma) = false by case: Z_le_dec=> //; lia.
have [me_le mx_ge1]:= me_le_y_le_mx Hc i_ge.
rewrite -/i in mx_ge1; set y :=  _ + _ - _ in mx_ge1.
have mx_ge2 : 2 * pow (p + i -1) <= Rabs mx.
  suff H : 2 * pow (- 1) <= y.
    apply: Rle_trans  mx_ge1.
    rewrite [in X in X <= _]bpow_plus.
    have -> : (- (1) = - 1)%Z by lia.
    by have := bpow_gt_0 beta (p + i); nra.
  suff : (pow p - 2) * pow (- i) <= pow (p - 2) by rewrite /y; lra.
  have /(bpow_le beta) : (p - i <= p - 2)%Z by lia.
  by rewrite bpow_plus; have := bpow_gt_0 beta (- i); lra.
apply: Rle_trans me_le _.
have -> : pow (p + i) = pow (p + i - 1) * (IZR beta).
  by rewrite -pow1E -bpow_plus; congr (pow _); lia.
suff : IZR beta * (2 * pow (p + i - 1)) <= (4 * (IZR beta - 1)) * Rabs mx.
  by lra.
by have := beta_ge_2; have := bpow_gt_0 beta (p + i - 1); nra.
Qed.

Lemma me_mult_mx_le : C -> Rabs e <= (IZR beta - 1) * Rabs x.
Proof.
move=> Hc.
apply/Rle_div_l; first by have := C_imp_x_neq_0 Hc; split_Rabs; lra.
by apply: me_div_mx_le.
Qed.

(* Prop 3.2 *)
Lemma error_x_K (K := (IZR beta + 1) * u + (IZR beta) * u ^2) :
  Rabs (x' - x) <= K * Rabs x.
Proof.
have [Hc | Hc] := C_case.
  apply: Rle_trans error_x_x _.
  rewrite /K.
  by have := me_mult_mx_le Hc; have := u_gt_0; nra.
suff : u <= K.
  have [/format_bc_x'_RN_x->|/format_f_x'_RN_x->] := Hc;
  by have := error_bound_ulp_u x; split_Rabs; nra.
rewrite /K.
by have := u_gt_0; have := beta_ge_2; nra.
Qed.

(* 3.2 *)
Lemma x'_x_same_sign : 0 <= x * x'.
Proof.
have := error_x_K.
set K := _ + _ => /=.
suff F : 8 * K <= 7 by split_Rabs; nra.
have : 4 * (IZR beta + 1) * u <= 3.
  rewrite /u bpow_plus pow1E.
  have : IZR beta ^ 2  * pow (-p) <= 1.
    rewrite -pow1E -pow2M -bpow_plus.
    by apply: (@bpow_le _ _ 0); lia.
  by have := beta_ge_2; nra.
suff : 8 * (IZR beta) * u ^ 2 <= 1 by rewrite /K; nra.
     have Hb2 := beta_ge_2;
     have : / IZR beta <= /2 by apply: Rinv_le; lra.
    suff : IZR beta * u ^ 2 <= /4 * / IZR beta by nra.
    rewrite -pow1E -bpow_opp /u.
    have -> : (- (1) = -1)%Z by lia.
    have : pow (3 - 2 * p) <= pow (- 1) by apply: bpow_le; lia.
    have -> : (3 - 2 * p = 1 + 2 * (1 - p))%Z by lia.
    by rewrite bpow_plus pow2M; nra.
Qed.

(* 3.4 *)
Lemma eps1_le : Rabs eps1 <= /2 * (IZR beta) * (ulp x).
Proof.
have [Hc | [Hc | Hc]] := C_case; last 2 first.
- have -> : eps1 = RN x - x.
    by rewrite /eps1 /f' /f /w' [RN (b * c)]round_generic.
  have := beta_ge_2.
  have := error_bound_ulp_u x.
  by split_Rabs; nra.
- have -> : eps1 = 0 by rewrite /eps1 /f'  round_generic //; lra.
  by have := ulp_ge_0 beta fexp x; have := beta_ge_2; split_Rabs; nra.
apply: Rle_trans eps1_bound _.
rewrite Rmult_assoc; apply: Rmult_le_compat_l; first by lra.
rewrite -pow1E Rmult_comm -ulp_FLX_exact_shift.
apply: ulp_le.
rewrite Rabs_mult Rabs_pow.
have -> : f = x - e by rewrite xE; lra.
apply: Rle_trans (_ : Rabs x + Rabs e <= _); first by split_Rabs; lra.
by have := me_mult_mx_le Hc; rewrite pow1E; lra.
Qed.

Lemma eps2_le : Rabs eps2 <= /2 * (IZR beta) * (ulp x).
Proof.
have [Hc | [Hc | Hc]] := C_case; last 2 first.
- have -> : eps2 = 0. 
    rewrite /eps2 /x' /f' /f /e /w' [RN (b * c)]round_generic //.
    rewrite Rminus_eq_0 Rplus_0_r round_generic; first by lra.
    by apply: generic_format_round.
  by have := ulp_ge_0 beta fexp x; have := beta_ge_2; split_Rabs; nra.
- have -> : eps2 = RN x - x by rewrite /eps2 /x' /f' [RN f]round_generic // -xE.
    have := beta_ge_2.
  have := error_bound_ulp_u x.
  by split_Rabs; nra.
apply: Rle_trans eps2_bound _.
rewrite Rmult_assoc; apply: Rmult_le_compat_l; first by lra.
suff : ulp (f' + e) < pow 2 * ulp x.
  have [->|fe_eq_0] := Req_dec (f' + e) 0.
    by rewrite ulp_FLX_0; have := beta_ge_2; have := ulp_ge_0 beta fexp x; nra.
  rewrite !ulp_neq_0 //; last by apply: C_imp_x_neq_0.
  rewrite -pow1E -!bpow_plus.
  by move=> /lt_bpow H; apply: bpow_le; lia.
have -> : f' + e = x + eps1 by rewrite /eps1 xE; lra.
apply: Rle_lt_trans (@ulp_FLX_le beta p _ (x + eps1)) _.
apply: Rle_lt_trans (_ : Rabs x * pow (1 - p) + Rabs eps1 *  pow (1 - p) < _).
  by have := bpow_gt_0 beta (1 - p); split_Rabs; nra.
apply: Rle_lt_trans (_ : pow (1 - p) * Rabs x + 
                      / 2 * IZR beta * pow (1 - p) * ulp x  < _).
  by have := eps1_le; have := bpow_gt_0 beta (1 - p); nra.
rewrite bpow_plus pow1E.
apply: Rle_lt_trans (_ : 
    (IZR beta + / 2 * IZR beta * (IZR beta * pow (- p))) * ulp x < _ ).
  by have := @ulp_FLX_ge beta p p_gt_0 x; have := beta_ge_2; nra.
apply: Rmult_lt_compat_r.
  by rewrite ulp_neq_0; [apply: bpow_gt_0 | apply: C_imp_x_neq_0].
rewrite -pow1E !Rmult_assoc -!bpow_plus.
have : pow(1 + (1 + - p)) <= 1. by suff -> : 1 = pow 0 by apply: bpow_le; lia.
have : pow 2 = (IZR beta) ^ 2 by rewrite -pow1E -pow2M; congr (pow _); lia.
rewrite pow1E; have := beta_ge_2; nra.
Qed.

(* Prop 3.5 *)
Lemma error_x_beta_ulp : Rabs (x' - x) <= IZR beta * ulp x.
Proof.
by rewrite x'BxE; have := eps1_le; have := eps2_le; split_Rabs; lra.
Qed.

(* Prop 4.1 *)
Lemma error_x_cond_half_ulp : 
  Rabs eps2 <= /2 * ulp x -> Rabs (x' - x) <= Rabs eps1 + /2 * ulp x.
Proof. by rewrite x'BxE; split_Rabs; lra. Qed.

Lemma error_x_cond_half_ulp_u : 
  Rabs eps2 <= /2 * ulp x -> Rabs (x' - x) <= 2 * u * Rabs x.
Proof.
move=> eps2_le.
have [Hc|Hc] := C_case; last first.
  have -> : x' = RN x.
    by have [/format_bc_x'_RN_x | /format_f_x'_RN_x] := Hc.
  have := u_gt_0; have : 0 <= Rabs x by split_Rabs; lra.
  by have := error_bound_ulp_u x; nra.
have x_neq_0 := C_imp_x_neq_0 Hc.
have mx_neq_0 : mx <> 0.
  have [mu [_ _ _ mxE _]] := mu_def.
  by move=> F1; case:  C_imp_x_neq_0 => //; rewrite mxE F1; lra.
have [eps1_le | eps1_gt] := Rle_dec (Rabs eps1) (/2 * ulp x).
  apply: Rle_trans (_ : ulp x <= _).
    by have := error_x_cond_half_ulp; lra.
  have := error_bound_ulp_u x; lra.
have F4_1 : Rabs (x' - x) <= /2 * (IZR beta + 1) * ulp x.
  by have := eps1_le; have := error_x_cond_half_ulp; lra.
have F : ulp x = / IZR beta * ulp f.
  apply: Rle_antisym.
    have F1 : ulp x < ulp f by have := eps1_bound; lra.
    have f_neq_0 : f <> 0.
      move=> f_eq_0; rewrite f_eq_0 ulp_FLX_0 in F1.
      have := ulp_ge_0 beta fexp x; lra.
    move: F1; rewrite !ulp_neq_0 //.
    move=> /lt_bpow F1; rewrite -pow1E -bpow_opp -bpow_plus.
    by apply: bpow_le; lia.
  rewrite Rmult_comm -[_ * / _]/(_ / _).
  apply/Rle_div_l; first by apply: radix_pos.
  rewrite -pow1E -ulp_FLX_exact_shift.
  apply: ulp_le; rewrite Rabs_mult Rabs_pow pow1E.     
  apply: Rle_trans (_ : Rabs x + Rabs e <= _); last first.
    by have := me_mult_mx_le Hc; lra.
  by rewrite xE; split_Rabs; lra. 
have F1 : ulp f = IZR beta * ulp x.
  by rewrite F; field; have := beta_ge_2; lra.
have F1' : ulp mf = IZR beta * ulp mx.
  have := F1.
  have [mu [_ -> _ -> _]] := mu_def.
  rewrite !ulp_FLX_exact_shift.
  by have := bpow_gt_0 beta mu; nra.
pose eta := Rabs me / ulp mx.
have ulpx_gt_0 : 0 < ulp x by rewrite ulp_neq_0 //; apply: bpow_gt_0.
have F2 : eta <= /2 * (pow p - pow (p - 1)) -> Rabs (x' - x) <= 2 * u * Rabs x.
  move=> eta_le.
  have F2 : Rabs x < pow p * ulp x <= Rabs x + Rabs e.
    split.
      have Fp := bpow_gt_0 beta p.
      rewrite Rmult_comm; apply/Rlt_div_l; first by lra.
      rewrite /Rdiv -bpow_opp; have := ulp_FLX_gt x_neq_0; nra.
    rewrite F -pow1E -bpow_opp -Rmult_assoc -bpow_plus.
    have -> : (p + - (1) = - (1 - p))%Z by lia.
    apply: Rle_trans (_ : Rabs f <= _); last by rewrite xE; split_Rabs; lra.
    rewrite bpow_opp Rmult_comm.
    apply/Rle_div_l; first by apply: bpow_gt_0.
    by apply: ulp_FLX_le.
  have F3 : 0 < pow p - Rabs x  / ulp x <= eta.
    have -> : pow p - Rabs x / ulp x = (pow p * ulp x - Rabs x) / ulp x.
      by field; lra.
    split; first by apply: Rdiv_lt_0_compat; lra.
    apply/Rle_div_l => //.
    suff -> : eta * ulp x = Rabs e by lra.
    have [mu [-> _ _ mxE _]] := mu_def.
    rewrite mxE Rabs_mult Rabs_pow ulp_FLX_exact_shift /eta.
    suff ulp_mu_gt_0 : 0 < ulp mx by field; lra.
    rewrite ulp_neq_0; last by lra.
    by apply: bpow_gt_0.
  pose K' := /2 * /(pow p - eta) * (IZR beta + 1).
  have F4 : eta < pow p -> Rabs (x' - x) <= K' * Rabs x.
    move=> eta_lt.
    apply: Rle_trans F4_1 _.
    rewrite /K'.
    suff : ulp x <= / (pow p - eta) * Rabs x.
      by have := beta_ge_2; nra.
    rewrite Rmult_comm; apply/Rle_div_r; first by lra.
    by rewrite Rmult_comm; apply/Rle_div_r; lra.
  have F5 : /2 * (pow p - pow (p - 1)) < pow p.
    by have := bpow_gt_0 beta p; have := bpow_gt_0 beta (p - 1); lra.
  have F6 : eta < pow p by apply: Rle_lt_trans eta_le _; lra.
  have F7 : Rabs (x' - x) <= K' * Rabs x by apply/F4/F6.
  suff :  K' <= 2 * u by split_Rabs; nra.
  rewrite /K' /u.
  apply: Rle_trans (_ : / (pow p + pow (p - 1)) * (IZR beta + 1) <= _).
     suff : /(pow p - eta) <= 2 / (pow p + pow (p - 1)).
      by have := beta_ge_2; nra.
    have -> : 2 / (pow p + pow (p - 1)) = / (/2 * (pow p + pow (p - 1))).
      by field; have := bpow_gt_0 beta p; have := bpow_gt_0 beta (p - 1); lra.
    by apply: Rinv_le; try lra.
  rewrite Rmult_comm.
  apply/Rle_div_l.
    have := bpow_gt_0 beta p; have := bpow_gt_0 beta (p - 1); lra.
  rewrite!Rmult_assoc Rmult_plus_distr_l -!bpow_plus.
  have -> : (1 - p + p = 1)%Z by lia.
  have -> : (1 - p + (p  - 1) = 0)%Z by lia.
  by rewrite -pow1E  pow0E; lra.
have F_gt : pow p < Rabs mf.
  have [|] := Rle_dec (Rabs mf) (pow p); last by lra.
  have [mu [_ mfE _ _ _]] := mu_def => H.
  pose fx := Float beta mF mu.
  have [_ []] := Hc.
  by apply: (@FLX_format_Rabs_Fnum f fx).
have F3 : IZR beta <= ulp mf.
  have -> : IZR beta = ulp (pow p).
    rewrite -pow1E ulp_bpow; congr bpow.
    by rewrite /fexp /cexp; lia.
  by apply: ulp_le; rewrite Rabs_pow; lra.
have [F4 F5] : 1 <= ulp mx /\ Rabs mx < Rabs mf.
  split; first by have := beta_ge_2; nra.
  have : (IZR beta) * (Rabs mx * pow (- p)) < Rabs mf * pow (1 - p).
    apply: Rlt_le_trans (@ulp_FLX_le beta p _ mf).
    rewrite F1'.
    apply: Rmult_lt_compat_l; first by have := beta_ge_2; lra.
    by apply: ulp_FLX_gt.
  rewrite Rmult_comm Rmult_assoc -pow1E -bpow_plus.
  have -> : (- p + 1 = 1 - p)%Z by lia.
  by have := bpow_gt_0 beta (1 - p); nra.
have [sigma_pos | [sigma_N1 | sigma_leN2]] :
   (0 <= sigma \/ (sigma = -1 \/ sigma <= -2))%Z by lia.
- have Hl : is_left (Z_le_dec 0 sigma) by case: Z_le_dec=> //; lia.
  have me_le : Rabs me <= /2 * pow p.
    apply: Rle_trans (_ : /2 * ulp (mb * mc) <= _).
      have := error_bound_ulp_u (mb * mc).
      rewrite /me /mE Hl minus_IZR mult_IZR /mW' -iRNE mult_IZR -mbE -mcE.
      by lra. 
    by have := ulp_mbc_le Hc; lra.
  have [umxE| umxE]:= Req_dec (ulp mx) 1; last first.
    apply: F2.
    apply/Rle_div_l; try lra.
    apply: Rle_trans me_le _.
    apply: Rle_trans (_ : / 2 * (pow (p + 1) - pow p) <= _).
      rewrite bpow_plus pow1E; have := beta_ge_2; have := bpow_gt_0 beta p.
      by nra.
    have -> : pow (p + 1) - pow p = (pow p - pow (p - 1)) * IZR beta.
      rewrite -pow1E Rmult_minus_distr_r -!bpow_plus.
      by congr (pow _ - pow _); lia.
    suff : IZR beta <= ulp mx.
      suff : pow (p - 1) < pow p by nra.
      by apply: bpow_lt; lia.
    have : 1 < ulp mx by lra.
    rewrite ulp_neq_0 // -pow1E -(pow0E beta) => /lt_bpow H.
    by apply: bpow_le; lia.
  have F6 : Rabs (mx' - mx) <= /2 * IZR beta.
    suff : 2 * Rabs (mx' - mx) <= IZR beta by lra.
    suff:  2 * Rabs (mx' - mx) <= (IZR beta + 1).
      rewrite /mx' /mx -minus_IZR Rabs_Zabs -plus_IZR -mult_IZR.
      move=> /le_IZR H; apply/IZR_le.
      suff hbetaE : (beta = 2 * (beta / 2) :> Z)%Z by lia.
      have [b2 ->]:= Zeven_ex beta; rewrite Hbeta_even.
      by rewrite Zplus_0_r [(2 * b2)%Z]Zmult_comm Z.div_mul; lia.
    have [mu [_ _ _ mxE mx'E]] := mu_def.
    have powmu_gt_0 := bpow_gt_0 beta mu.
    suff : 2 * Rabs (x' - x) <= (IZR beta + 1) * pow mu.
      by rewrite mx'E mxE -Rmult_minus_distr_r Rabs_mult Rabs_pow; nra.
    apply: Rle_trans (_ : (IZR beta + 1) * ulp x <= _); first by lra.
    rewrite Rplus_comm; apply: Rmult_le_compat_l.
      by have := radix_pos beta; lra.
    by rewrite mxE ulp_FLX_exact_shift umxE; lra.
  have [mu [meE mfE  _ mxE mx'E]] := mu_def.
  rewrite mxE mx'E -Rmult_minus_distr_r !Rabs_mult Rabs_pow.
  have powmu_gt_0 := bpow_gt_0 beta mu.
  apply: Rle_trans (_ : / 2 * IZR beta * pow mu <= _); first by nra.
  suff : IZR beta  <= 4 * u * Rabs mx by nra.
  apply: Rle_trans (_ : 2 * u * pow p <= _); last first.
    have := u_gt_0.
    suff : /2 * pow p <= Rabs mx by nra.
    have -> : mx = me + mf by have := xE; rewrite mxE mfE meE; nra.
    apply: Rle_trans (_ : Rabs mf - Rabs me <= _); last by split_Rabs; lra.
    by lra.
  rewrite /u !Rmult_assoc -bpow_plus -pow1E.
  have -> : (1 - p + p = 1)%Z by lia.
  by lra.
- have Hr : is_left (Z_le_dec 0 sigma) = false by case: Z_le_dec=> //; lia.
  have [bcLp1|p2Lbc] := Rle_dec (Rabs (mb * mc)) (pow (2 * p - 1)).
    have me_le : Rabs me <= /2 * pow p.
      have [xF1|xF1] :=  Req_dec (pow (2 * p - 1)) (Rabs (mb * mc)).
        rewrite /me /mE Hr /mW' mult_IZR minus_IZR -iRNE round_generic.
          by have := bpow_gt_0 beta p; split_Rabs; lra.
        rewrite mult_IZR -mbE -mcE.
        move: xF1; rewrite /Rabs; split_case_Rabs => xF1; last first.
          by rewrite -xF1; apply: generic_format_bpow'; rewrite /fexp; lia.
        rewrite -[_ * _]Ropp_involutive -xF1.
        by apply/generic_format_opp/generic_format_bpow'; rewrite /fexp; lia.
      rewrite /me /mE Hr mult_IZR IZR_Zpower sigma_N1 // bpow_1
              Rabs_mult Rabs_beta.
      have pE : p = (p - 1 + 1)%Z by lia.
      rewrite [in X in _ <= X]pE bpow_plus bpow_1 -Rmult_assoc.  
      apply: Rmult_le_compat_r; first by apply: IZR_le; lia.
      rewrite -ulp_mbc_lt //; try lra.
      rewrite /mW' minus_IZR -iRNE mult_IZR -mbE -mcE.
      by  have := error_bound_ulp_u (mb * mc); lra.
    have [umxE| umxE]:= Req_dec (ulp mx) 1; last first.
      apply: F2.
      apply/Rle_div_l; try lra.
      apply: Rle_trans me_le _.
      apply: Rle_trans (_ : / 2 * (pow (p + 1) - pow p) <= _).
        rewrite bpow_plus pow1E; have := beta_ge_2; have := bpow_gt_0 beta p.
        by nra.
      have -> : pow (p + 1) - pow p = (pow p - pow (p - 1)) * IZR beta.
        rewrite -pow1E Rmult_minus_distr_r -!bpow_plus.
        by congr (pow _ - pow _); lia.
      suff : IZR beta <= ulp mx.
        suff : pow (p - 1) < pow p by nra.
        by apply: bpow_lt; lia.
      have : 1 < ulp mx by lra.
      rewrite ulp_neq_0 // -pow1E -(pow0E beta) => /lt_bpow H.
      by apply: bpow_le; lia.
    have F6 : Rabs (mx' - mx) <= /2 * IZR beta.
      suff : 2 * Rabs (mx' - mx) <= IZR beta by lra.
      suff:  2 * Rabs (mx' - mx) <= (IZR beta + 1).
        rewrite /mx' /mx -minus_IZR Rabs_Zabs -plus_IZR -mult_IZR.
        move=> /le_IZR H; apply/IZR_le.
        suff hbetaE : (beta = 2 * (beta / 2) :> Z)%Z by lia.
        have [b2 ->]:= Zeven_ex beta; rewrite Hbeta_even.
        by rewrite Zplus_0_r [(2 * b2)%Z]Zmult_comm Z.div_mul; lia.
      have [mu [_ _ _ mxE mx'E]] := mu_def.
      have powmu_gt_0 := bpow_gt_0 beta mu.
      suff : 2 * Rabs (x' - x) <= (IZR beta + 1) * pow mu.
        by rewrite mx'E mxE -Rmult_minus_distr_r Rabs_mult Rabs_pow; nra.
      apply: Rle_trans (_ : (IZR beta + 1) * ulp x <= _); first by lra.
      rewrite Rplus_comm; apply: Rmult_le_compat_l.
        have := radix_pos beta; lra.
      by rewrite mxE ulp_FLX_exact_shift umxE; lra.
    have [mu [meE mfE  _ mxE mx'E]] := mu_def.
    rewrite mxE mx'E -Rmult_minus_distr_r !Rabs_mult Rabs_pow.
    have powmu_gt_0 := bpow_gt_0 beta mu.
    apply: Rle_trans (_ : / 2 * IZR beta * pow mu <= _); first by nra.
    suff : IZR beta  <= 4 * u * Rabs mx by nra.
    apply: Rle_trans (_ : 2 * u * pow p <= _); last first.
      have := u_gt_0.
      suff : /2 * pow p <= Rabs mx by nra.
      have -> : mx = me + mf by have := xE; rewrite mxE mfE meE; nra.
      apply: Rle_trans (_ : Rabs mf - Rabs me <= _); last by split_Rabs; lra.
      by lra.
    rewrite /u !Rmult_assoc -bpow_plus -pow1E.
    have -> : (1 - p + p = 1)%Z by lia.
    by lra.
  have me_le : Rabs me <= /2 * pow (p + 1).
    rewrite /me /mE Hr mult_IZR IZR_Zpower sigma_N1 // bpow_1
            Rabs_mult Rabs_beta bpow_plus bpow_1 -Rmult_assoc.  
    apply: Rmult_le_compat_r; first by apply: IZR_le; lia.
    rewrite -ulp_mbc_ge //; try lra.
    rewrite /mW' minus_IZR -iRNE mult_IZR -mbE -mcE.
    by  have := error_bound_ulp_u (mb * mc); lra.
  have [umx_ge|umx_le] : pow 2 <= ulp mx \/ ulp mx <= pow 1.
  - rewrite ulp_neq_0 //.
    have [H|H] : (2 <= cexp mx \/ cexp mx <= 1)%Z by lia.
      by left; apply: bpow_le.
    by right; apply: bpow_le.
  - apply: F2.
    apply: Rle_trans (_ : /2 *  pow (p - 1) <= _); last first.
      suff : 2 * pow (p - 1) <= pow p by lra.
      have -> : pow p = IZR beta * pow (p - 1).
        by rewrite -pow1E -bpow_plus; congr bpow; lia.
      by have := beta_ge_2; have := bpow_gt_0 beta (p - 1); nra.
    apply/Rle_div_l; first by lra.
    apply: Rle_trans me_le _.
    have -> : (p + 1 = (p - 1) + 2)%Z by lia.
    by rewrite bpow_plus; have := bpow_gt_0 beta (p -1); nra.
  have pow_RN_le :  pow (2 * p - 1) <= RN (Rabs (mb * mc)).
   by  rewrite -RN_pow; apply: round_le; lra.
  have [RN_eq|RN_ge] : RN (Rabs (mb * mc)) = pow (2 * p - 1) \/
             pow (2 * p - 1) + pow p <= RN (Rabs (mb * mc)).
  - have -> : pow (2 * p - 1) + pow p = succ beta fexp (pow (2 * p - 1)).
      rewrite /succ; case: Rle_bool_spec => [_|]; last first.
        by have := bpow_gt_0 beta (2 * p - 1); lra.
      by rewrite ulp_bpow; congr (_ + pow _); rewrite /fexp /cexp; lia.
    have [|] :=  Req_dec (pow (2 * p - 1)) (RN (Rabs (mb * mc))); first by left.
  right.
  apply: succ_le_lt; first by apply: format_pow.
    by apply: generic_format_round.
  by lra.
  - suff :  pow (2 * p) < Rabs (ma * md).
      have := ad_bound Hc.
      suff : 1 < pow p by lra.
      by apply: (bpow_lt _ 0); lia.
    have mbc_neq_0 : mb * mc <> 0.
      have := C_imp_abcd_neq_0 Hc.
      rewrite bE cE => H H1; case: H.
      by ring[H1].
    have [mbc_gt0|mbc_le0] : 0 < mb * mc \/ mb * mc < 0 by lra.
      have me_lt0 : me < 0.
        rewrite /me /mE Hr sigma_N1 mult_IZR IZR_Zpower; last by lia.
        rewrite minus_IZR -iRNE mult_IZR -mbE  -mcE.
        have -> : (- (-1) = 1)%Z by lia.
        suff : RN (mb * mc) < mb * mc by have := bpow_gt_0 beta 1; nra.
        by rewrite -[mb * mc]Rabs_pos_eq; lra.
      have : 0 < mf.
        by move: F5; rewrite /mx /mX plus_IZR -/mf -/me; split_Rabs; lra.
      rewrite /mf /mF /mW' Hr sigma_N1 minus_IZR !mult_IZR -iRNE mult_IZR.
      rewrite -maE  -mdE -mbE -mcE -[mb * mc]Rabs_pos_eq; last by lra.
      rewrite RN_eq Rmult_1_r -pow1E -bpow_plus.
      have -> : (2 * p - 1 + 1 = 2 * p)%Z by lia.
      by have := bpow_gt_0 beta (2 * p); split_Rabs; lra.
    have me_gt0 : 0 < me.
      rewrite /me /mE Hr sigma_N1 mult_IZR IZR_Zpower; last by lia.
      rewrite minus_IZR -iRNE mult_IZR -mbE  -mcE.
      have -> : (- (-1) = 1)%Z by lia.
      suff : - RN (mb * mc) < - (mb * mc) by have := bpow_gt_0 beta 1; nra.
      by rewrite -RN_sym // -Rabs_left; lra.
    have : mf < 0.
      by move: F5; rewrite /mx /mX plus_IZR -/mf -/me; split_Rabs; lra.
    rewrite /mf /mF /mW' Hr sigma_N1 minus_IZR !mult_IZR -iRNE mult_IZR.
    rewrite -maE  -mdE -mbE -mcE /Rminus Ropp_mult_distr_l -RN_sym //.
    rewrite -Rabs_left; last by lra.
    rewrite RN_eq Rmult_1_r -pow1E -bpow_plus.
    have -> : (2 * p - 1 + 1 = 2 * p)%Z by lia.
    by have := bpow_gt_0 beta (2 * p); split_Rabs; lra.
  have me_gt : pow (p + 1) + /2 * pow p < Rabs mf.
    apply: Rlt_le_trans (_ : (IZR beta) * (pow (2 * p - 1) + pow p) -
                             (pow (2 * p) - 2 * pow p + 1) <= _).
      rewrite -pow1E Rmult_plus_distr_l -!bpow_plus.
      have -> : (1 + (2 * p - 1) = 2 * p)%Z by lia.
      have -> : (1 + p = p + 1)%Z by lia.
      suff :  1 <= pow p by lra.
      by apply: (bpow_le _ 0); lia.
    rewrite /mf /mF Hr sigma_N1 minus_IZR !mult_IZR Rmult_1_r.
    rewrite -maE -mdE -iRNE mult_IZR -mbE -mcE.
    apply: Rle_trans (_ : RN (Rabs (mb * mc) * IZR beta) -
                             Rabs (ma * md)  <= _); last first.
      rewrite -pow1E RN_mult_pow pow1E RN_abs.
      by have := beta_ge_2; rewrite /Rabs; split_case_Rabs; nra.
    rewrite -pow1E RN_mult_pow [pow 1 * _]Rmult_comm pow1E.
    by have := ad_bound Hc; have := radix_pos beta; nra.
  have mx_gt : /2 * (IZR beta + 1) * pow p < Rabs mx.
    rewrite /mx /mX plus_IZR -/mf -/me.
    apply: Rlt_le_trans (_ : Rabs mf - Rabs me <= _); last first.
      by rewrite /Rabs; split_case_Rabs; lra.
    rewrite bpow_plus pow1E in me_gt me_le.
    by lra.
  apply: Rle_trans F4_1 _.
  have [mu [_ _ _ -> _]] := mu_def.
  have powmu_gt_0 := bpow_gt_0 beta mu.
  rewrite ulp_FLX_exact_shift Rabs_mult Rabs_pow.
  suff : / 2 * (IZR beta + 1) * ulp mx <= 2 * u * Rabs mx by nra.
  suff : / 2 * pow 1 <= pow p * u.
    by have := radix_pos beta; have := u_gt_0; nra.
  suff : pow 1 = pow p * pow (1 - p) by rewrite /u; lra.
  by rewrite -bpow_plus; congr bpow; lia.
pose i := (- sigma)%Z.
have i_ge : (2 <= i)%Z by lia.
have Hr : is_left (Z_le_dec 0 sigma) = false by case: Z_le_dec=> //; lia.
have [me_le mx_ge1]:= me_le_y_le_mx  Hc i_ge.
rewrite -/i in mx_ge1 me_le; set y :=  _ + _ - _ in mx_ge1.
have [iE2 | i_ge3] : (i = 2 \/ 3 <= i)%Z by lia.
  have mx_ge : 2 * pow (p + 1) + pow 2 < Rabs mx.
    have <- : pow 2 * (pow (p - 1) + 1) ^ 2 - pow (2 * p) = 
              2 * pow (p + 1) + pow 2.
      have  -> : pow (2 * p) = pow 2 * pow (p - 1) ^ 2.
        by rewrite -pow2M -bpow_plus; congr (pow _); lia.
      have  -> : pow (p + 1) = pow 2 * pow (p - 1).
        by rewrite -bpow_plus; congr (pow _); lia.
      by lra.
    rewrite /mx /mX /mF /mE Hr -/i iE2 plus_IZR minus_IZR 3!mult_IZR.
    rewrite minus_IZR mult_IZR -maE -mdE -mbE -mcE IZR_Zpower; last by lia.
    apply: Rlt_le_trans (_ : pow 2 * Rabs (mb * mc) - Rabs (ma * md) <= _);
        last first.
      by rewrite /Rabs; split_case_Rabs; lra.
    have : (pow (p - 1) + 1) ^ 2 <= Rabs (mb * mc).
      rewrite Rabs_mult.
      have := mb_ge_powp1 Hc; have := mc_ge_powp1 Hc;
        have := bpow_gt_0 beta (p - 1).
      nra.
    suff:  Rabs (ma * md) < pow (2 * p) by have := bpow_gt_0 beta 2; nra.
    rewrite pow2M Rabs_mult.
    have a_neq_0 : a <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
    have d_neq_0 : d <> 0 by have := C_imp_abcd_neq_0 Hc; nra.
    have ba := mant_bound_le Fa a_neq_0; rewrite -/ma in ba.
    have bd := mant_bound_le Fd d_neq_0; rewrite -/md in bd.
    have : 0 <= Rabs ma by rewrite /Rabs; split_case_Rabs; lra.
    have : 0 <= Rabs md by rewrite /Rabs; split_case_Rabs; lra.
    by nra.
  have ulp_mx_ge : pow 2 <= ulp mx.
    pose f := Float beta (2 * Z.pow beta (p - 1) +1) 2.
    rewrite ulp_neq_0 //.
    apply: bpow_le.
    rewrite /cexp /fexp.
    suff: (2 + p <= mag beta mx)%Z by lia.
    apply: mag_ge_bpow.
    have -> : (2 + p - 1 = p + 1)%Z by lia.
    by have := bpow_gt_0 beta 2; have := bpow_gt_0 beta (p + 1); nra.
  have [bcLp1|p2Lbc] := Rle_dec (Rabs (mb * mc)) (pow (2 * p - 1)).
    have me_le1 : Rabs me <= /2 * pow (p + 1).
      have [xF1|xF1] :=  Req_dec (pow (2 * p - 1)) (Rabs (mb * mc)).
        rewrite /me /mE Hr /mW' mult_IZR minus_IZR -iRNE round_generic.
          by have := bpow_gt_0 beta (p + 1); split_Rabs; lra.
        rewrite mult_IZR -mbE -mcE.
        move: xF1; rewrite /Rabs; split_case_Rabs => xF1; last first.
          by rewrite -xF1; apply: generic_format_bpow'; rewrite /fexp; lia.
        rewrite -[_ * _]Ropp_involutive -xF1.
        by apply/generic_format_opp/generic_format_bpow'; rewrite /fexp; lia.
      rewrite /me /mE Hr mult_IZR IZR_Zpower -/i iE2 // Rabs_mult Rabs_pow.
      have pE : (p + 1 = p - 1 + 2)%Z by lia.
      rewrite [in X in _ <= X]pE bpow_plus -Rmult_assoc. 
      apply: Rmult_le_compat_r; first by apply: IZR_le; lia.
      rewrite -ulp_mbc_lt //; try lra.
      rewrite /mW' minus_IZR -iRNE mult_IZR -mbE -mcE.
      by  have := error_bound_ulp_u (mb * mc); lra.
    apply: F2.
    apply/Rle_div_l.
      rewrite ulp_neq_0; last by lra.
      by apply: bpow_gt_0; lra.
    apply: Rle_trans me_le1 _.
    have pD1_ge := bpow_gt_0 beta (p + 1).
    suff : pow (p + 1) <= (pow p - pow (p - 1)) *  pow 2.
      have := bpow_le beta p (p - 1).
      by have := bpow_gt_0 beta 2; nra.
    rewrite Rmult_minus_distr_r -!bpow_plus.
    have -> : (p + 2 = p + 1 + 1)%Z by lia.
    have -> : (p - 1 + 2 = p + 1)%Z by lia.
    rewrite [pow (_ + _ + 1)]bpow_plus pow1E.
    by have := beta_ge_2; nra.
  have me_le2 : Rabs me <= /2 * pow (p + 2) by rewrite -[in (_ + _)%Z]iE2.
  have FF1 : pow (p + 1) <= ulp mx.
    have -> : (p + 1 = fexp (2 * p + 1))%Z by rewrite /fexp; lia.
    rewrite -ulp_bpow; apply: ulp_le; rewrite Rabs_pow.
    apply: Rle_trans (_ : Rabs(mb * mc) * pow 2 - Rabs (ma * md) <= _); 
          last first.
      suff -> : mx = ma * md - mb * mc * pow 2 by split_Rabs; lra.
      rewrite /mx /mX /mF /mE Hr plus_IZR minus_IZR !mult_IZR minus_IZR.
      rewrite mult_IZR -maE -mdE -mbE -mcE -/i iE2 IZR_Zpower; last by lia.
      by lra.
    have :  pow (2 * p - 1) * pow 2 <= Rabs (mb * mc) * pow 2.
      by have := bpow_gt_0 beta 2; nra.
    have -> :  pow (2 * p - 1) * pow 2 =  pow (2 * p) * pow 1.
      by rewrite -!bpow_plus; congr (pow _); lia.
    suff : 2 * pow (2 * p) - 2 * pow p + 1 <= pow (2 * p) * pow 1.
      by have := ad_bound Hc; nra.
    rewrite pow1E.
    have := bpow_gt_0 beta (2 * p); have := beta_ge_2.
    suff : 1 < pow p by nra.
    by apply:  (bpow_lt beta 0 p); lia.
  apply: F2.
  apply/Rle_div_l.
    rewrite ulp_neq_0; last by lra.
    by apply: bpow_gt_0; lra.
  apply: Rle_trans me_le2 _.
  suff : pow (p + 2) <= (pow p - pow (p - 1)) * ulp mx by lra.
  have xF1 : pow (p - 1) + pow 1 <= pow p.
    have -> : pow p = pow (p - 1) * pow 1.
      by rewrite -bpow_plus; congr (pow _); lia.
    have xF1 : pow 1 <= pow (p - 1) by  apply: bpow_le; lia.
    have : 2 <= pow 1 by rewrite pow1E; apply: beta_ge_2.
    by nra.
  have -> : pow (p + 2) = pow (p + 1) * pow 1.
    by rewrite -bpow_plus; congr (pow _); lia.
  have := bpow_gt_0 beta 1.
  by nra.
apply: F2.
apply: Rle_trans (_ : /2 * pow (p -1) <= _); last first.
  suff : 2 * pow (p - 1) <= pow p by lra.
  have -> : pow p = pow (p - 1) * pow 1.
    by rewrite -bpow_plus; congr (pow _); lia.
  by rewrite pow1E; have := beta_ge_2; have := bpow_gt_0 beta (p - 1); nra.
apply/Rle_div_l.
  by rewrite ulp_neq_0 //; have := bpow_gt_0 beta (cexp mx); lra.
apply: Rle_trans me_le _.
have -> : (p + i = p - 1 + (i + 1))%Z by lia.
rewrite bpow_plus.
suff: pow (i + 1) <= ulp mx by have := bpow_gt_0 beta (p - 1); nra.
have -> : (i + 1 = fexp (p + i + 1))%Z.
   by rewrite /fexp; lia.
rewrite -ulp_bpow; apply: ulp_le; rewrite Rabs_pow.
suff : 1 <= y by have := bpow_gt_0 beta (p + i); nra.
rewrite /y.
have xF1 := bpow_gt_0 beta 1.
have xFN1 := bpow_gt_0 beta (-1).
have xF2 := bpow_gt_0 beta 2.
have xFi := bpow_gt_0 beta i.
have xFNi := bpow_gt_0 beta (-i).
have xFp := bpow_gt_0 beta (p - 2).
have xFb := beta_ge_2.
have [->|p_ge3] : (p = 2 \/ p >= 3)%Z by lia.
  have -> : (2 - 2 = 0)%Z by lia.
  suff : pow 2 * pow (- i) <= pow (-1) by rewrite pow0E; nra.
  by rewrite -bpow_plus; apply: bpow_le; lia.
suff : 1 + pow p * pow (-i) <= pow (p - 2) by nra.
have <- : pow i * pow (- i) = 1
  by rewrite -bpow_plus -(pow0E beta); congr (pow _); lia.
have -> : (p - 2 = p + i - 2 - i)%Z by lia.
suff : pow i + pow p <= pow (p + i - 2).
  by rewrite [in X in _ -> X]bpow_plus; nra.
have [pLi|iLp] : (p <= i \/ i <= p)%Z by lia.
  apply: Rle_trans (_ : pow (i + 1) <= _).
    by rewrite bpow_plus pow1E; have := bpow_le beta _ _ pLi; nra.
  by apply: bpow_le; lia.
apply: Rle_trans (_ : pow (p + 1) <= _).
  by rewrite bpow_plus pow1E; have := bpow_le beta _ _ iLp; nra.
by apply: bpow_le; lia.
Time Qed.

(* Prop 4.2 *)

Lemma eps2_gt_x_neq_0 : /2 * ulp x < Rabs eps2 -> x <> 0.
Proof.
move=> eps2_gt x_eq_0; rewrite x_eq_0 ulp_FLX_0 in eps2_gt.
suff: eps2 = 0 by split_Rabs; lra.
rewrite /eps2 /x'.
suff -> : f' = - e.
  have -> : - e + e = 0 by lra.
  by rewrite round_0; lra.
rewrite /f'.
have -> : f = -e by rewrite xE in x_eq_0; lra.
by rewrite RN_sym // (round_generic _ _ _ _ Fe).
Qed.

Lemma f'e_ge_eps2_gt :
  /2 * ulp x < Rabs eps2 -> pow p * ulp(x) <= Rabs (f' + e).
Proof.
move=> eps2_gt.
have x_neq_0 := eps2_gt_x_neq_0 eps2_gt.
have xFp := bpow_gt_0 beta p.
have xFp1 := bpow_gt_0 beta (p - 1).
have xFNp1 := bpow_gt_0 beta (1 - p).
apply: Rle_trans (_ : pow (p - 1) * ulp (f' + e) <= _); last first.
  by have := ulp_FLX_bound_le beta Hp2 (f' + e); lra.
have -> : pow p = pow (p - 1) * pow 1.
  by rewrite -bpow_plus; congr (pow _); lia.
suff: pow 1 *  ulp x <= ulp (f' + e) by nra.
rewrite pow1E.
apply: ulp_lt_le => //.
by have := eps2_bound; lra.
Qed.

Lemma x'E_eps2_gt : /2 * ulp x < Rabs eps2 -> Rabs x' = pow p * ulp(x). 
Proof.
move=> eps2_gt.
have x_neq_0 := eps2_gt_x_neq_0 eps2_gt.
have xFp := bpow_gt_0 beta p.
have f'e_ge := f'e_ge_eps2_gt eps2_gt.
have mx_le : Rabs x <= Rabs (f' + e).
  apply: Rle_trans f'e_ge.
  by have := ulp_FLX_bound_le beta Hp2 x; nra.
have x'_ge : pow p * ulp x <= Rabs x'.
  rewrite /x' -RN_abs ulp_neq_0 // -bpow_plus -RN_pow.
  apply: round_le.
  by rewrite bpow_plus -ulp_neq_0.
have F1 : Rabs x' < (pow p + pow 1) * ulp x.
  apply: Rle_lt_trans (_ : Rabs x + Rabs (x' - x) < _).
    split_Rabs; lra.
  suff : Rabs (x' - x) <= pow 1 * ulp x.
    by have := ulp_FLX_bound beta Hp2 x_neq_0; lra.
  by have := error_x_beta_ulp; rewrite pow1E.
have [//|HD] := Req_dec (Rabs x') (pow p * ulp(x)).
have : succ beta fexp (pow p * ulp(x)) <= Rabs x'.
  apply: succ_le_lt.
  - rewrite ulp_neq_0 // -bpow_plus.
    by apply: format_pow.
  - rewrite -RN_abs.
    by apply: generic_format_round.
  by lra.
suff -> : succ beta fexp (pow p * ulp x) = (pow p + pow 1) * ulp x by lra.
rewrite /succ.
have [_|] := Rle_bool_spec; last first.
  by have := ulp_gt_0 p beta x_neq_0; nra.
suff -> : ulp (pow p * ulp x) = pow 1 * ulp x by lra.
rewrite [ulp x]ulp_neq_0 // -!bpow_plus ulp_bpow.
by congr (pow _); rewrite /fexp; lia.
Qed.

Lemma error_eps1_eps2_gt : 
  /2 * ulp x < Rabs eps2 -> Rabs (x' - x) <= Rabs eps1.
Proof.
move=> eps2_gt.
have x_neq_0 := eps2_gt_x_neq_0 eps2_gt.
have x'E := x'E_eps2_gt eps2_gt.
have -> : Rabs (x' - x) = Rabs x' - Rabs x.
  suff : Rabs x < Rabs x'.
    by have := x'_x_same_sign; split_Rabs; nra.
  by rewrite x'E; have := ulp_FLX_bound beta Hp2 x_neq_0; lra.
suff : Rabs x' <= Rabs x + Rabs eps1 by lra.
apply: Rle_trans (_ : Rabs (x + eps1) <= _); last by split_Rabs; lra.
have <- : f' + e = x + eps1 by rewrite /eps1 xE; lra.
by rewrite x'E; exact: f'e_ge_eps2_gt eps2_gt.
Qed.

Lemma error_L_eps2_gt (L := Rabs eps1 / (pow p * ulp x - Rabs eps1)) : 
  /2 * ulp x < Rabs eps2 -> Rabs (x' - x) <= L * Rabs x.
Proof.
move=> eps2_gt.
have x_neq_0 := eps2_gt_x_neq_0 eps2_gt.
have x'E := x'E_eps2_gt eps2_gt.
have x_ge : pow p * ulp x - Rabs eps1 <= Rabs x.
  suff : pow p * ulp x <= Rabs (x + eps1) by split_Rabs; lra.
  have <- : f' + e = x + eps1 by rewrite /eps1 xE; lra.
  by apply: f'e_ge_eps2_gt.
apply: Rle_trans (error_eps1_eps2_gt eps2_gt) _.
suff : 1 <= Rabs x / (pow p * ulp x - Rabs eps1).
  have : 0 <= Rabs eps1 by split_Rabs; lra.
  by rewrite /L; nra.
apply/Rle_div_r; last by lra.
suff : 0 < pow p * ulp x - /2 * pow 1 * ulp x.
  by rewrite pow1E; have := eps1_le; lra.
suff : pow 1 < pow p by have := bpow_gt_0 beta 1; 
   have := ulp_gt_0 p beta x_neq_0; nra.
by apply: bpow_lt; lia.
Qed.

Lemma error_u_eps2_gt : 
  /2 * ulp x < Rabs eps2 -> Rabs (x' - x) <= u / (1 - u) * Rabs x.
Proof.
move=> eps2_gt.
have x_neq_0 := eps2_gt_x_neq_0 eps2_gt.
have error_L := error_L_eps2_gt eps2_gt.
have eps1_le := eps1_le.
have ulpx_gt_0 := ulp_gt_0 p beta x_neq_0.
have ax_gt_0 : 0 < Rabs x by split_Rabs; lra.
have L_pos : 0 < pow p * ulp x - /2 * pow 1 * ulp x.
  suff : pow 1 < pow p
    by have := bpow_gt_0 beta 1; have := ulp_gt_0 p beta x_neq_0; nra.
  by apply: bpow_lt; lia.
have denom_pos : 0 < pow p * ulp x - Rabs eps1.
  by rewrite pow1E in L_pos; lra.
have -> : u / (1 - u) =
         (/2 * pow 1 * ulp x) / (pow p * ulp x - /2 * pow 1 * ulp x).
  have Fp := bpow_gt_0 beta p.
  have Fp1 : pow 1 < pow p by apply: bpow_lt; lia.
  rewrite /u bpow_plus bpow_opp.
  by field; nra.
apply: Rle_trans error_L _.
suff :  Rabs eps1 / (pow p * ulp x - Rabs eps1) <=
        (/2 * pow 1 * ulp x) / (pow p * ulp x - / 2 * pow 1 * ulp x) by nra.
apply: Rmult_le_compat.
- by split_Rabs; lra.
- by have := Rinv_0_lt_compat _ denom_pos; lra.
- rewrite pow1E; lra.
apply: Rinv_le; last by rewrite pow1E; lra.
by lra.
Qed.

(* Theorem 1.1 *)

Lemma kahan_first_bound : Rabs (x' - x) <= (IZR beta + 1) / 2 * ulp x.
Proof.
apply: Rle_trans (_ : Rabs eps1 + /2 * ulp x <= _); last first.
  by have := eps1_le; lra.
have [eps2_le|eps2_gt] := Rle_dec (Rabs eps2) (/2 * ulp x).
  by apply: error_x_cond_half_ulp.
have ulpx_ge_0 := ulp_ge_0 beta fexp x.
suff : Rabs (x' - x) <= Rabs eps1 by nra.
by apply: error_eps1_eps2_gt; lra.
Qed.

(* Theorem 1.2 *)

Lemma kahan_second_bound : Rabs (x' - x) <= 2 * u * Rabs x.
Proof.
have [eps2_le|eps2_gt] := Rle_dec (Rabs eps2) (/2 * ulp x).
  by apply: error_x_cond_half_ulp_u.
have u_bound : 0 < u <1 := u_bound beta Hp2.
suff : u / (1 - u) <= 2 * u.
  have F : Rabs (x' - x) <= u / (1 - u) * Rabs x.
    apply: error_u_eps2_gt; lra.
  have : 0 <= Rabs x by split_Rabs; lra.
  nra.
apply/Rle_div_l; first by lra.
suff : 3 * u <= 1 by nra.
have : pow (1 - p) <= pow (- (1)) by apply: bpow_le; lia.
rewrite bpow_opp pow1E /u.
have : / IZR beta <= / (3 / 2) by  apply: Rinv_le; have := beta_ge_2; lra.
by lra.
Qed.

Lemma kahan_bound : 
  Rabs (kahan a b c d - (a * d - b * c)) <= 2 * u * Rabs (a * d - b * c).
Proof. 
rewrite /kahan [RN (RN _ - b * c)](round_generic _ _ _ _ Fe).
by apply: kahan_second_bound.
Qed.

(* 5.5 *)
Lemma eps1_ulpx : Rabs e <= /2 * ulp x -> Rabs eps1 <= /2 * ulp x.
Proof.
have [x_eq_0|x_neq_0] := Req_dec x 0.
  rewrite x_eq_0 ulp_FLX_0 => H.
  have e_eq_0 : e = 0 by split_Rabs; lra.
  rewrite /eps1  /f' /f /w'.
  have -> : RN (b * c) = b * c by rewrite /e /w' in e_eq_0; lra.
  by rewrite -/x x_eq_0 round_0; split_Rabs; lra.
have [ufLux|uxLuf] := Rle_lt_dec (ulp f) (ulp x).
  have F24 := eps1_bound; lra.
have f_neq_0 : f <> 0.
  move=> f_eq_0; rewrite f_eq_0 ulp_FLX_0 in uxLuf.
  by have := ulp_gt_0 p beta x_neq_0; lra.
have eps1E : Rabs eps1 = Rabs (RN (Rabs f) - Rabs f).
  rewrite /eps1 /f' RN_abs.
  suff : 0 <= RN f * f by split_Rabs; nra.
  have [f_pos|f_neg] := Rle_lt_dec 0 f.
    have : RN 0 <= RN f by apply: round_le.
    by rewrite round_0; nra.
  have : RN f <= RN 0 by apply: round_le; lra.
  by rewrite round_0; nra.
move=> e_le.
apply: Rle_trans e_le.
apply: Rle_trans (_ : Rabs f - Rabs x <= _); last first.
  by rewrite xE; split_Rabs; lra.
pose y := (Float beta (Z.pow beta (p - 1)) (cexp f)).
have Fy : format (F2R y).
  apply: FLX_format_Rabs_Fnum (refl_equal _) _.
  rewrite -abs_IZR -IZR_Zpower; last by lia.
  apply: IZR_le.
  rewrite /y /= Z.abs_pow Z.abs_eq; last by lia.
  by apply: Zpower_le; lia.
have yE : F2R y = pow (p - 1) * ulp f.
  rewrite /y /F2R /=.
  rewrite IZR_Zpower; try lia.
  by rewrite ulp_neq_0.
have F1 : F2R y <= Rabs f.
  rewrite yE; have := ulp_FLX_bound beta Hp2 f_neq_0; lra.
have F2 : Rabs x < F2R y.
  rewrite yE; have := ulp_FLX_bound beta Hp2 x_neq_0.
  have ->: pow p = IZR beta * pow (p - 1).
    by rewrite -pow1E -bpow_plus; congr (pow _); lia.
  have {}uxLuf : IZR beta * ulp x <= ulp f by apply: ulp_lt_le.
  by have := bpow_gt_0 beta (p - 1); nra.
apply: Rle_trans (_ : Rabs f - F2R y <= _); last by lra.
rewrite eps1E.
have [_]// := round_N_pt beta fexp choice (Rabs f).
move/(_ _ Fy); rewrite -/y => H.
split_Rabs; lra.
Qed.

End KahanMult.
  

(* Copyright (c)  Inria. All rights reserved. *)
From Stdlib Require Import Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
Require Import Nmore Rmore Cmore Fmore Rstruct Cstruct.
Require Import digitn kahan_mult ifloat brent.

Delimit Scope R_scope with R.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FFT.

Variable p : Z.
Let beta := radix2.

Hypothesis Hp2: Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

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

Lemma error_le_quarter_ulp x eps (eps_2 : 0 <= eps < /2):
  Rabs x <= ulp x * (pow (p - 1) + eps) -> 
  Rabs (RN x) = ulp x * pow (p - 1) /\ Rabs (RN x - x) <= eps * ulp x.
Proof.
have [->|x_neq0 Lx] := Req_dec x 0.
  by rewrite !(ulp_FLX_0, round_0, Rsimp01); lra.
have [xL _]:= ulp_FLX_bound_le beta Hp2 x.
have F : Rabs (RN x) = ulp x * pow (p - 1).
  rewrite -RN_abs // -ulp_abs.
  apply: RN_nearest_lt_half_ulp => //.
  - by apply/mult_bpow_exact_FLX/generic_format_ulp.
  - by apply: Rmult_le_pos; [apply: ulp_ge_0|apply: bpow_ge_0].
  rewrite ulp_abs.
  split; first by lra.
  have -> : ulp (ulp x * pow (p - 1)) = ulp x.
    rewrite [ulp x]ulp_neq_0 // -bpow_plus ulp_bpow.
    by congr (pow _); rewrite /fexp; lia.
  have : 0 < ulp x by apply: ulp_gt_0.
  by nra.
split => //.
suff -> : Rabs (RN x - x) = Rabs (RN (Rabs x) - Rabs x).
  have: 0 <= Rabs x - RN (Rabs x) <= eps * ulp x.
    by rewrite -RN_abs // in F; lra.
  by split_Rabs; lra.
have HRP x1 : 0 <= x1 -> 0 <= RN x1.
  move=> x_pos.
  have -> : 0 = RN 0 by rewrite round_0.
  by apply: round_le.
have : x <= 0 -> RN x <= 0.
  rewrite -[RN x]Ropp_involutive -RN_sym //.
  by have := HRP (- x); lra.
by have := HRP x; rewrite RN_abs //; split_Rabs; lra.
Qed.

Definition ulp' x := 
  if Rlt_bool (ulp x * (pow (p - 1) + /4)) (Rabs x) then ulp x else ulp x / 2.

Lemma error_le_half_ulp' x : Rabs (RN x - x) <= /2 * ulp' x.
Proof.
rewrite /ulp'.
case: Rlt_bool_spec => H; first by apply: error_le_half_ulp.
by case: (@error_le_quarter_ulp x (/4)); lra.
Qed.

Definition RZ x := round beta fexp Ztrunc x.

Lemma ulp'_abs x : ulp' (Rabs x) = ulp' x.
Proof. by rewrite /ulp' Rabs_Rabsolu ulp_abs. Qed.

Lemma ulp'_le x y : Rabs x <= Rabs y -> ulp' x <= ulp' y.
Proof.
move=> xLy.
have uxLuy : ulp x <= ulp y by apply: ulp_le.
(rewrite /ulp'; do 2 case: Rlt_bool_spec) => H1 H2 //.
- have /(ulp_lt_le _ Hp2) : ulp x < ulp y.
    by have := bpow_gt_0 beta (p - 1); nra.
  by rewrite -[IZR beta]/2; lra.
- by have u_pos := ulp_ge_0 beta fexp x; lra.
by lra.
Qed.

Lemma relative_error_N_FLX'' x : Rabs ((RN x - x) / x) <= u / (1 + u).
Proof.
have u_gt_0 := u_gt_0.
have [->|x_neq0] := Req_dec x 0.
  rewrite round_0 !Rsimp01.
  by apply: Rdiv_le_0_compat; lra.
suff F : Rabs (RN x - x) <= u / (1 + u) * Rabs x.
  rewrite Rabs_mult Rabs_inv //.
  apply/Rle_div_l => //.
  by split_Rabs; lra.
have -> : u = u_ro beta p by congr (/ 2 * pow _); lia.
by apply: relative_error_N_FLX' => //; lia.
Qed.

Lemma lt_u_div_Su : u / (1 + u) < u.
Proof.
have u_gt_0 := u_gt_0.
rewrite [X in _ < X](_ : _ = u / 1); last by lra.
apply: Rmult_lt_compat_l => //.
apply: Rinv_lt; lra.
Qed.

Lemma relative_error_N_FLX''' x : Rabs ((RN x - x) / x) < u.
Proof.
by apply: Rle_lt_trans (relative_error_N_FLX'' x) lt_u_div_Su.
Qed.


(* Componentwise relative error *)
Definition cmpw_error (z : C) := 
  let (x, y) := z in
  Rmax (Rabs ((RN x - x) / x)) (Rabs ((RN y - y) / y)).

Lemma cmpw_error_ge_0 z : 0 <= cmpw_error z.
Proof.
case z => x y /=; rewrite /cmpw_error /Rmax.
by case: Rle_dec => _; apply: Rabs_pos.
Qed.

Lemma cmpw_error_N_FLX z : cmpw_error z <= u / (1 + u).
Proof.
case: z => x y.
by apply: Rmax_lub; apply: relative_error_N_FLX''.
Qed.

Lemma cmpw_error_0 : cmpw_error 0 = 0.
Proof.
by rewrite /cmpw_error /= round_0 /Rdiv Rinv_0 
           Rmult_0_r Rabs_R0 Rmax_right; lra.
Qed.

Lemma cmpw_error_N_FLX' (z : C) : cmpw_error z < u.
Proof.
have [->|] := Ceq_dec z 0; first by rewrite cmpw_error_0; apply: u_gt_0.
case: z => x y z_neq_0.
have [x_eq_0|x_neq_0] := Req_dec x 0.
  have y_neq_0 : y <> 0.
    by contradict z_neq_0; rewrite x_eq_0 z_neq_0.
  rewrite [cmpw_error _]Rmax_right.
    by apply: relative_error_N_FLX'''.
  rewrite x_eq_0 round_0 !Rsimp01.
  by apply: Rabs_pos.
have [y_eq_0|y_neq_0] := Req_dec y 0.
  rewrite [cmpw_error _]Rmax_left.
    by apply: relative_error_N_FLX'''.
  rewrite y_eq_0 round_0 !Rsimp01.
  by apply: Rabs_pos.
by apply: Rmax_lub_lt; apply: relative_error_N_FLX'''.
Qed.

(* Normwise relative error *)
Definition normw_error (z : C) := Cmod (((RNC z) - z) / z)%C.

Lemma normw_error_ge_0 (z : C) : 0 <= normw_error z.
Proof. by apply: Cmod_ge_0. Qed.

Lemma normw_error_0 : normw_error 0 = 0.
Proof. by rewrite /normw_error Cdiv_0_r Cmod_0. Qed.

Lemma normw_error_less_cmpw z : normw_error z <= cmpw_error z.
Proof.
have [->|] := Ceq_dec z 0; first by rewrite cmpw_error_0 normw_error_0; lra.
case: z => x y Dxy.
set e := cmpw_error _.
have Hx : (RN x - x) * (RN x - x) <= (e * x) * (e * x).
  suff : Rabs (RN x - x) <= e * Rabs x by split_Rabs; nra.
  have [->|x_neq0] := Req_dec x 0.
    by rewrite round_0 !Rsimp01; lra.
  suff-> : Rabs (RN x - x) = Rabs ((RN x - x) / x) * Rabs x.
    suff :  Rabs ((RN x - x) / x) <= e.
      by have := Rabs_pos ((RN x - x) / x); have := Rabs_pos x; nra.
    by rewrite /e /cmpw_error /Rmax; case: Rle_dec; lra.
  rewrite Rabs_mult Rmult_assoc -Rabs_mult [_ * x]Rmult_comm Rinv_r; try lra.
  by rewrite Rabs_R1; lra.
have Hy : (RN y - y) * (RN y - y) <= (e * y) * (e * y).
  suff : Rabs (RN y - y) <= e * Rabs y by split_Rabs; nra.
  have [->|y_neq0] := Req_dec y 0.
    by rewrite round_0 !Rsimp01; lra.
  suff-> : Rabs (RN y - y) = Rabs ((RN y - y) / y) * Rabs y.
    suff :  Rabs ((RN y - y) / y) <= e.
      by have := Rabs_pos ((RN y - y) / y); have := Rabs_pos y; nra.
    by rewrite /e /cmpw_error /Rmax; case: Rle_dec; lra.
  rewrite Rabs_mult Rmult_assoc -Rabs_mult [_ * y]Rmult_comm Rinv_r; try lra.
  by rewrite Rabs_R1; lra.
have Hd : (RN x - x) * (RN x - x) + (RN y - y) * (RN y - y) <= 
       (e  * e) * (x * x + y * y) by nra.
rewrite /normw_error Cmod_mult CmodJ.
apply/Rle_div_l.
  suff : 0 < Cmod (x, y) by lra.
  by apply/Cmod_gt_0.
apply: leq_sqrt.
  apply: Rmult_le_pos; first by apply: cmpw_error_ge_0.
  by apply: Cmod_ge_0.
have->: e * Cmod (x, y) * (e * Cmod (x, y)) = 
        e * e * (Cmod (x, y) * Cmod (x, y)) by lra.
by rewrite !Cmod_sqr.
Qed.

Lemma normw_error_N_FLX z : normw_error z <= u / (1 + u).
Proof.
by apply: Rle_trans (normw_error_less_cmpw _) (cmpw_error_N_FLX _).
Qed.

Lemma normw_error_N_FLX' (z : C) : normw_error z < u.
Proof.
by apply: Rle_lt_trans (normw_error_less_cmpw _) (cmpw_error_N_FLX' _).
Qed.

Lemma normw_error_le (z : C) :  Cmod (RNC z - z) <= u * Cmod z.
Proof.
have [->|z_neq_0] := Ceq_dec z 0; first by  rewrite RNC_0 !Csimp01; lra.
apply/Rle_div_l; first by apply/Rlt_gt/Cmod_gt_0.
rewrite -Cmod_div //.
by apply/Rlt_le/normw_error_N_FLX'.
Qed.

Section RootOfUnit.

Lemma u_pow : u = pow (- p).
Proof. by rewrite /u -[/2]/(pow (-1)) -bpow_plus; congr bpow; lia. Qed.

Lemma abs_le_1_ulp x : Rabs x < 1 -> ulp x <= u.
Proof.
move=> HR.
have [->|x_neq0] := Req_dec x 0.
  by rewrite ulp_FLX_0; apply Rlt_le; apply: u_gt_0.
rewrite ulp_neq_0 // u_pow.
apply: bpow_le.
have Hm := mag_le_bpow beta x 0 x_neq0 HR.
rewrite /cexp /fexp; lia.
Qed.

Lemma abs_le_1_error x : Rabs x <= 1 -> Rabs ((RN x - x)) <= / 2 * u.
Proof.
have u_gt_0 := u_gt_0.
move=> x_le_1.
have [->|x_neq_0] := Req_dec x 0.
  by rewrite round_0 Rminus_eq_0 Rabs_R0; lra.
have [|x_neq_1] := Req_dec (Rabs x) 1.
  rewrite {1}/Rabs; case: Rcase_abs => [_ x_n1|_ ->].
    rewrite (_ : x = -1); try lra.
    rewrite RN_sym // RN_1 // (_ : (- (1) - -1) = 0); last by lra.
    by rewrite Rabs_R0; lra.
  by rewrite RN_1 // Rminus_eq_0 Rabs_R0; lra.
apply: Rle_trans (_ : /2 * ulp x <= _).
  apply: error_le_half_ulp.
suff : ulp x <= u by lra.
apply: abs_le_1_ulp; lra.
Qed.

Lemma cmperror_norm1 z : Cmod z = 1 -> normw_error z <= /(sqrt 2) * u.
Proof.
have u_gt_0 := u_gt_0.
case z => x y /= Hc.
rewrite /normw_error Cmod_mult CmodJ Hc Rinv_1 Rmult_1_r.
apply: leq_sqrt.
  apply: Rmult_le_pos; try lra.
  apply: Rinv_0_le_compat.
  by apply: sqrt_pos.
rewrite Cmod_sqr /=.
have-> : / sqrt 2 * u * (/ sqrt 2 * u) = (u / 2) * (u / 2) + (u / 2) * (u / 2).
  have : u / 2  * 2 = u by lra.
  have : (/ sqrt 2)  *  (/ sqrt 2) * u  = u / 2.
    rewrite -Rinv_mult [sqrt _ * _]Rsqr_sqrt; lra.
    by nra.
rewrite 2![_ * _]Rsqr_abs /Rsqr -![_ + - _]/(_ - _).
have :  0 <= Rabs ((RN x - x)) <= / 2 * u.
  split; first by apply: Rabs_pos.
  by apply/abs_le_1_error; apply: (Cmod_abs_l (x, y)); rewrite Hc; lra.
have :  0 <= Rabs ((RN y - y)) <= / 2 * u.
  split; first by apply: Rabs_pos.
  by apply/abs_le_1_error; apply: (Cmod_abs_r (x, y)); rewrite Hc; lra.
nra.
Qed.

End RootOfUnit.

Section Imult.

Variable fma : bool.

Definition fft_imult (z1 z2 : C) :=
  if fma then A1_imult p beta choice z1 z2 else
  brent_imult p beta choice z1 z2.

Lemma fft_imult_0_r c : fft_imult c 0 = 0.
Proof.
rewrite /fft_imult; case: fma; [apply: A1_imult_0_r | apply: brent_imult_0_r].
Qed.

Lemma fft_imult_0_l c : fft_imult 0 c = 0.
Proof.
rewrite /fft_imult; case: fma; [apply: A1_imult_0_l | apply: brent_imult_0_l].
Qed.

Lemma fft_imult_1_r c : fft_imult c 1 = RNC c.
Proof.
by rewrite /fft_imult; case: fma;
    [apply: A1_imult_1_r | apply: brent_imult_1_r].
Qed.

Lemma fft_imult_1_l c : fft_imult 1 c = RNC c.
Proof.
by rewrite /fft_imult; case: fma;
     [apply: A1_imult_1_l | apply: brent_imult_1_l].
Qed.

Lemma fft_imult_N1_r c : fft_imult c (-1) = (- (RNC c))%C.
Proof.
by rewrite /fft_imult; case: fma;
     [apply: A1_imult_N1_r | apply: brent_imult_N1_r].
Qed.

Lemma fft_imult_N1_l c : fft_imult (-1) c = (- (RNC c))%C.
Proof.
by rewrite /fft_imult; case: fma;
     [apply: A1_imult_N1_l | apply: brent_imult_N1_l].
Qed.

Lemma fft_imult_i_r c : fft_imult c Ci = (RNC c * Ci)%C.
Proof.
by rewrite /fft_imult; case: fma;
     [apply: A1_imult_i_r | apply: brent_imult_i_r].
Qed.

Lemma fft_imult_i_l c : fft_imult Ci c = (Ci * RNC c)%C.
Proof.
by rewrite /fft_imult; case: fma;
     [apply: A1_imult_i_l | apply: brent_imult_i_l].
Qed.

Lemma fft_imult_Ni_r c : fft_imult c (- Ci) = ((RNC c) * - Ci)%C.
Proof.
by rewrite /fft_imult; case: fma;
     [apply: A1_imult_Ni_r | apply: brent_imult_Ni_r].
Qed.

Lemma fft_imult_Ni_l c : fft_imult (- Ci) c = (- Ci * (RNC c))%C.
Proof.
by rewrite /fft_imult; case: fma;
     [apply: A1_imult_Ni_l | apply: brent_imult_Ni_l].
Qed.

Lemma fft_imult_pow41_l c1 c2 : (c1 ^ 4 = 1 -> fft_imult c1 c2 = c1 * RNC c2)%C.
Proof.
case/Cpow4_eq1_inv => ->; first by rewrite fft_imult_1_l Csimp01.
- by rewrite fft_imult_N1_l; ring.
- by rewrite fft_imult_i_l; ring.
rewrite fft_imult_Ni_l; ring.
Qed.

Lemma fft_imult_pow41_r c1 c2 : (c2 ^ 4 = 1 -> fft_imult c1 c2 = RNC c1 * c2)%C.
Proof.
case/Cpow4_eq1_inv => ->; first by rewrite fft_imult_1_r Csimp01.
- by rewrite fft_imult_N1_r; ring.
- by rewrite fft_imult_i_r; ring.
rewrite fft_imult_Ni_r; ring.
Qed.

Notation delta := normw_error.

Definition rho fma := if fma then 2 * u else sqrt 5 * u.

Lemma rho_gt_0 : 0 < rho fma.
Proof.
rewrite /rho; case: fma; first by have := u_gt_0; lra.
have := u_gt_0; have : 0 < sqrt 5 by apply: sqrt_lt_R0; lra.
nra.
Qed.

End Imult.

Lemma error_fft_imult fma c1 c2 : 
  2 ^ 5 * u <= 1 -> iformat c1 -> iformat c2 ->
  Cmod (fft_imult fma c1 c2 - c1 * c2) <= rho fma * Cmod (c1 * c2).
Proof.
move=> Hu Fc1 Fc2.
case: fma => /=; first by apply: error_fma_A1_mult.
by apply: error_brent_imult.
Qed.

Section Def.

(* See reverse_poly in mfft *)
Definition reverse_exact n (l : seq C) : seq C :=
  [seq (get l (rdigitn 2 n i)) | i : 'I_(2 ^ n)].

(* See istep1 in mfft *)
(* w should such that  w ^ (2 ^ n) = -1 *)
Definition step_exact m n (w : C) (l : seq C) : seq C :=
  [seq 
   (if ((i %% 2 ^ n.+1) < 2 ^ n)%N then
       get l i + w ^ (i %% 2 ^ n) * get l (i + 2 ^ n)
    else 
       get l (i - 2 ^ n) - (w ^ (i %% 2 ^ n))%C * get l i)%C
    | i : 'I_(2 ^ (m + n).+1)].

Lemma size_step_exact (m n : nat) w l : 
  (size (step_exact m n w l) = 2 ^ (m + n).+1)%N.
Proof. by rewrite size_map size_enum_ord. Qed.

Lemma get_step_exact (m n : nat) w l i : 
  (i < 2 ^ (m + n).+1)%N -> 
  get (step_exact m n w l) i = 
   (if ((i %% 2 ^ n.+1) < 2 ^ n)%N then
       get l i + w ^ (i %% 2 ^ n) * get l (i + 2 ^ n)
    else 
       get l (i - 2 ^ n) - (w ^ (i %% 2 ^ n))%C * get l i)%C.
Proof.
move=> iL2mn.
have O0 : (0 < 2 ^  (m + n).+1)%N by rewrite expn_gt0.
by rewrite [LHS](nth_map (Ordinal O0)) ?nth_enum_ord // size_enum_ord.
Qed.

Fixpoint fft_aux_exact m n (w : C) (p : seq C) : seq C :=
  if m is m1.+1 then fft_aux_exact m1 n.+1 w (step_exact m1 n (w ^ (2 ^ m1)) p) 
  else p.

Definition fft_exact n (w : C) (p : seq C) : seq C :=
  fft_aux_exact n 0 w (reverse_exact n p).

Definition reverse_float n (l : seq C) : seq C :=
  [seq get l (rdigitn 2 n i) | i : 'I_(2 ^ n)].

Definition step_float fma m n (w : C) (l : seq C) :=
  [seq 
    if (i %% 2 ^ n.+1 < 2 ^ n)%N then
      (RNC (get l i + 
           fft_imult fma (RNC (w ^ (i %% 2 ^ n))) (get l (i + 2 ^ n))))
    else 
      (RNC (get l (i - 2 ^ n) - 
           fft_imult fma (RNC (w ^ (i %% 2 ^ n))) (get l i)))%RR
    | i : 'I_(2 ^ (m + n).+1)].

Lemma size_step_float fma (m n : nat) w l : 
  (size (step_float fma m n w l) = 2 ^ (m + n).+1)%N.
Proof. by rewrite size_map size_enum_ord. Qed.

Lemma get_step_float fma (m n : nat) w l i : 
  (i < 2 ^ (m + n).+1)%N -> 
  get (step_float fma m n w l) i = 
    if (i %% 2 ^ n.+1 < 2 ^ n)%N then
      (RNC (get l i + 
           fft_imult fma (RNC (w ^ (i %% 2 ^ n))) (get l (i + 2 ^ n))))
    else 
      (RNC (get l (i - 2 ^ n) - 
           fft_imult fma (RNC (w ^ (i %% 2 ^ n))) (get l i)))%RR.
Proof.
move=> iL2mn; have O0 : (0 < 2 ^  (m + n).+1)%N by rewrite expn_gt0.
by rewrite [LHS](nth_map (Ordinal O0)) ?nth_enum_ord // size_enum_ord.
Qed.

Fixpoint fft_aux_float fma m n (w : C) (p : seq C) :=
  if m is m1.+1 then 
    fft_aux_float fma m1 n.+1 w (step_float fma m1 n (w ^ (2 ^ m1)) p) 
  else p.

Definition fft_float fma n w p := fft_aux_float fma n 0 w (reverse_float n p).

Lemma cnorm2_scalen (n : nat) k (l : seq C) : 
  (k <= n)%N ->
  cnorm2 n.+1 l = (\sum_(i < 2 ^ n) 
                      ((Cmod (get l (scalen k i))) ^ 2 + 
                       (Cmod (get l (scalen k i + 2 ^ k))) ^ 2)%R)%RR.
Proof.
move=> kLn.
rewrite /cnorm2.
have -> //= :=  partition_big_idem (@GRing.addr0 _ 0%RR) (index_enum _) _
         (_ : forall i : _, xpredT i -> xpredT (shrink_ord i kLn)).
apply: eq_bigr => /= i _.
rewrite (bigD1 (scalen_ord i kLn)) => //=; last first.
  by apply/eqP/val_eqP; rewrite /= shrink_scalen.
rewrite (bigD1 (scalen_k_ord i kLn)) => //=; last first.
  apply/andP; split; apply/eqP/val_eqP=> /=.
    by rewrite shrink_scalen_k.
  by rewrite -[X in _ != X]addn0 eqn_add2l expn_eq0.
rewrite big1 ?GRing.addr0 // =>
  [] [i1 Hi1] /andP[/andP[/eqP/val_eqP/= /eqP Hs /eqP/val_eqP /= Hi2]
  /eqP/val_eqP /= Hi3].
case: (_ %% 2)%N (ltn_mod (i1 %/ 2 ^ k) 2) (scalen_shrink k i1) => 
    [_ H|[_ H|] //]; rewrite (addn0, mul1n) in H.
  by case/eqP: Hi2; rewrite -Hs.
by case/eqP: Hi3; rewrite -Hs.
Qed.

End Def.

Lemma cnorm2_step_exact  m n (w : C) (l : seq C) 
  (x := scalen n) (y := (fun i => scalen n i + 2 ^ n)%N) :
cnorm2 (m + n).+1 (step_exact m n w l) =
  (\sum_(i < 2 ^ (m + n))
    (Cmod ((get l (x i)) + (w ^ (x i %% 2 ^ n))%C * l`_(y i)) ^ 2 +  
     Cmod ((get l (x i)) - (w ^ (x i %% 2 ^ n))%C * l`_(y i)) ^ 2)%R)%RR.
Proof.
rewrite (cnorm2_scalen _ (_ : n <= _)%N) /y /x; last by rewrite leq_addl.
apply: eq_bigr => /= i _.
rewrite !get_step_exact ?scalen_lt_k ?scalen_lt ?leq_addl //.
rewrite addnK modnMDl modn_small; last first.
  apply: leq_trans (_ : 2 ^ n <= _)%N; first by rewrite ltn_mod expn_gt0.
  by rewrite leq_exp2l.
rewrite ltn_mod expn_gt0 //= ifF ?modnDr //.
rewrite -addnA modnMDl modn_small; first by rewrite ltnNge leq_addl.
by rewrite expnS mul2n -addnn ltn_add2r ltn_mod expn_gt0 .
Qed.

Notation delta := normw_error.

Lemma delta_ge_0 z : 0 <= delta z.
Proof. by apply: normw_error_ge_0. Qed.

Lemma error_multw fma z w (w' := RNC w) (w'z := fft_imult fma w' z) : 
  2 ^ 5 * u <= 1 -> iformat z -> Cmod w = 1 ->
  Cmod ((w'z - w * z) / (w * z)) <= delta w + rho fma * (1 + delta w).
Proof.
move=> uE Fx wC1.
have w_neq_0 : w <> 0.
 move=> w_eq0; rewrite w_eq0 Cmod_0 in wC1.
 by case: C1_nz; rewrite wC1.
have [->|z_neq_0] := Ceq_dec z 0.
  rewrite !Csimp01.
  have := delta_ge_0 w; have := rho_gt_0 fma; nra.
have wz_neq_0 : (w * z <> 0)%C by apply: Cmult_neq_0.
rewrite Cmod_div // Rle_div_l; last by apply/Rlt_gt/Cmod_gt_0.
rewrite Cmod_mult wC1 Rsimp01.
pose w''z := (w' * z)%C.
apply: Rle_trans (_ : Cmod(w'z - w''z) + Cmod (w''z - w * z) <= _).
  have-> : (w'z - w * z = (w'z - w''z) + (w''z - w * z))%C by ring.
  by apply: Cmod_triangle.
have F1 : Cmod (w''z - w * z) <= delta w * Cmod z.
  rewrite (_ : _ - _ = (w' - w) * z)%C; last by rewrite /w''z; ring.
  by rewrite Cmod_mult [delta w]Cmod_div // wC1 Rsimp01 -/w'; lra.
suff : Cmod (w'z - w''z) <= (rho fma * (1 + delta w)) * Cmod z by lra.
apply: Rle_trans (_ : rho fma * Cmod (w' * z) <= _).
  apply: error_fft_imult => //; first by apply: generic_formatC_roundC.
have Cw'_ge_0 := Cmod_ge_0 w'; have Czw'_ge_0 := Cmod_ge_0 (w * z).
have rho_ge_0 := rho_gt_0 fma; have delta_ge_0 := delta_ge_0 w.
have Cz_ge_0 := Cmod_ge_0 z.
suff : Cmod (w' * z) <= (1 + delta w) * Cmod z by nra.
rewrite Cmod_mult.
suff : Cmod w' <= (1 + delta w) by nra.
rewrite /delta  -/w' Cmod_div // wC1 Rsimp01.
rewrite -wC1.
rewrite [in Cmod w'](_ : w' = w + (w' - w))%C; last by ring.
apply: Cmod_triangle.
Qed.

Lemma RN1 : RN 1 = 1.
Proof. by rewrite -(pow0E beta) round_generic //; apply: format_pow. Qed.

Lemma RNC1 : RNC 1 = 1.
Proof. by rewrite /RNC /= round_0 RN1. Qed.

Lemma delta1 : delta 1 = 0.
Proof. by rewrite /delta RNC1 !Csimp01. Qed.

Section Rootn.

Variable n : nat.
Variable w : C.
Variable fma : bool.
Hypotheses wX : (w ^ (2 ^ n) = 1)%C.
Hypotheses wXmin : forall k, (k < 2 ^ n)%nat -> (w ^ k = 1)%C -> (k = 0)%N.

Lemma wXM1 : (0 < n)%N -> ((w ^ (2 ^ n.-1) = -1)%C).
Proof.
move=> n_pos; case: (Cpow2_eq1_inv (w ^ 2 ^ n.-1)) => // [|Hc].
  rewrite -Cpow_mult_r -wX; congr (_ ^ _)%C.
  by rewrite -[in RHS](prednK n_pos) expnS mulnC.
have [] : (2^ n.-1 <> 0)%N by apply/eqP; rewrite expn_eq0.
by apply: wXmin; first by rewrite ltn_exp2l ?ltn_predL.
Qed.

Lemma wXM2 :
  (1 < n)%N -> ((w ^ (2 ^ n.-2) = - Ci)%C \/ (w ^ (2 ^ n.-2) = Ci)%C).
Proof.
set u := (w ^ _)%C.
move=> n_pos1; have n_pos : (0 < n)%nat by apply: leq_ltn_trans n_pos1. 
have /Cpow4_eq1_inv [F1|F1|F1|F1] : (u ^ 4 = 1)%C.
- rewrite -Cpow_mult_r -[(_ * _)%coq_nat]/(muln _ _).
  by rewrite -(expnD 2 _ 2) !addnS addn0 !prednK // -ltnS prednK.
- have [] : (2 ^ n.-2 <> 0)%N by apply/eqP; rewrite expn_eq0.
  apply: wXmin => //.
  by rewrite ltn_exp2l ?ltn_predL // prednK // -ltnS prednK.
- have [] : (2 ^ n.-1 <> 0)%N by apply/eqP; rewrite expn_eq0.
  apply: wXmin; first by rewrite ltn_exp2l ?ltn_predL.
  rewrite -[n.-1]prednK; last by rewrite -ltnS prednK.
  by rewrite expnS mulnC Cpow_mult_r -/u F1; ring.
- by right.
by left.
Qed.

Lemma w_norm1 : Cmod w = 1.
Proof.
apply: (pow_inv _ _ (2 ^ n)) => //; try lra.
- by apply: Cmod_ge_0.
- by rewrite expn_gt0.
by rewrite -Cmod_pow wX Csimp01 pow1.
Qed.

Variable k : nat.
Hypothesis kLn : (k <= n)%nat.

Let wk := (w ^ (2 ^ (n - k)))%C.

Let Cmod_wk : Cmod wk = 1.
Proof. by rewrite Cmod_pow w_norm1 pow1. Qed.

Fixpoint delta_max_rec m := 
  if m is m1.+1 then Rmax (delta (wk ^ m)) (delta_max_rec m1) else 0.

Lemma delta_max_rec_bound m : 0 <= delta_max_rec m <= sqrt 2 /2 * u.
Proof.
elim: m => /= [|m IH]; first by have := u_gt_0; have := Rlt_sqrt2_0; nra.
have := normw_error_ge_0 (wk * wk ^ m).
have : delta (wk * wk ^ m) <= sqrt 2 / 2 * u.
  have -> : sqrt 2 / 2 = / sqrt 2.
    have H : sqrt 2 * sqrt 2 = 2 by apply: sqrt_def; lra.
    by field[H]; apply: sqrt2_neq_0.
  apply: cmperror_norm1.
  by rewrite (Cmod_pow wk m.+1) Cmod_wk pow1.
by rewrite /Rmax; case: Rle_dec; lra.
Qed.

Definition delta_max := delta_max_rec ((2 ^ k) - 1).

Lemma delta_max_bound : 0 <= delta_max <= sqrt 2 /2 * u.
Proof. by apply: delta_max_rec_bound. Qed.

Lemma delta_max_correct m : (m < 2 ^ k)%nat -> delta (wk ^ m) <= delta_max.
Proof.
move=> H.
rewrite /delta_max.
have : (m <= 2 ^ k - 1)%N by rewrite subn1; case: (2 ^ k)%N H => /=.
elim: (2 ^ k - 1)%N => {H}/= [|v IH].
  by case: m => //=; rewrite delta1; lra.
case: ltngtP => // [/IH H _|-> _].
  by apply: Rle_trans H (Rmax_r _ _).
by apply: Rmax_l.
Qed.

Definition gk :=
  if (k <= 2)%N then 0 else delta_max + rho fma * (1 + delta_max).

Lemma gk_ge_0 : 0 <= gk.
Proof.
rewrite /gk.
case: k => [|[|[|k1]]] /=; try by lra.
by have := delta_max_bound; have := rho_gt_0 fma; nra.
Qed.

Lemma error_multw_gk z i (w' := RNC (wk ^ i)) (zw' := fft_imult fma w' z) : 
  2 ^ 5 * u <= 1 -> iformat z -> (i < 2 ^ k)%N ->
  Cmod ((zw' - wk ^ i * z)) <= Cmod z * gk.
Proof.
move=> Hu Hi Hib; have := delta_max_correct Hib; rewrite /zw' /w' /gk /wk.
case: k kLn => [|[|[|k1]]] k1Ln1 Hd /=.
- rewrite subn0 wX Cpow_1_l RNC1 fft_imult_1_l roundC_generic // Csimp01.
  by rewrite Cminus_x_x !Csimp01 Rsimp01; lra.
- have C4 : (((w ^ 2 ^ (n - 1)) ^ i) ^ 4 = 1)%C.
    rewrite -!Cpow_mult_r -![(_ * _)%coq_nat]/(muln _ _).
    have ->:  (2 ^ (n - 1) * (i * 4) = 2 ^ n * (i * 2))%N.
      rewrite -[in RHS](prednK k1Ln1) expnS [in RHS]mulnC !mulnA.
      by rewrite -[(_ * 2 * 2)%N]mulnA [in RHS]mulnC subn1 mulnA.
    by rewrite Cpow_mult_r wX Cpow_1_l.
  rewrite RNC_pow4 // fft_imult_pow41_l // roundC_generic //.
  by rewrite Cminus_x_x !Csimp01 Rsimp01; lra.
- have C4 : (((w ^ 2 ^ (n - 2)) ^ i) ^ 4 = 1)%C.
    rewrite -!Cpow_mult_r -![(_ * _)%coq_nat]/(muln _ _).
    have ->:  (2 ^ (n - 2) * (i * 4) = 2 ^ n * i)%N.
      by rewrite -[in RHS](subnK k1Ln1) expnD -mulnA [(_ * i)%N]mulnC.
    by rewrite Cpow_mult_r wX Cpow_1_l.
  rewrite RNC_pow4 // fft_imult_pow41_l // roundC_generic //.
  by rewrite Cminus_x_x !Csimp01 Rsimp01; lra.
set x := (_ ^ i)%C in Hd *.
have Cmod_x : Cmod x = 1 by rewrite !Cmod_pow w_norm1 !pow1.
have x_neq0 : (x <> 0)%C.
  move=> x_eq0; rewrite x_eq0 Csimp01 in Cmod_x.
  by lra.
have [->|z_neq0] := Ceq_dec z 0.
  rewrite !Csimp01 !Rsimp01 fft_imult_0_r Csimp01; lra.
rewrite Rmult_comm.
apply/Rle_div_l; first by apply/Cmod_gt_0.
apply: Rle_trans (_ : delta x + rho fma * (1 + delta x) <= _); last first.
  by have := rho_gt_0 fma; nra.
have : Cmod ((fft_imult fma (RNC x) z - x * z) / (x * z)) <= 
           delta x + rho fma * (1 + delta x) by apply: error_multw.
rewrite Cmod_div; last by apply: Cmult_neq_0.
by rewrite Cmod_mult !Cmod_pow w_norm1 !pow1 Rsimp01.
Qed.

(* 13 *)
Fact gk_le : gk <= sqrt 2 / 2 * u + rho fma * (1 + sqrt 2 / 2 * u).
Proof.
have HF : 0 <= sqrt 2 / 2 * u + rho fma * (1 + sqrt 2 / 2 * u).
  have := u_gt_0; have := rho_gt_0 fma.
  have : 0 <= sqrt 2 by apply: sqrt_positivity; lra.
  move=> *.
  have: 0 <= (1 + sqrt 2 / 2 * u) by nra.
  by nra.
rewrite /gk; case: (k) => //= [] [|[|]] //= k1.
by have := delta_max_bound; have := rho_gt_0 fma; nra.
Qed.

Definition fft_stepp z0 z1 i := RNC (z0 + fft_imult fma (RNC (wk ^ i)) z1).
Definition fft_stepm z0 z1 i := RNC (z0 - fft_imult fma (RNC (wk ^ i)) z1).

(* This is Lemma 1 *)
Lemma Cmod_tv t v : 
 (Cmod (t + v) + Cmod (t - v)) * Rmax (Cmod t) (Cmod v) <= 
 (Cmod (t + v) ^2 + Cmod (t - v) ^2).
Proof.
set a := (t + v)%C; set b := (t - v)%C.
have Ca_ge_0 := Cmod_ge_0 a.
have Cb_ge_0 := Cmod_ge_0 b.
have-> : (t = /2 * (a + b))%C by rewrite /a /b; field.
have-> : (v = /2 * (a - b))%C by rewrite /a /b; field.
apply: Rle_trans (_ : (Cmod a + Cmod b) * /2 * (Cmod a + Cmod b) <= _).
  suff: Rmax (Cmod (/ 2 * (a + b))) (Cmod (/ 2 * (a - b))) <= 
         /2 * (Cmod a + Cmod b) by nra.
  rewrite !Cmod_mult Cmod_inv; last by move=> /RtoC_inj; lra.
  rewrite Cmod_R Rabs_right; last by lra.
  rewrite RmaxRmult; last by lra.
  suff : Rmax (Cmod (a + b)) (Cmod (a - b)) <= (Cmod a + Cmod b) by lra.
  rewrite /Rmax; case: Rle_dec => _; last by apply: Cmod_triangle.
  by rewrite -(Cmod_opp b); apply: Cmod_triangle.
suff : 0 <= /2 * (Cmod a - Cmod b) ^ 2 by nra.
by set k1 := _ - _; nra.
Qed.

(* This is 16 *)
Lemma norm2_plus_minus i (z1 z2 ww : C) : 
  Cmod ww = 1 ->
  Cmod (z1 - ww ^ i * z2) ^ 2 + Cmod (z1 + ww ^ i * z2) ^ 2 = 
    2 * (Cmod z1 ^ 2 + Cmod z2 ^ 2).
Proof. 
move=> Hc.
apply: RtoC_inj.
rewrite RtoC_plus !Cmod2_conj Cminus_conj Cplus_conj.
apply: trans_equal (_ : 2 * (z1 * Cconj z1 + 
                             (ww ^ i * z2) * Cconj (ww ^ i * z2)) = _)%C.
  by ring.
rewrite -!Cmod2_conj Cmod_mult Cmod_pow Hc pow1 Rsimp01.
by rewrite -RtoC_plus -RtoC_mult.
Qed.

(* Lemma 2 *)
Lemma error_stepp_stepm z0 z1 i (omegak := u + gk * (1 + u)) :
  2 ^ 5 * u <= 1 -> iformat z1 -> (i < 2 ^ k)%N ->
  (Cmod (fft_stepp z0 z1 i - (z0 + (wk ^ i) * z1))) ^ 2 +
  (Cmod (fft_stepm z0 z1 i - (z0 - (wk ^ i) * z1))) ^ 2  <= 
  ((Cmod  (z0 + (wk ^ i) * z1)) ^ 2 + (Cmod  (z0 - (wk ^ i) * z1)) ^ 2 ) * 
  omegak ^ 2.
Proof.
move=> Hu Hi Hik; rewrite /fft_stepm /fft_stepp.
set wz1' := fft_imult _ _ _; set wz1 := (_ * z1)%C.
have F1 : Cmod (wz1' - wz1) <= Cmod z1 * gk by apply: error_multw_gk.
(* This is 14 *)
have F2 : Cmod (RNC(z0 + wz1') - (z0 + wz1)) <= 
          Cmod (z0 + wz1) * u + Cmod z1 * (gk + u * gk).
  have-> : (RNC (z0 + wz1') - (z0 + wz1) = 
           (RNC(z0 + wz1') - (z0 + wz1')) + (wz1' - wz1))%C by ring.
  apply: Rle_trans (Cmod_triangle _ _) _.
  apply: Rle_trans (_ : u * Cmod (z0 + wz1') + Cmod z1 * gk <= _).
    apply: Rplus_le_compat => //.
    by apply: normw_error_le.
  suff : Cmod (z0 + wz1') <= Cmod (z0 + wz1) + Cmod z1 * gk.
    by have := u_gt_0; nra.
  have-> : (z0 + wz1' = (z0 + wz1) + (wz1' - wz1))%C by ring.
  by apply: Rle_trans (Cmod_triangle _ _) _; lra.
(* This is 15 *)
have F3 : Cmod (RNC(z0 - wz1') - (z0 - wz1)) <= 
          Cmod (z0 - wz1) * u + Cmod z1 * (gk + u * gk).
  have-> : (RNC (z0 - wz1') - (z0 - wz1) = 
           (RNC(z0 - wz1') - (z0 - wz1')) + (wz1 - wz1'))%C by ring.
  apply: Rle_trans (Cmod_triangle _ _) _.
  have -> : Cmod (wz1 - wz1') = Cmod (wz1' - wz1).
    by rewrite -Cmod_opp; congr Cmod; ring.
  apply: Rle_trans (_ : u * Cmod (z0 - wz1') + Cmod z1 * gk <= _).
    apply: Rplus_le_compat => //.
    by apply: normw_error_le.
  suff : Cmod (z0 - wz1') <= Cmod (z0 - wz1) + Cmod z1 * gk.
    by have := u_gt_0; nra.
  have-> : (z0 - wz1' = (z0 - wz1) + (wz1 - wz1'))%C by ring.
  apply: Rle_trans (Cmod_triangle _ _) _.
  have -> : Cmod (wz1 - wz1') = Cmod (wz1' - wz1).
    by rewrite -Cmod_opp; congr Cmod; ring.
  by nra.
(* This is 16 *)
have F4 : Cmod (z0 - wz1) ^ 2 + Cmod (z0 + wz1) ^2 = 
             2 * ((Cmod z0)^2 + (Cmod z1) ^2).
  by apply: norm2_plus_minus.
(* This is 17 *)
have F5 : (Cmod z0) ^ 2  <= /2  * (Cmod (z0 - wz1) ^ 2 + Cmod (z0 + wz1) ^2).
  by nra.
have F6 : (Cmod z1) ^ 2  <= /2 * (Cmod (z0 - wz1) ^ 2 + Cmod (z0 + wz1) ^2).
  by nra.
set x1 := (z0 + wz1)%C in F2 F4 F5 F6 *.
set x2 := (z0 - wz1)%C in F3 F4 F5 F6 *.
set v := (Cmod x1 ^ 2 + Cmod x2 ^ 2).
apply: Rle_trans (_ : v * u ^ 2 + v * (gk + u * gk ) ^ 2 
                    + 2 * u * Cmod z1 * (gk + u * gk) 
                            * (Cmod x1 + Cmod x2) <= _).
  have: 0 <= Cmod (RNC (z0 - wz1') - x2) by apply: Cmod_ge_0.
  have: 0 <= Cmod (RNC (z0 + wz1') - x1) by apply: Cmod_ge_0.
  have : 0 <= (gk + u * gk) ^ 2 by set y := _ + _; nra.
  by rewrite -/x1 -/x2 /v; nra.
have F7 : Cmod z1 * (Cmod x1 + Cmod x2) <= v.
  have := Cmod_tv z0 (wk ^ i * z1)%C.
  rewrite Cmod_mult Cmod_pow Cmod_wk pow1 Rsimp01.
  have := Rmax_r (Cmod z0) (Cmod z1).
  rewrite -/x1 -/x2 -/v.
  by have := Cmod_ge_0 x1; have := Cmod_ge_0 x2; nra.
rewrite /omegak.
suff : 0 <=  u * (gk + u * gk) by nra.
by have u_gt0 := u_gt_0; have := gk_ge_0; nra.
Qed.

End Rootn.

Lemma cnorm_step_exact_mult_2  m n (w : C) (l : seq C) :
Cmod w = 1 ->
cnorm (m + n).+1 (step_exact m n w l) = sqrt 2 * cnorm (m + n).+1 l.
Proof.
move=> Hc; rewrite /cnorm -sqrt_mult_alt; last by lra.
congr sqrt.
rewrite cnorm2_step_exact (cnorm2_scalen _ (_ : (n <= (m + n))%N)); last first.
  by rewrite leq_addl.
rewrite -/x [RHS](@GRing.mulr_sumr (GRing.PzRing.clone _ R)).
elim/big_ind2: _ => /= [|x1 x2 y1 y2 H1 H2|i _].
- by rewrite /GRing.zero /=; lra.
- by rewrite /GRing.add /=; lra.
by rewrite /GRing.add /= Rplus_comm norm2_plus_minus.
Qed.

(* This is 18 *)
Lemma cnorm_step_floatDexact fma m n (w : C) (l : seq C) :
(w ^ 2 ^ (m + n))%C = 1 ->
 let omega := u + gk (m + n) w fma n * (1 + u) in
 2 ^ 5 * u <= 1 ->
 (forall i, (i < 2  ^ (m + n).+1)%N -> iformat (get l i)) ->
cnorm (m + n).+1 
 (csub (m + n).+1 (step_float fma m n (w ^ (2 ^ m)) l) 
                  (step_exact m n (w ^ (2 ^ m)) l)) <= 
  omega * (cnorm (m + n).+1 (step_exact m n (w ^ (2 ^ m)) l)).
Proof.
move=> Cw omegak Hu Hl; rewrite Rmult_comm.
have om_ge_0 : 0 <= omegak.
  have u_ge_0 : 0 <= u by apply/Rlt_le/u_gt_0.
  suff : 0 <= gk (m + n) w fma n by rewrite /omegak; nra.
  by apply: gk_ge_0.
rewrite -(sqrt_pow2 _ om_ge_0) -sqrt_mult_alt; last by apply: cnorm2_ge0.
apply: sqrt_le_1_alt.
rewrite (cnorm2_scalen _ (_ : (n <= (m + n))%N)) ?leq_addl //.
rewrite (cnorm2_scalen _ (_ : (n <= (m + n))%N)) ?leq_addl //.
rewrite [X in _ <= X](@GRing.mulr_suml (GRing.PzRing.clone _ R)).
apply: leR_sum => i _ _.
rewrite !get_csub ?scalen_lt ?scalen_lt_k ?leq_addl //.
rewrite !get_step_exact ?scalen_lt_k ?scalen_lt ?leq_addl //.
rewrite !get_step_float ?scalen_lt_k ?scalen_lt ?leq_addl //.
rewrite scalen_mod_lt ltnNge !if_neg scalen_mod_leq //.
have He : (2 ^ m = 2 ^ (m + n - n))%N by rewrite addnK.
rewrite modnDr addnK He.
apply: error_stepp_stepm => //; first by apply: leq_addl.
  apply: Hl.
  by apply: scalen_lt_k => //; apply: leq_addl.
by rewrite ltn_mod expn_gt0.
Qed.


Lemma csub_step_exact m n w l1 l2 : 
 csub (m + n).+1 (step_exact m n w l1) (step_exact m n w l2) =
 step_exact m n w  (csub (m + n).+1 l1 l2).
Proof.
apply/eq_in_map => i _; rewrite !get_step_exact //.
case: leqP => H.
  rewrite !get_csub //; first by ring.
  by apply: leq_ltn_trans (leq_subr _ _) _.
rewrite !get_csub //; first by ring.
rewrite (divn_eq i (2 ^ n.+1)).
apply: leq_trans (_ : (i %/ 2 ^ n.+1).+1 * 2 ^ n.+1 <= _)%N.
  rewrite mulSn [X in (_ < X)%N]addnC -addnA ltn_add2l //.
  by rewrite [X in (_ < X)%N]expnS mul2n -addnn ltn_add2r.
rewrite -[X in (_ <= 2 ^ X)%N]addnS expnD leq_mul2r expn_eq0 /=.
by rewrite ltn_divLR ?expn_gt0 // -expnD addnS.
Qed.

Lemma iformat_RNC v : iformat (RNC v).
Proof. by split; apply: generic_format_round. Qed.

(* This is 19 *)
Lemma cnorm_aux_floatDexact fma m n (w : C) (l1 l2 : seq C) :
let omega k := u + gk (m + n).-1 w fma k * (1 + u) in
  size l1 = (2 ^ (m + n))%N -> size l2 = (2 ^ (m + n))%N ->
  (forall i : nat, (i < 2 ^ (m + n))%N -> iformat (get l1 i)) ->
  cnorm (m + n) (csub (m + n) l1 l2) <= 
  cnorm (m + n) l2 * ((\prod_(i < n) (1 + omega i)%R)%RR - 1) ->
  (w ^ 2 ^ (m + n).-1)%C = 1 ->
   2 ^ 5 * u <= 1 ->
  cnorm (m + n) 
    (csub (m + n) (fft_aux_float fma m n w l1) 
                  (fft_aux_exact m n w l2)) <= 
    cnorm (m + n) (fft_aux_exact m n w l2) * 
    ((\prod_(i < (m + n)) (1 + omega i)%R)%RR - 1).
Proof.
move=> omega; rewrite {}/omega.
elim: m n w l1 l2 => // m IH n w l1 l2 Hs1 Hs2 Hi Hb Hw Hu /=.
under eq_bigr => i _ do rewrite -[(m + n)%nat]/((m .+1 + n).-1).
rewrite addSnnS.
apply: IH => //; last by rewrite -addSnnS.
- by rewrite size_step_float addnS.
- by rewrite size_step_exact addnS.
- rewrite addnS => i Hni.
  rewrite get_step_float //.
  by case: (_ < _)%N; apply: iformat_RNC.
pose omega i := u + gk (m + n) w fma i * (1 + u).
under eq_bigr => i _ do rewrite addnS -[u + _]/(omega i).
move : Hb.
(under [in X in X -> _]eq_bigr => i _ do rewrite -[u + _]/(omega i)) => Hb.
rewrite addnS.
apply: Rle_trans (cnormB _ _ _ _) _; last first.
apply: Rle_trans 
   (Rplus_le_compat_r _ _ _ (cnorm_step_floatDexact _ _ _ _)) _ => //.
have Cw : Cmod w = 1 by apply: (@w_norm1 ((m + n))).
have Cwm : Cmod (w ^ 2 ^ m) = 1 by rewrite Cmod_pow Cw pow1.
rewrite csub_step_exact !cnorm_step_exact_mult_2 //.
rewrite -[u + gk (m + n) w fma n * (1 + u)]/(omega n).
suff : 
  omega n * cnorm (m + n).+1 l1 +
  cnorm (m + n).+1 (csub (m + n).+1 l1 l2) <=
  cnorm (m + n).+1 l2 * ((\prod_(i < n.+1) (1 + omega i)%R)%RR - 1).
  suff: 0 <= sqrt 2 by rewrite /=; nra.
  by apply: sqrt_ge_0.
have Hnl1 : cnorm (m.+1 + n) l1 <= 
          cnorm (m.+1 + n) l2 * (\prod_(i < n) (1 + omega i)%R)%RR.
  have -> : l1 = cadd (m + n).+1 (csub (m + n).+1 l1 l2) l2.
    apply: (@eq_from_nth _ C0); first by rewrite size_cadd.
    rewrite Hs1 => i Hsi.
    rewrite -![nth C0 _ _]/(get _ _) get_cadd // get_csub //.
    set x1 := get _ _; set x2 := get _ _.
    by have : (x1 - x2 + x2 = x1)%C by ring.
  apply: Rle_trans (cnormD _ _ _) _.
  set x1 := cnorm _ _ in Hb *.
  set x2 := cnorm _ _ in Hb *.
  set xx := (\prod_(i < n) (1 + omega i)%R)%RR in Hb *.
  by lra.
rewrite big_ord_recr /= {1}/GRing.mul /=.
rewrite addSn in Hb Hnl1.
have O0 : 0 <= omega n.
  rewrite /omega.
  have u_ge_0 : 0 <= u by apply/Rlt_le/u_gt_0.
  have : 0 <= gk (m + n) w fma n by apply: gk_ge_0.
  by nra.
set xx := (\prod_(i < n) (1 + omega i)%R)%RR in Hb Hnl1 *.
by nra.
Qed.

(* This is theorem 7 *)
Lemma cnorm_floatDexact fma n (w : C) (l : seq C) :
let omega k := u + gk n.-1 w fma k * (1 + u) in
  size l = (2 ^ n)%N -> 
  (forall i : nat, (i < 2 ^ n)%N -> iformat (get l i)) ->
  (w ^ 2 ^ n.-1)%C = 1 ->
   2 ^ 5 * u <= 1 ->
  cnorm n 
    (csub n (fft_float fma n w l) (fft_exact n w l)) <= 
    cnorm n (fft_exact n w l) * 
    ((\prod_(i < n) (1 + omega i)%R)%RR - 1).
Proof.
move=> Hf Hs Hi.
have O0 : (0 < 2 ^ n)%N by rewrite expn_gt0.
have F := @cnorm_aux_floatDexact fma n 0 w (reverse_float n l) (reverse_exact n l).
rewrite !addn0 in F.
apply: F => //=.
- by rewrite size_map size_enum_ord.
- by rewrite size_map size_enum_ord.
- move=> i Hvi.
  rewrite /reverse_float /get.
  rewrite (nth_map (Ordinal O0)); first by apply/Hi/ltn_rdigitn.
  by rewrite size_enum_ord.
suff Hc : cnorm2 n (csub n (reverse_float n l) (reverse_exact n l)) = 0.
  by rewrite /cnorm Hc sqrt_0 big_ord0 Rminus_eq_0 Rmult_0_r; lra.
apply: big1 => /= i _.
suff -> : get (csub n (reverse_float n l) (reverse_exact n l)) i = C0.
  by rewrite Cmod_0 /GRing.zero /=; ring.
rewrite get_csub //.
rewrite /get (nth_map (Ordinal O0)).
  by set x := get _ _; have -> : (x - x = 0)%C by ring.
by rewrite size_enum_ord.
Qed.

End FFT.

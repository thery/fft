(* Copyright (c)  Inria. All rights reserved. *)

From Stdlib Require Import Reals  Psatz.
From Flocq Require Import Core Relative Sterbenz Operations.
From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
Require Import Rmore Cmore Fmore kahan_mult.
Set Implicit Arguments.

Section IFloat.

Variables  p: Z.
Variable beta: radix.
Hypothesis Hbeta2: Z.lt 1 beta.
(* not in the paper, needed for kahan *)
Hypothesis Hbeta_even : Z.even beta.
Hypothesis Hp2: Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Local 
Instance
 p_gt_0 
 : 
 Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Open Scope R_scope.

Notation u := (u p beta).
Notation u_gt_0 := (u_gt_0 p beta).

Variable choice : Z -> bool.

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation iformat := (generic_formatC beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RN := (round beta fexp (Znearest choice)).
Local Notation RNC:= (roundC beta fexp (Znearest choice)).
Local Notation ulp := (ulp beta fexp).

Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Definition A0_imult (c1 c2 : C) : C := 
  let a := RN (RN (c1.1 * c2.1) - RN (c1.2 * c2.2)) in
  let b := RN (RN (c1.1 * c2.2) + RN (c1.2 * c2.1)) in (a, b).

Lemma A0_iformat_imult c1 c2 : iformat (A0_imult c1 c2).
Proof. by split; apply: generic_format_round. Qed.
   
(* FMA on the left *)
Definition A1_imult (c1 c2 : C) : C := 
  let a := RN (c1.1 * c2.1 - RN (c1.2 * c2.2)) in
  let b := RN (c1.1 * c2.2 + RN (c1.2 * c2.1)) in (a, b).

Lemma A1_imult_0_l c : A1_imult 0 c = 0.
Proof.
by congr (_, _); 
   rewrite /= !(Rsimp01, round_0).
Qed.

Lemma A1_imult_0_r c : A1_imult c 0 = 0.
Proof.
by congr (_, _); rewrite /= !(Rsimp01, round_0).
Qed.

Lemma A1_imult_1_l c : A1_imult 1 c = RNC c.
Proof.
by rewrite /A1_imult /= !Rsimp01 round_0 !Rsimp01.
Qed.

Lemma A1_imult_1_r c : A1_imult c 1 = RNC c.
Proof.
rewrite /A1_imult /= !Rsimp01 round_0 Rsimp01; congr (_, _).
rewrite round_generic //.
by apply: generic_format_round.
Qed.

Lemma A1_imult_N1_r c : A1_imult c (-1) = (- RNC c)%C.
Proof.
rewrite /A1_imult /= !(Rsimp01, round_0, RN_sym) //; congr (_, _).
rewrite round_generic //=.
by apply: generic_format_round.
Qed.

Lemma A1_imult_N1_l c : A1_imult (-1) c = (- RNC c)%C.
Proof. by rewrite /A1_imult /= !(Rsimp01, round_0, RN_sym). Qed.

Lemma A1_imult_i_r c : A1_imult c Ci = ((RNC c) * Ci)%C.
Proof.
rewrite /A1_imult /= !(Rsimp01, round_0, RN_sym) //=; congr (_, _);
    rewrite /= !Rsimp01 //.
rewrite round_generic //.
by apply: generic_format_round.
Qed.

Lemma A1_imult_i_l c : A1_imult Ci c = (Ci * RNC c)%C.
Proof.
by rewrite /A1_imult /= !Rsimp01; congr (_, _);
    rewrite /= !Rsimp01 // ?RN_sym // round_generic //;
    apply: generic_format_round.
Qed.

Lemma A1_imult_Ni_r c : A1_imult c (- Ci)%C = (RNC c * (- Ci))%C.
Proof.
by rewrite /A1_imult /= !Rsimp01 round_0 Rsimp01; congr (_, _);
    rewrite /= -![_ * (-1)]Ropp_mult_distr_r !Rsimp01 !RN_sym // 
    !Ropp_involutive round_generic //;
    apply: generic_format_round.
Qed.

Lemma A1_imult_Ni_l c : A1_imult (- Ci) c = ((- Ci) * RNC c)%C.
Proof.
by rewrite /A1_imult /= !Rsimp01; congr (_, _);
    rewrite /= -![(-1) * _]Ropp_mult_distr_l !Rsimp01 !RN_sym // 
    ?Ropp_involutive round_generic //;
    apply: generic_format_round.
Qed.

Lemma A1_imult_pow41_l c1 c2 : (c1 ^ 4 = 1 -> A1_imult c1 c2 = c1 * RNC c2)%C.
Proof.
case/Cpow4_eq1_inv => ->; first by rewrite A1_imult_1_l Csimp01.
- by rewrite A1_imult_N1_l; ring.
- by rewrite A1_imult_i_l; ring.
rewrite A1_imult_Ni_l; ring.
Qed.

Lemma A1_imult_pow41_r c1 c2 : (c2 ^ 4 = 1 -> A1_imult c1 c2 = RNC c1 * c2)%C.
Proof.
case/Cpow4_eq1_inv => ->; first by rewrite A1_imult_1_r Csimp01.
- by rewrite A1_imult_N1_r; ring.
- by rewrite A1_imult_i_r; ring.
rewrite A1_imult_Ni_r; ring.
Qed.

Lemma iformat_A1_imult c1 c2 : iformat (A1_imult c1 c2).
Proof. by split; apply: generic_format_round. Qed.

(* Variants of A1 algo *) 
Definition A1_imult2 (c1 c2 : C) : C := 
  let a := RN (c1.1 * c2.1 - RN (c1.2 * c2.2)) in
  let b := RN (RN (c1.1 * c2.2) + c1.2 * c2.1) in (a, b).

Lemma imult2E c1 c2 : A1_imult2 c1 c2 = A1_imult c2 c1.
Proof.
rewrite /A1_imult /A1_imult2.
congr (RN (_ - RN _) , RN (_)); [lra|lra|].
by rewrite Rplus_comm; congr (_ + RN _); lra.
Qed.

Let Cerror_mult f c1 c2 := Cmod ((f c1 c2 - c1 * c2) / (c1 * c2))%C.
  
Lemma error_imult2 (c1 c2 : C) : 
  Cerror_mult A1_imult2 c1 c2 = Cerror_mult A1_imult c2 c1.
Proof. by rewrite /Cerror_mult imult2E [(c2 * _)%C]Cmult_comm. Qed.

Definition A1_imult3 (c1 c2 : C) : C := 
  let a := RN (RN (c1.1 * c2.1) - c1.2 * c2.2) in
  let b := RN (RN (c1.1 * c2.2) + c1.2 * c2.1) in (a, b).

Lemma A1_imult3E c1 c2 : A1_imult3 c1 c2 = A1_imult (- Ci * c1)%C (Ci * c2)%C.
Proof.
rewrite /A1_imult /A1_imult3 /= !Rsimp01.
rewrite -!Ropp_mult_distr_l !Ropp_involutive !RN_sym //.
congr (RN _ , RN _); first by lra.
by rewrite -!Ropp_mult_distr_r RN_sym //; lra.
Qed.

Lemma error_fma_A1_imult3 (c1 c2 : C) : 
  Cerror_mult A1_imult3 c1 c2 = Cerror_mult A1_imult (- Ci * c1)%C (Ci * c2)%C.
Proof.
rewrite /Cerror_mult.
have [->|c1_neq0] := Ceq_dec c1 0.
  by rewrite /= A1_imult3E Cmult_0_r A1_imult_0_l !Cmult_0_l.
have [->|c2_neq0] := Ceq_dec c2 0.
  by rewrite /= A1_imult3E Cmult_0_r A1_imult_0_r !Cmult_0_r.
have c1c2_neq_0 : (c1 * c2 <> 0)%C by apply: Cmult_neq_0.
rewrite /= !Cmod_div //; last first.
  repeat apply: Cmult_neq_0 => //.
    by apply/Copp_neq_0/Ci_neq_0.
  by apply: Ci_neq_0.
congr (_ _ _)%C; last first.
  rewrite !Cmod_mult !Cmod_opp !Cmod_Ci; lra.
rewrite A1_imult3E.
congr (Cmod (_ - _)%C).
congr (_, _); rewrite /=; lra.
Qed.

Definition A1_imult4 (c1 c2 : C) : C := 
  let a := RN (RN (c1.1 * c2.1) - c1.2 * c2.2) in
  let b := RN (c1.1 * c2.2 + RN (c1.2 * c2.1)) in (a, b).

Lemma A1_imult4E c1 c2 : A1_imult4 c1 c2 = A1_imult (Ci * c2)%C (- Ci * c1)%C.
Proof.
rewrite /A1_imult /A1_imult4 /= !Rsimp01.
rewrite -!Ropp_mult_distr_l !Ropp_involutive.
congr (RN _ , RN _).
  by rewrite -!Ropp_mult_distr_r RN_sym // Rmult_comm; lra.
by rewrite [X in RN X]Rmult_comm; lra.
Qed.

Lemma error_fma_A1_imult4 (c1 c2 : C) :
  Cerror_mult A1_imult4 c1 c2 = Cerror_mult A1_imult (Ci * c2)%C (- Ci * c1)%C.
Proof.
rewrite /Cerror_mult.
have [->|c1_neq0] := Ceq_dec c1 0.
  by rewrite /= A1_imult4E !Cmult_0_r A1_imult_0_r !Cmult_0_l.
have [->|c2_neq0] := Ceq_dec c2 0.
  by rewrite /= A1_imult4E !Cmult_0_r A1_imult_0_l !Cmult_0_l.
have c1c2_neq_0 : (c1 * c2 <> 0)%C by apply: Cmult_neq_0.
rewrite /= !Cmod_div //; last first.
  repeat apply: Cmult_neq_0 => //.
    by apply: Ci_neq_0.
  by apply/Copp_neq_0/Ci_neq_0.
congr (_ _ _)%C; last first.
  rewrite !Cmod_mult !Cmod_opp !Cmod_Ci; lra.
rewrite A1_imult4E.
congr (Cmod (_ - _)%C).
by congr (_, _); rewrite /=; lra.
Qed.

Definition cht a b c d := 
  let w1 := RN (a * b) in
  let w2 := RN (c * d) in
  let e1 := RN (a * b - w1) in
  let e2 := RN (c * d - w2) in
  let f := RN (w1 + w2) in 
  let e := RN (e1 + e2) in
  RN (f + e).

Lemma iformat_cht a b c d : format (cht a b c d).
Proof. by apply: generic_format_round. Qed.

Definition A2_imult (c1 c2 : C) : C := 
  let a := cht c1.1 c2.1 (-c1.2) c2.2 in
  let b := cht c1.1 c2.2 c1.2 c2.1 in (a, b).

Lemma iformat_A2_imult c1 c2 : iformat (A2_imult c1 c2).
Proof. by split; apply: iformat_cht. Qed.
   
Definition kahan a b c d := 
  let w := RN (c * d) in
  let e := RN (c * d - w) in
  let f := RN (a * b + w) in
  RN (f + e).

Let kahan1 := kahan_mult.kahan p beta choice.

Lemma kahanE a b c d : kahan a b c d = kahan1 a d (- c) b.
Proof.
rewrite /kahan /kahan1 /kahan_mult.kahan.
rewrite -Ropp_mult_distr_r RN_sym // /Rminus !Ropp_involutive.
by rewrite [d * _]Rmult_comm [c * d + _]Rplus_comm.
Qed.

(* See kahan papers *)
Lemma kahan_bound a b c d : 
  format a -> format b -> format c -> format d ->
  Rabs (kahan a b c d - (a * b + c * d)) <= 2 * u * Rabs (a * b + c * d).
Proof.
move=> Fa Fb Fc Fd.
have := kahan_bound Hbeta2 Hbeta_even Hp2 choice choice_sym Fa Fd 
          (generic_format_opp beta fexp _ Fc) Fb.
rewrite -/kahan1 -kahanE /u.
gsplit_Rabs; lra.
Qed.

Lemma format_kahan a b c d : format (kahan a b c d).
Proof. by apply: generic_format_round. Qed.

Definition A3_imult (c1 c2 : C) : C := 
  let a := kahan c1.1 c2.1 (- c1.2) c2.2 in
  let b := kahan c1.1 c2.2 c1.2 c2.1 in (a, b).

Lemma iformat_A3_imult c1 c2 : iformat (A3_imult c1 c2).
Proof. by split; apply: format_kahan. Qed.

(* Variants of A3 algo *) 
Definition A3_imult2 (c1 c2 : C) : C := 
  let a := kahan c1.1 c2.1 (- c1.2) c2.2 in
  let b := kahan c1.2 c2.1 c1.1 c2.2 in (a, b).

Lemma A3_imult_0_l c : A3_imult 0 c = 0.
Proof.
by congr (_, _); 
   rewrite /kahan  /= !(Rsimp01, round_0).
Qed.

Lemma A3_imult_0_r c : A3_imult c 0 = 0.
Proof.
by congr (_, _); rewrite /kahan /= !(Rsimp01, round_0).
Qed.

Lemma A3_imult2E c1 c2 : A3_imult2 c1 c2 = A3_imult c2 c1.
Proof.
rewrite /A3_imult /A3_imult2.
rewrite /kahan.
have->: - c1.2 * c2.2 = - c2.2 * c1.2 by lra.
by congr (RN (_ + RN _) , RN (_)); rewrite Rmult_comm //(Rmult_comm c1.1).
Qed.

  
Lemma error_imult3 (c1 c2 : C) : 
  Cerror_mult A3_imult2 c1 c2 = Cerror_mult A3_imult c2 c1.
Proof. by rewrite /Cerror_mult A3_imult2E [(c2 * _)%C]Cmult_comm. Qed.

Definition A3_imult3 (c1 c2 : C) : C := 
  let a := kahan (- c1.2) c2.2 c1.1 c2.1 in
  let b := kahan c1.2 c2.1 c1.1 c2.2 in (a, b).

Lemma A3_imult3E c1 c2 : A3_imult3 c1 c2 = A3_imult (- Ci * c1)%C (Ci * c2)%C.
Proof.
rewrite /A3_imult /A3_imult3 /kahan /= !Rsimp01.
rewrite -!Ropp_mult_distr_l !Ropp_involutive !RN_sym //.
by congr (RN _ , RN _); 
   rewrite -!Ropp_mult_distr_r // RN_sym // !Ropp_involutive.
Qed.

Lemma error_fma_A3_imult3 (c1 c2 : C) : 
  Cerror_mult A3_imult3 c1 c2 = Cerror_mult A3_imult (- Ci * c1)%C (Ci * c2)%C.
Proof.
rewrite /Cerror_mult.
have [->|c1_neq0] := Ceq_dec c1 0.
  by rewrite /= A3_imult3E Cmult_0_r A3_imult_0_l !Cmult_0_l.
have [->|c2_neq0] := Ceq_dec c2 0.
  by rewrite /= A3_imult3E Cmult_0_r A3_imult_0_r !Cmult_0_r.
have c1c2_neq_0 : (c1 * c2 <> 0)%C by apply: Cmult_neq_0.
rewrite /= !Cmod_div //; last first.
  repeat apply: Cmult_neq_0 => //.
    by apply/Copp_neq_0/Ci_neq_0.
  by apply: Ci_neq_0.
congr (_ _ _)%C; last first.
  rewrite !Cmod_mult !Cmod_opp !Cmod_Ci; lra.
rewrite A3_imult3E.
congr (Cmod (_ - _)%C).
congr (_, _); rewrite /=; lra.
Qed.

Definition A3_imult4 (c1 c2 : C) : C := 
  let a := kahan (- c1.2) c2.2 c1.1 c2.1 in
  let b := kahan c1.1 c2.2 c1.2 c2.1 in (a, b).

Lemma A3_imult4E c1 c2 : A3_imult4 c1 c2 = A3_imult (Ci * c2)%C (- Ci * c1)%C.
Proof.
rewrite /A3_imult /A3_imult4 /kahan /= !Rsimp01.
rewrite -!Ropp_mult_distr_l !Ropp_involutive.
congr (RN _ , RN _).
  by rewrite RN_sym // -Ropp_mult_distr_r RN_sym // !Ropp_involutive Rmult_comm
             (Rmult_comm c1.1).
by rewrite  -Ropp_mult_distr_r !Ropp_involutive Rmult_comm (Rmult_comm c1.2).
Qed.

Lemma error_fma_A3_imult4 (c1 c2 : C) :
  Cerror_mult A3_imult4 c1 c2 = Cerror_mult A3_imult (Ci * c2)%C (- Ci * c1)%C.
Proof.
rewrite /Cerror_mult.
have [->|c1_neq0] := Ceq_dec c1 0.
  by rewrite /= A3_imult4E !Cmult_0_r A3_imult_0_r !Cmult_0_l.
have [->|c2_neq0] := Ceq_dec c2 0.
  by rewrite /= A3_imult4E !Cmult_0_r A3_imult_0_l !Cmult_0_l.
have c1c2_neq_0 : (c1 * c2 <> 0)%C by apply: Cmult_neq_0.
rewrite /= !Cmod_div //; last first.
  repeat apply: Cmult_neq_0 => //.
    by apply: Ci_neq_0.
  by apply/Copp_neq_0/Ci_neq_0.
congr (_ _ _)%C; last first.
  rewrite !Cmod_mult !Cmod_opp !Cmod_Ci; lra.
rewrite A3_imult4E.
congr (Cmod (_ - _)%C).
congr (_, _); rewrite /=; lra.
Qed.


(* 2.1 *)
Notation error_bound_ulp_u := (error_bound_ulp_u beta Hp2 choice).

(* 2.2 *)
Notation RN_E := (RN_E beta Hp2 choice).

Inductive h := zero | one | two | three.

Definition zh h := 
  if h is zero then A0_imult else 
  if h is  one then A1_imult else 
  if h is  two then A2_imult else A3_imult.

Lemma zh_0_l h c : zh h 0 c = 0.
Proof.
pose l := (Rsimp01, round_0).
case: h => /=.
- by rewrite /A0_imult /= !l.
- by rewrite /A1_imult /= !l.
- by rewrite /A2_imult /cht /= !l.
by rewrite /A3_imult /kahan /= !l.
Qed.

Lemma zh_0_r h c : zh h c 0 = 0.
Proof.
pose l := (Rsimp01, round_0).
case: h => /=.
- by rewrite /A0_imult /= !l.
- by rewrite /A1_imult /= !l.
- by rewrite /A2_imult /cht /= !l.
by rewrite /A3_imult /kahan /= !l.
Qed.

Lemma Cmult_i c1 c2 :
  let (r, i) :=  (c1 * c2)%C in 
  (c1 * Ci * c2 = ((- i)%R, r))%C.
Proof. by congr (_, _); simpl; lra. Qed.

Lemma zh_i h c1 c2 :
  let (r, i) :=  zh h c1 c2 in 
  zh h c1 (Ci * c2)%C = ((- i)%R, r).
Proof.
case: c1 => a b; case: c2 => c d. 
case: h => /=.
- rewrite /A0_imult /= !Rsimp01 -!Ropp_mult_distr_r !RN_sym //.
  congr (_, _).
  by rewrite -[RHS]RN_sym //; congr RN; lra.
- rewrite /A1_imult /= !Rsimp01 -!Ropp_mult_distr_r !RN_sym //.
  congr (_, _).
  by rewrite -[RHS]RN_sym //; congr RN; lra.
- rewrite /A2_imult /= /cht.
  rewrite !Rsimp01 -!Ropp_mult_distr_r -!Ropp_mult_distr_l !RN_sym //.
  congr (_, _).
  rewrite -[RHS]RN_sym //; congr RN.
  rewrite Ropp_plus_distr -![in RHS]RN_sym //; congr (RN _ + RN _); first lra.
  by rewrite Ropp_plus_distr -![in RHS]RN_sym //; congr (RN _ + RN _); lra.
rewrite /A3_imult /= /kahan.
rewrite !Rsimp01 -!Ropp_mult_distr_r -!Ropp_mult_distr_l !RN_sym //.
congr (_, _).
rewrite -[RHS]RN_sym //; congr RN.
rewrite Ropp_plus_distr -![in RHS]RN_sym //; congr (RN _ + RN _); lra.
Qed.

Lemma error_i h (c1 c2 : C) : 
  Cerror_mult (zh h) c1 c2 = Cerror_mult (zh h) c1 (Ci * c2)%C.
Proof.
rewrite /Cerror_mult.
have [->|c1_neq0] := Ceq_dec c1 0.
  by rewrite !zh_0_l !Cmult_0_l Cminus_0_r Cdiv_0_l.
have [->|c2_neq0] := Ceq_dec c2 0.
  by rewrite !(zh_0_r, Cmult_0_r, Cminus_0_r) Cdiv_0_l.
have c1c2_neq_0 : (c1 * c2 <> 0)%C by apply: Cmult_neq_0.
rewrite !Cmod_div //; last first.
  by repeat apply: Cmult_neq_0 => //; apply: Ci_neq_0.
congr (_ / _); last by rewrite !Cmod_mult Cmod_Ci; lra.
have := zh_i h c1 c2.
case: zh => a b ->.
by congr (sqrt _); rewrite /Cmod /=; lra.
Qed.

Definition pos_cond c1 c2 :=  0 <= c1.1 * c1.2 * c2.1 * c2.2.

Lemma pos_cond_lemma c1 c2 : pos_cond c1 c2 \/ pos_cond c1 (Ci * c2)%C.
Proof. rewrite /pos_cond /=; nra. Qed.

(* Error for A3_mult                                                          *)

(* Theorem 2.1 *)
Lemma error_fma_A3_mult c1 c2 : 
  iformat c1 -> iformat c2 ->
  Cmod (A3_imult c1 c2 - c1 * c2)%C <= 2 * u * Cmod (c1 * c2)%C.
Proof.
pose r := (c1 * c2)%C.1.
pose i := (c1 * c2)%C.2.
pose r3 := (A3_imult c1 c2)%C.1.
pose i3 := (A3_imult c1 c2)%C.2.
move => Fc1 Fc2.
have -> : Cmod (c1 * c2)%C = sqrt (r ^ 2 + i ^ 2) by [].
have -> : Cmod (A3_imult c1 c2 - (c1 * c2)%C)%C = 
          sqrt ((r3 - r) ^ 2 + (i3 - i) ^ 2) by [].
pose a := c1.1; pose b := c1.2; pose c := c2.1; pose d := c2.2.
have u_gt_0 := u_gt_0.
have -> : 2 * u = sqrt ((2 * u) ^ 2) by rewrite sqrt_pow2; lra.
rewrite -sqrt_mult_alt; last by nra.
apply: sqrt_le_1_alt.
rewrite /r3 /i3 [_.1]/= -/a -/b -/c -/d [_.2]/= -/a -/b -/c -/d.
have Fa : format a by case: Fc1.
have Fb : format b by case: Fc1.
have FNb : format (- b) by apply: generic_format_opp.
have Fc : format c by case: Fc2.
have Fd : format d by case: Fc2.
have := kahan_bound Fa Fc FNb Fd.
have := kahan_bound Fa Fd Fb Fc.
rewrite -Ropp_mult_distr_l -[_ + - _]/r -[a * d + _]/i.
split_Rabs; nra.
Qed.

(* Error for A1_mult                                                          *)

(* 3.1 *)
Lemma bound_A1_mult_re c1 c2 :
  let (r, i) := (c1 * c2)%C in 
  let bd := c1.2 * c2.2 in
  Rabs ((A1_imult c1 c2).1 - r) <= u * Rabs r + u * Rabs bd + u ^ 2 * Rabs bd.
Proof.
case: c1 => a b; case: c2 => c d /=.
rewrite Rmult_1_r.
have [eps1 [-> eps1Lu]]:= RN_E (b * d).
have [eps2 [-> eps2Lu]]:= RN_E (a * c - b * d * (1 + eps1)).
rewrite [X in Rabs X](_ : _ = (a * c - b * d) * eps2 - (b * d) * eps1 - 
                              (b * d) * eps1 * eps2); last by lra.
apply: Rle_trans (Rabs_triang _ _) _.
apply: Rle_trans (Rplus_le_compat_r _ _ _ (Rabs_triang _ _)) _.
rewrite !Rabs_Ropp ![Rabs (_ * eps2)]Rabs_mult ![Rabs (_ * eps1)]Rabs_mult.
repeat apply: Rplus_le_compat.
- rewrite Rmult_comm.
  by apply: Rmult_le_compat_r; move: eps2Lu; gsplit_Rabs; lra.
- rewrite Rmult_comm.
  by apply: Rmult_le_compat_r; move: eps1Lu; gsplit_Rabs; lra.
rewrite [X in X <= _]Rmult_assoc Rmult_comm.
apply: Rmult_le_compat_r; first by gsplit_Rabs; lra.
by apply: Rmult_le_compat; split_Rabs; lra.
Qed.

Lemma bound_A1_mult_im c1 c2 : 
  let (r, i) := (c1 * c2)%C in 
  let bc := c1.2 * c2.1 in
  Rabs ((A1_imult c1 c2).2 - i) <= u * Rabs i + u * Rabs bc + u ^ 2 * Rabs bc.
Proof.
case: c1 => a b; case: c2 => c d /=.
rewrite Rmult_1_r.
have [eps1 [-> eps1Lu]]:= RN_E (b * c).
have [eps2 [-> eps2Lu]]:= RN_E (a * d + b * c * (1 + eps1)).
rewrite [X in Rabs X](_ : _ = (a * d + b * c) * eps2 + (b * c) * eps1 + 
                              (b * c) * eps1 * eps2); last by lra.
apply: Rle_trans (Rabs_triang _ _) _.
apply: Rle_trans (Rplus_le_compat_r _ _ _ (Rabs_triang _ _)) _.
rewrite ![Rabs (_ * eps2)]Rabs_mult ![Rabs (_ * eps1)]Rabs_mult.
repeat apply: Rplus_le_compat.
- rewrite Rmult_comm.
  by apply: Rmult_le_compat_r; move: eps2Lu; gsplit_Rabs; lra.
- rewrite Rmult_comm.
  by apply: Rmult_le_compat_r; move: eps1Lu; gsplit_Rabs; lra.
rewrite [X in X <= _]Rmult_assoc Rmult_comm.
apply: Rmult_le_compat_r; first by gsplit_Rabs; lra.
by apply: Rmult_le_compat; split_Rabs; lra.
Qed.

(* 3.2 *)
Lemma pos_cond_bound_A1_mult_im c1 c2 : 
  pos_cond c1 c2 -> 
  let (r, i) := (c1 * c2)%C in 
  let bc := c1.2 * c2.1 in
  Rabs ((A1_imult c1 c2).2 - i) <= u * Rabs i + u * Rabs bc.
Proof.
rewrite /pos_cond; case: c1 => a b; case: c2 => /= c d Hpc.
set g := _ + RN _; set i := _ + _.
have -> : RN g - i = (RN g - g) + (g - i) by lra.
apply: Rle_trans (Rabs_triang _ _) _.
have -> : g - i = RN (b * c) - b * c by rewrite /g /i; lra.
apply: Rplus_le_compat; last first.
  by have := error_bound_ulp_u (b * c); lra.
have [gLi|iLg] := Rle_lt_dec (ulp g) (ulp i).
  apply: Rle_trans (_ : /2 * ulp g <= _).
    by have := error_bound_ulp_u g; lra.
  apply: Rle_trans (_ : /2 * ulp i <= _); first by nra.
  by have := error_bound_ulp_u i; lra.
have u_gt_0 := u_gt_0.
apply: Rle_trans (_ : u * Rabs (b * c) <= _); last first.
  suff: Rabs (b * c) <= Rabs i by nra.
  by rewrite /i; gsplit_Rabs; nra.
have [k Hk] : exists k, Rabs i < pow k <= Rabs g.
  exists (mag beta g - 1)%Z.
  have g_neq0 : g <> 0.
    move=> g_eq0; rewrite g_eq0 ulp_FLX_0 in iLg.
    by have := ulp_ge_0 beta fexp i; lra.
  have := lt_mag_ulp beta Hp2 _ _ iLg.
  by have := bpow_mag_le beta g g_neq0; lra.
apply: Rle_trans (_ : Rabs g - pow k <= _); last first.
  apply: Rle_trans (_ : Rabs g - Rabs i <= _); first by split_Rabs; lra.
  apply: Rle_trans (_ : Rabs (g - i) <= _); first by split_Rabs; lra.
  have -> : g - i = RN (b * c) - b * c by rewrite /g /i; lra.
  by have := error_bound_ulp_u (b * c); lra.
have : Rabs (RN g - g) <= Rabs (pow k - g).
  have [_ ] := round_N_pt beta fexp choice g.
  apply.
  by apply: generic_format_bpow'; rewrite /fexp; lia.
have : Rabs (RN g - g) <= Rabs (- pow k - g).
  have [_ ] := round_N_pt beta fexp choice g.
  apply.
  apply: generic_format_opp.
  by apply: generic_format_bpow'; rewrite /fexp; lia.
split_Rabs; lra.
Qed.

(* 3.3 *)
(* error in the proof delta is also /2 ulp (b * d) -> should be ulp (b * d) *)
Lemma pos_cond_bound_A1_mult_re c1 c2 (a := c1.1) (b := c1.2)
                                      (c := c2.1) (d := c2.2): 
  pos_cond c1 c2 -> 
  iformat c1 -> iformat c2 ->
  Rabs (a * c) < /2 * Rabs (b * d) ->
  let (r, i) := (c1 * c2)%C in 
  Rabs ((A1_imult c1 c2).1 - r) <= u * Rabs r + u * Rabs (b * d).
Proof.
rewrite /iformat /pos_cond -/a -/b -/c -/d => Hpc [Fa Fb] [Fc Fd] acLbd.
pose r := (c1 * c2)%C.1.
pose f := a * c - RN (b * d).
pose C := ~ format (b * d) /\ ~ format f.
have [[NFbd NFf]|[Fbd | Ff]] : C \/ (format (b * d) \/ format f); last 2 first.
- apply: Rle_trans (_ : u * Rabs r <= _); last first.
    rewrite -[_ - _]/r.
    by have := u_gt_0; gsplit_Rabs; nra.
  rewrite -[c1.1 * _ - _]/r.
  rewrite /A1_imult /= /r /= -/a -/b -/c -/d [RN (b * d)]round_generic //.
  by have := error_bound_ulp_u (a * c - b * d); lra.
- apply: Rle_trans (_ : u * Rabs (b * d) <= _); last first.
    rewrite -[_ - _]/r.
    by have := u_gt_0; gsplit_Rabs; nra.
  rewrite -[c1.1 * _ - _]/r.
  rewrite /A1_imult /= /r /= -/a -/b -/c -/d round_generic //.
  have := error_bound_ulp_u (b * d); gsplit_Rabs; lra.
- by rewrite /C /format; lra.
have f_neq_0 : f <> 0.
  by move=> f_eq_0; case: NFf; rewrite f_eq_0; apply: generic_format_0.
have [ufLur|urLuf] := Rle_lt_dec (ulp f) (ulp r).
apply: Rle_trans (_ : Rabs (RN f - f) + Rabs (RN (b * d) - b * d) <= _).
  rewrite /A1_imult /= /r /= -/a -/b -/c -/d /f.
  by gsplit_Rabs; lra.
apply: Rle_trans (_ : /2 * ulp f + u * Rabs (b * d) <= _).
  by have := error_bound_ulp_u f; have := error_bound_ulp_u (b * d); lra.
  rewrite -[_ - _]/r.
  by have := error_bound_ulp_u r; lra.
have /ulp_lt_le := urLuf; move=> /(_ Hp2) => {}urLuf.
pose e := RN (b * d) - b * d.
have f_ge : Rabs f <= Rabs r + Rabs e.
  have rE : r = f + e by rewrite /r /f /e /= -/a -/b -/c -/d; lra.
  gsplit_Rabs; lra.
have f_ge1 : Rabs f <= IZR beta * Rabs r.
  have : Rabs e <= (IZR beta - 1) * Rabs r by apply: me_mult_mx_le.
by lra.
have ulpf_eq : ulp f = IZR beta * ulp r.
  suff: ulp f <= IZR beta * ulp r by lra.
  rewrite -pow1E Rmult_comm -ulp_FLX_exact_shift.
  apply: ulp_le.
  by rewrite Rabs_mult Rabs_pow pow1E; lra.
have [ubdLur|urLubd] := Rle_lt_dec (ulp (b * d)) (ulp r).
  apply: Rle_trans (_ : Rabs (RN f - f) + Rabs (RN (b * d) - b * d) <= _).
    rewrite /A1_imult /= /r /= -/a -/b -/c -/d /f.
    by gsplit_Rabs; lra.
  rewrite -[c1.1 * _ - _]/r.
  suff: Rabs (RN f - f) <= u * Rabs r.
    by have := error_bound_ulp_u (b * d); lra.
  apply: Rle_trans (_ : /2 * ulp r <= _).
    apply: eps1_ulpx => //.
    rewrite /kahan_mult.e /= /w' -/e.
    rewrite /x -[_ - _]/r /e.
    by have := error_bound_ulp_u (b * d); lra.
  have := @ulp_FLX_le beta p p_gt_0 r.
  by rewrite /u; lra.
have r_neq_0 : r <> 0.
  move=> r_eq_0.
  rewrite r_eq_0 ulp_FLX_0 in ulpf_eq.
  by have := ulp_gt_0 p beta f_neq_0; lra.
have urLbd1 : IZR beta * ulp r <= ulp (b * d).
  have bd_neq_0 : b * d <> 0.
    move=> bd_eq_0; rewrite bd_eq_0 ulp_FLX_0 in urLubd.
    by have := ulp_ge_0 beta fexp r; lra.
  rewrite !ulp_neq_0 // in urLubd *.
  rewrite -pow1E Rmult_comm -bpow_plus.
  by apply: bpow_le; have /lt_bpow := urLubd; lia.
have ulpbd_eq : ulp (b * d) = IZR beta * ulp r.
  suff: ulp (b * d) <= IZR beta * ulp r by lra.
  rewrite -pow1E [pow 1 * _]Rmult_comm -ulp_FLX_exact_shift.
  apply: ulp_le.
  rewrite [Rabs (r * _)]Rabs_mult Rabs_pow.
  apply: Rle_trans (_ : Rabs (b * d) * pow 1 - Rabs (a * c) * pow 1 <= _);
      last first.
    rewrite /r [_.1]/= -/a -/b -/c -/d.
    by have := bpow_gt_0 beta 1; gsplit_Rabs; nra.
  apply: Rle_trans (_ : /2 * Rabs (b * d) * pow 1 <= _); last first.
    by have := bpow_gt_0 beta 1; split_Rabs; nra.
  by rewrite pow1E; have := beta_ge_2 beta Hbeta2; gsplit_Rabs; nra.
have RfE : Rabs f = Rabs (RN (b * d)) - Rabs (a * c).
  have Hpc1 : 0 <= (b * d) * (a * c) by nra.
  have Hpc2 : 0 <= RN (b * d) * (b * d) by apply: RN_same_sign.
  suff: Rabs (a * c) <= Rabs (RN (b * d)) by rewrite /f; split_Rabs; nra.
  apply: Rle_trans (_ : Rabs (b * d) * (1 - u) <= _); last first.
    have := error_bound_ulp_u (b * d).
    gsplit_Rabs; nra.
  suff: 2 * u <= 1 by split_Rabs; nra.
  suff: pow (1 - p) <= 1 by rewrite /u; lra.
  by rewrite -(pow0E beta); apply: bpow_le; lia.
have [k Hk] : exists k, Rabs r < pow k <= Rabs f.
  exists (cexp r + p)%Z; split.
    have := ulp_FLX_bound beta Hp2 r_neq_0.
    by rewrite !ulp_neq_0 // -!bpow_plus; lra.
  apply: Rle_trans (_ : pow (cexp f + (p - 1)) <= _).
    apply: bpow_le.
    have := urLuf.
    by rewrite !ulp_neq_0 // -pow1E -!bpow_plus => /le_bpow; lia.
  have := ulp_FLX_bound beta Hp2 f_neq_0.
  by rewrite !ulp_neq_0 // -!bpow_plus; lra.
pose delta := ulp (b * d).
have Hdelta : Rabs f < pow k + /2 * delta.
  rewrite RfE /delta /f.
  apply: Rle_lt_trans (_ : Rabs (RN (b * d)) - Rabs (a * c) < _).
    by gsplit_Rabs; lra.
  apply: Rle_lt_trans (_ : Rabs ((b * d)) + /2 * ulp (b * d)
                           - Rabs (a * c) < _).
    by have := error_bound_ulp_u (b * d); gsplit_Rabs; lra.
  rewrite /r /= -/a -/b -/c -/d in Hk.
  by split_Rabs; lra.
have powf_lt : Rabs (pow k - (Rabs f)) < /2 * ulp (Rabs f).
  by rewrite /delta in Hdelta; rewrite ulp_abs; split_Rabs; lra.
have RNRfE : RN (Rabs f) = pow k.
  apply: RN_nearest_lt_half_ulp => //; first by apply: format_pow.
    by apply: bpow_ge_0.
  suff: ulp (pow k) = delta by split; split_Rabs; lra.
  rewrite /delta ulpbd_eq -ulpf_eq -[ulp f]ulp_abs.
  rewrite ulp_bpow ulp_neq_0 // /cexp /fexp; last by gsplit_Rabs; lra.
  rewrite (mag_unique_pos beta _ (k + 1)) //.
  have -> : (k + 1 - 1)%Z = k by lia.
  split; first by lra.
  rewrite bpow_plus pow1E.
  apply: Rle_lt_trans (_ : IZR beta * Rabs r < _); first by lra.
  by have := beta_ge_2 beta Hbeta2; nra.
have r_ge : pow k <= Rabs r + /2 * delta.
  apply: Rle_trans (_ : Rabs f <= _); first by lra.
  apply: Rle_trans (_ : Rabs (b * d) - Rabs (a * c) + /2 * delta  <= _);
      last first.
    by rewrite /r /= -/a -/b -/c -/d; gsplit_Rabs; lra.
  rewrite RfE /delta.
  by have := error_bound_ulp_u (b * d); gsplit_Rabs; lra.
apply: Rle_trans (_ : u * Rabs (b * d) <= _); last first.
  by have := u_gt_0; gsplit_Rabs; nra.
apply: Rle_trans (_ : /2 * ulp (b * d) <= _); last first.
  by have := error_bound_ulp_u (b * d); gsplit_Rabs; lra.
rewrite /= -/a -/b -/c -/d -[_ - b * _]/r -/f.
suff -> : Rabs (RN f - r) = Rabs (RN f) - Rabs r.
  by rewrite -RN_abs // RNRfE -/delta; lra.
have : Rabs r < Rabs (RN f) by rewrite -RN_abs // RNRfE; lra.
suff: Rabs (RN f - r) <= Rabs r by gsplit_Rabs; lra.
apply: Rle_trans (_ : u * (3 + 2 * u) * Rabs r <= _).
  have  /= := bound_A1_mult_re c1 c2.
  rewrite -/a -/b -/c -/d -/f -[a * c - _]/r.
  suff: Rabs (b * d) < 2 * Rabs r by have := u_gt_0 ; nra.
  by rewrite /r /= -/a -/b -/c -/d -/f; split_Rabs; nra.
suff: pow (1 - p) * (3 + pow (1 - p)) <= 2 by rewrite /u; gsplit_Rabs; nra.
have -> : 2 = 2 * pow (1 - p) * pow (p - 1).
  rewrite Rmult_assoc -bpow_plus.
  have -> : (1 - p + (p - 1) = 0)%Z by lia.
  by rewrite pow0E; lra.
suff: (3 + pow (1 - p)) <= 2 * pow (p - 1)
  by have := bpow_gt_0 beta (1 - p); nra.
have :  pow (1 - p) <= /2.
  suff: IZR beta * pow (1 - p) <= 1. 
    by have := beta_ge_2 beta Hbeta2; have := bpow_gt_0 beta (1 - p); nra.
  by rewrite -pow1E -(pow0E beta) -bpow_plus; apply: bpow_le; lia.
suff:  2 <= pow (p - 1) by lra.
apply: Rle_trans (beta_ge_2 beta Hbeta2) _.
by rewrite -pow1E; apply: bpow_le; lia.
Qed.

Arguments Cmod x%_C.

Lemma iformatMCi c : iformat c -> iformat (Ci * c)%C.
Proof.
case: c => a b  [/= Fa Fb]; split; rewrite /= !Rsimp01 //.
by apply: generic_format_opp.
Qed.

Lemma u_lt_1 : u < 1.
Proof.
rewrite /u.
suff: pow (1 - p) < pow 0 by rewrite pow0E; lra.
by apply: bpow_lt; lia.
Qed.

Lemma error_bound22_ulp_u a b : 
  beta = 2%Z :> Z -> p = 2%Z -> format a -> format b ->
  Rabs (RN (a * b) - a * b) <= /4 * ulp (a * b) <= u/2 * (Rabs (a * b)).
Proof.
move=> betaE pE.
wlog ab_pos : a b / 0 <= a * b => [H Fa Fb|].
  have [ab_pos|ab_neg] := Rle_lt_dec 0 (a * b).
    by apply: H => //; lra.
  have -> : Rabs (a * b) = Rabs (- a * b) by gsplit_Rabs; lra.
  have -> : ulp (a * b) = ulp (- a * b).
    by rewrite -ulp_opp; congr (ulp _); lra.
  suff -> : Rabs (RN (a * b) - a * b)  = Rabs (RN (- a * b) - (- a) * b).
    apply: H => //; first by lra.
    by apply: generic_format_opp.
  by rewrite -Ropp_mult_distr_l RN_sym //; gsplit_Rabs; lra.
wlog a_pos : a b ab_pos / 0 <= a => [H Fa Fb|].
  have [a_pos|a_neg] := Rle_lt_dec 0 a.
    by apply: H => //; lra.
  have -> : Rabs (a * b) = Rabs (- a * (- b)) by gsplit_Rabs; lra.
  have -> : ulp (a * b) = ulp (- a * (- b)).
    by congr (ulp _); lra.
  suff -> : Rabs (RN (a * b) - a * b) = 
            Rabs (RN (- a * (- b)) - (- a) * (- b)).
    apply: H => //; first by nra.
    - lra.
    - by apply: generic_format_opp.
    - by apply: generic_format_opp.
  by congr (Rabs (RN _ - _)); lra.
have [->|a_neq_0] := Req_dec a 0.
  rewrite !Rsimp01 round_0 ulp_FLX_0; gsplit_Rabs; lra. 
have [->|b_neq_0] := Req_dec b 0.
  by rewrite !Rsimp01 round_0 ulp_FLX_0; gsplit_Rabs; lra. 
have b_pos : 0 <= b by nra.
pose xa := (Ztrunc (mant a)).
pose ya := cexp a.
pose xb := (Ztrunc (mant b)).
pose yb := cexp b.
have betaEE : beta = radix2 by apply: radix_val_inj.
have uE : u = /4 by rewrite /u pE betaEE -[bpow radix2 (1 -2)]/(/2); lra.
rewrite uE => Fa Fb; move: (Fa) (Fb).
rewrite /generic_format /F2R /= -/xa -/ya -/xb -/yb => aE bE.
have xa_pos : (0 < xa)%Z.
  suff: 0 < IZR xa by move=> /lt_IZR.
  have : 0 < a by lra.
  rewrite aE; have := bpow_gt_0 beta ya.
  by nra.
have xb_pos : (0 < xb)%Z.
  suff: 0 < IZR xb by move=> /lt_IZR.
  have : 0 < b by lra.
  rewrite bE; have := bpow_gt_0 beta yb.
  by nra.
have [xa2|xa3] : xa = 2%Z \/ xa = 3%Z.
- have := mant_bound Fa a_neq_0.
  rewrite betaEE pE.
  have -> : bpow radix2 (2 - 1) = 2 by [].
  have -> : bpow radix2 2 = 4 by [].
  rewrite scaled_mantissa_generic // -/xa -betaEE -pE //.
  by rewrite -abs_IZR => [] [/le_IZR H1 /lt_IZR H2]; lia.
- rewrite aE xa2; set xx := 4 /2.
  have pow1_2 : 2 = pow 1 by rewrite betaEE.
  rewrite pow1_2 {}/xx -bpow_plus.
  rewrite Rmult_comm RN_mult_pow round_generic //.
  rewrite Rminus_eq_0 Rabs_R0.
  set v := b * _.
  split; first by have := ulp_ge_0 beta fexp v; lra.
  suff: ulp v <= Rabs v * pow (1 - 2).
    have -> : pow (1 - 2) = /2 by rewrite betaEE.
    have -> : pow 1 = 2 by rewrite betaEE.
    lra.
  by rewrite -pE; apply: ulp_FLX_le.
have [xb2|xb3] : xb = 2%Z \/ xb = 3%Z.
- have := mant_bound Fb b_neq_0.
  have -> : pow (p - 1) = 2 by rewrite betaEE pE.
  have -> : pow p = 4 by rewrite betaEE pE.
  rewrite scaled_mantissa_generic // -/xb.
  by rewrite -abs_IZR => [] [/le_IZR H1 /lt_IZR H2]; lia.
- rewrite bE xb2; set xx := 4 /2.
  have pow1_2 : 2 = pow 1 by rewrite betaEE.
  rewrite pow1_2 {}/xx -bpow_plus.
  rewrite RN_mult_pow round_generic //.
  rewrite Rminus_eq_0 Rabs_R0.
  set v := a * _.
  split; first by have := ulp_ge_0 beta fexp v; lra.
  suff: ulp v <= Rabs v * bpow beta (1 - 2).
    have -> : pow (1 - 2) = /2 by rewrite betaEE.
    have -> : pow 1 = 2 by rewrite pow1E betaE.
    lra.
  by rewrite -pE; apply: ulp_FLX_le.
suff: Rabs (RN 9 - 9) <= /4 * ulp 9 <= 9 / 8.
  have -> : a * b = 9 * bpow beta (ya + yb).
    by rewrite [in LHS]aE [in LHS]bE xa3 xb3 bpow_plus; lra.
  rewrite RN_mult_pow // ulp_FLX_exact_shift.
  have F_g := bpow_gt_0 beta (ya + yb).
  gsplit_Rabs; nra.
have -> : ulp 9 = 4.
  rewrite ulp_neq_0 /cexp /fexp; last by lra.
  rewrite pE betaEE.
  rewrite (mag_unique_pos radix2 _ 4) //=.
  by lra.
split; last by lra.
have ulp8 : ulp 8 = 4.
  rewrite ulp_neq_0 /cexp /fexp ; last by lra.
  rewrite pE betaEE.
  by rewrite (mag_unique_pos radix2 _ 4) /=; lra.
suff -> : RN 9 = 8 by gsplit_Rabs; lra.
have pow3 : 8 = pow 3 by rewrite betaEE.
have succ8: succ beta fexp 8 = 12 by rewrite succ_eq_pos ?ulp8; lra.
have Rf : round beta fexp Zfloor 9 = 8.
  apply: round_DN_eq.
  rewrite pow3; apply: generic_format_bpow; rewrite /fexp ; lia.
  lra.
have Rc: round beta fexp Zceil 9 = 12.
apply: round_UP_eq.
pose f := Float beta 3 2.
apply:(@FLX_format_Rabs_Fnum p beta Hp2 12 f).
- by rewrite /F2R /= betaEE /Z.pow_pos /=; lra.
- rewrite /f /= Rabs_pos_eq; last by lra.
  by rewrite betaEE pE -[bpow _ _]/4; lra.
- rewrite -{1}succ8 pred_succ; first by lra.
  by rewrite pow3; apply: generic_format_bpow; rewrite /fexp ; lia.
rewrite -Rf; apply: round_N_eq_DN;  lra.
Qed. 

Lemma RN22_E t1 t2 :
  p = 2%Z -> beta = 2%Z :> Z -> format t1 -> format t2 ->
  exists d, RN (t1 * t2) = (t1 * t2) * (1 + d) /\ Rabs d <= u / 2.
Proof.
move=> pE betaEE Ft1 Ft2.
have [->|t_neq_0] := Req_dec (t1 * t2) 0.
  exists 0; split; first by rewrite round_0; lra.
  by have := u_gt_0; rewrite Rabs_R0; lra.
exists ((RN (t1 * t2) - (t1 * t2)) / (t1 * t2)); split; first by field; nra.
rewrite Rabs_div //.
apply/Rle_div_l; first by gsplit_Rabs; lra.
by case: (error_bound22_ulp_u betaEE pE Ft1 Ft2); lra.
Qed.

Lemma bound22_A1_mult_re c1 c2 :
  p = 2%Z -> beta = 2%Z :> Z ->
  let (r, i) := (c1 * c2)%C in 
  let bd := c1.2 * c2.2 in
  iformat c1 -> iformat c2 ->
  Rabs ((A1_imult c1 c2).1 - r) <= 
    u * Rabs r + u * Rabs bd + u ^ 2 / 2 * Rabs bd.
Proof.
move=> pE betaEE.
case: c1 => a b; case: c2 => c d /= [/= Fa Fb] [/= Fc Fd].
rewrite Rmult_1_r.
have [eps1 [-> eps1Lu]]:= RN22_E pE betaEE Fb Fd.
have [eps2 [-> eps2Lu]]:= RN_E (a * c - b * d * (1 + eps1)).
rewrite [X in Rabs X](_ : _ = (a * c - b * d) * eps2 - (b * d) * eps1 - 
                              (b * d) * eps1 * eps2); last by lra.
apply: Rle_trans (Rabs_triang _ _) _.
apply: Rle_trans (Rplus_le_compat_r _ _ _ (Rabs_triang _ _)) _.
rewrite !Rabs_Ropp ![Rabs (_ * eps2)]Rabs_mult ![Rabs (_ * eps1)]Rabs_mult.
repeat apply: Rplus_le_compat.
- rewrite Rmult_comm.
  by apply: Rmult_le_compat_r; split_Rabs; lra.
- rewrite Rmult_comm.
  by apply: Rmult_le_compat_r; split_Rabs; lra.
rewrite [X in X <= _]Rmult_assoc Rmult_comm.
apply: Rmult_le_compat_r; first by gsplit_Rabs; lra.
have -> : u * u / 2 = u / 2 * u by lra.
apply: Rmult_le_compat; split_Rabs; lra.
Qed.

(* Theorem 3.1 *)
Lemma error_fma_A1_mult c1 c2 : 
  iformat c1 -> iformat c2 ->
  Cmod (A1_imult c1 c2 - c1 * c2)%C <= 2 * u * Cmod (c1 * c2).
Proof.
wlog Hc : c1 c2 / pos_cond c1 c2 => [H|].
  move=> Fc1 Fc2.
  have [Hc | Hc] :=  pos_cond_lemma c1 c2; first by apply: H.
  have F x : x ^ 2 =  (- x) ^ 2 by lra.
  have ->: Cmod (c1 * c2) =  Cmod (c1 * (Ci * c2)%C).
    by rewrite !Cmod_mult Cmod_Ci; lra.
  have ->: Cmod (A1_imult c1 c2 - (c1 * c2)%C) = 
          Cmod (A1_imult c1 (Ci * c2)%C - (c1 * (Ci * c2))%C).
    case: {Fc1 Fc2 Hc}c1 => a b; case: c2 => c d.
    rewrite /Cconj /Cplus /A1_imult /= !Rsimp01 /Cmod.
    rewrite Rplus_comm; congr (sqrt (_ + _ ^ 2)).
      rewrite [RHS]F; congr (_ ^ 2).
      rewrite /= !Rsimp01 !Ropp_plus_distr -RN_sym // !Ropp_plus_distr.
      by rewrite -Ropp_mult_distr_r !Ropp_involutive.
    by rewrite /= -Ropp_mult_distr_r RN_sym // !Rsimp01 -Ropp_mult_distr_r.
  apply: H => //.
  by apply: iformatMCi.
pose r := (c1 * c2)%C.1.
pose i := (c1 * c2)%C.2.
pose r1 := (A1_imult c1 c2)%C.1.
pose i1 := (A1_imult c1 c2)%C.2.
have -> : Cmod (c1 * c2) = sqrt (r ^ 2 + i ^ 2) by [].
have -> : Cmod (A1_imult c1 c2 - (c1 * c2)%C) = 
          sqrt ((r1 - r) ^ 2 + (i1 - i) ^ 2) by [].
set q := /(u ^ 2) * ((r1 - r) ^ 2 + (i1 - i) ^ 2).
have u_gt_0 := u_gt_0.
move=> Fc1 Fc2.
suff H : q <= 4 * (r ^ 2 + i ^ 2).
  have -> : 2 * u * sqrt (r ^ 2 + i ^ 2) = 
            sqrt ((2 ^ 2 * (r ^ 2 + i ^ 2) * u ^ 2)).
    by rewrite 2?sqrt_mult ?sqrt_pow2; nra.
  apply: sqrt_le_1_alt.
  apply/Rle_div_l; first by nra.
  rewrite [_/_]Rmult_comm.
  by have -> : 2 ^ 2 = 4 by lra.
pose a := c1.1; pose b := c1.2; pose c := c2.1; pose d := c2.2. 
have rE : Rabs r = Rabs (Rabs (a * c) - Rabs (b * d)).
  rewrite /a /b /c /d /pos_cond /r /= in Hc *.
  by gsplit_Rabs; nra.
have [bdLac|acLbd] := Rle_lt_dec (Rabs (b * d)) (Rabs (a * c)).
  have {}rE : Rabs r = Rabs (a * c) - Rabs (b * d).
    by split_Rabs; lra.
  have F1 : Rabs (r1 - r) <= u * (Rabs (a * c) + Rabs (b * d)). 
    have F1 :  u * Rabs (b * d) <= Rabs (b * d).
      have := u_lt_1; gsplit_Rabs; nra.
    have := bound_A1_mult_re c1 c2.
    by rewrite -/a -/b -/c -/d -/r1 -[a * c - _]/r rE; nra.
  have F2 : Rabs (i1 - i) <= u * (Rabs (a * d) + 2 * Rabs (b * c)).
    have := pos_cond_bound_A1_mult_im Hc.
    rewrite -/a -/b -/c -/d -/i1 -[a * d + _]/i /= {2}/i /= -/a -/b -/c -/d.
    by have := u_gt_0; gsplit_Rabs; nra.
  rewrite /q Rmult_comm; apply/Rle_div_l; first by nra.
  apply: Rle_trans (_ : ((a * c) ^ 2 + (b * d) ^ 2 + (a * d) ^ 2 + 
                        4 * (b * c) ^ 2 + 6 * a * b * c * d) * u ^ 2 <=  _).
    by rewrite /pos_cond -/a -/b -/c -/d in Hc; split_Rabs; nra.
  rewrite /r /i [_.1]/= [(_ * _)%C.2]/= -/a -/b -/c -/d.
  suff: 0 <= (a * c - b * d) ^ 2 by nra.
  by apply: pow2_ge_0.
have {}rE : Rabs r = Rabs (b * d) - Rabs (a * c).
  by rewrite rE; split_Rabs; nra.
have [bd2Lac|acLbd2] := Rle_lt_dec (/2 * Rabs (b * d)) (Rabs (a * c)).
  pose u1 := if (beta * p =? 4)%Z then u / 2 else u.
  have Fr : Rabs (r1 - r) <= u * (2 * Rabs (b * d) - Rabs (a * c) +
                                  u1 * Rabs (b * d)). 
    have HuR : u * Rabs (b * d) <= Rabs (b * d)
       by have := u_lt_1; gsplit_Rabs; nra.
    rewrite /u1.
    have [He | He] := Z.eqb_spec.
      have [bE pE] : ((beta = 2 :> Z) /\ p = 2)%Z by nia.
      have := bound22_A1_mult_re pE bE Fc1 Fc2.
      by rewrite -[(_).1]/r1 -/a -/b -/c -/d -/r -[a * c - _]/r rE; lra.
    have := bound_A1_mult_re c1 c2.
    by rewrite  -/a -/b -/c -/d -/r1  -[a * c - _]/r rE; lra.
  have Fi : Rabs (i1 - i) <= u * (Rabs (a * d) + 2 * Rabs (b * c)).
    have := pos_cond_bound_A1_mult_im Hc.
    rewrite -/a -/b -/c -/d -/i1 -[a * d + _]/i /= {2}/i /= -/a -/b -/c -/d.
    by have := u_gt_0; gsplit_Rabs; nra.
  pose q' := 4 * u1 * (b * d) ^ 2.
  pose q'' := u1 ^ 2 * (b * d) ^ 2 - 2 * a * b * c * d * u1.
  apply: Rle_trans (_ : ((a * c) ^ 2 + 4 * (b * d) ^ 2 + (a * d) ^ 2 + 
                        4 * (b * c) ^ 2 + q' + q'') <=  _).
    have ->: (a * c) ^ 2 + 4 * (b * d) ^ 2 + (a * d) ^ 2 + 4 * (b * c) ^ 2 
               + q' + q'' =
             (2 * Rabs (b * d) - Rabs (a * c) + u1 * Rabs (b * d)) ^ 2 +
               (Rabs (a * d) + 2 * Rabs (b * c)) ^ 2.
      rewrite /q' /q''.
      by rewrite /pos_cond -/a -/b -/c -/d in Hc; split_Rabs; nra.
    rewrite /q Rmult_comm; apply/Rle_div_l; first by nra.
    by move: Fr Fi; gsplit_Rabs; nra.
  apply: Rle_trans  (_ : ((a * c) ^ 2 + 4 * (b * d) ^ 2 + (a * d) ^ 2 + 
                          4 * (b * c) ^ 2 + q') <=  _).
    suff: q'' <= 0 by lra.
    suff:  (b * d) ^ 2 <= 2 * a * b * c * d.
      rewrite /q''.
      suff: u1 ^ 2 <= u1 by nra.
      rewrite /u1; have [He | He] := Z.eqb_spec.
        have [bE pE] : ((beta = 2 :> Z) /\ p = 2)%Z by nia.
        suff: pow (1 - p) ^ 2 <= pow (1 - p) by rewrite /u; nra.
        by rewrite -pow2M; apply: bpow_le; lia.
      suff: pow (1 - p) ^ 2 <= pow (1 - p) by rewrite /u; nra.
      by rewrite -pow2M; apply: bpow_le; lia.       
    by rewrite /pos_cond -/a -/b -/c -/d in Hc; split_Rabs; nra.
  suff: q' <= 3 * (a * c) ^ 2.
    rewrite /r /i [_.1]/= [(_ * _)%C.2]/= -/a -/b -/c -/d.
    by nra.
  rewrite /q' /u1; have [He | He] := Z.eqb_spec.
    have [bE pE] : ((beta = 2 :> Z) /\ p = 2)%Z by nia.
    have uE : u = 1 / 4.
      by rewrite /u pE /= bE /= IZR_Zpower_pos /=; lra.
    by move: bd2Lac; gsplit_Rabs; nra.
  have bEOpE : ((2 < beta) \/ 2 < p)%Z by nia.
  have u_Le : u <= /6.
    suff: pow (1 - p) <= /3 by rewrite /u; lra.
    case: bEOpE => bEIpE.
      apply: Rle_trans (_ : pow (-1) <= _); first by apply: bpow_le; lia.
      rewrite /= IZR_Zpower_pos /= Rmult_1_r.
      apply: Rinv_le; first by lra.
      by apply: IZR_le; lia.
    apply: Rle_trans (_ : pow (-2) <= _); first by apply: bpow_le; lia.
    rewrite (bpow_opp _ 2%Z).
    apply: Rinv_le; first by lra.
    rewrite (pow2M _ 1%Z) pow1E. 
    by have := beta_ge_2 beta Hbeta2; nra.
  suff: 2 * (b * d) ^ 2 <= 9 * (a * c) ^ 2 by rewrite /q'; nra.
  by move: bd2Lac; gsplit_Rabs; nra.
have F1 : Rabs (r1 - r) <= u * (2 * Rabs (b * d) - Rabs (a * c)). 
  have F1 :  u * Rabs (b * d) <= Rabs (b * d).
    have := u_lt_1; gsplit_Rabs; nra.
  have := pos_cond_bound_A1_mult_re Hc Fc1 Fc2 acLbd2.
  by rewrite  -/a -/b -/c -/d -/r1  -[a * c - _]/r rE; lra.
have F2 : Rabs (i1 - i) <= u * (Rabs (a * d) + 2 * Rabs (b * c)).
  have := pos_cond_bound_A1_mult_im Hc.
  rewrite -/a -/b -/c -/d -/i1 -[a * d + _]/i /= {2}/i /= -/a -/b -/c -/d.
  by have := u_gt_0; gsplit_Rabs; nra.
rewrite /q Rmult_comm; apply/Rle_div_l; first by nra.
apply: Rle_trans (_ : ((a * c) ^ 2 + 4 * (b * d) ^ 2 + (a * d) ^ 2 + 
                        4 * (b * c) ^ 2) * u ^ 2  <=  _).
  suff <- : (2 * Rabs (b * d) - Rabs (a * c)) ^ 2 + 
        (Rabs (a * d) + 2 * Rabs (b * c)) ^ 2 = 
        ((a * c) ^ 2 + 4 * (b * d) ^ 2 + (a * d) ^ 2 + 4 * (b * c) ^ 2).
    by split_Rabs; nra.
  by rewrite /pos_cond -/a -/b -/c -/d in Hc; gsplit_Rabs; nra.
rewrite /r /i [_.1]/= [(_ * _)%C.2]/= -/a -/b -/c -/d.
by nra.
Qed.

(* Error for A2_mult                                                          *)

(* 3.4 *)
Lemma error_cht a b c d (r := a * b + c * d) (r' := cht a b c d) :
  format a -> format b -> format c -> format d ->
  Rabs (r' - r) <= (2 * u + u ^ 2) * Rabs r + 
                   (2 * u ^ 2 + 2 * u ^ 3) * (Rabs (a * b) + Rabs (c * d)).
Proof.
move=> Fa Fb Fc Fd.
pose w1 := RN (a * b).
pose w2 := RN (c * d).
pose e1 := a * b - w1.
have Fe1 : format e1.
  have -> : e1 = - (w1 - a * b) by rewrite /e1; lra.
  by apply/generic_format_opp/Mult_error.mult_error_FLX.
have RNe1E : RN e1 = e1 by rewrite round_generic.
pose e2 := c * d - w2.
have Fe2 : format e2.
  have -> : e2 = - (w2 - c * d) by rewrite /e2; lra.
  by apply/generic_format_opp/Mult_error.mult_error_FLX.
have RNe2E : RN e2 = e2 by rewrite round_generic.
pose f := RN (w1 + w2); pose e := RN (e1 + e2).
have r'E : r' = RN (f + e) by rewrite /r' /cht -/e1 RNe1E -/e2 RNe2E.
have [eps1 [Reps1 eps1_le]] := RN_E (a * b).
rewrite -/w1 in Reps1.
have [eps2 [Reps2 eps2_le]] := RN_E (c * d).
rewrite -/w2 in Reps2.
have [eps3 [Reps3 eps3_le]] := RN_E (w1 + w2).
rewrite -/f in Reps3.
have [eps4 [Reps4 eps4_le]] := RN_E (e1 + e2).
rewrite -/e in Reps4.
have [eps5 [Reps5 eps5_le]] := RN_E (f + e).
rewrite -r'E in Reps5.
have -> : r' - r = (eps3 + eps5 + eps3 * eps5) * r 
                + (a * b * eps1  + c * d * eps2) * (eps3 - eps4) * (1 + eps5).
  rewrite /r /e1 /e2 in Reps1 Reps2 Reps3 Reps4 Reps5 *.
  by ring [Reps1 Reps2 Reps3 Reps4 Reps5].
apply: Rle_trans (Rabs_triang _ _) _.
apply: Rplus_le_compat.
  rewrite Rabs_mult.
  by apply: Rmult_le_compat_r; split_Rabs; nra.
have -> : (2 * u ^ 2 + 2 * u ^ 3) * (Rabs (a * b) + Rabs (c * d)) =
          ((u * (Rabs (a * b) + Rabs (c * d))) * (2 * u)) * (1 + u).
  by lra.
rewrite Rabs_mult.
(apply: Rmult_le_compat; try by apply: Rabs_pos); last by split_Rabs; lra.
rewrite Rabs_mult.
(apply: Rmult_le_compat; try by apply: Rabs_pos); last by split_Rabs; lra.
by move: eps1_le eps2_le; gsplit_Rabs; nra.
Qed.

(* Theorem 3.2 *)
Lemma error_fma_A2_mult c1 c2 : 
  iformat c1 -> iformat c2 ->
  Cmod (A2_imult c1 c2 - c1 * c2)%C <= (2 * u + 6 * u ^ 2) * Cmod (c1 * c2)%C.
Proof.
wlog Hc : c1 c2 / pos_cond c1 c2 => [H|].
  move=> Fc1 Fc2.
  have [Hc | Hc] :=  pos_cond_lemma c1 c2; first by apply: H.
  have F x : x ^ 2 =  (- x) ^ 2 by lra.
  have ->: Cmod (c1 * c2) =  Cmod (c1 * (Ci * c2)%C).
    by rewrite !Cmod_mult Cmod_Ci; lra.
  have ->: Cmod (A2_imult c1 c2 - (c1 * c2)%C) = 
          Cmod (A2_imult c1 (Ci * c2)%C - (c1 * (Ci * c2))%C).
    case: {Fc1 Fc2 Hc}c1 => a b; case: c2 => c d.
    rewrite /Cconj /Cplus /A2_imult /= !Rsimp01 /Cmod.
    rewrite Rplus_comm; congr (sqrt (_ + _ ^ 2)).
      rewrite [RHS]F; congr (_ ^ 2).
      rewrite /= /cht /= !Rsimp01 !Ropp_plus_distr -RN_sym // !Ropp_plus_distr.
      congr (RN (_ + _) + _); last by lra.
        rewrite -RN_sym // !Ropp_plus_distr -!RN_sym //.
        by congr (RN (RN _ + RN _)); lra.
      rewrite -RN_sym // !Ropp_plus_distr -!RN_sym //.
      congr (RN (RN _ + RN _)).
        by rewrite Ropp_plus_distr -RN_sym //; congr (_ - RN _); lra.
      by rewrite Ropp_plus_distr -RN_sym //; congr (_ - RN _); lra.
    rewrite /= /cht /= !Rsimp01 !Ropp_plus_distr.
    by congr (RN (RN(_ + RN _) + RN (_ + RN (_ - RN _))) + _); lra.
  apply: H => //.
  by apply: iformatMCi.
pose a := c1.1; pose b := c1.2; pose c := c2.1; pose d := c2.2.
have ac_bd_pos : 0 <= (a * c) * (b * d).
  by rewrite /pos_cond -/a -/b -/c -/d in Hc; nra.
have ad_bc_pos : 0 <= (a * d) * (b * c).
 by rewrite /pos_cond -/a -/b -/c -/d in Hc; nra.
move=> Fc1 Fc2.
pose r := (c1 * c2)%C.1.
pose i := (c1 * c2)%C.2.
pose r2 := (A2_imult c1 c2)%C.1.
pose i2 := (A2_imult c1 c2)%C.2.
have RrE : Rabs r = Rabs (Rabs (a * c) - Rabs (b * d)).
  by rewrite /r /= -/a -/b -/c -/d; split_Rabs; nra.
have RiE : Rabs i = Rabs (a * d) + Rabs (b * c).
  by rewrite /i /= -/a -/b -/c -/d; split_Rabs; nra.
have -> : Cmod (c1 * c2)%C = sqrt (r ^ 2 + i ^ 2) by [].
have -> : Cmod (A2_imult c1 c2 - (c1 * c2)%C)%C = 
          sqrt ((r2 - r) ^ 2 + (i2 - i) ^ 2) by [].
have u_gt_0 := u_gt_0.
have Fa : format a by case: Fc1.
have Fb : format b by case: Fc1.
have FNb : format (- b) by apply: generic_format_opp.
have Fc : format c by case: Fc2.
have Fd : format d by case: Fc2.
have -> : (2 * u + 6 * u ^ 2) * sqrt (r ^ 2 + i ^ 2) = 
            sqrt ((2 * u + 6 * u ^ 2) ^ 2 * (r ^ 2 + i ^ 2)).
  by rewrite sqrt_mult ?sqrt_pow2 //; nra.
apply: sqrt_le_1_alt.
have Fi : Rabs (i2 - i) <= 2 * u * (1 + 3 / 2 * u + u ^ 2) * Rabs i. 
  have := error_cht Fa Fd Fb Fc.
  rewrite -[cht a d b c]/i2 -[a * d + _]/i.
  by rewrite RiE;lra.
pose r'' := Rabs (a * c) + Rabs (b * d).
have Fr : Rabs (r2 - r) <= 2 * u * ((1 + / 2 * u) * Rabs r + (u + u ^ 2) * r'').
  have := error_cht Fa Fc FNb Fd.
  rewrite -[cht a c _ _]/r2 -Ropp_mult_distr_l -[a * c + _]/r /r''.
  by rewrite RrE Rabs_Ropp; lra.
pose B := (1 + /2 * u) ^ 2 * r ^ 2 + (2 * u + 3 * u ^ 2 + u ^ 3) * 
          Rabs r * r'' + 
          (u + u ^ 2) ^ 2 * r'' ^ 2 + (1 + 3 / 2 * u + u ^ 2) ^ 2 * i ^ 2.
apply: Rle_trans (_ : 4 * u ^ 2 * B <= _).
  have Fi' :  (i2 - i) ^ 2 <= 4 * u ^ 2 * (1 + 3 / 2 * u + u ^ 2) ^ 2 * i ^ 2.
    by move: Fi; gsplit_Rabs; nra.
  have Fr' :  (r2 - r) ^ 2 <= 4 * u ^ 2 * 
                             ((1 + / 2 * u) * Rabs r + (u + u ^ 2) * r'') ^ 2.
    by move: Fr; gsplit_Rabs; nra.
  by rewrite /B; move: Fi' Fr'; gsplit_Rabs; nra.
pose B' := (3 + u) * Rabs r * r'' + (1 + 2 * u + u ^ 2) * r'' ^ 2 +
           (4 + 3 * u + u ^ 2) * i ^ 2.
have BE : B = (1 + u + /4 * u ^ 2) * (r ^ 2 + i ^ 2) + 2 * u * (Rabs r * r''
              + i ^ 2) + u ^ 2 * B'.
    by rewrite /B /B'; lra.
have Hacbd : 2 * a * b * c * d <= (a * c) ^ 2 + (b * d) ^ 2.
  suff: 0 <= (a * c - b * d) ^ 2 by nra.
  by apply: pow2_ge_0.
have Hadbc : 2 * a * b * c * d <= (a * d) ^ 2 + (b * c) ^ 2.
  suff: 0 <= (a * d - b * c) ^ 2 by nra.
  by apply: pow2_ge_0.
have rE : r ^ 2 + i ^ 2 = (a * c) ^ 2 + (b * d) ^ 2 + (a * d) ^ 2 + (b * c) ^ 2.
  by rewrite /r /i [_.1]/=  -/a -/b -/c -/d [_.2]/=  -/a -/b -/c -/d; lra. 
have rr''_le : Rabs r * r'' <= r ^ 2 + i ^ 2.
  rewrite rE /r'' /r [_.1]/=  -/a -/b -/c -/d.
  by gsplit_Rabs; nra.
have r''2_le : r'' ^ 2 <= r ^ 2 + i ^ 2.
  by rewrite rE /r''; gsplit_Rabs; nra.
have i2_le : i ^ 2 <= r ^ 2 + i ^ 2 by nra.
have B'_le : B' <= (8 + 6 * u + 2 * u ^ 2) * (r ^ 2 + i ^ 2).
  by rewrite /B'; nra.
have u_le_4 : u <= /4.
  have : pow (1 - p) <= pow (-1) by apply: bpow_le; lia.
  suff: pow (-1) <= /2 by rewrite /u; nra.
  rewrite (bpow_opp _ 1).
  apply: Rinv_le; first by lra.
  by rewrite pow1E; apply: beta_ge_2.
suff: B <= (1 + 3 * u) ^ 2 * (r ^ 2 + i ^ 2) by nra.
apply: Rle_trans
    (_ : (1 + 5 * u + /4 * u ^ 2) * (r ^ 2 + i ^ 2) + u ^ 2 * B' <= _).
  by rewrite BE; nra.
apply: Rle_trans
    (_ : (1 + 5 * u + 33 /4 * u ^ 2 + 6 * u ^ 3 + 2 * u ^ 4) * 
          (r ^ 2 + i ^ 2) <= _); first by nra.
suff: (1 + 5 * u + 33 / 4 * u ^ 2 + 6 * u ^ 3 + 2 * u ^ 4)  <=
      (1 + 3 * u) ^ 2 by nra.
by nra.
Qed.

(* Section 4.1 *)

Notation n:= (Zfloor (sqrt (/ 2 * pow (p - 1))) + 1)%Z.

Lemma Hn1 : (1 <= n)%Z.
Proof.
suff: (0 <= Zfloor (sqrt (/2* pow (p -1))))%Z by lia.
by apply/Zfloor_lub/sqrt_ge_0.
Qed.

(*L  4.1 part 1 *)
Lemma n_powp: pow (p - 1) + IZR n <= pow p.
Proof.
have u_gt_0 := u_gt_0.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
have u4: u <= /2 * /2.
  suff: pow (1 - p) <= /2 by rewrite /u; lra.
  apply: Rle_trans (_ : pow (- (1)) <= _); first by apply: bpow_le; lia.
  rewrite bpow_opp pow1E; apply: Rinv_le; first by lra.
  by apply: IZR_le; lia.
apply: Rle_trans  (_ : pow (p - 1) +  (sqrt (/2 * pow (p - 1)) + 1) <= _).
  apply: Rplus_le_compat_l.
  by rewrite plus_IZR; apply/Rplus_le_compat_r/Zfloor_lb.
apply: Rle_trans (_ : pow (p - 1) + pow (p - 1) <= _); last first.
  have ->:  pow (p - 1) + pow (p - 1)  = 2 * pow (p - 1) by lra.
  apply: Rle_trans (_ : IZR beta * pow (p -1) <= _).
    apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
    by apply: IZR_le; lia.
  by rewrite -pow1E -bpow_plus; apply: bpow_le; lia.
apply: Rplus_le_compat_l.
have : 2 * u + sqrt u <= 1.
  apply: Rle_trans (_ : 2 * (/ 2 * / 2) + sqrt (/ 2 * / 2) <= _).
    apply: Rplus_le_compat; first by lra.
    by apply: sqrt_le_1; lra.
  by rewrite sqrt_square; lra.
have ->: pow (p - 1) = / (2 * u).
  have->: (p - 1 = - (1 - p))%Z by lia.
  by rewrite bpow_opp /u; congr Rinv; lra.
move => h.
have: / (2 * u) * (2 * u + sqrt u) <= / (2 * u) * 1.
  apply: Rmult_le_compat_l => //. 
  by rewrite Rinv_mult; lra.
rewrite Rmult_1_r Rmult_plus_distr_l Rinv_l; last by lra.
rewrite Rplus_comm; apply/Rle_trans/Rplus_le_compat_r.
rewrite Rinv_mult.
rewrite -Rmult_assoc sqrt_mult; [|lra|lra].
rewrite sqrt_square; last by lra.
rewrite Rmult_assoc; apply: Rmult_le_compat_l; first lra.
rewrite -[X in X * _]sqrt_square; last by lra.
by rewrite sqrt_mult 1?Rmult_assoc -?sqrt_mult ?Rinv_l ?Rmult_1_r; lra.
Qed.

(* L  4.1 part 2 *)
Lemma bpow7 : 7 <= pow (p - 1) -> pow (p - 1) + 2 * IZR n < pow p.
Proof.
move=> bpowge7.
have u_gt_0 := u_gt_0.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
apply: Rle_lt_trans (_ : pow (p - 1) + 2 * ((sqrt (/2 * pow (p - 1))) + 1) < _).
apply/Rplus_le_compat_l/Rmult_le_compat_l; first by lra.
rewrite plus_IZR;apply/Rplus_le_compat_r/Zfloor_lb.
have-> : pow p = IZR beta * pow (p - 1).
rewrite bpow_plus bpow_opp pow1E [pow p * _]Rmult_comm -Rmult_assoc; field.
  by move/eq_IZR; lia.
have  iuE: pow (p - 1) = / (2 * u).
  have->: (p - 1 = - (1 - p))%Z by lia.
  by rewrite bpow_opp /u; congr Rinv; lra.
rewrite iuE.
apply: (Rmult_lt_reg_r (2 *u)); first by lra.
rewrite [X in X < _](_ : _ = 4 * u * sqrt (/ 2 * / (2 * u)) + 4 * u + 1);
    last by field; lra.
rewrite [X in _ < X](_ : _ = IZR beta); last by field; lra.
rewrite Rinv_mult -?Rmult_assoc 1?sqrt_mult ?sqrt_square //;
    [|lra|lra|lra].
have-> :  4 * / 2 * pow (1 - p) = 4 * u by rewrite /u; lra.
rewrite -[X in 4 * X * _]sqrt_sqrt; last lra.
have->:  4 * (sqrt u * sqrt u) * (/ 2 * sqrt (/ u)) = 2 * sqrt u.
  rewrite sqrt_Rinv; last by lra.
  by field; have := sqrt_lt_R0 u; lra.
suff: 3 * u + sqrt u + / 2 * (1 - IZR beta) <= 0 by lra.
apply: Rle_trans (_ : 3 * u + sqrt u - / 2 <= _).
  apply: Rplus_le_compat_l.
  suff: 2 <= IZR beta by lra.
  by apply: IZR_le; lia.
rewrite -{1}(sqrt_sqrt u); last by lra.
set su := sqrt u.
suff:  6 * (su * su) + 2 * su - 1 <= 0 by lra.
pose v := / 6 * (sqrt 7 - 1).
have vpos: 0 < v.
  rewrite /v; suff: 2 <= sqrt 7 by lra.
  apply: Rsqr_incr_0_var; rewrite ?Rsqr_sqrt /Rsqr; [lra|lra|].
  by apply: sqrt_ge_0.
pose b2m4ac := 4 * 7.
pose x1 := (-2 + 2 * sqrt 7) / 12.
pose x2 := (-2 - 2 * sqrt 7) / 12.

have s7 : sqrt 7 ^ 2 = 7 by rewrite -Rsqr_pow2 Rsqr_sqrt; lra.
have ->:  6 * (su * su) + 2 * su - 1 = 6 * (su - x1) * (su - x2).
  by rewrite /x1 /x2; lra.
rewrite /x1 /x2.
have supos := sqrt_pos u; have s7pos := sqrt_pos 7.
suff: (su - (- 2 + 2 * sqrt 7) / 12) <= 0 by rewrite /su; nra.
suff: sqrt u <= v by rewrite -/su /v; lra.
apply: Rsqr_incr_0_var; last by lra.
rewrite Rsqr_sqrt; last by lra.
apply: Rle_trans (_ : / 14 <= _).
  suff: 2 * u <= / 7 by lra.
  rewrite -(Rinv_inv (2 * u)). 
  by apply: Rinv_le; lra.
rewrite /v /Rsqr.
by nra.
Qed.

(* L 4.1 part 3 *)

Lemma bpow12 (bpowge12 : 12 <= pow (p - 1)) :
  / 2 * pow (p - 1) < Rsqr (IZR n) <= pow (p - 1).
Proof.
have u_gt_0 := u_gt_0.
have iu_gt_0:= Rinv_0_lt_compat _ u_gt_0.
have  iuE: pow (p - 1) = / (2 * u).
  have->: (p - 1 = - (1 - p))%Z by lia.
  rewrite bpow_opp /u; congr Rinv; lra.
split.
  rewrite [X in X < _](_ : _ = Rsqr (sqrt  (/ 2 * pow (p - 1)))); last first.
    by rewrite Rsqr_sqrt //; move:(bpow_ge_0 beta (p -1)); lra.
  apply: Rsqr_incrst_1.
  - by have := Zfloor_ub (sqrt (/ 2 * pow (p - 1))); rewrite -plus_IZR.
  - by apply: sqrt_ge_0.
  apply: IZR_le.
  suff: (0 <= Zfloor (sqrt (/ 2 * pow (p - 1))))%Z by lia.
  by apply/Zfloor_lub/sqrt_ge_0.
rewrite -[X in _ <= X]Rsqr_sqrt; last by apply: bpow_ge_0.
apply: Rsqr_incr_1; first last.
- by apply: sqrt_ge_0.
- by apply: IZR_le; move: Hn1; lia.
rewrite plus_IZR.
apply: Rle_trans (_ : (sqrt (/ 2 * pow (p - 1))) +1 <= _).
apply/Rplus_le_compat_r/Zfloor_lb.
rewrite sqrt_mult; [|lra | apply: bpow_ge_0; lra].
suff: 1 <= (1 - sqrt (/2)) * sqrt (pow (p - 1)) by lra.
apply: Rsqr_incr_0; [|lra|]; last first.
  apply: Rmult_le_pos; last by apply: sqrt_ge_0.
  suff: sqrt (/ 2) <= 1 by lra.
  apply: Rsqr_incr_0; [|apply: sqrt_ge_0 | lra].
  by rewrite Rsqr_sqrt /Rsqr; lra.
rewrite Rsqr_mult Rsqr_sqrt; last by apply: bpow_ge_0.
set den := 1 -sqrt (/ 2).
have denpos: 0 < den.
  suff:  sqrt (/ 2) < 1 by rewrite /den; lra.
  apply: Rsqr_incrst_0; [|apply: sqrt_ge_0|lra].
  by rewrite Rsqr_sqrt /Rsqr; lra.
rewrite /Rsqr Rmult_1_r.
apply: Rmult_le_reg_l (_ :  0 < /(den * den)) _.
  by apply: Rinv_0_lt_compat; nra.
rewrite -Rmult_assoc Rinv_l; last by nra.
rewrite Rmult_1_r Rmult_1_l; apply: Rle_trans bpowge12.
apply: Rmult_le_reg_r (_ : 0 < (den * den)) _; first by nra.
rewrite Rinv_l; last by nra.
have s2 : sqrt 2 ^ 2 = 2 by rewrite  - Rsqr_pow2  Rsqr_sqrt ; lra.
suff: sqrt (/ 2) <=/( 24/ 17) by rewrite /den; nra.
rewrite sqrt_Rinv; last by lra.
apply: Rinv_le; first by lra.
apply: Rsqr_incr_0; [|lra|apply: sqrt_ge_0].
rewrite Rsqr_sqrt /Rsqr; lra.
Qed.
 
Fact rel_err_R h (c : C) (cn0 : (c <> 0)%C) : 
       Rabs ((zh h c c).1 - (c * c)%C.1 )/(Cmod  (c * c)%C) <=  
         Cmod ((zh h c c) / (c * c)%C - 1)%C.
Proof.
have u_gt_0 := u_gt_0.
set z := (c * c)%C.
have zne0: (z <> 0) %C by apply: Cmult_neq_0.
have Cmodz_gt_0 : 0 < Cmod z by apply/Cmod_gt_0.
apply: Rmult_le_reg_r (Cmodz_gt_0) _.
rewrite Rmult_assoc Rinv_l; last by lra.
rewrite -Cmod_mult Rmult_1_r.
set zi := zh h _ _.
rewrite [X in _ <= Cmod X](_ : _ = zi - z)%C; last by field.
apply: Rle_trans (Rmax_Cmod _).
apply: Rle_trans (Rmax_l _ _).
by apply: Req_le; congr Rabs; rewrite /zi /r1.
Qed.

(* b is used for A1/A3 and A2 certificates *)
Section Certificates.

Let b := (pow (p -1 ) + IZR n).

Lemma bpos : 0 < b .
Proof.
suff: 0 <= IZR n by rewrite /b; have := bpow_gt_0 beta (p - 1); lra.
apply: IZR_le.
suff: (0 <= (Zfloor (sqrt (/ 2 * pow (p - 1)))))%Z by lia.
rewrite -Ztrunc_floor; last by apply: sqrt_ge_0.
rewrite -(Ztrunc_IZR 0).
apply/Ztrunc_le/sqrt_ge_0.
Qed.

Lemma Fb: format b.
Proof.
rewrite /b; case : n_powp; last by move->; apply: format_pow.
move=>blt.
pose f := Float beta (beta ^ (p-1) + n)%Z 0.
apply/generic_format_FLX/(FLX_spec _ _ _ f).
  rewrite /b /f /F2R /= Rmult_1_r.
  by rewrite  [RHS] plus_IZR IZR_Zpower //; lia.
rewrite /f /= Z.abs_eq.
  apply: lt_IZR; rewrite plus_IZR !IZR_Zpower //; lia.
apply: le_IZR; rewrite plus_IZR IZR_Zpower; last lia.
apply: Rplus_le_le_0_compat.
- by apply: bpow_ge_0.
rewrite plus_IZR; apply: Rplus_le_le_0_compat; last lra.
apply: IZR_le.
rewrite -Ztrunc_floor; last by apply: sqrt_ge_0.
by rewrite -(Ztrunc_IZR 0);apply/Ztrunc_le/sqrt_ge_0.
Qed.

Section A1_A3_certificates.

(* Warning : in Flocq pred x is an FP only if x is also  an FP ,              *)
(* it's not the case in the paper...                                          *)

Definition pred1 x := Ulp.pred  beta fexp (round beta fexp Zceil x).

Lemma Fpred1 x: format (pred1 x).
Proof. by apply/generic_format_pred/generic_format_round. Qed.

Lemma format_pred1E x (Fx:format x) : pred1 x = Ulp.pred beta fexp x.
Proof. by rewrite /pred1 round_generic//; apply: generic_format_pred. Qed.

Lemma nformat_pred1E x (nFx: ~format x) : pred1  x = (round beta fexp Zfloor x).
Proof. by rewrite /pred1; apply: pred_UP_eq_DN. Qed.

Lemma pred1_lt x (xpos: 0 < x): pred1 x < x.
Proof.
case : (generic_format_EM beta fexp x) => Fx.
  rewrite format_pred1E // pred_eq_pos; last by lra.
  by apply: pred_pos_lt_id; lra.
rewrite nformat_pred1E //.
by case: (round_DN_UP_lt beta fexp x).
Qed.

Lemma pred1_ge_0 x (xpos : 0 < x) : 0 <= pred1 x.
Proof.
apply: pred_ge_0; last by apply: generic_format_round.
by apply: gt_0_round_gt_0_FLX.
Qed.

Lemma pred1_le x (xpos: 0 < x) : x- ulp x <= pred1 x .
Proof.
have pred1lt:= pred1_lt xpos; have pred1_ge_0 := pred1_ge_0 xpos.
case : (generic_format_EM beta fexp x) => Fx.
  apply: Rle_trans (_ : x - ulp (pred1 x) <= _).
    suff:  ulp (pred1 x) <= ulp x by lra.
    by apply: ulp_le; rewrite !Rabs_pos_eq; lra.
  rewrite format_pred1E // pred_eq_pos; last by lra.
  suff: pred_pos beta fexp x + ulp (pred_pos beta fexp x) = x by lra.
  by apply: pred_pos_plus_ulp.
rewrite nformat_pred1E //.
suff: x <= round beta fexp Zfloor x + ulp x by lra.
rewrite -round_UP_DN_ulp//.
suff: round beta fexp Zfloor x < x < round beta fexp Zceil x by lra.
by apply: round_DN_UP_lt.
Qed.

(* pred1 has the good property *)
Fact pred1_max t f  (Ff : format f): f < t -> f <= pred1 t.
Proof.
move=> flt; rewrite /pred1.
apply: pred_ge_gt=>//; first by apply: generic_format_round.
apply: Rlt_le_trans flt _.
case : (generic_format_EM beta fexp t)=> Ft.
  by rewrite round_generic //; lra.
by case: (round_DN_UP_lt beta fexp t) => //; lra.
Qed.

Let a := pred1 (sqrt (/2 * pow (p -1))).

Lemma Fa: format a.
Proof. by apply: Fpred1. Qed.

Fact pred_lt_0 x(xpos:  0 < x) (Fx : format x): 0 < Ulp.pred beta fexp x.
Proof.
have-> : 0 = Ulp.pred beta fexp 0 by rewrite pred_0 ulp_FLX_0; lra.
apply: pred_lt => //.
by apply: generic_format_0.
Qed.

Fact apos: 0 < a.
Proof.
rewrite /a /pred1.
apply: pred_lt_0; last by apply: generic_format_round.
apply/gt_0_round_gt_0_FLX/sqrt_lt_R0.
have := bpow_gt_0 beta (p - 1); lra.
Qed.

(* eq 4.2 *)
Lemma a2ub: Rsqr a < /(4 * u).
Proof.
rewrite /a /u.
have->:   / (4 * (/ 2 * pow (1 - p))) = /2 * pow (p - 1).
  have-> : (p - 1 = -(1 - p))%Z by lia.
  rewrite bpow_opp; field.
  by move:(bpow_gt_0  beta (1-p)); lra.
have apos: 0 < (sqrt (/ 2 * pow (p - 1))).
apply: sqrt_lt_R0; first by have:= bpow_gt_0 beta (p -1);  lra.
apply: Rlt_le_trans (_ : (sqrt (/ 2 * pow (p - 1)))² <= _); last first.
  by rewrite Rsqr_sqrt; have := bpow_ge_0 beta (p -1); lra.
apply: Rsqr_incrst_1; first by apply: pred1_lt.
  by apply: pred1_ge_0.
by apply: sqrt_ge_0.
Qed.

(* eq 4.3 *)
Lemma b2ub : Rsqr b <= Rsqr (/2 * /u + /2 * /(sqrt u) + 1).
Proof.
have u_gt_0 := u_gt_0.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
have supos:= (sqrt_lt_R0 _ u_gt_0).
have isu_gt_0:= (Rinv_0_lt_compat _  supos).
have ppow_pos:= (bpow_gt_0 beta (1 -p)).
apply: Rsqr_incr_1; first last.
+ by lra.
+ by move:bpos; lra.
rewrite Rplus_assoc; apply: Rplus_le_compat.
  rewrite /u; have ->: (1 - p = - (p - 1))%Z by lia.
  rewrite bpow_opp.
  by apply: Req_le; field; move: (bpow_gt_0 beta (p -1)); lra.
rewrite plus_IZR; apply: Rplus_le_compat_r.
apply: (Rle_trans _ (sqrt (/ 2 * pow (p - 1)))).
  by apply: Zfloor_lb.
rewrite -Rinv_mult.
apply: Req_le.
have ->: (p - 1 = - ( 1  - p))%Z by lia.
rewrite bpow_opp -Rinv_mult.
rewrite  sqrt_Rinv; last lra.
congr Rinv; apply: Rsqr_inj; [apply: sqrt_ge_0; lra|lra|].
rewrite Rsqr_sqrt; last lra.
rewrite Rsqr_mult Rsqr_sqrt; last by lra.
rewrite /u /Rsqr; lra.
Qed.

Fact bubE : Rsqr (/ 2 * / u + / 2 * / sqrt u + 1) = 
            / 4 * (/ u) ^ 2 + / 2 * sqrt (/ u) ^ 3 + 5 / 4 * (/ u) +
            sqrt (/ u) + 1.
Proof.
 have u_gt_0 := u_gt_0.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
have supos:= (sqrt_lt_R0 _ u_gt_0).
have isu_gt_0:= (Rinv_0_lt_compat _  supos).
rewrite -sqrt_Rinv; last by lra.
set iu := /u.
have-> : sqrt iu ^ 3 = iu * sqrt (iu).
  rewrite -2!tech_pow_Rmult pow_1 2?Rinv_mult.
  rewrite sqrt_sqrt; first lra.
  by rewrite /iu; lra.
set siu:= sqrt iu.
suff : siu ^ 2 = iu by rewrite /Rsqr; nra.
by rewrite /siu /= Rmult_1_r sqrt_sqrt // /iu ; lra.
Qed.

(* eq 4.4 *)

Let z := ((a + Ci *b) * (a + Ci * b))%C.

Lemma zub : Cmod z < /4 * (Rsqr (/u)) + /2 * (sqrt (/u))^3  + 3/2*(/u) + 
                    sqrt (/u) + 1.
Proof.
have u_gt_0 := u_gt_0.
rewrite cmodz.
apply: (Rlt_le_trans _  (/(4 * u) +  (Rsqr (/2* /u + /2* /(sqrt u) + 1)))).
  apply: Rplus_lt_le_compat.
    by apply: a2ub.
  by apply: b2ub.
rewrite bubE.
apply: Req_le.
rewrite Rinv_mult.
by rewrite Rsqr_pow2; lra.
Qed.

Let s := Rsqr b.
Let s' := RN s.
Let r := Rsqr a - s.
Notation c := (a + Ci * b)%C.
Let r1 := (A1_imult c c)%C.1.
Let f := (pow (p -1) + 2*IZR n) * pow (p-1).
Let g := Rsqr (IZR n).

Fact fpos : 0 < f.
Proof.
rewrite /f.
have ppm1 := bpow_gt_0 beta (p - 1).
apply: Rmult_lt_0_compat; last by lra.
suff: 0 <=  2 * IZR n by lra.
by rewrite -mult_IZR; apply: IZR_le; move: Hn1; lia.
Qed.

Hypothesis beta12 : 12 <= pow (p -1). 

Fact ulpfE : ulp f = pow (p -1).
Proof.
have fpos:= fpos.
have bpm1:= (bpow_gt_0 beta (p -1)).
have npos: 1 <= IZR n  by apply: IZR_le; move: Hn1; lia.
rewrite ulp_neq_0 /cexp /fexp; last lra; congr bpow.
rewrite (mag_unique_pos beta f (2 * p - 1)%Z); first lia.
have->: (2 * p - 1 - 1 = p -1 + (p -1))%Z by lia.
have->:  (2 * p - 1 = (p + (p -1)))%Z by lia.
rewrite !(bpow_plus _ _ (p -1)) /f.
split; [apply: Rmult_le_compat_r; lra| apply: Rmult_lt_compat_r; [lra|]].
by apply: bpow7; lra.
Qed.

Fact magfE : (mag beta f = 2 * p - 1 :>Z)%Z.
Proof.
move: ulpfE; rewrite ulp_neq_0 /cexp /fexp; last by move: fpos; lra.
by move/bpow_inj; lia.
Qed.

Lemma sE : s = f + g.
Proof. rewrite /s /f /g /b /Rsqr; lra. Qed.

Lemma Ff : format f.
Proof.
rewrite /f.
pose ff := Float beta (beta ^ (p -1) + (2 * n))  (p -1).
have mffE : ((Fnum ff) =  beta ^ (p - 1) + 2 * n)%Z by [].
apply/generic_format_FLX/(FLX_spec _ _ _ ff).
  congr Rmult.
  rewrite mffE 2!plus_IZR mult_IZR (IZR_Zpower beta); last by lia.
  congr Rplus; congr Rmult.
  by rewrite plus_IZR.
rewrite /ff Z.abs_eq mffE.
  apply: lt_IZR.
  rewrite plus_IZR mult_IZR  !IZR_Zpower; [|lia|lia].
  by apply: bpow7; lra.
apply: le_IZR; rewrite plus_IZR mult_IZR.
rewrite IZR_Zpower; last by lia.
suff: 0 <= IZR n by have := bpow_ge_0 beta (p - 1); lra.
by apply: IZR_le; move:Hn1; lia.
Qed.

Fact g_lub : /2 * (ulp f) < g <= ulp f.
Proof. by rewrite /g ulpfE; apply: bpow12; apply: beta12. Qed.

(* 4.5*)
Fact rsE : s' = f + ulp f.
Proof.
have Ff := Ff.
have sE := sE.
have fpos := fpos.
have [gl gu] := g_lub.
have Ffpu: format (f + ulp f)  by apply/generic_format_plus_ulp/Ff.
case : gu => gu; last first.
rewrite /s' sE gu; rewrite round_generic //.
have Zff: round beta fexp Zfloor s = f.
  apply: round_DN_eq=>//.
  rewrite succ_eq_pos;  lra.
have Zcf: round beta fexp Zceil s = f + ulp f.
  apply: round_UP_eq=>//.
  rewrite -{1}succ_eq_pos ?pred_succ //; lra.
rewrite /s' round_N_eq_UP //; lra.
Qed.

Fact sb : pow (2 * p - 2) < s' <= pow (2 * p - 1).
Proof.
have fpos:= fpos.
have Ff:= Ff.
rewrite rsE.
split.
  apply: Rle_lt_trans (_ : Rabs f < _).
    have-> : (2 * p - 2  = mag beta  f - 1)%Z by rewrite magfE; lia.
    by apply: bpow_mag_le; lra.
  have uP : 0 < ulp f by rewrite ulpfE; apply: bpow_gt_0.
  by rewrite Rabs_pos_eq; lra.
rewrite -succ_eq_pos; last lra.
apply: succ_le_lt => //; first by apply: format_pow.
rewrite -magfE.
by have := bpow_mag_gt beta f; rewrite Rabs_pos_eq; lra.
Qed.

Fact predsb : pow (2 * p - 2) <= Ulp.pred beta fexp s' < pow (2 * p - 1).
Proof.
have [sbl sbu] := sb.
split.
  apply: pred_ge_gt=>//.
  + by apply: format_pow.
  by apply: generic_format_round.
apply: pred_lt_le=>//.
by move:(bpow_ge_0 beta (2 * p - 2)); lra.
Qed.



(* 4.15a.1*)
Fact s'_gt_0: 0 < s'.
Proof.
apply: (Rlt_trans _ (pow (2 * p - 2))).
  apply: bpow_gt_0.
by move:sb; lra.
Qed.


(* 4.15a.2*)
Fact us': pow (p - 1) <= ulp s'.
Proof.
have hs':=  s'_gt_0.
have sb:= sb.
rewrite ulp_neq_0 /cexp ; try (move: s'_gt_0; lra).
rewrite {1}/fexp.
apply: bpow_le.
suff: (2 * p - 1 <= mag beta s')%Z by lia.
apply: mag_ge_bpow; rewrite Rabs_pos_eq; last by lra.
have-> : (2 * p - 1 - 1 = 2 * p - 2)%Z by lia.
lra.
Qed.

(* 4.15a.3*)
Fact s'nepow: s' <> pow (2 * p - 2 ).
Proof. by move:sb; lra. Qed.

Fact rs'_eps eps : Rabs eps < /2 * pow (p -1) ->
    RN (s' + eps) = s'.
Proof.
move=> eb.
have sb := sb.
have us' := us'.
have predsb := predsb.
have ppm1 : 0 < pow (1 - p) by apply: bpow_gt_0.
have s'_gt_0:= s'_gt_0.
have Fs': format s' by apply: generic_format_round.
have ups : ulp (Ulp.pred beta fexp s') = pow (p -1).
  rewrite ulp_neq_0.
    rewrite /cexp (mag_unique_pos beta _ (2 * p - 1)).
      by rewrite /fexp; congr bpow; lia.
    have -> : (2 * p - 1 - 1 = 2 * p - 2)%Z by lia.
    lra.
  by have := bpow_gt_0 beta (2 * p - 2); lra.
have psE : Ulp.pred beta fexp s' = s' - pow (p -1).
  suff: Ulp.pred beta fexp s' +  ulp (Ulp.pred beta fexp s') = s' by lra.
  by rewrite pred_eq_pos ?pred_pos_plus_ulp //; lra.
case : (Rlt_le_dec 0 eps)=> e'0.
 apply/RN_nearest_lt_half_ulp =>//; first lra.
 split; try lra.
  move: eb; rewrite Rabs_pos_eq;  lra.
case: e'0=>[e'0|->]; last by rewrite Rplus_0_r round_generic.
move:eb; rewrite Rabs_left; last lra; move=> eb.
have Zff : round beta fexp Zfloor (s' + eps) = s' - pow (p - 1).
have->: s' + eps = s' - (- eps) by lra.
   rewrite -psE;  apply: round_DN_minus_eps_pos=>//; lra.
have Zcf : round beta fexp Zceil (s' + eps) = s'.
  rewrite -succ_DN_eq_UP ?Zff -?psE ?succ_pred //.
  move=>Fsa; rewrite round_generic // in Zff;lra.
rewrite round_N_eq_UP // Zff Zcf; lra.
Qed.

(* 4.6*)
Fact r1E : r1 = -s'.
Proof.
have predsb := predsb.
have a2ub := a2ub.
have ppm1 : 0 < pow (1 - p) by apply: bpow_gt_0.
have-> : r1 = RN (Rsqr a - s') 
   by rewrite /r1/A1_imult /= !Rsimp01 /s' /s /Rsqr.
rewrite -Ropp_minus_distr RN_sym //; congr Ropp.
have s'pos : 0 < s'.
  apply: gt_0_round_gt_0_FLX.
  by apply: Rlt_0_sqr; move:bpos; lra.
have Fs': format s' by apply: generic_format_round.
have ups : ulp (Ulp.pred beta fexp s') = pow (p -1).
  rewrite ulp_neq_0.
    rewrite /cexp (mag_unique_pos beta _ (2 * p - 1)).
      by rewrite /fexp; congr bpow; lia.
    by have -> : (2 * p - 1 - 1 = 2 * p - 2)%Z by lia.
  by have := bpow_gt_0 beta (2 * p - 2); lra.
have psE : Ulp.pred beta fexp s' = s' - pow (p -1).
  suff: Ulp.pred beta fexp s' +  ulp (Ulp.pred beta fexp s') = s' by lra.
  by rewrite pred_eq_pos ?pred_pos_plus_ulp //; lra.
have a2lub :  0 < a² < /2* pow (p - 1).
  split; first by apply: Rlt_0_sqr; move: apos; lra.
  apply: (Rlt_le_trans _ (/ (4 * u))); first lra.
  rewrite /u.
  have->: 4 * (/ 2 * pow (1 - p)) = 2 * pow (1 - p) by lra.
  rewrite Rinv_mult.
  rewrite -bpow_opp; have->:  (- (1 - p) = p - 1)%Z by lia.
  by lra.
have Zff : round beta fexp Zfloor (s' - Rsqr a) = s' - pow (p - 1).
  by rewrite -psE; apply: round_DN_minus_eps_pos=>//; lra.
have Zcf : round beta fexp Zceil (s' - Rsqr a) = s'.
  rewrite -succ_DN_eq_UP ?Zff -?psE ?succ_pred //.
  move=>Fsa; rewrite round_generic // in Zff.
  by lra.
by rewrite round_N_eq_UP // Zff Zcf; lra.
Qed.

(* 4.7 *)
Fact errorabE : Rabs (r1 - r) = s' - s + Rsqr a.
Proof.
rewrite r1E /r.
have->: - s' - (a² - s) = - (s' - s + a²) by lra.
rewrite Rabs_Ropp Rabs_pos_eq //.
rewrite rsE sE.
suff: 0 <= ulp f - g by have := Rle_0_sqr a; lra.
move:g_lub; lra.
Qed.

Fact errsE : s' - s = pow (p - 1) - Rsqr (IZR n).
Proof. by rewrite rsE sE ulpfE /g; lra. Qed.

(*4.8*)
Fact serrb : / 4 * / u - / sqrt u -1 <= s' - s.
Proof.
have u_gt_0 := u_gt_0.
have bpp:= bpow_gt_0 beta (1 -p).
rewrite rsE sE ulpfE /g.
rewrite [X in _ <= X](_ : _ = pow (p - 1) - (IZR n)²); last by lra.
apply: Rle_trans (_ : pow (p - 1) - (Rsqr (sqrt (/2 * pow (p -1)) + 1)) <= _).
  apply: Req_le.
  have su: /u = 2 * pow (p -1).
    rewrite /u Rinv_mult -bpow_opp.
    have ->: (- ( 1 - p) = p - 1)%Z by lia.
    by lra.
  rewrite sqrt_mult; [|lra|lra].
  rewrite -sqrt_Rinv //.
  rewrite su sqrt_mult; [|lra|lra].
  rewrite sqrt_Rinv /Rsqr; last lra.
  have Hs : sqrt 2 ^ 2 = 2 by rewrite -Rsqr_pow2 Rsqr_sqrt; lra.
  have Hp : sqrt (pow (p - 1)) ^ 2 = pow (p - 1) 
    by rewrite -Rsqr_pow2 Rsqr_sqrt; lra.
  have Hd : sqrt 2 <> 0   by apply: sqrt2_neq_0; lra.
  by field[Hs Hp].
apply/Rplus_le_compat_l/Ropp_le_contravar/Rsqr_incr_1.
- rewrite plus_IZR.
  by apply/Rplus_le_compat_r/Zfloor_lb.
- by apply: IZR_le; move:Hn1; lia.
set aa:= (_ * _).
suff: 0 <= sqrt aa by lra.
by apply: sqrt_ge_0.
Qed.

(* 4.9 *)
Fact a2lb : /(4 * u) - 1 + u <= Rsqr a.
Proof.
have p1mp : 0 < pow (1 - p) by apply: bpow_gt_0.
have ppm1 : 0 < pow (p - 1) by apply: bpow_gt_0.
have u_gt_0 := u_gt_0.
have apos:= apos.
pose bb:= sqrt (/2 * pow ( p - 1)).
have bbpos: 0 < bb.
  apply: sqrt_lt_R0; move:(bpow_gt_0 beta (p -1)); lra.
have ubble: ulp bb <= bb.
  apply: (Rle_trans _  (Rabs bb  * bpow beta (1 - p))).
    by apply: ulp_FLX_le.
  rewrite Rabs_pos_eq; last by lra.
  rewrite  -{2}(Rmult_1_r bb).
  apply: Rmult_le_compat_l; first by lra.
  have ->: 1 = pow 0 by [].
  apply: bpow_le; lia.
have bble: 0 <= bb - ulp bb <= a.
  split; first lra.
  by apply: pred1_le.
apply: (Rle_trans _ (/2* pow (p - 1) * (Rsqr (1 - 2*u)))).
apply/Req_le/Rminus_diag_uniq; rewrite /Rsqr Rinv_mult.
  have ->: pow ( p - 1) = /2 * /u.
    have->:( p -1 = - (1 -p))%Z by lia.
    rewrite  bpow_opp /u Rinv_mult;  lra.
  by field; lra.
apply: (Rle_trans _ (Rsqr (bb - ulp bb))); last first.
  by apply: Rsqr_le_abs_1; rewrite  !Rabs_pos_eq; lra.
have->: bb - ulp bb = bb * (1 - /bb* ulp bb) by field; lra.
rewrite Rsqr_mult Rsqr_sqrt; last lra.
apply: Rmult_le_compat_l; first lra.
have ulei2: u <= /2.
  rewrite /u; suff: pow ( 1 -p) <= 1 by lra.
  have->:  1 = pow 0 by [].
  apply: bpow_le; lia.
have hbb: / bb * ulp bb <= 1.
  apply: (Rmult_le_reg_l bb); try nra.
  rewrite -Rmult_assoc Rinv_r;  lra.
apply: Rsqr_incr_1; [|lra|lra].
suff: / bb * ulp bb <= 2*u by lra.
apply: (Rmult_le_reg_l bb); first by nra.
rewrite -Rmult_assoc Rinv_r; last by lra.
case:( error_bound_ulp_u bb)=> _ .
rewrite Rabs_pos_eq; lra.
Qed.

(* 4.10 *)
Fact err1_lb : /2 * /u - /(sqrt u) -2 + u <= Rabs (r1 - r).
Proof.
have u_gt_0 := u_gt_0.
rewrite errorabE.
apply: (Rle_trans _ ((/4 * /u -/(sqrt u) - 1) 
                   + (/(4 * u) - 1 + u))); last first.
  by apply: Rplus_le_compat; last apply: a2lb; apply: serrb.
rewrite Rinv_mult; lra.
Qed.

Let z1 := zh one c c .

(* eq 4.1 *)
Fact rel_err1_R : Rabs (r1 - r) / (Cmod z) <=  Cmod (z1 / z - 1)%C.
Proof.
rewrite /r1 /z1 -/(zh  one).
set c := (a + _)%C.
have->: r =  (c  * c)%C.1 by rewrite /r /c /= /s /Rsqr; lra.
apply: rel_err_R.
case;move:apos bpos; lra.
Qed.

(* eq 4.1 *)
 
Fact rel_err_R' h :
  Rabs ((zh h c c).1 - r )/(Cmod z) <=  Cmod ((zh h c c) /z - 1)%C.
Proof.
have u_gt_0 := u_gt_0.
have apos:= apos.
have bpos:= bpos.
have cn0: c <> 0 by case; lra.
have->: r =  (c  * c)%C.1 by rewrite /r /c /= /s /Rsqr; lra.
by apply: rel_err_R.
Qed.

Fact ui2: u <= /2. 
Proof.
rewrite /u; suff: pow (1 - p) <= 1 by lra.
have-> : 1 = pow 0 by [].
apply: bpow_le; lia.
Qed.

Fact su2 : sqrt u ^ 2 = u.
Proof. by rewrite -Rsqr_pow2 Rsqr_sqrt; move:u_gt_0; lra. Qed. 

Fact su3 : sqrt u ^ 3 = u * sqrt u.
Proof. 
by rewrite -[X in X *_]Rsqr_sqrt /Rsqr; first lra; move: u_gt_0;  lra. 
Qed.

Fact su4 : sqrt u ^4 = u^2. 
Proof.  rewrite -[X in X^2]su2; lra. Qed.

Let  phiun:= (2*u -4* ((sqrt u )^ 3) - 8 * u^2+ 4 *u^3).
Let  phiud := (1 + 2 * sqrt u + 6*u + 4 * ((sqrt u )^ 3)+ 4 * u^2).
Let  phiu := phiun/phiud.

Fact phiudpos: 0 < phiud.
Proof. rewrite /phiud; move:(sqrt_ge_0 u) u_gt_0; nra. Qed.



(* Th 4.1 for z1 *)
Theorem rel_err_aux :  phiu * Cmod z <= Rabs (r1 - r).
Proof.
have u_gt_0 := u_gt_0.
have ui2 := ui2.
have apos:= apos.
have bpos:= bpos.
have cn0: c <> 0 by case; lra.
have zne0: (z <> 0) %C by apply: Cmult_neq_0.
have Cmodz_gt_0 : 0 < Cmod z by apply/Cmod_gt_0.
have rel_err1_R:= rel_err1_R.
have  err1_lb :=  err1_lb.
have zub:= zub.
have supos: 0 < sqrt u by apply: sqrt_lt_R0.
have u2pos: 0 < u^2 by nra.
have su2:= su2; have su3:= su3; have su4:= su4.
have phiudpos:= phiudpos.
have phiulb: 2 * u - 8 * u * sqrt u - 4 * u² < phiu.
  rewrite /phiu.
  apply: (Rmult_lt_reg_r phiud)=>//.
  rewrite (Rmult_assoc phiun) Rinv_l ?Rmult_1_r; last by lra.
  suff: 0 < phiun - (2 * u - 8 * u * sqrt u - 4 * u²) * phiud by lra.
  rewrite /phiun /phiud /Rsqr !(su3, su2, su4).
  by nra.
have hu :  0 < 2 * u - 8 * u * sqrt u - 4 * u^2.
  suff:  4 * sqrt u < 1 - 2 * u by nra.
  have->: 4 = sqrt 16 .
    have->: 16 = Rsqr 4 by rewrite /Rsqr ; lra.
    by rewrite sqrt_Rsqr; lra.
  rewrite -sqrt_mult; [|lra|lra].
  apply: Rsqr_incrst_0; [|apply: sqrt_ge_0|lra].
  rewrite Rsqr_sqrt; last by lra.
  suff: 0 <(1 - 2 * u)² - 16 * u by lra.
  rewrite /Rsqr /u.
  set ppm1 := pow (1 - p).
  suff: 0 < ppm1 ^ 2 - 10 * ppm1 + 1 by lra.
  suff:  ppm1 <= / 10 by nra.
  rewrite /ppm1; have ->:(1 - p = - (p - 1))%Z by lia.
  rewrite bpow_opp.
  by apply: Rinv_le; lra.
have phiupos: 0 < phiu.
  apply: Rle_lt_trans phiulb.
  rewrite /Rsqr; lra.
have iphiupos: 0 < /phiu by apply: Rinv_0_lt_compat.
apply: (Rle_trans _ (/ 2 * / u - / sqrt u - 2 + u)) =>//.
apply: (Rmult_le_reg_l (/phiu)); first by lra.
rewrite -Rmult_assoc Rinv_l ?Rmult_1_l; last lra.
have->: /phiu = phiud/phiun.
  rewrite /phiu.
  apply: Rinv_div.
apply: Rle_trans (_ :  / 4 * (/ u)² + / 2 * sqrt (/ u) ^ 3 + 
                      3 / 2 * / u + sqrt (/ u) + 1 <= _); first by lra.
rewrite /phiun /phiud.
have Rle_minus0: forall x y , 0 <= x - y -> y <= x by move=> *; lra.
apply: Rle_minus0; rewrite sqrt_Rinv //.
rewrite /Rsqr.
rewrite [X in _ <= X](_ : _ = 0); first by lra.
field[su3 su2 su4]; nra.
Qed.

(* Th 4.1 for z1 *)
Theorem rel_err1_aux :  phiu * Cmod z <= Rabs (r1 - r).
Proof.
have u_gt_0 := u_gt_0.
have ui2 := ui2.
have apos:= apos.
have bpos:= bpos.
have cn0: c <> 0 by case; lra.
have zne0: (z <> 0) %C by apply: Cmult_neq_0.
have Cmodz_gt_0 : 0 < Cmod z by apply/Cmod_gt_0.
have rel_err1_R:= rel_err1_R.
have  err1_lb :=  err1_lb.
have zub:= zub.
have supos: 0 < sqrt u by apply: sqrt_lt_R0.
have u2pos: 0 < u^2 by nra.
have su2:= su2; have su3:= su3; have su4:= su4.
have phiudpos:= phiudpos.
have phiulb: 2 * u - 8 * u * sqrt u - 4 * u² < phiu.
  rewrite /phiu.
  apply: (Rmult_lt_reg_r phiud)=>//.
  rewrite (Rmult_assoc phiun) Rinv_l ?Rmult_1_r; last by lra.
  suff: 0 < phiun - (2 * u - 8 * u * sqrt u - 4 * u²) * phiud by lra.
  rewrite /phiun /phiud /Rsqr !(su3, su2, su4).
  by nra.
have hu :  0 < 2 * u - 8 * u * sqrt u - 4 * u^2.
  suff:  4 * sqrt u < 1 - 2 * u by nra.
  have->: 4 = sqrt 16 .
    have->: 16 = Rsqr 4 by rewrite /Rsqr ; lra.
    by rewrite sqrt_Rsqr; lra.
  rewrite -sqrt_mult; [|lra|lra].
  apply: Rsqr_incrst_0; [|apply: sqrt_ge_0|lra].
  rewrite Rsqr_sqrt; last by lra.
  suff: 0 < (1 - 2 * u)² - 16 * u by lra.
  rewrite /Rsqr /u.
  set ppm1:= pow (1 - p).
  suff: 0 < ppm1 ^ 2 - 10 * ppm1 + 1 by lra.
  suff:  ppm1 <= /10 by nra.
  rewrite /ppm1; have ->:(1 - p = - ( p - 1))%Z by lia.
  rewrite bpow_opp.
  by apply: Rinv_le; lra.
have phiupos: 0 < phiu.
  apply: Rle_lt_trans phiulb.
  by rewrite /Rsqr; lra.
have iphiupos: 0 < /phiu by apply: Rinv_0_lt_compat.
apply: (Rle_trans _ (/ 2 * / u - / sqrt u - 2 + u)) =>//.
apply: Rmult_le_reg_l iphiupos _.
rewrite -Rmult_assoc Rinv_l ?Rmult_1_l; last by lra.
have->: / phiu = phiud / phiun.
  rewrite /phiu.
  by apply: Rinv_div.
apply: Rle_trans (_ : / 4 * (/ u)² + / 2 * sqrt (/ u) ^ 3 + 
                      3 / 2 * / u + sqrt (/ u) +  1 <= _); first by lra.
rewrite /phiun /phiud.
have Rle_minus0: forall x y , 0 <= x - y -> y <= x by move=>*; lra.
apply: Rle_minus0; rewrite sqrt_Rinv //.
rewrite /Rsqr.
rewrite [X in _ <= X](_ : _ = 0); first by lra.
field[su3 su2 su4]; nra.
Qed.

Theorem rel_err1 : 2 * u - 8 * u * sqrt u - 4 * Rsqr u < Cmod (z1 / z - 1).
Proof.
have u_gt_0 := u_gt_0.
have ui2:= ui2.
have apos:= apos.
have bpos:= bpos.
have cn0: c <> 0 by case; lra.
have zne0: (z <> 0) %C by apply: Cmult_neq_0.
have Cmodz_gt_0 : 0 < Cmod z by apply/Cmod_gt_0.
have rel_err1_R:= rel_err1_R.
have  err1_lb :=  err1_lb.
have zub:= zub.
have phiudpos:=phiudpos.
have su2 :=su2; have su3 := su3; have su4 := su4.
have supos: 0 < sqrt u by apply: sqrt_lt_R0.
have u2pos: 0 < u^2 by nra.
have phiulb: 2 * u - 8 * u * sqrt u - 4 * u² < phiu.
  rewrite /phiu.
  apply: (Rmult_lt_reg_r phiud)=>//.
  rewrite (Rmult_assoc phiun) Rinv_l ?Rmult_1_r; last by lra.
  suff: 0 < phiun - (2 * u - 8 * u * sqrt u - 4 * u²) * phiud by lra.
  by rewrite /phiun /phiud /Rsqr !(su3, su2, su4); nra.
have hu :  0 < 2 * u - 8 * u * sqrt u - 4 * u^2.
  suff:  4 * sqrt u < 1 - 2 * u by nra.
  have->: 4 = sqrt 16 .
    have->: 16 = Rsqr 4 by rewrite /Rsqr ; lra.
    rewrite sqrt_Rsqr; lra.
    rewrite -sqrt_mult; [|lra|lra].
  apply: Rsqr_incrst_0; [|apply: sqrt_ge_0|lra].  
  rewrite Rsqr_sqrt; last by lra.
  suff: 0 < (1 - 2 * u)² - 16 * u by lra.
  rewrite /Rsqr /u.
  set ppm1:= pow (1 - p).
  suff: 0 < ppm1 ^ 2 - 10 * ppm1 + 1 by lra.
  suff: ppm1 <= / 10 by nra.
  rewrite /ppm1; have ->:(1 - p = - (p - 1))%Z by lia.
  rewrite bpow_opp.
  by apply: Rinv_le; lra.
have phiupos: 0 < phiu.
  apply: (Rle_lt_trans _ _ _ _ phiulb).
  rewrite /Rsqr; lra.
have iphiupos: 0 < /phiu by apply: Rinv_0_lt_compat.
clear - phiulb rel_err1_R   Cmodz_gt_0 Hbeta2 Hp2 choice_sym s' f g beta12.
apply: (Rlt_le_trans _ phiu)=>//.
apply: (Rle_trans _  (Rabs (r1 - r) / Cmod z)); last lra.
apply: (Rmult_le_reg_r (Cmod z))=>//.
rewrite (Rmult_assoc (Rabs _)) Rinv_l ?Rmult_1_r; last lra.
by apply: rel_err1_aux.
Qed.

Let r3 := (A3_imult  c c)%C.1.

Fact r3Er1 : r3 = r1.
Proof.
have Fb:= Fb.
pose e := s' - s.
have-> : r3 = RN (r1 + e).
  rewrite /r1 /r3 /A1_imult /A3_imult /= !Rsimp01 /kahan.
  congr RN.
  rewrite -Ropp_mult_distr_l RN_sym //.
  congr Rplus.
  have->:(- (b * b) - - RN (b * b)) = RN (b * b) - (b * b) by lra.
  rewrite /e /s' -/(Rsqr b) /s round_generic//.
 by apply: Mult_error.mult_error_FLX.
by rewrite r1E /e -[RHS]RN_sym //; congr (RN _); lra.
Qed.

Let z3 := zh three c c .

Theorem rel_err3 : 2 * u -8 * u * (sqrt u) - 4 * Rsqr u < Cmod (z3 / z - 1)%C.
Proof.
have u_gt_0 := u_gt_0.
have ui2:= ui2.
have apos:= apos.
have bpos:= bpos.
have cn0: c <> 0 by case; lra.
have zne0: (z <> 0) %C by apply: Cmult_neq_0.
have Cmodz_gt_0 : 0 < Cmod z by apply/Cmod_gt_0.
have rel_err1_R:= rel_err_R three.
have  err1_lb :=  err1_lb.
have zub:= zub.
have phiudpos:=phiudpos.
have su2 :=su2; have su3 := su3; have su4 := su4.
have supos: 0 < sqrt u by apply: sqrt_lt_R0.
have u2pos: 0 < u^2 by nra.
have phiulb: 2 * u - 8 * u * sqrt u - 4 * u² < phiu.
  rewrite /phiu.
  apply: (Rmult_lt_reg_r phiud)=>//.
  rewrite (Rmult_assoc phiun) Rinv_l ?Rmult_1_r; last by lra.
  suff: 0 < phiun - (2 * u - 8 * u * sqrt u - 4 * u²) * phiud by lra.
  by rewrite /phiun /phiud /Rsqr !(su3, su2, su4); nra.
have hu :  0 < 2 * u - 8 * u * sqrt u - 4 * u^2.
  suff:  4 * sqrt u < 1 - 2 * u by nra.
  have->: 4 = sqrt 16 .
    have->: 16 = Rsqr 4 by rewrite /Rsqr ; lra.
    by rewrite sqrt_Rsqr; lra.
  rewrite -sqrt_mult; [|lra|lra].
  apply: Rsqr_incrst_0; [|apply: sqrt_ge_0|lra].
  rewrite Rsqr_sqrt; last by lra.
  suff: 0 < (1 - 2 * u)² - 16 * u by lra.
  rewrite /Rsqr /u.
  set ppm1:= pow (1 - p).
  suff: 0 < ppm1 ^ 2 - 10 * ppm1 + 1 by lra.
  suff: ppm1 <= / 10 by nra.
  rewrite /ppm1; have ->:(1 - p = - ( p - 1))%Z by lia.
  rewrite bpow_opp.
  by apply: Rinv_le; lra.
have phiupos: 0 < phiu.
  apply: Rle_lt_trans phiulb.
  by rewrite /Rsqr; lra.
have iphiupos: 0 < /phiu by apply: Rinv_0_lt_compat.
clear - phiulb rel_err1_R r1 r3 Cmodz_gt_0 Hbeta2 Hp2 
       choice_sym s' f g beta12 z1 r.
apply: Rlt_le_trans phiulb _.
apply: (Rle_trans _  (Rabs (r3 - r) / Cmod z)).
  apply: (Rmult_le_reg_r (Cmod z))=>//.
  rewrite (Rmult_assoc (Rabs _)) Rinv_l ?Rmult_1_r; last by lra.
  rewrite r3Er1.
  by apply: rel_err1_aux.
move: rel_err_R'.
rewrite /r3 /z3 -/(zh three).
apply.
Qed.

(* Lemma 4.2 *)
Notation RN_lt_pos := (RN_lt_pos beta Hp2 choice).

End A1_A3_certificates.

Section A2_certificate.

Local Notation RD := (round beta fexp Zfloor).

Let a :=  RD ((1 - u) * sqrt (/2 * pow (p -1))).

Lemma Fa2 : format a.
Proof. by  apply: generic_format_round. Qed.

Fact a2pos : 0 < a.
Proof.
apply: gt_0_round_gt_0_FLX.
have: 0 < sqrt (/2 * pow( p - 1)).
  apply: sqrt_lt_R0; move :(bpow_gt_0 beta (p -1)); lra.
move:u_lt_1; nra.
Qed.
 
Notation c := (a + Ci *b)%C.

Let z := (c * c)%C.

Fact cmodz2 : Cmod z = Rsqr a + Rsqr b.
Proof.
rewrite /z Cmod_mult /Cmod sqrt_sqrt /Rsqr /=; nra.
Qed.

(* 4.12*)
Fact a2_ub : Rsqr a <= /4* Rsqr (1 -u) * /u.
Proof. 
have u_gt_0 := u_gt_0.
have u_lt_1 := u_lt_1.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
have supos:= (sqrt_lt_R0 _ u_gt_0).
have isu_gt_0:= (Rinv_0_lt_compat _  supos).
have apos:= a2pos.
have->:  /4 * (1 - u)² * / u = Rsqr (/2 * ( 1 - u) * (sqrt (/u))).
  rewrite !Rsqr_mult Rsqr_sqrt /Rsqr; lra.
rewrite sqrt_Rinv; last lra.
apply: Rsqr_incr_1;  try nra.
rewrite /a.
set aa :=(_ *_).
apply: (Rle_trans _ aa).
  by case: (round_DN_UP_le beta Hp2 aa).
apply: Req_le.
rewrite /aa.
have->: (pow (p - 1)) = /2 * /u.
  have ->: (p - 1 = - (1 - p))%Z by lia.
  have hp:= (bpow_gt_0 beta (1 - p)).
  rewrite /u bpow_opp; field; lra.
rewrite -Rmult_assoc sqrt_mult; [|lra|lra].
rewrite (sqrt_Rsqr (/2)); last by lra.
rewrite sqrt_Rinv; try field; lra.
Qed.

(* 4.13 *)
Fact z_ub : Cmod z <= /4 * /(Rsqr u) + /2 * /( u * sqrt u) + 3/2 * /u + 
                      /(sqrt u) + /2 + /4 * u.
Proof.
have u_gt_0 := u_gt_0.
(* have u_lt_1 := u_lt_1. *)
(* have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0). *)
have supos:= (sqrt_lt_R0 _ u_gt_0).
(* have isu_gt_0:= (Rinv_0_lt_compat _  supos). *)
(* have apos:= a2pos. *)
have su2:= su2; have su3:= su3.
apply: (Rle_trans _ (/4 * Rsqr (1 -u) * /u +  (/4 * (/u)^2 +
                     /2 * sqrt (/u)^3 + 5/4 * (/u) + sqrt (/u) + 1))).
  rewrite cmodz2; apply: Rplus_le_compat.
    by apply: a2_ub.
  by rewrite -bubE; apply: b2ub.
by apply/Req_le/Rminus_diag_uniq; rewrite /Rsqr Rinv_mult ?sqrt_Rinv;
    [field [su2]; nra|lra].
Qed.

Notation s := (Rsqr b).
Notation s' := (RN s).
Notation e1 := (Rsqr a - RN (Rsqr a)).
(* Notation e2 := (s - s'). *)
Notation e2 := (s' - s).
Notation r := z.1.
Fact rE : r = Rsqr a - s.
Proof. by rewrite /= /Rsqr ;  lra. Qed.

Notation  z2 := (zh two c c) .
Notation r2 := z2.1.
Let e' := (RN (e1 + e2)).

(* 4.14 *)
Fact r2E : r2 =  RN ((RN (RN (Rsqr a) - s')) + e').
Proof.
rewrite /= /cht /e' !Rsimp01 -/(Rsqr a).
have->: - b * b = - (Rsqr b) by rewrite /Rsqr; lra.
rewrite !RN_sym //.
have->:  (- s - - s') =  s' - s  by lra.
congr  (RN (_ + _)).
congr RN.
rewrite round_generic.
congr Rplus; rewrite round_generic //.
apply: Mult_error.mult_error_FLX; apply: Fb.
rewrite - Ropp_minus_distr; 
  apply/generic_format_opp/Mult_error.mult_error_FLX; apply: Fa2.
Qed.

Hypothesis beta12 : 12 <= pow (p -1). 

Fact altb : Rsqr a < Rsqr b.
Proof.
have upos:= u_gt_0.
have ult1:= u_lt_1.
have apos:= a2pos.
have bpos:= bpos.
have bpm1:= (bpow_gt_0 beta (p - 1)).
apply/Rsqr_lt_abs_1; rewrite !Rabs_pos_eq;[|lra|lra].
rewrite /a /b.
set x := (_ *_).
apply/(Rle_lt_trans _ x); first by case:(round_DN_UP_le beta Hp2 x).
apply/(Rle_lt_trans _ (sqrt (/ 2 * pow (p - 1)))).
  rewrite -[X in _<= X]Rmult_1_l; apply/Rmult_le_compat_r; last lra.
  by apply/sqrt_ge_0.
suff: sqrt (/ 2 * pow (p - 1)) < IZR n by lra.
apply/Rsqr_incrst_0; first last.
+ by apply/IZR_le; move:Hn1; lia.
+ by apply/sqrt_ge_0.
rewrite [X in X <_]Rsqr_sqrt; try lra.
by case: bpow12.
Qed.


Fact errs_int : s' - s = IZR (beta ^ (p - 1) - n * n).
Proof.
rewrite errsE // /Rsqr -mult_IZR -{1}IZR_Zpower -?minus_IZR //; lia.
Qed.

(* 4.15b*)
Fact errs_b : 0 < s' - s </2 * pow (p - 1).
Proof.
have u_gt_0 := u_gt_0.
have u_lt_1 := u_lt_1.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
have supos:= (sqrt_lt_R0 _ u_gt_0).
have isu_gt_0:= (Rinv_0_lt_compat _  supos).
have serrb:=serrb.
have su3:= su3.
suff e2_pos: 0 < e2 by split=>//; rewrite errsE; move: bpow12; lra.
apply: Rlt_le_trans (_ : / 4 * / u - / sqrt u - 1 <= _); last by lra.
rewrite [X in _ < X](_ : _ =  (-4 * u * sqrt u - 4 * u + sqrt u) / 
                              (4 * u * sqrt u)); last by field; lra.
apply: Rdiv_lt_0_compat; last by nra.
have->:  -4 * u * sqrt u - 4 * u + sqrt u = 
         sqrt u * (- 4 * u - 4 * sqrt u + 1) by nra.
suff: 12 * u + 12 * sqrt u < 3 by nra.
rewrite /u.
have i12: pow (1 -p ) <= /12.
  have->:( 1 -p = -(p -1))%Z by lia.
  rewrite bpow_opp.
  by apply: Rinv_le_contravar; lra.
suff: 12 * sqrt (/ 2 * pow (1 - p)) < 3 - /2 by lra.
suff: sqrt (/ 2 * pow (1 - p)) < 5/24 by lra.
apply: Rsqr_incrst_0; [|apply: sqrt_ge_0|lra].
rewrite Rsqr_sqrt /Rsqr; first by lra.
by have := bpow_ge_0 beta (1 -p); lra.
Qed.


Let  y := /2 * pow (p - 1).

Fact yb : pow (p - 2) <= y < pow (p - 1).
Proof.
split; last by rewrite /y;move:(bpow_gt_0 beta (p -1)); lra.
have->: (p - 2  = ( Z.opp 1   + (p - 1)))%Z by lia.
rewrite /y bpow_plus; apply: Rmult_le_compat_r.
  by apply: bpow_ge_0. rewrite bpow_opp pow1E; apply: Rinv_le; try lra.
by apply: IZR_le; lia.
Qed.

Fact ypos: 0 < y.
Proof. by  rewrite /y; move:(bpow_gt_0 beta (p - 2)); lra. Qed.

Fact uyE : ulp y = pow (- (1)).
Proof.
have yb := yb.
rewrite /y ulp_neq_0 /cexp /fexp ?(mag_unique_pos _ _ (p - 1)); 
  last by lra.
  by congr bpow; lia.
by have -> : (p - 1 - 1 = p - 2)%Z by lia.
Qed.

Fact uyle2 : ulp y <= /2.
Proof.
rewrite uyE bpow_opp pow1E; apply: Rinv_le; first by lra.
by apply: IZR_le; lia.
Qed.

(* 4.16 *)
Fact RNa2b: RN (Rsqr a) < /2 * pow (p - 1).
Proof.
have u_gt_0 := u_gt_0.
have u_lt_1 := u_lt_1.
have a2_Ub := a2_ub.
set x := /2 * pow (p - 1) -/2 + /4 * u.
have xE:  x = / 4 * (1 - u)² * / u.    
  rewrite /x /Rsqr; apply: Rminus_diag_uniq.
  suff H : 16 * pow (p - 1) * u = 8 by field[H]; lra.
  rewrite /u.
  have ->: (p - 1 = - ( 1 - p))%Z by lia.
  by rewrite bpow_opp; field; move : (bpow_gt_0 beta (1 - p)); lra.
have h1: RN (Rsqr a) <= RN x by apply: round_le; lra.
have yb := yb; have uyE := uyE; have uyle2:= uyle2 ; have ypos:= ypos.
have h2: x + /2 * ulp (y) <= /2 * pow (p - 1) - /4 + u / 4 < y.
  by rewrite /x; split; first lra; rewrite /y ; lra.
apply: RN_lt_pos=> //; try (rewrite /Rsqr ;  lra).  
  by apply: Rle_0_sqr.
rewrite -/y; lra.
Qed.

Fact e1b : Rabs e1 <= /4 * Rsqr (1 - u).
Proof.
have u_gt_0 := u_gt_0.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
have supos:= (sqrt_lt_R0 _ u_gt_0).
have a2_ub:= a2_ub.
apply/(Rle_trans _ (u * (Rsqr a))); rewrite /e1.
  have->: (a² + - RN a²) = - (RN a² - a²) by lra.
  rewrite Rabs_Ropp -[X in _ <= _*X]Rabs_pos_eq; last by apply/Rle_0_sqr.
  move:(error_bound_ulp_u (Rsqr a)); lra.
by apply/(Rmult_le_reg_l (/u)); rewrite // -Rmult_assoc Rinv_l ?Rmult_1_l; nra.
Qed.

Fact e2b : Rabs e2 <= /2 * pow (p -1) - /2.
Proof.
have p_ge_0: (0 <= p - 1)%Z by lia.
have errs_b:= errs_b.
rewrite Rabs_pos_eq; try lra.
suff : 2 * e2 <= pow (p - 1) - 1 by lra.
rewrite errs_int; set m:= (beta ^ (p - 1) - n * n)%Z.
rewrite -IZR_Zpower // -mult_IZR -minus_IZR; apply/IZR_le.
suff:  (2 * m < beta ^ (p - 1))%Z by lia.
apply/lt_IZR; rewrite IZR_Zpower // mult_IZR  /m -errs_int; lra.
Qed.


(* 4.17*)
Fact eb : Rabs e' < /2 * pow (p -1).
Proof.
apply: (Rle_lt_trans _ (RN (Rabs e1 + Rabs e2))).
  by rewrite /e' -RN_abs //; apply/round_le/Rabs_triang.
pose x' := /2 * pow (p - 1)  -/4 - /2*u + /4* (Rsqr u).
have x'lb: (Rabs e1 + Rabs e2) <= x'.
  rewrite /x' ; try lra.
  move: e1b e2b; rewrite /Rsqr; nra.
apply/(Rle_lt_trans _ (RN x')).
  by apply/round_le.
have yb:=yb; have uyE := uyE; have uyle2:= uyle2 ; have ypos:= ypos.
suff:  x' < y - /2 * ulp y.
  apply: RN_lt_pos => //; try lra.
  by move: (Rabs_pos e1) (Rabs_pos e2); lra.
have x'E:  x'= / 2 * pow (p - 1) - / 4 - / 2 * u + / 4 * u² by [].
suff:  - / 4 - / 2 * u + / 4 * u² <  - / 2 * ulp y.
  rewrite {2}/y; lra.
suff: 0 <  2*u - (Rsqr u) by lra.
have u_gt_0 := u_gt_0.
have u_lt_1 := u_lt_1.
rewrite  /Rsqr; nra.
Qed.

Fact Ra2s': RN (RN (Rsqr a) - s') = -s'.
Proof.
have->: (RN a² - s') = - (s' - (RN (Rsqr a))) by lra.
rewrite RN_sym //.
congr Ropp.
have apos := a2pos.
have predsb := predsb.
have RNa2b := RNa2b.
have ppm1 : 0 < pow (1 - p) by apply: bpow_gt_0.
have s'_gt_0:= s'_gt_0.
have sb := sb.
have Fs': format s' by apply: generic_format_round.
have ups : ulp (Ulp.pred beta fexp s') = pow (p -1).
  rewrite ulp_neq_0.
    rewrite /cexp (mag_unique_pos beta _ (2 * p - 1)).
      by rewrite /fexp; congr bpow; lia.
    have -> : (2 * p - 1 - 1 = 2 * p - 2)%Z by lia.
    lra.
  by have := bpow_gt_0 beta (2 * p - 2); lra.
have psE : Ulp.pred beta fexp s' = s' - pow (p -1).
  suff: Ulp.pred beta fexp s' +  ulp (Ulp.pred beta fexp s') = s' by lra.
  by rewrite pred_eq_pos ?pred_pos_plus_ulp //; lra.
have a2lub :  0 < RN a² < /2* pow (p - 1).
  split=>//.
  by apply/gt_0_round_gt_0_FLX/Rsqr_pos_lt; lra.
have Zff : round beta fexp Zfloor (s' - (RN (Rsqr a))) = s' - pow (p - 1).
  by rewrite -psE; apply: round_DN_minus_eps_pos=>//; lra.
have Zcf : round beta fexp Zceil (s' - RN (Rsqr a)) = s'.
  rewrite -succ_DN_eq_UP ?Zff -?psE ?succ_pred //.
  move=>Fsa; rewrite round_generic // in Zff.
  by lra.
by rewrite round_N_eq_UP // Zff Zcf; lra.
Qed.

(* needs some cleaning *)

Fact r2e' : r2 = -s'.
Proof.
rewrite r2E Ra2s'.
have->: (-s'  + e') = - (s' - e') by lra.
rewrite RN_sym //.
congr Ropp.
have eb:= eb.
have predsb := predsb.
have ppm1 : 0 < pow (1 - p) by apply: bpow_gt_0.
have s'_gt_0:= (s'_gt_0 beta12).
have sb := sb.
have Fs': format s' by apply: generic_format_round.
have ups : ulp (Ulp.pred beta fexp s') = pow (p -1).
  rewrite ulp_neq_0.
    rewrite /cexp (mag_unique_pos beta _ (2 * p - 1)).
      by rewrite /fexp; congr bpow; lia.
    have -> : (2 * p - 1 - 1 = 2 * p - 2)%Z by lia.
    lra.
  by have := bpow_gt_0 beta (2 * p - 2); lra.
have psE : Ulp.pred beta fexp s' = s' - pow (p -1).
  suff: Ulp.pred beta fexp s' +  ulp (Ulp.pred beta fexp s') = s' by lra.
  by rewrite pred_eq_pos ?pred_pos_plus_ulp //; lra.
case : (Rlt_le_dec 0 e')=> e'0; last first.
case: e'0=>[e'0|->]; last by rewrite Rminus_0_r round_generic.
  have->: s' - e' = s' + (-e') by lra.
apply/RN_nearest_lt_half_ulp =>//; first lra.
split; try lra.
move: eb.
rewrite Rabs_left //.
move:us';lra.

have Zff : round beta fexp Zfloor (s' - e') = s' - pow (p - 1).
   rewrite -psE; apply: round_DN_minus_eps_pos=>//.
move:eb; rewrite Rabs_right;lra.

have Zcf : round beta fexp Zceil (s' - e') = s'.
  rewrite -succ_DN_eq_UP ?Zff -?psE ?succ_pred //.
  move=>Fsa; rewrite round_generic // in Zff.
move:eb; rewrite Rabs_right;lra.
rewrite round_N_eq_UP // Zff Zcf.
move:eb; rewrite Rabs_right;lra.
Qed.

Fact err2E : Rabs (r2 -r) = s' - s + Rsqr a.
Proof.
rewrite r2e' rE.
have->:  (- s' - (a² - s)) = -( s' - s + Rsqr a) by lra.
rewrite Rabs_Ropp Rabs_pos_eq //.
have errs_b := errs_b.
suff: 0 <= Rsqr a by lra.
apply/Rle_0_sqr.
Qed.


Fact a2b : /4 * /u - 3/2 + 13/4 * u - 3 * u^2 + u^3 <= Rsqr a.
Proof.
have apos:= a2pos.
have u_gt_0 := u_gt_0.
have ui2:= ui2.
have ui2': 0 <= 1 - 2*u by nra.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
have p1mp: 0 < pow(1 -p) by apply/bpow_gt_0.
have ppm1: 0 < pow(p - 1) by apply/bpow_gt_0.

apply/(Rle_trans _ ((1 -2*u)^2 * ( 1 - u)^2 * (/2 * pow (p - 1)))).
  apply/Req_le/Rminus_diag_uniq; rewrite /u.
  have->: (p - 1 = - ( 1 - p))%Z by lia.
  by rewrite bpow_opp;field; lra.

pose aa:= (sqrt (/ 2 * pow (p - 1))).
have aaE : aa = sqrt (/ 2 * pow (p - 1)) by [].

have aapos: 0 < aa.
rewrite /aa; apply/sqrt_lt_R0; lra.

have->: (/ 2 * pow (p - 1)) = Rsqr aa.
  rewrite /aa Rsqr_sqrt //; lra.
rewrite -!Rsqr_pow2 -!Rsqr_mult.

apply/Rsqr_incr_1;try nra; last by apply/Rmult_le_pos; nra.
rewrite /a -/aa.
rewrite Rmult_assoc.
set aaa:= ((1 -u) * _).

have aaapos : 0 <= aaa.
rewrite /aaa; apply/Rmult_le_pos; try nra.

suff: -2 * u * aaa <= RD aaa - aaa by lra.

apply/(Rle_trans _ (- (ulp aaa))); last first.
have :   Rabs (RD aaa -aaa) <= ulp aaa.
apply/error_le_ulp.
 move/Rabs_le_inv; lra.
suff : ulp aaa <= 2 * u * aaa by lra.
rewrite -{2}(Rabs_pos_eq aaa) // Rmult_comm  /u -(Rmult_assoc 2) Rinv_r;
    last lra.
by rewrite Rmult_1_l; apply/ulp_FLX_le.
Qed.

(* Th 4.2 *)
Fact  ui24 : u <= /24.
Proof.
move: beta12 ; rewrite /u.
  have-> : (p - 1 = - ( 1 - p))%Z by lia.
  rewrite bpow_opp.
  move/(Rmult_le_compat_r (pow (1 - p))); rewrite Rinv_l; 
   move: (bpow_gt_0 beta (1 -p)); lra.
Qed.

Fact su24 : sqrt u <= /2* sqrt 6.
Proof.
have u_gt_0 := u_gt_0.
have ui24:= ui24.
apply/Rsqr_incr_0_var; try (move :(sqrt_pos 6); nra).
rewrite Rsqr_mult !Rsqr_sqrt /Rsqr; lra.
Qed.

Lemma rel_err2_r : 
  (2 * u - 8 * u * sqrt u - 6 * u²) * Cmod z < Rabs (r2 - r).
Proof.
have u_gt_0 := u_gt_0.
have supos: 0 < sqrt u by apply: sqrt_lt_R0.
have p1mp: 0 < pow(1 -p) by apply/bpow_gt_0.
have ui24:= ui24.
have su24:= su24.
(* have ui2:= ui2. *)
have apos:= a2pos.
have bpos:= bpos.
have cn0: c <> 0 by case; lra.
have zne0: (z <> 0) %C by apply: Cmult_neq_0.
have Cmodz_gt_0 : 0 < Cmod z by apply/Cmod_gt_0.
have rel_err1_R:= rel_err_R two.
have  err1_lb :=  err1_lb.
have zub:= z_ub.
have phiudpos:=phiudpos.
have su2 :=su2; have su3 := su3; have su4 := su4.
have u2pos: 0 < u^2 by nra.
(* clear u2pos phiudpos su2 err1_lb  rel_err1_R Cmodz_gt_0 zne0 cn0 
         su24 apos bpos. *)
have lb_pos:   0 < 2 * u - 8 * u * sqrt u - 6 * u² by rewrite /Rsqr; nra.
rewrite err2E.
apply/(Rlt_le_trans _ (/ 4 * / u - / sqrt u - 1  +
       ( /4* /u -3/2 + 13/4 * u -3 * u^2 + u^3)));
        last by move: a2b serrb; lra.
have ->: /4 * /u - /(sqrt u)  - 1 +
   (/4 * /u - 3/2 + 13/4 * u - 3 * u^2 + u^3)=
   /2 * /u - /(sqrt u) -5/2 +13/4*u -3*u^2 + u^3  by rewrite /Rsqr ; field; lra.
apply/(Rle_lt_trans _ ( (2 * u - 8 * u * sqrt u - 6 * u²)*
          (/ 4 * / u² + / 2 * / (u * sqrt u) + 3 / 2 * / u +
           / sqrt u + / 2 + / 4 * u))).
 apply/Rmult_le_compat_l; lra.
apply/Rlt_0_minus.
rewrite /Rsqr; field_simplify[su2 su3 su4]; last lra. 
apply/(Rmult_lt_reg_r (8 * sqrt u * u ^ 2)); first  nra.
rewrite Rmult_0_l (Rmult_assoc _ (/ _)) Rinv_l ?Rmult_1_r; last nra.
have->:   20 * sqrt u * u ^ 5 - 4 * sqrt u * u ^ 4 +
  154 * sqrt u * u ^ 3 + 16 * u ^ 5 + 80 * u ^ 4 +
  104 * u ^ 3 =
  (20 * sqrt u * u ^ 2 - 4 * sqrt u * u + 154 * sqrt u  +
   16 * u ^ 2 + 80 * u  + 104 ) * u^3  by field.
apply/Rmult_lt_0_compat; nra.
Qed.

Theorem rel_err2 : 2 * u - 8 * u * (sqrt u) - 6 * Rsqr u < Cmod (z2/z - 1)%C.
Proof.
have u_gt_0 := u_gt_0.
have iu_gt_0:= (Rinv_0_lt_compat _  u_gt_0).
have p1mp: 0 < pow(1 -p) by apply/bpow_gt_0.
have ui24: u <= /24.
  move: beta12 ; rewrite /u.
  have-> : (p -1 = - ( 1 - p))%Z by lia.
  rewrite bpow_opp.
  move/(Rmult_le_compat_r (pow (1 - p))); rewrite Rinv_l; nra.
have su24: sqrt u <= /2* sqrt 6.
apply/Rsqr_incr_0_var; move :(sqrt_pos 6);  try nra.
rewrite Rsqr_mult !Rsqr_sqrt /Rsqr; try lra.
have ui2:= ui2.
have supos: 0 < sqrt u by apply: sqrt_lt_R0.
have apos:= a2pos.
have bpos:= bpos.
have cn0: c <> 0 by case; lra.
have zne0: (z <> 0) %C by apply: Cmult_neq_0.
have Cmodz_gt_0 : 0 < Cmod z by apply/Cmod_gt_0.
have rel_err1_R:= rel_err_R two.
have  err1_lb :=  err1_lb.
have zub:= z_ub.
have phiudpos:=phiudpos.
have su2 :=su2; have su3 := su3; have su4 := su4.
have u2pos: 0 < u^2 by nra.
have lb_pos:   0 < 2 * u - 8 * u * sqrt u - 6 * u² by rewrite /Rsqr; nra.
apply: (Rlt_le_trans _  (Rabs (r2 - r) / Cmod z)); last first.
  by apply/rel_err_R; case; lra.
apply: (Rmult_lt_reg_r (Cmod z))=>//.
  rewrite (Rmult_assoc (Rabs _)) Rinv_l ?Rmult_1_r; last by lra.
apply/rel_err2_r.
Qed.

(* Corollary 4.1 *)
Let z0 := zh zero c c .
Let r' := cht a a  (-b) b.
Let r0 := z0.1.

Theorem rel_err0 : 2*u -8*u*(sqrt u) - 6 * Rsqr u < Cmod (z0/z - 1)%C
                   /\  2*u -8*u*(sqrt u) - 6 * Rsqr u < Rabs (r'/r -1) .
Proof.
have apos:= a2pos.
have bpos:= bpos.
have cn0: c <> 0 by case; lra.
have zne0: (z <> 0) %C by apply: Cmult_neq_0.
have Cmodz_gt_0 : 0 < Cmod z by apply/Cmod_gt_0.
have r2Er0:  r2 = r0 by rewrite r2e' /r0 /z0 /= !Rsimp01 Ra2s'.
have r'Er2: r' = r2 by rewrite /= !Rsimp01 /r'. 
have h1:  2 * u - 8 * u * sqrt u - 6 * u² < Rabs (r0 - r) / Cmod z.
  apply/(Rmult_lt_reg_r (Cmod z))=>//.
  rewrite (Rmult_assoc (Rabs _)) Rinv_l ?Rmult_1_r; last by lra.
  rewrite -r2Er0.
  by apply/rel_err2_r.
split.
  apply/(Rlt_le_trans _  (Rabs (r0 -r) / Cmod  z ))=>//.
  by apply/rel_err_R.
rewrite r'Er2.
apply/(Rlt_le_trans _ ( Rabs (r0 - r) / Cmod z))=>//.
rewrite r2Er0.
have rn0: r <> 0.
  rewrite /r /z /= !Rsimp01.
suff: Rsqr a < Rsqr b by  rewrite /Rsqr; lra.
  by apply/altb.
have-> :r0 / r - 1= (r0 -r)/r by field.
rewrite Rabs_mult.
apply/Rmult_le_compat_l; first by apply/Rabs_pos.
rewrite Rabs_inv //.
apply/Rinv_le; first by apply/Rabs_pos_lt.
rewrite /r cmodz2 /= !Rsimp01.
split_Rabs; rewrite /Rsqr; nra.
Qed.
End  A2_certificate.
End Certificates.

Section AppendixA.
Let P1 h x y  :=  zh h x y = zh h  y x.

Let P2 h x := (zh h x (Cconj x)).2 = 0.

Fact P_0 x y : P1 zero x y /\ P2 zero x.
Proof.
split.
  apply/pair_equal_spec.
  by rewrite  !(Rmult_comm x.1 ) !(Rmult_comm x.2 ) Rplus_comm.
by rewrite /P2 /= -Ropp_mult_distr_r RN_sym //
          (Rmult_comm x.1 ) Rplus_opp_l round_0.
Qed.

Fact P_2 x y : P1 two x y /\ P2 two x.
Proof.
split.
  rewrite /P1  /= /A2_imult /cht -!Ropp_mult_distr_l  !RN_sym //.
  apply/pair_equal_spec; split.
    by rewrite  !(Rmult_comm x.1 ) !(Rmult_comm x.2 ).
  congr (RN (_ + _)); congr RN.
    by rewrite  !(Rmult_comm x.2 ) !(Rmult_comm x.1) Rplus_comm.
  by rewrite Rplus_comm !(Rmult_comm x.2) (Rmult_comm x.1).
rewrite /P2  /= /A2_imult.
set a := x.1 ; set d := x.2.
rewrite /cht  -Ropp_mult_distr_r !RN_sym // (Rmult_comm a).
have->: - RN (d * a) + RN (d * a) = 0 by lra.
rewrite round_0 Rplus_0_l.
have-> : (- (d * a) - - RN (d * a)) = - ((d * a) -  RN (d * a)) by lra.
by rewrite RN_sym // Rplus_opp_l !round_0.
Qed.

Fact P_3 x  : P2 three  x.
Proof.
rewrite /P2  /= /A3_imult /kahan  -Ropp_mult_distr_r 
        -Ropp_minus_distr RN_sym //.
have ->: - (x.1 * x.2) + RN (x.2 * x.1) = RN (x.2 * x.1) - x.2 * x.1 by lra.
have ->: 0 = RN 0 by rewrite round_0.
congr RN; lra.
Qed.

Let a := pow (p -1).
Let b := a + 1.
Let c := a + 1.
Let d := pow p -  IZR (Ztrunc ((IZR beta + 1)/2)). 

Fact dEeven : Zeven.Zeven beta -> d = pow p - (IZR beta)/2.
Proof.
case/Zeven.Zeven_ex=> z betaE.
have z1: (1 <= z)%Z by lia.
rewrite /d.
congr (_ - _); rewrite betaE mult_IZR.
suff ->:  Ztrunc ((2 * IZR z + 1) / 2) = z by lra.
have ->: ((2 * IZR z + 1) / 2) = IZR z + /2 by field.
rewrite Ztrunc_floor; last first.
  suff : 0 < IZR z by lra.
  apply/IZR_lt; lia.
by apply/Zfloor_imp; rewrite plus_IZR; lra.
Qed.

Fact dEodd : Zeven.Zodd beta -> d = pow p - (IZR beta +1)/2.
Proof.
case/Zeven.Zodd_ex=> z betaE.
have z1: (1 <= z)%Z by lia.
rewrite /d.
congr (_ - _); rewrite betaE plus_IZR mult_IZR.
have  ->:   ((2 * IZR z + 1 + 1) / 2) = IZR z + 1 by lra.
rewrite Ztrunc_floor; last first.
  suff : 0 < IZR z by lra.
  apply/IZR_lt; lia.
rewrite -plus_IZR.
congr IZR.
by apply/Zfloor_imp;  rewrite (plus_IZR ( z + 1)); lra.
Qed.

(* Fact exampleA1           *)

End AppendixA.
End IFloat.

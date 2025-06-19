(* Copyright (c)  Inria. All rights reserved. *)
From HB Require Import structures.
From Stdlib Require Import Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot Complex.
Require Import Rmore Cmore Rstruct.

Delimit Scope ring_scope with RR.
Delimit Scope R_scope with R.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

HB.instance Definition _ :=  Choice.on C.

Lemma Cplus_opp_l c : (- c + c = 0)%C.
Proof. by ring. Qed.

HB.instance Definition _ := GRing.isZmodule.Build C
  Cplus_assoc Cplus_comm Cplus_0_l Cplus_opp_l.

Fact C1_neq_0 : 1 != 0 :> C.
Proof. by apply/eqP=> /RtoC_inj; lra. Qed.

HB.instance Definition _ := GRing.Nmodule_isNzSemiRing.Build C
  Cmult_assoc Cmult_1_l Cmult_1_r
  Cmult_plus_distr_r Cmult_plus_distr_l Cmult_0_l Cmult_0_r C1_neq_0.

HB.instance Definition _ := GRing.PzRing_hasCommutativeMul.Build C
  Cmult_comm.

Import Monoid.

HB.instance Definition _ :=
  isComLaw.Build C 0%R Cplus Cplus_assoc Cplus_comm Cplus_0_l.

HB.instance Definition _ := isMulLaw.Build C 0%R Cmult Cmult_0_l Cmult_0_r.

HB.instance Definition _ := isAddLaw.Build C Cmult Cplus
  Cmult_plus_distr_r Cmult_plus_distr_l.

Definition Cinvx (c : C) : C := if (c != 0%RR) then / c else c.

Definition unit_C (c : C) := c != 0%RR.

Lemma CmultRinvx : {in unit_C, left_inverse 1%RR Cinvx Cmult}.
Proof.
move=> c; rewrite -topredE /unit_C /Cinvx => /= cNZ /=.
by rewrite cNZ Cinv_l //; apply/eqP.
Qed.

Lemma CinvxRmult : {in unit_C, right_inverse 1%RR Cinvx Cmult}.
Proof.
move=> c; rewrite -topredE /unit_C /Cinvx => /= cNZ /=.
by rewrite cNZ Cinv_r //; apply/eqP.
Qed.

Lemma intro_unit_C (x y : C) : (y * x = 1)%RR /\ (x * y = 1)%RR -> unit_C x.
Proof.
move=> [yxE1 xyE1]; apply/eqP=> xZ.
case/eqP: C1_neq_0.
by rewrite -[(RtoC 1)]yxE1 xZ /GRing.mul /= Cmult_0_r.
Qed.

Lemma Cinvx_out : {in predC unit_C, Cinvx =1 id}.
Proof. by move=> x; rewrite inE /= /Cinvx -if_neg => ->. Qed.

HB.instance Definition _ := GRing.NzRing_hasMulInverse.Build C
  CmultRinvx CinvxRmult intro_unit_C Cinvx_out.

Lemma C_idomainMixin (x y : C) : (x * y = 0)%RR -> (x == 0%RR) || (y == 0%RR).
Proof.
(do 2 case: (boolP (_ == _))=> // /eqP)=> yNZ xNZ xyZ.
by case: (Cmult_neq_0 _ _ xNZ yNZ).
Qed.

HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build C C_idomainMixin.

Lemma C_field_axiom : GRing.field_axiom C.
Proof. by done. Qed.

HB.instance Definition _ := 
  GRing.UnitRing_isField.Build C C_field_axiom.

(* Big Op *)

Lemma sum_Cconj (A : Type) (l : seq A) (P : A -> bool) (f : A -> C) : 
 (Cconj (\sum_(i <- l | P i) (f i)) = \sum_(i <- l | P i) (Cconj (f i)))%RR.
Proof.
elim: l => /= [|a l IH]; first by rewrite !big_nil Cconj0.
rewrite !big_cons; case: (P a) => //.
by rewrite Cplus_conj IH.
Qed.

Lemma mulC_sumr (I : Type) (r : seq I) 
         (P : I -> bool) (F : I -> C) (x : C) : 
  (x * (\sum_(i <- r | P i) F i)%RR)%C = (\sum_(i <- r | P i) (x * F i)%C)%RR.
Proof. by apply: (@GRing.mulr_sumr (GRing.PzRing.clone _ C)). Qed.

Lemma sum_RtoC (A : Type) (l : seq A) (P : A -> bool) (f : A -> R) : 
 (RtoC (\sum_(i <- l | P i) (f i)) = \sum_(i <- l | P i) (RtoC (f i)))%RR.
Proof.
elim: l => /= [|a l IH]; first by rewrite !big_nil.
rewrite !big_cons; case: (P a) => //.
by rewrite RtoC_plus IH.
Qed.

(* Algebraic operatopns on sequences of complex numbers                       *)

Definition get (T : pzRingType) (l : seq T) (i : nat) :=
  (l `_ i)%RR.

Definition cadd (n : nat) (l1  l2 : seq C) : seq C := 
  [seq (get l1 i + get l2 i)%C | i : 'I_(2 ^ n)].

Lemma size_cadd n l1 l2 : size (cadd n l1 l2) = (2 ^ n)%N.
Proof. by rewrite size_map size_enum_ord. Qed.

Lemma get_cadd (n : nat) (l1 l2 : seq C) i : 
  (i < 2 ^ n)%N -> get (cadd n l1 l2) i = (get l1 i + get l2 i)%C.
Proof.
move=> iL2n; have C0 : (0 < 2 ^ n)%N by rewrite expn_gt0.
by rewrite /get /cadd (nth_map (Ordinal C0)) ?nth_enum_ord // size_enum_ord.
Qed.

Definition copp (n : nat) (l : seq C) : seq C := 
  [seq  (- get l i)%C | i : 'I_(2 ^ n)].

Lemma size_copp n l : size (copp n l) = (2 ^ n)%N.
Proof. by rewrite size_map size_enum_ord. Qed.

Lemma get_copp (n : nat) (l : seq C) i : 
  (i < 2 ^ n)%N -> get (copp n l) i = (- get l i)%C.
Proof.
move=> iL2n; have C0 : (0 < 2 ^ n)%N by rewrite expn_gt0.
by rewrite /get /cadd (nth_map (Ordinal C0)) ?nth_enum_ord // size_enum_ord.
Qed.

Definition csub (n : nat) (l1  l2 : seq C) : seq C := 
  [seq (get l1 i - get l2 i)%C | i : 'I_(2 ^ n)].

Lemma size_csub n l1 l2 : size (csub n l1 l2) = (2 ^ n)%N.
Proof. by rewrite size_map size_enum_ord. Qed.

Lemma get_csub (n : nat) (l1 l2 : seq C) i : 
  (i < 2 ^ n)%N -> get (csub n l1 l2) i = (get l1 i - get l2 i)%C.
Proof.
move=> iL2n; have C0 : (0 < 2 ^ n)%N by rewrite expn_gt0.
by rewrite /get /csub (nth_map (Ordinal C0)) ?nth_enum_ord // size_enum_ord.
Qed.

Lemma csub_add_opp n l1 l2 : csub n l1 l2 = cadd n l1 (copp n l2).
Proof. by apply/eq_in_map => i _; rewrite get_copp. Qed.

(* Properties of norm of sequence of complex numbers *)

Definition cnorm2 (n : nat) (l : seq C) : R := 
  (\sum_(i < 2 ^ n) ((Cmod (get l i)) ^ 2)%R)%RR.

Lemma cnorm2_ge0 n l : 0 <= cnorm2 n l.
Proof.
rewrite /cnorm2; elim: index_enum => [|a l1 IH].
  by rewrite big_nil /GRing.zero /=; lra.
rewrite big_cons.
have := pow2_ge_0 (Cmod (get l a)).
rewrite /GRing.add /= in IH *.
by nra.
Qed.

Definition cnorm (n : nat) (l : seq C) : R := sqrt (cnorm2 n l).

Lemma cnorm2_eq0 n l : 
   cnorm2 n l = 0 <-> forall i, (i < 2 ^ n)%N -> get l i = C0.
Proof.
(split; rewrite /cnorm2); last first.
  elim: (2 ^ _)%N => [|n1 IH H]; first by rewrite big_ord0.
  rewrite big_ord_recr /= H // IH //=.
    by rewrite Cmod_0 /GRing.add /=; lra.
  by move=> i Hi; apply: H; rewrite ltnS ltnW.
move=> H i; move: H. 
elim: (2 ^ _)%N => // n1 IH; rewrite big_ord_recr /=.
set x := (_  * (_ * 1))%R; set s := (\sum_(_ < n1) _)%RR in IH *.
rewrite /GRing.add /= ltnS => H1 H2.
have x_pos : 0 <= x by rewrite /x; nra.
have s_pos : 0 <= s.
  rewrite /s; elim: {H1 H2 x s IH x_pos}n1 => [|n1 IH].
    by rewrite big_ord0 /GRing.zero /=; lra.
  by rewrite big_ord_recr /= /GRing.add /= in IH *; nra.
have x_eq0 : x = 0 by lra.
have s_eq0 : s = 0 by lra.
case: (ltngtP i n1) H2 => // [iLn1 _|-> _]; first by apply: IH.
by apply: Cmod_eq_0; move: x_eq0; rewrite /x; nra.
Qed.

Lemma cnorm_eq0 n l : cnorm2 n l = 0 <-> cnorm n l = 0.
Proof.
split; first by rewrite /cnorm => ->; rewrite sqrt_0.
by apply: sqrt_eq_0; apply: cnorm2_ge0.
Qed.

Definition cprod (n : nat) (l1  l2 : seq C) : C := 
 (\sum_(i < 2 ^ n) ((get l1 i) * (Cconj (get l2 i)))%C)%RR.

Lemma cprod_conj n l1 l2 :  Cconj (cprod n l1 l2) = cprod n l2 l1.
Proof.
rewrite sum_Cconj; apply: eq_bigr => i _.
by rewrite Cmult_conj Cmult_comm Cconj_conj.
Qed.

Lemma cprodNl n l1 l2 : cprod n (copp n l1) l2 = (- (cprod n l1 l2))%C.
Proof.
rewrite /cprod.
under eq_bigr do rewrite get_copp // -Copp_mult_distr_l.
by rewrite GRing.sumrN.
Qed.

Lemma cprodNr n l1 l2 : cprod n l1 (copp n l2) = (- (cprod n l1 l2))%C.
Proof.
rewrite /cprod.
under eq_bigr do rewrite get_copp // Copp_conj -Copp_mult_distr_r.
by rewrite GRing.sumrN.
Qed.

Lemma cprodDl n l1 l2 l3 :
  cprod n (cadd n l1 l2) l3 = (cprod n l1 l3 + cprod n l2 l3)%C.
Proof.
rewrite /cprod.
under eq_bigr do rewrite get_cadd // Cmult_plus_distr_r.
by rewrite big_split.
Qed.

Lemma cprodDr n l1 l2 l3 :
  cprod n l1 (cadd n l2 l3) = (cprod n l1 l2 + cprod n l1 l3)%C.
Proof.
rewrite /cprod.
under eq_bigr do rewrite get_cadd // Cplus_conj Cmult_plus_distr_l.
by rewrite big_split.
Qed.

Lemma cprod_0l n l1 l2 : cnorm n l1 = 0 -> cprod n l1 l2 = 0.
Proof.
move/cnorm_eq0/cnorm2_eq0 => Hi.
by apply: big1 => i _; rewrite Hi // Csimp01.
Qed.

Lemma cprod_0r n l1 l2 : cnorm n l2 = 0 -> cprod n l1 l2 = 0.
Proof.
move/cnorm_eq0/cnorm2_eq0 => Hi.
by apply: big1 => i _; rewrite Hi ?Cconj0 // Csimp01.
Qed.

Lemma norm2E n l : cnorm2 n l = cprod n l l :> C.
Proof. by rewrite sum_RtoC; apply: eq_bigr => i _; rewrite Cmod2_conj. Qed.

Lemma Cauchy_schwartz n l1 l2 : Cmod (cprod n l1 l2) <= cnorm n l1 * cnorm n l2.
Proof.
rewrite -(sqrt_pow2 _ (Cmod_ge_0 _)) -sqrt_mult_alt; last by apply: cnorm2_ge0.
apply: sqrt_le_1_alt.
set c := cprod _ _ _; set a := cnorm2 _ _; set b := cnorm2 _ _.
have b_ge0 : 0 <= b by apply: cnorm2_ge0.
have [b_eq0|b_gt0]: b = 0 \/ 0 < b by lra.
  rewrite /c cprod_0r.
    by rewrite b_eq0 !Csimp01 !Rsimp01 pow_i; try lra; lia.
  by apply/cnorm_eq0.
pose d : R := (\sum_(i < 2 ^ n) 
              ((Cmod (b * (get l1 i) - c * (get l2 i))) ^ 2)%R)%RR.
have d_pos : 0 <= d by apply: sumR_ge0 => i _ _; apply: pow2_ge_0.
suff: d = (b ^ 2 * a - b * Cmod c ^ 2)%R by nra.
apply: RtoC_inj.
rewrite RtoC_minus sum_RtoC.
under eq_bigr do rewrite Cmod2_conj Cminus_conj !Cmult_conj !RtoC_conj.
under eq_bigr do rewrite Cmult_minus_distr_r !Cmult_minus_distr_l.
rewrite !GRing.sumrB.
set x1 : C := (\sum_ _ _)%RR; set x2 : C := (\sum_ _ _)%RR.
set x3 : C := (\sum_ _ _)%RR; set x4 : C := (\sum_ _ _)%RR.
set x5 := RtoC (b * _).
have  <- : x1 = (b ^ 2 * a)%R.
  rewrite  mulR_sumr [RHS]sum_RtoC.
  apply: eq_bigr => i _.
  by rewrite RtoC_mult Cmod2_conj RtoC_pow; ring.
have -> : x2 = x5.
  rewrite /x5 RtoC_mult Cmod2_conj.
  rewrite /x2.
  under eq_bigr do rewrite -Cmult_assoc.
  rewrite -mulC_sumr.
  under eq_bigr => i _ do
    (rewrite (_ : (get l1 i * (Cconj c * Cconj (get l2 i)) =
                  Cconj c * (get l1 i * Cconj (get l2 i)))%C); [|ring]).
  rewrite -mulC_sumr.
  by congr (_ * _)%C; rewrite Cmult_comm.
have  -> : x3 = x5.
  rewrite /x5 /x3 RtoC_mult Cmod2_conj.
  under eq_bigr do rewrite -Cmult_assoc.
  rewrite -mulC_sumr.
  under eq_bigr => i _ do
    (rewrite (_ : (get l2 i * (b * Cconj (get l1 i)) =
                  b * (get l2 i * Cconj (get l1 i)))%C); [|ring]).
  rewrite -mulC_sumr cprod_conj !Cmult_assoc.
  by congr (_ * _)%C; ring.
have  -> : x4 = x5.
  rewrite /x4 /x5 RtoC_mult Cmod2_conj.
  under eq_bigr do rewrite -Cmult_assoc.
  rewrite -mulC_sumr.
  under eq_bigr => i _ do
    (rewrite (_ : (get l2 i * (Cconj c * Cconj (get l2 i)) =
                  Cconj c * (get l2 i * Cconj (get l2 i)))%C); [|ring]).
  rewrite -mulC_sumr /b norm2E [RHS]Cmult_comm !Cmult_assoc.
  by congr (_ * _)%C; ring.
rewrite -[(x1 - x5 - (x5 - x5))%RR]/(x1 - x5 - (x5 - x5))%C.
by ring.
Qed.

Lemma cnorm2E n l : cnorm2 n l = ((cnorm n l) ^ 2)%R.
Proof. by rewrite pow2_sqrt //; apply: cnorm2_ge0. Qed.

Lemma cnorm_ge0 n l : 0 <= cnorm n l.
Proof. by apply: sqrt_ge_0. Qed.

Lemma cnormD n l1 l2 : cnorm n (cadd n l1 l2) <= cnorm n l1 + cnorm n l2.
Proof.
rewrite -[X in _ <= X]sqrt_pow2; last first.
  by have := cnorm_ge0 n l1; have := cnorm_ge0 n l2; lra.
apply: sqrt_le_1_alt.
have -> : (cnorm2 n (cadd n l1 l2) = 
           cnorm n l2 ^ 2 + (cnorm n l1 ^ 2 + 2 * Re (cprod n l1 l2)))%R.
  apply: RtoC_inj.
  rewrite norm2E cprodDl !cprodDr -!norm2E -[cprod n l2 l1]cprod_conj.
  rewrite !cnorm2E Cplus_assoc Cplus_comm -Cplus_assoc.
  rewrite (_ : cprod _ _ _ + _ = 2 * Re(cprod n l1 l2))%C; last first.
    by rewrite re_alt; field.
  by rewrite -RtoC_mult -!RtoC_plus.
suff :  Re (cprod n l1 l2) <= cnorm n l1 * cnorm n l2 by lra.
apply: Rle_trans (Rle_abs _) _.
apply: Rle_trans (re_le_Cmod _) _.
apply: Cauchy_schwartz.
Qed.

Lemma cnormB n l1 l2 l3 : 
  cnorm n (csub n l1 l2) <= cnorm n (csub n l1 l3) + cnorm n (csub n l3 l2).
Proof.
suff -> : csub n l1 l2 = cadd n (csub n l1 l3) (csub n l3 l2) by apply: cnormD.
by apply/eq_in_map => i _; rewrite !get_csub //; ring.
Qed.

Lemma natr_RtoC_INR n : (n%:R)%RR = RtoC (INR n).
Proof.
elim: n => // n IH.
by rewrite S_INR [(_.+1%:R)%RR](natrD _ 1) IH addrC RtoC_plus.
Qed.

Lemma natrCS_neq0 n : (n.+1%:R != 0 :> C)%RR.
Proof.
rewrite !natr_RtoC_INR S_INR; apply/eqP => /eqP/andP[/eqP /= nE _]. 
by have := pos_INR n;lra.
Qed.

Lemma Cchar m n : (m%:R = n%:R :> C -> m = n)%RR.
Proof.
elim: m n => [|m IH] [|n] // /eqP.
- by rewrite eq_sym (negPf (natrCS_neq0 n)).
- by rewrite (negPf (natrCS_neq0 m)).
rewrite !natrS => /eqP Hs.
by rewrite (IH n) // -[LHS](addKr (RtoC 1)) Hs addKr.
Qed.

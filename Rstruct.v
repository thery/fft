(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

From HB Require Import structures.
From Stdlib Require Import Rdefinitions Raxioms RIneq Rbasic_fun Zwf.
From Stdlib Require Import Epsilon FunctionalExtensionality Ranalysis1 Rsqrt_def.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice bigop.
From mathcomp Require Import archimedean ssrnum ssralg fintype poly mxpoly.
From mathcomp Require Import div order.
From Stdlib Require Import Rtrigo1 Reals Lra Reals Psatz.
Require Import Coquelicot.Coquelicot.

Delimit Scope ring_scope with RR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Local Open Scope R_scope.

Lemma Req_EM_T (r1 r2 : R) : {r1 = r2} + {r1 <> r2}.
Proof.
case: (total_order_T r1 r2) => [[r1Lr2 | <-] | r1Gr2].
- by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {2}r1Er2.
- by left.
by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {1}r1Er2.
Qed.

Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 is left _ then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof.
by move=> r1 r2; rewrite /eqr; case: Req_EM_T=> H; apply: (iffP idP).
Qed.

HB.instance Definition _ := hasDecEq.Build R eqrP.

Fact inhR : inhabited R.
Proof. exact: (inhabits 0). Qed.

Definition pickR (P : pred R) (n : nat) :=
  let x := epsilon inhR P in if P x then Some x else None.

Fact pickR_some P n x : pickR P n = Some x -> P x.
Proof. by rewrite /pickR; case: (boolP (P _)) => // Px [<-]. Qed.

Fact pickR_ex (P : pred R) :
  (exists x : R, P x) -> exists n, pickR P n.
Proof. by rewrite /pickR; move=> /(epsilon_spec inhR)->; exists 0%nat. Qed.

Fact pickR_ext (P Q : pred R) : P =1 Q -> pickR P =1 pickR Q.
Proof.
move=> PEQ n; rewrite /pickR; set u := epsilon _ _; set v := epsilon _ _.
suff->: u = v by rewrite PEQ.
by congr epsilon; apply: functional_extensionality=> x; rewrite PEQ.
Qed.

HB.instance Definition _ := hasChoice.Build R pickR_some pickR_ex pickR_ext.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

HB.instance Definition _ := GRing.isZmodule.Build R
  RplusA Rplus_comm Rplus_0_l Rplus_opp_l.

Fact RmultA : associative (Rmult).
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Fact R1_neq_0 : R1 != R0.
Proof. by apply/eqP/R1_neq_R0. Qed.

HB.instance Definition _ := GRing.Nmodule_isNzSemiRing.Build R
  RmultA Rmult_1_l Rmult_1_r
  Rmult_plus_distr_r Rmult_plus_distr_l Rmult_0_l Rmult_0_r R1_neq_0.

HB.instance Definition _ := GRing.PzRing_hasCommutativeMul.Build R
  Rmult_comm.

Import Monoid.

HB.instance Definition _ := isComLaw.Build R 0%R Rplus RplusA Rplus_comm Rplus_0_l.

HB.instance Definition _ := isComLaw.Build R 1%R Rmult RmultA Rmult_comm Rmult_1_l.

HB.instance Definition _ := isMulLaw.Build R 0%R Rmult Rmult_0_l Rmult_0_r.

HB.instance Definition _ := isAddLaw.Build R Rmult Rplus
  Rmult_plus_distr_r Rmult_plus_distr_l.

Definition Rinvx r := if (r != 0) then / r else r.

Definition unit_R r := r != 0.

Lemma RmultRinvx : {in unit_R, left_inverse 1 Rinvx Rmult}.
Proof.
move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_l //; apply/eqP.
Qed.

Lemma RinvxRmult : {in unit_R, right_inverse 1 Rinvx Rmult}.
Proof.
move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_r //; apply/eqP.
Qed.

Lemma intro_unit_R x y : y * x = R1 /\ x * y = R1 -> unit_R x.
Proof.
move=> [yxE1 xyE1]; apply/eqP=> xZ.
by case/eqP: R1_neq_0; rewrite -yxE1 xZ Rmult_0_r.
Qed.

Lemma Rinvx_out : {in predC unit_R, Rinvx =1 id}.
Proof. by move=> x; rewrite inE /= /Rinvx -if_neg => ->. Qed.

HB.instance Definition _ := GRing.NzRing_hasMulInverse.Build R
  RmultRinvx RinvxRmult intro_unit_R Rinvx_out.

Lemma R_idomainMixin x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
(do 2 case: (boolP (_ == _))=> // /eqP)=> yNZ xNZ xyZ.
by case: (Rmult_integral_contrapositive_currified _ _ xNZ yNZ).
Qed.

HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build R R_idomainMixin.

Lemma R_field_axiom : GRing.field_axiom R.
Proof. by done. Qed.

HB.instance Definition _ := 
  GRing.UnitRing_isField.Build R R_field_axiom.

(** Reflect the order on the reals to bool *)

Definition Rleb r1 r2 := if Rle_dec r1 r2 is left _ then true else false.
Definition Rltb r1 r2 := Rleb r1 r2 && (r1 != r2).
Definition Rgeb r1 r2 := Rleb r2 r1.
Definition Rgtb r1 r2 := Rltb r2 r1.

Lemma RlebP r1 r2 : reflect (r1 <= r2) (Rleb r1 r2).
Proof. by rewrite /Rleb; apply: (iffP idP); case: Rle_dec. Qed.

Lemma RltbP r1 r2 : reflect (r1 < r2) (Rltb r1 r2).
Proof.
rewrite /Rltb /Rleb; apply: (iffP idP); case: Rle_dec=> //=.
- by case=> // r1Er2 /eqP[].
- by move=> _ r1Lr2; apply/eqP/Rlt_not_eq.
by move=> Nr1Lr2 r1Lr2; case: Nr1Lr2; left.
Qed.

Lemma RgebP r1 r2 : reflect (r1 >= r2) (Rgeb r1 r2).
Proof.
rewrite /Rgeb /Rleb; apply: (iffP idP); case: Rle_dec=> //=.
  by move=> r2Lr1 _; apply: Rle_ge.
by move=> Nr2Lr1 r1Gr2; case: Nr2Lr1; apply: Rge_le.
Qed.

Lemma RgtbP r1 r2 : reflect (r1 > r2) (Rgtb r1 r2).
Proof.
rewrite /Rleb; apply: (iffP idP) => r1Hr2; first by apply: Rlt_gt; apply/RltbP.
by apply/RltbP; apply: Rgt_lt.
Qed.

(*
Ltac toR := rewrite /GRing.add /GRing.opp /GRing.zero /GRing.mul /GRing.inv
  /GRing.one //=.
*)

Section ssreal_struct.
 
Import GRing.Theory.
Import Num.Theory.
Import Num.Def.
 
Local Open Scope R_scope.
 
Lemma Rleb_norm_add x y : Rleb (Rabs (x + y)) (Rabs x + Rabs y).
Proof. by apply/RlebP/Rabs_triang. Qed.
 
Lemma addr_Rgtb0 x y : Rltb 0 x -> Rltb 0 y -> Rltb 0 (x + y).
Proof. by move/RltbP=> Hx /RltbP Hy; apply/RltbP/Rplus_lt_0_compat. Qed.
 
Lemma Rnorm0_eq0 x : Rabs x = 0 -> x = 0.
Proof. by move=> H; case: (x == 0) /eqP=> // /Rabs_no_R0. Qed.
 
Lemma Rleb_leVge x y : Rleb 0 x -> Rleb 0 y -> (Rleb x y) || (Rleb y x).
Proof.
move/RlebP=> Hx /RlebP Hy; case: (Rlt_le_dec x y).
by move/Rlt_le/RlebP=> ->.
by move/RlebP=> ->; rewrite orbT.
Qed.
 
Lemma RnormM : {morph Rabs : x y / x * y}.
exact: Rabs_mult. Qed.
 
Lemma Rleb_def x y : (Rleb x y) = (Rabs (y - x) == y - x).
apply/(sameP (RlebP x y))/(iffP idP)=> [/eqP H| /Rle_minus H].
  apply: Rminus_le; rewrite -Ropp_minus_distr.
  apply/Rge_le/Ropp_0_le_ge_contravar.
  by rewrite -H; apply: Rabs_pos.
apply/eqP/Rabs_pos_eq.
rewrite -Ropp_minus_distr.
by apply/Ropp_0_ge_le_contravar/Rle_ge.
Qed.
 
Lemma Rltb_def x y : (Rltb x y) = (y != x) && (Rleb x y).
apply/(sameP (RltbP x y))/(iffP idP).
  case/andP=> /eqP H /RlebP/Rle_not_gt H2.
  by case: (Rtotal_order x y)=> // [][] // /esym.
move=> H; apply/andP; split; [apply/eqP|apply/RlebP].
  exact: Rgt_not_eq.
exact: Rlt_le.
Qed.
 
 HB.instance Definition _ :=  
  Num.IntegralDomain_isNumRing.Build R Rleb_norm_add
     addr_Rgtb0 Rnorm0_eq0 Rleb_leVge RnormM Rleb_def Rltb_def.

Fact Rle_0D x y : Rleb 0 x -> Rleb 0 y -> Rleb 0 (x + y).
Proof. by move=> /RlebP Hx /RlebP Hy; apply/RlebP; lra. Qed.

Fact Rle_0M x y : Rleb 0 x -> Rleb 0 y -> Rleb 0 (x * y).
Proof. by move=> /RlebP Hx /RlebP Hy; apply/RlebP; nra. Qed.

Fact Rle_0A x : Rleb 0 x -> Rleb x 0 -> x = 0.
Proof. by move=> /RlebP Hx /RlebP Hy; nra. Qed.

Fact Rle_0B x y : Rleb 0 (y - x) = Rleb x y.
Proof. by apply/RlebP/RlebP; lra. Qed.

Fact Rle_0X x : Rleb 0 x || Rleb x 0.
Proof.
case: (Rle_dec 0 x) => [/RlebP->//|H]; rewrite orbC.
by have /RlebP-> : x <= 0 by lra.
Qed.

Fact Rle0_Rabs x : Rleb 0 x -> Rabs x = x.
Proof. by move=> /RlebP/Rabs_pos_eq. Qed.

Fact Rlt_def x y : (Rltb x y) = (y != x) && (Rleb x y).
Proof.
apply/RltbP/andP => [xLy|[/eqP yDx /RlebP xLy]]; last by lra.
  split; first by apply/eqP; lra.
by apply/RlebP; lra.
Qed.

Lemma Rleb_refl : reflexive Rleb.
Proof. by move=> a;apply/RlebP; lra. Qed.

Lemma Rleb_anti : antisymmetric Rleb.
Proof. move=> a b /andP[/RlebP H /RlebP H1]; lra. Qed.

Lemma Rleb_trans : transitive Rleb.
Proof. by move=> a b c /RlebP H /RlebP H1;apply/RlebP; lra. Qed.

HB.instance Definition _ :=
  Order.isPOrder.Build ring_display R Rlt_def Rleb_refl Rleb_anti Rleb_trans.

Lemma Rleb_total : total Rleb.
Proof.
move=> a b; have [/RlebP->//|/RlebP->//] : a <= b \/ b <= a by lra.
by rewrite orbT.
Qed.

HB.instance Definition _ :=
  Order.POrder_isTotal.Build ring_display R Rleb_total.

HB.instance Definition _ :=
   Num.IntegralDomain_isLeReal.Build R Rle_0D Rle_0M Rle_0A Rle_0B Rle_0X
              Rabs_Ropp Rle0_Rabs Rlt_def.

Lemma Rarchimedean_axiom : Num.archimedean_axiom R.
Proof.
move=> x; exists (Z.abs_nat (up x) + 2)%nat.
have [Hx1 Hx2]:= (archimed x).
have Hz (z : Z): z = (z - 1 + 1)%Z by rewrite Zplus_comm Zplus_minus.
have Zabs_nat_Zopp z : Z.abs_nat (- z)%Z = Z.abs_nat z by case: z.
apply/RltbP/Rabs_def1.
  apply: (Rlt_trans _ ((Z.abs_nat (up x))%:R)%RR); last first.
    rewrite -[((Z.abs_nat _)%:R)%RR]Rplus_0_r mulrnDr.
    by apply/Rplus_lt_compat_l/Rlt_0_2.
  apply: (Rlt_le_trans _ (IZR (up x)))=> //.
  elim/(well_founded_ind (Zwf_well_founded 0)): (up x) => z IHz.
  case: (ZArith_dec.Z_lt_le_dec 0 z) => [zp | zn].
    rewrite [z]Hz plus_IZR Zabs.Zabs_nat_Zplus //; last exact: Zorder.Zlt_0_le_0_pred.
    rewrite plusE mulrnDr.
    apply/Rplus_le_compat_r/IHz; split; first exact: Zorder.Zlt_le_weak.
    exact: Zorder.Zlt_pred.
  apply: (Rle_trans _ (IZR 0)); first exact: IZR_le.
  by apply/RlebP/(ler0n (Num.NumDomain.clone _ R) (Z.abs_nat z)).
apply: (Rlt_le_trans _ (IZR (up x) - 1)).
  apply: Ropp_lt_cancel; rewrite Ropp_involutive.
  rewrite Ropp_minus_distr /Rminus -opp_IZR -{2}(Z.opp_involutive (up x)).
  elim/(well_founded_ind (Zwf_well_founded 0)): (- up x)%Z => z IHz .
  case: (ZArith_dec.Z_lt_le_dec 0 z) => [zp | zn].
  rewrite [z]Hz Zabs_nat_Zopp plus_IZR.
  rewrite Zabs.Zabs_nat_Zplus //; last exact: Zorder.Zlt_0_le_0_pred.
    rewrite plusE -Rplus_assoc -addnA [(_ + 2)%nat]addnC addnA mulrnDr.
    apply: Rplus_lt_compat_r; rewrite -Zabs_nat_Zopp.
    apply: IHz; split; first exact: Zorder.Zlt_le_weak.
    exact: Zorder.Zlt_pred.
  apply: (Rle_lt_trans _ 1).
    rewrite -{2}[1]Rplus_0_r; apply: Rplus_le_compat_l.
    by rewrite -/(IZR 0); apply: IZR_le.
  rewrite mulrnDr; apply: (Rlt_le_trans _ 2).
    by rewrite -{1}[1]Rplus_0_r; apply/Rplus_lt_compat_l/Rlt_0_1.
  rewrite -[2]Rplus_0_l; apply: Rplus_le_compat_r.
  by apply/RlebP/(ler0n (Num.NumDomain.clone _ R) (Z.abs_nat _)).
apply: Rminus_le.
rewrite /Rminus Rplus_assoc [- _ + _]Rplus_comm -Rplus_assoc -!/(Rminus _ _).
exact: Rle_minus.
Qed.

HB.instance Definition _ := 
  Num.NumDomain_bounded_isArchimedean.Build R Rarchimedean_axiom.

(** Here are the lemmas that we will use to prove that R has
the rcfType structure. *)
 
Lemma continuity_eq f g : f =1 g -> continuity f -> continuity g.
Proof.
move=> Hfg Hf x eps Heps.
have [y [Hy1 Hy2]]:= Hf x eps Heps.
by exists y; split=> // z; rewrite -!Hfg; exact: Hy2.
Qed.
 
Lemma continuity_sum (I : finType) F (P : pred I):
(forall i, P i -> continuity (F i)) ->
continuity (fun x => (\sum_(i | P i) ((F i) x)))%RR.
Proof.
move=> H; elim: (index_enum I)=> [|a l IHl].
  set f:= fun _ => _.
  have Hf: (fun x=> 0) =1 f by move=> x; rewrite /f big_nil.
  by apply: (continuity_eq Hf); exact: continuity_const.
set f := fun _ => _.
case Hpa: (P a).
  have Hf: (fun x => F a x + \sum_(i <- l | P i) F i x)%RR =1 f.
    by move=> x; rewrite /f big_cons Hpa.
  apply: (continuity_eq Hf); apply: continuity_plus=> //.
  exact: H.
have Hf: (fun x => \sum_(i <- l | P i) F i x)%RR =1 f.
  by move=> x; rewrite /f big_cons Hpa.
exact: (continuity_eq Hf).
Qed.
 
Lemma continuity_exp f n: continuity f -> continuity (fun x => (f x)^+ n)%RR.
Proof.
move=> Hf; elim: n=> [|n IHn]; first exact: continuity_const.
set g:= fun _ => _.
have Hg: (fun x=> f x * f x ^+ n)%RR =1 g.
  by move=> x; rewrite /g exprS.
by apply: (continuity_eq Hg); exact: continuity_mult.
Qed.

Lemma Rreal_closed_axiom : Num.real_closed_axiom R.
Proof.
move=> p a b; rewrite !le_eqVlt.
case Hpa: (p.[a] == 0)%RR.
  by move=> ? _ ; exists a=> //; rewrite lexx le_eqVlt.
case Hpb: (p.[b] == 0)%RR.
  by move=> ? _; exists b=> //; rewrite lexx le_eqVlt andbT.
case Hab: (a == b).
  by move=> _; 
     rewrite (eqP Hab) eq_sym Hpb /= (ltNge 0%R) /=; case/andP=> /ltW ->.
rewrite eq_sym Hpb /=; clear=> /RltbP Hab /andP [] /RltbP Hpa /RltbP Hpb.
suff Hcp: continuity (fun x => (p.[x])%RR).
  have [z [[Hza Hzb] /eqP Hz2]]:= IVT _ a b Hcp Hab Hpa Hpb.
  by exists z=> //; apply/andP; split; apply/RlebP.
rewrite -[p]coefK poly_def.
set f := fun _ => _.
have Hf: (fun (x : R) => \sum_(i < size p) (p`_i * x^+i))%RR =1 f.
  move=> x; rewrite /f horner_sum.
  by apply: eq_bigr=> i _; rewrite hornerZ hornerXn.
apply: (continuity_eq Hf); apply: continuity_sum=> i _.
apply:continuity_scal; apply: continuity_exp=> x esp Hesp.
by exists esp; split=> // y [].
Qed.
 
HB.instance Definition _ := 
  Num.RealField_isClosed.Build R Rreal_closed_axiom.

(* proprietes utiles de l'exp *)

Open Scope ring_scope.

Lemma expR0 : exp 0%RR = 1.
Proof. by rewrite exp_0. Qed.

Lemma expRD x y : exp(x) * exp(y) = exp (x + y)%RR.
Proof. by rewrite exp_plus. Qed.

Lemma expRX x n : exp(x) ^+ n = exp(x *+ n).
Proof.
elim: n => [|n Ihn].
  by rewrite expr0 mulr0n exp_0.
by rewrite exprS Ihn mulrS expRD.
Qed.

Lemma Rplus_add x y : (x + y)%R = (x + y)%RR.
Proof. by done. Qed.

Lemma Rmult_mul x y : (x * y)%R = (x * y)%RR.
Proof. by done. Qed.

Lemma Ropp_opp x : (- x)%R = (- x)%RR.
Proof. by done. Qed.

Lemma Rdiv_div x y : y != 0 -> Rdiv x y = x / y.
Proof.
move=> Hneq0.
apply: (@mulIr _ y); first by rewrite unitfE.
rewrite -!mulrA mulVr; last by rewrite unitfE.
rewrite -[X in _*X]Rmult_mul Rinv_l //.
by apply: (elimN eqP Hneq0).
Qed.

Lemma sin_add x y : sin (x + y)%RR = sin x * cos y + cos x * sin y.
Proof. by rewrite sin_plus. Qed. 

Lemma cos_add x y : cos (x + y)%RR = (cos x * cos y - sin x * sin y).
Proof. by rewrite cos_plus. Qed. 

Lemma natr_INR n : n%:R = INR n.
Proof.
elim: n => // n IH.
rewrite  S_INR [_.+1%:R](natrD _ 1) IH -[1%:R]/1.
by rewrite addrC.
Qed.

Lemma natrS (R : pzRingType) n : n.+1%:R = 1 + n%:R :> R.
Proof. by rewrite -(natrD _ 1 n). Qed.

Lemma Z_of_nat_gt0 n: (0 < n)%nat -> (0 < Z.of_nat n)%Z.
Proof. by case: n. Qed.

Lemma IZR_Zof_nat n : IZR (Z.of_nat n) = n%:R.
Proof. by rewrite -INR_IZR_INZ natr_INR. Qed.

Lemma expr_Rexp a1 b1 : (a1 ^+ b1)%RR = (a1 ^ b1)%R.
Proof.  by elim: b1 => //= n <-; rewrite exprS. Qed.

End ssreal_struct.

(* More theorems to make Reals and ssreflect work together *)

Ltac toR := rewrite /GRing.add /GRing.opp /GRing.zero /GRing.mul /GRing.inv
  /GRing.one ?natr_INR //=.

Lemma pow_expn x n : Nat.pow x n = expn x n.
Proof. by elim: n => //= n ->; rewrite expnS. Qed.

Lemma Rabs_expr x n : Rabs (x ^+ n)%RR = (Rabs x ^+ n)%RR.
Proof.
elim: n => [|n IH]; first by rewrite !expr0 Rabs_R1.
by rewrite !exprS Rabs_mult IH.
Qed.

Lemma Rabs_exprN1 n : Rabs ((-1) ^+ n)%RR = 1.
Proof. by rewrite Rabs_expr Rabs_Ropp Rabs_R1 expr1n. Qed.

Lemma continuous_continuity_pt f t : 
  continuous f t -> continuity_pt f t.
Proof.
move=> Hc.
apply: limit1_imp; last first.
  apply: is_lim_Reals_0.
  apply: is_lim_comp_continuous => //.
  apply: is_lim_id.
by move=> x [_]; lra.
Qed.

Import path.

Lemma eqR_leb a b : (a == b) = (Rleb a b && Rleb b a).
Proof.
apply/eqP/andP=> [->|[/RlebP H /RlebP]]; try lra.
by split; apply/RlebP; lra.
Qed.

Lemma Rltb_trans : transitive Rltb.
Proof. by move=> a b c /RltbP H /RltbP H1;apply/RltbP; lra. Qed.

Lemma Rltb_sorted_uniq_leb s : sorted Rltb s = uniq s && sorted Rleb s.
Proof.
case: s => //= n s; elim: s n => //= m s IHs n.
rewrite inE Rltb_def negb_or IHs -!andbA eq_sym.
case sn: (n \in s); last do !bool_congr.
rewrite andbF; apply/and5P=> [[ne_nm lenm _ _ le_ms]]; case/negP: ne_nm.
by rewrite eqR_leb lenm; apply: (allP (order_path_min Rleb_trans le_ms)).
Qed.

Lemma ex_derive_n_minus_inter f g n a b (h := fun z => f z - g z) :
      (forall x k,
        (k <= n)%nat -> a < x < b -> ex_derive_n f k x) ->
      (forall x k,
        (k <= n)%nat -> a < x < b -> ex_derive_n g k x) ->
      (forall x k,
        (k <= n)%nat -> a < x < b -> ex_derive_n h k x).
Proof.
move=> Hf Hg x k kLn aLxLb.
pose d := (Rmin (x - a) (b - x)) / 2.
have Pd : 0 < d.
  by rewrite /d /Rmin; case: Rle_dec; lra.
have Hd : a < x - d < x /\ x < x + d < b.
  by rewrite /d /Rmin; case: Rle_dec; lra.
apply: ex_derive_n_minus.
  exists (mkposreal _ Pd) => /= y Hy k1 Hk1.
  apply: Hf; first apply: leq_trans kLn.
    by apply/ssrnat.leP.
  rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /= in Hy.
  split_Rabs; lra.
exists (mkposreal _ Pd) => /= y Hy k1 Hk1.
apply: Hg; first apply: leq_trans kLn.
  by apply/ssrnat.leP.
rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /= in Hy.
split_Rabs; lra.
Qed.

Lemma Z_of_nat_S n : Z.of_nat n.+1 = (Z.of_nat n + 1)%Z.
Proof. rewrite /=; lia. Qed.

Lemma Z_of_nat_double n : Z.of_nat n.*2 = (Z.of_nat n * 2)%Z.
Proof.
by elim: n => [//=|n IH]; rewrite doubleS !Z_of_nat_S IH; lia.
Qed.

Lemma RInt_deriv_lin (f : R -> R) (x y : R) t1 t2  b1 b2 c1 c2 :
   y != 0 -> t1 <= t2 -> c1 < b1 -> b2 < c2 ->
  b1 <= x + t1 * y <= b2 -> 
  b1 <= x + t2 * y <= b2 -> 
  (forall x, c1 < x < c2 -> ex_derive f x) ->
  (forall x, b1 <= x <= b2 -> continuous (Derive f) x) ->
   RInt (fun z : R => Derive f  (y * z + x)) t1 t2 = 
    (/y) * (f (y * t2 + x) - f (y * t1 + x)).
Proof.
pose g t := y * t + x.
have ef u : ex_derive g u.
  by repeat (apply: ex_derive_mult || apply: ex_derive_plus ||
             apply : ex_derive_const || apply: ex_derive_id).
have Dg u : Derive g u = y.
    rewrite !(Derive_plus, Derive_const, Derive_mult, Derive_id) ; try
      by repeat (apply: ex_derive_mult || apply: ex_derive_plus ||
                apply : ex_derive_const || apply: ex_derive_id).
    by ring.
have Cg u : continuous g u.
  by do 5
   (apply: continuous_plus || apply: continuous_mult || apply: continuous_id || 
    apply: continuous_const).
pose RC := R_CompleteNormedModule.
move=> /eqP xDy t1Lt2 c1Lb1 b2Lc2 xt1B xt2B Df Cf.
have RyP : 0 < Rabs y by split_Rabs; lra.
have CDfg t : t1 <= t <= t2 ->continuous (Derive (f \o g)) t.
  move=> tB.
  have : continuous (fun x => Derive g x * Derive f (g x)) t.
    apply: continuous_mult.
      apply: (continuous_ext (fun _ => y)) => [v//|].
      by apply: continuous_const.
    apply: continuous_comp => //.
    apply: Cf.
    by rewrite /g; nra.
  apply: continuous_ext_loc.
  have K2 a b c : 0 < a -> b < c / a -> a * b < c.
    move=> aP abLc.
    rewrite (_ : c =  a * (c / a)).
      by apply: Rmult_lt_compat_l.
    by field; lra.
  have gtB : b1 <= g t <= b2 by rewrite /g; nra.
  pose eps := Rmin (Rabs ((c1 - g t)/ y))
                   (Rabs ((c2 - g t)/ y)).
  have epsP : 0 < eps by
  apply: Rmin_glb_lt; rewrite Rabs_div //;
  apply: Rdiv_lt_0_compat; split_Rabs; lra.
  exists (mkposreal _ epsP) => u /= Hu.
  have uB : c1 < g u < c2.
    have F u1 u2 u3 : u1 < Rmin u2 u3 -> (u1 < u2 /\ u1 < u3).
      by rewrite /Rmin; case: Rle_dec; lra.
    have /F[F1 F2] : Rabs (u - t) < eps by apply: Hu.
    split.
      suff : Rabs (g t - g u) < Rabs (c1 - g t) by split_Rabs; lra.
      have -> : g t - g u = y * (t - u)  by rewrite /g; lra.
      rewrite Rabs_mult.
      apply: K2 => //.
      by rewrite -Rabs_div // Rabs_minus_sym.
    suff : Rabs (g t - g u) < Rabs (c2 - g t) by split_Rabs; lra.
    have -> : g t - g u = y * (t - u)  by rewrite /g; lra.
    rewrite Rabs_mult.
    apply: K2 => //.
    by rewrite -Rabs_div // Rabs_minus_sym.
  rewrite [RHS]Derive_comp //.
  by apply: Df; lra.
rewrite (_ : _ - _ = (f \o g) t2 - (f \o g) t1); last first.
  by rewrite /g; congr (_ - f _); ring.
rewrite -RInt_Derive; last 2 first.
  move=> t; rewrite Rmin_left // Rmax_right // => tB.
  apply: ex_derive_comp => //.
    by apply: Df; rewrite /g; nra.
  move=> t; rewrite Rmin_left // Rmax_right // => tB //.
  by exact: CDfg.
rewrite -[RHS](@RInt_scal RC); last first.
  apply: ex_RInt_continuous => t; rewrite Rmin_left // Rmax_right //.
  by exact: CDfg.
apply: RInt_ext; rewrite Rmin_left // Rmax_right // => u Hu.
rewrite [in RHS]Derive_comp => //; last first.
  by apply: Df; rewrite /g; nra.
rewrite Dg /g /scal /= /mult /=; field; lra.
Qed.


Section Sum.

Import GRing.Theory.
Open Scope ring_scope.


Lemma ex_RInt_sum (T : eqType) (P : pred T) (f : T -> R -> R) a b l :
  (forall i, i \in l -> P i -> ex_RInt (f i) a b) -> 
  ex_RInt (fun x : R => \sum_(j <- l | P j) f j x)  a b.
Proof.
elim: l => /= [_|c l IH He].
  apply: ex_RInt_ext => [x Hx|].
    by rewrite big_nil.
  by apply: ex_RInt_const.
apply: ex_RInt_ext => [x Hx|].
  by rewrite big_cons.
have [Pc | NPc] := boolP (P c); last first.
  apply: IH => i iIl.
  by apply: He; rewrite inE iIl orbT.
apply: ex_RInt_plus.
  by apply: He => //; rewrite inE eqxx.
apply: IH => i iIl.
by apply: He; rewrite inE iIl orbT.
Qed.

Lemma RInt_sum (T : eqType) (P : pred T) (f : T -> R -> R) a b l :
  (forall i, i \in l -> P i -> ex_RInt (f i) a b) ->
  RInt
    (fun x : R => \sum_(i <- l| P i) (f i x)) a b =
  \sum_(i <- l | P i)
    RInt
      (fun x : R => (f i x)) a b.
Proof.
elim: l => /= [HR|c l IH HR].
  apply: etrans.
    apply: RInt_ext => i Hi.
    by rewrite big_nil.
  by rewrite RInt_const [LHS](@mulr0 (GRing.PzRing.clone _ R)) big_nil.
rewrite big_cons.
apply: etrans.
  apply: RInt_ext => x Hx.
  by rewrite big_cons.
case: (boolP (P c)) => [HP|HNP]; last first.
  apply: IH => i iIl Pi.
  by apply: HR; rewrite ?inE ?iIl ?orbT.
rewrite RInt_plus ?IH => // [i iIl Pi||].
- by apply: HR; rewrite ?inE ?iIl ?orbT.
- by apply: HR; rewrite ?inE ?eqxx.
apply: ex_RInt_sum=> i iIl Pi.
by apply: HR; rewrite ?inE ?iIl ?orbT.
Qed.

End Sum.

Lemma ex_RInt_comp_lin1 f (u v a b : R) :
       ex_RInt f (u * a + v) (u * b + v) ->
       @ex_RInt R_CompleteNormedModule (fun y : R => f (u * y + v)) a b.
Proof.
move=> H.
case: (Req_dec u 0) => [->|/eqP uNz].
  apply: ex_RInt_ext => [x Hx|].
    rewrite [_ * _](@mul0r (GRing.PzRing.clone _ R)) 
            [_ + _](@add0r (GRing.PzRing.clone _ R)).
     by [].
  by apply: ex_RInt_const.
apply: ex_RInt_ext => [x Hx|].
  rewrite -[RHS](@mulfK _ u); last by [].
  by rewrite mulrC [(_ * u)%RR]mulrC.
apply: ex_RInt_scal.
by apply: ex_RInt_comp_lin.
Qed.

Lemma MVT_le (f : R -> R) (a b : R) (df : R -> R): 
   (forall x : R,
     a <= x <= b -> is_derive f x (df x)) ->
   (forall x : R,
     a <= x <= b -> 0 <= df x) ->
   (forall x : R,
      a <= x <= b -> continuity_pt f x) ->
     a <= b -> f a <= f b.
Proof.
move=> H1 H2 H3 aLb.
case: (MVT_gen f a b df) => x;
    rewrite Rmin_left // Rmax_right // => Hx.
- by apply: H1; lra.
- by apply: H3.
rewrite (_ : f b = f b - f a + f a); try lra.
have [Hx1 ->] := Hx.
have := H2 _ Hx1.
nra.
Qed.

Lemma natDivP x y : (0 < y)%nat -> (x %/ y)%nat = (x / y)%nat.
Proof.
move=> yP.
apply: (Nat.div_unique _ _ _ (x %% y)).
 by apply/ssrnat.ltP; rewrite ltn_mod.
by rewrite [(_ * _)%coq_nat]mulnC -[RHS]divn_eq.
Qed.

Lemma Rchar : [pchar R]%RR =i pred0.
Proof.
case => //= i; rewrite !inE.
by rewrite (@eqr_nat (Num.NumDomain.clone _ R) i.+1 0%nat) andbF.
Qed.

(* Big op and R *)
Lemma leR_sum (A : eqType) (f g : A -> R) (P : A -> bool) (l : seq A) :
  (forall i, i \in l -> P i -> f i <= g i) ->
   (\sum_(i <- l | P i) f i)%RR <= (\sum_(i <- l | P i) g i)%RR.
Proof.
elim: l => [_|a l IH H] /=; first by rewrite !big_nil; lra.
have F :  (\sum_(i <- l | P i) f i)%RR <= (\sum_(i <- l | P i) g i)%RR.
  by apply: IH => i iIl ?; apply: H => //; rewrite in_cons iIl orbT.
rewrite !big_cons; case: (boolP (P a)) => Hp //.
rewrite /GRing.add /= in F *.
suff:  f a <= g a by lra.
by apply: H => //; rewrite in_cons eqxx.
Qed.

Lemma sumR_ge0 (A : eqType) (l : seq A) (P : A -> bool) (f : A -> R) : 
 (forall i, i \in l -> P i -> 0 <= f i) -> 0 <= (\sum_(i <- l | P i) (f i))%RR.
Proof.
elim: l => [_|a l IH H]; first by rewrite big_nil /GRing.zero /=; lra.
have HP :  0 <= (\sum_(i <- l | P i) f i)%RR.
  by apply: IH => i HA; apply: H; rewrite in_cons HA orbT.
rewrite big_cons; case E : (P a) => //.
apply: Rplus_le_le_0_compat => //.
by apply: H; rewrite ?in_cons ?eqxx.
Qed.

Lemma mulR_sumr (I : Type) (r : seq I) 
         (P : I -> bool) (F : I -> R) (x : R) : 
  (x * (\sum_(i <- r | P i) F i)%RR) = (\sum_(i <- r | P i) (x * F i)%R)%RR.
Proof. by apply: (@GRing.mulr_sumr (GRing.PzRing.clone _ R)). Qed.


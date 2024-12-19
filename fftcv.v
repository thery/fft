Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import String Rstruct Reals Cstruct Psatz Cmore.
Require Import Coquelicot.Coquelicot.
Require Import digitn mfft.

Notation "m ^ n" := (expn m n) : nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

From Interval Require Import Specific_ops Missing.Stdlib Xreal.
From Interval Require Import Basic Float Sig Interval.
From Interval Require Import Tactic.

Module SFBI2 := SpecificFloat Specific_bigint.BigIntRadix2.
Module I := Float_full.FloatIntervalFull SFBI2.

Module Complex_interval (F : FloatOps with Definition sensible_format := true).
Module I := Float_full.FloatIntervalFull F.

Section Complex_intervals.

Variable prec: F.precision.

Notation mant := Specific_bigint.BigIntRadix2.smantissa_type.
Notation xpnt := Specific_bigint.BigIntRadix2.exponent_type.
 
Notation D := F.type.
Notation ID := (Float.f_interval F.type).
Notation "x '\contained_in' I" := 
  (contains (I.convert I) (Xreal x)) (at level 20).
Notation D2R := I.T.toR.
Notation I0 := (I.bnd F.zero F.zero).
Definition mkI f := (I.bnd f f).
Notation I1 := (I.fromZ prec 1).
Definition mkIz z := (I.fromZ prec z).
Notation scl2 I := (I.mul prec I ((I.fromZ prec 2))).
Notation add I J := (I.add prec I J).
Notation mul I J := (I.mul prec I J).
Notation sqr I := (I.sqr prec I).
Notation sub I J := (I.sub prec I J).
Notation inv I := (I.sub prec I).
Notation div I J := (I.div prec I J).
Notation sqrt I := (I.sqrt prec I).
Notation pi := (I.pi prec).

Definition FtoZ_aux beta s m e := 
let sm := if s then Z.neg m else Z.pos m in
match e with
| 0%Z => sm
| Z.pos p => (sm * Z.pow_pos (Zaux.radix_val beta) p)%Z
| Z.neg p => (sm / (Z.pow_pos (Zaux.radix_val beta) p))%Z
end.

Definition FtoZ beta (f : float beta) :=
match f with
| Basic.Fnan => 0%Z
| Fzero => 0%Z
| Float s m e => FtoZ_aux beta s m e
end.

Definition getZCandidate (i : ID) := 
  match i with
  | Float.Inan => None 
  | Float.Ibnd a b => 
     let a1 := (FtoZ (F.toF (I.F.nearbyint_DN rnd_DN a))) in 
     let b1 := (FtoZ (F.toF (I.F.nearbyint_UP rnd_UP b))) in
     Some ((a1 -1)%Z, (Z.to_nat (b1 - a1 + 2)%Z)) 
  end.

Fixpoint isZCandidate (n : nat) (z : Z) (i : ID) :=
if n is n1.+1 then
  let zI := mkIz z in 
  if I.subset zI i then
    if I.is_empty (I.meet (mkIz (z + 1)) i) then Some z 
    else None 
  else if I.is_empty (I.meet zI i) then isZCandidate n1 (z + 1) i 
       else None
else None.

Lemma isZCandidate_correct n z z1 i :
  ~ ((IZR z  - 1) \contained_in i) -> isZCandidate n z i = Some z1 -> 
  [/\ ~ (IZR z1 - 1) \contained_in i ,
        (IZR z1)     \contained_in i &
      ~ (IZR z1 + 1) \contained_in i 
  ].
Proof.
elim: n z => //= n IH z Hz.
case: (boolP (I.subset _ _)) => [Hi|/ negP Hi].
  case: (boolP (I.is_empty _)) => [He [<-]|//].
  split => //.
    apply: I.subset_correct Hi.
    by apply: I.fromZ_correct.
  rewrite -plus_IZR =>  Hz1.
  have Hz2 : IZR (z + 1) \contained_in  (I.meet (mkIz (z + 1)) i).
    by apply: I.meet_correct => //; apply: I.fromZ_correct.
  by apply: I.is_empty_correct Hz2 He.
case: (boolP (I.is_empty _)) => [He Hc|//].
apply: IH Hc => //.
have -> : (IZR (z + 1) - 1 = IZR z)%R by rewrite plus_IZR; lra.
move=> Hz1.
have Hz2 : IZR z \contained_in  (I.meet (mkIz z) i).
  by apply: I.meet_correct => //; apply: I.fromZ_correct.
by apply: I.is_empty_correct Hz2 He.
Qed.

Definition onlyOneZ (i : ID) := 
  if getZCandidate i is Some (z, n) then 
    if I.is_empty (I.meet (mkIz z) i) then isZCandidate n (z + 1) i else None 
  else None.
  
Lemma contains_connect x y z i : 
  x \contained_in i -> y \contained_in i -> 
  (x <= z <= y)%R -> z \contained_in i.
Proof.
rewrite /contains.
by case: I.convert => // [] [|r1] [|l1]; lra.
Qed.

Lemma onlyOneZ_correct i z z1 :
  onlyOneZ i = Some z -> IZR z1 \contained_in i -> z = z1.
Proof.
rewrite /onlyOneZ.
case E : getZCandidate => [[z2 n2]|//].
case: (boolP (I.is_empty _)) => [He Hc Hz1|//].
have [] := isZCandidate_correct _ Hc.
  have -> : (IZR (z2 + 1) - 1 = IZR z2)%R by rewrite plus_IZR; lra.
  move=> Hz2.
  have H1z2 : IZR z2 \contained_in  (I.meet (mkIz z2) i).
    by apply: I.meet_correct => //; apply: I.fromZ_correct.
  by apply: I.is_empty_correct H1z2 He.
move=> H1z H2z H3z.
have : [\/ (IZR z = IZR z1), (IZR z1 <= IZR z -1)%R | (IZR z + 1 <= IZR z1)%R].
  suff : (IZR z = IZR z1) \/ (IZR z1 <= IZR z -1)%R \/ (IZR z + 1 <= IZR z1)%R.
    case; first by apply: Or31.
    by case; [apply: Or32|apply: Or33].
  have : (z = z1) \/ (z1 <= z -1)%Z \/ (z + 1 <= z1)%Z by lia.
  rewrite -minus_IZR -plus_IZR.
  case; first by move->; left.
  by case => H; [right;left|right;right]; apply: IZR_le.
case => [/eq_IZR//|z1Lz|zLz1].
  by case: H1z; apply: contains_connect Hz1 H2z _; lra.
by case: H3z; apply: contains_connect H2z Hz1 _; lra.
Qed.

Definition chalf := F.div2 (F.fromZ 1).

Lemma chalf_correct :  F.toX chalf = Xreal (/ 2).
Proof.
rewrite F.div2_correct //=; last first.
  by rewrite /D2R F.fromZ_correct //= Rabs_R1; lra.
by rewrite F.fromZ_correct // Xdiv_split Xmul_1_l /= /Xinv' is_zero_false.
Qed.

Notation div2 I := (I.mul_mixed prec I chalf).

Notation "l '\lcontained_in' L" :=
 (forall i,  l`_i \contained_in nth I0 L i) (at level 20).

Inductive ExtendedC : Set := XCnan : ExtendedC | Xcomplex : C -> ExtendedC.

Inductive cinterval := CInterval of interval * interval.

Definition Ccontains (i : cinterval) (v : ExtendedC) :=
  let 'CInterval (c1, c2) := i in 
  if v is Xcomplex (r1, r2) then
    contains c1 (Xreal r1) /\ contains c2 (Xreal r2)
  else  
    contains c1 Xnan /\ contains c2 Xnan.

Definition CItype := (I.type * I.type)%type.

Definition CIconvert (I : CItype) : cinterval := 
  CInterval (I.convert I.1, I.convert I.2).

Notation "x '\Ccontained_in' I" := 
  (Ccontains (CIconvert I) (Xcomplex x)) (at level 20).

Definition CI0 : CItype := (I0, I0).
Definition mkCI (i1 i2 : I.type) : CItype := (i1, i2).
Definition CI1 : CItype := (I1, I0).
Definition CIscl2 (I : CItype) : CItype := (scl2 I.1, scl2 I.2).
Definition CIadd (I J : CItype) : CItype := (add I.1 J.1, add I.2 J.2).
Definition CImul (I J : CItype) : CItype := 
  (sub (mul I.1 J.1) (mul I.2 J.2), add (mul I.1 J.2) (mul I.2 J.1)).
Definition CIsqr (I : CItype) : CItype := 
  (sub (sqr I.1) (sqr I.2), scl2 (mul I.1 I.2)).
Definition CIneg (I : CItype) : CItype := (I.neg I.1, I.neg I.2).
Definition CIsub (I J : CItype) : CItype := (sub I.1 J.1, sub I.2 J.2).
Definition CIinv (I : CItype) : CItype := 
  let q := (add (sqr I.1) (sqr I.2)) in (div I.1 q,(div (I.neg I.2) q)).
Definition CIdiv2 (I : CItype) : CItype :=  (div2 I.1, div2 I.2).
Definition CIdiv (I J : CItype) : CItype := 
  let q := (add (sqr J.1) (sqr J.2)) in
  (div (add (mul I.1 J.1) (mul I.2 J.2)) q, 
   div (sub (mul I.2 J.1) (mul I.1 J.2)) q).
Definition CImod (I : CItype) : I.type := sqrt (add (sqr I.1) (sqr I.2)).


Fixpoint CIpowN (I : CItype) (p : positive) : CItype := 
match p with 
| xH => I
| xO p1 => CIpowN (CIsqr I) p1
| xI p1 => CImul I (CIpowN (CIsqr I) p1)
end.

Definition  CIpow (I : CItype) (n : nat) : CItype :=
 if n is 0%nat then CI1 else CIpowN I (Pos.of_nat n).

Definition FtoI (a: D) := (Float.Ibnd a a).

Lemma FtoI_correct a : F.real a -> (D2R a) \contained_in (FtoI a).
Proof.
move=> aR /=.
rewrite (I.F'.valid_lb_real _ aR) (I.F'.valid_ub_real _ aR) /=.
by rewrite /D2R; case: F.toX => //= r; lra.
Qed.

Lemma I020 x : x \contained_in I0 -> x = 0%R.
Proof. 
rewrite /= F.zero_correct; case: F.valid_lb; case: F.valid_ub => //=; lra. 
Qed.
 
Lemma I0_correct: 0 \contained_in I0.
Proof. 
rewrite /= F.zero_correct /= I.F'.valid_lb_zero I.F'.valid_ub_zero => /=; lra.
Qed.

Lemma I1_correct: 1%R \contained_in I1.
Proof.
have [H1 H2]:=  I.F.fromZ_DN_correct prec 1.
have [H3 H4]:=  I.F.fromZ_UP_correct prec 1.
rewrite /= H1 H3 /=; case: I.F.toX H2; case: I.F.toX H4 => //=.
 by move=> _ r; rewrite /le_lower /=; lra.
by move=> r Hr r1; rewrite /le_lower /=; lra.
Qed.

Lemma mul_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x * y) \contained_in (mul I J).
Proof. by apply I.mul_correct. Qed.

Lemma sqr_correct x I :
	x \contained_in I -> (x * x) \contained_in sqr I.
Proof. by apply I.sqr_correct. Qed.

Lemma sub_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x - y) \contained_in (sub I J).
Proof. by apply I.sub_correct. Qed.

Lemma opp_correct x I :
	x \contained_in I ->  (- x) \contained_in (I.neg I).
Proof. by apply I.neg_correct. Qed.

Lemma add_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (add I J).
Proof. by apply I.add_correct. Qed.

Lemma inv_correct x I:
	x \contained_in I -> (/ x)%R \contained_in (I.inv prec I).
Proof.
move=> xI.
have /= := I.inv_correct prec I (Xreal x) xI.
rewrite /Xinv'; case: is_zero => //=; case: I.inv => //= l b.
by case: F.valid_lb => //=; case: F.valid_ub.
Qed.

Lemma div_correct_prec p x y I J:
	x \contained_in I -> y \contained_in J -> 
    (x / y)%R \contained_in (I.div p I J).
Proof.
move=> xI yJ.
have /= := I.div_correct p I J (Xreal x) (Xreal y) xI yJ.
rewrite /Xdiv'; case: is_zero => //; case: I.div => //= l b.
by case: F.valid_lb => //=; case: F.valid_ub.
Qed.

Lemma div_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x / y)%R \contained_in (div I J).
Proof. by apply: div_correct_prec. Qed.

Lemma scl2_correct x I:
	x \contained_in I -> (x *+ 2) \contained_in (scl2 I).
Proof.
move=> xI.
suff -> : Xreal (x *+ 2) = Xmul (Xreal x) (Xreal (Raux.bpow radix2 1)).
  apply: mul_correct => //.
  by apply: I.fromZ_correct.
congr Xreal.
by have ->: (x*2 = x + x)%R by lra.
Qed.

Lemma div2_correct x I: x \contained_in I -> (x / 2) \contained_in (div2  I).
Proof.
move=> xI.
have -> : Xreal (x / 2) = Xmul (Xreal x) (Xreal (/2)) by [].
rewrite -chalf_correct.
by apply: I.mul_mixed_correct.
Qed.

Lemma neg_correct x I:
	x \contained_in I -> (-x) \contained_in (I.neg I).
Proof. by apply I.neg_correct. Qed.

Lemma abs_correct x I:
	x \contained_in I -> Rabs x \contained_in (I.abs I).
Proof. by apply I.abs_correct. Qed.

Lemma sqrt_correct x I :
	x \contained_in I ->  R_sqrt.sqrt x \contained_in (sqrt I).
Proof. by apply: I.sqrt_correct. Qed.

Lemma power_pos_correct x I (n : nat) :
  (0 < n)%nat ->
  x \contained_in I -> (x ^ n) \contained_in I.power_pos prec I (Pos.of_nat n).
Proof.
move=> nP.
have := I.power_pos_correct prec (Pos.of_nat n) I (Xreal x).
rewrite /= /I.extension /= Nat2Pos.id //.
by case: n nP.
Qed.

Definition D2C (a : D) : C := (D2R a, 0%R).
Definition FtoCI (a: D) : CItype := (Float.Ibnd a a, I0).

Lemma FtoCI_correct a : F.real a -> (D2C a) \Ccontained_in (FtoCI a).
Proof.
move=> aR /=.
rewrite /D2C /D2R /= I.F'.valid_lb_zero I.F'.valid_ub_zero /= F.zero_correct /=.
rewrite (I.F'.valid_lb_real _ aR) (I.F'.valid_ub_real _ aR) /=.
by case: F.toX => /= [| r]; lra.
Qed.

Lemma CI020 x : x \Ccontained_in CI0 -> x = 0%C.
Proof.
rewrite /GRing.zero /= /GRing.zero; case: x => x y /=.
rewrite I.F'.valid_lb_zero I.F'.valid_ub_zero /= F.zero_correct /=.
by intros [? ?]; congr (_, _); lra.
Qed.
 
Lemma CI0_correct: 0 \Ccontained_in CI0.
Proof.
by rewrite /GRing.zero /= /GRing.zero F.zero_correct /= I.F'.valid_lb_zero 
     I.F'.valid_ub_zero => /=; lra.
Qed.
 

Lemma CI1_correct: 1 \Ccontained_in CI1.
Proof. by split; [apply: I1_correct| apply: I0_correct]. Qed.

Lemma CIadd_correct x y I J:
	x \Ccontained_in I -> y \Ccontained_in J -> 
  (x + y)%C \Ccontained_in (CIadd I J).
Proof.
case: x => x1 x2; case: y => y1 y2; case: I => I1 I2; case: J => J1 J2.
by move=> [H1 H2] [H3 H4]; split; apply: add_correct.
Qed.

Lemma CIsub_correct x y I J:
	x \Ccontained_in I -> y \Ccontained_in J -> 
  (x - y)%C \Ccontained_in (CIsub I J).
Proof.
case: x => x1 x2; case: y => y1 y2; case: I => I1 I2; case: J => J1 J2.
by move=> [H1 H2] [H3 H4]; split; apply: sub_correct.
Qed.

Lemma CImul_correct x y I J:
	x \Ccontained_in I -> y \Ccontained_in J -> 
  (x * y)%C \Ccontained_in (CImul I J).
Proof.
case: x => x1 x2; case: y => y1 y2; case: I => I1 I2; case: J => J1 J2.
move=> [H1 H2] [H3 H4]; split.
  by apply: sub_correct; apply: mul_correct.
by apply: add_correct; apply: mul_correct.
Qed.

Lemma CIsqr_correct x I :
	x \Ccontained_in I -> (x * x) \Ccontained_in CIsqr I.
Proof.
case: x => x1 x2; case: I => I1 I2.
move=> [H1 H2]; split.
  by apply: sub_correct; apply: sqr_correct.
rewrite [(_.2 * _)%R]Rmult_comm -[(_ + _)%R](@mulr2n (GRing.Nmodule.clone _ R)).
by apply: scl2_correct; apply: mul_correct.
Qed.

Lemma CIneg_correct x I :
	x \Ccontained_in I ->  (- x) \Ccontained_in (CIneg I).
Proof.
case: x => x1 x2; case: I => I1 I2.
by move=> [H1 H2]; split; apply opp_correct.
Qed.

Lemma CIinv_correct x I:
	x \Ccontained_in I -> (/ x)%C \Ccontained_in (CIinv I).
Proof.
case: x => x1 x2; case: I => I1 I2.
have F1 : ((x1, x2).1 ^ 2 + (x1, x2).2 ^ 2 = (x1 * x1 + x2 * x2))%R.
  by rewrite /=; lra.
move=> [H1 H2]; split; rewrite F1.
  by apply: div_correct => //; apply: add_correct; apply: sqr_correct.
apply: div_correct; first by apply: opp_correct.
by apply: add_correct; apply: sqr_correct.
Qed.

Lemma CIdiv_correct x y I J:
	x \Ccontained_in I -> y \Ccontained_in J -> 
  (x / y)%C \Ccontained_in (CIdiv I J).
Proof.
case: x => x1 x2; case: y => y1 y2; case: I => I1 I2; case: J => J1 J2.
move=> [H1 H2] [H3 H4]; split => /=.
  have -> : ((y1 * (y1 * 1) + y2 * (y2 * 1)) = y1 * y1 + y2 * y2)%R by lra.
  rewrite /Rdiv; set z := (/ _).
  have -> : ((x1 * (y1 * z) - x2 * (- y2 * z)) = (x1 * y1 + x2 * y2) * z)%R.
    by lra.
  apply: div_correct.
    by apply: add_correct; apply: mul_correct.
  by apply: add_correct; apply: sqr_correct.
have -> : ((y1 * (y1 * 1) + y2 * (y2 * 1)) = y1 * y1 + y2 * y2)%R by lra.
rewrite /Rdiv; set z := (/ _).
have -> : ((x1 * (- y2 * z) + x2 * (y1 * z)) = (x2 * y1 - x1 * y2) * z)%R.
  by lra.
apply: div_correct.
  by apply: sub_correct; apply: mul_correct.
by apply: add_correct; apply: sqr_correct.
Qed.

Lemma CIscl2_correct x I:
	x \Ccontained_in I -> (x *+ 2)%C \Ccontained_in (CIscl2 I).
Proof.
case: x => x1 x2; case: I => I1 I2.
by move=> [H1 H2]; split; apply: scl2_correct.
Qed.

Lemma CIdiv2_correct x I: 
  x \Ccontained_in I -> (x / 2)%C \Ccontained_in (CIdiv2 I).
Proof.
case: x => x1 x2; case: I => I1 I2.
move=> [H1 H2]; split.
  set xx := (_ - _)%R; have -> : xx = (x1 / 2)%R.
    by rewrite /xx /=; lra.
  by apply: div2_correct.
set xx := (_ + _)%R; have -> : xx = (x2 / 2)%R.
  by rewrite /xx /=; lra.
by apply: div2_correct.
Qed.

Lemma CImod_correct x I:
	x \Ccontained_in I -> Cmod x \contained_in (CImod I).
Proof.
case: x => x1 x2; case: I => I1 I2.
move=> [H1 H2].
by apply: sqrt_correct; apply: add_correct; rewrite Rmore.pow2_mult;
   apply: sqr_correct.
Qed.

Lemma CIpowN_correct x I (n : positive) :
  x \Ccontained_in I -> (x ^ Pos.to_nat n) \Ccontained_in CIpowN I n.
Proof.
elim: n x I => [p IH|p IH|] x I xCI; last first.
- have -> : (x ^ Pos.to_nat 1 = x)%C by rewrite /=; ring.
  by[].
- have -> : (x ^ Pos.to_nat p~0 = (x ^ 2) ^ Pos.to_nat p)%C.
    rewrite -Cpow_mult_r; congr (_ ^ _)%C.
    by rewrite Pos2Nat.inj_xO.
  apply: IH.
  have -> : (x ^ 2 = x * x)%C by ring.
  by apply: CIsqr_correct.
have -> : (x ^ Pos.to_nat p~1 = x * (x ^ 2) ^ Pos.to_nat p)%C.
  rewrite -Cpow_mult_r -Cpow_S; congr (_ ^ _)%C.
  by rewrite Pos2Nat.inj_xI.
rewrite [CIpowN _ _]/=; apply: CImul_correct => //.
apply: IH.
have -> : (x ^ 2 = x * x)%C by ring.
by apply: CIsqr_correct.
Qed.

Lemma CIpow_correct x I (n : nat) :
  x \Ccontained_in I -> (x ^ n) \Ccontained_in CIpow I n.
Proof.
case: n => [|n1] xCI; first by apply: CI1_correct.
have {2}-> : n1.+1 = Pos.to_nat (Pos.of_nat n1.+1) by rewrite Nat2Pos.id.
by apply: CIpowN_correct.
Qed.

Definition onlyOneC (i : CItype) := 
  let: (i1, i2) := i in 
  if onlyOneZ i1 is Some z then 
    if onlyOneZ i2 is Some 0%Z then Some z else None
  else None. 
   
Lemma onlyOneC_correct i (z z1 : Z) : 
  onlyOneC i = Some z -> RtoC (IZR z1) \Ccontained_in i -> z = z1.
Proof.
case: i => i1 i2 /=.
case E1 : onlyOneZ =>[j|//].
case E2 : onlyOneZ =>[k|//].
case: k E2 => // E2 [<-] [Hz1 Hz2].
by apply: onlyOneZ_correct E1 _.
Qed.

Definition ci_get s i := nth CI0 s i.

Definition ci_reverse n (l : seq CItype) : seq CItype :=
  [seq (ci_get l (rdigitn 2 n i)) | i : 'I_(2 ^ n)].

Definition ci_step m n (w : CItype) (l : seq CItype) :=
  [seq 
    if ((i %% 2 ^ n.+1) < 2 ^ n)%nat then
      CIadd (ci_get l i) (CImul (CIpow w (i %% 2 ^ n)) (ci_get l (i + 2 ^ n)))
    else 
      CIsub (ci_get l (i - 2 ^ n)) (CImul (CIpow w (i %% 2 ^ n)) (ci_get l i))
    | i : 'I_(2 ^ (m + n).+1)].

Fixpoint ci_odd (A : Type) (l : seq A) := 
 if l is a :: b :: l1 then b :: ci_odd l1 else [::].

Definition  ci_even (A : Type) (l : seq A) := 
 if l is a :: l1 then a :: ci_odd l1 else [::].

Fixpoint ci_map2 (A B C : Type) (f : A -> B -> C) 
                   (l1 : seq A) (l2 : seq B) (l : seq C) :=
  if l1 is a :: l3 then
  if l2 is b :: l4 then f a b :: ci_map2 f l3 l4 l else l else l.

Lemma size_ci_map2 (A B C : Type) (f : A -> B -> C) 
                   (l1 : seq A) (l2 : seq B) (l : seq C) : 
  size (ci_map2 f l1 l2 l) = (minn (size l1) (size l2) + size l)%nat.
Proof.
elim : l1 l2 => /= [|a1 l1 IH] [|a2 l2] //=.
by rewrite IH /= minnSS.
Qed.

Fixpoint ci_pow (A B : Type) (f: B -> B) (l : seq A) (x : B) := 
 if l is a :: l1 then x :: ci_pow f l1 (f x) else [::].

Lemma size_ci_pow (A B : Type) (f: B -> B) (l : seq A) (x : B) :
  size (ci_pow f l x) = size l.
Proof. by elim: l x => //= _ l IH x; rewrite IH. Qed. 

Fixpoint c_fft (n : Datatypes.nat) (l1 : seq C) (w : C) : seq C := 
  if n is n1.+1 then 
  let w2 := w * w in 
  let e := c_fft n1 (ci_even l1) w2 in 
  let o := c_fft n1 (ci_odd l1) w2 in 
  let p := ci_pow (Cmult w)%C e 1 in 
  let o1 := ci_map2 Cmult p o [::] in 
  ci_map2 Cplus e o1 (ci_map2 Cminus e o1 [::]) 
  else [:: nth 0%C l1 0%N].

Lemma size_c_fft n l w : size (c_fft n l w) = (2 ^ n)%nat.
Proof.
elim: n l w => //= n IH l w.
rewrite !(size_ci_map2, size_ci_pow, IH).
by rewrite !(minnn, addn0) addnn -mul2n expnS.
Qed.

Lemma ci_odd_correct (A : ringType) (l : seq A) :
  Poly (ci_odd l) = odd_poly (Poly l).
Proof.
elim: (size _).+1 {-2}l  (leqnn (size l).+1) => // n IH [|a [|b {}l]] /=.
- by rewrite odd_polyC.
- by rewrite cons_poly_def odd_polyD mul0r !odd_polyC add0r.
rewrite !ltnS => Hs.
rewrite !cons_poly_def IH; last by apply: leq_trans Hs.
by rewrite !odd_polyD odd_polyMX even_polyD even_polyC even_polyMX odd_polyC 
           addr0.
Qed.

Lemma ci_even_correct (A : ringType) (l : seq A) : 
  Poly (ci_even l) = even_poly (Poly l).
Proof.
case: l => /= [|a l]; first by rewrite even_polyC.
by rewrite !cons_poly_def ci_odd_correct even_polyD even_polyMX even_polyC.
Qed.

Lemma ci_pow_correct (R : ringType) w (l : seq R) : 
  Poly (ci_pow (Cmult w)%C l 1) = \poly_(i < size l) w^+i.
Proof.
suff F j : Poly (ci_pow (Cmult w)%C l (w^+j)) = \poly_(i < size l) w^+(i + j).
  rewrite (F 0).
  by apply/polyP => i; rewrite !coef_poly addn0.
elim: l j => [|a l IH] j /=.
  by apply/polyP => i; rewrite coef_poly ltn0 coefC if_same.
rewrite cons_poly_def.
have -> : (w * w^+j = w^+ j.+1)%C by rewrite exprS.
rewrite IH.
apply/polyP => i.
rewrite coefD coefC coefMX !coef_poly.
case: i => [|i] /=; first by rewrite add0r.
by rewrite ltnS addnS addr0.
Qed.

Lemma ci_map_scal a (l : seq C) : Poly [seq (a * i) | i <- l]  = a *: Poly l.
Proof.
elim: l => /= [|b l IH]; first by rewrite scaler0.
by rewrite !cons_poly_def IH // scalerDr scale_polyC scalerAl.
Qed.

Lemma ci_map2_plus l1 l2 l3: 
  size l1 = size l2 -> Poly (ci_map2 Cplus l1 l2 l3) = 
    Poly l1 + Poly l2 + 'X^ (size l1) * Poly l3.
Proof.
elim: l1 l2 => [|a1 l1 IH] [|a2 l2] //=; first by rewrite !add0r mul1r.
case => Hs.
rewrite !cons_poly_def IH // addrCA !addrA -mulrDl -addrA !rmorphD /=.
rewrite !mulrDl !addrA -addrA [Poly l2 * 'X + _]addrC -!addrA; congr (_ + _).
congr (_ + _).
rewrite addrC !addrA; congr (_ + _).
by rewrite mulrAC exprS ['X * _]mulrC.
Qed.

Lemma ci_map2_minus l1 l2 l3: 
  size l1 = size l2 -> Poly (ci_map2 Cminus l1 l2 l3) = 
    Poly l1 - Poly l2 + 'X^ (size l1) * Poly l3.
Proof.
elim: l1 l2 => [|a1 l1 IH] [|a2 l2] //=; first by rewrite subr0 add0r mul1r.
case => Hs.
rewrite !cons_poly_def IH // !mulrDl -!addrA; congr (_ + _).
rewrite -[in RHS]addrC opprD -mulNr -!addrA; congr (_ + _).
rewrite addrCA; congr (_ + _).
  by rewrite mulrAC exprS ['X * _]mulrC.
by rewrite rmorphB /= addrC.
Qed.

Lemma ci_map2_mult l1 l2 l3: 
  size l1 = size l2 -> Poly (ci_map2 Cmult l1 l2 l3) = 
  poly_mul (Poly l1) (Poly l2) + 'X^ (size l1) * Poly l3.
Proof.
elim: l1 l2 => [|a1 l1 IH] [|a2 l2] //=.
  by rewrite poly_mu0l add0r mul1r.
case => Hs.
rewrite !cons_poly_def IH // poly_mulaMx.
rewrite mulrDl -!addrA; congr (_ + _).
rewrite addrC; congr (_ + _).
by rewrite mulrAC exprS ['X * _]mulrC.
Qed.

Lemma polyD (R1 : ringType) (a b : nat) (E : nat -> R1): 
  \poly_(i < a + b) E i = 
  \poly_(i < a) E i + 'X^a * \poly_(i < b) E (a + i)%nat.
Proof.
rewrite !poly_def.
elim: b => [|b IH].
  by rewrite addn0 big_ord0 mulr0 addr0.
rewrite addnS !big_ord_recr /= IH mulrDr !addrA; congr (_ + _ + _).
by rewrite -!mul_polyC exprD mulrA [_ * 'X^a]commr_polyXn mulrA.
Qed.

Lemma c_fft_correct n l1 (w : C) : 
  (2 ^ n).-primitive_root w -> Poly (c_fft n l1 w) = fft n w (Poly l1).
Proof.
elim: n l1 w => [|n IH] l1 w Hw /=.
  by rewrite cons_poly_def mul0r add0r /= coef_Poly.
have wwE := prim_sqr Hw.
have -> : w * w = w ^+2 by [].
rewrite ci_map2_plus; last first.
  by rewrite !(size_c_fft, size_ci_map2, size_ci_pow, minnn, addn0).
rewrite ci_map2_mult; last first.
  by rewrite size_ci_pow !size_c_fft.
rewrite IH // ci_even_correct.
rewrite ci_pow_correct.
rewrite mulr0 addr0.
rewrite ci_map2_minus //; last first.
  by rewrite size_c_fft size_ci_map2 size_ci_pow !size_c_fft minnn addn0.
rewrite size_c_fft !IH // ci_map2_mult; last first.
  by rewrite size_ci_pow !size_c_fft.
rewrite !mulr0 !addr0 ci_even_correct ci_pow_correct.
rewrite size_c_fft IH // ci_odd_correct.
have -> : (2 ^ n.+1 =  2 ^ n + 2 ^ n)%nat by rewrite expnS mul2n addnn.
rewrite polyD; congr (_ + _).
  apply/polyP => i.
  rewrite !coefE.
  case: (ltnP i (2 ^ n)) => [iL2n|nLi].
    rewrite modn_small //.
    congr (_ + _).
    case: ltnP; first by rewrite mulrC.
    rewrite geq_min => /orP[/leq_sizeP|/leq_sizeP->//]; last by rewrite mul0r.
    by move=> /(_ i (leqnn _)); rewrite coef_poly iL2n => ->; rewrite mulr0.
  rewrite mul0r if_same addr0.
  by have /leq_sizeP-> := 
        leq_trans (size_fft n (w ^+2) (even_poly (Poly l1))) nLi.
congr (_ * _).
apply/polyP => i.
rewrite !coefE.
case: (ltnP i (2 ^ n)) => [iL2n|nLi]; last first.
  rewrite ifN.
    by rewrite subr0 (leq_sizeP _ _ (leq_trans (size_fft _ _ _) nLi)).
  by rewrite -leqNgt geq_min (leq_trans _ nLi) // size_poly.
rewrite modnDl modn_small // exprD prim_exp2nS // mulN1r mulrN.
congr (_ - _).
case: ltnP; first by rewrite mulrC.
rewrite geq_min => /orP[/leq_sizeP|/leq_sizeP->//]; last by rewrite mul0r.
by move=> /(_ i (leqnn _)); rewrite coef_poly iL2n => ->; rewrite mulr0.
Qed.

Fixpoint ci_fft (n : Datatypes.nat) (l1 : seq CItype) (w : CItype) : 
    seq CItype := 
  if n is n1.+1 then 
  let w2 := CIsqr w in 
  let e := ci_fft n1 (ci_even l1) w2 in 
  let o := ci_fft n1 (ci_odd l1) w2 in 
  let p := ci_pow (CImul w)%C e CI1 in 
  let o1 := ci_map2 CImul p o [::] in 
  ci_map2 CIadd e o1 (ci_map2 CIsub e o1 [::]) 
  else [:: nth CI0 l1 0%N].

Definition lCcontains (l1 : seq C) l2 := 
 size l1 = size l2 /\
 (forall i, (i < size l1)%nat -> nth 0%RR l1 i \Ccontained_in nth CI0 l2 i).

Notation "l1 '\lCcontained_in' l2" := 
  (lCcontains l1 l2) (at level 20).

Lemma lCcontains_nil : [::] \lCcontained_in [::].
Proof. by split. Qed.

Lemma lCcontains_cons a1 a2 l1 l2 :
  a1 \Ccontained_in a2 ->  l1 \lCcontained_in l2 -> 
  (a1 :: l1) \lCcontained_in (a2 :: l2).
Proof.
move=> Ha1al2 [Hs Hl1l2]; split => [|[|i Hi]] //=; first by rewrite Hs.
by apply: Hl1l2.
Qed.

Lemma lCcontains_consl a1 a2 l1 l2 :
 (a1 :: l1) \lCcontained_in (a2 :: l2) -> a1 \Ccontained_in a2.
Proof. by move=> [] [_ /(_ 0 isT)]. Qed.

Lemma lCcontains_consr a1 a2 l1 l2 :
 (a1 :: l1) \lCcontained_in (a2 :: l2) -> l1 \lCcontained_in l2.
Proof. by move=> [] /= [Hs] Hl; split => // i Hi; apply: (Hl i.+1). Qed.

Lemma lCcontains_odd l1 l2 :
  l1 \lCcontained_in l2 -> ci_odd l1 \lCcontained_in ci_odd l2.
Proof.
elim: (size _).+1 {-2}l1 l2 (leqnn (size l1).+1) => // n IH [|a1 [| b1 {}l1]].
- by case => // ? ? _ [].
- case => [|a2 [|b2 l2]]; first by move=> _ [].
    by move => _ _; apply: lCcontains_nil.
  by move=> _ [].
case => [|a2 [|b2 l2]]; first by move=> _ [].
  by move=> _ [].
move => Hs Hl1l2; rewrite ![ci_odd (_ :: _)]/=.
apply: lCcontains_cons.
  by apply: lCcontains_consl (lCcontains_consr Hl1l2).
apply: IH; first by rewrite -ltnS; apply: ltnW.
by apply: lCcontains_consr (lCcontains_consr Hl1l2).
Qed.

Lemma lCcontains_even l1 l2 :
 l1 \lCcontained_in l2 -> ci_even l1 \lCcontained_in ci_even l2.
Proof.
case: l1 => [|a1 l1]; rewrite ![ci_even _]/=; first by case: l2 => // ? ? [].
case: l2 => [|a2 l2 Hl1l2]; first by case.
apply: lCcontains_cons; first by apply: lCcontains_consl Hl1l2.
by apply/lCcontains_odd/(lCcontains_consr Hl1l2).
Qed.

Fixpoint onlyOnelC l :=
  if l is (a1 :: l1) then 
    if onlyOneC a1 is Some b1 then 
      if onlyOnelC l1 is Some m1 then Some (b1 :: m1) else None   
    else None
  else Some [::].

Definition isZC i := exists zl, [seq RtoC (IZR z) | z <- zl]  = i.

Lemma onlyOnelC_correct i (zl : seq Z) zl1 : 
  onlyOnelC i = Some zl -> isZC zl1 -> zl1 \lCcontained_in i -> 
  zl1 = [seq RtoC (IZR z) | z <- zl].
Proof.
move=> Ho []l {zl1}<- Hc; suff -> : l = zl by []; apply: sym_equal.
elim: i zl l Ho Hc => //= [|c i IH zl zl1].
  by case => [|a zl] [|b zl1] //= _ [].
case E : onlyOneC => [z|//].
case E1 : onlyOnelC => [zl2|//].
case=> <-; case: zl1 => [[]//|b zl1 /=] Hc.
congr (_ :: _).
  apply: onlyOneC_correct E _.
  by apply: lCcontains_consl Hc.
apply: IH => //.
by apply: lCcontains_consr Hc.
Qed.

Lemma lCIpow_correct (A B : Type) (l1 : seq A) (l2 : seq B) x1 x2 f1 f2 :
  size l1 = size l2 ->
  (forall x1 x2, 
     x1 \Ccontained_in x2 -> f1 x1 \Ccontained_in f2 x2) -> 
  x1 \Ccontained_in x2 ->
  ci_pow f1 l1 x1 \lCcontained_in ci_pow f2 l2 x2.
Proof.
move=> Hs Hf.
elim: l1 l2 x1 x2 Hs => [|a1 l1 IH]; first by case.
case=> // a2 l2.
move=> x1 x2 [Hs] Hx1x2 /=; apply: lCcontains_cons => //.
apply: IH => //.
by apply: Hf.
Qed.

Lemma CImap_correct l1 l2 f1 f2 :
  (forall x Ix, x \Ccontained_in Ix -> f1 x \Ccontained_in f2 Ix) ->
  l1 \lCcontained_in l2-> 
  [seq f1 i | i <- l1] \lCcontained_in [seq f2 i | i <- l2].
Proof.
move=> Hf.
elim: l1 l2 => [|a1 l1 IH] [|a2 l2] [] //= [Hs] Hf1.
apply: lCcontains_cons.
apply: Hf; first by have /= := Hf1 0 isT.
apply: IH; split => // i Hi.
by apply: (Hf1 i.+1).
Qed.

Lemma CImap2_correct l1 l2 l3 l4 l5 l6 f1 f2 :
  (forall x1 Ix1 x2 Ix2, 
     x1 \Ccontained_in Ix1 -> x2 \Ccontained_in Ix2 -> 
     f1 x1 x2 \Ccontained_in f2 Ix1 Ix2) ->
  l1 \lCcontained_in l4 -> l2 \lCcontained_in l5 -> l3 \lCcontained_in l6 -> 
  ci_map2 f1 l1 l2 l3 \lCcontained_in ci_map2 f2 l4 l5 l6.
Proof.
move=> Hf.
elim: l1 l2 l4 l5 => [|a1 l1 IH] l2 l4 l5.
  by case: l4 => //= ? ? [].
case: l4 => [|a2 l4]; first by case.
move=> Hl1l4; case: l2 => [|b1 l2 //].
  by case: l5 => [|b2 l5]; case.
case: l5 => [|b2 l5 Hl2l5 Hl3l6 /=]; first by case.
apply: lCcontains_cons.
  apply: Hf; first by apply: lCcontains_consl Hl1l4.
  by apply: lCcontains_consl Hl2l5.
apply: IH => //; first by apply: lCcontains_consr Hl1l4.
by apply: lCcontains_consr Hl2l5.
Qed.

Definition z2i (n : nat) : 'I_n -> 'Z_n -> 'I_n := 
  if n is n'.+1 return 'I_n -> 'Z_n -> 'I_n 
  then fun _ => inZp else fun v => fun _ => v.


Lemma CIfft_correct n l1 l2 w1 w2 :
  l1 \lCcontained_in l2 -> w1 \Ccontained_in w2 -> 
  c_fft n l1 w1 \lCcontained_in ci_fft n l2 w2.
Proof.
elim: n l1 l2 w1 w2 => [|n IH] l1 l2 w1 w2 Hl1l2 Hw1 /=.
  case: l1 Hl1l2 => [|a l1]; case: l2 => //=.
  - by move=> _; split => // [] [] // _; apply: CI0_correct.
  - by move=> ? ? [].
  - by case.
  by move=> b l2 [_ /(_ 0) Hl2]; split => // [] [].
have Hw : 
  c_fft n (ci_even l1) (w1 * w1)%RR \lCcontained_in
  ci_fft n (ci_even l2) (CIsqr w2).
  apply: IH; first by apply: lCcontains_even.
  by apply: CIsqr_correct.
apply: CImap2_correct.
- by move=> x1 Ix1 x2 Ix2; apply: CIadd_correct.
- apply: IH; first by apply: lCcontains_even.
  by apply: CIsqr_correct.
- apply: CImap2_correct => //.
  - by move=> x1 Ix1 x2 Ix2; apply: CImul_correct.
  - apply: lCIpow_correct => //.
    - by case Hw.
    - by move=> x1 x2 Hx1x2; apply: CImul_correct.
  by apply: CI1_correct.
  apply: IH; first by apply: lCcontains_odd.
  by apply: CIsqr_correct.
apply: CImap2_correct => //.
  by move=> x1 Ix1 x2 Ix2; apply: CIsub_correct.
apply: CImap2_correct => //.
- by move=> x1 Ix1 x2 Ix2; apply: CImul_correct.
- apply: lCIpow_correct => //.
  - by case: Hw.
  - by move=> x1 x2 Hx1x2; apply: CImul_correct.
  by apply: CI1_correct.
apply: IH; first by apply: lCcontains_odd.
by apply: CIsqr_correct.
Qed.

Definition c_ifft  (n : Datatypes.nat) (l1 : seq C) (w : C) : seq C := 
  let s := RtoC (/ pow 2 n) in 
  let w1 := Cinv w in 
  let l2 := c_fft n l1 w1 in [seq (s * i) | i <- l2].

Lemma Cpow_ring (a : C) n : (a ^ n)%C = (a ^+ n).
Proof. by elim: n => /= [|n ->]; [rewrite expr0 | rewrite exprS]. Qed.

Lemma RtoC_IZR n : (RtoC (IZR (Z.of_nat n))) = n%:R.
Proof.
elim: n => //= n IH.
by rewrite Zpos_P_of_succ_nat succ_IZR RtoC_plus IH -natr1.
Qed.

Lemma prim_neq0 (R :ringType) n (w : R) :
  (0 < n)%nat -> n.-primitive_root w -> w != 0.
Proof.
move=> n_pos /prim_expr_order; case : (w =P 0) => // ->.
rewrite expr0n; case: n n_pos => //= n _ /eqP.
by rewrite eq_sym oner_eq0.
Qed.

Lemma Cinv_ring (c : C) : (/ c)%C = (c ^-1)%R.
Proof.
rewrite /GRing.inv /= /Cinvx; case: eqP => //= ->.
by rewrite /Cinv /= Rmult_0_l Ropp_0 !Rdiv_0_l.
Qed.

Lemma prim_Cexp1 n : (0 < n)%nat -> n.-primitive_root (Croot n).
Proof.
move=> n_pos; apply/andP; split => //.
apply/forallP => /= x.
rewrite /root_of_unity /root !hornerE -Cpow_ring.
apply/eqP; apply/idP/idP; last first.
  by move=> /eqP->; apply/eqP; rewrite Croot_expn subrr.
move=> /eqP Hc; apply/eqP.
have Hc' :  (Croot n ^ x.+1 = 1)%C by rewrite -[LHS](subrK 1) Hc add0r.
by apply: Croot_expn_eq1 Hc' => /=.
Qed.

Lemma c_ifft_correct n l1 (w : C) :
 (2 ^ n).-primitive_root w -> Poly (c_ifft n l1 w) = ifft n w (Poly l1).
Proof.
move=> Hw; rewrite /ifft /c_ifft ci_map_scal mul_polyC; congr (_ *: _).
  have Hp : (2 ^ n <> 0)%R by apply: pow_nonzero; lra.
  rewrite natrX RtoC_inv //.
  rewrite RtoC_pow /GRing.inv /= /Cinvx ifT; last first.
    suff Hf : (2 != 0 :> C) by rewrite expf_eq0 (negPf Hf) andbF.
    by apply/eqP => [] /eqP/andP[/= /eqP]; lra.
  by rewrite Cpow_ring (RtoC_IZR 2).
rewrite c_fft_correct.
  rewrite /GRing.inv /= /Cinvx ifT //.
  by apply: prim_neq0 Hw; apply: expn_gt0.
by rewrite Cinv_ring; apply: primJ.
Qed.

Definition ci_ifft (n : Datatypes.nat) (l1 : seq CItype) (w : CItype) : 
    seq CItype := 
  let s := CIinv (mkCI (mkIz (two_power_nat n)) (mkIz 0)) in 
  let w1 := CIinv w in 
  let l2 := ci_fft n l1 w1 in [seq (CImul s i) | i <- l2].

Lemma RtoC_inv (x : R) : RtoC (/ x) = (/ RtoC x)%C.
Proof.
case (Req_dec x 0); intros Hx.
  by rewrite Hx; apply injective_projections; simpl;
     rewrite !(Ropp_0, Rdiv_0_l, Rinv_0).
by apply injective_projections ; simpl; field.
Qed.

Lemma CIifft_correct n l1 l2 w1 w2 :
  l1 \lCcontained_in l2 -> w1 \Ccontained_in w2 -> 
  c_ifft n l1 w1 \lCcontained_in ci_ifft n l2 w2.
Proof.
move=> Hl1l2 Hw1Hw2; apply: CImap_correct.
  move=> x Ix HxIx; apply: CImul_correct => //.
  rewrite RtoC_inv; apply: CIinv_correct.
  split; last by apply: I.fromZ_correct.
  rewrite two_power_nat_equiv pow_IZR.
  by apply: I.fromZ_correct.
apply: CIfft_correct => //.
by apply: CIinv_correct.
Qed.

Definition c_poly_mul (l1 l2 : seq C) := ci_map2 Cmult l1 l2 [::].

Lemma c_poly_mul_correct l1 l2 :
 Poly (c_poly_mul l1 l2) = poly_mul (Poly l1) (Poly l2).
Proof.
elim: l1 l2 => [l2|a1 l1 IH [|a2 l2]] /=; first by rewrite poly_mu0l.
  by rewrite poly_mul0.
by rewrite IH !cons_poly_def poly_mulaMx.
Qed.

Definition ci_poly_mul (l1 l2 : seq CItype) := ci_map2 CImul l1 l2 [::].

Lemma ci_poly_mul_correct l1 l2 l3 l4 :
  l1 \lCcontained_in l2 -> l3 \lCcontained_in l4 -> 
  c_poly_mul l1 l3 \lCcontained_in ci_poly_mul l2 l4.
Proof.
elim: l1 l2 l3 l4 => [[|? ?] ? ? []//|a1 l1 IH [|a2 l2]].
  by move=> ? ? [].
case => [|a3 l3] [|a4 l4] //=; first by move=> _ [].
  by move=> _ [].
move=> Hl1l2 Hl3l4.
rewrite /c_poly_mul /ci_poly_mul /=.
apply: lCcontains_cons.
  apply: CImul_correct; first by apply: lCcontains_consl Hl1l2.
  by apply: lCcontains_consl Hl3l4.
apply: IH; first by apply: lCcontains_consr Hl1l2.
by apply: lCcontains_consr Hl3l4.
Qed.
  
Definition c_fft_mul n (l1 l2 : seq C) (w : C) := 
  let l1' :=  c_fft n l1 w in
  let l2' :=  c_fft n l2 w in
  c_ifft n (c_poly_mul l1' l2') w.

Lemma c_fft_mul_correct n l1 l2 w : (2 ^ n).-primitive_root w ->
 Poly (c_fft_mul n l1 l2 w) = fft_mul n w (Poly l1) (Poly l2).
Proof.
move=> Hr.
by rewrite /c_fft_mul /fft_mul c_ifft_correct //
           c_poly_mul_correct !c_fft_correct.
Qed.

Definition ci_fft_mul n (l1 l2 : seq CItype) (w : CItype) := 
  let l1' :=  ci_fft n l1 w in
  let l2' :=  ci_fft n l2 w in
  ci_ifft n (ci_poly_mul l1' l2') w.

Lemma ci_fft_mul_correct n l1 l2 l3 l4 w1 w2 :
  l1 \lCcontained_in l2 -> l3 \lCcontained_in l4 ->
  w1 \Ccontained_in w2 -> 
  c_fft_mul n l1 l3 w1 \lCcontained_in ci_fft_mul n l2 l4 w2.
Proof.
move=> Hl1l2 Hl3l4 Hw1w2.
apply: CIifft_correct => //.
by apply: ci_poly_mul_correct; apply: CIfft_correct.
Qed.

Definition CI_root n : CItype := 
  let n1 := mkIz (two_power_nat n) in 
  let v2pi := scl2 pi in 
  let v := div v2pi n1 in (I.cos prec v, I.sin prec v).

Lemma CI_root_correct n : Croot (2 ^ n) \Ccontained_in CI_root n.
Proof.
have Hf : 
  (2 * PI / INR (2 ^ n)) \contained_in div (scl2 pi) (mkIz (two_power_nat n)).
  apply: div_correct.
    have <- : (PI *+ 2 = 2 * PI)%R by rewrite mulr2n /GRing.add /=; lra.
    by apply/scl2_correct/I.pi_correct.
  have -> : INR (2 ^ n) = IZR (two_power_nat n).
    by rewrite two_power_nat_equiv -pow_expn pow_INR -pow_IZR.
  by apply: I.fromZ_correct.
split.
  by apply: (@I.cos_correct prec _ (Xreal (2 * PI / INR (2 ^ n)))).
by apply: (@I.sin_correct prec _ (Xreal (2 * PI / INR (2 ^ n)))).
Qed.

Definition ci_fft_xmul n l1 l2 := ci_fft_mul n l1 l2 (CI_root n).

End Complex_intervals.

End Complex_interval.


Module V := Complex_interval SFBI2.

Export V.

From Bignums Require Import BigZ.

Definition prec := 53%bigZ.

Definition mkfZ z := mkCI (mkIz prec z) (mkIz prec 0).

Compute onlyOnelC prec 
  (ci_fft_xmul prec 3%nat [:: mkfZ (-1); mkfZ 0; mkfZ 1] [:: mkfZ 0; mkfZ (-2); mkfZ 1]).

Definition mylog (n : nat) := (Nat.log2 (n.-1)).+1.

Lemma mylog_correct n : (n <= 2 ^ mylog n)%nat.
Proof.
case: n => // [] [|n] //.
rewrite /mylog /= -pow_expn.
have [] := Nat.log2_spec n.+1; first by apply/ltP.
by move => _ /ltP.
Qed.

Require Import upoly.

Fixpoint lzplus (l1 l2 : seq Z) := 
  if l1 is a1 :: l3 then
  if l2 is a2 :: l4 then (a1 + a2)%Z :: lzplus l3 l4  
  else l1 else l2.

Definition z2int (z : Z) : int := 
  if z is 0%Z then 0 else 
  if z is Z.pos a then Posz (Z.to_nat z) else (- (Posz (Z.to_nat (-z)))).

Definition int2z (z : int) : Z := 
  if z is Posz _ then Z.of_nat (`|z|) else - Z.of_nat (`|z|).

Lemma z2intN z : z2int (- z) = - (z2int z).
Proof. by case: z => //= p; rewrite opprK. Qed. 

Lemma z2intD z1 z2 : z2int (z1 + z2) = z2int z1 + z2int z2.
Proof.
wlog z1_pos : z1 z2 / (0 <= z1)%Z => [Hf|].
  case: (Z_le_dec 0 z1) => [/Hf->//|z1_neg].
  have -> : (z1 + z2 = - ((- z1) + (-z2)))%Z by lia.
  by rewrite !(z2intN, Hf, opprD, opprK) //; lia.
elim/Wf_Z.natlike_ind : z1_pos z2 => [z2 |z3 z3_pos IH z2].
  by rewrite Zplus_0_l !add0r.
have F z : z2int (Z.succ z) = z2int z + 1.
  suff G t : z2int (Z.succ t) = z2int t  + 1 /\ z2int (Z.pred t) = z2int t  - 1.
    by case: (G z).
  wlog t_pos : t / (0 <= t)%Z => [Hft|].
  case: (Z_le_dec 0 t) => [/Hft//|t_neg].
    have -> : (Z.succ t = - (Z.pred (- t)))%Z by lia.
    have -> : (Z.pred t = - (Z.succ (- t)))%Z by lia.
    rewrite !z2intN;   case: (Hft (-t)%Z) => [|-> ->]; first by lia.
    by rewrite !z2intN !opprD !opprK.
  case: t t_pos => // p _; split; first by rewrite /= Pos2Nat.inj_add.
  case : (Pos.eq_dec p 1) => [->//|p_neq1].
  rewrite -Pos2Z.inj_pred //= Pos2Nat.inj_pred; last by lia.
  have : (0 < Pos.to_nat p)%nat by apply/ltP/Pos2Nat.is_pos.
  case : Pos.to_nat => //= k _.
  by rewrite intS [(1 + _)]addrC addrK.
have -> : (Z.succ z3 + z2 = z3 + Z.succ z2)%Z by lia.
by rewrite IH !F // addrAC addrA.
Qed.

Lemma z2intM z1 z2 : z2int (z1 * z2) = z2int z1 * z2int z2.
Proof.
wlog z1_pos : z1 z2 / (0 <= z1)%Z => [Hf|].
  case: (Z_le_dec 0 z1) => [/Hf->//|z1_neg].
  have -> : (z1 * z2 = ((- z1) * (-z2)))%Z by lia.
  by rewrite !(z2intN, Hf, opprD, opprK, mulrN, mulNr) //; lia.
elim/Wf_Z.natlike_ind : z1_pos z2 => [z2 |z3 z3_pos IH z2].
  by rewrite Zmult_0_l !mul0r.
have -> : (Z.succ z3 * z2 = z3 * z2 + z2)%Z by lia.
have -> : (Z.succ z3 = z3  + 1)%Z by lia.
by rewrite !(z2intD, IH) mulrDl mul1r.
Qed.

Lemma int2zK : cancel int2z z2int.
Proof.
case; elim => //= n IH; first by rewrite SuccNat2Pos.id_succ.
rewrite Pos2Nat.inj_succ; rewrite !NegzE in IH *.
by have [->] /= := oppr_inj IH.
Qed.

Lemma z2intK : cancel z2int int2z.
Proof.
case=> //= p; first by rewrite positive_nat_Z.
rewrite -[in RHS](Pos2Nat.id p).
have : (0 < Pos.to_nat p)%nat by apply/ltP/Pos2Nat.is_pos.
by case : Pos.to_nat => //= [] [|n] _ //; rewrite Pos.succ_of_nat.
Qed.

Lemma int2zN z : int2z (- z) = (- (int2z z))%Z.
Proof. by apply: (can_inj z2intK); rewrite z2intN !int2zK. Qed.

Lemma int2zD z1 z2 : int2z (z1 + z2) = (int2z z1 + int2z z2)%Z.
Proof. by apply: (can_inj z2intK); rewrite z2intD !int2zK. Qed.

Lemma int2zM z1 z2 : int2z (z1 * z2) = (int2z z1 * int2z z2)%Z.
Proof. by apply: (can_inj z2intK); rewrite z2intM !int2zK. Qed.

Definition zPoly l : {poly int} := Poly [seq z2int i | i <- l].

Lemma zPoly_cons a l : zPoly (a :: l) = (z2int a)%:P + zPoly l * 'X.
Proof. by rewrite /zPoly /= cons_poly_def addrC. Qed.

Lemma zPoly_nil : zPoly [::] = 0.
Proof. by []. Qed.

Lemma zPoly_cons1 a : zPoly [:: a] = (z2int a)%:P.
Proof. by rewrite zPoly_cons zPoly_nil mul0r addr0. Qed.

Lemma lzplus_correct l1 l2 : zPoly (lzplus l1 l2) = zPoly l1 + zPoly l2.
Proof.
elim: l1 l2 => [|a1 l1 IH] [|a2 l2] //=; try by rewrite !(addr0, add0r).
rewrite !zPoly_cons IH z2intD rmorphD mulrDl /= -!addrA; congr (_ + _)%RR.
by rewrite addrC -!addrA; congr (_ + _)%RR; rewrite addrC.
Qed.
  
Fixpoint pexpr2lZ (e : pexpr) :=
match e with
| Pcons a => Some [:: Z.of_nat a]
| Pxn n => Some ((nseq n 0%Z) ++ [::1%Z])
| Px => Some [::0%Z; 1%Z]
| Popp p => 
   if pexpr2lZ p is Some l1 then Some [seq (- i)%Z | i <- l1]
   else None
| Padd p1 p2 => 
  if pexpr2lZ p1 is some l1 then 
  if pexpr2lZ p2 is some l2 then Some (lzplus l1 l2)
  else None
  else None 
| Pmult p1 p2 => 
  if pexpr2lZ p1 is some l1 then 
  if pexpr2lZ p2 is some l2 then
    let n := mylog ((size l1 + size l2).-1) in
    let l3 := [seq (mkfZ i) | i <- l1] in 
    let l4 := [seq (mkfZ i) | i <- l2] in 
     onlyOnelC prec (ci_fft_xmul prec n l3 l4)
  else None
  else None 
end.

Lemma s2int_of_nat n : z2int (Z.of_nat n) = n%:R.
Proof.
elim: n => // n IH.
have -> : (Z.of_nat n.+1  = Z.of_nat n + 1)%Z by lia.
by rewrite z2intD -natr1 IH.
Qed.

Lemma zPolyN l : zPoly [seq (- i)%Z  | i <- l] = - zPoly l.
Proof.
elim: l => /= [|a l IH]; first by rewrite !zPoly_nil oppr0.
by rewrite !zPoly_cons IH z2intN opprD rmorphN mulNr.
Qed.

Definition mkZ (z : Z) : C := (IZR z, 0).

Lemma mkZ_contains l : 
  lCcontains [seq mkZ i  | i <- l] [seq mkfZ i  | i <- l].
Proof.
elim: l => //= a l IH; apply: lCcontains_cons => //.
by split; apply: I.fromZ_correct.
Qed.

Lemma leq_pred m n : (m <= n -> m.-1 <= n.-1)%nat.
Proof. by case: m; case: n. Qed.

Lemma isZC_nil : isZC [::].
Proof. by exists [::]. Qed.

Lemma IZR_int2z x : IZR (int2z x) = x%:~R :> C.
case: x => /=.
  elim => //= n IH.
  by rewrite Zpos_P_of_succ_nat succ_IZR RtoC_plus IH intS rmorphD /= addrC.
elim => //= [|n IH].
  by apply/eqP/andP; split; rewrite /= -opp_IZR.
rewrite IZR_NEG /= Pos2Z.inj_succ succ_IZR Ropp_plus_distr -IZR_NEG.
rewrite RtoC_plus IH !NegzE !intS !rmorphN /= !rmorphD /=.
rewrite !opprD [RHS]addrC; congr (_ + _).
by rewrite RtoC_opp.
Qed.

Lemma isZC_cons a l : isZ a -> isZC l -> isZC (a :: l).
Proof.
by move=> [x ->] [l1 <-]; exists (int2z x :: l1); rewrite /=  IZR_int2z.
Qed.

Lemma isZC_Poly l : isZPoly (Poly l) -> isZC l.
Proof.
elim: l => [|a l IH] Hp; first by apply: isZC_nil.
apply: isZC_cons; first by apply: isZPoly_Poly_consl Hp.
by apply/IH/(isZPoly_Poly_consr Hp).
Qed.

Lemma isZC_consl a l : isZC (a :: l) -> isZ a.
Proof.
by case=> [] [|b l1]//= [<- _]; exists (z2int b); rewrite -IZR_int2z z2intK.
Qed.

Lemma isZC_consr a l : isZC (a :: l) -> isZC l.
Proof. by case=> [] [|b l1]//= [_ <-]; exists l1. Qed.


Lemma isZPoly_Poly l : isZC l -> isZPoly (Poly l).
Proof.
elim: l => [|a l IH] Hp /=; first by apply: (isZPoly_polyC _ 0).
rewrite cons_poly_def.
apply: isZPolyD; last first.
  have [b ->] := isZC_consl Hp.
  by exists [::b]; rewrite /int2Poly /= cons_poly_def mul0r add0r.
apply: isZPolyM; first by apply/IH/(isZC_consr Hp).
by apply: isZPoly_polyX.
Qed.

Lemma pexpr2lZ_correct e l : pexpr2lZ e = Some l -> pexpr2poly int e = zPoly l.
Proof.
elim: e l => /= [a l [<-]|n l [<-]| l [<-]|p IH l|p1 IH1 p2 IH2 l|
    p1 IH1 p2 IH2 l].
- by rewrite zPoly_cons1 -polyC_natr s2int_of_nat.
- elim: n => //= [|n IH]; first by rewrite zPoly_cons1.
  by rewrite zPoly_cons add0r -IH mulrC exprS.
- by rewrite zPoly_cons zPoly_cons1 add0r mul1r.
  case: pexpr2lZ IH => // l1 /(_ l1 (refl_equal _)) -> [<-].
  by rewrite zPolyN.
- case: pexpr2lZ IH1 => // l1 /(_ l1 (refl_equal _)) ->.
  case: pexpr2lZ IH2 => // l2 /(_ l2 (refl_equal _)) -> [<-].
  by rewrite lzplus_correct.
case: pexpr2lZ IH1 => // l1 /(_ l1 (refl_equal _)) ->.
case: pexpr2lZ IH2 => // l2 /(_ l2 (refl_equal _)) -> /onlyOnelC_correct.
set n := mylog _.
have H2 := 
  ci_fft_mul_correct prec n (mkZ_contains l1) (mkZ_contains l2) 
    (CI_root_correct prec n).
rewrite /ci_fft_xmul => /(_ _ _ H2).
have H3 : (0 < 2 ^ n)%nat by apply: expn_gt0.
have H4 := @c_fft_mul_correct n [seq mkZ i  | i <- l1] [seq mkZ i  | i <- l2] 
              _ (prim_Cexp1 H3).
rewrite fft_mul_correct // in H4; last 3 first.
- by apply/negP => [] /andP[/eqP]; rewrite /= /GRing.add; lra.
- apply: leq_trans (leq_pred _) (mylog_correct _).
  by apply: leq_add; apply: leq_trans (size_Poly _) _; rewrite size_map.
- by apply: prim_Cexp1.
set fmul := c_fft_mul _ _ _ _ in H4 *.
have isZf : isZC fmul.
  apply: isZC_Poly; rewrite H4.
  apply: isZPolyM; apply: isZPoly_Poly; first by exists l1.
  by exists l2.
move=> /(_ isZf) fmulE.
rewrite fmulE in H4.
rewrite /zPoly.
have /= := @ptransferM (GRing.Ring.clone _ C) (GRing.Ring.clone _ int) Cchar.
have F x : Poly [seq z2int i  | i <- x] = int2Poly _ [seq z2int i  | i <- x].
  elim: x => //= x xl IH.
  rewrite cons_poly_def int2Poly_cons IH addrC mulrC; congr (_ + _).
  rewrite -polyC_intr; congr (_%:P).
  suff K n1 : n1 = n1 %:~R :> int by case: x.
  elim: n1 => //= n1 IH1.
    by rewrite -addn1 !rmorphD /= -IH1.
  by rewrite !rmorphN /= -addn1 !rmorphD /= !opprD -!rmorphN /= -IH1.
rewrite !F.
apply.
have G x : Poly [seq mkZ i  | i <- x] = int2Poly C [seq z2int i  | i <- x].
  elim: x => //= x xl IH.
  rewrite cons_poly_def int2Poly_cons IH addrC mulrC; congr (_ + _).
  rewrite -polyC_intr; congr (_%:P).
  suff -> : (z2int x)%:~R = RtoC (IZR (int2z (z2int x))) by rewrite z2intK.
  suff K n1 : n1%:~R = IZR (int2z n1) :> C by case: z2int.
  elim: n1 => // n1 IH2.
    by rewrite -addn1 !rmorphD int2zD !plus_IZR !RtoC_plus -IH2.
  rewrite int2zN -[in RHS]addn1 rmorphD int2zD Z.opp_add_distr -int2zN.
  rewrite plus_IZR !RtoC_plus -IH2 rmorphN -addn1 !rmorphD /= opprD.
  by rewrite RtoC_opp rmorphN.
by rewrite -!G.
Qed.


Lemma natr_int (n : nat) : n%:R = n.
Proof.
elim: n => //= n IH1.
by rewrite -addn1 !rmorphD /= IH1.
Qed.

Lemma natz_int z : z%:~R = z.
Proof.
have F (n : nat) : n%:~R = n :> int.
  elim: n => //= n IH1.
  by rewrite -addn1 !rmorphD /= IH1.
case: z => // n.
by rewrite NegzE rmorphN /= F.
Qed.

Lemma zPoly_int2Poly l : zPoly l = int2Poly int [seq z2int i | i <- l].
Proof.
elim: l => //= a l IH.
rewrite zPoly_cons int2Poly_cons mulrC IH; congr (_ + _).
apply/polyP => i; rewrite !(coefE, coefMrz); case: eqP => //= _.
  by rewrite [RHS]natz_int.
by rewrite mul0rz.
Qed.

Fixpoint lzisZ (l : seq Z) : bool :=
  if l is a :: l then 
  if a is 0%Z then lzisZ l else false 
  else true.

Lemma lzisZ_correct R l : lzisZ l -> int2Poly R [seq z2int i  | i <- l] = 0.
Proof.
elim: l => /= [|a l IH]; first by rewrite int2Poly_nil.
case: a => //; rewrite ?int2Poly_cons.
by move=> /IH->; rewrite add0r mulr0.
Qed.

Definition z2P (R : ringType) (a : Z) (n : nat) : {poly R} := 
  if a is 0%Z then 0 else
  if a is (-1)%Z then 
    if n is n1.+1 then 
      if n1 is n2.+1 then (- 'X^ n) else (- 'X) 
    else (- 1) else
  if a is (1)%Z then 
    if n is n1.+1 then 
      if n1 is n2.+1 then 'X^ n else 'X 
    else 1 else
  let v := 
     if a is Zneg b then (-(Z.to_nat (- a))%:R) else ((Z.to_nat a)%:R) in
  if n is n1.+1 then 
    if n1 is n2.+1 then (v * 'X^ n) else (v * 'X) 
  else v.

Lemma z2P_correct R a n : z2P R a n = (z2int a) %:~R * 'X^n.
Proof.
rewrite /z2P; case: a => [|a|a]; first by rewrite mul0r.
  case: a => [p|p|].
  - by case: n => [|[|n]] //; rewrite mulr1.
  - by case: n => [|[|n]] //; rewrite mulr1.
  by case: n => [|[|n]] //; rewrite mul1r.
case: a => [p|p|].
- by case: n => [|[|n]] //; rewrite mulr1.
- by case: n => [|[|n]] //; rewrite ?mulr1 /= !rmorphN.
by case: n => [|[|n]] //; rewrite ?mulr1 /= !rmorphN //= mulNr mul1r.
Qed.
  
Fixpoint lz2Paux (R : ringType) (n: nat) (l : seq Z) : {poly R} :=
  if l is a :: l then 
    if a is 0%Z then lz2Paux R n.+1 l 
    else if lzisZ l then ((z2P R a n))%R 
    else (lz2Paux R n.+1 l + z2P R a n)
  else 0.

Lemma lz2Paux_correct R n l :
  lz2Paux R n l = int2Poly R [seq z2int i | i <- l] * 'X^n.
Proof.
elim: l n => /= [n|a l IH n]; first by rewrite int2Poly_nil mul0r.
case: a => [|p|p].
- by rewrite int2Poly_cons add0r -commr_polyX -mulrA -exprS -IH.
- case: lzisZ (@lzisZ_correct R l) => Hp.
    by rewrite z2P_correct int2Poly_cons Hp // mulr0 addr0.
  rewrite z2P_correct int2Poly_cons IH mulrDl addrC; congr (_ + _).
  by rewrite -commr_polyX -mulrA exprS.
case: lzisZ (@lzisZ_correct R l) => Hp.
  by rewrite z2P_correct int2Poly_cons Hp // mulr0 addr0.
rewrite z2P_correct int2Poly_cons IH mulrDl addrC; congr (_ + _).
by rewrite -commr_polyX -mulrA exprS.
Qed.

Definition lz2P R l := if l is some l then lz2Paux R 0 l else 0.

Lemma lz_correct R l : lz2P R (some l) = int2Poly R [seq z2int i | i <- l].
Proof. by rewrite /= lz2Paux_correct mulr1. Qed.

Definition v_ex := Pmult (Padd (Padd (Pxn 2) Px) (Pcons 1)) 
               (Padd (Pxn 2) (Popp (Pcons 1))).

Eval cbn delta [pexpr2poly v_ex] beta iota in
  pexpr2poly (GRing.Ring.clone _ C) v_ex.

Definition r_ex := Eval compute in pexpr2lZ v_ex.

Eval lazy delta [lz2P lz2Paux lzplus lzisZ  z2P r_ex Z.to_nat Pos.to_nat
    Pos.iter_op Init.Nat.add Z.opp size rev catrev predn] beta iota zeta in 
  lz2P (GRing.Ring.clone _ C) r_ex.

Eval lazy delta [lz2P lz2Paux lzplus lzisZ  z2P r_ex Z.to_nat Pos.to_nat
    Pos.iter_op Init.Nat.add Z.opp size rev catrev predn] beta iota zeta in 
  lz2P (GRing.Ring.clone _ C) r_ex.

Lemma pexpr2lZ_correct' R e l : 
  pexpr2lZ e = Some l -> pexpr2poly R e = lz2Paux R 0 l.
Proof.
move /pexpr2lZ_correct => Hr.
rewrite lz2Paux_correct mulr1.
rewrite zPoly_int2Poly in Hr.
apply: ptransferE Hr.
by move=> m n; rewrite !natz => [] [].
Qed.

Ltac getExpr term := 
match term with
| 0 => constr:(Pcons 0)
| 1 => constr:(Pcons 1)
| ((?a)%:R) => constr:(Pcons a)
| 'X^?n => constr:(Pxn n)
| 'X => constr:(Px)
| - ?X =>  let v := getExpr X in constr:(Popp v)
| ?X + ?Y => let p1 := getExpr X in
             let p2 := getExpr Y in constr:(Padd p1 p2)
| ?X * ?Y => let p1 := getExpr X in
             let p2 := getExpr Y in constr:(Pmult p1 p2)
end.

Ltac left_simpl := 
let H := fresh "H" in 
let vl := fresh "vl" in 
(match goal with 
| |- ?X = _ => 
  let e := getExpr X in
  let ll := eval compute in (pexpr2lZ e) in 
  match ll with 
  | Some ?l => have H := (@pexpr2lZ_correct' _ e l); pose vl := ll 
  | _ => idtac "Error in left_simpl"
  end
end); 
rewrite [LHS]H; [clear H vl|vm_cast_no_check (refl_equal vl)];
lazy delta [lz2P lz2Paux lzplus lzisZ  z2P Z.to_nat Pos.to_nat
    Pos.iter_op Init.Nat.add Z.opp size rev catrev predn] beta iota zeta.

Parameter R : ringType.
Axiom foo : forall P, P.

Goal ('X^2 + 'X + 2) * ('X^2 - 32 * 'X)  = 0 :> {poly R}.
left_simpl.
apply: foo.
Qed.

Goal ('X^2 - 'X^13) * ('X^2 - 1) * 'X^15 = 0 :> {poly C}.
left_simpl.
apply: foo.
Qed.

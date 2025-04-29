Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import String Rstruct Reals Cstruct Psatz Cmore.
From Bignums Require Import BigZ.
Require Import fftcv upoly. 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import Complex.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition prec := 12%bigZ.

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
  let ll := eval compute in (pexpr2lZ prec e) in 
  match ll with 
  | Some ?l => have H := (@pexpr2lZ_correct' prec _ e l); pose vl := ll 
  | _ => idtac "Error in left_simpl"
  end
end); 
rewrite [LHS]H; [clear H vl|vm_cast_no_check (refl_equal vl)];
lazy delta [lz2P lz2Paux lzplus lzisZ  z2P Z.to_nat Pos.to_nat
    Pos.iter_op Init.Nat.add Z.opp size rev catrev predn] beta iota zeta.

Parameter R : nzRingType.
Axiom foo : forall P, P.

Goal ('X^2 + 'X + 2) * ('X^2 - 32 * 'X)  = 0 :> {poly R}.
left_simpl.
apply: foo.
Qed.

Goal ('X^2 - 'X^13) * ('X^2 - 1) * 'X^15 = 0 :> {poly C}.
left_simpl.
apply: foo.
Qed.

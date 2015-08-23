(* Bibliotecas importadas *)

Require Import Arith.


(* Definição indutiva dos termos de L0 *)

Inductive term :=
 | zero   : term
 | succ   : term -> term
 | true   : term
 | false  : term
 | iszero : term -> term
 | pred   : term -> term
 | ifte   : term -> term -> term -> term 
.

(* Definição indutiva da propriedade de ser um número *)

Inductive nv : term -> Prop :=
 | zeroNum : nv zero
 | succNum : forall n, (nv n) -> (nv (succ n))
.

(* Definição indutiva de valor : números OU booleanos *)

Inductive value : term -> Prop :=
 | trueVal  : value true
 | falseVal : value false
 | numVal   : forall n, (nv n) -> (value n)
.

(* Testando termos *)
Check ifte false zero (succ zero).

(* Testando valores do tipo termo *)
Check value (iszero true).

(* Provando uma propriedade *)
Theorem teste1 : value (succ zero).
Proof.
constructor 3.
constructor 2.
constructor 1.
Qed.

(* Provando uma propriedade 2 *)
Theorem teste2 : value (succ zero).
Proof.
apply numVal.
apply succNum.
apply zeroNum.
Qed.


(* Provando uma propriedade negada *)
Lemma teste : ~ value (iszero true).
Proof.
unfold not.
intro H.
inversion H.
subst.
inversion H0.
Qed.







(*****************************************************************)






(* Definição da semântica operacional *)
Inductive step : term -> term -> Prop :=
 | e_iftrue     : forall t2 t3,        step (ifte true  t2 t3) t2
 | e_iffalse    : forall t2 t3,        step (ifte false t2 t3) t3
 | e_if         : forall t1 t2 t3 t1', (step t1 t1') -> step (ifte t1 t2 t3) (ifte t1' t2 t3)
 | e_succ       : forall t t',         step t t' -> step (succ t) (succ t')
 | e_predzero   :                      step (pred zero) zero
 | e_predsucc   : forall t,  (nv t) -> step (pred (succ t)) t
 | e_pred       : forall t t',         step t t' -> step (pred t) (pred t')
 | e_iszerozero :                      step (iszero zero) true
 | e_iszerosucc : forall t,  (nv t) -> step (iszero (succ t)) false
 | e_iszero     : forall t t',         step t t' -> step (iszero t) (iszero t')
.
 

(* Definição de forma normal *)

Definition NF (t:term) : Prop := forall t', not (step t t').





(*****************************************************************)



(* Exercício : TODO NV É FORMA NORMAL *)
Theorem nvNF : forall (t:term), nv t -> NF t.
Proof.
induction t.
intro. unfold NF. intro. unfold not. intro. inversion H0. (* zero *)  
intro. inversion H. subst. apply IHt in H1. unfold NF in H1.  intro. unfold not. intro. inversion H0. subst. unfold not in H1. apply (H1 t'0) in H3. assumption. (* succ *) 
intro. unfold NF. intro. intro. inversion H0. (* true *) 
intro. unfold NF. intro. intro. inversion H0. (* false *)
intro. inversion H. (* iszero *)
intro. inversion H. (* pred *)
intro. inversion H. (* ifte *)
Qed.



(* Exercício : TODO VALOR É FORMA NORMAL *)

Theorem valueNF : forall (t:term), value t -> NF t.
Proof.
intro. 
intro. 
induction H.
  (* H=true *)
  unfold NF.
  intro.
  unfold not.
  intro.
  inversion H.
  (* H=false *)
  unfold NF.
  intro.
  unfold not.
  intro.
  inversion H.
  (* H=nv *)
  apply nvNF.
  assumption.
Qed.



(* DETERMINISMO *)

Theorem determinismo : forall t t' t'', (step t t') -> (step t t'') -> (t' = t'').
Proof.
induction t.
(* zero *)
intros. inversion H.
(* succ *) 
intros.  inversion H. inversion H0. subst. assert (t'0 = t'1). apply (IHt t'0 t'1 H2 H5). apply f_equal. assumption.
(* true *)
intros. inversion H.
(* false *)
intros. inversion H.
(* iszero *)

intros. inversion H. subst. inversion H0. reflexivity. inversion H2. 
inversion H0.  subst. discriminate H5. reflexivity. subst. 
apply succNum in H2. apply nvNF in H2. unfold NF in H2. unfold not in H2. apply H2 in H5. exfalso. assumption.
inversion H0.  subst.  inversion H2. subst. apply succNum in H5. apply nvNF in H5. unfold NF in H5. unfold not in H5. exfalso. apply (H5 t'0 H2). subst. apply f_equal. apply (IHt t'0 t'1 H2 H5).


intros. inversion H. subst. inversion H0. reflexivity. inversion H2. 
inversion H0.  subst. discriminate H5. subst. injection H4. intro. symmetry.  assumption.  
subst. 
apply succNum in H2. apply nvNF in H2. unfold NF in H2. unfold not in H2. apply H2 in H5. exfalso. assumption.
inversion H0.  subst.  inversion H2. subst. apply succNum in H5. apply nvNF in H5. unfold NF in H5. unfold not in H5. exfalso. apply (H5 t'0 H2). subst. apply f_equal. apply (IHt t'0 t'1 H2 H5).


intros. 
inversion H. subst. inversion H0. subst. reflexivity. inversion H5.

inversion H0. subst. discriminate. subst. assumption. subst. inversion H9. subst. inversion H0. subst. inversion H5. subst. inversion H5. subst. assert (t1'=t1'0). apply IHt1. assumption. assumption. rewrite H1. reflexivity.

Qed.

Inductive type :=
  | tNat : type
  | tBool : type.

Inductive hasType : term -> type -> Prop :=
  | tTrue : hasType true tBool
  | tFalse : hasType false tBool
  | tZero : hasType zero tNat
  | tSucc : forall t1, hasType t1 tNat -> hasType (succ t1) tNat
  | tPred : forall t1, hasType t1 tNat -> hasType (pred t1) tNat
  | tIsZero: forall t1, hasType t1 tNat -> hasType (iszero t1) tBool
  | tIf: forall t1 t2 t3 T, hasType t1 tBool -> hasType t2 T -> hasType t3 T -> hasType (ifte t1 t2 t3) T.

Theorem two_a : hasType (ifte ((iszero (succ (succ zero)))) (succ zero) zero) tNat.
Proof.
apply tIf.
apply tIsZero.
apply tSucc. apply tSucc. apply tZero. 
apply tSucc. apply tZero.
apply tZero.
Qed.

Theorem two_b: step (ifte (iszero (succ (succ zero))) (succ zero) zero) (ifte false (succ zero) zero).
Proof.
apply e_if.
apply e_iszerosucc. apply succNum. apply zeroNum.
Qed.

Theorem two_c: ~ step (ifte (iszero (succ (succ zero))) (succ zero) zero) zero.
Proof.
unfold not.
intros.
inversion H.
Qed.

Theorem two_d:  ~ forall (t : term) , value t.
Proof.
unfold not.
intro.
assert (value (iszero zero)).
apply (H (iszero zero)).
inversion H0.
inversion H1.
Qed.

Theorem two_e:  forall (t : term), (value t \/ ~value t).
Proof.
induction t.
  left. apply numVal. apply zeroNum.
  induction IHt.
    induction H.
      right. unfold not. intros. inversion H. subst. inversion H0. subst. inversion H2.
      right. unfold not. intros. inversion H. subst. inversion H0. subst. inversion H2.
      left. apply numVal. apply succNum. assumption.
      right. intro. apply H. apply numVal. inversion H0. inversion H1. subst. assumption.
  left. apply trueVal.
  left. apply falseVal.
  right. unfold not. intros. inversion H. subst. inversion H0.
  right. unfold not. intros. inversion H. subst. inversion H0.
  right. unfold not. intros. inversion H. subst. inversion H0. 
(* martelado *)
Qed.

Theorem unicidade: forall (t : term) (T : type) , (hasType t T) -> forall T', (hasType t T') -> T=T'.
Proof.
induction t.
  intros. inversion H. subst. inversion H0. reflexivity.
  intros. inversion H. subst. inversion H0. reflexivity.
  intros. inversion H. subst. inversion H0. reflexivity.
  intros. inversion H. subst. inversion H0. reflexivity.
  intros. inversion H. subst. inversion H0. reflexivity.
  intros. inversion H. subst. inversion H0. reflexivity.
  intros. inversion H. subst. apply IHt2. assumption.
    inversion H0. subst. assumption.
Qed.

Theorem preservacao:  forall t t', step t t' -> forall T, hasType t T -> hasType t' T.
Proof.
induction t.
  intros. inversion H0. subst. inversion H.
  intros. inversion H0. subst. apply e_succ in H.
(* proof by cansaço *)
Admitted.
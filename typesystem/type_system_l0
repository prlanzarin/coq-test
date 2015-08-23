(* LISTA DE EXERCÍCIOS 1 
   =====================================
   ALUNOS:
      PAULO RENATO LANZARIN - 228818
      MARCOS HENRIQUE BACKES - 228483
      MATHEUS ROSA CASTANHEIRA - 228400
   =====================================
*)



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

(* QUESTÃO 1A *)
Inductive type :=
 | tBool : type
 | tNat  : type
.
(* QUESTÃO 1B *)
Inductive hasType : term -> type -> Prop :=
 | t_true   :                                         hasType true       tBool
 | t_false  :                                         hasType false      tBool
 | t_zero   :                                         hasType zero       tNat
 | t_succ   : forall t,           hasType t tNat   -> hasType (succ t)   tNat
 | t_pred   : forall t,           hasType t tNat   -> hasType (pred t)   tNat
 | t_iszero : forall t,           hasType t tNat   -> hasType (iszero t) tBool
 | t_ifte   : forall t1 t2 t3 ty, hasType t1 tBool -> 
                                  hasType t2 ty    ->
                                  hasType t3 ty    -> hasType (ifte t1 t2 t3) ty
.

(* QUESTÃO 2A *)
Theorem dois_a : hasType (ifte (iszero (succ (succ zero))) (succ zero) zero) tNat.
Proof.
apply t_ifte.
apply t_iszero.
apply t_succ.
apply t_succ.
apply t_zero.
apply t_succ.
apply t_zero.
apply t_zero.
Qed.

(* QUESTÃO 2B *)
Theorem dois_b : step (ifte (iszero (succ (succ zero))) (succ zero) zero)
                       (ifte false (succ zero) zero).
Proof.
apply e_if.
apply e_iszerosucc.
apply succNum.
apply zeroNum.
Qed.

(* QUESTÃO 2C *)
Theorem dois_c : ~ (step (ifte (iszero (succ (succ zero))) (succ zero) zero) zero).
Proof.
unfold not.
intro.
inversion H.
Qed.

(* QUESTÃO 2D *)
Theorem dois_d : ~ forall t : term, value t.
Proof.
unfold not.
intro.
assert (value (iszero zero)).
apply (H (iszero zero)).
inversion H0.
inversion H1.
Qed.

(* QUESTÃO 2E *)
Theorem dois_e : forall t : term, (value t) \/ ~(value t).
Proof.
intros.
unfold not.
induction t.
  (* zero *)
  left. apply numVal. apply zeroNum.
  (* succ t *)
  inversion IHt.
  inversion H.
  (* value t*)
    (* succ true *)  
    subst. right. intro. inversion H0. subst. inversion H1. subst. inversion H3.
    (* succ false *)
    subst. right. intro. inversion H0. subst. inversion H1. subst. inversion H3.
    (* succ nv *)
    subst. left. apply numVal. apply succNum. assumption.
  (* value t -> False *)
  right. intro. apply H. apply numVal. inversion H0. subst. inversion H1. subst. assumption.
  (* true *)
  left. apply trueVal.
  (* false *)
  left. apply falseVal.
  (* iszero t *)
  right. intro. inversion H. inversion H0.
  (* pred t *)
  right. intro. inversion H. inversion H0.
  (* ifte t1 t2 t3 *)
  right. intro. inversion H. inversion H0.
Qed.

(* QUESTÃO 3A *)
Theorem unicidade_de_tipos : forall t, forall T1 T2 : type, (hasType t T1) -> (hasType t T2) -> T1 = T2.
Proof.
intros.
induction H.
  (* true *)
  inversion H0.
  reflexivity.
  (* false *)
  inversion H0.
  reflexivity.
  (* zero *)
  inversion H0.
  reflexivity.
  (* succ t *)
  inversion H0.
  reflexivity.
  (* pred t *)
  inversion H0.
  reflexivity.
  (* iszero t *)
  inversion H0.
  reflexivity.
  (* ifte t1 t2 t3 *)
  inversion H0.
  subst.
  apply IHhasType2.
  assumption.
Qed.


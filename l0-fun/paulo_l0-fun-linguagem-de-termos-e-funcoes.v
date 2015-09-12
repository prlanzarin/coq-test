(********************* BIBLIOTECAS DO COQ NECESSÁRIAS *******************)

(* Bibliotecas importadas *)
Require Import Arith ListSet MSets.

(* Infraestrutura para usar a biblioteca MSets de conjuntos *)
Module ModNat.
Definition t := nat.
Definition eq_dec :=  eq_nat_dec.
Definition lt := lt.
End ModNat.
Module ND  := Make_UDT(ModNat).      
Module S   := MSetWeakList.Make ND.          (* NatSets *)
Module SP  := MSetProperties.WProperties S.  (* NatSet Properties *)
Module SF  := MSetFacts.WFacts S.            (* NatSet Facts *)
(* 
   Operações para trabalhar com conjuntos de variáveis 
   Nesse caso, usamos a biblioteca MSet de Coq
*)
Definition setNat    := S.t. 
Definition emptySet  := S.empty.
Definition union     := S.union. 
Definition remove    := S.remove.
Definition add       := S.add.
Definition member    := S.mem. (* -> bool *) (* .mem e .In testam se sao membros do cj *)
Definition In        := S.In. (* -> Prop *)



(********************* SINTAXE DE TIPOS E TERMOS ***********************)

(* Definição indutiva dos termos de L0+FUN *)

(* Tipos da linguagem *)
Inductive type := 
 | tnat  : type
 | tbool : type
 | tfn   : type -> type -> type
.

(* Exemplos *)
Check tfn tnat tnat.                           (* nat -> nat *)
Check tfn (tfn tnat tnat) (tfn tbool tbool).   (* (nat->nat)->(bool->bool) *)


(* 
  Termos da linguagem
  Nota: para representar parâmetros serão usados números naturais 
  Exemplo: x = var 0 
           y = var 1 
           z = var 2
           ...
*)
Inductive term :=
 | zero   : term
 | succ   : term -> term
 | true   : term
 | false  : term
 | iszero : term -> term
 | pred   : term -> term
 | ifte   : term -> term -> term -> term 
 | var    : nat -> term
 | fn     : nat -> type -> term -> term
 | app    : term -> term -> term
 | _let   : nat -> type -> term -> term -> term
 | letrec : nat -> type -> type -> nat -> term -> term -> term
.

(* Exemplo 1: 

   (fn x:nat => succ succ x) (succ succ succ 0) 

*)
Check app (fn 0 tnat 
              (succ (succ (var 0)))) 
          (succ (succ (succ zero))).   


(* Exemplo 2: 

   (fn x:nat => fn y:bool => y) 

*)
Check (fn 0 tnat 
          (fn 1 tbool
              (var 1))).

(* Definição indutiva da propriedade de ser um número *)

Inductive nv : term -> Prop :=
 | zeroNum : nv zero
 | succNum : forall n, (nv n) -> (nv (succ n))
.

(* Definição indutiva de valor : números OU booleanos OU funções *)

Inductive value : term -> Prop :=
 | trueVal  : value true
 | falseVal : value false
 | numVal   : forall n, (nv n) -> (value n)
 | funVal   : forall x T t, value (fn x T t)
.


(*****************************************************************)


(* Definição de substituição {t/x}e - potencialmente com captura de variáveis livres *)
Fixpoint subs (t:term) (x:nat) (e:term) : term :=
 match e with
  | true     => true
  | false    => false
  | zero     => zero
  | succ u   => succ (subs t x u)
  | iszero u => iszero (subs t x u)
  | pred u   => pred (subs t x u)
  | ifte t1 t2 t3 => ifte (subs t x t1) (subs t x t2) (subs t x t3)
  | var y => if beq_nat x y
               then t
               else (var y)
  | app t1 t2 =>  app (subs t x t1) (subs t x t2)
  | fn y T body => if beq_nat x y
                     then fn y T body
                     else fn y T (subs t x body)
  | _let y T e1 e2 => if beq_nat x y
                        then _let y T (subs t x e1) e2
                        else _let y T (subs t x e1) (subs t x e2)
  | letrec f T1 T2 y e1 e2  => if beq_nat f x
                                  then letrec f T1 T2 y e1 e2
                                  else if beq_nat x y (* SEI LA QUEM SABE: {e/x} no segundo caso *)
                                         then letrec f T1 T2 y e1 (subs t x e2)
                                         else letrec f T1 T2 y (subs t x e1) 
                                                               (subs t x e2)
 end.


(* Exemplo de substituição - sem captura de variaveis livres *)
(* 
   {succ 0/y} (x y)   

   =  x (succ 0) 
*)
Eval compute in subs (succ zero) 1 
                     (app (var 0) (var 1)).


(* Exemplo de substituição - com captura de variaveis livres *)
(* 
   {succ x/y} (fn x:bool => x y)   

   =  (fn x:bool => x (succ x))
*)
Eval compute in subs (succ (var 0)) 1 
                     (fn 0 tbool (app (var 0) (var 1))).




(* Definição da semântica operacional *)
Inductive step : term -> term -> Prop :=
 | e_iftrue     : forall t2 t3,           step (ifte true  t2 t3) t2
 | e_iffalse    : forall t2 t3,           step (ifte false t2 t3) t3
 | e_if         : forall t1 t2 t3 t1',    (step t1 t1') -> step (ifte t1 t2 t3) (ifte t1' t2 t3)
 | e_succ       : forall t t',            step t t' -> step (succ t) (succ t')
 | e_predzero   :                         step (pred zero) zero
 | e_predsucc   : forall t,  (nv t) ->    step (pred (succ t)) t
 | e_pred       : forall t t',            step t t' -> step (pred t) (pred t')
 | e_iszerozero :                         step (iszero zero) true
 | e_iszerosucc : forall t,  (nv t) ->    step (iszero (succ t)) false
 | e_iszero     : forall t t',            step t t' -> step (iszero t) (iszero t')
 | e_app1       : forall t t' u,          step t t' -> step (app t u) (app t' u)
 | e_app2       : forall t t' v,          step t t' -> value v -> 
                                                    step (app v t) (app v t')
 | e_beta       : forall t x T e,         value t -> 
                                              step (app (fn x T e) t) (subs t x e)
 | e_let1       : forall x T v e2,        value v ->
                                              step (_let x T v e2) (subs v x e2)
 | e_let2       : forall x T e1 e1' e2,   step e1 e1' -> 
                                              step (_let x T e1 e2) (_let x T e1' e2)
(* a sei la vai se fude nao faço ideia se ta certo*)
 | e_letrec     : forall f T1 T2 y e1 e2, step (letrec f T1 T2 y e1 e2)
                                               (subs (fn y T1 (letrec f T1 T2 y e1 e1)) f e2) 
.


(* Definição de forma normal *)
Definition NF (t:term) : Prop := forall t', not (step t t').


(* TODO NV É FORMA NORMAL *)
Theorem nvNF : forall (t:term), nv t -> NF t.
Proof. 
intro. intro. 
induction H. unfold NF. intros. intro. inversion H.
unfold NF. intros. intro. unfold NF in IHnv. inversion H0. subst. 
assert (~ step n t'0). apply IHnv.
contradiction.
Qed.

(* TODO VALOR É FORMA NORMAL *)
Theorem valueNF : forall (t:term), value t -> NF t.
Proof.
intro. intro. induction H.
(* H=true *)     unfold NF. intro. unfold not. intro. inversion H.
(* H=false *)    unfold NF. intro. unfold not. intro. inversion H.
(* H=nv *)       apply nvNF. assumption. 
(* H=fn x T e *) unfold NF. intros. intro. inversion H.
Qed.


(*****************************************************************)

(* Ambiente de tipos *)


Definition env  := list (nat*type). (* pares do gamma -> pares var ; tipo do contexto *)


(* Consulta a ambiente de tipos *)
Fixpoint   lookup (x:nat) (Gamma:env) : option type := 
 match Gamma with
  | nil               => None
  | cons (y,T) Gamma' => if beq_nat y x
                           then Some T
                           else lookup x Gamma'
 end.

Eval compute in lookup 2 (cons (1,tnat) 
                               (cons (2,tbool) nil)).

(* Atualiza um ambiente de tipos *)
Fixpoint update (x:nat) (T:type) (Gamma:env) : env :=
 match Gamma with
   | nil                => cons (x,T) nil
   | cons (y,T') Gamma' => if beq_nat x y
                             then cons (x,T) Gamma'
                             else cons (y,T') (update x T Gamma')
 end.

(* Domínio de um ambiente = conjunto de variáveis definidas em um dado ambiente de tipos *)
Fixpoint domEnv (Gamma:env) : setNat :=
match Gamma with
  | nil               => emptySet
  | cons (x,T) Gamma' => add x (domEnv Gamma')
end.


(* Exemplos *)

(* Ambiente vazio *)
Check nil.

(* Ambiente com associações: Gamma = <epsilon>, x:nat, y:bool->bool *)
Check (cons (1,tfn tbool tbool) 
         (cons (0,tnat) 
              nil)).

(* Consulta ao ambiente: Gamma(x) *)
Eval compute in lookup 0 
                  (cons (1,tfn tbool tbool) 
                    (cons (0,tnat) 
                       nil)).


(****************************************************)
(*           Propriedades de ambientes              *)
(****************************************************)

Lemma update_after_update : forall Gamma x T U, update x T (update x U Gamma) = update x T Gamma.
Proof.
intros.
induction Gamma.
  simpl. rewrite <- beq_nat_refl. reflexivity. subst.
  induction a. 
    simpl. 
    destruct (beq_nat x a) as []_eqn. 
    simpl. 
    rewrite <- beq_nat_refl. 
    reflexivity.
  simpl. rewrite <- IHGamma. rewrite -> Heqb0. reflexivity. (* wtf *)
Qed.

Lemma lookup_after_update : forall Gamma x T, lookup x (update x T Gamma) = Some T.
Proof.
intros.
induction Gamma.
  simpl. rewrite <- beq_nat_refl. reflexivity.
  simpl.
  induction a.
    destruct (beq_nat x a) as []_eqn.
    simpl. rewrite <- beq_nat_refl. reflexivity.
    simpl. destruct (beq_nat a x) as []_eqn. rewrite <- IHGamma.
Admitted. 




(****************************************************)
(*                                                  *)
(****************************************************)


(* Função que calcula as variáveis livres de um termo - FV(t) *)
Fixpoint fv (t:term) : setNat :=
match t with
  | true          => emptySet 
  | false         => emptySet
  | zero          => emptySet
  | succ t1       => fv t1
  | ifte t1 t2 t3 => (union (union (fv t1) (fv t2)) (fv t3))
  | pred t1       => fv t1
  | iszero t1     => fv t1
  | var x         => add x emptySet 
  | fn x T body   => remove x (fv body)
  | app t1 t2     => union (fv t1) (fv t2)
  | _let x T e1 e2 => union (fv e1) (fv e2)
  | letrec a b c d e f => emptySet
end.


(* Testando o cálculo de variáveis livres 
  
  FV( fn x:nat => x y )       

  = { y }

*)
Eval compute in fv (fn 0 tnat (app (var 0) (var 1))).  


(* Termos fechados são aqueles que não possuem variáveis livres *)
Definition closed (t:term) : Prop := S.Empty (fv t).

(* Sistema de tipos *)
Inductive hasType : env -> term -> type -> Prop :=
 | t_true       : forall Gamma, hasType Gamma true  tbool
 | t_false      : forall Gamma, hasType Gamma false tbool
 | t_zero       : forall Gamma, hasType Gamma zero  tnat
 | t_if         : forall Gamma t1 t2 t3 T, (hasType Gamma t1 tbool) -> 
                                           (hasType Gamma t2 T) -> 
                                           (hasType Gamma t3 T) ->
                                           hasType Gamma (ifte t1 t2 t3) T
 | t_succ       : forall Gamma t,  (hasType Gamma t tnat) -> (hasType Gamma (succ t) tnat)
 | t_pred       : forall Gamma t,  (hasType Gamma t tnat) -> (hasType Gamma (pred t) tnat)
 | t_iszero     : forall Gamma t,  (hasType Gamma t tnat) -> (hasType Gamma (iszero t) tbool)
 | t_var        : forall Gamma x T, lookup x Gamma = Some T -> (hasType Gamma (var x) T)
 | t_fun        : forall Gamma x T T' body, (hasType (update x T Gamma) body T') ->
                                            (hasType Gamma (fn x T body) (tfn T T'))     
 | t_app        : forall Gamma f a T T', (hasType Gamma f (tfn T T')) ->
                                         (hasType Gamma a T) ->
                                         (hasType Gamma (app f a) T')
 | t_let        : forall Gamma e1 T x e2 T', (hasType Gamma e1 T) ->
                                             (hasType (update x T Gamma) e2 T') ->
                                             (hasType Gamma (_let x T e1 e2) T')
 | t_letrec     : forall Gamma f T T1 T2 x e1 e2, (hasType (update f (tfn T1 T2) (update x T1 Gamma)) e1 T2) ->
                                                  (hasType (update f (tfn T1 T2) Gamma) e2 T) ->
                                                  (hasType Gamma (letrec f T1 T2 x e1 e2) T)
.



(**** Propriedades do sistema de tipos da linguagem ****)
 
Lemma bool_values : forall t, hasType nil t tbool -> value t -> t=true \/ t=false.
Proof.
intro.
intro. 
inversion H.
(*induction t.*)
 left. reflexivity. (* t *)
 right. reflexivity. (* f *)
 intro. left. subst. inversion H6. subst. inversion H3. (* if *)
 intro. subst. inversion H3. subst. inversion H1. subst. (* iszero *)
 intro. inversion H1. subst. inversion H2. subst. (* var *)
 intro. inversion H2. subst. inversion H3. subst. (* app *)
 intro. inversion H2. subst. inversion H3. subst. (* _let *)
 intro. inversion H2. subst.  inversion H3. (* letrec *)
Qed. (* testified, amen *)
 
Lemma nat_values : forall t, hasType nil t tnat -> value t -> t=zero \/ (exists t', t=succ t').
Proof.
intro.
intro. 
inversion H.
 left. reflexivity. subst. (* zero *)
 intro. inversion H3. subst. inversion H4. subst. (* if *)
 intro. inversion H1. subst. inversion H2. subst. right. exists t0. reflexivity. subst. (* succ *)
 intro. inversion H1. subst. inversion H2. subst. (* pred *)
 intro. inversion H1. subst. inversion H2. subst. (* var *)
 intro. inversion H2. subst. inversion H3. subst. (* app *)
 intro. inversion H2. subst. inversion H3. subst. (* _let *)
 intro. inversion H2. subst. inversion H3. (* subst. letrec *)
Qed. (* testified, amen *)

Theorem progresso : forall t T, 
         hasType nil t T -> 
           ((value t) \/ (exists t', step t t') ).
Proof. 
intro.
induction t.
(* t=zero *)
intros.
left.
apply numVal.
apply zeroNum.
(* t=succ t1*)
intros.
inversion H. subst. 
assert (value t \/ (exists t' : term, step t t')).
apply (IHt tnat). assumption.
elim H0.
  intros. 
  inversion H1.
  subst.  inversion H2.
  subst.  inversion H2.
  subst. left. apply numVal. apply succNum. assumption.
  subst.
inversion H2. 
intros. 
right. 
inversion H1.
apply ex_intro with (x:=succ x).
apply e_succ.
assumption.
(* t=true *)
intros. left. apply trueVal.
(* t=false *)
intros. left. apply falseVal.
(* t=iszero t1 *) 
intros.
inversion_clear H.
assert (value t \/ (exists t' : term, step t t')).
apply (IHt tnat). assumption.
elim H. 
intros.
right.  
inversion H1. subst. inversion H0.
subst. inversion H0.
subst.
inversion H2.
subst.  
apply ex_intro with (x:=true).
apply e_iszerozero.
subst.
apply ex_intro with (x:=false).
apply e_iszerosucc.
inversion H2. assumption.
subst.  inversion H0.
intros. 
right.
inversion H1.
apply ex_intro with (x:=iszero x).
apply e_iszero.
assumption.
(* t=pred t1 *)
intros.
right.
inversion H. subst. 
assert (value t \/ (exists t' : term, step t t')).
apply (IHt tnat). assumption.
elim H0.
intros.
inversion H1. 
subst. inversion H2. subst. inversion H2.
subst. 
inversion H3.
subst. 
apply ex_intro with (x:=zero).
apply e_predzero.
subst. 
apply ex_intro with (x:=n).
apply e_predsucc.
assumption.
subst.
inversion H2.
intros.
inversion H1.
apply ex_intro with (x:=pred x).
apply e_pred.
assumption.
(* t=ifte t1 t2 t3 *)
intros.
right. 
inversion H.
subst. 
assert (value t1 \/ (exists t' : term, step t1 t')).
apply (IHt1 tbool). assumption.
elim H0.
 intros. 
apply bool_values in H4.
elim H4.
subst. 
  intros. subst. 
  apply ex_intro with (x:=t2).
  apply e_iftrue.
  intros. subst. 
  apply ex_intro with (x:=t3).
  apply e_iffalse. assumption. 
intros. 
inversion H1.
apply ex_intro with (x:=ifte x t2 t3).
apply e_if. assumption.
(* -------------------------------------- *)
(* t=var n *)
intro.
intro.
left.
inversion H. subst. inversion H2. (* apply numVal. subst. *)

(* t=fn x T body *)
intro.
intro. left. apply funVal. (*inversion H. subst. apply funVal.*)

(* t=app t1 t2 *)
intro.
intro. left. inversion H. subst.
 assert (value t1 \/ (exists t' : term, step t1 t')). apply (IHt1 tfn). 


admit.

(* completar com mais casos ao estender a linguagem... *)
(* t = _let n t1 t2 t3 *)
admit.

(* t = letrec n t1 t2 n0 t3 t4 *)
intro.
intro. inversion H. subst. right. exists t4. rewrite -> (subs (fn n0 t1 (letrec n t1 t2 n0 t4 t4)) n t3). apply e_letrec.
admit.
Qed.


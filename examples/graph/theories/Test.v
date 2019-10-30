Require Import Data.Graph.Inductive.Graph.
Require Import CoLoR.Util.Relation.Lexico.
Require Import CoLoR.Util.Relation.SN.
Require Import Coq.Relations.Relation_Operators.

Section WF.

 Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}.


Definition natNodes (g : gr a b) := (BinInt.Z.abs_nat(Graph.noNodes g)).

Definition natNodes_lt (x y : gr a b) := natNodes x < natNodes y.
Definition natNodes_eq (x y : gr a b) := natNodes x = natNodes y.
Definition list_length_lt {a} (x y : list a) := length x < length y.

Definition bf_measure_list (a: Type) := 
  transp (lex (transp natNodes_lt) natNodes_eq (transp  (@list_length_lt a))).
End WF.


Section Test.

 Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}.

(*This works fine*)
 Program Fixpoint test  (q: list (Node * Num.Int)) (g: gr a b) {measure (g, q) (bf_measure_list _)} : list (Node * Num.Int) :=
  match q, g with
  | nil, _ => nil
  | cons (v,j) vs, g => match match_ v g with
                                | (Some c, g') => cons (v,j) (test vs g')
                                | (None, g') => test vs g'
                                end
  end. 
Admit Obligations.
End Test.

(*Gives a Stack Overflow*)
Program Fixpoint test {gr : Type -> Type -> Type} {a : Type} {b : Type} {Hgraph : Graph.Graph gr} {Hlaw: LawfulGraph gr} 
  (q: list (Node * Num.Int)) (g: gr a b) {measure (g, q) (bf_measure_list _)} : list (Node * Num.Int) :=
  match q, g with
  | nil, _ => nil
  | cons (v,j) vs, g => match match_ v g with
                                | (Some c, g') => cons (v,j) (test vs g')
                                | (None, g') => test vs g'
                                end
  end.

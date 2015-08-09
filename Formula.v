Require Import Arith.
Require Import Recdef.

Inductive formula : Set :=
    | True  : formula
    | False : formula
    | Var   : nat -> formula
    | Not   : formula -> formula
    | And   : formula -> formula -> formula
    | Or    : formula -> formula -> formula
    | Imply : formula -> formula -> formula.

Fixpoint elim_imply (f : formula) : formula :=
    match f with
    | Not   f1    => Not (elim_imply f1)
    | And   f1 f2 => And (elim_imply f1) (elim_imply f2)
    | Or    f1 f2 => Or (elim_imply f1) (elim_imply f2)
    | Imply f1 f2 => Or (Not (elim_imply f1)) (elim_imply f2)
    | _           => f
    end.

Fixpoint detached_not (f : formula) : nat :=
    match f with
    | Not   True    => 0
    | Not   False   => 0
    | Not   (Var _) => 0
    | Not   f1      => S (detached_not f1)
    | And   f1 f2   => detached_not f1 + detached_not f2
    | Or    f1 f2   => detached_not f1 + detached_not f2
    | Imply f1 f2   => detached_not f1 + detached_not f2
    | _             => 0
    end.

Function move_not (f : formula) {measure detached_not} : formula :=
    match f with
    | Not True        => Not True
    | Not False       => Not False
    | Not (Var n)     => Not (Var n)
    | Not (Not f1)    => move_not f1
    | Not (And f1 f2) => Or  (move_not (Not f1)) (move_not (Not f2))
    | Not (Or  f1 f2) => And (move_not (Not f1)) (move_not (Not f2))
    | And f1 f2       => And (move_not f1) (move_not f2)
    | Or  f1 f2       => Or  (move_not f1) (move_not f2)
    | _               => f
    end.
Proof.
Admitted.

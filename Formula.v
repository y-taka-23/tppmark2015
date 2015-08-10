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
    | True        => True
    | False       => False
    | Var n       => Var n
    | Not   f1    => Not (elim_imply f1)
    | And   f1 f2 => And (elim_imply f1) (elim_imply f2)
    | Or    f1 f2 => Or (elim_imply f1) (elim_imply f2)
    | Imply f1 f2 => Or (Not (elim_imply f1)) (elim_imply f2)
    end.

Fixpoint height (f : formula) : nat :=
    match f with
    | True        => 0
    | False       => 0
    | Var n       => 0
    | Not   f1    => S (height f1)
    | And   f1 f2 => S (Peano.max (height f1) (height f2))
    | Or    f1 f2 => S (Peano.max (height f1) (height f2))
    | Imply f1 f2 => S (Peano.max (height f1) (height f2))
    end.

Fixpoint not_height (f : formula) : nat :=
    match f with
    | True        => 0
    | False       => 0
    | Var n       => 0
    | Not   f1    => S (height f1)
    | And   f1 f2 => Peano.max (not_height f1) (not_height f2)
    | Or    f1 f2 => Peano.max (not_height f1) (not_height f2)
    | Imply f1 f2 => Peano.max (not_height f1) (not_height f2)
    end.

Lemma not_height_le_height :
    forall f : formula, not_height f <= height f.
Proof.
    induction f as [| | n | f1 H1 | f1 H1 f2 H2 | f1 H1 f2 H2 | f1 H1 f2 H2];
    simpl;
    try trivial.

        (* Case : f = And f1 f2 *)
        apply le_S.
        apply (NPeano.Nat.max_le_compat _ _ _ _ H1 H2).

        (* Case : f = And f1 f2 *)
        apply le_S.
        apply (NPeano.Nat.max_le_compat _ _ _ _ H1 H2).

        (* Case : f = And f1 f2 *)
        apply le_S.
        apply (NPeano.Nat.max_le_compat _ _ _ _ H1 H2).
Qed.

Function move_not_aux (f : formula) {measure not_height} : formula :=
    match f with
    | True   => True
    | False  => False
    | Var n  => Var n
    | Not f1 => match f1 with
        | True          => Not True
        | False         => Not False
        | Var n         => Not (Var n)
        | Not   f1'     => move_not_aux f1'
        | And   f1' f2' => Or  (move_not_aux (Not f1')) (move_not_aux (Not f2'))
        | Or    f1' f2' => And (move_not_aux (Not f1')) (move_not_aux (Not f2'))
        | Imply f1' f2' => Not (Imply f1' f2')
        end
    | And   f1 f2 => And   f1 f2
    | Or    f1 f2 => Or    f1 f2
    | Imply f1 f2 => Imply f1 f2
    end.
Proof.
    (* Case : f = Not (Not f1' *)
    intros _ _ f1' _ _.
    simpl.
    apply lt_S.
    apply (le_lt_trans _ (height f1') _ (not_height_le_height _) (lt_n_Sn _)).

    (* Case : f = Not (And f1' f2') : move_not_aux (Not f2') *)
    intros _ _ f1' f2' _ _.
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Not (And f1' f2') : move_not_aux (Not f1')  *)
    intros _ _ f1' f2' _ _.
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).

    (* Case : f = Not (Or f1' f2') : move_not_aux (Not f2')  *)
    intros _ _ f1' f2' _ _.
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Not (Or f1' f2') : move_not_aux (Not f1')  *)
    intros _ _ f1' f2' _ _.
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).
Defined.

Function move_not (f : formula) : formula :=
    match f with
    | True   => True
    | False  => False
    | Var n  => Var n
    | Not f1 => match f1 with
        | True          => Not True
        | False         => Not False
        | Var n         => Not (Var n)
        | Not   f1'     => move_not_aux (Not (Not f1'))
        | And   f1' f2' => move_not_aux (Not (And f1' f2'))
        | Or    f1' f2' => move_not_aux (Not (Or  f1' f2'))
        | Imply f1' f2' => Not (Imply (move_not f1') (move_not f2'))
        end
    | And   f1 f2 => And   (move_not f1) (move_not f2)
    | Or    f1 f2 => Or    (move_not f1) (move_not f2)
    | Imply f1 f2 => Imply (move_not f1) (move_not f2)
    end.

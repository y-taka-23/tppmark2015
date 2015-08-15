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

Inductive equiv : formula -> formula -> Prop :=
    | equiv_and_comm   : forall f1 f2 : formula, equiv (And f1 f2) (And f2 f1)
    | equiv_or_comm    : forall f1 f2 : formula, equiv (Or f1 f2) (Or f2 f1)
    | equiv_and_assoc  : forall f1 f2 f3 : formula,
                         equiv (And (And f1 f2) f3) (And f1 (And f2 f3))
    | equiv_or_assoc   : forall f1 f2 f3 : formula,
                         equiv (Or (Or f1 f2) f3) (Or f1 (Or f2 f3))
    | equiv_and_absorp : forall f1 f2 : formula, equiv (And f1 (Or f1 f2)) f1
    | equiv_or_absorp  : forall f1 f2 : formula, equiv (Or f1 (And f1 f2)) f1
    | equiv_and_iden   : forall f : formula, equiv (And f True) f
    | equiv_or_iden    : forall f : formula, equiv (Or f False) f
    | equiv_and_distr  : forall f1 f2 f3 : formula,
                         equiv (And f1 (Or f2 f3)) (Or (And f1 f2) (And f1 f3))
    | equiv_or_distr   : forall f1 f2 f3 : formula,
                         equiv (Or f1 (And f2 f3)) (And (Or f1 f2) (Or f1 f3))
    | equiv_and_compl  : forall f : formula, equiv (And f (Not f)) False
    | equiv_or_compl   : forall f : formula, equiv (Or f (Not f)) True
    | equiv_refl       : forall f : formula, equiv f f
    | equiv_sym        : forall f1 f2 : formula, equiv f1 f2 -> equiv f2 f1
    | equiv_trans      : forall f1 f2 f3 : formula,
                         equiv f1 f2 -> equiv f2 f3 -> equiv f1 f2.

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

Fixpoint move_not (f : formula) : formula :=
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

Fixpoint eval_const (f : formula) : formula :=
    match f with
    | True  => True
    | False => False
    | Var n => Var n
    | Not f1 => match eval_const f1 with
        | True  => False
        | False => True
        | f1'   => Not f1'
        end
    | And f1 f2 => match eval_const f1, eval_const f2 with
        | True,  f2'   => f2'
        | False, f2'   => False
        | f1',   True  => f1'
        | f1',   False => False
        | f1',   f2'   => And f1' f2'
        end
    | Or f1 f2 => match eval_const f1, eval_const f2 with
        | True,  f2'   => True
        | False, f2'   => f2'
        | f1',   True  => True
        | f1',   False => f1'
        | f1',   f2'   => Or f1' f2'
        end
    | Imply f1 f2 => match eval_const f1, eval_const f2 with
        | True,  False => False
        | False, f2'   => True
        | f1',   True  => True
        | f1',   f2'   => Imply f1' f2'
        end
    end.

Fixpoint or_size (f : formula) : nat :=
    match f with
    | True        => 0
    | False       => 0
    | Var n       => 0
    | Not   f1    => or_size f1
    | And   f1 f2 => or_size f1 + or_size f2
    | Or    f1 f2 => S (height f1 + height f2)
    | Imply f1 f2 => or_size f1 + or_size f2
    end.

Function distr_or_aux (f : formula) {measure or_size} : formula :=
    match f with
    | True   => True
    | False  => False
    | Var n  => Var n
    | Not f1 => Not f1
    | And f1 f2 => And f1 f2
    | Or  f1 f2 => match f1, f2 with
        | f1, And f1' f2' =>
            And (distr_or_aux (Or f1 f1')) (distr_or_aux (Or f1 f2'))
        | And f1' f2', f2 =>
            And (distr_or_aux (Or f1' f2)) (distr_or_aux (Or f2' f2))
        | f1, f2 => Or f1 f2
        end
    | Imply f1 f2 => Imply f1 f2
    end.
Proof.
    (* Case : f = Or True (And f1' f2') : distr_or_aux (Or True f2') *)
    intros _ _ _ _ f1' f2' _ _ .
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Or True (And f1' f2') : distr_or_aux (Or True f1') *)
    intros _ _ _ _ f1' f2' _ _ .
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).

    (* Case : f = Or False (And f1' f2') : distr_or_aux (Or False f2') *)
    intros _ _ _ _ f1' f2' _ _ .
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Or True (And f1' f2') : distr_or_aux (Or False f1') *)
    intros _ _ _ _ f1' f2' _ _ .
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).

    (* Case : f = Or (Var n) (And f1' f2') : distr_or_aux (Or (Var n) f2') *)
    intros _ _ _ n _ f1' f2' _ _ .
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Or (Var n) (And f1' f2') : distr_or_aux (Or (Var n) f1') *)
    intros _ _ _ n _ f1' f2' _ _ .
    simpl.
    apply lt_n_S.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).

    (* Case : f = Or (Not f0) (And f1' f2') : distr_or_aux (Or (Not f0) f2' *)
    intros _ _ _ f0 _ f1' f2' _ _.
    simpl.
    repeat apply lt_n_S.
    apply plus_lt_compat_l.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Or (Not f0) (And f1' f2') : distr_or_aux (Or (Not f0) f1' *)
    intros _ _ _ f0 _ f1' f2' _ _.
    simpl.
    repeat apply lt_n_S.
    apply plus_lt_compat_l.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).

    (* Case : f = Or (And f1 f2') True : distr_or_aux (Or f2' True) *)
    intros _ _ _ f1' f2' _ _ _.
    simpl.
    repeat apply lt_n_S.
    repeat rewrite plus_0_r.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Or (And f1 f2') True : distr_or_aux (Or f1' True) *)
    intros _ _ _ f1' f2' _ _ _.
    simpl.
    repeat apply lt_n_S.
    repeat rewrite plus_0_r.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).

    (* Case : f = Or (And f1 f2') False : distr_or_aux (Or f2' False) *)
    intros _ _ _ f1' f2' _ _ _.
    simpl.
    repeat apply lt_n_S.
    repeat rewrite plus_0_r.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Or (And f1 f2') False : distr_or_aux (Or f1' False) *)
    intros _ _ _ f1' f2' _ _ _.
    simpl.
    repeat apply lt_n_S.
    repeat rewrite plus_0_r.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).

    (* Case : f = Or (And f1 f2') (Var n) : distr_or_aux (Or f2' (Var n)) *)
    intros _ _ _ f1' f2' _ n _ _.
    simpl.
    repeat apply lt_n_S.
    repeat rewrite plus_0_r.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_r _ _) (lt_n_Sn _)).

    (* Case : f = Or (And f1 f2') (Var n) : distr_or_aux (Or f1' (Var n)) *)
    intros _ _ _ f1' f2' _ n _ _.
    simpl.
    repeat apply lt_n_S.
    repeat rewrite plus_0_r.
    apply (le_lt_trans _ (Peano.max (height f1') (height f2')) _
           (Max.le_max_l _ _) (lt_n_Sn _)).

    (* Case : f = Or (And f1' f2') (Not f0) : distr_or_aux (Or f2' (Not f0)) *)
    intros _ _ _ f1' f2' _ f0 _ _.
    simpl.
    apply lt_n_S.
    apply le_lt_n_Sm.
    apply (plus_le_compat_r _ _ _ (Max.le_max_r _ _)).

    (* Case : f = Or (And f1' f2') (Not f0) : distr_or_aux (Or f1' (Not f0)) *)
    intros _ _ _ f1' f2' _ f0 _ _.
    simpl.
    apply lt_n_S.
    apply le_lt_n_Sm.
    apply (plus_le_compat_r _ _ _ (Max.le_max_l _ _)).

    (* Case : f = Or (And f1' f2') (And f1'0 f2'0) : distr_or_aux (Or (And f1' f2') f2'0) *)
    intros _ _ _ f1' f2' _  f1'0 f2'0 _ _.
    simpl.
    repeat apply lt_n_S.
    apply plus_lt_compat_l.
    apply (le_lt_n_Sm _ _ (Max.le_max_r _ _)).

    (* Case : f = Or (And f1' f2') (And f1'0 f2'0) : distr_or_aux (Or (And f1' f2') f1'0) *)
    intros _ _ _ f1' f2' _  f1'0 f2'0 _ _.
    simpl.
    repeat apply lt_n_S.
    apply plus_lt_compat_l.
    apply (le_lt_n_Sm _ _ (Max.le_max_l _ _)).

    (* Case : f = Or (And f1' f2') (Or f0 f3) : distr_or_aux (Or f2' (Or f0 f3)) *)
    intros _ _ _ f1' f2' _ f0 f3 _ _.
    simpl.
    apply lt_n_S.
    apply le_lt_n_Sm.
    apply plus_le_compat_r.
    apply Max.le_max_r.

    (* Case : f = Or (And f1' f2') (Or f0 f3) : distr_or_aux (Or f1' (Or f0 f3)) *)
    intros _ _ _ f1' f2' _ f0 f3 _ _.
    simpl.
    apply lt_n_S.
    apply le_lt_n_Sm.
    apply plus_le_compat_r.
    apply Max.le_max_l.

    (* Case : f = Or (And f1' f2') (Imply f0 f3) : distr_or_aux (Or f2' (Imply f0 f3)) *)
    intros _ _ _ f1' f2' _ f0 f3 _ _.
    simpl.
    apply lt_n_S.
    apply le_lt_n_Sm.
    apply plus_le_compat_r.
    apply Max.le_max_r.

    (* Case : f = Or (And f1' f2') (Imply f0 f3) : distr_or_aux (Or f1' (Imply f0 f3)) *)
    intros _ _ _ f1' f2' _ f0 f3 _ _.
    simpl.
    apply lt_n_S.
    apply le_lt_n_Sm.
    apply plus_le_compat_r.
    apply Max.le_max_l.

    (* Case : f = Or (Or f0 f3) (And f1' f2') : distr_or_aux (Or (Or f0 f3) f2') *)
    intros _ _ _ f0 f3 _ f1' f2' _ _.
    simpl.
    repeat apply lt_n_S.
    apply plus_lt_compat_l.
    apply (le_lt_n_Sm _ _ (Max.le_max_r _ _)).

    (* Case : f = Or (Or f0 f3) (And f1' f2') : distr_or_aux (Or (Or f0 f3) f1') *)
    intros _ _ _ f0 f3 _ f1' f2' _ _.
    simpl.
    repeat apply lt_n_S.
    apply plus_lt_compat_l.
    apply (le_lt_n_Sm _ _ (Max.le_max_l _ _)).

    (* Case : f = Or (Imply f0 f3) (And f1' f2') : distr_or_aux (Or (Imply f0 f3) f2' *)
    intros _ _ _ f0 f3 _ f1' f2' _ _.
    simpl.
    repeat apply lt_n_S.
    apply plus_lt_compat_l.
    apply (le_lt_n_Sm _ _ (Max.le_max_r _ _)).

    (* Case : f = Or (Imply f0 f3) (And f1' f2') : distr_or_aux (Or (Imply f0 f3) f1') *)
    intros _ _ _ f0 f3 _ f1' f2' _ _.
    simpl.
    repeat apply lt_n_S.
    apply plus_lt_compat_l.
    apply (le_lt_n_Sm _ _ (Max.le_max_l _ _)).
Defined.

Fixpoint distr_or (f : formula) : formula :=
    match f with
    | True   => True
    | False  => False
    | Var n  => Var n
    | Not f1 => Not (distr_or f1)
    | And f1 f2 => And (distr_or f1) (distr_or f2)
    | Or  f1 f2 => match f1, f2 with
        | f1, And f1' f2' =>
            And (distr_or_aux (Or f1 f1')) (distr_or_aux (Or f1 f2'))
        | And f1' f2', f2 =>
            And (distr_or_aux (Or f1' f2)) (distr_or_aux (Or f2' f2))
        | f1, f2 => Or (distr_or f1) (distr_or f2)
        end
    | Imply f1 f2 => Imply (distr_or f1) (distr_or f2)
    end.

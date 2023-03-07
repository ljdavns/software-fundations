(* ================================================================= *)
(** ** Booleans *)

(** Another familiar enumerated type: *)

Inductive bool : Type :=
  | true
  | false.

(** Booleans are also available from Coq's standard library, but
    in this course we'll define everything from scratch, just to see
    how it's done. *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** Note the syntax for defining multi-argument
    functions ([andb] and [orb]).  *)
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** We can define new symbolic notations for existing definitions. *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** We can also write these function using Coq's "if" expressions.  *)

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(** **** Exercise: 1 star, standard (nandb)
    The command [Admitted] can be used as a placeholder for an
    incomplete proof.  We use it in exercises to indicate the parts
    that we're leaving for you -- i.e., your job is to replace
    [Admitted]s with real proofs.
    Remove "[Admitted.]" and complete the definition of the following
    function; then make sure that the [Example] assertions below can
    each be verified by Coq.  (I.e., fill in each proof, following the
    model of the [orb] tests above, and make sure Coq accepts it.) The
    function should return [true] if either or both of its inputs are
    [false].
    Hint: if [simpl] will not simplify the goal in your proof, it's
    probably because you defined [nandb] without using a [match]
    expression. Try a different definition of [nandb], or just
    skip over [simpl] and go directly to [reflexivity]. We'll
    explain this phenomenon later in the chapter. *)

Definition nandb (b1:bool) (b2:bool) : bool := 
  match b1 with
  | false => true
  | true =>
    match b2 with
    | true => false
    | false => true
    end
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed. 

Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)

(** Most exercises are omitted from the "terse" version of the
    notes used in lecture.
    The "full" version contains both the assigned reading and all the
    exercises for your homework assignment. *)
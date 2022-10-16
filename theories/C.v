From SimpleIO Require Import SimpleIO.
From SimpleIO Require Import IO_UnsafeNat.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Ascii.
Import IO.Notations.
Import ListNotations.

From Coq.extraction Require Import ExtrOcamlIntConv.

#[local] Open Scope string_scope.

Section Impl.

  Fixpoint solver (l : list bool) (c : nat) : nat :=
    match l with
    | [] => 0
    | h :: t =>
      if h
      then 1 + solver t 2
      else
        if c
        then solver t c
        else 1 + solver t (pred c)
    end.

  Definition one : ascii := "1".
  Fixpoint list_bool_of_string (s : string) : list bool :=
    match s with
    | EmptyString => nil
    | String ch s => cons (eqb ch one) (list_bool_of_string s)
    end.

  Definition main : IO unit :=
    (* Read inputs *)
    n <- read_nat;;
    l_raw <- read_line';;
    let l := list_bool_of_string l_raw in
    (* Compute answer *)
    let res := solver l 0 in
    (* Print answer *)
    print_nat res;;
    print_endline "".

  
  Definition run_main : io_unit :=
    IO.unsafe_run (main).
End Impl.

(* Extraction "C" run_main. *)

Section Theories.

  Inductive LectureTrace : list bool -> nat -> nat -> Prop :=
  | sleep : forall t w, LectureTrace t 0 w -> LectureTrace (false :: t) 0 w
  | refill : forall t c w, LectureTrace t 2 w -> LectureTrace (true :: t) c (S w)
  | drink : forall t c w, LectureTrace t c w -> LectureTrace (false :: t) (S c) (S w)
  | end_day : forall c, LectureTrace [] c 0.

  Theorem can_stay_awake' : forall l c w,
    solver l c = w <-> LectureTrace l c w.
  Proof.
    split.
    - generalize dependent c.
      generalize dependent w.
      induction l; intros.
      + subst. constructor.
      + destruct a.
        * cbn in *. 
          rewrite <- H.
          constructor.
          now apply IHl.
        * cbn in *.
          destruct c.
          ** rewrite <- H.
            constructor.
            now apply IHl.
          ** rewrite <- H.
            constructor.
            now apply IHl.
    - intros.
      induction H.
      + now rewrite <- IHLectureTrace.
      + now rewrite <- IHLectureTrace.
      + now rewrite <- IHLectureTrace.
      + reflexivity.
  Qed.

End Theories.

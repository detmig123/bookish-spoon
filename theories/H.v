From SimpleIO Require Import SimpleIO. Import IO.Notations.
From SimpleIO Require Import IO_UnsafeNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import String.
From Coq Require Import Arith.
From Coq.extraction Require Import ExtrOcamlIntConv.
From Coq.extraction Require Import ExtrOcamlNatInt.



Section Impl.
  Definition peak_hight (low high low' : nat) :=
    min (high - low) (high - low').

  Fixpoint get_peak (l : list nat) (best low high prev : nat) : nat :=
    match l with
    | [] => max best (peak_hight low high prev)
    | h :: t =>
      if prev <=? h
      then get_peak t best low h h
      else get_peak' t best low high h
    end
    with get_peak' (l : list nat) (best low high prev : nat) : nat :=
      match l with
      | [] => max best (peak_hight low high prev)
      | h :: t =>
        if h <=? prev
        then get_peak' t best low high h
        else 
          let new_best := max best (peak_hight low high prev) in
          get_peak t new_best prev h h
      end.

  Definition solver (l : list nat) : nat :=
    match l with
    | [] => 0
    | (h :: t) => get_peak t 0 h h h
    end.
  
  (* Tests *)
  (* Compute (solver [0;1;2;3;4;5;4;3;2;1;0]). *)
  (* Compute (solver [29;85;88;12;52;37;19;86;7;44]). *)
  (* Compute (solver [1;1;1]). *)

  Parameter read_ints : IO (list int).
  Definition read_nats : IO (list nat) :=
    IO.map (map nat_of_int) read_ints.

  Definition main : IO unit :=
    (* Read inputs *)
    n <- read_int;;
    l <- read_nats;;
    (* Compute answer *)
    let res := solver l in
    (* Print answer *)
    print_nat res;;
    print_endline ""%string.

  Definition run_main : io_unit :=
    IO.unsafe_run (main).
End Impl.


Extract Constant int_of_nat => "fun x -> x".
Extract Constant nat_of_int => "fun x -> x".
Extract Constant read_ints =>
  "fun k -> k (read_line () |>
               String.split_on_char ' ' |> List.map int_of_string)".
(* Extraction "D" run_main. *)

Section Theories.
  Inductive decreasing : list nat -> Prop :=
  | dnil : forall x, decreasing [x]
  | dcons : forall x y t, x > y -> decreasing (y :: t) -> decreasing (x :: y :: t).

  Inductive increasing : list nat -> Prop :=
  | inil : forall x, increasing [x]
  | icons : forall x y t, x < y -> increasing (y :: t) -> increasing (x :: y :: t).

  Definition peak (l : list nat) : Prop :=
    exists x l1 l2, l = l1 ++ [x] ++ l2 ->
      increasing (l1 ++ [x]) /\ decreasing ([x] ++ l2).
  
  Definition height (l : list nat) : nat :=
    let peak := list_max l in
      min (peak - (hd peak l)) (peak - (last l peak)).

  Theorem solver_correct : forall l p,
    solver l = p ->
      forall l' l_p l_t, l = l_p ++ l' ++ l_t -> peak l' -> height l' <= p.
  Proof.
    induction l.
    - intros p Hsolver * Heq Hpeak.
      cbn in *.
      symmetry in Heq.
      apply app_eq_nil in Heq as [_ Heq].
      apply app_eq_nil in Heq as [Heq _].
      now subst.
    - intros p Hsolver * Heq Hpeak.
      cbn in *.
      unfold get_peak in *.

      Search (_ ++ _ = []).
      unfold peak in *.
      destruct Hpeak as (x & l1 & l2 & H).
  Admitted.

  Theorem solver_correct' : forall l p,
    solver l = p ->
      exists l' l_p l_t, l = l_p ++ l' ++ l_t -> peak l' -> height l' = p.
  Proof.
    destruct l.
    - intros p Hsolver.
      cbn in *.
      now do 3 exists [].
    - cbn.
      induction l.
      + intros p Hsolver.
        cbn in *.
      induction l.
      + 
  Admitted.

End Theories.

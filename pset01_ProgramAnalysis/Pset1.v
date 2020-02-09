(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 1 *)

Require Import Frap Pset1Sig.
Require Import Nat.

(* The first part of this assignment involves the [bool] datatype,
 * which has the following definition.
 * <<
     Inductive bool :=
     | true
     | false.
   >>
 * We will define logical negation and conjunction of Boolean values,
 * and prove some properties of these definitions.
 *)

(* Define [Neg] so that it implements Boolean negation, which flips
 * the truth value of a Boolean value.
 *)
Definition Neg (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* For instance, the negation of [true] should be [false].
 * This proof should follow from reducing both sides of the equation
 * and observing that they are identical.
 *)
Theorem Neg_true : Neg true = false.
Proof.
  simplify.
  equality.
Qed.

(* Negation should be involutive, meaning that if we negate
 * any Boolean value twice, we should get the original value back.

 * To prove a fact like this that holds for all Booleans, it suffices
 * to prove the fact for both [true] and [false] by using the
 * [cases] tactic.
 *)
Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
Proof.
  simplify.
  cases b.
  equality.
  equality.
Qed.

(* Define [And] so that it implements Boolean conjunction. That is,
 * the result value should be [true] exactly when both inputs
 * are [true].
 *)
Definition And (x y : bool) : bool :=
  match x with
  | true
    => match y with
    | true => true
    | false => false
    end
  | false =>  false
  end.

(* Here are a couple of examples of how [And] should act on
 * concrete inputs.
 *)
Theorem And_true_true : And true true = true.
Proof.
  equality.
Qed.

Theorem And_false_true : And false true = false.
Proof.
  equality.
Qed.

(* Prove that [And] is commutative, meaning that switching the order
 * of its arguments doesn't affect the result.
 *)
Theorem And_comm : forall x y : bool, And x y = And y x.
Proof.
  simplify.

  cases x.

  cases y.

  equality.
  equality.

  cases y.

  equality.
  equality.
Qed.

(* Prove that the conjunction of a Boolean value with [true]
 * doesn't change that value.
 *)
Theorem And_true_r : forall x : bool, And x true = x.
Proof.
  simplify.
  cases x.
  equality.
  equality.
Qed.

(* In the second part of this assignment, we will work with a simple language
 * of imperative arithmetic programs that sequentially apply operations
 * to a natural-number-valued state.

 * The [Prog] datatype defines abstract syntax trees for this language.
 *)

Print Prog.

(* Define [run] such that [run p n] gives the final state
 * that running the program [p] should result in, when the
 * initial state is [n].
 *)
Fixpoint run (p : Prog) (initState : nat) : nat :=
  match p with
  | Done => initState
  | AddThen val p_remaining => run p_remaining (val + initState)
  | MulThen val p_remaining => run p_remaining (val * initState)
  | DivThen val p_remaining => run p_remaining (initState / val)
  | VidThen val p_remaining => run p_remaining (val / initState)
  | SetToThen val p_remaining => run p_remaining val
  end.

Theorem run_Example1 : run Done 0 = 0.
Proof.
  equality.
Qed.

Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
Proof.
  equality.
Qed.

Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
Proof.
  equality.
Qed.

(* Define [numInstructions] to compute the number of instructions
 * in a program, not counting [Done] as an instruction.
 *)
Fixpoint numInstructions (p : Prog) : nat :=
  match p with
  | Done => 0
  | AddThen _ p_remaining => 1 + (numInstructions p_remaining)
  | MulThen _ p_remaining => 1 + (numInstructions p_remaining)
  | DivThen _ p_remaining => 1 + (numInstructions p_remaining)
  | VidThen _ p_remaining => 1 + (numInstructions p_remaining)
  | SetToThen _ p_remaining => 1 + (numInstructions p_remaining)
  end.

Theorem numInstructions_Example :
  numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
Proof.
  equality.
Qed.

(* Define [concatProg] such that [concatProg p1 p2] is the program
 * that first runs [p1] and then runs [p2].
 *)
Fixpoint concatProg (p1 p2 : Prog) : Prog :=
  match p1 with
  | Done => p2
  | AddThen   val p1_rem => AddThen val (concatProg p1_rem p2)
  | MulThen   val p1_rem => MulThen val (concatProg p1_rem p2)
  | DivThen   val p1_rem => DivThen val (concatProg p1_rem p2)
  | VidThen   val p1_rem => VidThen val (concatProg p1_rem p2)
  | SetToThen val p1_rem => SetToThen val (concatProg p1_rem p2)
  end.

Theorem concatProg_Example :
     concatProg (AddThen 1 Done) (MulThen 2 Done)
     = AddThen 1 (MulThen 2 Done).
Proof.
  equality.
Qed.

(* Prove that the number of instructions in the concatenation of
 * two programs is the sum of the number of instructions in each
 * program.
 *)
Theorem concatProg_numInstructions
  : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                      = numInstructions p1 + numInstructions p2.
Proof.
  simplify.
  induct p1.

  simplify; equality.
  simplify; equality.
  simplify; equality.
  simplify; equality.
  simplify; equality.
  simplify; equality.
Qed.

(* Prove that running the concatenation of [p1] with [p2] is
   equivalent to running [p1] and then running [p2] on the
   result. *)
Theorem concatProg_run
  : forall (p1 p2 : Prog) (initState : nat),
    run (concatProg p1 p2) initState =
    run p2 (run p1 initState).
Proof.
  simplify.
  induct p1.
  simplify; equality.

  apply IHp1.
  apply IHp1.
  apply IHp1.
  apply IHp1.
  apply IHp1.
Qed.

(* Read this definition and understand how division by zero is handled. *)
Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
  match p with
  | Done => (true, state)
  | AddThen n p => runPortable p (n+state)
  | MulThen n p => runPortable p (n*state)
  | DivThen n p =>
      if n ==n 0 then (false, state) else
      runPortable p (state/n)
  | VidThen n p =>
      if state ==n 0 then (false, 0) else
      runPortable p (n/state)
  | SetToThen n p =>
      runPortable p n
  end.
Arguments Nat.div : simpl never. (* you don't need to understand this line *)

(* Prove that running the concatenation [p] using [runPortable]
   coincides with using [run], as long as [runPortable] returns
   [true] to confirm that no divison by zero occurred. *)
Lemma runPortable_run : forall p s0 s1,
  runPortable p s0 = (true, s1) -> run p s0 = s1.
Proof.
  simplify.
  induct p.

  simplify; equality.
  apply IHp; equality.
  apply IHp; equality.

  cases  n.
  simplify;  equality.
  apply IHp.
  simplify; equality.

  cases  n.
  apply IHp.
  simplify.
  cases s0.
  simplify; equality.
  simplify; equality.
  simplify.
  cases s0.
  simplify; equality.
  simplify; apply IHp; equality.

  simplify; apply IHp; equality.
Qed.


(* The final goal of this pset is to implement [validate : Prog -> bool]
   such that if this function returns [true], the program would not trigger
   division by zero regardless of what state it starts out in.  [validate] is
   allowed to return [false] for some perfectly good programs that never cause
   division by zero, but it must recognize as good the examples given below.  In
   jargon, [validate] is required to be sound but not complete, but "complete
   enough" for the use cases defined by the examples given here: *)

Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
Example runPortable_good : forall n,
  runPortable goodProgram1 n = (true, 10/(1+n)).
Proof. simplify. equality. Qed.

Definition badProgram1 := AddThen 0 (VidThen 10 Done).
Example runPortable_bad : let n := 0 in
  runPortable badProgram1 n = (false, 0).
Proof. simplify. equality. Qed.

Definition badProgram2 := AddThen 1 (DivThen 0 Done).
Example runPortable_bad2 : forall n,
  runPortable badProgram2 n = (false, 1+n).
Proof. simplify. equality. Qed.

Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
Definition goodProgram4 := Done.
Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).

(* If you already see a way to build [validate] that meets the
 * requirements above, _and have a plan for how to prove it correct_,
 * feel free to just code away. Our solution uses one intermediate definition
 * and one intermediate lemma in the soundness proof -- both of which are more
 * sophisticated than the top-level versions given here. *)

Fixpoint validate_helper (p : Prog) (possible_zero : bool) : bool :=
  match p with
  | Done => true
  | AddThen n p' => validate_helper p' (if possible_zero then (if n ==n 0 then true else false) else false)
  | MulThen n p' => validate_helper p' (if n ==n 0 then true else possible_zero)
  | DivThen n p' => if n ==n 0 then false else validate_helper p' (if n ==n 1 then possible_zero else true)
  | VidThen n p' => if possible_zero then false else validate_helper p' true
  | SetToThen n p' => validate_helper p' (if n ==n 0 then true else false)
  end.

Definition validate (p : Prog) : bool := validate_helper p true.

Example validate1 : validate goodProgram1 = true.
Proof.  simplify.  equality.  Qed.
Example validate2 : validate goodProgram2 = true.
Proof.  simplify.  equality.  Qed.
Example validate3 : validate goodProgram3 = true.
Proof.  simplify.  equality.  Qed.
Example validate4 : validate goodProgram4 = true.
Proof.  simplify.  equality.  Qed.
Example validate5 : validate goodProgram5 = true.
Proof.  simplify.  equality.  Qed.
Example validate6 : validate goodProgram6 = true.
Proof.  simplify.  equality.  Qed.
Example validate7 : validate goodProgram7 = true.
Proof.  simplify.  equality.  Qed.

Example validateBad1 : validate badProgram1 = false.
Proof.  simplify. equality. Qed.
Example validateBad2 : validate badProgram2 = false.
Proof.  simplify. equality. Qed.

(* If a clear plan hasn't emerged in 10 minutes (or if you get stuck later),
 * take a look at the hints for this pset on the course web site.
 * It is not expected that this pset is doable for everyone without the hints,
 * but some planning is required for successful proof.
 * In particular, repeatedly trying out different combinations of tactics
 * and ideas from hints until something sticks can go on for arbitrarily long
 * with little insight and no success; just guessing a solution is unlikely.
 * Thus, we encourage you to take your time thinking, look at the hints when
 * necessary, and only jump into coding when you have some idea why it should
 * succeed. Some may call Coq a video game, but it is not a grinding contest. *)

Lemma temp : forall (s : nat), s <> 0 -> forall n, s + n * s <> 0.
Proof.
  simplify.
  apply Nat.neq_0_lt_0 in H.
  apply Nat.neq_0_lt_0.
  Search(0 < _ -> 0 < _ + _).
  apply Nat.add_pos_l with (n := s).
  equality.
Qed.


Lemma validate_helper_sound : forall p possible_zero, validate_helper p possible_zero = true ->
  forall s, ((possible_zero = false -> (s <> 0)))
  -> runPortable p s = (true, run p s).
Proof.
  simplify.
  induct p.
  induct s.

  simplify; equality.
  simplify; equality.

  simplify.
  cases possible_zero.
    cases n.
      simplify.
      apply IHp with (possible_zero := true).
      equality.
      equality.
      simplify.
      apply IHp with (possible_zero := false).
      equality.
      equality.
    cases n.
      simplify.
      apply IHp with (possible_zero := false).
      equality.
      equality.
      simplify.
      apply IHp with (possible_zero := false).
      equality.
      equality.

  simplify.
  cases possible_zero.
    cases n.
      simplify.
      apply IHp with (possible_zero := true).
      equality.
      equality.
      simplify.
      apply IHp with (possible_zero := true).
      equality.
      propositional.
      equality.
    cases n.
      simplify.
      apply IHp with (possible_zero := true).
      equality.
      equality.
      propositional.
      simplify.
      apply IHp with (possible_zero := false).
      equality.
      propositional.
      apply temp with (n:= n) in H1.
      equality.

  simplify.
    cases possible_zero.
      cases n.
        simplify.
        equality.
        simplify.
      cases n.
        simplify.
        rewrite Nat.div_1_r with (a := s).
        apply IHp with (possible_zero := true).
        equality.
        equality.
        simplify.
        apply IHp with (possible_zero := true).
        equality.
        equality.
        propositional.
      cases n.
        simplify.
        equality.
        simplify.
        cases n.
          simplify.
          apply IHp with (possible_zero := false).
          equality.
          rewrite Nat.div_1_r with (a := s).
          equality.
          simplify.
          propositional.
          apply IHp with (possible_zero := true).
          equality.
          equality.

  simplify.
  cases possible_zero.
    cases s.
      equality.
      equality.
    propositional.
    cases (n / s).
      cases s.
        equality.
        simplify.
        apply IHp with (possible_zero := true).
        equality.
        equality.
      cases s.
        equality.
        simplify.
        apply IHp with (possible_zero := true).
        equality.
        equality.

  cases n.
    simplify.
    apply IHp with (possible_zero := true).
    equality.
    equality.
    simplify.
    apply IHp with (possible_zero := false).
    equality.
    equality.
Qed.

Lemma validate_sound : forall p, validate p = true ->
  forall s, runPortable p s = (true, run p s).
Proof.
  simplify.
  apply validate_helper_sound with (possible_zero := true).
  equality.
  equality.
Qed.

(* Here is the complete list of commands used in one possible solution:
  - Search, for example Search (_ + 0).
  - induct, for example induct x
  - simplify
  - propositional
  - equality
  - linear_arithmetic
  - cases, for example cases (X ==n Y)
  - apply, for example apply H
  - apply in, for example apply H1 in H2 or apply somelemma in H1
  - apply with, for example apply H1 with (x:=2)
  - apply in with, for example apply H1 with (x:=2) in H2
  - rewrite, for example rewrite H
  - rewrite in, for example rewrite H1 in H2 or rewrite somelemma in H1
  - ;, for example simplify; propositional *)

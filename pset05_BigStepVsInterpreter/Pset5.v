(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 5 *)

(* Author: Samuel Gruetter <gruetter@mit.edu> *)

Require Import Frap.Frap.
Require Import Pset5Sig.

(* Delete this line if you don't like bullet points and errors like
   "Expected a single focused goal but 2 goals are focused." *)
Set Default Goal Selector "!".

(* In this pset, we will explore different ways of defining semantics for the
   simple imperative language we used in Chapter 4 (Interpreters.v) and
   Chapter 7 (OperationalSemantics.v).
   Make sure to re-read these two files, because many definitions we ask you
   to come up with in this pset are similar to definitions in these two files.

   Pset5Sig.v contains the number of points you get for each definition and
   proof. Note that since we ask you to come up with some definitions
   yourself, all proofs being accepted by Coq does not necessarily guarantee a
   full score: You also need to make sure that your definitions correspond to
   what we ask for in the instructions. *)

(* Our language has arithmetic expressions (note that we removed Times and Minus,
   because they don't add anything interesting for this pset): *)
Inductive arith : Set :=
| Const(n: nat)
| Var(x: var)
| Plus(e1 e2: arith).

(* And it has commands, some of which contain arithmetic expressions: *)
Inductive cmd :=
| Skip
| Assign(x: var)(e: arith)
| Sequence(c1 c2: cmd)
| If(e: arith)(thn els: cmd)
| While(e: arith)(body: cmd).

(* As in the lecture, we use a finite map to store the values the variables: *)
Definition valuation := fmap var nat.

(* To make it a bit more interesting, we add a twist:
   If an arithmetic expression reads an undefined variable, instead of just
   returning 0, we specify that an arbitrary value can be returned.
   Therefore, the signature we used in class,

     Fixpoint interp (e : arith) (v : valuation) : nat := ...

   will not work any more, because that one can only return one value.
   Instead, we will use the following definition: *)
Fixpoint interp(e: arith)(v: valuation)(a: nat): Prop :=
  match e with
  | Const n => a = n
  | Var x =>
    match v $? x with
    | None => True (* any a is possible! *)
    | Some n => a = n
    end
  | Plus e1 e2 => exists a1 a2, interp e1 v a1 /\ interp e2 v a2 /\ a = a1 + a2
  end.
(* You can read "interp e v a" as the claim "interpreting expression e under
   the valuation v can return the value a".
   And if we don't provide the last argument, we can think of "interp e v",
   which has type "nat -> Prop", as "the set of all possible values e could
   return". *)

(* For example, if we interpret the expression "y+z" in a valuation where
   y is defined to be 2, but z is undefined, we can get any value for z,
   so the possible results are all values greater or equal to 2. *)
Goal interp (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) = (fun a => 2 <= a).
Proof.
  simplify.
  apply sets_equal.
  split; simplify.
  - invert H. invert H0. linear_arithmetic.
  - exists 2, (x - 2). linear_arithmetic.
Qed.
(* Hint which will be useful later:
   In the above proof, you can see how you can deal with existentials:
   - If you have an "H: exists x, P" above the line, you can "invert H"
     do obtain such an "x" and an "H0: P".
   - If you have an "exists x, P" below the line, you can use "exists y"
     to provide the value for which you want to prove the existential. *)

(* An alternative way of specifying how arithmetic expressions are evaluated
   is by using inference rules, where we put preconditions above the line,
   and the conclusion below the line, and a name of the rule to the right of
   the line, and use "Oxford brackets" to write statements of the form
   "a ∈ [[e]]_v" which we read as "the natural number a is in the set of
   values to which e can evaluate under the valuation v".
   If we were to write this on a blackboard, it might look like this:

                      ------------ ValuesConst
                      n ∈ [[n]]_v

                       (x↦a) ∈ v
                      ------------ ValuesVarDefined
                      a ∈ [[x]]_v

                      x ∉ dom(v)
                     ------------ ValuesVarUndefined
                     a ∈ [[x]]_v

          a1 ∈ [[e1]]_v   a2 ∈ [[e2]]_v   a=a1+a2
          ----------------------------------------- ValuesPlus
                     a ∈ [[e1+e2]]_v

   Let's translate this to an Inductive Prop in Coq called "values", that is,
   "values e v a" should mean "the natural number a is in the set of
   values to which e can evaluate under the valuation v".
   Define an Inductive with four constructors, one for each of the four rules
   above, using the names written to the right of the lines above as the
   constructor names.
*)
Inductive values: arith -> valuation -> nat -> Prop :=
| ValuesConst : forall v n,
    values (Const n) v n
| ValuesVarDefined : forall v x a,
    v $? x = Some a
    -> values (Var x) v a
| ValuesVarUndefined : forall v x a,
    v $? x = None
    -> values (Var x) v a
| ValuesPlus : forall e1 e2 v a1 a2 a,
    values e1 v a1
    -> values e2 v a2
    -> a = a1 + a2
    -> values (Plus e1 e2) v a.

(* Note that the following alternative would also work for ValuesPlus:

          a1 ∈ [[e1]]_v     a2 ∈ [[e2]]_v
          --------------------------------- ValuesPlus
                a1+a2 ∈ [[e1+e2]]_v

   But in Coq, this would be a bit less convenient, because the tactic
   "eapply ValuesPlus" would only work if the goal is of the shape
   "values _ _ (_ + _)", whereas if we add this extra equality,
   "eapply ValuesPlus" works no matter what the last argument to "values" is. *)

(* Contrary to the Fixpoint-based definition "interp", we can't do simplification
   of the kind "replace interp by its body and substitute the arguments in it",
   because an Inductive Prop describes a family of proof trees, and isn't a
   function with a right-hand side you could plug in somewhere else.
   In order to prove the example Goal from above for "values", we need to construct
   the following proof tree:

  ("y"↦2) ∈ {"y"↦2}                         "z" ∉ dom({"y"↦2})
 -------------------- ValuesVarDefined      ------------------------ ValuesVarUndefined
 2 ∈ [["y"]]_{"y"↦2}                        a-2 ∈ [["z"]]_{"y"↦2}                          a=2+a-2
 ---------------------------------------------------------------------------------------------------- ValuesPlus
                                a ∈ [["y"+"z"]]_{"y"↦2}
*)
Example values_example: forall a,
    2 <= a ->
    values (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) a.
Proof.
  (* "simplify" only introduces the hypotheses but can't really simplify
     anything here. This is not a limitation of "simplify", but by design. *)
  simplify.
  (* Once you define the four constructors for "values", you can uncomment
     the script below. Make sure you understand how it relates to the proof
     tree above! *)

  eapply ValuesPlus with (a1 := 2) (a2 := a - 2).
  - eapply ValuesVarDefined. simplify. equality.
  - eapply ValuesVarUndefined. simplify. equality.
  - linear_arithmetic.
Qed.

(* Now, let's prove that "interp" and "values" are equivalent: *)
Theorem interp_to_values: forall e v a,
    interp e v a -> values e v a.
Proof.
  induct e; simplify.

  - subst. eapply ValuesConst.

  - cases (v $? x); subst.
    1: eapply ValuesVarDefined; trivial.
    eapply ValuesVarUndefined; trivial.

  - invert H. invert H0.
    propositional.
    specialize (IHe1 v x).
    specialize (IHe2 v x0).
    propositional.
    eapply ValuesPlus with (a1 := x) (a2 := x0); trivial.
Qed.

(* To prove the other direction, we can induct on the proof tree of "values" *)
Theorem values_to_interp: forall e v a,
    values e v a -> interp e v a.
Proof.
  induct 1; (* <-- do not change this line *)
    simplify; try equality.
  - rewrite H. trivial.
  - rewrite H. trivial.
  - exists a1. exists a2.
    propositional.
Qed.

(* Note that we could also induct on e, but this is a bit more work
   (let's still do it as an exercise, though). *)
Theorem values_to_interp_induction_on_e: forall e v a,
    values e v a -> interp e v a.
Proof.
  induct e; (* <-- BAD, but for the sake of the exercise, do not change this line *)
    simplify; invert H; trivial.
  - rewrite H1; try equality.
  - rewrite H1; trivial.
  - specialize (IHe1 v a1).
    specialize (IHe2 v a2).
    propositional.
    exists a1. exists a2.
    propositional.
Qed.

(* Let's define nondeterministic big-step semantics for evaluating a command.
   Define "eval" as an Inductive Prop such that "eval v1 c v2" means
   "If we run command c on valuation v1, we can obtain valuation v2".
   Whenever you encounter an arithmetic expression, use "values" to obtain a
   value it can step to.
   Hint: This will be quite similar to "eval" in OperationalSemantics.v! *)
Inductive eval: valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
  eval v Skip v
| EvalAssign : forall v x e a,
  values e v a
  -> eval v (Assign x e) (v $+ (x, a))
| EvalSeq : forall v c1 v1 c2 v2,
  eval v c1 v1
  -> eval v1 c2 v2
  -> eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e then_ else_ v',
  (exists a, values e v (S a))
  -> eval v then_ v'
  -> eval v (If e then_ else_) v'
| EvalIfFalse : forall v e then_ else_ v',
  values e v 0
  -> eval v else_ v'
  -> eval v (If e then_ else_) v'
| EvalWhileTrue : forall v e body v' v'',
  (exists a, values e v (S a))
  -> eval v body v'
  -> eval v' (While e body) v''
  -> eval v (While e body) v''
| EvalWhileFalse : forall v e body,
  values e v 0
  -> eval v (While e body) v.

(* Before you continue your epic journey through this adventure game, I want
   to give you another tool. It's much more powerful than any combination of
   "invert", "simplify", "exists", "eapply", etc you could ever imagine, so
   please make sure to keep the following tool at an easy to access place in
   your toolbox. Here it is, in the form of a hint:

   Hint: Many of the proofs below will depend on definitions we ask you to
   find yourself, and if you get these definitions wrong, the proofs will
   not work, so keep in mind that you might have to go back and adapt your
   definitions!
   Also, it can happen that many proofs go through and you become (overly)
   confident that your definitions are correct, even though they aren't. *)

(* Here's an example program. If we run it on the empty valuation, reading the
   variable "oops" can return any value, but after that, no matter whether
   "oops" was zero or not, we assign a non-zero value to "tmp", so the answer
   will always be 42. *)
Example the_answer_is_42 :=
  Sequence (Assign "x" (Var "oops"))
           (Sequence (If (Var "x")
                         (Assign "tmp" (Plus (Var "x") (Var "x")))
                         (Assign "tmp" (Const 1)))
                     (If (Var "tmp")
                         (Assign "answer" (Const 42))
                         (Assign "answer" (Const 24)))).

(* To prove that this sample program always returns 42, we first prove a handy
   helper lemma: *)
Lemma read_last_value: forall x v c n,
    values (Var x) (v $+ (x, c)) n -> n = c.
Proof.
  simplify.
  invert H.
  - Search((_ $+ (_, _)) $? _).
    rewrite lookup_add_eq with (k1 := x) (k2 := x) in H1; equality.
  - rewrite lookup_add_eq with (k1 := x) (k2 := x) in H1; equality.
Qed.


Ltac last_value :=
  match goal with
    | [ H : (_ $+ (?K, _)) $? ?K = _ |- _ ] =>
      rewrite lookup_add_eq with (k1 := K) (k2 := K) in H
    | [ |- context[(_ $+ (?K, _)) $? ?K = _] ] =>
      rewrite lookup_add_eq with (k1 := K) (k2 := K); try linear_arithmetic; try equality
  end.
Hint Extern 1 => last_value : core.

(* Hint: This one is a bit boring -- it's about 30 lines of "invert", "simplify",
   "discriminate", "equality", "exfalso", "linear_arithmetic" and
   "apply read_last_value in H", "subst" in our solution.
   But it's a good test case to make sure you got the definition of "eval" right!
   And note that inverting the hypotheses in the right order, i.e.
   in the order the program is executed, as well as using read_last_value
   whenever possible, will make your proof less long. *)
Theorem the_answer_is_indeed_42:
  forall v, eval $0 the_answer_is_42 v -> v $? "answer" = Some 42.
Proof.
  intros.
  invert H.
  invert H5.
  assert (exists a, values (Var "tmp") v2 (S a)).
  - clear H6.
    invert H3.
    cases a.
    1: invert H2.
      1: {
        invert H6.
        invert H; last_value; equality.
      }
      1: {
        invert H7.
        invert H3.
        exists 0.
        econstructor.
        auto.
      }
      invert H2.
      2: {
        exists 0.
        econstructor.
        specialize read_last_value with (x := "x") (v := $0) (c := S a) (n := 0) as HH.
        propositional; equality.
      }
      invert H7.
      invert H3.
      apply read_last_value in H1.
      apply read_last_value in H2.
      subst; simplify.
      remember (a + S a) as b.
      exists b.
      remember ($0 $+ ("x", S a)) as v'.
      assert (S b <> 0); try equality.
      econstructor.
      auto.
  - invert H6;
    invert H9.
    1: invert H6; auto.
    invert H.
    invert H0; invert H8; try equality.
    invert H2; invert H10; invert H1; auto; try equality.
Qed.

(* Here's another example program. If we run it on a valuation which is
   undefined for "x", it will read the undefined variable "x" to decide$0 $+ ("x", S a)
   whether to abort the loop, so any number of loop iterations is possible. *)
Example loop_of_unknown_length :=
  (While (Var "x") (Assign "counter" (Plus (Var "counter") (Const 1)))).

(* Hint: you might need the "maps_equal" tactic to prove that two maps are the same. *)
Theorem eval_loop_of_unknown_length: forall n initialCounter,
    eval ($0 $+ ("counter", initialCounter))
         loop_of_unknown_length
         ($0 $+ ("counter", initialCounter + n)).
Proof.
  unfold loop_of_unknown_length.
  induct n; simplify.
  - replace (initialCounter + 0) with initialCounter; try linear_arithmetic.
    eapply EvalWhileFalse.
    eapply ValuesVarUndefined.
    simplify; equality.
  - eapply EvalWhileTrue.
    1: exists 0; eapply ValuesVarUndefined; simplify; equality.
    1: econstructor; econstructor; econstructor; simplify; f_equal.
    specialize (IHn (initialCounter + 1)).
    replace ($0 $+ ("counter", initialCounter) $+ ("counter", initialCounter + 1))
      with ($0 $+ ("counter", initialCounter + 1)).
      2: maps_equal.
    replace (initialCounter + 1 + n) with (initialCounter + S n) in IHn; try linear_arithmetic.
    assumption.
Qed.

(* Wherever this TODO_FILL_IN is used, you should replace it with your solution *)
Axiom TODO_FILL_IN: Prop.

(* You might wonder whether we can use "Fixpoint" instead of "Inductive" to define
   such nondeterministic big-step evaluation of commands, and indeed we can.
   But we need some trick to convince Coq that this Fixpoint will always terminate,
   even though there could be infinite loops.
   We achieve this by using a "fuel" argument that limits the recursion depth.
   This does not exclude any possible final valuations, because for every final
   valuation, there exists a recursion depth sufficient to reach it.
   So let's define a Fixpoint "run" such that "run fuel v1 c v2" means
   "if we run command c on valuation v1, and limit the recursion depth to fuel,
   we can obtain valuation v2".
   We already defined all cases for you except the "While" case, but all the
   building blocks you need can be found in the other cases too.
 *)
Fixpoint run(fuel: nat)(v1: valuation)(c: cmd)(v2: valuation): Prop :=
  match fuel with
  | O => False
  | S fuel' =>
    match c with
    | Skip => v1 = v2
    | Assign x e => exists a, interp e v1 a /\ v2 = (v1 $+ (x, a))
    | Sequence c1 c2 => exists vmid, run fuel' v1 c1 vmid /\ run fuel' vmid c2 v2
    | If e c1 c2 =>
      (exists r, interp e v1 r /\ r <> 0 /\ run fuel' v1 c1 v2) \/
      (interp e v1 0 /\ run fuel' v1 c2 v2)
    | While e c1 =>
      (exists r vmid, interp e v1 r /\ r <> 0 /\ run fuel' v1 c1 vmid /\ run fuel' vmid (While e c1) v2) \/
      (interp e v1 0 /\ v1 = v2)
    end
  end.

Hint Extern 1 =>
  match goal with
    | [ H : interp ?E ?V ?A |- _ ] =>
        apply interp_to_values with (e := E) (v := V) (a := A)
  end.
Hint Extern 1 =>
  match goal with
    | [ |- context[interp ?E ?V ?A] ] => apply interp_to_values with (e := E) (v := V) (a := A)
  end.

(* Now let's prove that "run" and "eval" are equivalent! *)

Theorem run_to_eval: forall fuel v1 c v2,
    run fuel v1 c v2 ->
    eval v1 c v2.
Proof.
  induct fuel; intros.
  - simplify. equality.
  - induct c; try equality.
    1: unfold run in H; subst; eapply EvalSkip.
    1: {
      unfold run in H.
      invert H.
      propositional.
      subst. eapply EvalAssign.
      auto.
    }
    1: {
      invert H. propositional.
      remember x as vmid.
      pose proof (IHfuel v1 c1 vmid); propositional.
      pose proof (IHfuel vmid c2 v2); propositional.
      econstructor.
      1: instantiate (1 := vmid); assumption.
      assumption.
    }
    1: {
      invert H; invert H0; propositional; auto.
      1: {
        auto. (* TODO: Why does auto not work here? <08-03-20, shankha> *)
        apply interp_to_values with (e := e) (v := v1) (a := x) in H0.
        econstructor.
        1: {
          cases x; propositional.
          exists x.
          assumption.
        }
        apply IHfuel.
        assumption.
      }
      econstructor 5; auto.
    }
    invert H; propositional.
    2: subst; econstructor 7; auto.
    invert H0.
    invert H.
    propositional.
    econstructor.
    1: {
      cases x; propositional.
      exists x.
      auto.
    }
    1: instantiate (1 := x0); auto.
    auto.
Qed.

(* For the other direction, we could naively start proving it like this: *)
Theorem eval_to_run: forall v1 c v2,
    eval v1 c v2 ->
    exists fuel, run fuel v1 c v2.
Proof.
  induct 1; simplify.
  (* feel free to prove part of this to experience how tedious the existentials
     are, but don't waste too much time on it, because there's a better way
     to do it below! *)
Abort. (* <-- do not change this line *)

(* To prove the other direction, we will first define a wrapper around "run"
   that hides the existential: *)
Definition wrun(v1: valuation)(c: cmd)(v2: valuation): Prop :=
  exists fuel, run fuel v1 c v2.

(* The idea is that in the run_to_eval proof above, using the constructors of
   "eval", i.e. doing "eapply EvalAssign", "eapply EvalSeq", "eapply EvalIfTrue",
   was quite convenient, so let's expose the same "API" for constructing proofs
   of "run" (or actually, proofs of the slightly nicer "wrun"). *)

Theorem run_with_more_fuel: forall fuel v1 c v2,
    run fuel v1 c v2 -> run (S fuel) v1 c v2.
Proof.
  induct fuel; intros.
  - invert H.
  - induct c; try eapply IHfuel with (v2 := v1); try equality.
    1: {
      invert H; propositional.
      pose proof (IHfuel v1 c1 x); propositional.
      pose proof (IHfuel x c2 v2); propositional.
      exists x.
      econstructor; propositional.
    }
    1: {
      invert H; propositional.
      1: {
        invert H0; propositional.
        apply (IHfuel v1 c1 v2) in H2.
        econstructor.
        exists x; propositional.
      }
      econstructor 2; propositional.
      apply (IHfuel v1 c2 v2) in H1.
      assumption.
    }
    invert H; propositional.
    1: {
      invert H0; invert H; propositional.
      econstructor.
      exists x.
      exists x0.
      propositional.
      1: apply (IHfuel v1 c x0) in H1; assumption.
      apply (IHfuel x0 (While e c) v2) in H3; assumption.
    }
    subst.
    econstructor 2; propositional; trivial.
Qed.

(* But first, we need a helper lemma run_monotone.
   Hint: Here, some proof automation might pay off!
   You could try writing a "repeat match goal" loop, to do all possible
   simplifications on your hypotheses, and then use "eauto" to solve
   the goal. Maybe you need to increase the maximum search depth of eauto;
   in our solution, we had to write "eauto 10" instead of just "eauto",
   which defaults to "eauto 5".
   And note that "eauto" does not know about linear arithmetic by default,
   so either you have to register that as an extern hint, but a simpler
   way here would be to use the lemma "le_S_n" to turn "S fuel1 <= S fuel2"
   into "fuel1 <= fuel2", which will be needed for the IH. *)
Lemma run_monotone: forall fuel1 fuel2 v1 c v2,
    fuel1 <= fuel2 ->
    run fuel1 v1 c v2 ->
    run fuel2 v1 c v2.
Proof.
  induct fuel2; intros; cases fuel1; try equality; try linear_arithmetic.
  1: invert H0.
  invert H; try assumption.
  specialize (IHfuel2 v1 c v2).
  propositional.
  apply run_with_more_fuel.
  assumption.
Qed.

(* Now let's define proof rules to get the same "API" for "wrun" as for "eval".
   Hint: Again, some proof automation might simplify the task (but manual proofs are
   possible too, of course). *)

Ltac blah :=
  repeat match goal with
    | [ H : interp ?E ?V 0 |- run _ ?V (While ?E _) _ ] => econstructor 2; propositional
    | [ H : interp ?E ?V 0 |- run _ ?V (If ?E _ _) _ ] => econstructor 2; propositional
    | [ |- run _ _ _ _ ] => econstructor; propositional
    | [ |- run _ _ _ _ ] => econstructor; propositional
    | [ H : run ?F1 ?V1 ?C ?V2 |- run ?F2 ?V1 ?C ?V2 ] =>
        apply run_monotone with (fuel1 := F1) (fuel2 := F2);
        propositional; try linear_arithmetic; try equality
    | [ H : run _ ?V1 ?C ?V2 |- run _ ?v1 ?C ?V2 ] => unify v1 V1
    | [ H : run _ ?V1 ?C ?V2 |- run _ ?V1 ?C ?v2 ] => unify v2 V2
    | [ H : run _ _ ?C1 _ |- run _ _ (Sequence ?C1 ?C2) _ ] => econstructor
    | [ H : interp ?E ?V ?A |- interp ?E ?V ?a ] => unify a A
  end; try eexists; propositional; try linear_arithmetic; try equality; try assumption.

Lemma WRunSkip: forall v,
    wrun v Skip v.
Proof.
  simplify; econstructor.
  instantiate (1 := 1).
  blah.
Qed.

Lemma WRunAssign: forall v x e a,
    interp e v a ->
    wrun v (Assign x e) (v $+ (x, a)).
Proof.
  simplify; econstructor.
  instantiate (1 := 1).
  blah.
Qed.

Lemma WRunSeq: forall v1 c1 vmid c2 v2,
    wrun v1 c1 vmid ->
    wrun vmid c2 v2 ->
    wrun v1 (Sequence c1 c2) v2.
Proof.
  simplify.
  invert H.
  invert H0.
  econstructor.
  instantiate (1 := S (x + x0)).
  blah.
Qed.

Lemma WRunIfTrue: forall v e then_ else_ v',
  (exists a, interp e v (S a))
  -> wrun v then_ v'
  -> wrun v (If e then_ else_) v'.
Proof.
  simplify.
  invert H.
  invert H0.
  econstructor.
  instantiate (1 := S x0).
  blah; blah.
Qed.

Lemma WRunIfFalse: forall v e then_ else_ v',
  interp e v 0
  -> wrun v else_ v'
  -> wrun v (If e then_ else_) v'.
Proof.
  simplify.
  (*invert H.*)
  invert H0.
  econstructor.
  instantiate (1 := S x).
  blah.
Qed.

Lemma WRunWhileTrue: forall v e body v' v'',
  (exists a, interp e v (S a))
  -> wrun v body v'
  -> wrun v' (While e body) v''
  -> wrun v (While e body) v''.
Proof.
  simplify.
  invert H.
  invert H0.
  invert H1.
  econstructor.
  instantiate (1 := S (x0 + x1)).
  blah; blah; blah.
Qed.

Lemma WRunWhileFalse: forall v e body,
  interp e v 0
  -> wrun v (While e body) v.
Proof.
  simplify.
  econstructor.
  instantiate (1 := 1).
  blah.
Qed.

(* Now, thanks to these helper lemmas, proving the direction from eval to wrun
   becomes easy: *)
Theorem eval_to_wrun: forall v1 c v2,
    eval v1 c v2 ->
    wrun v1 c v2.
Proof.
  induct c; intros.

  1: invert H; apply WRunSkip.
  1: invert H; eapply WRunAssign; try apply values_to_interp; trivial.
  1: {
    invert H.
    eapply WRunSeq; try instantiate (1 := v0); try apply IHc1; try apply IHc2; admit.
  }
  1: {
    repeat invert H; try eapply WRunIfTrue;
      try exists x; try apply values_to_interp; try equality; try apply IHc2; try assumption.
      1: invert H5; apply values_to_interp in H; exists x; assumption.
      2: { 
        invert H5. apply values_to_interp in H; exists x; assumption.
    repeat invert H; try eapply WRunIfFalse; try eapply WRunIfTrue;
      try exists x; try apply values_to_interp; try equality;
      try apply IHc1; try apply IHc2; try assumption.
      3: {
Admitted.

(* The following definitions are needed because of a limitation of Coq
   (the kernel does not recognize that a parameter can be instantiated by an
   inductive type).
   Please do not remove them! *)
Definition values_alias_for_grading := values.
Definition eval_alias_for_grading := eval.

(* You've reached the end of this pset, congratulations! *)

(* ****** Everything below this line is optional ****** *)

(* Let's take the deterministic semantics we used in OperationalSemantics.v, but
   prefix them with "d" to mark them as deterministic: *)

Fixpoint dinterp(e: arith)(v: valuation): nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => dinterp e1 v + dinterp e2 v
  end.

Inductive deval: valuation -> cmd -> valuation -> Prop :=
| DEvalSkip: forall v,
    deval v Skip v
| DEvalAssign: forall v x e,
    deval v (Assign x e) (v $+ (x, dinterp e v))
| DEvalSeq: forall v c1 v1 c2 v2,
    deval v c1 v1 ->
    deval v1 c2 v2 ->
    deval v (Sequence c1 c2) v2
| DEvalIfTrue: forall v e thn els v',
    dinterp e v <> 0 ->
    deval v thn v' ->
    deval v (If e thn els) v'
| DEvalIfFalse: forall v e thn els v',
    dinterp e v = 0 ->
    deval v els v' ->
    deval v (If e thn els) v'
| DEvalWhileTrue: forall v e body v' v'',
    dinterp e v <> 0 ->
    deval v body v' ->
    deval v' (While e body) v'' ->
    deval v (While e body) v''
| DEvalWhileFalse: forall v e body,
    dinterp e v = 0 ->
    deval v (While e body) v.

(* Now let's prove that if a program evaluates to a valuation according to the
   deterministic semantics, it also evaluates to that valuation according to
   the nondeterministic semantics (the other direction does not hold, though). *)
Theorem deval_to_eval: forall v1 v2 c,
    deval v1 c v2 ->
    eval v1 c v2.
Proof.
Admitted.

(* In deterministic semantics, Fixpoints work a bit better, because they
   can return just one value, and let's use "option" to indicate whether
   we ran out of fuel: *)
Fixpoint drun(fuel: nat)(v: valuation)(c: cmd): option valuation. Admitted.

(* More open-ended exercise:
   Now we have six different definitions of semantics:

                        deterministic     nondeterministic

   Inductive            deval             eval

   Wrapped Fixpoint     dwrun             wrun

   Fixpoint             drun              run

   We have proved that all the nondeterministic semantics are equivalent among
   each other.
   If you want, you could also prove that all the deterministic semantics are
   equivalent among each other and experiment whether it's worth creating an
   "Inductive"-like API for "dwrun", or whether you're ok dealing with drun's
   existentials when proving deval_to_drun.
   Moreover, we have proved that "deval" implies "eval", so every definition in
   the left column of the above table implies every definition in the right
   column of the table.
   If you're curious to learn more about the trade-offs between Inductive Props
   and Fixpoints, you can try to prove some of these implications directly,
   and see how much harder than "deval_to_eval" it is (we believe that
   "deval_to_eval" is the simplest one).
 *)


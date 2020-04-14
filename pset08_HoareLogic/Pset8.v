(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 8 *)

Require Import Frap.

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu)
 * Adam Chlipala (adamc@csail.mit.edu) 
 *)

Set Implicit Arguments.

(** * Hoare Logic with Input/Output Traces *)

(* Hoare logic as covered in lecture is only the beginning, so far as
 * programming features that can be supported. In this problem set, we
 * will implement one of variant, a Hoare logic that deals with
 * input/output traces.
 *
 * Behaviors of a program can be defined as sequences of communications with
 * the outside world. Hoare logic certainly can be used for proving properties
 * about program behaviors. Besides valuation and heap, we will need to keep
 * track of traces of a program to ensure the properties we want, sometimes by
 * proving invariants in the middle of the program.
 *
 * The problem set consists of 4 tasks; basically we ask you to formally prove 
 * the correctness of some programs using Hoare logic:
 * 1) To design a big-step operational semantics of the given language.
 * 2) To define a Hoare logic for the language, and to prove the consistency
 *    between the semantics and the logic.
 * 3) To verify three example programs we provide, using Hoare logic.
 * 4) To design your own program and to verify it.
 *)

(** * Language syntax *)

(* There is nothing special with the definitions of [exp] and [bexp]; they are
 * exactly same as we've seen in the lecture.
 *)
Inductive exp :=
| Const (n : nat)
| Var (x : string)
| Read (e1 : exp)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| Mult (e1 e2 : exp).

Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

(* [heap] and [valuation] are also as usual. *)
Definition heap := fmap nat nat.
Definition valuation := fmap var nat.

(* Besides [heap] and [valuation], we have one more component to verify using 
 * Hoare logic, called [io]. We keep track of inputs and outputs of a certain
 * program, regarding them as meaningful communication with the outside world.
 * When a program is executed, it generates [trace], which is a list of [io]s,
 * meaning inputs and outputs that occurred during the execution. Traces are
 * also called behaviors of a program.
 *)
Inductive io := In (v : nat) | Out (v : nat).
Definition trace := list io.

(* We now have two types of assertions: [iassertion] is used only for asserting 
 * properties of internal states. [assertion] can be used for asserting 
 * properties of [trace]s as well as internal states.
 *)
Definition iassertion := heap -> valuation -> Prop.
Definition assertion := trace -> heap -> valuation -> Prop.

(* [cmd] has more constructors than what we've seen.  The new ones are called
 * [Input] and [Output]. As expected, semantically they generates [io]s,
 * eventually forming a [trace] of a program.
 *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Write (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd)
| While_ (inv : assertion) (be : bexp) (body : cmd)

| Assert (a : iassertion) (* Note that we are using [iassertion], not 
                           * [assertion], for [Assert]. While [valuation] and
                           * [heap] are internal states directly manipulated by
                           * a program, [trace] is rather an abstract notion for
                           * defining a behavior of a program.
                           *)

(* The new constructors are below! *)
| Input (x : var) (* [Input] takes an input from the external world and assigns
                   * the value to the local variable [x].
                   *)
| Output (e : exp). (* [Output] prints the value of [e]. *)

(** We here provide fancy notations for our language. *)

Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Notation "*[ e ]" := (Read e) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Mult : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | Read dst' => Write dst' src
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'when' b 'then' then_ 'else' else_ 'done'" :=
  (If_ b then_ else_) (at level 75, b at level 0) : cmd_scope.
Notation "{{ I }} 'while' b 'loop' body 'done'" := (While_ I b body) (at level 75) : cmd_scope.
Notation "'assert' {{ I }}" := (Assert I) (at level 75) : cmd_scope.
Notation "x '<--' 'input'" := (Input x) (at level 75) : cmd_scope.
Notation "'output' e" := (Output e) (at level 75) : cmd_scope.
Delimit Scope cmd_scope with cmd.

Infix "+" := plus : reset_scope.
Infix "-" := Init.Nat.sub : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.


(** * Task 1: A big-step operational semantics for commands *)

(* Your first task is to define a big-step operational semantics for commands.
 * While it should be very similar to what we've seen in class, it should
 * also represent something about [io]s (or [trace]). Make sure the semantics
 * captures the effects of [Input]/[Output] on [trace]s. The most
 * recent event should appear at the *front* of the list in the trace.
 *
 * We provide the signature of the big-step semantics below. Replace the
 * [Axiom] below with your own definition of the semantics.
 * The first three arguments are the trace, heap, and valuation before execution,
 * and the final three arguments are the trace, heap, and valuation after execution.

 * Again, the task for this pset is to *extend* the framework from
 * frap/HoareLogic.v, not to reinvent it. In particular, if you are
 * having trouble with a construct other than input or output, the
 * basic version should be able to help you out.
 *)

(** * Define your semantics here! *)

(* Shorthand notation for looking up in a finite map, returning zero if the key
 * is not found *)
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

(* Start of expression semantics: meaning of expressions *)
Fixpoint eval (e : exp) (h : heap) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v $! x
  | Read e1 => h $! eval e1 h v
  | Plus e1 e2 => eval e1 h v + eval e2 h v
  | Minus e1 e2 => eval e1 h v - eval e2 h v
  | Mult e1 e2 => eval e1 h v * eval e2 h v
  end.

(* Meaning of Boolean expressions *)
Fixpoint beval (b : bexp) (h : heap) (v : valuation) : bool :=
  match b with
  | Equal e1 e2 => if eval e1 h v ==n eval e2 h v then true else false
  | Less e1 e2 => if eval e2 h v <=? eval e1 h v then false else true
  end.

Inductive exec : trace ->heap -> valuation -> cmd -> trace -> heap -> valuation -> Prop :=
| ExSkip : forall t h v,
  exec t h v Skip t h v
| ExAssign : forall t h v x e,
  exec t h v (Assign x e) t h (v $+ (x, eval e h v))
| ExWrite : forall t h v e1 e2,
  exec t h v (Write e1 e2) t (h $+ (eval e1 h v, eval e2 h v)) v
| ExSeq : forall t1 h1 v1 c1 t2 h2 v2 c2 t3 h3 v3,
  exec t1 h1 v1 c1 t2 h2 v2
  -> exec t2 h2 v2 c2 t3 h3 v3
  -> exec t1 h1 v1 (Seq c1 c2) t3 h3 v3
| ExIfTrue : forall t1 h1 v1 b c1 c2 t2 h2 v2,
  beval b h1 v1 = true
  -> exec t1 h1 v1 c1 t2 h2 v2
  -> exec t1 h1 v1 (If_ b c1 c2) t2 h2 v2
| ExIfFalse : forall t1 h1 v1 b c1 c2 t2 h2 v2,
  beval b h1 v1 = false
  -> exec t1 h1 v1 c2 t2 h2 v2
  -> exec t1 h1 v1 (If_ b c1 c2) t2 h2 v2
| ExWhileFalse : forall I t h v b c,
  beval b h v = false
  -> exec t h v (While_ I b c) t h v
| ExWhileTrue : forall I t1 h1 v1 b c t2 h2 v2 t3 h3 v3,
  beval b h1 v1 = true
  -> exec t1 h1 v1 c t2 h2 v2
  -> exec t2 h2 v2 (While_ I b c) t3 h3 v3
  -> exec t1 h1 v1 (While_ I b c) t3 h3 v3
| ExAssert : forall t h v (a : iassertion),
  a h v
  -> exec t h v (Assert a) t h v
| ExInput : forall t h v x xv,
  exec t h v (Input x) (In xv :: t) h (v $+ (x, xv))
| ExOutput : forall t h v e,
  exec t h v (Output e) (Out (eval e h v) :: t) h v.


(** * Task 2 : Hoare logic *)

(* We also ask you to define a Hoare logic for our language. The logic should
 * derive triples of the form {{ P }} c {{ Q }}, where "P" and "Q" have type
 * [assertion] and "c" has type [cmd]. It should be also very similar to the
 * Hoare logic we've defined in class.
 *)

(* The logic should be consistent with the semantics you defined, so we
 * also ask you to prove a soundness relation between your Hoare logic and your
 * semantics.  You will need this consistency to prove the correctness of
 * example programs we will provide soon.
 *)

(** Task 2-1: Define your Hoare logic here! *)

Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
| HtSkip : forall P, hoare_triple P Skip P
| HtAssign : forall (P : assertion) x e,
  hoare_triple P (Assign x e) (fun t h v => exists v', P t h v' /\ v = v' $+ (x, eval e h v'))
| HtWrite : forall (P : assertion) (e1 e2 : exp),
  hoare_triple P (Write e1 e2) (fun t h v => exists h', P t h' v /\ h = h' $+ (eval e1 h' v, eval e2 h' v))
| HtSeq : forall (P Q R : assertion) c1 c2,
  hoare_triple P c1 Q
  -> hoare_triple Q c2 R
  -> hoare_triple P (Seq c1 c2) R
| HtIf : forall (P Q1 Q2 : assertion) b c1 c2,
  hoare_triple (fun t h v => P t h v /\ beval b h v = true) c1 Q1
  -> hoare_triple (fun t h v => P t h v /\ beval b h v = false) c2 Q2
  -> hoare_triple P (If_ b c1 c2) (fun t h v => Q1 t h v \/ Q2 t h v)
| HtWhile : forall (I P : assertion) b c,
  (forall t h v, P t h v -> I t h v)
  -> hoare_triple (fun t h v => I t h v /\ beval b h v = true) c I
  -> hoare_triple P (While_ I b c) (fun t h v => I t h v /\ beval b h v = false)
| HtAssert : forall (P : assertion) (I : iassertion),
  (forall t h v, P t h v -> I h v)
  -> hoare_triple P (Assert I) P
| HtConsequence : forall (P Q P' Q' : assertion) c,
  hoare_triple P c Q
  -> (forall t h v, P' t h v -> P t h v)
  -> (forall t h v, Q t h v -> Q' t h v)
  -> hoare_triple P' c Q'
| HtInput : forall (P : assertion) x,
  hoare_triple P (Input x) (fun t h v => exists xv v' t', P t' h v' /\ v = v' $+ (x, xv) /\ t = (In xv :: t'))
| HtOutput : forall (P : assertion) (e : exp),
  hoare_triple P (Output e) (fun t h v => exists t', P t' h v /\ t = (Out (eval e h v) :: t')).

Lemma HtStrengthenPost : forall (P Q Q' : assertion) c,
  hoare_triple P c Q
  -> (forall t h v, Q t h v -> Q' t h v)
  -> hoare_triple P c Q'.
Proof.
  simplify; eapply HtConsequence; eauto.
Qed.

Notation "[[ tr , h , v ]] ~> e" := (fun tr h v => e%reset) (at level 90).
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c%cmd Q) (at level 90, c at next level).

(** Task 2-2: Prove the consistency theorem. *)

(* Let's prove that the intuitive description given above really applies to this
 * predicate.  First, a lemma, which is difficult to summarize intuitively!
 * More or less precisely this obligation shows up in the main proof below. *)
Lemma hoare_triple_big_step_while: forall (I : assertion) b c,
  (forall t h v t' h' v', exec t h v c t' h' v'
                     -> I t h v
                     -> beval b h v = true
                     -> I t' h' v')
  -> forall t h v t' h' v', exec t h v (While_ I b c) t' h' v'
                       -> I t h v
                       -> I t' h' v' /\ beval b h' v' = false.
Proof.
  induct 2; eauto.
Qed.

Theorem hoare_triple_big_step :
  forall pre c post,
    hoare_triple pre c post ->
    forall t h v t' h' v',
      exec t h v c t' h' v' ->
      pre t h v -> post t' h' v'.
Proof.
    induct 1; eauto; invert 1; eauto; simplify.

    eapply hoare_triple_big_step_while; try eauto.

    exists xv. exists v. exists t. propositional.
Qed.


(** * Task 3: Verification of some example programs *)

(* Now it's time to verify programs using the Hoare logic you've just defined!
 * We provide three example programs and three corresponding correctness 
 * theorems. You are required to prove the theorems stated below using Hoare
 * logic.
 *)

(** Task 3-1: adding two inputs -- prove [add_two_inputs_ok] *)

Example add_two_inputs :=
  ("x" <-- input;;
   "y" <-- input;;
   output ("x" + "y"))%cmd.

Theorem add_two_inputs_ok:
  forall tr h v tr' h' v',
    exec tr h v add_two_inputs tr' h' v' ->
    tr = nil ->
    exists vx vy, tr' = [Out (vx + vy); In vy; In vx].
Proof.
    simplify.
    invert H.
    invert H6.
    invert H10.
    invert H4.
    invert H8.
    exists xv.
    exists xv0.
    simplify.
    equality.
Qed.

(** Task 3-2: finding the maximum of three numbers -- prove [max3_ok] *)

Example max3 :=
  ("x" <-- input;;
   "y" <-- input;;
   "z" <-- input;;
   when "x" < "y" then
     when "y" < "z" then
       output "z"
     else 
       output "y"
     done
   else
     when "x" < "z" then
       output "z"
     else
       output "x"
     done
   done)%cmd.

Inductive max3_spec : trace -> Prop :=
| M3s: forall x y z mx,
    mx >= x ->
    mx >= y ->
    mx >= z ->
    (mx = x \/ mx = y \/ mx = z) ->
    max3_spec [Out mx; In z; In y; In x].

Theorem max3_ok:
  forall tr h v tr' h' v',
    exec tr h v max3 tr' h' v' ->
    tr = nil ->
    max3_spec tr'.
Proof.
    simplify.
    invert H. invert H6.
    invert H10. invert H4.
    invert H8. invert H4.

    invert H9.
    invert H8.
    invert H10.
    all: simplify; cases (xv0 <=? xv); cases (xv1 <=? xv0); try linear_arithmetic; try equality.
    1: {
        invert H11.
        simplify.
        econstructor; linear_arithmetic.
    }
    1: {
        invert H11.
        simplify.
        econstructor; linear_arithmetic.
    }
    1: {
        invert H10.
        invert H9.
        invert H11.
        simplify.
        all: simplify; cases (xv1 <=? xv); try linear_arithmetic; try equality.
        invert H11.
        simplify.
        econstructor; linear_arithmetic.
    }
    invert H10.
    invert H9.
    invert H11.
    simplify.
    all: simplify; cases (xv1 <=? xv); try linear_arithmetic; try equality.
    1: econstructor; linear_arithmetic.
    invert H11.
    simplify.
    econstructor; linear_arithmetic.
Qed.

(** Task 3-3: Fibonacci sequence -- prove [fibonacci_ok] *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | O => 1
  | S n' =>
    match n' with
    | O => 1
    | S n'' => fib n' + fib n''
    end
  end.

Inductive fibonacci_spec : trace -> Prop :=
| Fs0: fibonacci_spec nil
| Fs1: fibonacci_spec [Out 1]
| Fs2: fibonacci_spec [Out 1; Out 1]
| Fsn:
    forall x y tr,
      fibonacci_spec (Out y :: Out x :: tr) ->
      fibonacci_spec (Out (x + y) :: Out y :: Out x :: tr).

Example fibonacci (n: nat) :=
  ("cnt" <- 0;;
   "x" <- 0;;
   "y" <- 1;;
   output "y";;
   {{ [[ t , h , v ]] ~> exists t',
       (v $! "cnt" = 0 /\ v $! "x" = 0 /\ v $! "y" = 1 /\ t = (Out 1 :: nil)) \/
       (v $! "cnt" = 1 /\ v $! "x" = 1 /\ v $! "y" = 1 /\ t = (Out 1 :: Out 1 :: nil)) \/ 
       (v $! "cnt" >= 2 /\ v $! "y" = fib (v $! "cnt") /\ v $! "x" = fib (v $! "cnt" - 1)
                        /\ t = (Out (v $! "y") :: Out (v $! "x") :: t')
                        /\ fibonacci_spec t) }}
   while "cnt" < n loop
     "tmp" <- "y";;
     "y" <- "x" + "y";;
     "x" <- "tmp";;
     "cnt" <- "cnt" + 1;;
     output "y"
   done)%cmd.

Ltac invert_commands := repeat match goal with
                               | [ H : exec _ _ _ (Seq _ _) _ _ _ |- _ ] => invert H
                               | [ H : exec _ _ _ (Assign _ _) _ _ _ |- _ ] => invert H
                               | [ H : exec _ _ _ (Input _) _ _ _ |- _ ] => invert H
                               | [ H : exec _ _ _ (Output _) _ _ _ |- _ ] => invert H
                               end; simplify.

Ltac ht1 := apply HtSkip || apply HtAssign || apply HtWrite || eapply HtSeq
            || eapply HtIf || eapply HtWhile || eapply HtAssert
            || eapply HtInput || eapply HtOutput.

Ltac t := cbv beta; propositional; subst;
          repeat match goal with
                 | [ H : ex _ |- _ ] => invert H; propositional; subst
                 end;
          simplify;
          repeat match goal with
                 | [ _ : context[?a <=? ?b] |- _ ] => destruct (a <=? b); try discriminate
                 | [ H : ?E = ?E |- _ ] => clear H
                 end; simplify; propositional; auto; try equality; try linear_arithmetic.

Ltac ht := simplify; repeat ht1; t.

Lemma fibonacci_ok' (n: nat): forall n,
  {{ [[ t , h , v ]] ~> t = nil }}
  fibonacci n
  {{ [[ t , h , v ]] ~> exists t',
      (v $! "cnt" = 0 /\ v $! "x" = 0 /\ v $! "y" = 1 /\ t = (Out 1 :: nil)) \/
      (v $! "cnt" = 1 /\ v $! "x" = 1 /\ v $! "y" = 1 /\ t = (Out 1 :: Out 1 :: nil)) \/ 
      (v $! "cnt" >= 2 /\ v $! "y" = fib (v $! "cnt") /\ v $! "x" = fib (v $! "cnt" - 1)
                       /\ t = (Out (v $! "y") :: Out (v $! "x") :: t')
                       /\ fibonacci_spec t) }}.
Proof.
  simplify.
  eapply HtSeq; try apply HtAssign.
  eapply HtSeq; try apply HtAssign.
  eapply HtSeq; try apply HtAssign.
  eapply HtSeq.
  apply HtOutput.

  eapply HtStrengthenPost.

  eapply HtWhile.

  1: {
    simplify.
    ht.
    exists nil.
    equality.
  }

  1: {
    ht.
    eapply HtStrengthenPost.
    eapply HtOutput.
    ht.
    1: {
      rewrite H; rewrite H0; rewrite H1; simplify.
      exists (x0).
      right.
      left.
      propositional.
    }
    1: {
      rewrite H; rewrite H0; rewrite H1; simplify.
      exists (Out 1 :: nil).
      right.
      right.
      propositional; try linear_arithmetic.
        replace 2 with (1 + 1); try linear_arithmetic.
        econstructor.
        econstructor.
    }
    rewrite H; rewrite H1; simplify.
    eexists.
    right.
    right.
    propositional.
    1: linear_arithmetic.
    1: {
      symmetry.
      cases (x1 $! "cnt" + 1); try linear_arithmetic.
      assert (x1 $! "cnt" = n1); try linear_arithmetic; subst.
      remember (x1 $! "cnt") as k.
      assert (exists k', k = S k').
      1: exists (k - 1); linear_arithmetic.
      simplify.
      invert H2.
      cases (x1 $! "cnt"); try linear_arithmetic.
      replace (S n1 - 1) with n1; try linear_arithmetic.
    }
    cases (x1 $! "cnt"); simplify; try linear_arithmetic.
    invert H0; simplify; try linear_arithmetic.
    cases n1; try linear_arithmetic.
    simplify.
    cases n1; try linear_arithmetic.
    cases (S n1 + 1); try linear_arithmetic.
    subst.
    invert Heq0.
    cases n1; try linear_arithmetic.
    1: simplify; equality.
    replace (S n1 + 1) with (S (S n1)); try linear_arithmetic.
    simplify.
    equality.
    econstructor.
    rewrite <- H1.
    rewrite <- H.
    assumption.
  }

  ht.
Qed.

Theorem fibonacci_ok (n: nat):
  forall tr h v tr' h' v',
    exec tr h v (fibonacci n) tr' h' v' ->
    tr = nil ->
    fibonacci_spec tr'.
Proof.
  simplify.
  eapply hoare_triple_big_step with (c := fibonacci n) (t := tr) (t' := tr'); try eassumption.
  (*eapply hoare_triple_big_step; try eassumption.*)
  1: {
    eapply HtStrengthenPost.
    1: eapply fibonacci_ok'; assumption.
    simplify.
    invert H1.
    propositional; subst.
    1: constructor.
    1: constructor.
  }
  simplify.
  assumption.
Qed.


(** * Task 4-1: please estimate the time you have spent on this pset so far:

  space for work provided here (not graded): 14

*)

(** * Task 4-2: please subtract the answer of 4-1 from 8 hours:
   (8 hours is our target time when designing these psets):

  space for work provided here (not graded): 6

*)

(** * Task 4-3: Implement your own program to verify. *)

(* The last task is to implement your own program and to verify its correctness
 * using Hoare logic. Note that the three examples we provided above had nothing
 * to do with [heap]s. Design a program that uses the heap and that is more
 * complicated than the first example above, and prove it correct. Please take
 * care to estimate the difficulty of the verification task you are about to
 * undertake, and consider it in the context of the last two answers.
 * We are not expecting this program to use a noteworthy data structure or
 * algorithm. However, your program should at least either read or write the
 * heap, and either accept input or produce output, and the relationship
 * between these two interactions should be verified. There is no extra credit
 * for doing more, but feel free to prove to your heart's content -- we won't
 * take off any points either, and we'll help you in office hours if we can.
 *)

(** Define your own program and prove its correctness here! *)

Example index_in_3_inputs :=
  ( "n0" <-- input;;
    "n1" <-- input;;
    "n2" <-- input;;
    *[0] <- "n0";;
    *[1] <- "n1";;
    *[2] <- "n2";;
    "index" <-- input;;
    output *["index"]
  )%cmd.

Inductive index_spec : trace -> Prop :=
| Index0: forall n0 n1 n2, index_spec [Out n0; In 0; In n2; In n1; In n0]
| Index1: forall n0 n1 n2, index_spec [Out n1; In 1; In n2; In n1; In n0]
| Index2: forall n0 n1 n2, index_spec [Out n2; In 2; In n2; In n1; In n0]
| Index_invalid: forall  t index, index > 2 -> index_spec t.

Theorem index_ok (n: nat):
  forall t h v t' h' v',
    exec t h v index_in_3_inputs t' h' v' ->
    t = nil ->
    index_spec t'.
Proof.
  simplify.
  invert H.
  repeat match goal with
         | [ H : exec _ _ _ _ _ _ _ |- _ ] => invert H
         end; invert_commands; simplify.
  cases xv; simplify; try econstructor; cases xv; simplify; econstructor.
Qed.

(*Example add_n_inputs :=*)
  (*( "n" <-- input;;*)
    (*"cnt" <- 0;;*)
    (*"sum" <- 0;;*)
    (*{{ [[ t , h , v ]] ~> True }}*)
    (*while "cnt" < "n" loop*)
      (*"tmp" <-- input;;*)
      (**["cnt"] <- "tmp";;*)
      (*"cnt" <- "cnt" + 1*)
    (*done;;*)
    (*"cnt" <- 0;;*)
    (*{{ [[ t , h , v ]] ~> True }}*)
    (*while "cnt" < "n" loop*)
      (*"sum" <- "sum" + *["cnt"]*)
    (*done;;*)
    (*output "sum"*)
  (*)%cmd.*)

(*Fixpoint sum_spec (l : list nat) (t : trace) : Prop :=*)
  (*match l with*)
  (*| [] => match t with*)
           (*| [] => False*)
           (*| In s :: t' => False*)
           (*| Out s :: t' => s = 0 /\ t' = [In 0]*)
           (*end*)
  (*| x :: l' => match t with*)
           (*| [] => False*)
           (*| In s :: t' => False*)
           (*| Out s :: t' => s = 0 /\ t' = [In 0]*)
  (*end.*)
(*| Ssn: forall s n x t,*)
    (*sum_spec (Out s :: t ++ [In n])*)
    (*-> sum_spec (Out (s + x) :: In x :: t ++ [In (S n)]).*)

(*Example zero_sum : sum_spec [Out 0 ; In 0].*)
(*Proof. econstructor. Qed.*)
(*Example three_sum : sum_spec [Out 3 ; In 3 ; In 1].*)
(*Proof.*)
  (*eapply Ssn with (n := 0) (x := 3) (s := 0) (t := nil).*)
  (*simplify.*)
  (*econstructor 2.*)
(*Qed.*)

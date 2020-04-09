(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 7 *)

(* Authors:
 * Peng Wang (wangpeng@csail.mit.edu)
 * Adam Chlipala (adamc@csail.mit.edu)
 * Samuel Gruetter (gruetter@mit.edu)
 *)

Require Import Frap.Frap.
Require Import Pset7Sig.

(* Delete this line if you don't like bullet points and errors like
   "Expected a single focused goal but 2 goals are focused." *)
(*Set Default Goal Selector "!".*)
Set Implicit Arguments.


(** * Subtyping *)

(* We can't resist fitting in another crucial aspect of type systems:
 * *subtyping*, which formalizes when any value of one type should also be
 * permitted as a value of some other type.  Languages like Java include
 * *nominal* subtyping, based on declared type hierarchies.  Instead, here we
 * will prove soundness of *structural* subtyping, whose rules we'll get to
 * shortly.  The simply typed lambda calculus will be our starting point. *)

(* Expression syntax *)
Inductive exp  :=
(* Our old friends from simply typed lambda calculus *)
| Var (x : var)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)
(* New features, surrounding *tuple* types, which build composite types out of
 * constituents *)
| TupleNil
(* Empty tuple (no fields *)
| TupleCons (e1 e2 : exp)
(* Nonempty tuple, where [e1] is the first field of the tuple, and [e2] is a
 * nested tuple with all the remaining fields *)
| Proj (e : exp) (n : nat)
(* Grab the [n]th field of tuple [e]. *)
.

(* Values (final results of evaluation) *)
Inductive value : exp -> Prop :=
| VAbs : forall x e1, value (Abs x e1)
| VTupleNil : value TupleNil
| VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
.

(* The next few definitions are quite routine and should be safe to skim through
 * quickly; but start paying more attention when we get to defining the
 * subtyping relation! *)

(* Substitution (not capture-avoiding, for the usual reason) *)
Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => if y ==v x then e1 else Var y
  | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
  | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  | TupleNil => TupleNil
  | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
  | Proj e2' n => Proj (subst e1 x e2') n
  end.

(* Evaluation contexts *)
Inductive context :=
| Hole
| App1 (C : context) (e2 : exp)
| App2 (v1 : exp) (C : context)
| TupleCons1 (C : context) (e2 : exp)
| TupleCons2 (v1 : exp) (C : context)
| Proj1 (C : context) (n : nat)
.

(* Plugging an expression into a context *)
Inductive plug : context -> exp -> exp -> Prop :=
| PlugHole : forall e, plug Hole e e
| PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
| PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
| PlugTupleCons1 : forall C e e' e2,
    plug C e e'
    -> plug (TupleCons1 C e2) e (TupleCons e' e2)
| PlugTupleCons2 : forall v1 C e e',
    value v1
    -> plug C e e'
    -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
| PlugProj : forall C e e' n,
    plug C e e'
    -> plug (Proj1 C n) e (Proj e' n)
.

(* Small-step, call-by-value evaluation *)
Inductive step0 : exp -> exp -> Prop :=
| Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)

(* To project field 0 out of a tuple, just grab the first component. *)
| Proj0 : forall v1 v2,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) 0) v1

(* To project field [1+n], drop the first component and continue with [n]. *)
| ProjS : forall v1 v2 n,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
.

Inductive step : exp -> exp -> Prop :=
| StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

Definition trsys_of (e : exp) :=
  {| Initial := {e}; Step := step |}.

(* Syntax of types *)
Inductive type :=
| Fun (dom ran : type)
| TupleTypeNil
| TupleTypeCons (t1 t2 : type)
.

Inductive subtype : type -> type -> Prop :=

(* Two function types are related if their components are related pairwise.
 * Counterintuitively, we *reverse* the comparison order for function domains!
 * It may be worth working through some examples to see why the relation would
 * otherwise be unsound. *)
| StFun : forall t1' t2' t1 t2,
    subtype t1 t1' ->
    subtype t2' t2 ->
    subtype (Fun t1' t2') (Fun t1 t2)

(* An empty tuple type is its own subtype. *)
| StTupleNilNil :
    subtype TupleTypeNil TupleTypeNil

(* However, a nonempty tuple type is also a subtype of the empty tuple type.
 * This rule gives rise to *width* subtyping, where we can drop some fields of
 * a tuple type to produce a subtype. *)
| StTupleNilCons : forall t1 t2,
    subtype (TupleTypeCons t1 t2) TupleTypeNil

(* We also have *depth* subtyping: we can replace tuple components with
 * subtypes. *)
| StTupleCons : forall t1' t2' t1 t2,
    subtype t1' t1 ->
    subtype t2' t2 ->
    subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
.

(* Here's a more compact notation for subtyping. *)
Infix "$<:" := subtype (at level 70).

Hint Constructors subtype : core.

(* Projecting out the nth field of a tuple type *)
Inductive proj_t : type -> nat -> type -> Prop :=
| ProjT0 : forall t1 t2,
    proj_t (TupleTypeCons t1 t2) 0 t1
| ProjTS : forall t1 t2 n t,
    proj_t t2 n t ->
    proj_t (TupleTypeCons t1 t2) (1 + n) t
.

(* Expression typing relation *)
Inductive hasty : fmap var type -> exp -> type -> Prop :=
| HtVar : forall G x t,
    G $? x = Some t ->
    hasty G (Var x) t
| HtAbs : forall G x e1 t1 t2,
    hasty (G $+ (x, t1)) e1 t2 ->
    hasty G (Abs x e1) (Fun t1 t2)
| HtApp : forall G e1 e2 t1 t2,
    hasty G e1 (Fun t1 t2) ->
    hasty G e2 t1 ->
    hasty G (App e1 e2) t2
| HtTupleNil : forall G,
    hasty G TupleNil TupleTypeNil
| HtTupleCons: forall G e1 e2 t1 t2,
    hasty G e1 t1 ->
    hasty G e2 t2 ->
    hasty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
| HtProj : forall G e n t t',
    hasty G e t' ->
    proj_t t' n t ->
    hasty G (Proj e n) t

(* This is the crucial rule: when an expression has a type, it also has any
 * supertype of that type.  We call this rule *subsumption*. *)
| HtSub : forall G e t t',
    hasty G e t' ->
    t' $<: t ->
    hasty G e t
.

(* Prove these two basic algebraic properties of subtyping. *)

Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
  induct t1; econstructor; assumption.
Qed.
Hint Resolve subtype_refl.

Lemma subtype_trans_aux : forall t1 t2, t1 $<: t2 ->
 forall t3, (t2 $<: t3 -> t1 $<: t3) /\ (t3 $<: t1 -> t3 $<: t2).
Proof.
  induct 1; intros.
  2: propositional; cases t2; cases t3; invert H; invert H0; econstructor.
  2: {
    cases t2; propositional; try invert H; try econstructor.
  }
  2: {
    propositional.
    1: {
      invert H1; try econstructor.
      1: specialize (IHsubtype1 t0); propositional.
      specialize (IHsubtype2 t4); propositional.
    }
    invert H1; try econstructor.
    1: specialize (IHsubtype1 t1'0); propositional.
    specialize (IHsubtype2 t2'0); propositional.
  }
  propositional.
  1: {
    invert H1.
    econstructor.
    1: specialize (IHsubtype1 t0); propositional.
    specialize (IHsubtype2 t4); propositional.
  }
  invert H1.
  econstructor.
  1: specialize (IHsubtype1 t1'0); propositional.
  specialize (IHsubtype2 t2'0); propositional.
Qed.

Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
  intros.
  eapply subtype_trans_aux with (t1 := t1) (t2 := t2); assumption.
Qed.
Hint Resolve subtype_trans.


Hint Constructors value plug step0 step hasty proj_t.

(* BEGIN handy tactic that we suggest for these proofs *)
Ltac tac0 :=
  match goal with
  | [ H : ex _ |- _ ] => invert H
  | [ H : _ /\ _ |- _ ] => invert H
  | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
  | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify
  | [ H : step _ _ |- _ ] => invert H
  | [ H : step0 _ _ |- _ ] => invert1 H
  (*| [ H : hasty _ ?e _, H' : value ?e |- _ ] => invert H'; invert H*)
  (*| [ H : hasty _ ?e (Fun _ _), H' : value ?e |- _ ] => apply hasty_fun in H*)
  | [ H : hasty _ _ _ |- _ ] => invert1 H
  | [ H : proj_t _ _ _ |- _ ] => invert1 H
  | [ H : plug _ _ _ |- _ ] => invert1 H
  | [ H : subtype _ _ |- _ ] => invert1 H
  | [ H : Some _ = Some _ |- _ ] => invert H
  end;
  subst.

Ltac tac := simplify; subst; propositional; repeat (tac0; simplify); try equality; eauto.
(* END handy tactic *)


(* The real prize: prove soundness of this type system.
 * We suggest starting from a copy of the type-safety proof from the book's
 * LambdaCalculusAndTypeSoundness.v.
 * The soundness argument for simply typed lambda calculus is genuinely difficult
 * (a celebrated result!). We're not expecing you to reinvent it. Rather, the
 * task of this pset is to *extend* it to cover subtyping. This will involve
 * changing some proofs, and making appropriate additional helper lemmas (there
 * are more hints on the website).
 * Trying to write this proof from scratch is *not* recommended for this pset.
 * This is in contrast to the *previous* psets, which we tried to design so that
 * they could be solved from scratch a with good understanding of the lecture
 * material. *)
Lemma tuple_nil_hasty : forall G t, hasty G TupleNil t -> t = TupleTypeNil.
Proof.
  induct 1; try equality.
  cases t; subst; invert H0.
  trivial.
Qed.
Hint Resolve tuple_nil_hasty.

Lemma tuple_cons_hasty : forall G e1 e2 t,
  hasty G (TupleCons e1 e2) t -> t = TupleTypeNil \/ exists t1 t2, t = TupleTypeCons t1 t2.
Proof.
  induct 1; simplify.
  1: right; exists t1; exists t2; equality.
  propositional.
  1: subst; left; invert H0; equality.
  invert H1; invert H2.
  rename x into t1.
  rename x0 into t2.
  invert H0.
  1: left; equality.
  right; exists t0; exists t3; equality.
Qed.
Hint Resolve tuple_cons_hasty.

Lemma hasty_tuple_cons : forall e G t1 t2,
  hasty G e (TupleTypeCons t1 t2) -> value e ->
  exists e1 e2, value e1 /\ value e2 /\ e = TupleCons e1 e2.
Proof.
  induct 1; simplify; eauto.
  1: invert H0; eauto.
  1: invert H1.
  1: invert H1.
  1: exists e1; exists e2; propositional; assumption.
  1: invert H1.
  1: {
    invert H0.
    specialize (IHhasty t1' t2'); propositional.
  }
Qed.
Hint Resolve hasty_tuple_cons.

Lemma hasty_fun : forall e1 G t1 t2,
  hasty G e1 (Fun t1 t2) -> value e1 -> exists x e, e1 = Abs x e.
Proof.
  induct e1; propositional; invert H0; eauto.
  1: apply tuple_nil_hasty in H; try equality.
  1: {
    apply tuple_cons_hasty in H; invert H.
    1: invert H0.
    invert H0. invert H. invert H0.
  }
Qed.
Hint Resolve hasty_fun.

Lemma tuple_nil_subtype : forall t, TupleTypeNil $<: t -> t = TupleTypeNil.
Proof.
  induct 1; equality.
Qed.
Hint Resolve tuple_nil_subtype.

Lemma progress : forall e t,
    hasty $0 e t -> value e \/ (exists e', step e e').
Proof.
  induct 1; simplify; try equality; propositional; tac. (*; try right; eauto.*)
  1: {
    apply hasty_fun in H; try assumption.
    invert H. invert H2.
    eauto.
  }
  7: {
    invert H0; apply hasty_tuple_cons in H; try assumption.
    1: {
      invert H. invert H0.
      propositional; subst.
      invert H1.
      right.
      exists x.
      eapply StepRule with (C := Hole); eauto.
    }
    invert H. invert H0.
    propositional; subst.
    invert H1.
    right; exists (Proj x0 n0).
    eapply StepRule with (C := Hole); eauto.
  }
  all: right; eauto.
Qed.

(*BEGIN COPY FROM LambdaCalculusAndTypeSoundness.v*)
(* Inclusion between typing contexts is preserved by adding the same new mapping
 * to both. *)
Lemma weakening_override : forall (G G' : fmap var type) x t,
  (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
  -> (forall x' t', G $+ (x, t) $? x' = Some t'
                    -> G' $+ (x, t) $? x' = Some t').
Proof.
  simplify.
  cases (x ==v x'); simplify; eauto.
Qed.

(* This lemma lets us transplant a typing derivation into a new context that
 * includes the old one. *)
Lemma weakening : forall G e t,
  hasty G e t
  -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
    -> hasty G' e t.
Proof.
  induct 1; simplify.

  constructor.
  apply H0.
  assumption.

  constructor.

  econstructor.
  instantiate (1 := t2).
  apply IHhasty; simplify.
  cases (x ==v x0); subst; simplify; try assumption.
  apply H0; assumption.
  eauto.

  econstructor.
  instantiate (1 := t1).
  apply IHhasty1.
  assumption.
  apply IHhasty2.
  assumption.

  constructor.

  constructor.
  apply IHhasty1.
  assumption.
  apply IHhasty2.
  assumption.

  specialize (IHhasty G'); propositional.
  econstructor.
  eassumption.
  assumption.

  specialize (IHhasty G'); propositional.
  econstructor.
  eassumption.
  assumption.
Qed.

(* Replacing a variable with a properly typed term preserves typing. *)
Lemma substitution : forall G x t' e t e',
  hasty (G $+ (x, t')) e t
  -> hasty $0 e' t'
  -> hasty G (subst e' x e) t.
Proof.
  induct 1; simplify.

  cases (x0 ==v x).

  simplify.
  invert H.
  eapply weakening.
  eassumption.
  simplify.
  equality.

  simplify.
  constructor.
  assumption.

  econstructor.
  cases (x0 ==v x).
  simplify.
  subst.
  eapply weakening.
  eassumption.
  simplify; cases (x ==v x0); subst; simplify; equality.

  specialize (IHhasty (G $+ (x0, t1)) x t').
  assert (G $+ (x, t') $+ (x0, t1) = G $+ (x0, t1) $+ (x, t')).
  maps_equal.
  propositional.

  econstructor.
  eapply IHhasty1; equality.
  eapply IHhasty2; equality.

  constructor.

  constructor.
  propositional.
  specialize (IHhasty1 G x t').
  propositional.
  propositional.

  econstructor.
  propositional.
  eassumption.
  assumption.
  propositional.
  eapply HtSub.
  eassumption.
  assumption.
Qed.

Lemma hasty_Abs : forall  G x e t,
  hasty G (Abs x e) t ->
  exists t1 t2, hasty (G  $+ (x, t1)) e t2 /\ Fun t1 t2 $<: t.
Proof.
  induct 1; tac.
  exists x0. exists x1.
  propositional; try assumption.
  constructor; eauto.
Qed.
Hint Resolve hasty_Abs.

Lemma hasty_TupleCons : forall G e1 e2 t,
  hasty G (TupleCons e1 e2) t ->
  exists t1 t2, hasty G e1 t1 /\ hasty G e2 t2 /\ TupleTypeCons t1 t2 $<: t.
Proof.
  induct 1; simplify; tac.
  exists x.
  exists x0.
  propositional; eauto.
Qed.
Hint Resolve hasty_TupleCons.

Lemma hasty_App : forall G e1 e2 t,
  hasty G (App e1 e2) t ->
  exists t', hasty G e1 (Fun t' t) /\ hasty G e2 t'.
Proof.
  induct 1; tac.
Qed.
Hint Resolve hasty_App.

Lemma hasty_Proj0 : forall G e t,
  hasty G (Proj e 0) t ->
  exists t', hasty G e (TupleTypeCons t t').
Proof.
  induct 1; tac.
Qed.
Hint Resolve hasty_Proj0.

Lemma hasty_Projn : forall G n e t,
  hasty G (Proj e (S n)) t ->
  exists t1 t2 t', hasty G e (TupleTypeCons t1 t2) /\ proj_t t2 n t' /\ t' $<: t.
Proof.
  induct 1; tac.

  1: {
    exists t1. exists t2. exists t.
    propositional; eauto.
  }
  1: {
    exists x. exists x0. exists x1.
    propositional; eauto.
  }
Qed.

(* We're almost ready for the other main property.  Let's prove it first
 * for the more basic [step0] relation: steps preserve typing. *)
Lemma preservation0 : forall e1 e2,
  step0 e1 e2
  -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  invert 1; simplify.

  invert H.
  invert H4.
  eapply substitution.
  eassumption.
  assumption.

  1: {
    eapply hasty_Abs in H; simplify.
    invert H.
    invert H2.
    propositional.
    eapply substitution.
    econstructor.
    eassumption.
    assert (Fun x0 x1 $<: Fun t1 t); eauto.
    invert H.
    invert H2.
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    assert (Fun x0 x1 $<: Fun t1 t); eauto.
    invert H.
    econstructor.
    eassumption.
    assumption.
  }

  1: {
    eapply hasty_App in H1; simplify.
    invert H1; propositional.
    eapply hasty_Abs in H1; simplify.
    invert H1. invert H; propositional.
    eapply substitution.
    econstructor.
    eassumption.
    invert H4.
    eauto.
    invert H4.
    econstructor.
    eassumption.
    assumption.
  }

  1: {
    eapply hasty_Proj0 in H; simplify.
    invert H.
    eapply hasty_TupleCons in H2; simplify.
    invert H2. invert H.
    propositional.
    invert H4.
    econstructor; eassumption; assumption.
  }

  eapply hasty_Projn in H. invert H. invert H2. invert H.
  propositional.
  econstructor 7.
  instantiate (1 := x1).
  2: assumption.
  eapply hasty_TupleCons in H; simplify. invert H. invert H3.
  propositional.
  (*invert H4.*)
  econstructor.
  invert H6.
  econstructor 7.
  eassumption.
  eassumption.
  assumption.
Qed.

(* We also need this key property, essentially saying that, if [e1] and [e2] are
 * "type-equivalent," then they remain "type-equivalent" after wrapping the same
 * context around both. *)
Lemma generalize_plug : forall e1 C e1',
  plug C e1 e1'
  -> forall e2 e2', plug C e2 e2'
    -> (forall t, hasty $0 e1 t -> hasty $0 e2 t)
    -> (forall t, hasty $0 e1' t -> hasty $0 e2' t).
Proof.
  induct 1; simplify.

  invert H.
  apply H0.
  assumption.

  1: {
    rename e0 into E. rename e2' into E'.
    invert H0.
    eapply hasty_App in H2. invert H2. propositional.
    econstructor.
    eapply IHplug.
    eassumption.
    assumption.
    eassumption.
    assumption.
  }

  1: {
    invert H1.
    eapply hasty_App in H3. invert H3. propositional.
    econstructor.
    eassumption.
    eapply IHplug.
    eassumption.
    assumption.
    assumption.
  }

  1: {
    rename e0 into E. rename e2' into E'.
    invert H0.
    eapply hasty_TupleCons in H2. invert H2. invert H0. propositional.
    specialize (IHplug E e'0); propositional.
    specialize (H5 x); propositional.
    apply HtTupleCons with (e1 := e'0) (t1 := x) in H2; try assumption.
    econstructor. eassumption. assumption.
  }

  1: {
    rename e2' into E'.
    invert H1.
    eapply hasty_TupleCons in H3. invert H3. invert H1. propositional.
    specialize (IHplug e2 e'0); propositional.
    specialize (H7 x0); propositional.
    apply HtTupleCons with (e1 := v1) (t1 := x) in H4; try assumption.
    econstructor. eassumption. assumption.
  }

  1: {
    invert H0.
    cases n; simplify.
    1: {
      eapply hasty_Proj0 in H2. invert H2.
      specialize (IHplug e2 e'0); propositional.
      specialize H3 with (1 := H0).
      econstructor.
      eassumption.
      econstructor.
    }
    eapply hasty_Projn in H2. invert H2. invert H0. invert H2. propositional.
    specialize (IHplug e2 e'0); propositional.
    specialize H5 with (1 := H2).
    econstructor 7. instantiate (1 := x1).
    2: assumption.
    econstructor.
    eassumption.
    econstructor.
    assumption.
  }
Qed.

(* OK, now we're almost done.  Full steps really do preserve typing! *)
Lemma preservation : forall e1 e2,
  step e1 e2
  -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  invert 1; simplify.

  eapply generalize_plug with (e1' := e1).
  eassumption.
  eassumption.
  simplify.
  eapply preservation0.
  eassumption.
  assumption.
  assumption.
Qed.
(*END COPY*)

Theorem safety :
  forall e t,
    hasty $0 e t -> invariantFor (trsys_of e)
                                 (fun e' => value e'
                                            \/ exists e'', step e' e'').
Proof.
  simplify.

  apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t).

  1: {
    apply invariant_induction; simplify; propositional; subst; try assumption.
    eapply preservation.
    1: eassumption.
    assumption.
  }

  simplify.
  eapply progress.
  eassumption.
Qed.

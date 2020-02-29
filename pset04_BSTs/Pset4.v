(** * Correctness of Binary Search Trees (BSTs) *)

(* Here we prove some correctness theorems about binary search trees (BSTs),
 * a famous data structure for finite sets, allowing fast (log-time) lookup,
 * insertion, and deletion of items. (We omit the rebalancing heuristics needed
 * to achieve worst-case log-time operations, but you will prove the correctness
 * of rotation operations these heuristics use to modify the tree.)
 * In this problem set, we show that insertion and deletion functions are
 * correctly defined by relating them to operations on functional sets. *)

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu),
 * Adam Chlipala (adamc@csail.mit.edu),
 * Benjamin Sherman (sherman@csail.mit.edu), 
 * Andres Erbsen (andreser@mit.edu)
 *)

Require Import Frap Datatypes Pset4Sig.
Require Import Compare_dec.

(* We will study binary trees of natural numbers only for convenience.
   Almost everything here would also work with an arbitrary type
   [t], but with [nat] you can use [linear_arithmetic] to prove
   goals about ordering of multiple elements (e.g., transitivity). *)
Local Notation t := nat.

(* Trees are an inductive structure, where [Leaf] doesn't have any items,
 * whereas [Node] has an item and two subtrees. Note that a [tree] can
 * contain nodes in arbitrary order, so not all [tree]s are valid binary
 * search trees. *)
(* (* Imported from Sig file: *)
Inductive tree :=
| Leaf (* an empty tree *)
| Node (d : t) (l r : tree).
*)
(* Then a singleton is just a node without subtrees. *)
Definition Singleton (v: t) := Node v Leaf Leaf.

(* MOST IMPORTANT DEFINITION: *)
(* [bst] relates a well-formed binary search tree to the set of elements it
   contains. Note that invalid trees with misordered elements are not valid
   representations of any set. All operations on a binary tree are specified
   in terms of how they affect the set that the tree represents. That
   set is encoded as function that takes a [t] and returns the proposition "[t]
   is in this set". *)
Fixpoint bst (tr : tree) (s : t -> Prop) :=
  match tr with
  | Leaf => forall x, not (s x) (* s is empty set *)
  | Node d l r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
  end.
(* ^MOST IMPORTANT DEFINITION^ *)

(* [member] computes whether [a] is in [tr], but to do so it *relies* on the
   [bst] property -- if [tr] is not a valid binary search tree, [member]
   will (and should, for performance) give arbitrarily incorrect answers. *)
Fixpoint member (a: t) (tr: tree) : bool :=
  match tr with
  | Leaf => false
  | Node v lt rt =>
    match compare a v with
    | Lt => member a lt
    | Eq => true
    | Gt => member a rt
    end
  end.

(* Here is a typical insertion routine for BSTs.
 * From a given value, we recursively compare the value with items in
 * the tree from the root, until we find a leaf whose place the new value can take. *)
Fixpoint insert (a: t) (tr: tree) : tree :=
  match tr with
  | Leaf => Singleton a
  | Node v lt rt =>
    match compare a v with
    | Lt => Node v (insert a lt) rt
    | Eq => tr
    | Gt => Node v lt (insert a rt)
    end
  end.

(* Helper functions for [delete] below. The *main task* in this pset
   is to understand, specify, and prove these helpers. *)
Definition is_leaf (tr : tree) : bool :=
  match tr with Leaf => true | _ => false end.
Fixpoint rightmost (tr: tree) : option t :=
  match tr with
  | Leaf => None
  | Node v _ rt =>
    if is_leaf rt
    then Some v
    else rightmost rt
  end.
Fixpoint delete_rightmost (tr: tree) : tree :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt =>
    if is_leaf rt
    then lt
    else Node v lt (delete_rightmost rt)
  end.
Definition merge_ordered lt rt :=
  match rightmost lt with
  | Some rv => Node rv (delete_rightmost lt) rt
  | None => rt
  end.

(* [delete] searches for an element by its value, and removes it if it is found.
   Removing an element from a leaf is degenerate (nothing to do) and
   removing the value from a node with no other children (both Leaf) can be done
   by replacing the node itself with a Leaf. Deleting a non-leaf node is
   substantially trickier because the type of [tree] does not allow for a Node
   with two subtrees but no value -- merging two trees is non-trivial. The
   implementation here removes the value anyway, and then moves the rightmost
   node of the left subtree up to replace the removed value. This is equivalent
   to using rotations to move the value to be removed into leaf position and
   removing it there. *)
Fixpoint delete (a: t) (tr: tree) : tree :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt =>
    match compare a v with
    | Lt => Node v (delete a lt) rt
    | Eq => merge_ordered lt rt
    | Gt => Node v lt (delete a rt)
    end
  end.

(* Here is a lemma that you will almost definitely want to use. *)
Example bst_iff : forall tr P Q, bst tr P -> (forall x, P x <-> Q x) -> bst tr Q.
Proof.
  induct tr; simplify.
  { rewrite <-H0. apply H with (x:=x). }
  rewrite H0 in H.
  propositional.
  { apply IHtr1 with (P:=(fun x : t => P x /\ x < d)); propositional.
    { rewrite <-H0; trivial. }
    { rewrite H0; trivial. } }
  { apply IHtr2 with (P:=(fun x : t => P x /\ d < x)); propositional.
    { rewrite <-H0; trivial. }
    { rewrite H0; trivial. } }
Qed.

(* You may want to call these tactics to use the previous lemma. *)
(* They are just a means to save some typing of [apply ... with]. *)
Ltac use_bst_iff known_bst :=
  lazymatch type of known_bst with
  | bst ?tree2 ?set2 =>
      lazymatch goal with
      | |- bst ?tree1 ?set1 =>
          apply bst_iff with (P:=set2) (Q := set1);
          lazymatch goal with
          |- bst tree2 set2 => apply known_bst
          | _ => idtac
          end
      end
  end.
Ltac use_bst_iff_assumption :=
  match goal with
  | H : bst ?t _ |- bst ?t _ =>
    use_bst_iff H
  end.
(* If you are comfortable with it, [eapply bst_iff] followed by careful
 * application of other [bst] facts (e.g., inductive hypotheses) can
 * save typing in some places where this tactic does not apply, though
 * keep in mind that forcing an incorrect choice for a ?unification
 * variable can make the goal false. *)

(* It may also be useful to know that you can switch to proving [False] by
 * calling [exfalso]. This, for example, enables you to apply lemmas that end in
 * [-> False]. Of course, only do this if the hypotheses are contradictory. *)

(* Other tactics used in our solution: apply, apply with, apply with in
 * (including multiple "with" clauses like in [use_bst_iff]), cases, propositional,
   linear_arithmetic, simplify, trivial, try, induct, equality, rewrite, assert. *)

(* Warm-up exercise: rebalancing rotations *)
(* Transcribe and prove one of the two rotations shown in [rotation1.svg] and [rotation2.svg].
   The AA-tree rebalancing algorithm applies these only if the annotations of relevant
   subtrees are in violation of a performance-critical invariant, but the rotations
   themselves are correct regardless. (These are straight from
   https://en.wikipedia.org/wiki/AA_tree#Balancing_rotations.) *)
(* Each one can be written as a simple non-recursive definition
   containing two "match" expressions that returns the original
   tree in cases where the expected structure is not present. *)

Definition rotate (T : tree) : tree :=
  match T with
  | Leaf => T
  | Node v lt rt =>
    match lt with
    | Leaf => T
    | Node lv llt lrt => Node lv llt (Node v lrt rt)
    end
  end.
Lemma bst_rotate T s (H : bst T s) : bst (rotate T) s.
Proof.
  cases T. simplify.
  1: { apply H with (x := x). }
  remember T1 as Tl.
  remember T2 as Tr.
  cases Tl.
  1: { simplify. assumption. }
  remember d as v.
  remember d0 as vl.
  remember Tl1 as Tll.
  remember Tl2 as Tlr.
  simplify.
  propositional.
  1: {
    use_bst_iff H1.
    propositional. linear_arithmetic.
  }
  1: {
    use_bst_iff H5.
    propositional.
  }
  use_bst_iff H2.
  propositional.
  linear_arithmetic.
Qed.
(* there is a hint on the class website that completely gives away the proofs
 * of these rotations. We recommend you study that code after completing this
 * exercise to see how we did it, and maybe pick up a trick or two to use below. *)

(*Lemma member_bst_imediate_node : forall a lt rt, member a (Node a lt rt) = true.*)
(*Proof.*)
  (*simplify.*)
  (*cases (compare a a).*)
  (*1: linear_arithmetic.*)
  (*1: trivial.*)
  (*linear_arithmetic.*)
(*Qed.*)

Lemma member_bst : forall tr s a, bst tr s -> member a tr = true <-> s a.
Proof.
  simplify.
  induct tr.
  1: {
    unfold member.
    propositional.
    1: equality.
    unfold bst in H.
    specialize H with (x := a).
    equality.
  }
  cases (member a tr1).
  1: {
    remember (fun x : t => s x /\ x < d) as s'.
    propositional.
    1: {
      simplify.
      specialize (IHtr1 s' a).
      subst.
      propositional.
    }
    assert (bst tr1 s').
    1: {
      simplify.
      propositional.
      subst.
      assumption.
    }
    assert (a < d).
    1: {
      specialize (IHtr1 s' a).
      propositional.
      rewrite Heqs' in H2.
      linear_arithmetic.
    }
    simplify.
    cases (compare a d).
    1: assumption.
    1: trivial.
    linear_arithmetic.
  }
  cases (member a tr2).
  1: {
    remember (fun x : t => s x /\ d < x) as s'.
    propositional.
    1: {
      simplify.
      specialize (IHtr2 s' a).
      subst.
      propositional.
    }
    assert (bst tr2 s').
    1: {
      simplify.
      propositional.
      subst.
      assumption.
    }
    assert (d < a).
    1: {
      specialize (IHtr2 s' a).
      propositional.
      rewrite Heqs' in H2.
      linear_arithmetic.
    }
    simplify.
    cases (compare a d).
    3: assumption.
    2: trivial.
    linear_arithmetic.
  }
  simplify.
  cases (compare a d).
  1: {
    remember (fun x : t => s x /\ x < d) as s'.
    propositional.
    1: equality.
    specialize (IHtr1 s' a).
    subst s'.
    propositional.
  }
  2: {
    remember (fun x : t => s x /\ d < x) as s'.
    propositional.
    1: equality.
    specialize (IHtr2 s' a).
    subst s'.
    propositional.
  }
  subst.
  propositional.
Qed.

Lemma bst_insert : forall tr s a, bst tr s ->
  bst (insert a tr) (fun x => s x \/ x = a).
Proof.
  simplify.
  induct tr.
  1: simplify; propositional; specialize (H x); propositional; linear_arithmetic.
  simplify.
  propositional.
  cases (compare a d).
  1: {
    remember (fun x : t => s x /\ x < d) as s'.
    simplify.
    propositional.
    1: {
      specialize ((IHtr1 s') a).
      propositional.
      use_bst_iff H1.
      subst.
      propositional.
      linear_arithmetic.
    }
    use_bst_iff H2.
    intros.
    propositional.
    subst.
    linear_arithmetic.
  }
  2: {
    remember (fun x : t => s x /\ d < x) as s'.
    simplify.
    propositional.
    2: {
      specialize ((IHtr2 s') a).
      propositional.
      use_bst_iff H1.
      subst.
      propositional.
      linear_arithmetic.
    }
    use_bst_iff H.
    intros; propositional; subst; linear_arithmetic.
  }
  simplify.
  propositional.
  1: {
    use_bst_iff H.
    intros; propositional; subst; linear_arithmetic.
  }
  use_bst_iff H2.
  intros; propositional; subst; linear_arithmetic.
Qed.

(* To prove [bst_delete], you will need to write specifications for its helper
   functions, find suitable statements for proving correctness by induction, and use
   proofs of some helper functions in proofs of other helper functions. The hints
   on the course website provide examples and guidance, but no longer ready-to-prove
   lemma statements. For time-planning purposes: you are not halfway done yet.
   (The Sig file also has a rough point allocation between problems.)

   It is up to you whether to use one lemma per function, multiple lemmas per
   function, or (when applicable) one lemma per multiple functions. However,
   the lemmas you prove about one function need to specify everything a caller
   would need to know about this function. *)

Lemma bst_rightmost_is_leaf : forall t, is_leaf t = true <-> rightmost t = None.
Proof.
  intros.
  induct t; simplify; try equality.
  propositional; try equality.
  cases (is_leaf t2); try equality.
Qed.
Lemma bst_rightmost_none : forall t s x, bst t s ->
  rightmost t = None -> member x t = false.
Proof.
  intros.
  induct t.
  1: simplify; equality.
  invert H0.
  cases (is_leaf t2); try equality.
  apply bst_rightmost_is_leaf with (t := t2) in H2.
  equality.
Qed.
Lemma bst_rightmost_member : forall t s rv, bst t s ->
  rightmost t = Some rv -> member rv t = true.
Proof.
  intros.
  induct t.
  1: simplify. equality.
  cases (is_leaf t2).
  1: {
    simplify.
    rewrite Heq in H0.
    invert H0.
    cases (compare rv rv); try equality; try linear_arithmetic.
  }
  simplify.
  rewrite Heq in H0.
  propositional.
  specialize (IHt2 (fun x : t => s x /\ d < x) rv).
  propositional.
  (*assert (d < rv).*)
  assert(member rv t2 = true <-> s rv /\ d < rv).
  1: {
    apply member_bst with (tr := t2) (s := (fun x : t => s x /\ d < x)) (a := rv).
    assumption.
  }
  apply H2 in H4.
  propositional.
  cases (compare rv d); try linear_arithmetic; try equality.
Qed.

Lemma bst_rightmost : forall t s rv, bst t s ->
  rightmost t = Some rv -> bst t (fun x => s x /\ ~ rv < x).
Proof.
  simplify.
  induct t.
  1: unfold rightmost in H0. equality.
  cases (is_leaf t2).
  1: {
    simplify.
    invert H0.
    cases t2.
    2: invert Heq.
    propositional.
    1: invert H2. linear_arithmetic.
    1: use_bst_iff_assumption. propositional. invert H2. linear_arithmetic.
    simplify.
    specialize (H3 x).
    propositional.
  }
  propositional.
  invert H0.
  rewrite Heq in H2.
  invert H.
  propositional.
  specialize bst_rightmost_member with (t := t2) (s := (fun x : t => s x /\ d < x)) (rv := rv).
  propositional.
  apply member_bst with (tr := t2) (s := (fun x : t => s x /\ d < x)) (a := rv) in H1; try assumption.
  simplify.
  propositional; try linear_arithmetic.
  2: {
    specialize (IHt2 (fun x : t => s x /\ d < x) rv); propositional.
    use_bst_iff_assumption.
    simplify; propositional; linear_arithmetic.
  }
  use_bst_iff_assumption.
  simplify; propositional; linear_arithmetic.
Qed.

Lemma bst_delete_rightmost : forall t s rv, bst t s ->
  rightmost t = Some rv -> bst (delete_rightmost t) (fun x => s x /\ x < rv).
Proof.
  intros.
  induct t. simplify; try equality.
  cases (is_leaf t2).
  1: {
    invert H0.
    rewrite Heq in H2.
    invert H2.
    replace (delete_rightmost (Node rv t1 t2)) with t1.
    2: unfold delete_rightmost; rewrite Heq; equality.
    invert H; propositional.
    (*use_bst_iff_assumption.*)
    (*intros.*)
    (*propositional; try linear_arithmetic.*)
    (*unfold delete_rightmost.*)
    (*assert (member x t2 = false).*)
    (*1: {*)
      (*apply bst_rightmost_is_leaf in Heq.*)
      (*apply bst_rightmost_none with (s := (fun x : t => s x /\ rv < x)) (x := x) in Heq; assumption.*)
    (*}*)
    (*cases (compare rv x).*)
    (*1: {*)
      (*assert (member x t2 = true); try apply member_bst with (tr := t2) (s := (fun x : t => s x /\ rv < x)) (a := x);*)
      (*propositional; try linear_arithmetic; try equality.*)
    (*}*)
    (*equality.*)
    (*equality.*)
  }
  invert H0.
  rewrite Heq in H2.
  invert H; propositional.
  specialize (IHt2 (fun x : t => s x /\ d < x) rv); propositional.
  replace (delete_rightmost (Node rv t1 t2)) with (Node rv t1 (delete_rightmost t2)).
  2: unfold delete_rightmost; rewrite Heq; equality.
  simplify.
  rewrite Heq.
  assert (member rv t2 = true).
  1: {
    specialize bst_rightmost_member with (t := t2) (s := (fun x : t => s x /\ d < x)) (rv := rv) as HH.
    propositional.
  }
  assert (d < rv).
  1: rewrite member_bst with (s := (fun x : t => s x /\ d < x)) in H1; propositional.
  simplify; propositional; try linear_arithmetic; try use_bst_iff_assumption; propositional; linear_arithmetic.
Qed.

Lemma bst_merge_ordered : forall tl tr (sl : t -> Prop) (sr : t -> Prop) dv,
  rightmost tl = Some dv ->
  (forall x, sr x -> dv < x) ->
  bst tl sl -> bst tr sr ->
  bst (merge_ordered tl tr) (fun x => sl x \/ sr x).
Proof.
  intros.
  cases (rightmost tl); invert H.
  (*2: {*)
    (*unfold merge_ordered.*)
    (*cases (rightmost tl); try equality.*)
    (*use_bst_iff_assumption.*)
    (*intros.*)
    (*assert (member x tl = false); try apply bst_rightmost_none with (s := sl); try assumption.*)
    (*invert H3.*)
    (*specialize member_bst with (s := sl) (a := x) (tr := tl) as H6; propositional; try equality.*)
  (*}*)
  unfold merge_ordered.
  cases (rightmost tl); try equality.
  invert Heq.

  assert (bst (delete_rightmost tl) (fun x : t => sl x /\ x < dv)).
  apply bst_delete_rightmost; assumption.
  simplify; propositional.
  1: {
    left.
    assert (member dv tl = true).
    apply bst_rightmost_member with (s := sl); assumption.
    rewrite member_bst with (a := dv) (s := sl) in H3; try assumption.
  }
  1: {
    use_bst_iff_assumption.
    propositional.
    exfalso.
    specialize (H0 x); propositional.
    linear_arithmetic.
  }
  use_bst_iff_assumption.
  intros.
  specialize (H0 x); propositional.
  specialize bst_rightmost with (t := tl) (s := sl) (rv := dv) as HH; try assumption.
  propositional.
  apply member_bst with (a := x) (s := sl) in H1; propositional; try assumption.
  apply member_bst with (a := x) (s := (fun x : t => sl x /\ (dv < x -> False))) in H6; propositional; try assumption.
Qed.

Lemma bst_delete : forall tr s a, bst tr s ->
  bst (delete a tr) (fun x => s x /\ x <> a).
Proof.
  induct tr.
  1: simplify. specialize (H x). propositional.
  intros.
  cases (compare a d).
  1: {
    simplify.
    propositional.
    cases (compare a d); simplify; try linear_arithmetic.
    propositional.
    1: linear_arithmetic.
    2: {
      use_bst_iff H2.
      propositional.
      linear_arithmetic.
    }
    specialize (IHtr1 (fun x : t => s x /\ x < d) a).
    propositional.
    use_bst_iff H1.
    propositional.
  }
  2: {
    simplify.
    propositional.
    cases (compare a d); simplify; try linear_arithmetic.
    propositional.
    1: linear_arithmetic.
    1: {
      use_bst_iff H.
      propositional.
      linear_arithmetic.
    }
    specialize (IHtr2 (fun x : t => s x /\ d < x) a).
    propositional.
    use_bst_iff H1.
    propositional.
  }
  subst.
  propositional.
  cases (rightmost tr1).
  2: {
    simplify; propositional.
    cases (compare d d); try linear_arithmetic.
    unfold merge_ordered.
    rewrite Heq.
    use_bst_iff_assumption.
    propositional; try linear_arithmetic.
    assert (member x tr1 = false).
    1: apply bst_rightmost_none with (s := (fun x : t => s x /\ x < d)); try assumption.
    apply member_bst with (a := x) in H.
    propositional.
    cases (compare d x); propositional; try equality.
  }
  replace (delete d (Node d tr1 tr2)) with (merge_ordered tr1 tr2).
  2: simplify; cases (compare d d); try linear_arithmetic; try equality.
  invert H; propositional.
  apply bst_rightmost_member with (s := (fun x : t => s x /\ x < d)) in Heq as Heq'; try assumption.
  apply member_bst with (a := n) in H as H'; propositional.
  specialize bst_merge_ordered with (tl := tr1) (tr := tr2) (dv := n) (sl := (fun x : t => s x /\ x < d)) (sr := (fun x : t => s x /\ d < x)) as HH.
  rewrite Heq in HH; propositional.
  assert (forall x : t, s x /\ d < x -> n < x).
  1: intros. linear_arithmetic.
  propositional.
  use_bst_iff_assumption.
  intros.
  propositional; try linear_arithmetic.
  cases (compare x d); propositional.
Qed.

(* Great job! Now you have proven all tree-structure-manipulating operations
   necessary to implement a balanced binary search tree. Rebalancing heuristics
   that achieve worst-case logarithmic running time maintain annotations on
   nodes of the tree (and decide to rebalance based on these). The implementation
   here omits them, but as the rotation operations are correct regardless of
   the annotations, any way of calling them from heuristic code would result in a
   functionally correct binary tree. *)

Lemma member_insert a tr s (H : bst tr s) : member a (insert a tr) = true.
Proof. eapply member_bst. eapply bst_insert. eapply H. right. congruence. Qed.
Lemma member_delete a tr s (H : bst tr s) : member a (delete a tr) = false.
Proof.
  pose proof (bst_delete tr s a H) as X.
  apply (member_bst _ _ a) in X.
  cases (member a (delete a tr)); propositional.
Qed.

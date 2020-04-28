(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 10 *)

(* Authors:
 * Adam Chlipala (adamc@csail.mit.edu),
 * Peng Wang (wangpeng@csail.mit.edu),
 * Samuel Gruetter (gruetter@mit.edu) *)

Require Import Frap Pset10Sig.

(* Programmers who start programming with threads and locks soon realize that it
 * is tricky to avoid *deadlocks*, where thread #1 is waiting to take a lock
 * held by thread #2, and thread #2 is waiting to take a lock held by thread #3,
 * and... thread #N is waiting to take a lock held by thread #1.  That's a wait
 * cycle, and none of the threads will ever make progress.
 *
 * The most common wisdom about avoiding deadlocks is to impose a *total order*
 * on the locks.  A thread is only allowed to acquire a lock that is *less than*
 * all locks it currently holds.  In this pset, we formalize a simple static
 * analysis checking that the total-order rule is obeyed, and we prove that any
 * program accepted by the analysis avoids deadlock. *)

(* Please start by reading the definitions in Pset10Sig.v! *)

(* Before diving into the proof hacking, it might be helpful to write a short
   sample program (in Coq) where thread 1 acquires lock 1 and then lock 2,
   while thread 2 tries to acquire lock 2 and then lock 1, and explain (in
   English) how a deadlock can happen: *)

Example bad: prog. Admitted.

(* FILL IN explanation here *)

(* And now, explain why the total-order rule would reject your example by copy-pasting
   the one rule which rejects it from Pset10Sig.v and briefly describing how it would
   reject it: *)

(* FILL IN explanation here *)

(* The two questions above are not graded, but we hope they help you understand
   the material better! *)

(* Since we use the [a_useful_invariant] theorem, proving [deadlock_freedom]
 * reduces to proving this lemma. *)
Lemma if_no_locks_held_then_progress' : forall h c l,
   goodCitizen {} c l
   -> finished c \/ exists h' l' c', step0 (h, {}, c) (h', l', c').
Proof.
  induct 1; simplify; eauto.
  1: {
    invert IHgoodCitizen.
    1: {
      invert H2.
      eauto.
    }
    invert H2.
    invert H3.
    invert H2.
    right.
    eauto.
  }
  1: {
    right.
    eauto.
  }
  invert H.
Qed.

Theorem if_no_locks_held_then_progress : forall h p,
     Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
     -> locksOf p = {}
     -> Forall (fun l_c => finished (snd l_c)) p
       \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
  induct 1; simplify; eauto.
  assert (locksOf l = { }).
  1: {
    destruct x.
    sets.
  }
  propositional.
  1: {
    cases x.
    cases c; eauto.
    1: {
      left.
      econstructor; simplify; eauto.
    }
    all:
      rewrite H2; sets; simplify.
    2: right; eexists; eapply StepThread1; eapply StepLock; sets.
    2: {
      right; eexists; eapply StepThread1.
      invert H.
      eapply StepUnlock; sets.
    }
    invert H.
    assert (s = { }).
    1: {
      apply sets_equal.
      simplify.
      propositional.
      assert ((fun x : nat => s x \/ locksOf l x) x = (fun _ : nat => False) x).
      1: sets.
      simplify.
      invert H3.
      propositional.
    }
    subst.
    eapply if_no_locks_held_then_progress' in H7.
    propositional; eauto.
    1: {
      invert H.
      right.
      eexists.
      eapply StepThread1; eapply StepBindProceed.
    }
    invert H.
    right.
    invert H3. invert H.
    sets.
    replace (fun _ : nat => False \/ False) with (fun _ : nat => False) by sets.
    eexists.
    eapply StepThread1; eapply StepBindRecur.
    eassumption.
  }
  cases x.
  invert H4.
  invert H3.
  right.
  eexists.
  eapply StepThread with (cs1 := c :: cs1).
  invert H1.
  rewrite H2 in H8.
  rewrite H4.
  eassumption.
Qed.

Lemma who_has_the_lock'' : forall h a l l1 c l2,
      goodCitizen l1 c l2
      -> a \in l1
      -> l1 \subseteq l
      -> finished c
         \/ (exists h' l' c', step0 (h, l, c) (h', l', c'))
         \/ (exists a', a' < a /\ a' \in l).
Proof.
  induct 1; simplify; eauto.
  2: {
    right.
    left.
    eauto.
  }
  2: {
    right.
    left.
    eauto.
  }
  2: {
    right.
    excluded_middle (exists a' : nat, a' < a /\ a' \in l); propositional.
    specialize (H a); propositional.
    SearchAbout ex not.
    apply Classical_Pred_Type.not_ex_all_not with (n := a0) in H2.
    propositional.
    left.
    eauto.
  }
  2: {
    right.
    left.
    assert (a0 \in l); sets.
    eauto.
  }
  right.
  propositional.
  1: {
    invert H4.
    specialize (H1 r).
    invert H.
    propositional; eauto.
  }
  invert H5. invert H4. invert H5.
  left.
  eauto.
Qed.

Lemma who_has_the_lock' : forall h a l l1 c,
      goodCitizen l1 c {}
      -> a \in l1
      -> l1 \subseteq l
      -> (exists h' l' c', step0 (h, l, c) (h', l', c'))
        \/ (exists a', a' < a /\ a' \in l).
Proof.
  simplify.
  assert (~ finished c); propositional.
  1: invert H; eauto; try invert H2.
  apply who_has_the_lock'' with (h := h) (a := a) (l := l) in H; try assumption.
  invert H; propositional.
Qed.

Lemma who_has_the_lock : forall l h a p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> a \in locksOf p
      -> locksOf p \subseteq l
      -> (exists h_l_p', step (h, l, progOf p) h_l_p')
        \/ (exists a', a' < a /\ a' \in l).
Proof.
  induct 1; simplify; eauto.
  1: invert H.

  cases x.
  cases c; simplify; eauto.
  1: {
    (*left.*)
    invert H.
    sets.
    assert (forall x : nat, locksOf l0 x -> l x); sets.
    invert H1.
    left.
    eapply step_cat; eassumption.
  }
  1: {
    invert H.
    assert (forall x : nat, locksOf l0 x -> l x); sets; excluded_middle (a \in locksOf l0); sets.
    1: {
      left.
      invert H4.
      eapply step_cat; eauto.
    }
    1: {
      (*eexists. eapply StepThread1.*)
      (*econstructor.*)
      eapply who_has_the_lock'' in H6.
      2: sets; eassumption.
      2: instantiate (1 := l); sets.
      propositional; eauto.
      1: {
        invert H4.
        specialize (H8 r).
        invert H8; eauto.
      }
      left.
      invert H5. invert H4. invert H5.
      eexists.
      eapply StepThread1.
      econstructor; eassumption.
    }
    left.
    invert H1.
    eapply step_cat; eauto.
  }
  1: invert H; sets.
  invert H.
  assert (s = {a0}) by sets.
  cases (a ==n a0); subst.
  1: {
    left.
    assert (a0 \in l).
    1: sets.
    eexists.
    eapply StepThread1.
    econstructor; eassumption.
  }
  assert (a \in locksOf l0); sets.
  assert (forall x : nat, locksOf l0 x -> l x); sets.
  left.
  invert H3.
  eapply step_cat; eassumption.
Qed.

Theorem if_lock_held_then_progress : forall bound a h p,
   Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
   -> a \in locksOf p
   -> a < bound
   -> Forall (fun l_c => finished (snd l_c)) p
      \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
  induct bound; simplify; eauto.
  1: invert H1.

  excluded_middle (a < bound).
  1: {
    specialize (IHbound a h p); propositional.
  }
  assert (bound = a) by linear_arithmetic.
  pose proof (who_has_the_lock (locksOf p) h a p H); try eassumption.
  assert (locksOf p \subseteq locksOf p) by sets.
  propositional.
  invert H6; propositional.
  specialize (IHbound x h p); propositional.
Qed.

Lemma deadlock_freedom' :
  forall (h : heap) (p : prog'),
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof.
  intros.
  excluded_middle (exists a, a \in locksOf p).
  (*induct 1; simplify; eauto.*)
  1: {
    invert H0.
    eapply if_lock_held_then_progress in H; try eassumption.
    2: instantiate (1 := x + 1); linear_arithmetic.
    invert H.
    1: {
      left.
      cases p; eauto.
    }
    right.
    invert H0.
    eexists.
    eassumption.
  }

  assert (locksOf p = {}).
  1: {
    Search(~ (exists _, _)).
    apply sets_equal.
    simplify.
    eapply Classical_Pred_Type.not_ex_all_not with (P := locksOf p) (n := x) in H0.
    propositional.
  }
  eapply if_no_locks_held_then_progress in H; try eassumption.
  invert H.
  1: {
    left.
    cases p; eauto.
  }
  right.
  invert H2.
  eexists.
  eassumption.
Qed.

(* Here's how we can use [a_useful_invariant] to go from [deadlock_freedom'] to
   [deadlock_freedom]: *)
Theorem deadlock_freedom :
  forall h p,
    Forall (fun c => goodCitizen {} c {}) p ->
    invariantFor (trsys_of h {} p) (fun h_l_p =>
                                      let '(_, _, p') := h_l_p in
                                      Forall finished p'
                                      \/ exists h_l_p', step h_l_p h_l_p').
Proof.
  (* To begin with, we strengthen the invariant to the one proved in Pset10Sig. *)
  simplify.
  eapply invariant_weaken.
  eauto using a_useful_invariant.

  (* What's left is to prove that this invariant implies deadlock-freedom. *)
  first_order.
  destruct s as [[h' ls] p'].
  invert H0.

  (* We don't actually need to use the [disjointLocks] property.  It was only
   * important in strengthening the induction to prove that other invariant. *)
  clear H6.

  (* At this point, we apply the lemma that we expect you to prove! *)
  apply deadlock_freedom'. assumption.
Qed.

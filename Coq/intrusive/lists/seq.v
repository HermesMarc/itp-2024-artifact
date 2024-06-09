From Intrusive Require Import Setup.


(* -------------------------------------------------------------------
            Sequential linked lists with a chosen endpoint
----------------------------------------------------------------------

  start
    ⤵
    ┌─────┐    ┌─────┐    ┌─────┐    ┌─────┐    
    │   *-│--> │   *-│--> │   *-│--> │ end-│--> 
    └─────┘    └─────┘    └─────┘    └─────┘    

*)

Module Seq.
Section seq.
  Context `{!heapGS Σ}.

  Definition new : val :=
  λ: "start" "end", "start" <- "end".

  Definition push : val :=
    λ: "start" "new",
      "new"   <- !"start" ;;
      "start" <- "new".

  Definition pop : val :=
    λ: "start",
        let: "rem" := ! "start" in
        "start" <- ! "rem" ;;
        "rem".

  Definition next : val :=
    λ: "start", ! "start".

(* ----------- Representation predicate for sequences ------------- *)

  Fixpoint pred (s: loc) (L: list loc) (e: loc) : iProp Σ :=
    match L with
      | []          => s ↦ #e
      | next :: L'  => s ↦ #next ∗ pred next L' e
    end.
  Notation is_seq := pred.

  Fact pred_nil {s e: loc} :
    is_seq s [] e ⊣⊢ s ↦ #e.
  Proof. done. Qed.

  Fact pred_cons {s x e: loc} (L: list loc) :
    is_seq s (x :: L) e ⊣⊢ s ↦ #x ∗ is_seq x L e.
  Proof. done. Qed.

  Lemma split {s g e: loc} (L R: list loc) :
    is_seq s (L ++ g :: R) e ⊣⊢ is_seq s L g ∗ is_seq g R e.
  Proof.
    induction L as [| x L] in s, g, e, R |- *; simpl; 
    try rewrite IHL; iSteps.
  Qed.


(* ----------------- Verifying the specifications  ---------------- *)

  Lemma new_spec {s e: loc} {v} :
    {{{ s ↦ v }}} 
      new #s #e
    {{{ RET #(); is_seq s [] e }}}.
  Proof. iSteps. Qed.

  Lemma push_spec {s l e: loc} (L: list loc) v :
    {{{ l ↦ v ∗ is_seq s L e }}} 
      push #s #l
    {{{ RET #(); is_seq s (l :: L) e }}}.
  Proof. destruct L; iSteps. Qed.

  Lemma pop_spec {s e l: loc} (L: list loc) :
    {{{ is_seq s (l :: L) e }}}
      pop #s
    {{{ v, RET #l; l ↦ v ∗ is_seq s L e }}}.
  Proof. destruct L; iSteps. Qed.

  Lemma next_spec {s n e : loc} (L R: list loc) :
    {{{ is_seq s L e }}}
      next #s
    {{{ RET #((L ++ [e]) !!! 0%nat : loc); is_seq s L e }}}.
  Proof. destruct L; iSteps. Qed.

End seq.
End Seq.

Global Opaque Seq.pred Seq.new Seq.push Seq.pop Seq.next.

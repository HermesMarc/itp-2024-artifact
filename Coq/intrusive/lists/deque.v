From Intrusive Require Import Setup Util cycle_double.

Module Deque.
Section Deque.
  Context `{!heapGS Σ}.

(* ------------------ Representation predicate  ------------------- *)

  Definition pred l (vs: list val) : iProp Σ :=
    ∃ L, DCycle.pred l L ∗ [∗ list] i ↦ l ; v ∈ L ; vs, (l +ₗ (-1)) ↦ v.
  Notation is_deque := pred.

(* --------------------- Functions on deques ---------------------- *)

Definition new : val := 
  λ: <>,
    let: "new" := AllocN #2 NONE in
    DCycle.new "new";; "new".

Definition push_front : val :=
  λ: "x" "l",
    let: "l_x" := AllocN #3 "x" in
    DCycle.insert_0 "l" ("l_x" +ₗ #1).

Definition push_back : val :=
  λ: "x" "l",
    let: "l_x" := AllocN #3 "x" in
    DCycle.insert_1 "l" ("l_x" +ₗ #1).

Definition pop_front : val :=
  λ: "l",
    if: DCycle.is_empty "l" then NONEV else
    let: "next" := DCycle.next "l" in
    let: "x" := !("next" +ₗ #-1) in
    let: "rem" := DCycle.remove_0 "l" in
    array_free ("rem" +ₗ #-1) #3 ;;
    SOME "x".

Definition pop_back : val :=
  λ: "l",
    if: DCycle.is_empty "l" then NONEV else
    let: "prev" := DCycle.prev "l" in
    let: "x" := !("prev" +ₗ #-1) in
    let: "rem" := DCycle.remove_1 "l" in
    array_free ("rem" +ₗ #-1) #3;;
    SOME "x".

(* ------------------- Verificiation of the Specs ----------------- *)

Lemma new_spec :
{{{ emp }}}
  new #()
{{{ l, RET #l; is_deque l [] }}}.
Proof. iSteps. Qed.

Lemma push_front_spec D (x: val) (l: loc) :
{{{ is_deque l D }}}
  push_front x #l
{{{ RET #(); is_deque l (x :: D) }}}.
Proof.
  iStep 21 as (Φ L l') "HL HLD ? Hl'".
  rewrite unfold_array; simpl.
  iDestruct "Hl'" as "[H0 [H1 H2]]".
  wp_apply (DCycle.insert_0_spec with "[HL H1 H2]"); iSteps.
Qed.

Lemma push_back_spec D (x: val) (l: loc) :
{{{ is_deque l D }}}
  push_back x #l
{{{ RET #(); is_deque l (D ++ [x]) }}}.
Proof.
  iStep 21 as (Φ L' l') "HL HLD HΦ Hl".
  rewrite unfold_array; simpl.
  iDestruct "Hl" as "[H0 [H1 H2]]".
  wp_apply (DCycle.insert_1_spec with "[HL H1 H2]"); iSteps.
  rewrite big_sepL2_app_same_length; auto; iSteps.
Qed.

Lemma pop_front_empty_spec (l: loc) :
{{{ is_deque l [] }}}
  pop_front #l
{{{ RET NONEV; is_deque l [] }}}.
Proof. iSteps. Qed.

Lemma pop_front_cons_spec D (l: loc) (x: val) :
{{{ is_deque l (x :: D) }}}
  pop_front #l
{{{ RET (SOMEV x); is_deque l D }}}.
Proof.
  iSteps as (Φ l' L x0 x1) "HΦ HLD Hl'2 HL Hl'".
  wp_apply (wp_array_free with "[Hl' Hl'2] [-]").
  2: { instantiate (1:= [x; x0; x1]); iSteps. }
  all: reflexivity || iSteps.
Qed.

Lemma pop_back_empty_spec (l: loc) :
{{{ is_deque l [] }}}
  pop_back #l
{{{ RET NONEV; is_deque l [] }}}.
Proof. iSteps. Qed.

Lemma pop_back_cons_spec D (l: loc) (x: val) :
{{{ is_deque l (D ++ [x]) }}}
  pop_back #l
{{{ RET (SOMEV x); is_deque l D }}}.
Proof.
  iStep 13 as (? | Φ l1 L) "? ? HLD" | "HΦ HL HLD".
  { iDestruct (big_sepL2_nil_inv_l with "HLD") as "%H".
    apply app_eq_nil in H as [_ [=]]. }
  iDestruct (big_sepL2_app_inv_r with "HLD") as (L' L2 ->) "[HLD HL2]".
  iDestruct (big_sepL2_cons_inv_r with "HL2") as (l2 L3 ->) "[Hl2 HL2]".
  iDestruct (big_sepL2_nil_inv_r with "HL2") as "%H"; subst; iClear "HL2".
  iStep 10 as "Hl".
  rewrite rev_unit; simpl. iSteps as (x0 x1) "Pl2_2 Hl Pl2".
  wp_apply (wp_array_free with "[Pl2 Pl2_2] [-]").
  2: { instantiate (1:= [x; x0; x1]); iSteps. }
  all: reflexivity || iSteps.
Qed.

End Deque.
End Deque.

(* Make the definitions of the predicate and operations opaque. *)
Global Opaque Deque.pred
              Deque.new 
              Deque.push_front  Deque.push_back
              Deque.pop_front   Deque.pop_back.

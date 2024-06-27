From Intrusive Require Import Setup Util bst.

Module Map.
Section Map.
  Context `{!heapGS Σ}.

(* ------------------ Representation predicate  ------------------- *)

(* Map that assigns a value to every key *)
Definition pred (l: loc)(m: gmap nat val) : iProp Σ :=
  ∃ m', Tree.is_Intrusive_Map l m'
∗ [∗ map] l ; v ∈ m' ; m, (l +ₗ -1) ↦ v.

Notation is_Map := pred.

(* --------------------- Functions on Maps ---------------------- *)

Definition emptymap : val :=
  λ: "<>",
    let: "new" := AllocN #1 NONEV in
    Tree.new "new";; "new".

Definition insert : val :=
  λ: "map" "k" "v",
    let: "new_node" := AllocN #4 NONEV in
    "new_node"      <- "v" ;;
    "new_node" +ₗ #3 <- "k" ;;
    let: "ml" := Tree.insert "map" ("new_node" +ₗ #1) in
    match: "ml" with
      NONE      => #()
    | SOME "l'" => array_free "l'" #3 
    end.

Definition lookup : val :=
  λ: "map" "k",
    let: "pos" := Tree.locate "map" "k" in
    !("pos" +ₗ #-1).

(* -------------- Verification of the Specifications -------------- *)

Lemma emptymap_spec :
  {{{ emp }}}
    emptymap #()
  {{{ l, RET #l; is_Map l ∅ }}}.
Proof.
  iSteps as (Φ l) "HΦ Hl"; iModIntro.
  wp_apply (Tree.new_spec with "[$Hl]"); iSteps.
  iExists ∅. iSplitL.
  { now iApply Tree.Intrusive_Map_empty. }
  now iApply big_sepM2_empty.
Qed.

Lemma insert_spec (l: loc) m (k: nat) (v: val) :
  {{{ is_Map l m }}}
    insert #l #k v
  {{{ RET #(); is_Map l (<[k := v]> m) }}}.
Proof.
  iSteps as (Φ m' p) "Hl Hmap HΦ H0 H12 H3".
  rewrite unfold_array; simpl.
  iDestruct "H12" as "[H1 H2]".
  wp_apply (Tree.insert_spec_Intrusive_Map with "[$Hl H1 H2 H3]"); first iSteps.
  destruct (m' !! k) as [l'|].
  - iSteps as (v1 v2) "Hl Hl'"; iModIntro.
    wp_apply (wp_array_free with "[$Hl'] [-]"); first (simpl; lia); iSteps.
    iApply (big_sepM2_insert_2 with "[H0] [Hmap]"); iSteps.
  - iSteps; iModIntro.
    iApply (big_sepM2_insert_2 with "[H0] [Hmap]"); iSteps.
Qed.


End Map.
End Map.

From Intrusive Require Import Setup Util cycle_single.


Module DCycle.
Section Dcycle.
  Context `{!heapGS Σ}.

  Notation "(.+ₗ n )" := (λ l, l +ₗ n) (only parsing).
  Notation "( l +ₗ.)" := (Loc.add l) (only parsing).
  Notation "(+ₗ)" := Loc.add (only parsing).
  Definition rev_add_1 (L: list loc) : list loc :=
    (.+ₗ 1) <$> (rev L). (* use [reverse] instead of [rev] *)
  Definition rev_sub1 (L: list loc) : list loc :=
    (.+ₗ -1) <$> (rev L).

  Fact rev_add1_cons l L :
    rev_add_1 (l :: L) = rev_add_1 L ++ [l +ₗ 1].
  Proof. rewrite /rev_add_1 /= fmap_app //. Qed.

  Fact rev_add1_snoc l L :
    rev_add_1 (L ++ [l]) = (l +ₗ 1) :: rev_add_1 L.
  Proof. rewrite /rev_add_1 /= rev_unit fmap_cons //. Qed.

  Fact sub1_rev_add1 L :
    (.+ₗ -1) <$> (rev_add_1 L) = rev L.
  Proof.
    rewrite /rev_add_1 -list_fmap_compose.
    rewrite (list_fmap_ext (_ ∘ _) id).
    { by rewrite list_fmap_id. }
    intros i l H; simpl. rewrite Loc.add_assoc.
    enough ((1 + -1)%Z = 0%Z) as -> by (now rewrite Loc.add_0); lia.
  Qed.

  Lemma list_nil_or_snoc {A} (L: list A) :
    L = [] ∨ ∃ L' x, L = L' ++ [x].
  Proof.
    induction L as [|x L]; simpl; first by left.
    destruct IHL as [->|(L'&y&->)].
    - right. by exists [], x.
    - right. by exists (x :: L'), y.
  Qed.

(* ------ Representation predicate for doubly cyclic lists -------- *)

  Definition pred c (L: list loc) : iProp Σ :=
    Cycle.pred c L ∗ Cycle.pred (c +ₗ 1) (rev_add_1 L).
  Notation is_dcycle := pred.

  Fact pred_unfold c L :
    is_dcycle c L ⊣⊢ Cycle.pred c L ∗ Cycle.pred (c +ₗ 1) (rev_add_1 L).
  Proof. done. Qed.

  Lemma pred_rotate {c} c' L :
    is_dcycle c (c' :: L) ⊣⊢ is_dcycle c' (L ++ [c]).
  Proof.
    rewrite /pred /rev_add_1 /= rev_unit !fmap_app.
    simpl. by rewrite !Cycle.pred_rotate.
  Qed.

(* --------------------- Functions on dcycles --------------------- *)

Definition new : val :=
  λ: "l",
    Cycle.new ("l" +ₗ #0) ;;
    Cycle.new ("l" +ₗ #1).

Definition is_empty : val :=
  λ: "pos", Cycle.is_empty ("pos" +ₗ #0).

Definition next : val :=
  λ: "pos", Cycle.next ("pos" +ₗ #0).

Definition prev : val :=
  λ: "pos", (Cycle.next ("pos" +ₗ #1)) +ₗ #(-1).

Definition insert_0 : val :=
  λ: "pos" "new",
    let: "next" := next "pos" in
    Cycle.insert ("next" +ₗ #1) ("new" +ₗ #1) ;;
    Cycle.insert ("pos" +ₗ #0) ("new" +ₗ #0).

Definition insert_1 : val :=
  λ: "pos" "new",
    let: "prev" := prev "pos" in
    Cycle.insert ("prev" +ₗ #0) ("new" +ₗ #0) ;;
    Cycle.insert ("pos"  +ₗ #1) ("new" +ₗ #1).

Definition remove_0 : val :=
  λ: "pos",
    let: "2next" := next (next "pos") in
    let: "l0" := Cycle.remove ("pos" +ₗ #0) in
    Cycle.remove ("2next" +ₗ #1) ;;
    "l0".

Definition remove_1 : val :=
  λ: "pos",
    let: "2prev" := prev (prev "pos") in
    Cycle.remove ("pos"   +ₗ #1);;
    Cycle.remove ("2prev" +ₗ #0).

(* ----------- Specs for dcyclic linked list operations ----------- *)

  Lemma new_spec c v0 v1 :
  {{{ c ↦∗ [v0 ; v1] }}}
    new #c
  {{{ RET #(); is_dcycle c [] }}}.
  Proof. iSteps. Qed.

  Global Instance new_spec_diaframe c v0 v1 :
  SPEC  {{ c ↦∗ [v0 ; v1] }}
          new #c
        {{ RET #(); is_dcycle c [] }}.
  Proof. iStep; iApply (new_spec with "[-]"); iSteps. Qed.


  Lemma is_empty_spec c L :
  {{{ is_dcycle c L }}}
    is_empty #c
  {{{ RET #(bool_decide (L = [])); is_dcycle c L }}}.
  Proof. iSteps. Qed.

  Global Instance is_empty_spec_diaframe c L :
  SPEC  {{ is_dcycle c L }}
          is_empty #c
        {{ RET #(bool_decide (L = [])); is_dcycle c L }}.
  Proof. iStep; iApply (is_empty_spec with "[-]"); iSteps. Qed.


  Lemma next_spec c (L: list loc) :
  {{{ is_dcycle c L }}}
    next #c
  {{{ RET #((L ++ [c]) !!! 0%nat : loc); is_dcycle c L }}}.
  Proof. iSteps; rewrite Loc.add_0; iSteps. Qed.

  Global Instance next_spec_diaframe c L :
  SPEC  {{ is_dcycle c L }}
          next #c
        {{ RET #((L ++ [c]) !!! 0%nat : loc); is_dcycle c L }}.
  Proof. iStep; iApply (next_spec with "[-]"); iSteps. Qed.


(*  The specs of [next] and [prev] are kind of symmetric.
    Imagine for example applying the next_spec to [rev L]. *)

  Lemma prev_spec c (L: list loc) :
  {{{ is_dcycle c L }}}
    prev #c
  {{{ RET #((rev L ++ [c]) !!! 0%nat : loc); is_dcycle c L }}}.
  Proof.
    iSteps as (Φ) "Hc1 Hc2 HΦ".
    enough ((rev_add_1 L ++ [c +ₗ 1]) !!! 0%nat +ₗ -1 =
            ((rev L ++ [c]) !!! 0%nat)) as -> by iSteps.
    rewrite /rev_add_1 -(list_fmap_singleton (.+ₗ 1)).
    rewrite -fmap_app list_lookup_total_fmap.
    - rewrite Loc.add_assoc. replace (1 + -1)%Z with 0%Z by lia.
      by rewrite Loc.add_0.
    - rewrite app_length /=; lia.
  Qed.

  Global Instance prev_spec_diaframe c L :
  SPEC  {{ is_dcycle c L }}
          prev #c
        {{ RET #((rev L ++ [c]) !!! 0%nat : loc); is_dcycle c L }}.
  Proof. iStep; iApply (prev_spec with "[-]"); iSteps. Qed.


  Lemma insert_0_spec c l L v0 v1 :
  {{{ l ↦∗ [v0 ; v1] ∗ is_dcycle c L }}}
    insert_0 #c #l
  {{{ RET #(); is_dcycle c (l :: L) }}}.
  Proof.
    iStep 22 as (Φ) "HΦ Hc0 Hc1 Hl".
    destruct L as [|p L]; simpl.
    - iSteps; rewrite !Loc.add_0; iSteps.
    - rewrite rev_add1_cons -(Cycle.pred_rotate (_ +ₗ _)).
      iSteps. rewrite !Loc.add_0; iSteps.
      rewrite !Cycle.pred_rotate !rev_add1_cons; iSteps.
  Qed.

  Global Instance insert_0_spec_diaframe c l L v0 v1 :
  SPEC  {{ l ↦∗ [v0 ; v1] ∗ is_dcycle c L }}
          insert_0 #c #l
        {{ RET #(); is_dcycle c (l :: L) }}.
  Proof. iStep; iApply (insert_0_spec with "[-]"); iSteps. Qed.


  Lemma insert_1_spec c l L v0 v1 :
  {{{ l ↦∗ [v0 ; v1] ∗ is_dcycle c L }}}
    insert_1 #c #l
  {{{ RET #(); is_dcycle c (L ++ [l]) }}}.
  Proof.
    iStep 22 as (Φ) "Hl HΦ Hc0 Hc1"; rewrite !Loc.add_0. 
    destruct (list_nil_or_snoc L) as [->|(L'&p&->)]; simpl.
    - iSteps.
    - rewrite rev_unit -Cycle.pred_rotate; simpl. iStep 18.
      rewrite -!rev_add1_snoc Cycle.pred_rotate
              -app_comm_cons Cycle.pred_rotate; iSteps.
  Qed.

  Global Instance insert_1_spec_diaframe c l L v0 v1 :
  SPEC  {{ l ↦∗ [v0 ; v1] ∗ is_dcycle c L }}
          insert_1 #c #l
        {{ RET #(); is_dcycle c (L ++ [l]) }}.
  Proof. iStep; iApply (insert_1_spec with "[-]"); iSteps. Qed.


  Lemma remove_0_spec c l L :
  {{{ is_dcycle c (l :: L) }}}
    remove_0 #c
  {{{ v0 v1, RET #l; is_dcycle c L ∗ l ↦∗ [v0; v1] }}}.
  Proof.
    iStep 8 as (Φ) "HΦ Hc0 Hc1". iModIntro.
    wp_apply (next_spec with "[Hc0 Hc1]").
    { instantiate (1:= L ++ [c]). rewrite -pred_rotate; iFrame. }
    iStep 8 as "Hc0 Hc1".
    iAssert (is_dcycle c (l :: L))%I with "[Hc0 Hc1]" as "Hc".
    { rewrite pred_rotate; iFrame. }
    destruct L as [|p L]; simpl; first iSteps.
    iStep 12 as (v) "Hc1 Hc0 Hl".
    rewrite !fmap_app; simpl.
    rewrite -Cycle.pred_rotate app_comm_cons -Cycle.pred_rotate.
    iSteps as (v1) "Hc1 Hl1".
    rewrite Cycle.pred_rotate -rev_add1_cons; iSteps.
  Qed.

  Global Instance remove_0_spec_diaframe c l L :
  SPEC  {{ is_dcycle c (l :: L) }}
          remove_0 #c
        {{ v0 v1, RET #l; is_dcycle c L ∗ l ↦∗ [v0; v1] }}.
  Proof. iStep; iApply (remove_0_spec with "[-]"); iSteps. Qed.

  Lemma remove_1_spec c l L :
  {{{ is_dcycle c (L ++ [l]) }}}
    remove_1 #c
  {{{ v0 v1, RET #l; is_dcycle c L ∗ l ↦∗ [v0; v1] }}}.
  Proof.
    iStep 8 as (Φ) "HΦ Hc0 Hc1". iModIntro.
    wp_apply (prev_spec with "[Hc0 Hc1]").
    { rewrite rev_unit. simpl. instantiate (1:= c :: L ).
      rewrite pred_rotate. iFrame. }
    iStep 8 as "Hc0 Hc1". rewrite rev_unit; simpl.
    iAssert (is_dcycle c (L ++ [l]))%I with "[Hc0 Hc1]" as "Hc".
    { rewrite -pred_rotate; iFrame. }
    destruct (list_nil_or_snoc L) as [->|(L'&p&->)]; first iSteps.
    rewrite rev_unit; simpl.
    iDestruct "Hc" as "[Hc1 Hl]".
    rewrite rev_add1_snoc. iStep 12 as (v) "Hc1 Hl1".
    rewrite -Cycle.pred_rotate app_comm_cons -Cycle.pred_rotate.
    rewrite Loc.add_0. iStep 7.
    rewrite Cycle.pred_rotate; iSteps.
  Qed.

  Global Instance remove_1_spec_diaframe c l L :
  SPEC  {{ is_dcycle c (L ++ [l]) }}
          remove_1 #c
        {{ v0 v1, RET #l; is_dcycle c L ∗ l ↦∗ [v0; v1] }}.
  Proof. iStep; iApply (remove_1_spec with "[-]"); iSteps. Qed.

End Dcycle.
End DCycle.

Global Opaque DCycle.pred 
              DCycle.new DCycle.is_empty DCycle.next DCycle.prev 
              DCycle.insert_0 DCycle.insert_1 
              DCycle.remove_0 DCycle.remove_1.

From Intrusive Require Import Setup seq.


Module Cycle.
Section cycle.
  Context `{!heapGS Σ}.

(* ---------- Representation predicate for cyclic lists ----------- *)
  
  Definition pred c (L: list loc) : iProp Σ :=
    Seq.pred c L c.
  Notation is_cycle := pred.

  Fact pred_nil c :
    is_cycle c [] ⊣⊢ c ↦ #c.
  Proof. done. Qed.

  Fact pred_rotate c c' L :
    is_cycle c (c' :: L) ⊣⊢ is_cycle c' (L ++ [c]).
  Proof.
    unfold is_cycle. rewrite Seq.split /=. by apply :comm.
  Qed.

(* ---------------------- Functions on cycles --------------------- *)

  Definition new : val      :=  λ: "l", Seq.new "l" "l".

  Definition is_empty : val := λ: "l", !"l" = "l".

  Definition next : val   :=  Seq.next.

  Definition insert : val := Seq.push.

  Definition remove : val := Seq.pop.

(* ----------- Specs for cyclic linked list operations ------------ *)

  Lemma new_spec c v :
    {{{ c ↦ v }}}
      new #c
    {{{ RET #(); is_cycle c [] }}}.
  Proof.
    iSteps as (Φ) "Hc HΦ"; iModIntro.
    wp_apply (Seq.new_spec with "Hc"); done.
  Qed.

  Global Instance new_spec_diaframe c v :
  SPEC  {{ c ↦ v }}
          new #c
        {{ RET #(); is_cycle c [] }}.
  Proof. iStep as "H". iApply (new_spec with "H"); iSteps. Qed.

  Lemma is_empty_spec c L :
    {{{ is_cycle c L }}}
      is_empty #c
    {{{ RET #(bool_decide (L = [])); is_cycle c L }}}.
  Proof.
    unfold pred.
    destruct L as [| x L]; simpl.
    { iStep 5.
      rewrite Seq.pred_nil; iSteps.
      case_bool_decide; iSteps || simplify_eq. }
    iStep 5 as (Φ) "Hc HΦ".
    rewrite Seq.pred_cons. iModIntro.
    iDestruct "Hc" as "[Hc Hx]".
    wp_load. wp_pures. 
    case_bool_decide; [simplify_eq|iSteps].
    iModIntro. destruct L; simpl. 
    - rewrite Seq.pred_nil. iDecompose "Hc".
    - rewrite Seq.pred_cons. iDecompose "Hx".
  Qed.

  Global Instance is_empty_spec_diaframe c L :
  SPEC  {{ is_cycle c L }}
          is_empty #c
        {{ RET #(bool_decide (L = [])); is_cycle c L }}.
  Proof. iStep as "H". iApply (is_empty_spec with "H"); iSteps. Qed.

  Lemma next_spec c (L: list loc) :
    {{{ is_cycle c L }}}
      next #c
    {{{ RET #((L ++ [c]) !!! 0%nat : loc); is_cycle c L }}}.
  Proof.
    unshelve eapply Seq.next_spec; eauto.
  Qed.

  Global Instance next_spec_diaframe c (L : list loc) :
    SPEC {{ pred c L }} 
        next #c 
    {{ RET #((L ++ [c]) !!! 0%nat : loc); pred c L }}.
  Proof. iStep as "H". iApply (next_spec with "H"); iSteps. Qed.

  Lemma insert_spec {c l v} L :
    {{{ l ↦ v ∗ is_cycle c L }}}
      insert #c #l
    {{{ RET #(); is_cycle c (l :: L) }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_apply (Seq.push_spec with "Hc"); done.
  Qed.

  Global Instance insert_spec_diaframe c l v L :
  SPEC  {{ l ↦ v ∗ is_cycle c L }}
        insert #c #l
      {{ RET #(); is_cycle c (l :: L) }}.
  Proof. iStep as "H Hc". iApply (insert_spec with "[H Hc]"); iSteps. Qed.

  Lemma remove_spec c l L :
    {{{ is_cycle c (l :: L) }}}
      remove #c
    {{{ v, RET #l; is_cycle c L ∗ l ↦ v }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_apply (Seq.pop_spec with "Hc"); iSteps.
  Qed.

  Global Instance remove_spec_diaframe c l L :
  SPEC  {{ is_cycle c (l :: L) }}
        remove #c
      {{ v, RET #l; is_cycle c L ∗ l ↦ v }}.
  Proof. iStep as "H". iApply (remove_spec with "H"); iSteps. Qed.

  Global Instance cycle_pred_hint 
  (c1 l1o c2 l2o : loc) (o1 o2 : Z) L :
    FindBaseLoc c1 l1o o1 →
    FindBaseLoc c2 l2o o2 →
    TCEq l1o l2o →
    SolveSepSideCondition (o1 = o2) →
    HINT (pred c1 L) ✱ [- ; emp] ⊫ [id]; (pred c2 L) ✱ [emp] | 64.
  Proof.
    rewrite /FindBaseLoc TCEq_eq /SolveSepSideCondition => -> -> -> ->.
    iSteps.
  Qed.

End cycle.
End Cycle.

Global Opaque Cycle.pred 
              Cycle.new Cycle.is_empty Cycle.next 
              Cycle.insert Cycle.remove.

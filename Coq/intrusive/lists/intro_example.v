From Intrusive Require Import Setup.

Section List.
Context `{!heapGS Σ}.

(* -------------- Representation predicate for lists -------------- *)

Fixpoint is_list (v: val) (ds: list val) : iProp Σ :=
  match ds with
  | []      =>  ⌜ v = NONEV ⌝
  | d :: ds =>  ∃ (l: loc), ⌜ v = SOMEV #l ⌝ ∗
                ∃ (v': val), l ↦∗ [d; v'] ∗ is_list v' ds
  end.

Fixpoint nodes (vs: val) (ls: list loc) : iProp Σ :=
  match ls with
  | []      =>  ⌜ vs = NONEV ⌝
  | l :: ls =>  ⌜ vs = SOMEV #l ⌝ ∗
                ∃ (v': val), l ↦ v' ∗ nodes v' ls
  end.

Definition is_data_list v ds : iProp Σ := 
  ∃ (ls: list loc),
    nodes v ls ∗ [∗ list] i ↦ l ; d ∈ ls ; ds, (l +ₗ -1) ↦ d.

(* --------------------- Functions on lists  ---------------------- *)

(* Function which takes a list and moves to the n-th node *)
Definition get_pos : val :=
  rec: "get_pos" "n" "v"  :=
    if: "n" = #0 then "v"
    else  let: "n-1" := "n" - #1 in
          match: "v" with
            NONE     => NONEV
          | SOME "l" => let: "!l" := !"l" in
                        "get_pos" "n-1" "!l"
          end.

Definition replace_at : val :=
  λ: "n" "v" "a",
    match: get_pos "n" "v" with
      NONE     => #()
    | SOME "l" => ("l" +ₗ #-1) <- "a"
    end.

(* ---------------------   Verifying Specs  ----------------------- *)
Implicit Types n : nat.
Implicit Types v d : val.
Implicit Types l : loc.

Lemma get_pos_spec n v ls:
  {{{ nodes v ls }}}
    get_pos #n v
  {{{ RET (from_option (λ l, SOMEV #l) NONEV (ls !! n)) ;
      nodes v ls }}}.
Proof.
  iSteps as (Φ) "Hnodes HΦ".
  iInduction ls as [|l' ls] "IH" forall (n v); simplify_eq/=.
  { iDestruct "Hnodes" as "->". destruct n; unfold get_pos; iSteps. }
  iDestruct "Hnodes" as "[-> H2]".
  iDestruct "H2" as (v') "[Hl Hnodes]".
  destruct n as [|n]; simplify_eq/=.
  { iClear "IH". unfold get_pos. iSteps. }
  unfold get_pos.
  wp_pures; fold get_pos. wp_load. wp_pures.
  assert ((S n - 1) = n)%Z as -> by lia.
  iApply ("IH" with "[$Hnodes]"). iSteps.
Qed.

Lemma parallel_lookup n D L :
  length L = length D ->
  (exists l d, L !! n = Some l ∧ D !! n = Some d) \/
               L !! n = None   ∧ D !! n = None.
Proof.
  destruct (L !! n) as [l|] eqn:HL,
           (D !! n) as [d|] eqn:HD; intros Hlen; auto.
  { left. now exists l, d. }
  all: exfalso.
  - apply lookup_ge_None_1 in HD.
    apply lookup_lt_Some in HL; lia.
  - apply lookup_ge_None_1 in HL.
    apply lookup_lt_Some in HD; lia.
Qed.

Lemma replace_at_spec n v ds d :
  {{{ is_data_list v ds }}}
    replace_at #n v d
  {{{ RET #(); is_data_list v (<[n := d]> ds) }}}.
Proof.
  iStep 2 as (Φ l') "H Hld". unfold is_data_list.
  iRevert "H". iSteps as "Hl HΦ"; iModIntro.
  iDestruct (big_sepL2_length with "Hld") as %Hlen.
  wp_apply (get_pos_spec with "[$Hl]") as "Hnodes".
  apply (parallel_lookup n) in Hlen as [(l&d'&Hl&Hd)|[Hl Hd]]; rewrite Hl.
  - iDestruct (big_sepL2_insert_acc with "Hld") as "[Hl1 Hld]"; [done..|].
    iSteps as "Hl1". iModIntro.
    iSpecialize ("Hld" with "[$]").
    rewrite list_insert_id; done.
  - iSteps. rewrite list_insert_id'; first done.
    apply lookup_ge_None_1 in Hd. lia.
Qed.

End List.

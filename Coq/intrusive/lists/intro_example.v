From Intrusive Require Import Setup.

Section List.
Context `{!heapGS Σ}.

(* -------------- Representation predicate for lists -------------- *)

Fixpoint is_list (v: val) (ds: list val) : iProp Σ :=
  match ds with
  | []      =>  ⌜ v = NONEV ⌝
  | d :: ds =>  ∃ (l: loc), ⌜ v = SOMEV #l ⌝ ∗
                ∃ (v': val), l ↦∗ [v'; d] ∗ is_list v' ds
  end.

Fixpoint nodes (vs: val) (ls: list loc) : iProp Σ :=
  match ls with
  | []      =>  ⌜ vs = NONEV ⌝
  | l :: ls =>  ⌜ vs = SOMEV #l ⌝ ∗
                ∃ (v': val), l ↦ v' ∗ nodes v' ls
  end.

Lemma is_list_equiv v ds :
  is_list v ds ⊣⊢ ∃ (ls: list loc),
    nodes v ls ∗ [∗ list] i ↦ l ; d ∈ ls ; ds, (l +ₗ 1) ↦ d.
Proof.
  induction ds as [|d ds IH] in v |-*; simpl.
  { iSteps as (ls) "H1 H2". 2: iExists []; iSteps.
    rewrite big_sepL2_nil_inv_r. iDestruct "H2" as "->"; iSteps. }
  iSplit.
  + iSteps as (l v) "Hl Hv". rewrite IH. 
    iDestruct "Hv" as (ls) "[Hv Hls]".
    iExists (l :: ls); iSteps.
  + iStep 2 as (ls) "Hv Hls".
    destruct ls as [|l ls]; simpl in *; auto.
    iExists l. iDestruct "Hv" as "[-> Hv]".
    iDestruct "Hv" as (v') "[Hl Hv']". iSteps.
    rewrite IH. iSteps.
Qed.

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
  λ: "v" "n" "a",
    match: get_pos "n" "v" with
      NONE     => #()
    | SOME "l" => ("l" +ₗ #1) <- "a"
    end.

(* ---------------------   Verifying Specs  ----------------------- *)
Implicit Types n : nat.
Implicit Types v d : val.
Implicit Types l : loc.

Lemma get_pos_spec' n v ls:
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

Lemma replace_at_spec' n v ds d :
  {{{ is_list v ds }}}
    replace_at v #n d
  {{{ RET #(); is_list v (<[n := d]> ds) }}}.
Proof.
  iStep 2 as (Φ) "H". rewrite !is_list_equiv.
  iRevert "H". iSteps as "Hl Hld HΦ"; iModIntro.
  iDestruct (big_sepL2_length with "Hld") as %Hlen.
  wp_apply (get_pos_spec' with "[$Hl]") as "Hnodes".
  apply (parallel_lookup n) in Hlen as [(l&d'&Hl&Hd)|[Hl Hd]]; rewrite Hl.
  - iDestruct (big_sepL2_insert_acc with "Hld") as "[Hl1 Hld]"; [done..|].
    iSteps as "Hl1". iModIntro.
    iSpecialize ("Hld" with "[$]").
    rewrite list_insert_id; done.
  - iSteps. rewrite list_insert_id'; first done.
    apply lookup_ge_None_1 in Hd. lia.
Qed.

End List.

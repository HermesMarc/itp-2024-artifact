From Intrusive Require Import Setup Util.

Module Tree.
Section Tree.
  Context `{!heapGS Σ}.

Notation tree_insert k a t :=
  (tree.rec_insert (λ '(x, _) '(y, _), bool_decide (x < y) ) (k, a) t).

Notation tree_insert' k a t :=
  (tree.insert (λ '(x, _) '(y, _), bool_decide (x < y) ) (k, a) t).
  
Notation tree_locate k l Γ t :=
  (tree.locate (λ '(x, _) '(y, _), bool_decide (x < y)) (k, l) Γ t).

Lemma map_fst_insert {A} k (a: A) t :
  tree.map fst (tree_insert k a t) =
  tree.rec_insert (λ x y, bool_decide (x < y)) k (tree.map fst t).
Proof.
  apply tree.map_f_insert; now intros [][].
Qed.

Lemma tree_locate_ignore {k l Γ t} (p: loc) :
  tree_locate k l Γ t = tree_locate k p Γ t.
Proof.
  induction t as [| [k' l'] t0 H0 t1 H1] in l, p, Γ, t |-*; auto; simpl.
  destruct (bool_decide (k < k')) eqn:Hkk1; first apply H0.
  destruct (bool_decide (k' < k)) eqn:Hkk2; first apply H1.
  reflexivity.
Qed.

(* ------- Representation predicate for binary serch trees -------- *)

Fixpoint pred' (vt: val)(t: tree.t loc) : iProp Σ :=
  match t with
  | tree.Leaf         => ⌜ vt = NONEV ⌝
  | tree.Node l t1 t2 =>
    ⌜ vt = SOMEV #l ⌝
    ∗ ∃ (v1 v2: val), l ↦∗ [ v1; v2]
    ∗ pred' v1 t1 ∗ pred' v2 t2
  end.
Notation intrusive_tree' := pred'.

Definition pred (l: loc)(t: tree.t loc) : iProp Σ :=
  ∃ (vt: val), l ↦ vt ∗ pred' vt t.
Notation intrusive_tree := pred.


Fixpoint alt_pred (l: loc)(t: tree.t loc) : iProp Σ :=
  match t with
  | tree.Leaf         => l ↦ NONEV
  | tree.Node p t1 t2 =>
    l ↦ SOMEV #p ∗ alt_pred p t1 ∗ alt_pred (p +ₗ 1) t2
  end.

Lemma definitions_equivalent (l: loc)(t: tree.t loc) :
  pred l t ⊣⊢ alt_pred l t.
Proof.
  induction t as [|p t1 IH1 t2 IH2] in l |-*; simpl; first iSteps.
  rewrite <-IH1, <-IH2. iSteps.
Qed.




Definition BST_nat := tree.BST nat (fun x y => bool_decide(x < y)).

Definition BST (l: loc)(t: tree.t (nat * loc)) : iProp Σ :=
  intrusive_tree l (tree.map snd t)
∗ ⌜ BST_nat (tree.map fst t)⌝
∗ [∗ list] kl ∈ tree.inorder t, (kl.2 +ₗ 2) ↦ #(kl.1: nat).

(* Map that assigns a location to every key *)
Definition to_map t : gmap nat loc := list_to_map (tree.inorder t).

Definition is_Intrusive_Map (l: loc)(m: gmap nat loc) : iProp Σ :=
  ∃ t, BST l t ∗ ⌜ m = to_map t ⌝.

(* Map that assigns a value to every key *)
Definition is_Map (l: loc)(m: gmap nat val) : iProp Σ :=
  ∃ m', is_Intrusive_Map l m'
∗ [∗ map] l ; v ∈ m' ; m, (l +ₗ 3) ↦ v.

Definition is_Set l (s: gset nat) : iProp Σ :=
  ∃ m, is_Intrusive_Map l m ∗ ⌜ dom m = s ⌝.


Fact BST_Leaf_unfold (l: loc) :
  BST l tree.Leaf ⊣⊢ l ↦ NONEV .
Proof. iSteps. iPureIntro; constructor. Qed.

Lemma BST_Node_unfold (l p: loc) (k: nat) t0 t1 :
  BST l (tree.Node (k, p) t0 t1) ⊣⊢
  ⌜ BST_nat (tree.map fst (tree.Node (k, p) t0 t1) ) ⌝
  ∗ l ↦ SOMEV #p ∗ BST (p +ₗ 0) t0 ∗ BST (p +ₗ 1) t1 ∗ (p +ₗ 2) ↦ #k.
Proof.
  iSplit.
  - iIntros "[Htree [% Hk]]"; simpl.
    rewrite big_sepL_app.
    iDestruct "Hk" as "[Hl'2 [Hk1 Hk2]]".
    iDestruct "Htree" as (vt) "[Hl [H1 H2]]"; fold pred'.
    inversion H; subst. iFrame. iSteps; done.
  - iIntros "(%H & Hl & [Ht0 [% Hk0]] & [Ht1 [% Hk1]] & Hk')".
    iSplitL "Hl Ht0 Ht1"; iFrame.
    2: { simpl; iPureIntro; done. } 
    iDestruct "Ht0" as (v0) "Ht0".
    iDestruct "Ht1" as (v1) "Ht1".
    iExists (SOMEV #p). iSteps.
Qed.

Fact BST_singleton (p new: loc) (k: nat) : 
  p ↦ (SOMEV #new) ∗ new ↦∗ [ NONEV; NONEV; #k] ⊣⊢
  BST p (tree.Node (k, new) tree.Leaf tree.Leaf).
Proof.
  rewrite unfold_array; simpl.
  rewrite BST_Node_unfold !BST_Leaf_unfold; iFrame.
  iSplit; iSteps.
  iPureIntro; apply tree.BST_singleton.
Qed.

Fact ctx_BST Γ (t: tree.t (nat * loc)) :
  tree.ctx Γ ->
  BST_nat (tree.map fst (Γ t)) -> BST_nat (tree.map fst t).
Proof.
  intros Hctx. induction Hctx in t |-*; simpl; auto.
  all: intros H%IHHctx; now inversion H.
Qed.

(* ----------------------- Partial BST ---------------------------- *)

Definition part_BST (l: loc) Γ (p : loc) : iProp Σ :=
  ∀ t', BST p t' ∗ ⌜ BST_nat (tree.map fst (Γ t')) ⌝ -∗ BST l (Γ t').

Lemma part_BST_id l :
  emp -∗ (part_BST l id l).
Proof.
  iIntros "_". iIntros (t) "[H1 %H2]"; iFrame.
Qed.

Lemma part_BST_compose l p p' Γ Γ' :
  tree.ctx Γ ->
  part_BST l Γ p -∗ part_BST p Γ' p' -∗ part_BST l (Γ ∘ Γ') p'.
Proof.
  iIntros (HΓ) "H1 H2". iIntros (t) "[H3 %H4]".
  iApply "H1"; iSplitL; last done.
  iApply "H2". iFrame. iPureIntro.
  eapply ctx_BST; eauto.
Qed.

Lemma part_BST_init_left_hole (l l' : loc) (k': nat) t1 :
  BST (l' +ₗ 1) t1 ∗ l ↦ InjRV #l' ∗ (l' +ₗ 2) ↦ #k' -∗
  part_BST l (λ h, (tree.Node (k', l') h t1)) (l' +ₗ 0).
Proof.
  iIntros "(? & ? & ?)" (t0) "[? ?]".
  iApply BST_Node_unfold; iFrame.
Qed.

Lemma part_BST_init_right_hole (l l' : loc) (k': nat) t0 :
  BST (l' +ₗ 0) t0 ∗ l ↦ InjRV #l' ∗ (l' +ₗ 2) ↦ #k' -∗
  part_BST l (λ h, (tree.Node (k', l') t0 h)) (l' +ₗ 1).
Proof.
  iIntros "(? & ? & ?)" (t1) "[? ?]".
  iApply BST_Node_unfold; iFrame.
Qed.

Typeclasses Opaque part_BST.

(* --------------------- Functions on a BST ----------------------- *)

Definition new : val :=
  λ: "l", "l" <- NONEV.

Definition locate : val :=
  rec: "locate" "position" "key" :=
    match: ! "position" with
      NONE => "position"
    | SOME "node" =>
        let: "node_key" := !("node" +ₗ #2) in
        if: "key" < "node_key" then
          "locate" ("node" +ₗ #0) "key"
        else if: "node_key" < "key" then
          "locate" ("node" +ₗ #1) "key"
        else "position"
    end.

Definition insert : val :=
  λ: "root" "new",
  let: "new_key" := !("new" +ₗ #2) in
  let: "pos" := locate "root" "new_key" in
  match: ! "pos" with
    NONE => "pos" <- SOME "new";; NONEV
  | SOME "node" =>
    "new" +ₗ #0 <- !("node" +ₗ #0);;
    "new" +ₗ #1 <- !("node" +ₗ #1);;
    "pos" <- SOME "new";;
    SOME "node"
  end.

(* -------------- Verification of the Specifications -------------- *)

Lemma new_spec l v :
  {{{ l ↦ v }}}
    new #l
  {{{ RET #(); BST l tree.Leaf }}}.
Proof. 
  iSteps. iPureIntro; constructor.
Qed.

Lemma locate_spec_general (l p s: loc) (k: nat) Γ t Γ' t' :
  tree.ctx Γ -> tree_locate k s Γ t = (Γ', t') ->
{{{ part_BST l Γ p ∗ BST p t }}}
  locate #p #k
{{{ p', RET #p'; part_BST l Γ' p' ∗ BST p' t' }}}.
Proof.
  iIntros (HΓ Hlocate Φ) "[Hpart Hbst] HΦ".
  iRevert (Hlocate HΓ).
  iInduction t as [|kl tl IHl tr IHr] "IH" forall (Γ l p s);
    iIntros (Hlocate HΓ); simpl in Hlocate.
  { rewrite /locate. simpl in Hlocate. inversion Hlocate; subst. iSteps. }
  destruct kl as [k' l'].
  iDestruct (BST_Node_unfold with "Hbst") 
         as "(%Hbst & Hp & Htl & Htr & Hk)".
  wp_lam; wp_pures. repeat wp_load; wp_pures.
  case_bool_decide; iStep 8.
  { iApply ("IH" with "[-Htl HΦ] [$Htl] [$HΦ] [//] []").
    2: { iPureIntro. constructor; eauto with tree_ctx. }
    iApply (part_BST_compose with "Hpart"); auto.
    iApply part_BST_init_left_hole; iFrame. }
  case_bool_decide; iStep 8.
  { iApply ("IH1" with "[-Htr HΦ] [$Htr] [$HΦ] [//] []" ).
    2: { iPureIntro. constructor; eauto with tree_ctx. }
    iApply (part_BST_compose with "Hpart"); auto.
    change (tree.Node (k', l') tl) with (λ h, tree.Node (k', l') tl h).
    iApply part_BST_init_right_hole; iFrame. }
  inversion Hlocate; subst.
  rewrite BST_Node_unfold; iSteps.
Qed.

Lemma locate_spec (l s: loc) (k: nat) t Γ' t' :
  tree_locate k s id t = (Γ', t') ->
{{{ BST l t }}}
  locate #l #k
{{{ l', RET #l'; part_BST l Γ' l' ∗ BST l' t' }}}.
Proof.
  iIntros (Hlocate Φ) "Hbst HΦ".
  iApply (locate_spec_general with "[Hbst] [-]"); eauto.
  { constructor. }
  iFrame. unfold part_BST; iSteps.
Qed.

Definition option_loc_to_val (v: option loc) : val :=
  match v with
  | None   => NONEV
  | Some l => SOMEV #l
  end.

  
(*  This spec shows that if insert encounters a node that already has [k]
    stored in it, it will replace that node with the new one. *)
Lemma insert_spec (l new: loc) (k: nat) t :
  {{{ new ↦∗ [ NONEV; NONEV; #k] ∗ BST l t }}}
    insert #l #new
  {{{ ml, RET (option_loc_to_val ml);
    BST l (tree_insert' k new t) ∗
    if ml is Some l' then ∃ w0 w1, l' ↦∗ [ w0; w1; #k]
    else True
  }}}.
Proof.
  iIntros (Φ) "[Hnew Ht] HΦ".
  rewrite unfold_array; simpl.
  iDestruct "Hnew" as "(Hnew0 & Hnew1 & ?)"; iSteps as "HΦ Hnew2"; iModIntro.
  destruct (tree_locate k new id t) as [Γ' t'] eqn:H'.
  specialize (tree.insert_via_locate _ _ _ _ _ H') as H.
  iAssert (⌜ BST_nat (tree.map fst t) ⌝)%I as "%Hbst".
  { iDestruct "Ht" as "[_ [%Hbst _]]"; done. }
  eapply tree.BST_insert with (k:= k) in Hbst.
  2, 3: shelve.
  wp_apply (locate_spec with "Ht"); eauto.
  iIntros (p) "[Hpart Hbst]".
  destruct t' as [| [k' l'] t0 t1].
  - iSteps; do 2 iModIntro.
    iSpecialize ("HΦ" $! None). iStep 1.
    unfold tree_insert'.
    rewrite H'. unfold part_BST.
    iSplitL; last iSteps.
    iApply "Hpart". iSplitL.
    + iApply BST_singleton. rewrite unfold_array; iSteps.
    + iPureIntro. rewrite <-H.
      simpl. rewrite map_fst_insert.
      now rewrite tree.rec_insert_eq_insert.
  - iSteps as (Hbst_k v0 v1) "H2 ? ? ? H0 ? H1 ? ?"; do 2 iModIntro.
    iSpecialize ("HΦ" $! (Some l')). iStep 1.
    unfold tree_insert'. rewrite H'.
    specialize (tree.locate_spec _ H') as [H'' [Hk1 Hk2]].
    apply bool_decide_eq_false in Hk1.
    apply bool_decide_eq_false in Hk2.
    assert (k' = k) as -> by lia.
    iSplitR "H0 H1 H2"; last iSteps.
    unfold part_BST; iApply "Hpart". iSplitL.
    + rewrite BST_Node_unfold /BST big_sepL_app; iFrame.
      inversion Hbst_k; iSteps.
    + iPureIntro.
      rewrite <-H. simpl. rewrite map_fst_insert.
      now rewrite tree.rec_insert_eq_insert.
  Unshelve.
  { intros x y H1 H2.
    apply bool_decide_eq_true in H1.
    apply bool_decide_eq_true in H2; lia. }
  { intros x y H1 H2.
    apply bool_decide_eq_false in H1.
    apply bool_decide_eq_false in H2; lia. }
Qed.

Lemma insert_spec_Map (l new: loc) (k: nat) (m: gmap nat loc) :
  {{{ new ↦∗ [ NONEV; NONEV; #k] ∗ is_Intrusive_Map l m }}}
    insert #l #new
  {{{ ml, RET (option_loc_to_val ml); 
    is_Intrusive_Map l ( <[k := new]> m ) ∗
    if ml is Some l' 
    then ∃ w0 w1, l' ↦∗ [ w0; w1; #k]
    else True
  }}}.
Proof.
  iIntros (Φ) "[Hnew Hmap] HΦ".
  iDestruct "Hmap" as (t) "[Hbst %Hmap]".
  iAssert (⌜ BST_nat (tree.map fst t) ⌝)%I as %Hbst.
  { iDestruct "Hbst" as "[_ [%H' _]]". done. }
  iApply (insert_spec with "[$Hnew $Hbst]").
  iSteps. iPureIntro. clear H.
  rewrite -tree.rec_insert_eq_insert.
  induction t as [| [k' v'] t1 IHt1 t2 IHt2]; first reflexivity; inversion Hbst; simplify_eq/=.
  unfold to_map in *. simpl.
  rewrite list_to_map_app.
  simpl; repeat case_bool_decide; simpl.
  - rewrite list_to_map_app.
    rewrite -IHt1 //.
    rewrite -insert_union_l insert_commute; try lia.
    reflexivity.
  - rewrite list_to_map_app -IHt2 //.
    rewrite -insert_union_r.
    + rewrite insert_commute; try lia. reflexivity.
    + apply not_elem_of_list_to_map_1.
      rewrite -tree.inorder_map. intros Hk%tree.In_inorder_set.
      naive_solver lia.
  - assert (k = k') as -> by lia.
    rewrite insert_insert list_to_map_app. reflexivity.
Qed.

End Tree.
End Tree.

Global Opaque Tree.pred' Tree.pred
              Tree.new Tree.insert Tree.locate.

From Intrusive Require Import Setup.

Section util.
  Context `{!heapGS Σ}.

  Lemma unfold_array l L :
    l ↦∗ L ⊣⊢[∗ list] i ↦ x ∈ L, (l +ₗ i) ↦ x.
  Proof. done. Qed.
End util.


(* ------------------ Tree and BST structures --------------------- *)
Module tree.
Section module.
Section locate.

Section tree.
  Inductive t K :=
  | Leaf : t K
  | Node : K → t K → t K → t K.
  
  Fixpoint inorder {K} (t: t K) : list K :=
    match t with
    | Leaf _ => []
    | Node _ x l r => [x] ++ inorder l ++ inorder r
    end.
End tree.
Arguments Leaf {_}.
Arguments Node {_} _ _ _.

  Context {K: Type}.
  Context {EqDecision_K : EqDecision K}
          {Countable_K : Countable K}.

  Fixpoint to_set (t: t K) : gset K :=
    match t with
    | Leaf       => ∅
    | Node x l r => {[x]} ∪ to_set l ∪ to_set r
    end.

  Fixpoint map {A B} (f : A → B) (t' : t A) : t B :=
    match t' with
    | Leaf       => Leaf
    | Node x l r => Node (f x) (map f l) (map f r)
    end.

  Lemma inorder_map {A B} (f: A -> B) t :
    inorder (map f t) = fmap f (inorder t).
  Proof.
    induction t as [|x l IHl r IHr]; csimpl; auto.
    by rewrite IHl IHr fmap_app.
  Qed.

  Lemma In_inorder_set {t} {x: K} :
    x ∈ inorder t <-> x ∈ to_set t.
  Proof. 
    induction t as [|x' l IHl r IHr]; simpl.
    - rewrite elem_of_nil. set_solver.
    - rewrite elem_of_cons elem_of_app IHl IHr. set_solver.
  Qed.


  Context (p: K -> K -> bool).

  Fixpoint locate (k: K) (Γ: t K -> t K) t' : (t K -> t K) * t K :=
    match t' with
    | Leaf        => (Γ, Leaf)
    | Node k' l r =>
      if p k  k' then locate k (fun h => Γ (Node k' h r)) l else
      if p k' k  then locate k (fun h => Γ (Node k' l h)) r
      else (Γ, t')
    end.

  Lemma locate_spec {k: K} {Γ t loc} :
    locate k Γ t = loc ->
    match loc with
    | (Γ', Leaf)        => Γ' Leaf = Γ t
    | (Γ', Node k' l r) =>
        Γ' (Node k' l r) = Γ t /\ p k' k = false /\ p k k' = false
    end.
  Proof.
    intros <-.
    induction t as [|k' l IHl r IHr] in k, Γ |-*; simpl; auto.
    destruct (p k' k) eqn:Hp1, (p k k') eqn:Hp2; naive_solver.
  Qed.

  Fact locate_combine (k: K) Γ t Γ' t' :
    locate k Γ t = (Γ', t') -> Γ' t' = Γ t.
  Proof.
    intros H%locate_spec. destruct t'; tauto.
  Qed.

  Fixpoint rec_insert k t :=
    match t with
    | Leaf        => Node k Leaf Leaf
    | Node k' l r =>
      if      p k  k' then Node k' (rec_insert k l) r
      else if p k' k  then Node k' l (rec_insert k r)
                      else Node k l r
    end.

  Lemma insert_via_locate (k: K) Γ t loc :
    locate k Γ t = loc ->
    Γ (rec_insert k t) =
    match loc with
    | (Γ', Leaf)       => Γ' (Node k Leaf Leaf)
    | (Γ', Node _ l r) => Γ' (Node k l r)
    end.
  Proof.
    intros <-.
    induction t as [|k' l IHl r IHr] in Γ |-*; simpl; auto.
    destruct (p k' k) eqn:Hp1, (p k k') eqn:Hp2; auto.
    - now rewrite <-IHl.
    - now rewrite <-IHr.
    - now rewrite <-IHl.
  Qed.

  Definition insert k t :=
    match locate k id t with
    | (Γ', Leaf      ) => Γ' (Node k Leaf Leaf)
    | (Γ', Node _ l r) => Γ' (Node k l    r   )
    end.

  Fact rec_insert_eq_insert (k: K) t :
    rec_insert k t = insert k t.
  Proof.
    change (rec_insert k t) with (id (rec_insert k t)).
    apply insert_via_locate; auto.
  Qed.

End locate.
Arguments Leaf {_}.
Arguments Node {_} _ _ _.

  Notation "∀T" := (fun t P => ∀ x, x ∈ to_set t → P x : Prop) (only parsing).

  Lemma ForallTree_insert k P t :
    (∀T t P) -> P k ->
    ∀T (rec_insert (λ x y, bool_decide (x < y)) k t) P.
  Proof.
    induction t in k |- *; simpl;
    repeat case_decide; set_solver.
  Qed.
  
  Lemma map_f_insert {K V} P Q x (t: t (K * V)) (f: K * V -> K) :
    (forall x y, P x y = Q (f x) (f y)) ->
    map f (rec_insert P x t) =
    rec_insert Q (f x) (map f t).
  Proof.
    intros H. induction t as [|kv tl IHl tr IHr]; simpl; auto.
    destruct  (P x kv) eqn:HP1,
              (P kv x) eqn:HP2; simpl.
    all: rewrite H in HP1; rewrite H in HP2.
    all: rewrite HP1; try rewrite HP2; simpl; congruence.
  Qed.


(* --------------------- Binary Search Trees ---------------------- *)
Section BST.
  Variable K: Type.
  Context {EqDecision_K : EqDecision K}
          {Countable_K : Countable K}.
  Context (p: K -> K -> bool).

  Set Default Proof Using "Type*".

  Inductive BST : t K → Prop :=
  | BST_Leaf : BST (@Leaf K)
  | BST_Node (x: K) (l r: t K) :
      BST l → BST r →
      (∀ y, y ∈ to_set l → p y x = true) →
      (∀ y, y ∈ to_set r → p x y = true) →
      BST (@Node K x l r).

  (* ------------------- Contexts  ----------------- *)
  Inductive ctx : (t K -> t K) -> Prop :=
  | ctx_id         : ctx id
  | ctx_ht {k t} Γ : ctx Γ -> ctx (λ h, Γ (Node k h t))
  | ctx_th {k t} Γ : ctx Γ -> ctx (λ h, Γ (Node k t h)).

  Hint Constructors ctx : ctx.

  Fact ctx_compose Γ Γ' :
    ctx Γ -> ctx Γ' -> ctx (Γ ∘ Γ').
  Proof. 
    intros H1 H2. revert H1. 
    induction H2 as [|k t Γ'|k t Γ'] in Γ |-*; auto.
    - intros. change (ctx (λ h, (Γ ∘ Γ')(Node k h t))).
      constructor; auto.
    - intros. change (ctx (λ h, (Γ ∘ Γ')(Node k t h))).
      constructor; auto.
  Qed.

  Lemma ctx_BST_subtree {Γ t} :
    ctx Γ -> BST (Γ t) -> BST t.
  Proof.
    induction 1 as [|k r Γ HΓ IH|k l Γ HΓ IH] in t |-* ; auto.
    all: intros H%IH; inversion H; auto.
  Qed.

  Lemma in_ctx_tree {x Γ t} :
    ctx Γ -> (x ∈ to_set (Γ t) <->  x ∈ to_set (Γ Leaf) \/ x ∈ to_set t).
  Proof.
    induction 1 as [|???? IH|???? IH] in t |-*; simpl.
    all: try rewrite !(IH (Node _ _ _)); set_solver.
  Qed.

  Lemma eq_ctx_tree {Γ} t :
    ctx Γ -> to_set (Γ t) = to_set (Γ Leaf) ∪ to_set t.
  Proof.
    induction 1 as [|???? IH|???? IH] in t |-*; simpl.
    all: try rewrite !(IH (Node _ _ _)); set_solver.
  Qed.


  Lemma ctx_locate k Γ (t: t K) Γ' t':
    ctx Γ -> locate p k Γ t = (Γ', t') -> ctx Γ'.
  Proof.
    induction t as [| k' l Hl r Hr ] in Γ |-*; simpl; intros HΓ.
    - intros [=]; congruence.
    - destruct (p k' k) eqn:Hp1, (p k k') eqn:Hp2; auto.
      + apply Hl; now constructor.
      + apply Hr; now constructor.
      + apply Hl; now constructor.
      + intros [=]; congruence.
  Qed.

  Fact BST_singleton k : BST (Node k Leaf Leaf).
  Proof.
    constructor; try constructor; simpl; set_solver.
  Qed.

  Lemma BST_sidecondition_equiv x l r :
    BST l /\ BST r ->
   ((∀ y, y ∈ to_set l → p y x = true) /\ (∀ y, y ∈ to_set r → p x y = true)
    <-> BST (Node x l r)).
  Proof. 
    intros [Hl Hr]; split.
    - intros. constructor; tauto.
    - intros H. inversion H; tauto.
  Qed.

  Notation locate := (locate p).
  Notation insert := (insert p).

(* [BST_ctx Γ K K'] expresses that Γ is a context with a hole that
    can be filled by any BST [t] whose keys are a subset of [K], and 
    once we fill the hole with [t], the resulting tree [Γ t] is
    a BST with keys that are a subset of K'.
  
  This latter coniditon can be memorized as Γ K ⊆ K'
*)
  Definition BST_ctx (Γ: t K -> t K) C C' :=
    forall t, BST t -> to_set t ⊆ C -> BST (Γ t) /\ to_set (Γ t) ⊆ C'.

  Lemma BST_ctx_singelton k (Γ: t K -> t K) C C' :
    {[k]} ⊆ C -> BST_ctx Γ C C' ->
    BST (Γ (Node k Leaf Leaf)).
  Proof.
    intros H1 Hctx.
    assert (BST (Node k Leaf Leaf)) as H by apply BST_singleton.
    now specialize (Hctx _ H) as []; set_solver.
  Qed.
  
  Fact BST_ctx_id C C' :
    C ⊆ C' -> BST_ctx id C C'.
  Proof.
    intros H t Hbst Hincl. split; auto. simpl.
    intros x Hx. now apply H, Hincl.
  Qed.

  Lemma BST_ctx_ht C k t :
    (∀ y, y ∈ C → p y k = true) ->
    BST (Node k Leaf t) ->
    BST_ctx (λ h, Node k h t) C ({[k]} ∪ C ∪ to_set t).
  Proof.
    intros H1 Ht t' Hbst Hincl. split.
    - inversion Ht; constructor; auto.
    - set_solver.
  Qed.

  Lemma BST_ctx_th C k t :
    (∀ y, y ∈ C → p k y = true) ->
    BST (Node k t Leaf) ->
    BST_ctx (λ h, Node k t h) C ({[k]} ∪ C ∪ to_set t).
  Proof.
    intros H1 Ht t' Hbst Hincl. split.
    - inversion Ht; constructor; auto.
    - set_solver.
  Qed.

  Fact BST_ctx_compose X Γ Γ' Y Y' :
    BST_ctx Γ X Y -> BST_ctx Γ' Y Y' -> BST_ctx (Γ' ∘ Γ) X Y'.
  Proof.
    intros H1 H2 t Ht H. simpl. 
    specialize (H1 _ Ht H). now apply H2.
  Qed.

  Fact BST_ctx_weakening_left Γ C C' C'' :
    C' ⊆ C -> BST_ctx Γ C C'' -> BST_ctx Γ C' C''.
  Proof.
    intros H1 H2 t Ht H. apply H2; [tauto|set_solver].
  Qed.

  Fact BST_ctx_weakening_right {Γ C} C' {C''} :
    C' ⊆ C'' -> BST_ctx Γ C C' -> BST_ctx Γ C C''.
  Proof.
    intros H1 H2 t Ht H. apply H2 in Ht; split; [tauto|set_solver].
  Qed.
  
  Context (Hp_asym : forall x y, p x y = true -> p y x = true -> False)
          (Hp_antisym  : forall x y, p x y = false -> p y x = false -> x = y).

  Set Default Proof Using "Type*".

  Lemma BST_ctx_locate_spec {k Γ t Γ' t'} C :
    BST t -> BST_ctx Γ ({[k]} ∪ to_set t) ({[k]} ∪ C) ->
    locate k Γ t = (Γ', t') ->
    BST t' /\ BST_ctx Γ' ({[k]} ∪ to_set t') ({[k]} ∪ C).
  Proof.
    intros Hbst. induction Hbst as [|k' l r Hl IHl Hr IHr H1 H2]
     in Γ |-*; simpl; intros Hctx.
    { intros [= <- <-]. split; first constructor. set_solver. }
    destruct (p k' k) eqn:Hp1, (p k k') eqn:Hp2.
    - edestruct Hp_asym; eauto.
    - intros Hloc. edestruct IHr; eauto.
      eapply BST_ctx_compose; eauto.
      eapply BST_ctx_weakening_right.
      2: apply BST_ctx_th.
      + set_solver.
      + intros y Hy.
        assert (y = k \/ y ∈ to_set r) as [|] by set_solver; subst; auto.
      + constructor; auto; [constructor|set_solver].
    - intros Hloc. edestruct IHl; eauto.
      eapply BST_ctx_compose; eauto.
      eapply BST_ctx_weakening_right.
      2: apply BST_ctx_ht.
      + set_solver.
      + intros y Hy.
        assert (y = k \/ y ∈ to_set l) as [|] by set_solver; subst; auto.
      + constructor; auto; [constructor|set_solver].
    - assert (k' = k) as -> by now apply Hp_antisym.
      intros [= <- <-]. split; auto.
      now constructor.
  Qed.

  Corollary BST_ctx_locate_root {k t Γ' t'} :
    BST t ->
    locate k id t = (Γ', t') ->
    BST t' /\ BST_ctx Γ' ({[k]} ∪ to_set t') ({[k]} ∪ to_set t).
  Proof.
    intros Hbst Hloc.
    eapply BST_ctx_locate_spec; eauto.
    apply BST_ctx_id. set_solver.
  Qed.

  Lemma BST_insert k t :
    BST t -> BST (insert k t).
  Proof.
    intros Hbst. unfold insert.
    destruct (locate k id t) as [Γ' t'] eqn:Hloc.
    specialize (BST_ctx_locate_root Hbst Hloc) as [Hbst' Hctx']; auto.
    destruct t' as [|k' l r].
    - eapply BST_ctx_singelton; last eauto; set_solver.
    - apply locate_spec in Hloc as (H1 & H2 & H3).
      assert (k' = k) as -> by now apply Hp_antisym.
      rewrite H1; apply Hbst.
  Qed.


End BST.
End module.
End tree.
Arguments tree.Leaf {_}.
Arguments tree.Node {_} _ _ _.
Arguments tree.ctx {_} _.


Global Notation "∀T" := (fun t P => ∀ x, x ∈ tree.to_set t → P x : Prop) (only parsing).
Global Hint Constructors tree.ctx : tree_ctx.

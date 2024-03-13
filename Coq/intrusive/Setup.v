From iris.algebra Require Export excl agree csum.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Export assert proofmode notation adequacy.
From iris.heap_lang.lib Require Export array par diverge.
From iris.prelude Require Export options.
From iris.bi Require Export big_op.

From diaframe.heap_lang Require Export proof_automation.

Section location_index_automation.
  Context `{!heapGS Σ}.

  Class FindBaseLoc (li : loc) (lo : loc) (o : Z) :=
    find_base_loc : li = lo +ₗ o.

  Global Hint Mode FindBaseLoc + - - : typeclass_instances.

  Global Instance default_base_loc (l : loc) : FindBaseLoc l l 0 | 50.
  Proof. by rewrite /FindBaseLoc Loc.add_0. Qed.

  Global Instance rec_add_base_loc (l lo : loc) (o1 o2 : Z) :
    FindBaseLoc l lo o2 →
    FindBaseLoc (l +ₗ o1) lo (o2 + o1).
  Proof.
    rewrite /FindBaseLoc => ->.
    by rewrite Loc.add_assoc.
  Qed.

  Global Instance mapsto_val_from_base_locs (l1 l1o l2 l2o : loc) (v1 v2 : val) (o1 o2 : Z) :
    FindBaseLoc l1 l1o o1 →
    FindBaseLoc l2 l2o o2 →
    TCEq l1o l2o →
    SolveSepSideCondition (o1 = o2) →
    HINT l1 ↦ v1 ✱ [- ; ⌜v1 = v2⌝] ⊫ [id]; l2 ↦ v2 ✱ [⌜v1 = v2⌝ ] | 64.
  Proof.
    rewrite /FindBaseLoc TCEq_eq /SolveSepSideCondition => -> -> -> ->.
    iSteps.
  Qed.
End location_index_automation.

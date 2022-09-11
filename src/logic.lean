
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro np,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_cases p: P,
    --case P
    exact p,
    --case ¬P
    have ct := nnp p,
    contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  have fst := doubleneg_elim P,
  have snd := doubleneg_intro P,
  split,
    --part ¬¬P → P
    exact fst,
    --part P → ¬¬P
    exact snd,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro disj,
  cases disj,
    -- case P
    right,
      exact disj,
    -- case Q
    left,
      exact disj,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro conj,
  cases conj with p q,
  split,
    -- part Q
    exact q,
    -- part P
    exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro disj,
  intro p,
  cases disj,
    --case ¬P
    have contra := disj p,
    contradiction,
    --case Q
    exact disj,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro disj,
  intro np,
  cases disj,
    --case P
    have contra := np disj,
    contradiction,
    --case Q
    exact disj,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro impl,
  intro nq,
  intro p,
  have q := impl p,
  have contra := nq q,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro impl,
  intro p,
  by_cases q: Q,
    --case Q
    exact q,
    --case ¬Q
    have np := impl q,
    have contra := np p,
    contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  have fst := impl_as_contrapositive P Q,
  have snd := impl_as_contrapositive_converse P Q,
  split,
    --part (P → Q) → (¬Q → ¬P)
    exact fst,
    --part (¬Q → ¬P) → (P → Q)
    exact snd,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro n_lem,
  have lem: P ∨ ¬P,
    right,
    intro p,
    have disj: P ∨ ¬P,
      left,
      exact p,
    have ct := n_lem disj,
    contradiction,
  have ct := n_lem lem,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pierce,
  intro np,
  have impl: P → Q,
    intro p,
    contradiction,
  have p := pierce impl,
  have ct := np p,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro disj,
  intro n_conj,
  cases n_conj,
  cases disj,
    --case P
    have contra := n_conj_left disj,
    contradiction,
    --case Q
    have contra := n_conj_right disj,
    contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro conj,
  intro neg_disj,
  cases conj,
  cases neg_disj,
    --case ¬P
    have ct := neg_disj conj_left,
    contradiction,
    --case ¬Q
    have ct := neg_disj conj_right,
    contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

--Adicionado Pelo Ian--
theorem disj_impl : 
  (∀ p q: Prop, p → p ∨ q) :=
begin
  intro p,
  intro q,
  intro p_impl,
  left,
  exact p_impl,
end
----------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro neg_disj,
  split,
    --part ¬P
    intro p,
    have impl := disj_impl P Q,
    have disj := impl p,
    have ct := neg_disj disj,
    contradiction,
    --part ¬Q
    intro q,
    have impl := disj_impl Q P,
    have wr_disj := impl q,
    have disj_cm := disj_comm Q P,
    have rght_disj := disj_cm wr_disj,
    have ct := neg_disj rght_disj,
    contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro conj_negs,
  intro disj,
  cases conj_negs with np nq,
  cases disj with p q,
    --case P
    have ct := np p,
    contradiction,
    --case Q
    have ct := nq q,
    contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro n_conj,
  by_cases P,
    --case P
    left,
    intro q,
    have conj: P∧Q,
      split,
      --part P
      exact h,
      --part Q
      exact q,
    have ct := n_conj conj,
    contradiction,

    --case ¬P
    right,
    exact h,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro disj_negs,
  intro conj,
  cases conj with p q,
  cases disj_negs with nq np,
    --case ¬Q
    have ct := nq q,
    contradiction,
    --case ¬P
    have ct := np p,
    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  have dmg_conj := demorgan_conj P Q,
  have dmg_conj_cnv := demorgan_conj_converse P Q,
  split,
    --part ¬(P∧Q) → (¬Q ∨ ¬P)
    exact dmg_conj,
    --part (¬Q ∨ ¬P) → ¬(P ∧ Q)
    exact dmg_conj_cnv,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  have dmg_disj := demorgan_disj P Q,
  have dmg_disj_con := demorgan_disj_converse P Q,
  split,
    --part ¬(P ∨ Q) → (¬P ∧ ¬Q)
    exact dmg_disj,
    --part (¬P ∧ ¬Q) → ¬(P ∨ Q)
    exact dmg_disj_con,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro conj_disj,
  cases conj_disj with p disj,
  cases disj with q r,
    --case Q
    left,
    split,
      --part P
      exact p,
      --part Q
      exact q,
    --case R
    right,
    split,
      --part P
      exact p,
      --part R
      exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro disj_conj,
  cases disj_conj with conj_pq conj_pr,
    --case P∧Q
    cases conj_pq with p q,
    split,
      --part P
      exact p,
      --part Q∨R
      left,
        exact q,
    --case P∧R
    cases conj_pr with p r,
    split,
      --part P
      exact p,
      --part Q∨R
      right,
        exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro distr_disj,
  split,
    --part P∨Q
    cases distr_disj with p conj_qr,
      --case P
      left,
        exact p,
      --case Q∧R
      right,
        cases conj_qr with q r,
        exact q,
    
    --part P∨R
    cases distr_disj with p conj_qr,
      --case P
      left,
        exact p,
      --case Q∧R
      right,
        cases conj_qr with q r,
        exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro distr_conj,
  cases distr_conj with disj_pq disj_pr,
  cases disj_pq with p q,
    --case P
    left,
      exact p,
    --case Q
    cases disj_pr with p r,
      --case P
      left,
        exact p,
      --case R
      right,
        split,
          --part Q
          exact q,
          --part R
          exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro cur,
  intro p,
  intro q,
  have conj : P ∧ Q,
    split,
      --part P
      exact p,
      --part Q
      exact q,
  
  have r := cur conj,
  exact r,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro cur,
  intro conj,
  cases conj with p q,
  have impl := cur p,
  have r := impl q,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro conj,
  cases conj with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro conj,
  cases conj with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  have left := weaken_conj_left P P,
  split,
    --part P∧P → P
    exact left,
    --part P → P∧P
    intro p,
    split,
      --part P
      exact p,
      --part P
      exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
    --part P∨P → P
    intro disj,
    cases disj with p p,
      --case P
      exact p,
      --case P
      exact p,
    --part P → P∨P
    have wk_disj := weaken_disj_left P P,
    exact wk_disj,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop

------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro not_exists,
  intro x,
  intro px,
  have exist: ∃ x, P x,
    existsi x,
    exact px,
  have ct := not_exists exist,
  contradiction,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro for_all,
  intro exist,
  cases exist with x px,
  have npx := for_all x,
  have ct := npx px,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  have contrapos: ¬(∃x, ¬P x) → (∀x, P x),
    intros neg_exist x,
    by_contradiction npx,
    have exist: ∃x, ¬P x,
      existsi x,
      exact npx,
    exact neg_exist exist,
  
  have impl := contrapositive_law (¬(∃x, ¬P x)) (∀x, P x),
  cases impl with l r,
  have contrapos_conv := l contrapos,

  intro for_all,
  have neg_neg_exist := contrapos_conv for_all,
  have db_neg := doubleneg_elim (∃x, ¬P x),
  exact db_neg neg_neg_exist,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro exist,
  intro for_all,
  cases exist with x npx,
  have px := for_all x,
  have ct := npx px,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  --part ¬(∀x, P x) → (∃x, ¬P x)
  exact demorgan_forall U P,
  --part (∃x, ¬P x) → ¬(∀x, P x)
  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  have dmg_exist := demorgan_exists U P,
  have dmg_exist_cn := demorgan_exists_converse U P,
  split,
    --part ¬(∃x, P x) → (∀x, ¬P x)
    exact dmg_exist,
    --part (∀x, ¬P x) → ¬(∃x, P x)
    exact dmg_exist_cn,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro exist,
  intro for_all,
  cases exist with x px,
  have npx := for_all x,
  have ct := npx px,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro for_all,
  intro exist,
  cases exist with x npx,
  have px := for_all x,
  have ct := npx px,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro n_exist,
  intro x,

  --Disapointing magic--
  by_cases P x,
    --case P x
    exact h,

    --case ¬P x
    have exist: ∃(x: U), ¬P x,
    existsi x,
    exact h,
    have ct := n_exist exist,
    contradiction,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro neg_forall,
  by_contradiction neg_exist,
  have dmg_exists := demorgan_exists U P,
  have for_all := dmg_exists neg_exist,
  exact neg_forall for_all,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  --part (∀x, P x) → ¬(∃x, ¬P x)
  exact forall_as_neg_exists U P,
  --part ¬(∃x, ¬P x) → (∀x, P x)
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  --part (∃x, P x) → ¬(∀x, ¬P x)
  exact exists_as_neg_forall U P,
  --part ¬(∀x, ¬P x) → (∃x, P x)
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro exists_conj,
  cases exists_conj with x conj_x,
  cases conj_x with px qx,
  split,
    --part (∃x, P x)
    existsi x,
    exact px,
    --part (∃x, Q x)
    existsi x,
    exact qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro exists_disj,
  cases exists_disj with x disj_x,
  cases disj_x with px qx,
    --case P x
    left,
    existsi x,
    exact px,
    --case Q x
    right,
    existsi x,
    exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro exists_disj,
  cases exists_disj with exists_px exists_qx,
    --case (∃x, P x)
    cases exists_px with x px,
    existsi x,
    left,
    exact px,
    --case (∃x, Q x)
    cases exists_qx with x qx,
    existsi x,
    right,
    exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro forall_conj,
  split,
    --part (∀x, P x)
    intro x,
    have conj := forall_conj x,
    exact conj.left,
    --part (∀x, Q x)
    intro x,
    have conj := forall_conj x,
    exact conj.right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro forall_conj,
  cases forall_conj with forall_px forall_qx,
  intro x,
  split,
    --part P x
    exact forall_px x,
    --part Q x
    exact forall_qx x,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro forall_disj,
  intro x,
  cases forall_disj with forall_px forall_qx,
    --case (∀x, P x)
    left,
    exact forall_px x,
    --case (∀x, Q x)
    right,
    exact forall_qx x,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate

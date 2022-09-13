
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros P P',
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  by_cases h : P,
  {
    intro P'',
    exact h,
  }, 
  {
    intro P',
    contradiction,
  },
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  by_cases h : P,
  {
    intro P'',
    exact h,
  }, 
  {
    intro P',
    contradiction,
  },
  intros P P',
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro D,
  cases D,
  right,
  apply D,
  left,
  apply D, 
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro D,
  cases D,
  split,
  apply D_right,
  apply D_left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro D,
  intro P,
  cases D,
  contradiction,
  apply D,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros D P',
  cases D,
  contradiction,
  apply D,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros D Q' P,
  have Q := D  P,
  contradiction, 
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros D P,
  by_contra Q,
  have P' := D Q,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intros D Q' P,
  have Q := D  P,
  contradiction,
  intros D P,
  by_contra Q,
  have P' := D Q,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro D,
  by_cases h : P,
  {
    apply D,
    left,
    exact h,
  },
  {
    apply D,
    right,
    exact h,
  },
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros h1 np,
  by_cases h : (P→Q),
  have p : P := h1 h,
  contradiction,
  have h2 : (P → Q),
  intro P,
  contradiction,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros ha hb,
  cases hb,
  cases ha,
  apply hb_left,
  contradiction,
  apply hb_right,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros ha hb,
  cases ha,
  cases hb,
  have boom := hb ha_left,
  exact boom,
  have boom := hb ha_right,
  exact boom,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro D,
  split,
  intro P,
  apply D,
  left,
  exact P,
  intro Q,
  apply D,
  right,
  exact Q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros ha hb,
  cases ha with ha_l ha_r,
  cases hb,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h1,
  by_contradiction h2,
  have hp : (P∧Q),
  split,
  by_contradiction h3,
  apply h2,
  right,
  assumption,
  by_contradiction h3,
  apply h2,
  left,
  assumption,
  apply h1,
  contradiction,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros h1 h2,
  cases h2,
  cases h1,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  {
    intro h1,
    by_contradiction h2,
    have hp : (P∧Q),
    split,
    by_contradiction h3,
    apply h2,
    right,
    assumption,
    by_contradiction h3,
    apply h2,
    left,
    assumption,
    apply h1,
    contradiction,
  },
  {
    intros h1 h2,
    cases h2,
    cases h1,
    contradiction,
    contradiction,
  }
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  {
    intro D,
    split,
    intro P,
    apply D,
    left,
    exact P,
    intro Q,
    apply D,
    right,
    exact Q,
  },
  {
    intros ha hb,
    cases ha with ha_l ha_r,
    cases hb,
    contradiction,
    contradiction,
  }
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h1,
  cases h1,
  cases h1_right,
  left,
  split,
  assumption,
  assumption,
  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h1,
  cases h1,
  {
    cases h1,
    split,
    assumption,
    left,
    assumption,
  },
  {
    cases h1,
    split,
    assumption,
    right,
    assumption,
  }
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h1,
  cases h1,
  {
    split,
    left,
    assumption,
    left,
    assumption,
  },
  {
    cases h1,
    split,
    right,
    assumption,
    right,
    assumption,
  }
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with hl hr,
  cases hl,
  left,
  assumption,
  cases hr,
  left,
  assumption,
  right,
  split,
  assumption,
  assumption,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros h1 h2 h3,
  apply h1,
  split,
  assumption,
  assumption,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h1 h2,
  cases h2,
  apply h1,
  assumption,
  assumption,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro P,
  exact P,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro P,
  left,
  exact P,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro Q,
  right,
  exact Q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  {
    intro PD,
    cases PD,
    assumption,
  },
  {
    intro P,
    split,
    assumption,
    assumption,
  }
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  {
    intro P2,
    cases P2,
    assumption,
    assumption,
  },
  {
    intro P,
    left,
    assumption,
  }
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
  intros h1 x p,
  apply h1,
  existsi x,
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros h1 h2,
  cases h2 with x px,
  have h : ¬P x := h1 x,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intros h1,
  by_contradiction h2,
  apply h1,
  intro u,
  by_contradiction h3,
  apply h2,
  existsi u,
  assumption,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros h1 h2,
  cases h1 with x npx,
  have px : P x := h2 x,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  {
    intros h1,
    by_contradiction h2,
    apply h1,
    intro u,
    by_contradiction h3,
    apply h2,
    existsi u,
    assumption,
  },
  {
    intros h1 h2,
    cases h1 with x npx,
    have px : P x := h2 x,
    contradiction,
  }
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  {
    intros h1 x p,
    apply h1,
    existsi x,
    exact p,
  },
  {
    intros h1 h2,
    cases h2 with x px,
    have h : ¬P x := h1 x,
    contradiction,
  }
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros h1 h2,
  cases h1 with x px,
  have npx : ¬P x := h2 x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros h1 h2,
  cases h2 with x npx,
  have px : P x := h1 x,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros h1 x,
  by_contradiction npu,
  apply h1,
  existsi x,
  assumption,  
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h1,
  by_contradiction nepx,
  apply h1,
  intros x,
  by_contradiction px,
  apply nepx,
  existsi x,
  assumption,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  {
    intros h1 h2,
    cases h2 with x npx,
    have px : P x := h1 x,
    contradiction,
  },
  {
    intros h1 x,
    by_contradiction npu,
    apply h1,
    existsi x,
    assumption,
  }
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  {
    intros h1 h2,
    cases h1 with x px,
    have npx : ¬P x := h2 x,
    contradiction,
  },
  {
    intro h1,
    by_contradiction nepx,
    apply h1,
    intros x,
    by_contradiction px,
    apply nepx,
    existsi x,
    assumption,
  }
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h1,
  split,
  {
    cases h1 with x pqx,
    cases pqx,
    existsi x,
    assumption,
  },
  {
    cases h1 with x pqx,
    cases pqx,
    existsi x,
    assumption,
  }
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h1,
  cases h1 with x pqx,
  cases pqx,
  {
    left,
    existsi x,
    assumption,
  },
  {
    right,
    existsi x,
    assumption,
  }
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h1,
  cases h1,
  {
    cases h1 with x px,
    existsi x,
    left,
    assumption,
  },
  {
    cases h1 with x qx,
    existsi x,
    right,
    assumption,
  }
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h1,
  split,
  {
    intro x,
    have h : P x ∧ Q x := h1 x,
    cases h,
    assumption,
  },
  {
    intro x,
    have h : P x ∧ Q x := h1 x,
    cases h,
    assumption,
  }
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h1,
  intro x,
  cases h1,
  split,
  {
    have h : P x := h1_left x,
    assumption,
  },
  {
    have h : Q x := h1_right x,
    assumption,
  }
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros h1 x,
  cases h1,
  {
    left,
    have h : P x := h1 x,
    assumption,
  },
  {
    right,
    have h : Q x := h1 x,
    assumption,
  }
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

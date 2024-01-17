section propositional

variable (P Q : Prop)

------------------------------------------------
-- Proposições de dupla negação:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P :=
by
  intro p
  intro np
  contradiction


theorem doubleneg_elim :
  ¬¬P → P  :=
by
  intro p
  apply Classical.byContradiction
  intro np
  contradiction


theorem doubleneg_law :
  ¬¬P ↔ P  :=
by
  apply Iff.intro
  exact doubleneg_elim P
  exact doubleneg_intro P


------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption


theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
by
  intro ⟨p, q⟩
  constructor
  exact q
  exact p


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
by
  intro h
  intro p
  cases h
  contradiction
  assumption

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
by
  intro h
  intro h'
  cases h
  contradiction
  assumption


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
by
  intro pq
  intro notq
  intro p
  have q: Q := pq p
  contradiction


theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
by
  intro nqnp
  intro p
  by_cases q: Q
  assumption
  have np: ¬P := nqnp q
  contradiction


theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
by
  apply Iff.intro
  exact impl_as_contrapositive P Q
  exact impl_as_contrapositive_converse P Q


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
by
  intro h
  apply h
  apply Or.inr
  intro p
  apply h
  apply Or.inl
  assumption


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
by
  intro hp
  intro not_p
  apply not_p
  apply hp
  intro p
  contradiction


  theorem peirce_law :
  ((P → Q) → P) → P  :=
by
  intro pqp
  have peirceLawWeak: (((P → Q) → P) → ¬¬P) := peirce_law_weak P Q
  have nnp: ¬¬P := peirceLawWeak pqp
  apply Classical.byContradiction
  intro np
  contradiction


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
by
  intro pq
  intro np_nq
  apply Or.elim pq
  intro p
  exact And.left np_nq p
  intro q
  exact And.right np_nq q


theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
by
  intro pq
  intro np_nq
  apply Or.elim np_nq
  intro np
  have boom: False := np (And.left pq)
  contradiction
  intro nq
  have boom: False := nq (And.right pq)
  contradiction


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
by
  intro npq
  apply And.intro
  intro p
  apply npq
  apply Or.inl
  assumption
  intro q
  apply npq
  apply Or.inr
  assumption


theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
by
  intro npnq
  intro pq
  apply Or.elim pq
  intro p
  have boom: False := (And.left npnq) p
  contradiction
  intro q
  have boom: False := (And.right npnq) q
  contradiction


theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
by
  intro npq
  by_cases p: P
  apply Or.inl
  intro q
  apply npq
  apply And.intro
  assumption
  assumption
  apply Or.inr
  assumption


theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
by
  intro nqnp
  intro pq
  apply Or.elim nqnp
  intro nq
  have boom: False := nq (And.right pq)
  contradiction
  intro np
  have boom: False := np (And.left pq)
  contradiction


theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
by
  apply Iff.intro
  exact demorgan_conj P Q
  exact demorgan_conj_converse P Q


theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
by
  apply Iff.intro
  exact demorgan_disj P Q
  exact demorgan_disj_converse P Q

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
by
  intro ⟨p, qr⟩
  apply Or.elim qr
  intro q
  apply Or.inl
  apply And.intro
  assumption
  assumption
  intro r
  apply Or.inr
  apply And.intro
  assumption
  assumption


theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
by
  intro h
  apply Or.elim h
  intro pq
  apply And.intro
  exact And.left pq
  apply Or.inl
  exact And.right pq
  intro pr
  apply And.intro
  exact And.left pr
  apply Or.inr
  exact And.right pr


theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
by
  intro pqr
  apply Or.elim pqr
  intro p
  apply And.intro
  apply Or.inl
  assumption
  apply Or.inl
  assumption
  intro qr
  apply And.intro
  apply Or.inr
  exact And.left qr
  apply Or.inr
  exact And.right qr


theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
by
  intro ⟨pq, pr⟩
  apply Or.elim pr
  intro p
  apply Or.inl
  assumption
  intro r
  apply Or.elim pq
  intro p
  apply Or.inl
  assumption
  intro q
  apply Or.inr
  apply And.intro
  assumption
  assumption


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
by
  intro pqr
  intro p
  intro q
  apply pqr
  apply And.intro
  assumption
  assumption


theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
by
  intro pqr
  intro pq
  have qr: (Q→R) := pqr (And.left pq)
  have r: R := qr (And.right pq)
  assumption


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
by
  intro
  assumption

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
by
  intro p
  apply Or.inl
  assumption


theorem weaken_disj_left :
  Q → (P∨Q)  :=
by
  intro q
  apply Or.inr
  assumption


theorem weaken_conj_right :
  (P∧Q) → P  :=
by
  intro pq
  exact And.left pq


theorem weaken_conj_left :
  (P∧Q) → Q  :=
by
  intro pq
  exact And.right pq


theorem conj_idempot :
  (P∧P) ↔ P :=
by
  apply Iff.intro
  intro pp
  exact And.left pp
  intro p
  apply And.intro
  assumption
  assumption


theorem disj_idempot :
  (P∨P) ↔ P  :=
by
  apply Iff.intro
  intro pp
  apply Or.elim pp
  intro p
  assumption
  intro p
  assumption
  intro p
  apply Or.inl
  assumption


end propositional


----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U -> Prop)


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
by
  intro h
  intro x
  intro px
  apply h
  apply Exists.intro x
  assumption


theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
by
  intro h
  intro px
  apply Exists.elim px
  intro x
  intro pxx
  have npx: ¬P x := h x
  contradiction


theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
by
  intro h
  apply Classical.byContradiction
  intro hp
  apply h
  intro x
  by_cases px: P x
  assumption
  suffices hpp: (∃x, ¬P x) from False.elim (hp hpp)
  apply Exists.intro x
  assumption


theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
by
  intro np
  intro fpx
  apply Exists.elim np
  intro x
  intro npx
  have px: P x := fpx x
  contradiction


theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
by
  apply Iff.intro
  exact demorgan_forall U P
  exact demorgan_forall_converse U P


theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
by
  apply Iff.intro
  exact demorgan_exists U P
  exact demorgan_exists_converse U P


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
by
  intro h
  intro hp
  apply Exists.elim h
  intro x
  intro px
  have npx: ¬P x := hp x
  contradiction


theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
by
  intro h
  intro hp
  apply Exists.elim hp
  intro x
  intro npx
  have px: P x := h x
  contradiction


theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
by
  intro h
  intro x
  by_cases px: P x
  assumption
  suffices hp: (∃x, ¬P x) from False.elim (h hp)
  apply Exists.intro x
  assumption


theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
by
  intro h
  apply Classical.byContradiction
  intro hp
  apply h
  intro x
  intro px
  apply hp
  apply Exists.intro x
  assumption


theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
by
  apply Iff.intro
  exact forall_as_neg_exists U P
  exact forall_as_neg_exists_converse U P


theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
by
  apply Iff.intro
  exact exists_as_neg_forall U P
  exact exists_as_neg_forall_converse U P


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
by
  intro ⟨x,q⟩
  apply And.intro
  apply Exists.intro x
  exact And.left q
  apply Exists.intro x
  exact And.right q


theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
by
  intro h
  apply Exists.elim h
  intro x
  intro hpp
  apply Or.elim hpp
  intro px
  apply Or.inl
  apply Exists.intro x
  assumption
  intro qx
  apply Or.inr
  apply Exists.intro x
  assumption


theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
by
  intro h
  apply Or.elim h
  intro epx
  apply Exists.elim epx
  intro x
  intro px
  apply Exists.intro x
  apply Or.inl
  assumption
  intro eqx
  apply Exists.elim eqx
  intro x
  intro qx
  apply Exists.intro x
  apply Or.inr
  assumption


theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
by
  intro h
  apply And.intro
  intro x
  have pxqx: P x ∧ Q x := h x
  exact And.left pxqx
  intro x
  have pxqx: P x ∧ Q x := h x
  exact And.right pxqx


theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
by
  intro h
  intro x
  have px: P x := (And.left h) x
  apply And.intro
  assumption
  have qx: Q x := (And.right h) x
  assumption


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
by
  intro h
  intro x
  apply Or.elim h
  intro fpx
  have px: P x := fpx x
  apply Or.inl
  assumption
  intro fqx
  have qx: Q x := fqx x
  apply Or.inr
  assumption


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

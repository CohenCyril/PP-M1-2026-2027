From HB Require Import structures.
From Coq Require Import String.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From deriving Require Import deriving.
From mathcomp Require Import zify lra ring.

From ND Require Import extra.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
#[global] Set Uniform Inductive Parameters.

Declare Scope NJ_scope.
Delimit Scope NJ_scope with NJ.
Local Open Scope NJ_scope.

Module NJ.

Module Op.
Inductive bin : Type := Or | And | Imply.
End Op.

Definition binOp_indDef := [indDef for Op.bin_rect].
Canonical binOp_indType := IndType Op.bin binOp_indDef.

Print Op.bin.

Definition binOp_hasDecEq := [derive hasDecEq for Op.bin].
HB.instance Definition _ := binOp_hasDecEq.
Definition binOp_hasChoice := [derive hasChoice for Op.bin].
HB.instance Definition _ := binOp_hasChoice.
Definition binOp_isCountable := [derive isCountable for Op.bin].
HB.instance Definition _ := binOp_isCountable.

Inductive formula : Type :=
| Var of nat
| Bot
| BinOp (_ : Op.bin) (_ : formula) (_ : formula). 
Bind Scope NJ_scope with formula.

Definition formula_indDef := [indDef for formula_rect].
Canonical formula_indType := IndType formula formula_indDef.

Definition formula_hasDecEq := [derive hasDecEq for formula].
HB.instance Definition _ := formula_hasDecEq.
Definition formula_hasChoice := [derive hasChoice for formula].
HB.instance Definition _ := formula_hasChoice.
Definition formula_isCountable := [derive isCountable for formula].
HB.instance Definition _ := formula_isCountable.

Eval compute in (Var 0 == Bot).

Notation Or := (BinOp Op.Or).
Notation And := (BinOp Op.And).
Notation Imply := (BinOp Op.Imply).
(* Check (fun x y => x \/ y). *)
Notation "A ∨ B" := (Or A B) (at level 85) : NJ_scope.
Notation "A ∧ B" := (And A B) (at level 80) : NJ_scope.
Notation "A ⇒ B" := (Imply A B) (right associativity, at level 99) : NJ_scope.
Notation "⊥" := Bot  : NJ_scope.
Notation Neg := (fun A => A ⇒ ⊥).
Notation "¬ A" := (A ⇒ ⊥) (at level 75) : NJ_scope.
Notation Top := (¬ ⊥).
Notation "⊤" := Top : NJ_scope.

(* Sequents *)

Record sequent := Sequent {
  hypotheses : list formula;
  thesis : formula
}.
Bind Scope NJ_scope with sequent.

Scheme sequent_rect := Induction for sequent Sort Type.

Definition sequent_indDef := [indDef for sequent_rect].
Canonical sequent_indType := IndType sequent sequent_indDef.

Definition sequent_hasDecEq := [derive hasDecEq for sequent].
HB.instance Definition _ := sequent_hasDecEq.
Definition sequent_hasChoice := [derive hasChoice for sequent].
HB.instance Definition _ := sequent_hasChoice.
Definition sequent_isCountable := [derive isCountable for sequent].
HB.instance Definition _ := sequent_isCountable.

Coercion singlef (f : formula) : list formula := [:: f].
Notation "Γ ⊢ B" := (Sequent Γ B) (at level 100) : NJ_scope.
Notation "⊢ B" := (Sequent [::] B) (at level 100) : NJ_scope.

(* Rules *)

Record rule := Rule {
              premises : list sequent;
              conclusion : sequent;
}.
Bind Scope NJ_scope with rule.

Scheme rule_rect := Induction for rule Sort Type.

Definition rule_indDef := [indDef for rule_rect].
Canonical rule_indType := IndType rule rule_indDef.

Definition rule_hasDecEq := [derive hasDecEq for rule].
HB.instance Definition _ := rule_hasDecEq.
Definition rule_hasChoice := [derive hasChoice for rule].
HB.instance Definition _ := rule_hasChoice.
Definition rule_isCountable := [derive isCountable for rule].
HB.instance Definition _ := rule_isCountable.

Coercion JustConcl (s : sequent) : rule := Rule [::] s.

(* Derivation and derivability *)

Inductive derivation (premises : list sequent) : sequent -> Type :=
| Premise s i : tnth (in_tuple premises) i = s -> derivation s
| Ax Γ (i : 'I_(size Γ)) A : tnth (in_tuple Γ) i = A -> derivation (Γ ⊢ A)
| BotE Γ A : derivation (Γ ⊢ ⊥) -> derivation (Γ ⊢ A)
| AndI Γ A B : derivation (Γ ⊢ A) -> derivation (Γ ⊢ B) ->
         derivation (Γ ⊢ A ∧ B)
| AndE1 Γ A B : derivation (Γ ⊢ A ∧ B) -> derivation (Γ ⊢ A)
| AndE2 Γ A B : derivation (Γ ⊢ A ∧ B) -> derivation (Γ ⊢ B)
| OrI1 Γ A B : derivation (Γ ⊢ A) -> derivation (Γ ⊢ A ∨ B)
| OrI2 Γ A B : derivation (Γ ⊢ B) -> derivation (Γ ⊢ A ∨ B)
| OrE Γ A B C : derivation (Γ ⊢ A ∨ B) -> 
                derivation (A :: Γ ⊢ C) ->
                derivation (B :: Γ ⊢ C) ->
                derivation (Γ ⊢ C)
| ImplyI Γ A B : derivation (A :: Γ ⊢ B) -> derivation (Γ ⊢ A ⇒ B)
| ImplyE Γ A B : derivation (Γ ⊢ A ⇒ B) -> derivation (Γ ⊢ A) ->
                 derivation (Γ ⊢ B).
Arguments Ax {_ _}.
Arguments Premise {_ _}.
Derive Dependent Inversion derivationP with
  (forall prem s, derivation prem s) Sort Type.

Definition derivable (r : rule) :=
 derivation (premises r) (conclusion r).

Example der0 : derivation [::] ([:: Var 0; Var 1] ⊢ Var 0).
Proof. 
by apply: (Ax [ord 0]).
Defined.
Print der0.

Example der1 : derivation [::] ([:: Var 0; Var 1] ⊢ Var 0 ∧ Var 1).
Proof. 
apply: AndI.
  exact: der0.
exact: (Ax [ord 1]).
Defined.
Print der1.

Definition derivations (ls : list sequent) :=
  forall i, derivation [::] (tnth (in_tuple ls) i).

Definition admissible (r : rule) :=
  derivations (premises r) ->
  derivation [::] (conclusion r).

Definition reversible (r : rule) :=
  derivation [::] (conclusion r) ->
  derivations (premises r).

Theorem derivable_admissible (r : rule) :
  derivable r -> admissible r.
Proof.
rewrite /derivable /admissible /derivations/=.
case: r => prems concl /=.
move=> rd prem_der.
elim: rd => //=.
- move=> s i. move=> <-; exact: prem_der.
- exact: @Ax.
- move=> Γ A ? ?; exact: BotE.
- admit.
- admit. 
- admit.
- admit. 
- admit.
- admit. 
- admit. 
- admit.
Admitted.

Definition modus_ponens Γ A B : rule :=
  Rule [:: A :: Γ ⊢ B; Γ ⊢ A] (Γ ⊢ B). 

Ltac Intro := (apply: ImplyI).
Ltac AlmostAssert A := (apply: (@ImplyE _ _ A)). 
Ltac Premise i := (exact: (Premise [ord i])).

Lemma modus_ponens_derivable Γ A B :
  derivable (modus_ponens Γ A B).
Proof.
rewrite /derivable /modus_ponens/=.
AlmostAssert A.
  Intro.
  Premise 0.
Premise 1.
Qed.

Ltac Assert A := (apply: (modus_ponens_derivable _ A)). 

Lemma modus_ponens_derivable' Γ A B :
  derivable (modus_ponens Γ A B).
Proof.
rewrite /derivable /modus_ponens/=.
Assert A.
Qed.

Definition intro_imply_rule (Γ : list formula) (A B : formula) : rule. Admitted.

Lemma intro_imply_rule_derivable  Γ A B : derivable (intro_imply_rule  Γ A B).
Admitted.

Lemma intro_imply_rule_reversible  Γ A B : reversible (intro_imply_rule  Γ A B).
Admitted.

End NJ.




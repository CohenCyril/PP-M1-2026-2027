From HB Require Import structures.
From Coq Require Import String.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From elpi.apps Require Import derive.std.
From deriving Require Import deriving.
From mathcomp Require Import zify lra ring.

From ND Require Import extra.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope NJi_scope.
Delimit Scope NJi_scope with NJi.
Local Open Scope NJi_scope.

Module NJi.

(************)
(* Formulae *)
(************)

Inductive formula : Type :=
  | Var of nat
  | Imply of formula & formula.
Bind Scope NJi_scope with formula.

Definition formula_indDef := [indDef for formula_rect].
Canonical formula_indType := IndType formula formula_indDef.

Definition formula_hasDecEq := [derive hasDecEq for formula].
HB.instance Definition _ := formula_hasDecEq.
Definition formula_hasChoice := [derive hasChoice for formula].
HB.instance Definition _ := formula_hasChoice.
Definition formula_isCountable := [derive isCountable for formula].
HB.instance Definition _ := formula_isCountable.

Notation "A ⇒ B" := (Imply A B) (right associativity, at level 99) : NJi_scope.
Notation P_ n := (Var n).
Notation "'P_ n" := (P_ n) : NJi_scope.

Fixpoint size_formula (A : formula) : nat :=
  match A with
  | Var _ => 1
  | A ⇒ B => size_formula A + size_formula B
  end.

Lemma size_formula_gt0 (A : formula) : size_formula A > 0.
Proof. by elim: A => [//|A A0 B B0]/=; rewrite addn_gt0 A0. Qed.
Hint Resolve size_formula_gt0 : core.

Fixpoint subst_formula (ρ : list formula) (f : formula) :=
  match f with
  | Var n => nth 'P_(n - size ρ) ρ n
  | f ⇒ f' => (subst_formula ρ f) ⇒ (subst_formula ρ f')
  end.

(************)
(* Sequents *)
(************)
Record sequent := Sequent {
  hypotheses : list formula;
  thesis : formula
}.
Bind Scope NJi_scope with sequent.

Scheme sequent_rect := Induction for sequent Sort Type.
Definition sequent_indDef := [indDef for sequent_rect].
Canonical sequent_indType := IndType sequent sequent_indDef.
Definition sequent_hasDecEq := [derive hasDecEq for sequent].
HB.instance Definition _ := sequent_hasDecEq.
Definition sequent_hasChoice := [derive hasChoice for sequent].
HB.instance Definition _ := sequent_hasChoice.
Definition sequent_isCountable := [derive isCountable for sequent].
HB.instance Definition _ := sequent_isCountable.

Coercion singlef (f : formula) := [:: f].
Notation "Γ ⊢ B" := (Sequent Γ B) (at level 100) : NJi_scope.
Notation "⊢ B" := (Sequent [::] B) (at level 100) : NJi_scope.

Definition map_sequent (f : formula -> formula) (s : sequent) :=
  Sequent (map f (hypotheses s)) (f (thesis s)).

Definition subst_sequent (ρ : list formula) (s : sequent) :=
  map_sequent (subst_formula ρ) s.

(*********)
(* Rules *)
(*********)

Record rule := Rule {
  premises : list sequent;
  conclusion : sequent
}.
Bind Scope NJi_scope with rule.

Scheme rule_rect := Induction for rule Sort Type.
Definition rule_indDef := [indDef for rule_rect].
Canonical rule_indType := IndType rule rule_indDef.
Definition rule_hasDecEq := [derive hasDecEq for rule].
HB.instance Definition _ := rule_hasDecEq.
Definition rule_hasChoice := [derive hasChoice for rule].
HB.instance Definition _ := rule_hasChoice.
Definition rule_isCountable := [derive isCountable for rule].
HB.instance Definition _ := rule_isCountable.

Coercion single_sequent (f : sequent) := [:: f].
Notation "p -------------- c" := (Rule p c)
  (format "'[v   ' '//' '[' p ']' '//' -------------- '//' '[' c ']' '//' ']'",
   at level 150) : NJi_scope.
Coercion JustConcl (s : sequent) : rule := Rule [::] s.

(********************************)
(* Derivations and derivability *)
(********************************)

Inductive derivation (prems : seq sequent) : sequent -> Type :=
| Prem s : s ∈ prems -> derivation s
| Ax Γ i A : tnth (in_tuple Γ) i = A -> derivation (Γ ⊢ A)
| ImplyI Γ A B : derivation (A :: Γ ⊢ B) -> derivation (Γ ⊢ A ⇒ B)
| ImplyE Γ A B (l : derivation (Γ ⊢ A)) (r : derivation (Γ ⊢ A ⇒ B)) :
                 derivation (Γ ⊢ B).

Arguments Ax {_ _}.

Derive Dependent Inversion derivationP
 with (forall prems s, derivation prems s) Sort Type.

Definition derivable (r : rule) := derivation (premises r) (conclusion r).
Notation provable x := (derivation [::] (⊢ x)).

(* casting from derivation ps c to derivable (Rule ps c) *)
Coercion derivable_of_derivation ps c (d : derivation ps c) :
   derivable (Rule ps c) := d.

Fixpoint depth_derivation prems s (d : derivation prems s) :=
  match d with
  | Prem s x => 0
  | Ax Γ i A x => 1
  | ImplyI Γ A B x => (depth_derivation x).+1
  | ImplyE Γ A B l r => (maxn (depth_derivation l) (depth_derivation r)).+1
  end.

Definition subst_derivation (ρ : list formula) prems (s : sequent)  :
   derivation prems s ->
   derivation (map (subst_sequent ρ) prems) (subst_sequent ρ s).
Proof.
elim=> //=; do ?by constructor.
- by move=> h ?; apply/Prem/map_f.
- move=> Γ i _ <- /=.
  apply: (Ax [ord i]); first by rewrite size_map.
  by move=> ? /=;  apply: tnth_in_tuple_map.
- by move=> Γ A B ? + ?; apply: ImplyE.
Defined.


Module Rule.

Definition Ax Γ i : rule := Γ ⊢ tnth (in_tuple Γ) i.
Definition ImplyI Γ A B := Rule (A :: Γ ⊢ B) (Γ ⊢ A ⇒ B).
Definition ImplyE Γ A B := Rule [:: Γ ⊢ A; Γ ⊢ A ⇒ B] (Γ ⊢ B).

End Rule.

Definition simp := (mem_head, in_cons, eqxx, orbT).

Lemma Ax_derivable Γ i : derivable (@Rule.Ax Γ i). Proof. exact: Ax. Qed.

Lemma ImplyI_derivable Γ A B : derivable (Rule.ImplyI Γ A B).
Proof. by apply: (@NJi.ImplyI _ _ A); apply: Prem; rewrite ?simp. Qed.

Lemma ImplyE_derivable Γ A B : derivable (Rule.ImplyE Γ A B).
Proof. by apply: (@NJi.ImplyE _ _ A); apply: Prem; rewrite ?simp. Qed.

(***********)
(* Helpers *)
(***********)

Ltac Prem := by apply: Prem => /=.
Ltac EAx := by apply: Ax => /=.
Ltac Ax i := by apply: (Ax [ord i]) => /=.
Ltac ImplyI := apply ImplyI => /=.
Ltac ImplyE A := apply (@ImplyE _ _ A) => /=.

Ltac Rev := do ?[Prem|EAx|ImplyI].

Lemma ImplyAx prems Γ A B k :
                tnth (in_tuple Γ) k = (A ⇒ B) ->
                derivation prems (Γ ⊢ A) ->
                derivation prems (Γ ⊢ B).
Proof. move=> eqAB /ImplyE; apply; rewrite -eqAB; EAx. Defined.
Ltac ImplyAx k :=
   (apply: (@ImplyAx _ _ _ _ [ord k]) => /=;
     do ?by []); rewrite /tnth/=.

End NJi.

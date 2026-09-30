From HB Require Import structures.
From Coq Require Import String.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From elpi.apps Require Import derive.std.
From deriving Require Import deriving.
From mathcomp Require Import zify lra ring.

From ND Require Import extra NJi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* starts here *)

Import NJi.

Notation Ty := formula.

Module Pre.

Inductive Tm :=
| Db of nat
| Lam of Tm
| App of Tm & Tm.

Check Lam (Db 0). (* ⊢ λ x. x *)
Check Lam (Db 1). (* y : A ⊢ λ x. y *)
Check Lam (Lam (Db 0)). (* ⊢ λ x y. y *)
Check Lam (Lam (Db 1)). (* ⊢ λ x y. x *)

Inductive tyof : seq Ty -> Tm -> Ty -> Type :=
| LAx Γ i A : tnth (in_tuple Γ) i = A -> tyof Γ (Db i) A
| LImplyI Γ A B M : tyof (A :: Γ) M B -> tyof Γ (Lam M) (A ⇒ B)
| LImplyE Γ A B M N (l : tyof Γ M A) (r : tyof Γ N (A ⇒ B)) :
                 tyof Γ (App N M) B.

Definition ty (Γ : seq Ty) (M : Tm) : option Ty.
Admitted.

End Pre.

(**md
# A ROCQ TUTORIAL
 
This is a single, self-contained literate Rocq file. The mathematics
lives in the comments; the code between them is real and is meant to be
stepped through interactively, one `.`-terminated command at a time,
inside an IDE (RocqIDE, VsCode or VsCodium with VsRocq/coq-lsp, emacs
with Proof General, vim with CoqTail...).

It assumes you are comfortable with ordinary mathematics but have never
used a proof assistant. We start from vocabulary, then explore tactics,
and close with two examples in topology.

The proofs are deliberately written one elementary step per line, even
when a shorter combined script exists: the goal is to see the state change
after every tactic, not to be concise.

What you need installed (via opam, in one switch):
- rocq-core 9.1.1            (the kernel + the SSReflect proof language)
- rocq-stdlib 9.0.0          (the Rocq "standard library")
- mathcomp                   (rocq-mathcomp-ssreflect, -algebra, -field)
- mathcomp-analysis          (rocq-mathcomp-analysis, -classical)
- mathcomp-algebra-tactics   (gives `ring`, `field`, `lra`, `nra`)
- mathcomp-zify / mczify     (makes `lia`/`nia` understand nat & int)
*)

(**md
# SECTION 1.  VOCABULARY: how to talk about proof assistant concepts.

Read this section before touching any code. We provide all the definitions
you need to make sense of the instructions.

## Terms, types, and propositions

Rocq is built on a typed lambda-calculus (the Calculus of Inductive
Constructions), and everything that makes sense is a *term*. Moreover,
- every term has a *type*, and
- every type is itself a term,
and we write `t : A` to mean that `t` has type `A`.

The sole purpose of Rocq's kernel is to check assertions of the form
`t : A`; this is a decidable problem.

### Examples of terms and types
- `42` is a term, its type is `nat`, i.e. `42 : nat`.
- `nat` is a term too, its type is `Type@{0}`, i.e. `nat : Type@{0}`.
- `Type@{i}` is a type too, its type is `Type@{i+1}`,
  i.e. `Type@{i} : Type@{i+1}`. We often omit the "level" `@{i}`, since Rocq
  usually infers it (use `Set Printing Universes` to display it), though it
  is slightly more subtle than just a "level". Elements of `Type` are types,
  and may themselves contain terms.
- `fun n : nat => 1 + n` is a term, a function of type `nat -> nat`,
  i.e. `(fun n => 1 + n) : nat -> nat`.
- `forall n : nat, n = n` is a term, a "proposition", of type `Prop`.

### Propositions
The type `Prop` of propositions is itself a term, of type `Type@{1}`; and a
proposition `P` (of type `Prop`) is also a type. A proposition holds if and
only if it is inhabited. For example, `forall n : nat, n = n` holds because
`fun n : nat => erefl n` has type `forall n : nat, n = n`.

### Examples of propositions
- `True` is a proposition (`True : Prop`); it has a single inhabitant `I`,
  i.e. `I : True`.
- if `P` and `Q` are propositions, `P -> Q` is a proposition whose
  inhabitants are functions from `P` to `Q`, i.e. functions consuming proofs
  of `P` and producing proofs of `Q`. So `P -> Q` holds when "`P` holds"
  implies "`Q` holds".
- if `P` and `Q` are propositions, `P /\ Q` and `P \/ Q` are propositions
  that hold respectively when both `P` and `Q` hold, and when `P` or `Q`
  holds.
- if `A` is a type and `P` has type `A -> Prop`, then `forall x : A, P x` is
  a proposition, which holds when `P t` holds for every `t` of type `A`.
- `False` is a proposition (`False : Prop`); "Rocq is consistent" means
  `False` has no inhabitant.
- `~ A` is a proposition, defined as `A -> False`. A proof of `~ A` turns any
  inhabitant of `A` into a proof of `False`, so `~ A` holds exactly when `A`
  has no inhabitant.

## Contexts

Some terms do not make sense by themselves: e.g. `n = n` cannot be
interpreted without knowing what `n` means. This is the purpose of contexts.
A context `Γ` is a list associating names (like `n`) to types (like `nat`);
we write `Γ ⊢ t : A` to mean "`t` has type `A` in context `Γ`".

### Examples of contexts
- the empty context `()` has no variable; we used it implicitly when we wrote
  `42 : nat` and `nat : Type`. A term that typechecks in the empty context is
  called *closed*.
- the context with one element `n : nat` lets us type the term `n = n`:
  indeed `(n : nat) ⊢ (n = n) : Prop` holds.
- if `Γ ⊢ A : Type` holds, one can extend `Γ` with a variable of type `A`,
  and `Γ, x : A` is a valid context such that `(Γ, x : A) ⊢ x : A` holds.

## Definitions, lemmas and goals

The main interaction loop of Rocq provides assistance to write definitions,
state lemmas, and prove them.

Declaring a definition `d` of type `A` consists in giving a name to a closed
term of type `A`.

Proving a lemma `P` consists in finding, interactively, a term `t` of type
`P`. Rocq proceeds by creating a *hole*, also called a *goal* or an
*existential variable* `?t`, and invites the user to fill it.

More generally the context might not be empty, and a "goal" is a problem of
the shape `Γ ⊢ ?t : Q`, which Rocq displays as:
```
Γ
=============
Q
```
telling you that, assuming `Γ`, you are invited to build a proof of `Q`.

For example:
```
  n : nat                       <-- the context (a.k.a. local context):
  m : nat                           a list of variables and hypotheses,
  eq_m_n : n = m                    i.e. names with their types.
  ============================  <-- the Rocq display for the turnstile
  m = n                         <-- the statement under the bar:
                                    the type we must inhabit now.
```
reads: "assuming natural numbers `m` and `n` and a proof `eq_m_n` that
`n = m`, provide a proof term for `m = n`", or: "fill `?t` such that
`n : nat, m : nat, eq_m_n : n = m ⊢ ?t : m = n` holds".

## Proof terms vs scripts

There are two ways to produce the proof term that the kernel will check.

### Proof term (mostly non-interactive)

Write the inhabitant directly, e.g.
`Definition trivial_proof : forall n : nat, n = n := fun n => erefl.`
This is exactly like defining a function. While it is the recommended way to
declare a *definition*, it is not best practice for *proofs*, since proof
terms often contain lots of inferable data in Rocq. (Other proof assistants,
like Agda, are tuned towards this interaction mode.)

### Proof scripts (interactive)

You enter "proof mode" with the command `Proof` and issue *tactics*:
instructions that transform the goal, each one building a piece of term
for you. You watch the state evolve; when no goals remain you type `Qed.`
and the kernel checks the assembled term.

This is the privileged way to do proofs in Rocq (and also in Lean
bu with a different syntax) as it allows a higher level of abstraction
over the notion of proof.

## Tactics

We sort tactics into five categories. (We use the SSReflect proof language,
the MathComp dialect, which has a uniform and consistent way to deal with
bookkeeping.)

### 1. Theorem use
- `apply`: backward reasoning with a known fact. If `thm : A -> B` and the
  goal is `B`, then `apply: thm` reduces the goal to `A`. This is modus
  ponens read backwards, the workhorse of structured proof. We use the
  SSReflect form `apply: thm`.
- `exact: thm` is `by apply: thm` that must close the goal.
- `apply/equiv` uses an equivalence `equiv` (stated as `<->` or `reflect`)
  from left to right, or if it fails, from right to left.
- `rewrite`: substitutes with equalities. If `e : a = b` then `rewrite e`
  turns every `a` in the goal into `b`; `rewrite -e` goes right-to-left.
  You can chain them, e.g., `rewrite e1 -e2`.

### 2. Goal management (bookkeeping)
Shuffle things across the bar and decompose them. These do no "real"
mathematics; they reorganise goals, preparing them for theorem use (see 1.).
- `move=> x`: introduce, i.e., pull the leading `forall`/`->` from the statement
  down into the context, naming it `x`.
- `move: x`: revert (generalise), i.e., push `x` from the context up into the
  statement. The `:` and `=>` are the two halves of "stack management":
  `tac: a b` feeds `a, b` to the tactic, and `tac=> p q` names what the
  tactic leaves on the goal.
- `case: x`: case analysis, i.e., split `x` into its constructors (e.g. a `nat`
  becomes the cases `0` and `n.+1`).
- `elim: x`: induction on `x` (ressembles case analysis but provides
  induction hypotheses in each case).
- `split`: prove a conjunction by proving both halves.
- `exists t`: provide a witness for an existential.
- `have h : P`: forward reasonning step:
  introduce and separately prove a lemma `P`, then keep it as `h`.
  ("It suffices..." is the dual, `suff`, and `wlog` emulates
  "without loss of generality" reasonning steps.)
- `set x := e`, gives a name to an expression occuring in the goal;
- `pose x := e`, gives a name to a brand new expression.

See:
https://www-sop.inria.fr/marelle/math-comp-tut-16/MathCompWS/cheatsheet.pdf

### 3. Automation by decision procedure
A tactic that runs a complete algorithm for a decidable class of goals: if
the goal is in the class and true, it will close it; if it is in the class
and false, it fails (and often says so). These are the "push-button"
tactics, and knowing their theoretical limit is of essence.

*Computation + reflection* (the MathComp signature move):
- `by []` / `done`: close goals that hold "by computation plus a little
  database": reflexivity, `true`, decidable `bool` facts that compute to
  `true`, etc. In MathComp a decidable predicate is a `bool`-valued function,
  and `reflect` lemmas (e.g. `eqP`, `andP`) bridge `bool` and `Prop`.
  Deciding such a fact is just *running* it.

*Arithmetic* (the micromega family; on nat/int via zify/mczify):
- `lia`: linear integer arithmetic (Presburger). Complete for linear goals
  over Z/nat/int: `+`, `-`, multiplication by a constant, `<=`, `<`, `=`,
  `/\`, `\/`, `->`, quantifier-free (plus some quantifiers).
- `lra`: linear real/ordered-field arithmetic. Complete for linear goals over
  ordered fields (`realFieldType`).
- `psatz n`: Positivstellensatz certificates up to degree `n`; prove
  polynomial *inequalities* when a certificate exists.

*Ring / field equations* (mathcomp-algebra-tactics):
- `ring`: decides equalities in any commutative ring/semiring (`comRingType`):
  refies, normalise, compare. Complete for the equational theory of
  commutative semirings.
- `field`: same for fields, reducing to `ring` plus side goals of the form
  "this denominator is nonzero".

*Propositional / equality-of-terms:*
- `tauto`: intuitionistic propositional tautologies (decidable).
- `intuition`: `tauto` on the propositional skeleton, leaving the atomic
  leaves to you (or another tactic).
- `btauto`: Boolean-ring tautologies over `bool`.
- `congruence`: congruence closure, i.e. decides ground equalities in the theory
  of equality with uninterpreted functions.

### 4. Generic automation (heuristic search, not decision procedures)
- `auto` / `eauto` / `trivial`: depth-bounded Prolog-style search over a
  database of "hints". They are incomplete and silent on failure.
- `nia`: nonlinear integer arithmetic. A heuristic, not complete.
- `nra`: nonlinear real arithmetic. A heuristic (products, squares).
- `firstorder`: proof SEARCH in first-order logic. FOL is undecidable, so this
  is incomplete: it may loop or give up.

### 5. Hammers & machine learning: tactic producing!
(external, heuristic, reconstruction of proof terms)
A "hammer" exports your goal to external automated theorem provers (E,
Vampire, Z3, CVC5), does premise selection over your whole library, and on
success reconstructs a Rocq proof that the kernel re-checks (so a buggy
prover cannot fool you).
- CoqHammer: `hammer` (the full pipeline), plus the standalone
  reconstruction/search tactics `sauto`, `hauto`, `qauto`, `best`.
- Tactician: `suggest` -- learns tactics from existing proofs.
- ML premise selection / neural provers (Graph2Tac, Proverbot, Tactician's
  models...) are research-grade.
- LLM...

This tutorial covers tactics of type 1, 2 and 3 from above.

That is the whole vocabulary (I hope). From here on, we do "mathematics".

From now on, read the explanations, and when you are ready:
erase the proofs and try to do them again.
You can also play with alternative ways you may have in mind
to prove statements.
*)


(*md
# SECTION 2.  Loading the library, and a first proof
*)

From mathcomp Require Import all_boot.

(*md
 `all_boot` gives us the SSReflect tactic language, `nat`, sequences,
 `bool`, the `bigop` notations, finite types, and so on. *)

(*md
The simplest possible goal. `Goal P.` opens an anonymous theorem with
statement `P`; `Proof.` enters script mode; we close with `Qed.`.
*)
Goal forall n : nat, n + 3 = n + 3.
Proof.
move=> n.   (* introduce the variable n *)
by [].      (* both sides are identical, true by reflexivity (computation) *)
Qed.

(*md
The same goal as a bare proof term, no tactics, to demystify `Qed.`: *)
Definition refl_proof : forall n : nat, n + 3 = n + 3 :=
  fun n => erefl.
(*md
 `erefl` is the proof of `x = x`. The script above built exactly this. *)


(*md
# SECTION 3.  Rewriting, applying, and the `=>` / `:` stack
*)

(*md Using a hypothesis by rewriting with it. One elementary step per line. *)
Goal forall n m : nat, n = 3 * m -> n + 1 = 3 * m + 1.
Proof.
move=> n m nE.   (* introduce n, m, and the hypothesis nE : n = 3 * m *)
rewrite -nE.      (* replace n by 3 * m in the goal *)
by [].           (* both sides are now identical *)
Qed.

(*md `rewrite` can fire backwards (`-nE`); here we just use two equations, one
   rewrite per line. *)
Goal forall n m : nat, n = 2 * m -> m = 6 -> (n - 5) * m = 42.
Proof.
move=> n m nE mE.
rewrite nE.      (* use n = 2 * m *)
rewrite mE.      (* use m = 6 *)
by [].           (* the goal is now a closed arithmetic identity *)
Qed.

(*md
## Backward reasoning with `apply`

`apply` is backward reasoning: if a lemma's conclusion matches the current
goal `B`, applying it replaces `B` by the lemma's remaining premises. Three
forms are worth distinguishing.

- `apply: thm` is the SSReflect form (note the colon). It feeds `thm` to the
  tactic: SSReflect unifies the conclusion of `thm` with the goal and leaves
  one subgoal per remaining premise. This is the form we use everywhere.
- `apply: thm a b` supplies some of `thm`'s arguments explicitly (`a`, `b`)
  and lets unification fill in the rest. Equivalently, build the partial
  application yourself and pass it in parentheses: `apply: (thm a b)`.
- `apply thm` (no colon) is the vanilla Rocq tactic. On simple goals it does
  the same thing, but it differs in detail: its unification is less
  predictable on dependent or higher-order goals, unresolved premises may
  become shelved existential variables, and the resulting subgoal order can
  differ. In MathComp code we consistently prefer `apply:`.
- `apply/equiv` uses an equivalence `equiv` (stated as `<->` or `reflect`)
  from left to right, or if it fails, from right to left.

`exact: thm` is an `apply: thm` that is required to finish the goal outright,
with no premise left over.
*)

(* (A -> B -> C) <-> (A /\ B -> C) *)

Goal forall n m : nat, n <= m -> n <= m + 1.
Proof.
move=> n m nm.
have h := @leq_trans m.
apply: h.
  by [].
by apply: leq_addr.
(* Search (_ <= _ + _). *)
(* apply: (@leq_trans m). *)
(* (* `leq_trans : m <= n -> n <= p -> m <= p`. We hand the first premise `nm` to *)
(*    `apply:` up front, and let unification match the conclusion with the goal: *) *)
(* apply: (leq_trans nm). *)
(* (* exactly one premise is left: `m <= m + 1` *) *)
(* exact: leq_addr.   (* `leq_addr : m <= m + n`, here with n := 1 *) *)
Qed.

(*md
 Discoverability. You will not memorise the library. `Search` finds lemmas
   by name fragment and/or by a pattern with holes `_`. For instance:
       Search (_ + _) (_ <= _).
       Search "addn" "C".     (* names containing addn and C: addnC, ... *)
   `Locate "+".` to find the name of the definition behind `+ `.
   `About leq_trans.` prints a lemma's statement; `Print` unfolds a
   definition. *)

(*md
 We load `zify`, the bridge that lets `lia`/`nia` 
 read MathComp's `nat` and `int`. *)
From mathcomp Require Import zify.

(*md
# SECTION 4.  Arithmetic: decision procedure vs hand proof
*)

Lemma my_first_lia : forall n m : nat, n <= m -> n <= m + 1.
Proof. lia. Qed.


(*md
   Push-button. A linear nat goal that `lia` decides instantly. By hand this
   needs commutativity, associativity and cancellation lemmas; `lia` just
   settles it. *)
Lemma lia_linear (a b c : nat) : a + b + c = c + (b + a).
Proof. lia. Qed.

(*md
   The same statement done structurally, to see what `lia` spared us. We pick
   the exact subterm to rewrite with an occurrence pattern in [ ... ], one
   step at a time. *)
Lemma byhand_linear (a b c : nat) : a + b + c = c + (b + a).
Proof. by rewrite [b + a]addnC [c + _]addnC. Time Qed.

(*md
   Truncated subtraction on `nat` is a classic `lia` win:
  it knows `n - m = 0` when `m >= n`, did you know?
  By hand this is fiddly; `lia` does not care. *)
Lemma lia_sub (n : nat) : 2 * n - n = n.
Proof. lia. Qed.

(*md
   Out of scope for `lia`: a nonlinear identity (a product of variables).
   `lia` is linear and will refuse it. *)
Lemma square_of_sum_nat (a b : nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2.
Proof.
nia.   (* nonlinear, heuristic --  by chance it happens to handle this one *)
Qed.

(*md
   But the *right* tool for a ring identity is `ring`; see section 6.
   And note where even `nia` and `ring` gives up:
   reasonning with inductive types, arbitrary recursive functions, and with
   big operators (e.g., a sum over `0..n`) is beyond every arithmetic
   decision procedure, because it is not first-order arithmetic at all.
   We prove such goals by induction in Section 5 and 7. *)

(*md
# SECTION 5. Manoeuvering towards decision procedures.
 
We leave the reach of `lia`/`nia`/`ring`, as soon as we slightly step outside
arithmetic: quantify over a data structure, or use a higher-order recursion
combinator. Arithmetic solvers do not recognize a goal shape they don't know,
and give up on the statement, yet after an induction and a few rewriting steps
one can work towards getting leaf subgoals falling back into its scope.
*)

(*md
  `iter n f x` applies `f` to `x` exactly `n` times. It is a higher-order
   recursor, opaque to every arithmetic solver, so the statement below is out
   of their reach -- even though it just says "add one, n times, gives n". *)
Lemma iter_succn (n : nat) : iter n succn 0 = n.
Proof.
Fail lia.            (* the whole goal: lia cannot see through iter *)
elim: n.
- (* base case: iter 0 succn 0 reduces to 0 *)
  by [].
- (* step case *)
  move=> n IHn.
  rewrite iterS.     (* iter n.+1 succn 0 = succn (iter n succn 0) *)
  by lia.            (* with IHn in context, this linear leaf is back in scope *)
Qed.

(* A genuinely structural fact about sequences (lists), by induction on the
   first list. No decision procedure decides facts about `seq`. *)
Lemma my_size_cat (T : Type) (s1 s2 : seq T) :
  size (s1 ++ s2) = size s1 + size s2.
Proof.
elim: s1.
- (* base case: s1 = [::] *)
  by [].
- (* step case: s1 = x :: s1 *)
  move=> x s1 IH.
  simpl.             (* reduce the cons (++ and size) on both sides *)
  by lia.            (* remove it and lia won' work! *)
Qed.


(*md
# SECTION 6.  Algebra: `ring`, `field`, `lra` vs structural algebra
*)

From mathcomp Require Import all_algebra.
From mathcomp Require Import ring lra.   (* algebra-tactics: ring/field/lra *)
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(*md
   In `ring_scope`, `x ^+ n` is a power and `x *+ n` is the n-fold sum
   `x + ... + x`; the laws are those of the abstract algebraic hierarchy: a
   `comRingType` is any commutative ring, a `fieldType` any field, etc. *)

Section AlgebraTactics.
Variable R : comPzRingType.   (* an arbitrary commutative ring *)
Variables x y : R.

(*md
   Push-button. The binomial identity, in every commutative ring at once.
   `ring` is a genuine decision procedure for commutative-ring equalities. *)
Lemma ring_binom : (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Proof. ring. Qed.

(*md
   A polynomial identity that would be painful by rewriting; `ring` solves it. *)
Lemma ring_cube : (x - y) * (x ^+ 2 + x * y + y ^+ 2) = x ^+ 3 - y ^+ 3.
Proof. ring. Qed.
End AlgebraTactics.

Section FieldTactic.
Variable F : fieldType.
Variable x : F.

(*mf
   `field` is `ring` for fields: it clears denominators and leaves you the
   side conditions "denominator != 0", which you discharge. *)
Lemma field_inv : x != 0 -> x / x = 1.
Proof.
move=> xn0.
field.       (* reduces to the nonzero side condition... *)
exact: xn0.  (* ...which is our hypothesis. *)
Qed.
End FieldTactic.

Section RealArithmetic.
Variable R : realFieldType.   (* an ordered field, e.g. the reals *)
Variables x y : R.

(* Push-button. Linear ordered-field reasoning is decided by `lra`. *)
Lemma lra_linear : x <= 1 -> y <= 1 -> x + y <= 2.
Proof. lra. Qed.

(*md
   A nonlinear inequality. `lra` is linear and refuses it, but
   `nra` (nonlinear, heuristic) finds the sum-of-squares certificate. *)
Lemma by_hand_amqm : 0 <= (x - y) ^+ 2.
Proof. by rewrite sqr_ge0. Qed.

End RealArithmetic.

(*md
# SECTION 7.  Big operators: induction beyond every decision procedure

MathComp's `\sum`, `\prod`, and more generally `\big` are iterated operators.
Arithmetic decision procedure are helpless at first sight.
*)

(*md
 Linearity of a finite sum: split a sum of sums. One library lemma. *)
Lemma sum_split (R : ringType) (n : nat) (a b : 'I_n -> R) :
  \sum_(i < n) (a i + b i) = \sum_(i < n) a i + \sum_(i < n) b i.
Proof. by rewrite big_split. Qed.

(*md
 A big-operator identity by induction on the range. `lia` cannot do this:
   the `\sum` is an unbounded fold, not Presburger arithmetic. We take out the
   last summand with `big_ord_recr`, use the induction hypothesis, then let
   `lia` close the purely arithmetic goals.*)
Lemma sum_ones (n : nat) : \sum_(i < n) 1 = n.
Proof.
Fail lia.                  (* the whole goal: lia cannot see through \sum *)
elim: n.
- (* base case: the empty sum *)
  rewrite big_ord0.        (* \sum_(i < 0) 1 = 0 *)
  by [].
- (* step case *)
  move=> n IHn.
  rewrite big_ord_recr /=.    (* \sum_(i < n.+1) 1 = \sum_(i < n) 1 + 1 *)
  rewrite IHn.             (* use the induction hypothesis: = n + 1 *)
  by lia.                  (* n + 1 = n.+1 *)
Qed.

(*md
   Gauss's sum, the school identity, by induction on the range.
   We embed natural numbers (`nat`) into rationals (`rat`) with n%:R.
   it is a notation for `1 *+ n` which means `1 + ... + 1`.
  Arithmetic solvers `lia` / `lra` / `ring` / `field` cannot do this,
  but we can reduce the proof to goals they can solve.
*)
Lemma gauss_double (n : nat) :
  \sum_(i < n) i%:R = n%:R * (n%:R - 1) / 2 :> rat.
Proof.
Admitted. (* Prove me and replace this by Qed. *)


(*md
# SECTION 8.  self-contained mini-theorems (combining everything)
*)
Local Open Scope nat_scope.

(* Every prime > 2 is odd. We combine a forward step, case analysis, a
   structural number-theory lemma, and computation on the leaf. *)
Lemma prime_gt2_odd p : prime p -> 2 < p -> odd p.
Proof.
Admitted. (* Prove me and replace this by Qed *)

(* A genuinely interesting numeric leaf, to show that inside analysis the
   right decision procedure still does the heavy lifting.

   Convexity of the square function: the square of a convex combination is at
   most the convex combination of the squares.

   The goal is genuinely nonlinear (it multiplies the variables), so the
   linear solver `lra` is helpless. *)

Section Convexity.
Local Open Scope ring_scope.
Variable R : realDomainType.

Lemma convex_sqr (x y t : R) :
  0 <= t -> t <= 1 ->
  (t * x + (1 - t) * y) ^+ 2 <= t * x ^+ 2 + (1 - t) * y ^+ 2.
Proof.
Fail lra.   (* linear arithmetic cannot: the inequality is genuinely nonlinear *)
move=> t_gt0 t_le1.
rewrite -subr_ge0.
set leRHS := (X in 0 <= X).
have -> : leRHS = t * (1 - t) * (x - y) ^+ 2 by rewrite /leRHS; ring.
by rewrite ?(sqr_ge0, mulr_ge0) ?subr_ge0.
Qed.

End Convexity.



(*md
# SECTION 9.  Topology (mathcomp-analysis)

mathcomp-analysis builds point-set topology on filters. A topological space
carries `open`, `closed`, a neighbourhood filter `nbhs`, and convergence
`F --> x`. Sets use classical set notation (some operators are
backtick-delimited):
```
    setT        full set            set0        empty set
    A `&` B     intersection        A `|` B     union
    f @^-1` A   preimage            `]a, b[`    open interval
```
Run`Search` to locate lemmas and browe the library documentation at:
- https://math-comp.github.io/htmldoc_2_5_0/index.html
- https://math-comp.github.io/analysis/htmldoc/1_16_0/index.html
*)

From mathcomp Require Import classical_sets topology normedtype.
Local Open Scope classical_set_scope.

Section TopologyWarmup.
Variable T : topologicalType.

(*md
   The whole space and the empty set are open. These are part of the
   structure, exposed as named lemmas. `Search open.` lists the toolkit. *)
Lemma openT_demo : open (setT : set T).
Proof. exact: openT. Qed.

Lemma open0_demo : open (set0 : set T).
Proof. exact: open0. Qed.

(*md
Finite intersections of opens are open. `openI` takes two opens.
*)
Lemma openI_demo (A B : set T) : open A -> open B -> open (A `&` B).
Proof. exact: openI. Qed.

(* The complement of an open is closed:
   Search closed open (~` _). *)
Lemma open_closedC_demo (A : set T) : open A -> closed (~` A).
Proof. exact: open_closedC. Qed.
End TopologyWarmup.

Section Continuity.
Variables (T U : topologicalType).

(*md
   Continuity via preimages. `continuous f` is defined pointwise through
   filters; `continuousP` is the classical bridge: `f` is continuous iff the
   preimage of every open is open. We prove the standard corollary that a
   continuous preimage of an open is open, one step at a time.
   Search (continuous _) open "P". *)
Lemma preimage_open_of_continuous (f : T -> U) (A : set U) :
  continuous f -> open A -> open (f @^-1` A).
Proof.
move=> cf.
apply continuousP.
by [].
Qed.

(*md
   Composition of continuous maps is continuous. We reason at a point `x` and
   feed the two pointwise continuities to the composition lemma.
   Search continuous comp. *)
Lemma continuous_comp_demo (V : topologicalType)
    (f : T -> U) (g : U -> V) :
  continuous f -> continuous g -> continuous (g \o f).
Proof.
move=> cf cg x.
exact: continuous_comp (cf x) (cg (f x)).
Qed.
End Continuity.



(*md
## Where to go next

- The Mathematical Components book (Assia Mahboubi & Enrico Tassi) is the canonical
  reference for the proof style used throughout.

- The MathComp School lessons & exercises (`lesson1.v` ... `lesson8.v`):
  ssreflect, arithmetic, finite types, big operators, algebra, polynomials,
  matrices, and reflection-based automation.
  https://mathcomp-schools.gitlabpages.inria.fr/2022-12-school/school

- For analysis, the mathcomp-analysis documentation and its `theories/` files.

- Reflexes worth building: `Search` before you reprove anything, read a lemma
  with `About`. `rewrite /def` to generally not a good idea, use lemmas!
  Use `lia`/`ring`/`lra` on every arithmetic/algebraic leaf.
*)

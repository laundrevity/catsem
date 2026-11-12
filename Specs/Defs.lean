import Mathlib.Order.Heyting.Basic
import Mathlib.Order.GaloisConnection.Basic

namespace CatSem

/-- Given a current abstract state `a` and a target optimization invariant `b`
    in a Heyting domain, synthesize the weakest guard `g` such that `a ⊓ g ≤ b`. -/
def synthesizeGuard {α : Type*} [HeytingAlgebra α] (a b : α) : α :=
  a ⇨ b

-- Sanity checks on Prop Heyting structure
example : ¬ synthesizeGuard True False := by simp [synthesizeGuard]
example : synthesizeGuard False False := by simp [synthesizeGuard]

/-- A Kripke-Joyal CFG presheaf/transfer structure representing a basic-block transition `u → v`,
    equipped with a pullback transfer map `pullback : β → α` (weakest precondition) and a
    forward existential postcondition map `post : α → β` (strongest postcondition) linked by
    `GaloisConnection post pullback`. -/
structure CFGTransfer (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] where
  pullback : β → α
  post : α → β
  gc : GaloisConnection post pullback

/-- Backward guard synthesis across an edge `T : CFGTransfer α β`:
    synthesizes the weakest local guard at source block `u` establishing `b` at target block `v`. -/
def synthesizeEdgeGuard {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (a : α) (b : β) : α :=
  synthesizeGuard a (T.pullback b)

/-- Identity CFG transfer on a block `α`. -/
def CFGTransfer.id (α : Type*) [HeytingAlgebra α] : CFGTransfer α α where
  pullback := _root_.id
  post := _root_.id
  gc := fun _ _ => Iff.rfl

/-- Sequential composition of CFG transfers `u → v` (`T₁`) and `v → w` (`T₂`). -/
def CFGTransfer.comp {α β γ : Type*} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]
    (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ) : CFGTransfer α γ where
  pullback := T₁.pullback ∘ T₂.pullback
  post := T₂.post ∘ T₁.post
  gc := T₁.gc.compose T₂.gc

-- Sanity checks on identity and composed CFG transfers over Prop
example : ¬ synthesizeEdgeGuard (CFGTransfer.id Prop) True False := by
  simp [synthesizeEdgeGuard, CFGTransfer.id, synthesizeGuard]

example : synthesizeEdgeGuard (CFGTransfer.id Prop) False False := by
  simp [synthesizeEdgeGuard, CFGTransfer.id, synthesizeGuard]

example :
    synthesizeEdgeGuard ((CFGTransfer.id Prop).comp (CFGTransfer.id Prop)) False False := by
  simp [synthesizeEdgeGuard, CFGTransfer.comp, CFGTransfer.id, synthesizeGuard]

/-- A predicate `inv` is a forward loop invariant for a self-transfer `L : CFGTransfer α α`
    when its forward postcondition implies `inv`. -/
def IsLoopInvariant {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) (inv : α) : Prop :=
  L.post inv ≤ inv

/-- Abductive loop-step guard synthesis: synthesizes the weakest local guard on the loop header
    such that conjoining `inv` with the guard re-establishes `inv` across `L`. -/
def synthesizeLoopStepGuard {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) (inv : α) : α :=
  synthesizeEdgeGuard L inv inv

-- Sanity checks on loop invariance and abductive loop-step guard over Prop
example : IsLoopInvariant (CFGTransfer.id Prop) True := by
  simp [IsLoopInvariant, CFGTransfer.id]

example : synthesizeLoopStepGuard (CFGTransfer.id Prop) True := by
  simp [synthesizeLoopStepGuard, synthesizeEdgeGuard, CFGTransfer.id, synthesizeGuard]

/-- An invariant `inv` is an inductive witness for a target property `target` under loop `L`
    if `inv` is a loop invariant for `L` and implies `target`. -/
def IsInductiveFor {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) (inv target : α) : Prop :=
  IsLoopInvariant L inv ∧ inv ≤ target

/-- Hoisted preheader guard synthesis across loop entry edge `E : CFGTransfer α β`:
    synthesizes the weakest guard at the preheader `a₀` that establishes loop invariant `inv`
    upon entering the loop header. -/
def hoistLoopGuard {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (a₀ : α) (inv : β) : α :=
  synthesizeEdgeGuard E a₀ inv

-- Sanity checks on inductive witnesses and hoisted preheader guards over Prop
example : IsInductiveFor (CFGTransfer.id Prop) False True := by
  simp [IsInductiveFor, IsLoopInvariant, CFGTransfer.id]

example : ¬ hoistLoopGuard (CFGTransfer.id Prop) True False := by
  simp [hoistLoopGuard, synthesizeEdgeGuard, CFGTransfer.id, synthesizeGuard]

/-- `n`-fold loop iteration of a self-transfer `L : CFGTransfer α α`. -/
def CFGTransfer.iterate {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) :
    ℕ → CFGTransfer α α
  | 0 => CFGTransfer.id α
  | n + 1 => (CFGTransfer.iterate L n).comp L

-- Sanity checks on n-fold loop iteration over Prop
example : ((CFGTransfer.id Prop).iterate 0).post True := by
  simp [CFGTransfer.iterate, CFGTransfer.id]

example : ¬ synthesizeEdgeGuard ((CFGTransfer.id Prop).iterate 2) True False := by
    simp [CFGTransfer.iterate, CFGTransfer.comp, CFGTransfer.id, synthesizeEdgeGuard, synthesizeGuard]

/-- Kripke-Joyal forcing relation at a CFG stage `stage : α`:
    `stage` forces `prop` (`stage ⊩ prop`) when `stage ≤ prop` in the Heyting fiber. -/
def Forces {α : Type*} [HeytingAlgebra α] (stage prop : α) : Prop :=
  stage ≤ prop

/-- Kripke-Joyal forcing across a CFG morphism `T : CFGTransfer α β`:
    `stage` forces `prop` after `T` when the forward existential postcondition `T.post stage` forces `prop`. -/
def ForcesAfter {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (stage : α) (prop : β) : Prop :=
  Forces (T.post stage) prop

-- Sanity checks on Kripke-Joyal forcing over Prop
example : Forces False True := by
  simp [Forces]

example : ForcesAfter (CFGTransfer.id Prop) True True := by
  simp [ForcesAfter, Forces, CFGTransfer.id]

/-- Stage-guarded conditional equivalence for compiler IR terms `Term` interpreted over a
    semantic domain `Val` indexed by Heyting stages `α`: `t₁` and `t₂` evaluate identically
    at every stage `s` that Kripke-Joyal forces `p`. -/
def GuardedEquiv {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p : α) (t₁ t₂ : Term) : Prop :=
  ∀ s : α, Forces s p → eval s t₁ = eval s t₂

-- Sanity checks on stage-guarded conditional equivalence over Prop
example (eval : Prop → ℕ → ℕ) (t : ℕ) : GuardedEquiv eval True t t := by
  intro _ _
  rfl

example (eval : Prop → ℕ → ℕ) (t : ℕ) : GuardedEquiv eval False t t := by
  intro _ _
  rfl

/-- Pullback of a stage-indexed semantic evaluator `evalβ : β → Term → Val` along a
    CFG transfer `T : CFGTransfer α β`. -/
def pullbackEval {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (evalβ : β → Term → Val) : α → Term → Val :=
  fun s t => evalβ (T.post s) t

-- Sanity checks on evaluator pullback over Prop
example (eval : Prop → ℕ → ℕ) (s : Prop) (t : ℕ) :
    pullbackEval (CFGTransfer.id Prop) eval s t = eval s t := by
  rfl

/-- Denotational compositionality (semantic compatibility) for a binary IR constructor
    `op : Term → Term → Term` and a stage-indexed semantic combiner
    `semOp : α → Val → Val → Val`. -/
def CompatibleOp2 {α Term Val : Type*}
    (eval : α → Term → Val) (op : Term → Term → Term) (semOp : α → Val → Val → Val) : Prop :=
  ∀ s t₁ t₂, eval s (op t₁ t₂) = semOp s (eval s t₁) (eval s t₂)

-- Sanity checks on denotational compositionality
example : CompatibleOp2 (fun (_ : Prop) (n : ℕ) => n) (· + ·) (fun _ x y => x + y) := by
  intro _ _ _
  rfl

/-- Concrete instantiation of `CFGTransfer` for a state transition `step : S₁ → S₂`
    over Heyting state-predicate fibers `S → Prop`, with constructive Galois connection
    between existential image (`post`) and weakest-precondition substitution (`pullback`). -/
def stateTransfer {S₁ S₂ : Type*} (step : S₁ → S₂) : CFGTransfer (S₁ → Prop) (S₂ → Prop) where
  pullback := fun Q s₁ => Q (step s₁)
  post := fun P s₂ => ∃ s₁, step s₁ = s₂ ∧ P s₁
  gc := fun _ _ =>
    ⟨fun h s₁ hp => h (step s₁) ⟨s₁, rfl, hp⟩,
     fun h _ ⟨s₁, hstep, hp⟩ => hstep ▸ h s₁ hp⟩

-- Sanity checks on concrete state-predicate CFG transfer
example : (stateTransfer (fun n : ℕ => n + 1)).pullback (fun n => n > 0) 0 := by
  simp [stateTransfer]

/-! ## Milestone 1: Trusted Computing Base (IR Syntax, Semantics, Bridges & Cost Observers) -/

/-- Variable identifier in the expression IR. -/
abbrev VarId := Nat

/-- Concrete runtime environment mapping variables to integers. -/
abbrev Env := VarId → Int

/-- Pure total arithmetic sub-expressions (safe to evaluate inside guards without traps or UB). -/
inductive PureExpr where
  | lit (n : Int)
  | var (v : VarId)
  | add (e₁ e₂ : PureExpr)
  | sub (e₁ e₂ : PureExpr)
  | mul (e₁ e₂ : PureExpr)
  deriving DecidableEq, Repr

/-- Total operational evaluator for pure expressions. -/
def evalPure (env : Env) : PureExpr → Int
  | .lit n => n
  | .var v => env v
  | .add e₁ e₂ => evalPure env e₁ + evalPure env e₂
  | .sub e₁ e₂ => evalPure env e₁ - evalPure env e₂
  | .mul e₁ e₂ => evalPure env e₁ * evalPure env e₂

/-- Executable Heyting guard IR predicates over `PureExpr`. -/
inductive GuardIR where
  | top
  | bot
  | nonZero (e : PureExpr)
  | eq (e₁ e₂ : PureExpr)
  | conj (g₁ g₂ : GuardIR)
  | imp (g₁ g₂ : GuardIR)
  deriving DecidableEq, Repr

/-- Boolean runtime evaluator for `GuardIR`. -/
def evalGuard (env : Env) : GuardIR → Bool
  | .top => true
  | .bot => false
  | .nonZero e => decide (evalPure env e ≠ 0)
  | .eq e₁ e₂ => decide (evalPure env e₁ = evalPure env e₂)
  | .conj g₁ g₂ => evalGuard env g₁ && evalGuard env g₂
  | .imp g₁ g₂ => (!evalGuard env g₁) || evalGuard env g₂

/-- Denotation of a `GuardIR` syntax tree into the concrete Heyting fiber `Env → Prop`. -/
def denoteGuard (g : GuardIR) : Env → Prop :=
  fun env => evalGuard env g = true

/-- Operational outcomes distinguishing normal values, safe checked-division traps, and unchecked UB. -/
inductive Outcome where
  | val (n : Int)
  | trap
  | ub
  deriving DecidableEq, Repr

/-- Left-to-right strict binary sequencing over `Outcome`. -/
def bindOutcome2 (f : Int → Int → Outcome) (o₁ o₂ : Outcome) : Outcome :=
  match o₁ with
  | .val n₁ =>
    match o₂ with
    | .val n₂ => f n₁ n₂
    | .trap => .trap
    | .ub => .ub
  | .trap => .trap
  | .ub => .ub

/-- Compiler expression IR with checked division, unchecked division, and runtime guard branches. -/
inductive Expr where
  | pure (p : PureExpr)
  | add (e₁ e₂ : Expr)
  | sub (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)
  | checkedDiv (num div : Expr)
  | uncheckedDiv (num div : Expr)
  | iteGuard (g : GuardIR) (thenBranch elseBranch : Expr)
  deriving DecidableEq, Repr

/-- Reference left-to-right operational evaluator for `Expr`.
    Matches the left operand outcome before evaluating the right operand so Lean host
    execution short-circuits on `.trap`/`.ub` identically to `execCheckCost`, while remaining
    extensionally equal to `bindOutcome2`. -/
def evalExpr (env : Env) : Expr → Outcome
  | .pure p => .val (evalPure env p)
  | .add e₁ e₂ =>
    match evalExpr env e₁ with
    | .val n₁ =>
      match evalExpr env e₂ with
      | .val n₂ => .val (n₁ + n₂)
      | .trap => .trap
      | .ub => .ub
    | .trap => .trap
    | .ub => .ub
  | .sub e₁ e₂ =>
    match evalExpr env e₁ with
    | .val n₁ =>
      match evalExpr env e₂ with
      | .val n₂ => .val (n₁ - n₂)
      | .trap => .trap
      | .ub => .ub
    | .trap => .trap
    | .ub => .ub
  | .mul e₁ e₂ =>
    match evalExpr env e₁ with
    | .val n₁ =>
      match evalExpr env e₂ with
      | .val n₂ => .val (n₁ * n₂)
      | .trap => .trap
      | .ub => .ub
    | .trap => .trap
    | .ub => .ub
  | .checkedDiv num div =>
    match evalExpr env num with
    | .val n =>
      match evalExpr env div with
      | .val d => if d = 0 then .trap else .val (n / d)
      | .trap => .trap
      | .ub => .ub
    | .trap => .trap
    | .ub => .ub
  | .uncheckedDiv num div =>
    match evalExpr env num with
    | .val n =>
      match evalExpr env div with
      | .val d => if d = 0 then .ub else .val (n / d)
      | .trap => .trap
      | .ub => .ub
    | .trap => .trap
    | .ub => .ub
  | .iteGuard g t f =>
    if evalGuard env g then evalExpr env t else evalExpr env f

/-- Constructive stage-to-machine-state lifting bridge from a concrete evaluator `run : S → Term → Out`
    to a stage-indexed relational denotation `(S → Prop) → Term → (S → Out → Prop)`. -/
def liftEval {S Term Out : Type*} (run : S → Term → Out) (stage : S → Prop) (t : Term) :
    S → Out → Prop :=
  fun s out => stage s ∧ run s t = out

/-- Relational semantic combiner for binary `Outcome` operations compatible with `liftEval`. -/
def liftBinarySem (f : Int → Int → Outcome) (_stage : Env → Prop)
    (v₁ v₂ : Env → Outcome → Prop) : Env → Outcome → Prop :=
  fun env out => ∃ o₁ o₂, v₁ env o₁ ∧ v₂ env o₂ ∧ bindOutcome2 f o₁ o₂ = out

/-- Static count of `.checkedDiv` AST nodes in an expression. -/
def checkedDivCount : Expr → Nat
  | .pure _ => 0
  | .add e₁ e₂ | .sub e₁ e₂ | .mul e₁ e₂ | .uncheckedDiv e₁ e₂ =>
    checkedDivCount e₁ + checkedDivCount e₂
  | .checkedDiv e₁ e₂ => 1 + checkedDivCount e₁ + checkedDivCount e₂
  | .iteGuard _ t f => checkedDivCount t + checkedDivCount f

/-- Static count of all division (`.checkedDiv` + `.uncheckedDiv`) AST nodes in an expression. -/
def divOpCount : Expr → Nat
  | .pure _ => 0
  | .add e₁ e₂ | .sub e₁ e₂ | .mul e₁ e₂ =>
    divOpCount e₁ + divOpCount e₂
  | .checkedDiv e₁ e₂ | .uncheckedDiv e₁ e₂ =>
    1 + divOpCount e₁ + divOpCount e₂
  | .iteGuard _ t f => divOpCount t + divOpCount f

/-- Static count of `.iteGuard` AST nodes in an expression. -/
def guardBranchCount : Expr → Nat
  | .pure _ => 0
  | .add e₁ e₂ | .sub e₁ e₂ | .mul e₁ e₂ | .checkedDiv e₁ e₂ | .uncheckedDiv e₁ e₂ =>
    guardBranchCount e₁ + guardBranchCount e₂
  | .iteGuard _ t f => 1 + guardBranchCount t + guardBranchCount f

/-- Dynamic short-circuiting cost of evaluating a `GuardIR` predicate in `env`. -/
def guardEvalCost (env : Env) : GuardIR → Nat
  | .top | .bot => 0
  | .nonZero _ | .eq _ _ => 1
  | .conj g₁ g₂ =>
    guardEvalCost env g₁ + (if evalGuard env g₁ then guardEvalCost env g₂ else 0)
  | .imp g₁ g₂ =>
    guardEvalCost env g₁ + (if evalGuard env g₁ then guardEvalCost env g₂ else 0)

/-- Dynamic cost of runtime safety checks executed during left-to-right evaluation of `Expr` in `env`.
    Models abstract object-IR guard and division-check evaluations (short-circuiting right-hand
    checks whenever the left operand traps or triggers UB). -/
def execCheckCost (env : Env) : Expr → Nat
  | .pure _ => 0
  | .add e₁ e₂ | .sub e₁ e₂ | .mul e₁ e₂ | .uncheckedDiv e₁ e₂ =>
    execCheckCost env e₁ +
      (match evalExpr env e₁ with
       | .val _ => execCheckCost env e₂
       | _ => 0)
  | .checkedDiv e₁ e₂ =>
    execCheckCost env e₁ +
      (match evalExpr env e₁ with
       | .val _ =>
         execCheckCost env e₂ +
           (if match evalExpr env e₂ with | .val _ => true | _ => false then 1 else 0)
       | _ => 0)
  | .iteGuard g t f =>
    guardEvalCost env g +
      (if evalGuard env g then execCheckCost env t else execCheckCost env f)

/-- Parametric guarded-cancellation expression `(x * d) / d` over arbitrary `PureExpr` operands. -/
def mkCancelExpr (x d : PureExpr) : Expr :=
  .checkedDiv (.mul (.pure x) (.pure d)) (.pure d)

/-- Parametric dual-division benchmark expression `(x / d) + ((y * d) / d)` over arbitrary `PureExpr` operands. -/
def mkDualDivExpr (x y d : PureExpr) : Expr :=
  .add (.checkedDiv (.pure x) (.pure d)) (.checkedDiv (.mul (.pure y) (.pure d)) (.pure d))

/-- Milestone 1 benchmark expression `(v₁ * v₀) / v₀` testing guarded algebraic cancellation. -/
def m1CancelExpr : Expr :=
  .checkedDiv (.mul (.pure (.var 1)) (.pure (.var 0))) (.pure (.var 0))

/-- Milestone 1 benchmark expression `(v₁ / v₀) + ((v₂ * v₀) / v₀)` testing redundant check elimination. -/
def m1BenchExpr : Expr :=
  .add
    (.checkedDiv (.pure (.var 1)) (.pure (.var 0)))
    (.checkedDiv (.mul (.pure (.var 2)) (.pure (.var 0))) (.pure (.var 0)))

-- Sanity checks on Milestone 1 TCB evaluators, parametric builders, and cost observers
example : m1CancelExpr = mkCancelExpr (.var 1) (.var 0) := rfl
example : m1BenchExpr = mkDualDivExpr (.var 1) (.var 2) (.var 0) := rfl
example (env : Env) (e₁ e₂ : Expr) :
    evalExpr env (.add e₁ e₂) =
      bindOutcome2 (fun x y => .val (x + y)) (evalExpr env e₁) (evalExpr env e₂) := rfl
example (env : Env) (num div : Expr) :
    evalExpr env (.checkedDiv num div) =
      bindOutcome2 (fun n d => if d = 0 then .trap else .val (n / d))
        (evalExpr env num) (evalExpr env div) := rfl
example : evalExpr (fun _ => 0) m1BenchExpr = .trap := rfl
example : evalExpr (fun v => if v = 0 then 2 else 6) m1CancelExpr = .val 6 := rfl
example : checkedDivCount m1BenchExpr = 2 := rfl
example : divOpCount m1CancelExpr = 1 := rfl
example : guardBranchCount m1BenchExpr = 0 := rfl
example : execCheckCost (fun _ => 2) m1BenchExpr = 2 := rfl

/-! ## Milestone 2: Trusted Computing Base (Imperative CFG Statements, Block Programs & Cost Observers) -/

/-- Functional environment update assigning `val` to variable `v` without `Classical.choice`. -/
def updateEnv (env : Env) (v : VarId) (val : Int) : Env :=
  fun w => if decide (w = v) then val else env w

/-- Structured imperative basic-block / diamond CFG statement syntax. -/
inductive Stmt where
  | skip
  | assign (v : VarId) (rhs : PureExpr)
  | seq (s₁ s₂ : Stmt)
  | ite (cond : GuardIR) (thenBr elseBr : Stmt)
  deriving DecidableEq, Repr

/-- Total concrete operational state transition for `Stmt`. -/
def execStmt : Stmt → Env → Env
  | .skip, env => env
  | .assign v rhs, env => updateEnv env v (evalPure env rhs)
  | .seq s₁ s₂, env => execStmt s₂ (execStmt s₁ env)
  | .ite cond thenBr elseBr, env =>
    if evalGuard env cond then execStmt thenBr env else execStmt elseBr env

/-- Imperative block program pairing a statement prefix `body` with a terminal expression `ret`. -/
structure BlockProg where
  body : Stmt
  ret : Expr
  deriving DecidableEq, Repr

/-- Operational outcome of executing `prog.body` from `env` and evaluating `prog.ret` in the resulting state. -/
def evalBlock (env : Env) (prog : BlockProg) : Outcome :=
  evalExpr (execStmt prog.body env) prog.ret

/-- Dynamic cost of runtime guard evaluations executed during `Stmt` in `env`. -/
def stmtGuardCost : Env → Stmt → Nat
  | _, .skip => 0
  | _, .assign _ _ => 0
  | env, .seq s₁ s₂ => stmtGuardCost env s₁ + stmtGuardCost (execStmt s₁ env) s₂
  | env, .ite cond s₁ s₂ =>
    guardEvalCost env cond + (if evalGuard env cond then stmtGuardCost env s₁ else stmtGuardCost env s₂)

/-- Total dynamic check cost (statement branch guards + terminal expression checks) of `BlockProg` in `env`. -/
def execBlockCheckCost (env : Env) (prog : BlockProg) : Nat :=
  stmtGuardCost env prog.body + execCheckCost (execStmt prog.body env) prog.ret

/-- Parametric sequential assignment/clobber benchmark block:
    `d := x; x := 0; return (num / divVar) + ((y * divVar) / divVar)`. -/
def mkClobberBlock (x d : VarId) (num y : PureExpr) (divVar : VarId) : BlockProg :=
  { body := .seq (.assign d (.var x)) (.assign x (.lit 0))
    ret := mkDualDivExpr num y (.var divVar) }

/-- Parametric diamond safe-divisor benchmark block:
    `if x == 0 then d := n else d := x; return (num / d) + ((y * d) / d)`. -/
def mkDiamondSafeBlock (x d : VarId) (n : Int) (num y : PureExpr) : BlockProg :=
  { body := .ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))
    ret := mkDualDivExpr num y (.var d) }

/-- Parametric dead-branch benchmark block:
    `if p != 0 then d := n else d := 0; return (y * d) / d`. -/
def mkDeadBranchBlock (p : PureExpr) (d : VarId) (n : Int) (y : PureExpr) : BlockProg :=
  { body := .ite (.nonZero p) (.assign d (.lit n)) (.assign d (.lit 0))
    ret := mkCancelExpr y (.var d) }

-- Sanity checks on Milestone 2 TCB statement transitions, block evaluators, and cost observers
example : updateEnv (fun _ => 3) 0 9 0 = 9 := rfl
example : updateEnv (fun _ => 3) 0 9 1 = 3 := rfl
example : evalBlock (fun v => if v = 0 then 2 else 6) (mkClobberBlock 0 1 (.lit 8) (.lit 5) 1) = .val 9 := rfl
example : evalBlock (fun v => if v = 0 then 2 else 6) (mkClobberBlock 0 1 (.lit 8) (.lit 5) 0) = .trap := rfl
example : evalBlock (fun _ => 0) (mkDiamondSafeBlock 0 1 2 (.lit 8) (.lit 5)) = .val 9 := rfl
example : execBlockCheckCost (fun _ => 0) (mkDiamondSafeBlock 0 1 2 (.lit 8) (.lit 5)) = 3 := rfl
example : evalBlock (fun _ => 1) (mkDeadBranchBlock (.var 0) 1 2 (.lit 7)) = .val 7 := rfl

end CatSem

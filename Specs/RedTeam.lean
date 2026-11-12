import Specs.Target
import Mathlib.Order.BooleanAlgebra.Basic
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Guard-synthesis specification audit

The target statements through Round 11 match their blueprint claims after unfolding
the synthesis definitions. The earlier mismatch between the weakest-guard
implication and the blueprint's iff has been resolved: the blueprint now
separates `synthesizeGuard_weakest` from `synthesizeGuard_adjunction`.
`blueprint_adjunction` checks the equivalence independently below.

The proof and compiler stubs in `Specs.Target` currently contain placeholders. None
of the proofs below invokes them: importing a placeholder must not turn an
audit into circular evidence. The Bool cases use kernel-checked `decide`;
the Prop proofs use conjunction and implication directly. The constructive
Bool instance below avoids the classical Boolean-to-Heyting adapter, and
the generic proofs avoid choice-dependent library shortcuts. Axiom inspection
must find neither `sorryAx` nor `Classical.choice` in any audit declaration.

Bool exhausts four state/target pairs and eight state/target/guard triples.
Prop checks arbitrary propositions, including all True/False combinations.
The explicit active witnesses show that the hypotheses are satisfiable with
a true state and a true guard. The rejected witnesses show that the validity
premise is meaningful and cannot simply be omitted.
-/

namespace CatSem.RedTeam

/-- The usual Bool order and implication, with a constructive adjunction proof.
This keeps all existing truth tables while avoiding the classical adapter. -/
local instance constructiveBool : HeytingAlgebra Bool :=
  HeytingAlgebra.ofHImp (fun a b => !a || b) (by decide)

/-- The full blueprint equivalence, proved without the target declarations. -/
theorem blueprint_adjunction {α : Type*} [HeytingAlgebra α] (a b g : α) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  exact le_himp_iff'.symm

/-- Exhaustive soundness check over all four Bool pairs. -/
theorem bool_sound (a b : Bool) : a ⊓ synthesizeGuard a b ≤ b := by
  cases a <;> cases b <;> decide

/-- Exhaustive weakest-guard check over all eight Bool triples. -/
theorem bool_weakest (a b g : Bool) (h : a ⊓ g ≤ b) :
    g ≤ synthesizeGuard a b := by
  revert h
  cases a <;> cases b <;> cases g <;> decide

/-- Check both directions of the separate adjunction target. -/
theorem bool_adjunction (a b g : Bool) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  cases a <;> cases b <;> cases g <;> decide

/-- Synthesis is not a constant guard: these are all four Bool outputs. -/
theorem bool_truth_table :
    synthesizeGuard false false = true ∧
    synthesizeGuard false true = true ∧
    synthesizeGuard true false = false ∧
    synthesizeGuard true true = true := by
  decide

/-- Every Bool state/target pair admits a valid guard. -/
theorem bool_valid_guard_exists (a b : Bool) : ∃ g : Bool, a ⊓ g ≤ b := by
  refine ⟨false, ?_⟩
  cases a <;> cases b <;> decide

/-- Both hypotheses and conclusions hold with an active state and guard. -/
theorem bool_active_witness :
    (true ⊓ true ≤ true) ∧
    (true ⊓ synthesizeGuard true true ≤ true) ∧
    (true ≤ synthesizeGuard true true) := by
  decide

/-- A false target forces a false guard when the state is true. -/
theorem bool_restrictive_witness :
    (true ⊓ false ≤ false) ∧ (false ≤ synthesizeGuard true false) := by
  decide

/-- A false state allows a true guard even for a false target. -/
theorem bool_false_state_witness :
    (false ⊓ true ≤ false) ∧ (true ≤ synthesizeGuard false false) := by
  decide

/-- Dropping validity would make weakest-guard optimality false. -/
theorem bool_rejected_guard :
    ¬ (true ⊓ true ≤ false) ∧ ¬ (true ≤ synthesizeGuard true false) := by
  decide

/-- Soundness for arbitrary propositions, using direct modus ponens. -/
theorem prop_sound (a b : Prop) : a ⊓ synthesizeGuard a b ≤ b := by
  change (a ∧ (a → b)) → b
  exact fun h => h.2 h.1

/-- Weakest-guard optimality for arbitrary propositions, using currying. -/
theorem prop_weakest (a b g : Prop) (h : a ⊓ g ≤ b) :
    g ≤ synthesizeGuard a b := by
  change g → a → b
  exact fun hg ha => h ⟨ha, hg⟩

/-- The full Prop adjunction is currying/uncurrying, with no classical cases. -/
theorem prop_adjunction (a b g : Prop) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  change ((a ∧ g) → b) ↔ (g → a → b)
  constructor
  · exact fun h hg ha => h ⟨ha, hg⟩
  · exact fun h hag => h hag.2 hag.1

/-- Every Prop state/target pair admits a valid guard. -/
theorem prop_valid_guard_exists (a b : Prop) : ∃ g : Prop, a ⊓ g ≤ b := by
  exact ⟨False, fun h => h.2.elim⟩

/-- Concrete non-vacuity with a true state, true guard, and true target. -/
theorem prop_active_witness :
    (True ⊓ True ≤ True) ∧
    (True ⊓ synthesizeGuard True True ≤ True) ∧
    (True ≤ synthesizeGuard True True) := by
  exact ⟨fun _ => True.intro, fun _ => True.intro, fun _ _ => True.intro⟩

/-- Concrete restrictive guard for a true state and false target. -/
theorem prop_restrictive_witness :
    (True ⊓ False ≤ False) ∧ (False ≤ synthesizeGuard True False) := by
  exact ⟨fun h => h.2, fun h _ => h⟩

/-- A false state makes the true guard valid even for a false target. -/
theorem prop_false_state_witness :
    (False ⊓ True ≤ False) ∧ (True ≤ synthesizeGuard False False) := by
  exact ⟨fun h => h.1, fun _ h => h⟩

/-- The same omitted-premise counterexample in Prop. -/
theorem prop_rejected_guard :
    ¬ (True ⊓ True ≤ False) ∧ ¬ (True ≤ synthesizeGuard True False) := by
  exact ⟨fun h => h ⟨True.intro, True.intro⟩,
    fun h => h True.intro True.intro⟩

/-!
## Round 2: CFG transfers

`CFGTransfer.gc` has the required orientation:
`T.post x ≤ b ↔ x ≤ T.pullback b`. Thus edge soundness and optimality follow
from this adjunction and the local Heyting adjunction. The branch theorem
requires both postconditions, so its synthesized guard is a meet. All three
CFG theorem statements match the corresponding blueprint nodes exactly.

Scope: this structure supplies an adjoint pair for a single edge. Round 3
adds identity and composition operations, checked below. It does not yet
encode a CFG, a presheaf, or Kripke-Joyal forcing semantics. The algebraic
blueprint claims need only the given transfer operations.

The four-element domain below is `Bool × Bool` with componentwise order.
Each transfer retains one coordinate in its postcondition and allows the
other coordinate freely in its pullback. Both maps are nonidentity and
nonconstant. Their Galois connections are checked by exhaustive cases.
The independent edge checks cover 32 soundness cases and 128 optimality
cases across the two transfers. The branch check covers all 256 quadruples.
-/

namespace Round2

/-- A finite Boolean algebra with two independent coordinates. -/
abbrev State := Bool × Bool

/-- `true` retains the first coordinate; `false` retains the second. -/
def keepCoordinate (first : Bool) : CFGTransfer State State where
  post x := if first then (x.1, false) else (false, x.2)
  pullback b := if first then (b.1, true) else (true, b.2)
  gc := by
    rintro ⟨x₁, x₂⟩ ⟨b₁, b₂⟩
    cases first <;> cases x₁ <;> cases x₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- Neither map in either concrete transfer is the identity. -/
theorem transfer_nonidentity (first : Bool) :
    (keepCoordinate first).post ≠ id ∧ (keepCoordinate first).pullback ≠ id := by
  constructor
  · intro h
    have hf := congrFun h (true, true)
    cases first <;> cases hf
  · intro h
    have hf := congrFun h (false, false)
    cases first <;> cases hf

/-- Neither map collapses the domain to a constant. -/
theorem transfer_nonconstant (first : Bool) :
    (keepCoordinate first).post (false, false) ≠
      (keepCoordinate first).post (true, true) ∧
    (keepCoordinate first).pullback (false, false) ≠
      (keepCoordinate first).pullback (true, true) := by
  cases first <;> decide

/-- The full edge equivalence follows directly from the two adjunctions. -/
theorem edge_adjunction {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (a : α) (b : β) (g : α) :
    T.post (a ⊓ g) ≤ b ↔ g ≤ synthesizeEdgeGuard T a b := by
  exact (T.gc _ _).trans (blueprint_adjunction a (T.pullback b) g)

/-- Independent proof of the branch blueprint, also allowing different codomains. -/
theorem branch_adjunction {α β₁ β₂ : Type*}
    [HeytingAlgebra α] [HeytingAlgebra β₁] [HeytingAlgebra β₂]
    (T₁ : CFGTransfer α β₁) (T₂ : CFGTransfer α β₂)
    (a : α) (b₁ : β₁) (b₂ : β₂) (g : α) :
    T₁.post (a ⊓ g) ≤ b₁ ∧ T₂.post (a ⊓ g) ≤ b₂ ↔
      g ≤ synthesizeEdgeGuard T₁ a b₁ ⊓ synthesizeEdgeGuard T₂ a b₂ := by
  rw [edge_adjunction, edge_adjunction, le_inf_iff]

/-- Exhaustive soundness on both nonidentity transfers. -/
theorem finite_edge_sound (first : Bool) (a b : State) :
    (keepCoordinate first).post (a ⊓ synthesizeEdgeGuard (keepCoordinate first) a b) ≤ b := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  cases first <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- Exhaustive optimality, including the triples where validity is false. -/
theorem finite_edge_weakest (first : Bool) (a b g : State)
    (h : (keepCoordinate first).post (a ⊓ g) ≤ b) :
    g ≤ synthesizeEdgeGuard (keepCoordinate first) a b := by
  revert h
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases first <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    cases g₁ <;> cases g₂ <;> decide

/-- All 256 state/target/target/guard quadruples for independent branches. -/
theorem finite_branch_iff (a b₁ b₂ g : State) :
    (keepCoordinate true).post (a ⊓ g) ≤ b₁ ∧
      (keepCoordinate false).post (a ⊓ g) ≤ b₂ ↔
    g ≤ synthesizeEdgeGuard (keepCoordinate true) a b₁ ⊓
      synthesizeEdgeGuard (keepCoordinate false) a b₂ := by
  rcases a with ⟨a₁, a₂⟩
  rcases b₁ with ⟨b₁₁, b₁₂⟩
  rcases b₂ with ⟨b₂₁, b₂₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁₁ <;> cases b₁₂ <;>
    cases b₂₁ <;> cases b₂₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- A compact truth table for every input to each edge synthesizer. -/
theorem edge_truth_table (first a₁ a₂ b₁ b₂ : Bool) :
    synthesizeEdgeGuard (keepCoordinate first) (a₁, a₂) (b₁, b₂) =
      if first then ((!a₁ || b₁), true) else (true, (!a₂ || b₂)) := by
  cases first <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- For the full source state, all four branch target combinations give the
corresponding pair of guard bits; neither branch may be discarded. -/
theorem branch_truth_table (b₁ b₂ : Bool) :
    synthesizeEdgeGuard (keepCoordinate true) (true, true) (b₁, false) ⊓
      synthesizeEdgeGuard (keepCoordinate false) (true, true) (false, b₂) =
      (b₁, b₂) := by
  cases b₁ <;> cases b₂ <;> decide

/-- An active source and guard produce a nonbottom postcondition. -/
theorem edge_active_witness :
    (keepCoordinate true).post ((true, true) ⊓ (true, false)) = (true, false) ∧
    (keepCoordinate true).post ((true, true) ⊓ (true, false)) ≤ (true, false) ∧
    (true, false) ≤ synthesizeEdgeGuard (keepCoordinate true) (true, true) (true, false) := by
  decide

/-- A false target admits a nonbottom guard, but rejects the unrestricted guard. -/
theorem edge_restrictive_witness :
    synthesizeEdgeGuard (keepCoordinate true) (true, true) (false, false) = (false, true) ∧
    (keepCoordinate true).post ((true, true) ⊓ (false, true)) ≤ (false, false) ∧
    ¬ ((keepCoordinate true).post ((true, true) ⊓ (true, true)) ≤ (false, false)) ∧
    ¬ ((true, true) ≤ synthesizeEdgeGuard (keepCoordinate true) (true, true) (false, false)) := by
  decide

/-- Both branch premises hold with a nonbottom guard, which equals their synthesis. -/
theorem branch_active_witness :
    (keepCoordinate true).post ((true, true) ⊓ (true, false)) ≤ (true, false) ∧
    (keepCoordinate false).post ((true, true) ⊓ (true, false)) ≤ (false, false) ∧
    synthesizeEdgeGuard (keepCoordinate true) (true, true) (true, false) ⊓
      synthesizeEdgeGuard (keepCoordinate false) (true, true) (false, false) = (true, false) := by
  decide

/-- Each branch can fail while the other succeeds: both conjuncts matter. -/
theorem branches_independent :
    (¬ ((keepCoordinate true).post ((true, true) ⊓ (true, false)) ≤ (false, false)) ∧
      (keepCoordinate false).post ((true, true) ⊓ (true, false)) ≤ (false, false)) ∧
    ((keepCoordinate true).post ((true, true) ⊓ (false, true)) ≤ (false, false) ∧
      ¬ ((keepCoordinate false).post ((true, true) ⊓ (false, true)) ≤ (false, false))) := by
  decide

end Round2

/-!
## Round 3: sequential paths and diamond joins

The four new theorem statements match the blueprint exactly. `CFGTransfer.id`
has identity maps. `T₁.comp T₂` runs `T₁` then `T₂` forward, and pulls targets
back through `T₂` then `T₁`. The composition guard equality is definitional:
its intermediate target is `T₂.pullback c`, with no intermediate state parameter.
Right adjoints preserve meets; both pullback and fixed-state guard synthesis
are right adjoints. Diamond joins use the join of post-states and the meet
of path guards. This is a merge of alternative paths, not a claim that the
paths commute or yield equal post-states.

The audit independently proves all four general claims and checks identity
and associativity laws. For finite tests, compose a coordinate swap with
`Round2.keepCoordinate true` in both orders. Both stages and both resulting
paths are nonidentity; the resulting maps are also nonconstant. An explicit
witness distinguishes the two orders on posts, pullbacks, and guards.
Exhaustive checks cover 32 pullback-meet cases, 32 guard-composition cases,
128 guard-meet cases, and 64 diamond cases. Positive and negative witnesses
also detect replacing the joined post-state by a meet or the guard meet by
a join. No proof invokes a placeholder target theorem.
-/

namespace Round3

open Round2

/-- Identity transfer synthesis is ordinary local synthesis. -/
theorem identity_guard {α : Type*} [HeytingAlgebra α] (a b : α) :
    synthesizeEdgeGuard (CFGTransfer.id α) a b = synthesizeGuard a b := by
  rfl

/-- The identity is neutral on the source side of composition. -/
theorem identity_left {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) : (CFGTransfer.id α).comp T = T := by
  cases T
  rfl

/-- The identity is neutral on the target side of composition. -/
theorem identity_right {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) : T.comp (CFGTransfer.id β) = T := by
  cases T
  rfl

/-- Sequential composition is associative, including the adjunction proof field. -/
theorem composition_assoc {α β γ δ : Type*}
    [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ] [HeytingAlgebra δ]
    (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ) (T₃ : CFGTransfer γ δ) :
    (T₁.comp T₂).comp T₃ = T₁.comp (T₂.comp T₃) := by
  rfl

/-- Independent check of the general pullback-meet blueprint. -/
theorem pullback_meet {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (b₁ b₂ : β) :
    T.pullback (b₁ ⊓ b₂) = T.pullback b₁ ⊓ T.pullback b₂ := by
  apply le_antisymm
  · exact le_inf (T.gc.monotone_u inf_le_left) (T.gc.monotone_u inf_le_right)
  · apply (T.gc _ _).mp
    exact le_inf ((T.gc _ _).mpr inf_le_left) ((T.gc _ _).mpr inf_le_right)

/-- Independent check of the general composition blueprint. -/
theorem edge_comp {α β γ : Type*}
    [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]
    (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ) (a : α) (c : γ) :
    synthesizeEdgeGuard (T₁.comp T₂) a c = synthesizeEdgeGuard T₁ a (T₂.pullback c) := by
  rfl

/-- Independent check of the general conjunctive-target blueprint. -/
theorem edge_meet {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (a : α) (b₁ b₂ : β) :
    synthesizeEdgeGuard T a (b₁ ⊓ b₂) =
      synthesizeEdgeGuard T a b₁ ⊓ synthesizeEdgeGuard T a b₂ := by
  unfold synthesizeEdgeGuard synthesizeGuard
  rw [pullback_meet, himp_inf_distrib]

/-- Independent check of the general diamond blueprint, without path equality. -/
theorem diamond_adjunction {α γ : Type*} [HeytingAlgebra α] [HeytingAlgebra γ]
    (P₁ P₂ : CFGTransfer α γ) (a : α) (c : γ) (g : α) :
    P₁.post (a ⊓ g) ⊔ P₂.post (a ⊓ g) ≤ c ↔
      g ≤ synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c := by
  exact sup_le_iff.trans (Round2.branch_adjunction P₁ P₂ a c c g)

/-- A nonidentity automorphism, adjoint to itself. -/
def swap : CFGTransfer State State where
  post x := (x.2, x.1)
  pullback b := (b.2, b.1)
  gc := by
    rintro ⟨x₁, x₂⟩ ⟨b₁, b₂⟩
    cases x₁ <;> cases x₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- Both stages are nonidentity; changing their order changes the path. -/
def path (swapFirst : Bool) : CFGTransfer State State :=
  if swapFirst then swap.comp (keepCoordinate true) else (keepCoordinate true).comp swap

/-- Neither map of either composed path is the identity. -/
theorem path_nonidentity (swapFirst : Bool) :
    (path swapFirst).post ≠ id ∧ (path swapFirst).pullback ≠ id := by
  constructor
  · intro h
    have hf := congrFun h (true, true)
    cases swapFirst <;> cases hf
  · intro h
    have hf := congrFun h (false, false)
    cases swapFirst <;> cases hf

/-- Neither composed map degenerates to a constant. -/
theorem path_nonconstant (swapFirst : Bool) :
    (path swapFirst).post (false, false) ≠ (path swapFirst).post (true, true) ∧
    (path swapFirst).pullback (false, false) ≠ (path swapFirst).pullback (true, true) := by
  cases swapFirst <;> decide

/-- Complete truth tables for forward and backward traversal of both paths. -/
theorem path_truth_table (swapFirst x₁ x₂ b₁ b₂ : Bool) :
    (path swapFirst).post (x₁, x₂) =
      (if swapFirst then (x₂, false) else (false, x₁)) ∧
    (path swapFirst).pullback (b₁, b₂) =
      (if swapFirst then (true, b₁) else (b₂, true)) := by
  cases swapFirst <;> cases x₁ <;> cases x₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- Reversing composition changes all three observable operations. -/
theorem composition_order_witness :
    (path true).post (true, false) ≠ (path false).post (true, false) ∧
    (path true).pullback (true, false) ≠ (path false).pullback (true, false) ∧
    synthesizeEdgeGuard (path true) (true, true) (true, false) ≠
      synthesizeEdgeGuard (path false) (true, true) (true, false) := by
  decide

/-- All 32 path/target/target combinations for pullback meet preservation. -/
theorem finite_pullback_meet (swapFirst : Bool) (b c : State) :
    (path swapFirst).pullback (b ⊓ c) =
      (path swapFirst).pullback b ⊓ (path swapFirst).pullback c := by
  rcases b with ⟨b₁, b₂⟩
  rcases c with ⟨c₁, c₂⟩
  cases swapFirst <;> cases b₁ <;> cases b₂ <;> cases c₁ <;> cases c₂ <;> decide

/-- All 32 path/state/target combinations, checked against the intermediate pullback. -/
theorem finite_edge_comp (swapFirst : Bool) (a c : State) :
    synthesizeEdgeGuard (path swapFirst) a c =
      if swapFirst then synthesizeEdgeGuard swap a ((keepCoordinate true).pullback c)
      else synthesizeEdgeGuard (keepCoordinate true) a (swap.pullback c) := by
  rcases a with ⟨a₁, a₂⟩
  rcases c with ⟨c₁, c₂⟩
  cases swapFirst <;> cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> decide

/-- All 128 path/state/target/target combinations for guard meet preservation. -/
theorem finite_edge_meet (swapFirst : Bool) (a b c : State) :
    synthesizeEdgeGuard (path swapFirst) a (b ⊓ c) =
      synthesizeEdgeGuard (path swapFirst) a b ⊓ synthesizeEdgeGuard (path swapFirst) a c := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  rcases c with ⟨c₁, c₂⟩
  cases swapFirst <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    cases c₁ <;> cases c₂ <;> decide

/-- All 64 state/target/guard combinations for the two composed diamond paths. -/
theorem finite_diamond_iff (a c g : State) :
    (path true).post (a ⊓ g) ⊔ (path false).post (a ⊓ g) ≤ c ↔
      g ≤ synthesizeEdgeGuard (path true) a c ⊓ synthesizeEdgeGuard (path false) a c := by
  rcases a with ⟨a₁, a₂⟩
  rcases c with ⟨c₁, c₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- Explicit Boolean formulas for both sides' computed states and guards. -/
theorem diamond_truth_table (a₁ a₂ c₁ c₂ g₁ g₂ : Bool) :
    (path true).post ((a₁, a₂) ⊓ (g₁, g₂)) ⊔
      (path false).post ((a₁, a₂) ⊓ (g₁, g₂)) = (a₂ && g₂, a₁ && g₁) ∧
    synthesizeEdgeGuard (path true) (a₁, a₂) (c₁, c₂) ⊓
      synthesizeEdgeGuard (path false) (a₁, a₂) (c₁, c₂) = (!a₁ || c₂, !a₂ || c₁) := by
  cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- An active source and nonbottom guard establish a proper, nonbottom join target. -/
theorem diamond_active_witness :
    (path true).post ((true, true) ⊓ (false, true)) ⊔
      (path false).post ((true, true) ⊓ (false, true)) = (true, false) ∧
    (false, true) ≤ synthesizeEdgeGuard (path true) (true, true) (true, false) ⊓
      synthesizeEdgeGuard (path false) (true, true) (true, false) := by
  decide

/-- Each path can violate the common target while the other path satisfies it. -/
theorem diamond_paths_independent :
    (¬ ((path true).post (false, true) ≤ (false, false)) ∧
      (path false).post (false, true) ≤ (false, false)) ∧
    ((path true).post (true, false) ≤ (false, false) ∧
      ¬ ((path false).post (true, false) ≤ (false, false))) := by
  decide

/-- The false target rejects the unrestricted guard. Swapping either lattice
operation would incorrectly accept this same case. -/
theorem diamond_operator_counterexamples :
    ¬ ((path true).post (true, true) ⊔ (path false).post (true, true) ≤ (false, false)) ∧
    ¬ ((true, true) ≤ synthesizeEdgeGuard (path true) (true, true) (false, false) ⊓
      synthesizeEdgeGuard (path false) (true, true) (false, false)) ∧
    ((path true).post (true, true) ⊓ (path false).post (true, true) ≤ (false, false)) ∧
    ((true, true) ≤ synthesizeEdgeGuard (path true) (true, true) (false, false) ⊔
      synthesizeEdgeGuard (path false) (true, true) (false, false)) := by
  decide

end Round3

/-!
## Round 4: loop preservation and one-step guards

Both definitions and all four new theorem statements match the blueprint.
`IsLoopInvariant L inv` is the preservation condition `L.post inv ≤ inv`;
the adjunction gives exactly `inv ≤ L.pullback inv`. The loop-step guard is
`inv ⇨ L.pullback inv`, which equals top exactly when preservation holds.
Soundness does not assume that the candidate is already invariant. Closure
under meet requires both candidates to be invariant and follows even from
monotonicity of `post`; it does not require `post` to preserve meets.

Scope: preservation alone does not establish an initial state, termination,
or Kripke-Joyal forcing semantics. One-step soundness restores `inv`, not
necessarily `inv ⊓ guard`. The cycle counterexample below shows that an
initial guard check alone need not keep later unguarded iterations in `inv`.

The two nonidentity, nonconstant loops use the eight-element algebra Bool³.
The growth loop has post `(x, x || y, z)` and pullback `(x && y, y, z)`.
The cycle loop has post `(z, x, y)` and inverse pullback `(y, z, x)`.
Each of the first three targets is checked on all 16 loop/candidate choices;
meet closure is checked on all 128 loop/candidate/candidate choices. The
explicit meet witness uses distinct proper invariants with a nonbottom meet.
All proofs are independent of the target placeholders.
-/

namespace Round4

/-- Independent proof of forward/backward loop stability. -/
theorem invariant_pullback {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) :
    IsLoopInvariant L inv ↔ inv ≤ L.pullback inv := by
  exact L.gc inv inv

/-- Independent proof of the unrestricted-guard characterization. -/
theorem invariant_guard_top {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) :
    IsLoopInvariant L inv ↔ synthesizeLoopStepGuard L inv = ⊤ := by
  exact (L.gc inv inv).trans himp_eq_top_iff.symm

/-- Independent soundness proof for every candidate, including non-invariants. -/
theorem loop_sound {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) :
    L.post (inv ⊓ synthesizeLoopStepGuard L inv) ≤ inv := by
  exact (L.gc _ _).mpr (le_himp_iff'.mp le_rfl)

/-- Independent meet-closure proof using monotonicity of the forward map. -/
theorem invariant_meet {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv₁ inv₂ : α) :
    IsLoopInvariant L inv₁ → IsLoopInvariant L inv₂ →
      IsLoopInvariant L (inv₁ ⊓ inv₂) := by
  intro h₁ h₂
  exact le_inf ((L.gc.monotone_l inf_le_left).trans h₁)
    ((L.gc.monotone_l inf_le_right).trans h₂)

/-- Also check the definition's claim that the synthesized one-step guard is weakest. -/
theorem loop_guard_adjunction {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv g : α) :
    L.post (inv ⊓ g) ≤ inv ↔ g ≤ synthesizeLoopStepGuard L inv := by
  exact Round2.edge_adjunction L inv inv g

/-- Three independent Boolean coordinates give nontrivial partial repairs. -/
abbrev State := Bool × Bool × Bool

/-- `true` selects the cycle loop; `false` selects the growth loop. -/
def loop (cycle : Bool) : CFGTransfer State State where
  post x := if cycle then (x.2.2, x.1, x.2.1) else (x.1, x.1 || x.2.1, x.2.2)
  pullback b := if cycle then (b.2.1, b.2.2, b.1) else (b.1 && b.2.1, b.2.1, b.2.2)
  gc := by
    rintro ⟨x₁, x₂, x₃⟩ ⟨b₁, b₂, b₃⟩
    cases cycle <;> cases x₁ <;> cases x₂ <;> cases x₃ <;>
      cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

/-- Both loop maps differ from the identity at the same concrete input. -/
theorem loop_nonidentity (cycle : Bool) :
    (loop cycle).post (true, false, false) ≠ (true, false, false) ∧
    (loop cycle).pullback (true, false, false) ≠ (true, false, false) := by
  cases cycle <;> decide

/-- Neither forward nor backward loop map collapses to a constant. -/
theorem loop_nonconstant (cycle : Bool) :
    (loop cycle).post (false, false, false) ≠ (loop cycle).post (true, true, true) ∧
    (loop cycle).pullback (false, false, false) ≠ (loop cycle).pullback (true, true, true) := by
  cases cycle <;> decide

/-- Exhaustive forward/backward stability check on both loops. -/
theorem finite_invariant_pullback (cycle : Bool) (inv : State) :
    IsLoopInvariant (loop cycle) inv ↔ inv ≤ (loop cycle).pullback inv := by
  unfold IsLoopInvariant
  rcases inv with ⟨x, y, z⟩
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive check of both directions, including non-invariant candidates. -/
theorem finite_guard_top (cycle : Bool) (inv : State) :
    IsLoopInvariant (loop cycle) inv ↔ synthesizeLoopStepGuard (loop cycle) inv = ⊤ := by
  unfold IsLoopInvariant
  rcases inv with ⟨x, y, z⟩
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive one-step soundness, without assuming invariance. -/
theorem finite_loop_sound (cycle : Bool) (inv : State) :
    (loop cycle).post (inv ⊓ synthesizeLoopStepGuard (loop cycle) inv) ≤ inv := by
  rcases inv with ⟨x, y, z⟩
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive meet closure, preserving both premises of the target. -/
theorem finite_invariant_meet (cycle : Bool) (inv₁ inv₂ : State) :
    IsLoopInvariant (loop cycle) inv₁ → IsLoopInvariant (loop cycle) inv₂ →
      IsLoopInvariant (loop cycle) (inv₁ ⊓ inv₂) := by
  unfold IsLoopInvariant
  rcases inv₁ with ⟨x₁, y₁, z₁⟩
  rcases inv₂ with ⟨x₂, y₂, z₂⟩
  cases cycle <;> cases x₁ <;> cases y₁ <;> cases z₁ <;>
    cases x₂ <;> cases y₂ <;> cases z₂ <;> decide

/-- Complete classification: the cycle fixes equal bits; growth requires x ≤ y. -/
theorem invariant_truth_table (cycle x y z : Bool) :
    IsLoopInvariant (loop cycle) (x, y, z) ↔
      if cycle then x = y ∧ y = z else x ≤ y := by
  unfold IsLoopInvariant
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Complete loop-step guard table on all candidates. -/
theorem guard_truth_table (cycle x y z : Bool) :
    synthesizeLoopStepGuard (loop cycle) (x, y, z) =
      if cycle then (!x || y, !y || z, !z || x) else (!x || y, true, true) := by
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Distinct proper growth invariants have a proper, nonbottom invariant meet. -/
theorem growth_meet_witness :
    IsLoopInvariant (loop false) (true, true, false) ∧
    IsLoopInvariant (loop false) (false, true, true) ∧
    ((true, true, false) ⊓ (false, true, true) : State) = (false, true, false) ∧
    IsLoopInvariant (loop false) (false, true, false) := by
  unfold IsLoopInvariant
  decide

/-- The guard repairs a genuine failure while retaining a nonbottom state. -/
theorem growth_repair_witness :
    ¬ IsLoopInvariant (loop false) (true, false, true) ∧
    synthesizeLoopStepGuard (loop false) (true, false, true) = (false, true, true) ∧
    (true, false, true) ⊓ synthesizeLoopStepGuard (loop false) (true, false, true) =
      (false, false, true) ∧
    (loop false).post (false, false, true) = (false, false, true) := by
  unfold IsLoopInvariant
  decide

/-- Either missing invariance premise can make the conjunction non-invariant. -/
theorem meet_requires_both_premises :
    IsLoopInvariant (loop false) (true, true, true) ∧
    ¬ IsLoopInvariant (loop false) (true, false, true) ∧
    ¬ IsLoopInvariant (loop false) ((true, true, true) ⊓ (true, false, true)) ∧
    ¬ IsLoopInvariant (loop false) ((true, false, true) ⊓ (true, true, true)) := by
  unfold IsLoopInvariant
  decide

/-- The cycle guard is restrictive and leaves a nonbottom starting state. -/
theorem cycle_repair_witness :
    ¬ IsLoopInvariant (loop true) (true, true, false) ∧
    synthesizeLoopStepGuard (loop true) (true, true, false) = (true, false, true) ∧
    (true, true, false) ⊓ synthesizeLoopStepGuard (loop true) (true, true, false) =
      (true, false, false) := by
  unfold IsLoopInvariant
  decide

/-- Restoring inv once does not ensure the guard persists or allow another
unguarded step. This refutes a stronger interpretation, not the target. -/
theorem one_step_not_persistent :
    let L := loop true
    let inv : State := (true, true, false)
    let guarded := inv ⊓ synthesizeLoopStepGuard L inv
    L.post guarded ≤ inv ∧ ¬ IsLoopInvariant L guarded ∧
      ¬ (L.post (L.post guarded) ≤ inv) := by
  dsimp only
  unfold IsLoopInvariant
  decide

/-- Invariance requires a forward inclusion, not equality with the post-state. -/
theorem invariance_need_not_be_fixedpoint :
    IsLoopInvariant (Round2.keepCoordinate true) (false, true) ∧
    (Round2.keepCoordinate true).post (false, true) ≠ (false, true) := by
  unfold IsLoopInvariant
  decide

end Round4

/-!
## Round 5: inductive witnesses and preheader hoisting

Both definitions and all four new statements match the blueprint exactly.
`IsInductiveFor L inv target` contains preservation and `inv ≤ target`.
`hoistLoopGuard E a₀ inv` establishes the chosen invariant on loop entry;
it does not synthesize that invariant or minimize the guard over all possible
invariants. Entry-target soundness needs only the entailment conjunct, while
the one-step target theorem needs both. Two-step preservation follows from
monotonicity and invariance. No termination or unrestricted iteration theorem
is part of these four statements.

The preheader has two Boolean coordinates, and the loop header has three:
`E.post (x,y) = (y,false,x)` and `E.pullback (u,v,w) = (w,u)`.
Both maps are nonconstant. With the growth loop from Round 4, preheader 11
and invariant/target 110 produce guard 01, entry 100, and loop state 110.
Thus the guard is restrictive, execution remains nonempty, and the loop
actually changes the entered state. Tests also reject missing preservation,
missing target entailment, and omitting the entry guard.

Exhaustive checks cover 16 loop/candidate cases for two-step preservation,
512 loop/preheader/invariant/target cases for each target theorem, and 64
loop/preheader/invariant cases for step-invariance: 1104 cases in total.
All audit declarations, including previous rounds, are checked without
`sorryAx` or `Classical.choice`; only `propext` and `Quot.sound` may remain.
-/

namespace Round5

/-- Independent proof of preservation across two composed loop iterations. -/
theorem iterate_two {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) (h : IsLoopInvariant L inv) :
    (L.comp L).post inv ≤ inv := by
  exact (L.gc.monotone_l h).trans h

/-- Hoisting establishes the selected invariant without assuming preservation. -/
theorem entry_invariant {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (a₀ : α) (inv : β) :
    E.post (a₀ ⊓ hoistLoopGuard E a₀ inv) ≤ inv := by
  exact (E.gc _ _).mpr (le_himp_iff'.mp le_rfl)

/-- Independent proof of the entry-target blueprint. -/
theorem entry_target {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    E.post (a₀ ⊓ hoistLoopGuard E a₀ inv) ≤ target := by
  exact (entry_invariant E a₀ inv).trans h.2

/-- Independent proof of the preheader-plus-loop preservation blueprint. -/
theorem step_invariant {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv : β) (h : IsLoopInvariant L inv) :
    L.post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ inv := by
  exact (L.gc.monotone_l (entry_invariant E a₀ inv)).trans h

/-- Independent proof of the preheader-plus-loop target blueprint. -/
theorem step_target {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    L.post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target := by
  exact (step_invariant E L a₀ inv h.1).trans h.2

/-- Check the definition's weakest-guard claim for the selected invariant. -/
theorem hoist_adjunction {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (a₀ g : α) (inv : β) :
    E.post (a₀ ⊓ g) ≤ inv ↔ g ≤ hoistLoopGuard E a₀ inv := by
  exact Round2.edge_adjunction E a₀ inv g

abbrev PreState := Round2.State
abbrev HeaderState := Round4.State

/-- A nonconstant entry edge between different finite state domains. -/
def entry : CFGTransfer PreState HeaderState where
  post x := (x.2, false, x.1)
  pullback b := (b.2.2, b.1)
  gc := by
    rintro ⟨x₁, x₂⟩ ⟨b₁, b₂, b₃⟩
    cases x₁ <;> cases x₂ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

/-- Neither direction of the entry edge is constant. -/
theorem entry_nonconstant :
    entry.post (false, false) ≠ entry.post (true, true) ∧
    entry.pullback (false, false, false) ≠ entry.pullback (true, true, true) := by
  decide

/-- All 32 preheader/invariant combinations have this Boolean guard formula. -/
theorem hoist_truth_table (a b x y z : Bool) :
    hoistLoopGuard entry (a, b) (x, y, z) = (!a || z, !b || x) := by
  cases a <;> cases b <;> cases x <;> cases y <;> cases z <;> decide

/-- All 16 loop/candidate cases, preserving the invariance premise. -/
theorem finite_iterate_two (cycle : Bool) (inv : HeaderState) :
    IsLoopInvariant (Round4.loop cycle) inv →
      ((Round4.loop cycle).comp (Round4.loop cycle)).post inv ≤ inv := by
  unfold IsLoopInvariant
  rcases inv with ⟨x, y, z⟩
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- All 512 loop/preheader/invariant/target cases for entry target soundness. -/
theorem finite_entry_target (cycle : Bool) (a₀ : PreState) (inv target : HeaderState) :
    IsInductiveFor (Round4.loop cycle) inv target →
      entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv) ≤ target := by
  unfold IsInductiveFor IsLoopInvariant
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases target with ⟨t₁, t₂, t₃⟩
  cases cycle <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;> decide

/-- All 64 loop/preheader/invariant cases for preservation after entry and a step. -/
theorem finite_step_invariant (cycle : Bool) (a₀ : PreState) (inv : HeaderState) :
    IsLoopInvariant (Round4.loop cycle) inv →
      (Round4.loop cycle).post (entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv)) ≤ inv := by
  unfold IsLoopInvariant
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  cases cycle <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;> cases i₃ <;> decide

/-- All 512 loop/preheader/invariant/target cases for target soundness after a step. -/
theorem finite_step_target (cycle : Bool) (a₀ : PreState) (inv target : HeaderState) :
    IsInductiveFor (Round4.loop cycle) inv target →
      (Round4.loop cycle).post (entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv)) ≤ target := by
  unfold IsInductiveFor IsLoopInvariant
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases target with ⟨t₁, t₂, t₃⟩
  cases cycle <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;> decide

/-- A proper inductive invariant, restrictive nonbottom guard, and changing loop state. -/
theorem active_hoist_witness :
    let L := Round4.loop false
    let a₀ : PreState := (true, true)
    let inv : HeaderState := (true, true, false)
    let guard := hoistLoopGuard entry a₀ inv
    let entered := entry.post (a₀ ⊓ guard)
    IsInductiveFor L inv inv ∧ guard = (false, true) ∧
      a₀ ⊓ guard = (false, true) ∧ entered = (true, false, false) ∧
      L.post entered = inv ∧ (L.comp L).post entered ≤ inv := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant
  decide

/-- Entry can establish inv while a subsequent loop step violates it:
preservation is necessary for both loop-step claims and the two-step claim. -/
theorem missing_invariance_counterexample :
    let L := Round4.loop false
    let inv : HeaderState := (true, false, false)
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    ¬ IsLoopInvariant L inv ∧ entered = inv ∧
      ¬ ((L.comp L).post inv ≤ inv) ∧ ¬ (L.post entered ≤ inv) := by
  dsimp only
  unfold IsLoopInvariant
  decide

/-- Preservation alone cannot guarantee a target not implied by the invariant. -/
theorem missing_entailment_counterexample :
    let L := Round4.loop false
    let inv : HeaderState := (true, true, false)
    let target : HeaderState := (false, true, false)
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    IsLoopInvariant L inv ∧ ¬ (inv ≤ target) ∧
      ¬ (entered ≤ target) ∧ ¬ (L.post entered ≤ target) := by
  dsimp only
  unfold IsLoopInvariant
  decide

/-- Omitting the restrictive guard breaks both entry and post-step target safety. -/
theorem missing_guard_counterexample :
    ¬ (entry.post (true, true) ≤ (true, true, false)) ∧
    ¬ ((Round4.loop false).post (entry.post (true, true)) ≤ (true, true, false)) := by
  decide

/-- Hoisting is weakest for the chosen inv, not necessarily for the target:
a larger guard can still establish a larger proper target. -/
theorem target_guard_can_be_weaker :
    let L := Round4.loop false
    let inv : HeaderState := (false, true, false)
    let target : HeaderState := (true, true, false)
    let g : PreState := (false, true)
    IsInductiveFor L inv target ∧ entry.post g ≤ target ∧
      L.post (entry.post g) ≤ target ∧
      ¬ (g ≤ hoistLoopGuard entry (true, true) inv) := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant
  decide

end Round5

/-!
## Round 6: arbitrary finite iteration

`CFGTransfer.iterate` starts at identity and appends one loop step in its
successor clause. Thus the forward map is `L.post ∘ post_n`, while the
pullback is `pullback_n ∘ L.pullback`. All four new statements match the
blueprint, including `n = 0`. In the hoisted claims, zero counts loop steps
only: the entry edge has already run. Induction proves safety for every
finite iteration count; this does not prove termination or a full forcing
semantics. The same preheader guard is used once, with no repeated guard
test in the iterated transfer.

The general proofs below cover every natural number independently of the
target placeholders. Separate computation checks use all depths 0 through
5, the three-coordinate cycle, and a shift loop whose post is `(false,x,y)`
and whose pullback is `(v,w,true)`. These cover 96 forward-invariance cases,
96 pullback cases, 384 hoisted-invariance cases, and 3072 hoisted-target
cases: 3648 bounded checks, in addition to the unbounded induction proofs.
Exact traces detect off-by-one errors and distinguish forward traversal
from pullback. A delayed-failure witness passes at entry and after one
step, fails after two, and passes again after three, showing why shallow
checks cannot substitute for an inductive invariant.
-/

namespace Round6

/-- Zero iterations are exactly the identity transfer. -/
theorem iterate_zero {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) :
    L.iterate 0 = CFGTransfer.id α := by
  rfl

/-- One iteration is exactly the original transfer, including its proof field. -/
theorem iterate_one {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) :
    L.iterate 1 = L := by
  cases L
  rfl

/-- Successor iteration runs the loop last forward and first backward. -/
theorem successor_maps {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) (n : ℕ) :
    (L.iterate (n + 1)).post = L.post ∘ (L.iterate n).post ∧
    (L.iterate (n + 1)).pullback = (L.iterate n).pullback ∘ L.pullback := by
  exact ⟨rfl, rfl⟩

/-- Independent induction proof of the arbitrary-iteration invariant target. -/
theorem iterate_invariant {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post inv ≤ inv := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (L.gc.monotone_l ih).trans h

/-- Independent pullback stability proof for all iteration counts. -/
theorem iterate_pullback {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, inv ≤ (L.iterate n).pullback inv := by
  intro n
  exact ((L.iterate n).gc _ _).mp (iterate_invariant L inv h n)

/-- Establish inv at entry, then preserve it for any finite number of steps. -/
theorem hoist_invariant {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv : β) (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ inv := by
  intro n
  exact ((L.iterate n).gc.monotone_l (Round5.entry_invariant E a₀ inv)).trans
    (iterate_invariant L inv h n)

/-- Independent target-safety proof for all iteration counts. -/
theorem hoist_target {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target := by
  intro n
  exact (hoist_invariant E L a₀ inv h.1 n).trans h.2

open Round5

/-- A shift with observable behavior at zero, one, two, and three steps. -/
def shift : CFGTransfer HeaderState HeaderState where
  post x := (false, x.1, x.2.1)
  pullback b := (b.2.1, b.2.2, true)
  gc := by
    rintro ⟨x₁, x₂, x₃⟩ ⟨b₁, b₂, b₃⟩
    cases x₁ <;> cases x₂ <;> cases x₃ <;>
      cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

/-- Select the existing cycle or the new shift, both nonidentity and nonconstant. -/
def loop (cyclic : Bool) : CFGTransfer HeaderState HeaderState :=
  if cyclic then Round4.loop true else shift

/-- Six concrete depths; this bounded predicate does not stand for all naturals. -/
def ThroughFive (P : ℕ → Prop) : Prop := P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5

/-- Exhaustive forward preservation for both loops, all candidates, and six depths. -/
theorem finite_iterate (cyclic : Bool) (inv : HeaderState) :
    IsLoopInvariant (loop cyclic) inv →
      ThroughFive (fun n => ((loop cyclic).iterate n).post inv ≤ inv) := by
  unfold IsLoopInvariant ThroughFive
  rcases inv with ⟨x, y, z⟩
  cases cyclic <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive backward preservation at the same six depths. -/
theorem finite_pullback (cyclic : Bool) (inv : HeaderState) :
    IsLoopInvariant (loop cyclic) inv →
      ThroughFive (fun n => inv ≤ ((loop cyclic).iterate n).pullback inv) := by
  unfold IsLoopInvariant ThroughFive
  rcases inv with ⟨x, y, z⟩
  cases cyclic <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive hoisted preservation, retaining every premise. -/
theorem finite_hoist_invariant (cyclic : Bool) (a₀ : PreState) (inv : HeaderState) :
    IsLoopInvariant (loop cyclic) inv →
      ThroughFive (fun n =>
        ((loop cyclic).iterate n).post (entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv)) ≤ inv) := by
  unfold IsLoopInvariant ThroughFive
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  cases cyclic <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;> cases i₃ <;> decide

/-- Exhaustive hoisted target safety, varying the target independently of inv. -/
theorem finite_hoist_target (cyclic : Bool) (a₀ : PreState) (inv target : HeaderState) :
    IsInductiveFor (loop cyclic) inv target →
      ThroughFive (fun n =>
        ((loop cyclic).iterate n).post (entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv)) ≤ target) := by
  unfold IsInductiveFor IsLoopInvariant ThroughFive
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases target with ⟨t₁, t₂, t₃⟩
  cases cyclic <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;> decide

/-- All input states exhibit the expected shift and its backward adjoint. -/
theorem shift_trace (x y z : Bool) :
    (shift.iterate 0).post (x, y, z) = (x, y, z) ∧
    (shift.iterate 1).post (x, y, z) = (false, x, y) ∧
    (shift.iterate 2).post (x, y, z) = (false, false, x) ∧
    (shift.iterate 3).post (x, y, z) = (false, false, false) ∧
    (shift.iterate 5).post (x, y, z) = (false, false, false) ∧
    (shift.iterate 0).pullback (x, y, z) = (x, y, z) ∧
    (shift.iterate 1).pullback (x, y, z) = (y, z, true) ∧
    (shift.iterate 2).pullback (x, y, z) = (z, true, true) ∧
    (shift.iterate 3).pullback (x, y, z) = (true, true, true) ∧
    (shift.iterate 5).pullback (x, y, z) = (true, true, true) := by
  cases x <;> cases y <;> cases z <;> decide

/-- The cycle has period three; its post and pullback rotate in opposite directions. -/
theorem cycle_trace (x y z : Bool) :
    ((Round4.loop true).iterate 1).post (x, y, z) = (z, x, y) ∧
    ((Round4.loop true).iterate 2).post (x, y, z) = (y, z, x) ∧
    ((Round4.loop true).iterate 3).post (x, y, z) = (x, y, z) ∧
    ((Round4.loop true).iterate 5).post (x, y, z) = (y, z, x) ∧
    ((Round4.loop true).iterate 1).pullback (x, y, z) = (y, z, x) ∧
    ((Round4.loop true).iterate 2).pullback (x, y, z) = (z, x, y) ∧
    ((Round4.loop true).iterate 3).pullback (x, y, z) = (x, y, z) ∧
    ((Round4.loop true).iterate 5).pullback (x, y, z) = (z, x, y) := by
  cases x <;> cases y <;> cases z <;> decide

/-- A proper, nonbottom invariant is preserved by strict decrease, not equality. -/
theorem shift_invariant_witness :
    IsLoopInvariant shift (false, true, true) ∧
    (shift.iterate 1).post (false, true, true) = (false, false, true) ∧
    (shift.iterate 2).post (false, true, true) = (false, false, false) := by
  unfold IsLoopInvariant
  decide

/-- Zero iterations still enter the loop; positive depths use the already established inv. -/
theorem growth_hoisted_trace :
    let L := Round4.loop false
    let inv : HeaderState := (true, true, false)
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    (L.iterate 0).post entered = (true, false, false) ∧
    (L.iterate 1).post entered = inv ∧
    (L.iterate 2).post entered = inv ∧ (L.iterate 5).post entered = inv := by
  dsimp only
  decide

/-- Concrete non-vacuity for the full unbounded claim, with no per-step guard check. -/
theorem growth_hoist_all_steps :
    ∀ n : ℕ, ((Round4.loop false).iterate n).post
      (entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) (true, true, false))) ≤
        (true, true, false) := by
  exact hoist_invariant entry (Round4.loop false) (true, true) (true, true, false)
    (by unfold IsLoopInvariant; decide)

/-- Without invariance, entry and one step can pass, while two steps fail.
Success at three steps does not repair the failure of the universal claim. -/
theorem delayed_failure_counterexample :
    let inv : HeaderState := (true, true, false)
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    ¬ IsLoopInvariant shift inv ∧
    (shift.iterate 0).post entered ≤ inv ∧ (shift.iterate 1).post entered ≤ inv ∧
    ¬ ((shift.iterate 2).post entered ≤ inv) ∧ (shift.iterate 3).post entered ≤ inv := by
  dsimp only
  unfold IsLoopInvariant
  decide

end Round6

/-!
## Round 7: algebraic forcing and rewrite preconditions

The two definitions and all four theorem statements match the blueprint.
`Forces a p` means `a ≤ p`; `ForcesAfter T a q` means `T.post a ≤ q`.
The first equivalence is the transfer adjunction, and the guard/chain
equivalences follow from Heyting adjunction and meet. The hoisted forcing
claim unfolds to the arbitrary-iteration target claim from Round 6.

Scope: these definitions implement an order-based forcing fragment. They
introduce no site, covers, or recursive quantifier/locality clauses for full
Kripke-Joyal semantics. The rewrite-chain theorem establishes both conditions
at one guarded stage; it does not model sequential state-changing rewrites.
A concrete counterexample below separates these interpretations.

The independent computation checks cover 32 heterogeneous transfer cases,
64 guarded-forcing cases, 256 rewrite-chain cases, and 3072 hoisted forcing
cases at depths 0 through 5: 3424 cases, in addition to the Bool truth table,
direct Prop proofs, and general proofs (including all natural iteration counts).
Nonbottom witnesses and independently failing rewrite conditions rule out
vacuous examples. The entire audit retains zero sorryAx/choice dependencies.
-/

namespace Round7

/-- Independent forcing/pullback equivalence, with the original transfer orientation. -/
theorem after_pullback {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (a : α) (q : β) :
    ForcesAfter T a q ↔ Forces a (T.pullback q) := by
  exact T.gc a q

/-- Independent guarded-forcing equivalence. -/
theorem guard_forcing {α : Type*} [HeytingAlgebra α] (a p g : α) :
    Forces (a ⊓ g) p ↔ Forces g (synthesizeGuard a p) := by
  exact blueprint_adjunction a p g

/-- Independent equivalence for two conditions at the same guarded stage. -/
theorem rewrite_chain {α : Type*} [HeytingAlgebra α] (a p₁ p₂ g : α) :
    Forces (a ⊓ g) (p₁ ⊓ p₂) ↔ Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) := by
  unfold Forces synthesizeGuard
  simp only [le_inf_iff, le_himp_iff']

/-- Independent hoisted forcing proof for every natural iteration count. -/
theorem hoisted_forcing {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    ∀ n : ℕ, ForcesAfter (E.comp (L.iterate n)) (a₀ ⊓ hoistLoopGuard E a₀ inv) target := by
  exact Round6.hoist_target E L a₀ inv target h

/-- All four Bool forcing judgments, including the one rejected judgment. -/
theorem bool_forcing_table :
    Forces false false ∧ Forces false true ∧ Forces true true ∧ ¬ Forces true false := by
  unfold Forces
  decide

/-- On Prop, forcing is implication; it is not an assertion of its premise. -/
theorem prop_forcing (a p : Prop) : Forces a p ↔ (a → p) := by
  rfl

/-- Direct constructive Prop proof of the guard claim. -/
theorem prop_guard (a p g : Prop) :
    Forces (a ⊓ g) p ↔ Forces g (synthesizeGuard a p) := by
  change ((a ∧ g) → p) ↔ (g → a → p)
  exact ⟨fun h hg ha => h ⟨ha, hg⟩, fun h hag => h hag.2 hag.1⟩

/-- Direct constructive Prop proof, separately extracting both rewrite conditions. -/
theorem prop_chain (a p₁ p₂ g : Prop) :
    Forces (a ⊓ g) (p₁ ⊓ p₂) ↔ Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) := by
  change ((a ∧ g) → p₁ ∧ p₂) ↔ (g → (a → p₁) ∧ (a → p₂))
  constructor
  · exact fun h hg => ⟨fun ha => (h ⟨ha, hg⟩).1, fun ha => (h ⟨ha, hg⟩).2⟩
  · exact fun h hag => ⟨(h hag.2).1 hag.1, (h hag.2).2 hag.1⟩

open Round5

/-- All 32 forcing judgments across the nonconstant Bool²-to-Bool³ entry transfer. -/
theorem finite_after (a : PreState) (q : HeaderState) :
    ForcesAfter entry a q ↔ Forces a (entry.pullback q) := by
  unfold ForcesAfter Forces
  rcases a with ⟨a₁, a₂⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases a₁ <;> cases a₂ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- All 64 two-coordinate guarded-forcing cases. -/
theorem finite_guard (a p g : PreState) :
    Forces (a ⊓ g) p ↔ Forces g (synthesizeGuard a p) := by
  unfold Forces
  rcases a with ⟨a₁, a₂⟩
  rcases p with ⟨p₁, p₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases a₁ <;> cases a₂ <;> cases p₁ <;> cases p₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- All 256 two-coordinate stage/condition/condition/guard combinations. -/
theorem finite_chain (a p₁ p₂ g : PreState) :
    Forces (a ⊓ g) (p₁ ⊓ p₂) ↔ Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) := by
  unfold Forces
  rcases a with ⟨a₁, a₂⟩
  rcases p₁ with ⟨p₁₁, p₁₂⟩
  rcases p₂ with ⟨p₂₁, p₂₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases a₁ <;> cases a₂ <;> cases p₁₁ <;> cases p₁₂ <;>
    cases p₂₁ <;> cases p₂₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- Both dynamic loops, all preheaders/invariants/targets, and depths 0 through 5. -/
theorem finite_hoisted_forcing (cyclic : Bool) (a₀ : PreState) (inv target : HeaderState) :
    IsInductiveFor (Round6.loop cyclic) inv target →
      Round6.ThroughFive (fun n =>
        ForcesAfter (entry.comp ((Round6.loop cyclic).iterate n))
          (a₀ ⊓ hoistLoopGuard entry a₀ inv) target) := by
  unfold IsInductiveFor IsLoopInvariant Round6.ThroughFive ForcesAfter Forces
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases target with ⟨t₁, t₂, t₃⟩
  cases cyclic <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;> decide

/-- Using post in place of pullback, or ignoring the transfer, changes the answer. -/
theorem transfer_orientation_witness :
    let T := Round4.loop true
    let a : HeaderState := (true, false, false)
    let q : HeaderState := (false, true, false)
    ForcesAfter T a q ∧ Forces a (T.pullback q) ∧
      ¬ Forces a (T.post q) ∧ ¬ Forces a q := by
  dsimp only
  unfold ForcesAfter Forces
  decide

/-- Distinct proper preconditions share a nonbottom satisfying guarded stage. -/
theorem rewrite_active_witness :
    let a : HeaderState := (true, true, true)
    let p₁ : HeaderState := (true, true, false)
    let p₂ : HeaderState := (true, false, true)
    let g : HeaderState := (true, false, false)
    Forces (a ⊓ g) (p₁ ⊓ p₂) ∧
      Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) ∧
      ¬ Forces a (p₁ ⊓ p₂) := by
  dsimp only
  unfold Forces
  decide

/-- Each rewrite condition can fail while the other holds. -/
theorem rewrite_conditions_independent :
    (Forces (false, true, false) (true, true, false) ∧
      ¬ Forces (false, true, false) (true, false, true)) ∧
    (¬ Forces (false, false, true) (true, true, false) ∧
      Forces (false, false, true) (true, false, true)) := by
  unfold Forces
  decide

/-- Replacing either meet by join accepts a guard that fails the conjunction. -/
theorem rewrite_join_counterexample :
    let a : HeaderState := (true, true, true)
    let p₁ : HeaderState := (true, true, false)
    let p₂ : HeaderState := (true, false, true)
    let g : HeaderState := (false, true, false)
    Forces g (synthesizeGuard a p₁ ⊔ synthesizeGuard a p₂) ∧
      Forces (a ⊓ g) (p₁ ⊔ p₂) ∧ ¬ Forces (a ⊓ g) (p₁ ⊓ p₂) := by
  dsimp only
  unfold Forces
  decide

/-- The theorem does not promise that a state-changing first rewrite preserves
the second precondition. Both hold initially, but cycling the stage breaks p₂. -/
theorem same_stage_is_not_sequential :
    Forces (true, false, false) ((true, true, false) ⊓ (true, false, true)) ∧
    ¬ ForcesAfter (Round4.loop true) (true, false, false) (true, false, true) := by
  unfold ForcesAfter Forces
  decide

/-- A proper inductive witness succeeds in entry-then-loop order, but not in reverse. -/
theorem hoist_composition_order :
    let E := Round4.loop true
    let L := Round4.loop false
    let inv : HeaderState := (false, true, false)
    let a₀ : HeaderState := (true, true, true)
    let g := hoistLoopGuard E a₀ inv
    IsInductiveFor L inv inv ∧ g = (true, false, false) ∧
    ForcesAfter (E.comp (L.iterate 1)) (a₀ ⊓ g) inv ∧
    ¬ ForcesAfter ((L.iterate 1).comp E) (a₀ ⊓ g) inv := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant ForcesAfter Forces
  decide

/-- The same nonbottom guarded stage forces the proper target at every depth. -/
theorem hoisted_forcing_all_steps :
    ∀ n : ℕ, ForcesAfter ((Round4.loop true).comp ((Round4.loop false).iterate n))
      ((true, true, true) ⊓
        hoistLoopGuard (Round4.loop true) (true, true, true) (false, true, false))
      (false, true, false) := by
  exact hoisted_forcing (Round4.loop true) (Round4.loop false) (true, true, true)
    (false, true, false) (false, true, false)
    (by unfold IsInductiveFor IsLoopInvariant; decide)

/-- Without inductivity, the forcing claim can pass at depths 0 and 1 but fail at 2. -/
theorem delayed_forcing_failure :
    let inv : HeaderState := (true, true, false)
    let guarded := (true, true) ⊓ hoistLoopGuard entry (true, true) inv
    ¬ IsInductiveFor Round6.shift inv inv ∧
    ForcesAfter (entry.comp (Round6.shift.iterate 0)) guarded inv ∧
    ForcesAfter (entry.comp (Round6.shift.iterate 1)) guarded inv ∧
    ¬ ForcesAfter (entry.comp (Round6.shift.iterate 2)) guarded inv := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant ForcesAfter Forces
  decide

end Round7

/-!
## Round 8: stage-guarded IR equivalence

The definition and all four theorem statements match the blueprint exactly.
`GuardedEquiv eval p t₁ t₂` checks equality at every `s ≤ p`, not just at `p`.
All guards include bottom, so even a bottom guard requires equality there.
No evaluator monotonicity or restriction law is assumed or needed: both
rewrites are compared at the same stage. Synthesized-chain soundness gives
equality at the guarded stage, not at the original stage, and does not claim
the residual is weakest for endpoint equivalence.

The concrete IR has variables, constants, and binary addition. Its numeric
interpretation uses 0/1 inputs and natural addition; its Boolean interpretation
uses disjunction. The chain is x+(y+z) -> y+z -> z. The first guard forbids x,
the second forbids y, and their meet still permits z. The numeric endpoint
values agree exactly when x=y=false, and vary with z even inside that guard.
Both evaluators have the same exact classification of guarded equivalence;
Boolean pointwise equality alone can hold outside the valid guard.

Besides general proofs, the audit checks every guard for all three pairs,
all 64 pairs of guards for transitivity, and all 512 source/guard/guard
combinations for synthesis, under both evaluators. Explicit witnesses reject
guard joins, omitted premises, equality only at the maximal stage, and
assuming equality at the original unguarded stage. No target placeholder or
choice-dependent proof is used.
-/

namespace Round8

/-- Independent reflexivity proof, requiring no property of the evaluator. -/
theorem equiv_refl {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (t : Term) : GuardedEquiv eval ⊤ t t := by
  intro s _
  rfl

/-- Independent symmetry proof at each forcing stage. -/
theorem equiv_symm {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p : α) (t₁ t₂ : Term) :
    GuardedEquiv eval p t₁ t₂ → GuardedEquiv eval p t₂ t₁ := by
  intro h s hs
  exact (h s hs).symm

/-- Both rewrite premises apply to every stage below the meet. -/
theorem equiv_trans {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : GuardedEquiv eval p₁ t₁ t₂) (h₂ : GuardedEquiv eval p₂ t₂ t₃) :
    GuardedEquiv eval (p₁ ⊓ p₂) t₁ t₃ := by
  intro s hs
  exact (h₁ s (hs.trans inf_le_left)).trans (h₂ s (hs.trans inf_le_right))

/-- Independent synthesized-chain proof using the audited forcing equivalence. -/
theorem synthesized_chain {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (a p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : GuardedEquiv eval p₁ t₁ t₂) (h₂ : GuardedEquiv eval p₂ t₂ t₃) :
    eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) t₁ =
      eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) t₃ := by
  exact equiv_trans eval p₁ p₂ t₁ t₂ t₃ h₁ h₂ _
    ((Round7.rewrite_chain a p₁ p₂ _).mpr le_rfl)

abbrev Stage := Round4.State

/-- A small expression IR with two independently removable input contributions. -/
inductive IR where
  | zero
  | one
  | x
  | y
  | z
  | add (left right : IR)

/-- Numeric evaluation with the three stage bits supplying 0/1 variable values. -/
def evalNat (s : Stage) : IR → ℕ
  | .zero => 0
  | .one => 1
  | .x => if s.1 then 1 else 0
  | .y => if s.2.1 then 1 else 0
  | .z => if s.2.2 then 1 else 0
  | .add l r => evalNat s l + evalNat s r

/-- Boolean evaluation of the same syntax, with addition interpreted as disjunction. -/
def evalBool (s : Stage) : IR → Bool
  | .zero => false
  | .one => true
  | .x => s.1
  | .y => s.2.1
  | .z => s.2.2
  | .add l r => evalBool s l || evalBool s r

def original : IR := .add .x (.add .y .z)
def middle : IR := .add .y .z
def optimized : IR := .z
def guardX : Stage := (false, true, true)
def guardY : Stage := (true, false, true)

/-- Expand the universal stage check into three finite Boolean quantifiers. -/
theorem guarded_cube_iff {Term Val : Type*} (eval : Stage → Term → Val)
    (p : Stage) (t₁ t₂ : Term) :
    GuardedEquiv eval p t₁ t₂ ↔
      ∀ x y z : Bool, (x, y, z) ≤ p → eval (x, y, z) t₁ = eval (x, y, z) t₂ := by
  constructor
  · exact fun h x y z hs => h (x, y, z) hs
  · rintro h ⟨x, y, z⟩ hs
    exact h x y z hs

/-- Numeric equality holds pointwise exactly under the intended stage restrictions. -/
theorem numeric_pointwise_table (x y z : Bool) :
    (evalNat (x, y, z) original = evalNat (x, y, z) middle ↔ x = false) ∧
    (evalNat (x, y, z) middle = evalNat (x, y, z) optimized ↔ y = false) ∧
    (evalNat (x, y, z) original = evalNat (x, y, z) optimized ↔ x = false ∧ y = false) := by
  cases x <;> cases y <;> cases z <;> decide

/-- Exact guarded-equivalence table over every numeric guard, including bottom and top. -/
theorem nat_guard_classification (p : Stage) :
    (GuardedEquiv evalNat p original middle ↔ p.1 = false) ∧
    (GuardedEquiv evalNat p middle optimized ↔ p.2.1 = false) ∧
    (GuardedEquiv evalNat p original optimized ↔ p.1 = false ∧ p.2.1 = false) := by
  simp only [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- Universal substage checking yields the same exact guards for the Boolean evaluator. -/
theorem bool_guard_classification (p : Stage) :
    (GuardedEquiv evalBool p original middle ↔ p.1 = false) ∧
    (GuardedEquiv evalBool p middle optimized ↔ p.2.1 = false) ∧
    (GuardedEquiv evalBool p original optimized ↔ p.1 = false ∧ p.2.1 = false) := by
  simp only [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- Concrete reflexivity for every term in the chain, under both interpretations. -/
theorem concrete_refl :
    GuardedEquiv evalNat ⊤ original original ∧ GuardedEquiv evalNat ⊤ middle middle ∧
    GuardedEquiv evalNat ⊤ optimized optimized ∧ GuardedEquiv evalBool ⊤ original original ∧
    GuardedEquiv evalBool ⊤ middle middle ∧ GuardedEquiv evalBool ⊤ optimized optimized := by
  simp only [guarded_cube_iff]
  decide

/-- Concrete symmetry at every guard under both interpretations. -/
theorem finite_symm (p : Stage) :
    (GuardedEquiv evalNat p original middle → GuardedEquiv evalNat p middle original) ∧
    (GuardedEquiv evalBool p original middle → GuardedEquiv evalBool p middle original) := by
  simp only [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- All 64 guard pairs for each interpretation, keeping both rewrite hypotheses. -/
theorem finite_trans (p q : Stage) :
    (GuardedEquiv evalNat p original middle → GuardedEquiv evalNat q middle optimized →
      GuardedEquiv evalNat (p ⊓ q) original optimized) ∧
    (GuardedEquiv evalBool p original middle → GuardedEquiv evalBool q middle optimized →
      GuardedEquiv evalBool (p ⊓ q) original optimized) := by
  rw [(nat_guard_classification p).1, (nat_guard_classification q).2.1,
    (nat_guard_classification (p ⊓ q)).2.2,
    (bool_guard_classification p).1, (bool_guard_classification q).2.1,
    (bool_guard_classification (p ⊓ q)).2.2]
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases p₁ <;> cases p₂ <;> cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- All 512 source/guard/guard combinations for each evaluator. -/
theorem finite_synthesis (a p q : Stage) :
    (GuardedEquiv evalNat p original middle → GuardedEquiv evalNat q middle optimized →
      evalNat (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) original =
        evalNat (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) optimized) ∧
    (GuardedEquiv evalBool p original middle → GuardedEquiv evalBool q middle optimized →
      evalBool (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) original =
        evalBool (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) optimized) := by
  simp only [guarded_cube_iff]
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases p₁ <;> cases p₂ <;>
    cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Both chains have satisfiable, proper guards whose meet remains nonbottom. -/
theorem concrete_rewrites :
    GuardedEquiv evalNat guardX original middle ∧ GuardedEquiv evalNat guardY middle optimized ∧
    GuardedEquiv evalNat (guardX ⊓ guardY) original optimized ∧
    GuardedEquiv evalBool guardX original middle ∧ GuardedEquiv evalBool guardY middle optimized ∧
    GuardedEquiv evalBool (guardX ⊓ guardY) original optimized := by
  simp only [guarded_cube_iff]
  decide

/-- Synthesizing the two conditional rewrites keeps z and removes exactly x and y. -/
theorem residual_stage_table (x y z : Bool) :
    let a : Stage := (x, y, z)
    let residual := synthesizeGuard a guardX ⊓ synthesizeGuard a guardY
    residual = (!x, !y, true) ∧ a ⊓ residual = (false, false, z) ∧
    evalNat (a ⊓ residual) original = (if z then 1 else 0) ∧
    evalNat (a ⊓ residual) optimized = (if z then 1 else 0) ∧
    evalBool (a ⊓ residual) original = z ∧ evalBool (a ⊓ residual) optimized = z := by
  dsimp only
  cases x <;> cases y <;> cases z <;> decide

/-- Nonbottom guarded equality has value 1, differs from the bottom value 0,
and does not imply equality at the original maximal stage. -/
theorem active_stage_witness :
    guardX ⊓ guardY = (false, false, true) ∧
    evalNat (false, false, true) original = 1 ∧ evalNat (false, false, true) optimized = 1 ∧
    evalNat (false, false, false) original = 0 ∧
    evalNat (true, true, true) original = 3 ∧ evalNat (true, true, true) optimized = 1 := by
  decide

/-- Joining the guards cannot replace their conjunction. -/
theorem guard_join_counterexample :
    ¬ GuardedEquiv evalNat (guardX ⊔ guardY) original optimized ∧
    ¬ GuardedEquiv evalBool (guardX ⊔ guardY) original optimized := by
  simp only [guarded_cube_iff]
  decide

/-- Either missing rewrite premise permits a failing endpoint equivalence. -/
theorem both_rewrites_required :
    (¬ GuardedEquiv evalNat ⊤ original middle ∧
      GuardedEquiv evalNat guardY middle optimized ∧
      ¬ GuardedEquiv evalNat (⊤ ⊓ guardY) original optimized) ∧
    (GuardedEquiv evalNat guardX original middle ∧
      ¬ GuardedEquiv evalNat ⊤ middle optimized ∧
      ¬ GuardedEquiv evalNat (guardX ⊓ ⊤) original optimized) := by
  simp only [guarded_cube_iff]
  decide

/-- Boolean equality at p itself is insufficient: a smaller forcing stage distinguishes terms. -/
theorem checking_only_guard_stage_fails :
    evalBool (true, false, true) original = evalBool (true, false, true) middle ∧
    Forces (true, false, false) (true, false, true) ∧
    evalBool (true, false, false) original ≠ evalBool (true, false, false) middle ∧
    ¬ GuardedEquiv evalBool (true, false, true) original middle := by
  simp only [guarded_cube_iff]
  unfold Forces
  decide

/-- Bottom forces every guard, so incompatible constant terms have no guard at all. -/
theorem constants_never_equiv (p : Stage) : ¬ GuardedEquiv evalNat p .zero .one := by
  intro h
  have hb := h (false, false, false) bot_le
  change (0 : ℕ) = 1 at hb
  cases hb

/-- Conservative supplied preconditions can synthesize a stricter guard than endpoint equality needs. -/
theorem residual_need_not_be_weakest :
    GuardedEquiv evalNat ⊥ original middle ∧ GuardedEquiv evalNat guardY middle optimized ∧
    synthesizeGuard (true, true, true) (⊥ : Stage) ⊓
      synthesizeGuard (true, true, true) guardY = (false, false, false) ∧
    GuardedEquiv evalNat (false, false, true) original optimized := by
  simp only [guarded_cube_iff]
  decide

end Round8

/-!
## Round 9: inter-block and loop-hoisted conditional rewrites

The definition and all four statements match the blueprint. `pullbackEval`
precomposes a target evaluator with `T.post`, which maps source stages into
the evaluator's domain. The admissible source guard is instead `T.pullback q`,
by adjunction. Weakening restricts stages using `p ≤ q`. No monotonicity or
naturality of the evaluator is assumed. Transport preserves guarded
equivalence, but need not reflect it when some target stages are unreachable.

The numeric and Boolean IR evaluators from Round 8 are transported across
the heterogeneous entry edge `(x,y) ↦ (y,false,x)`. The target guard 011
becomes source guard 10. Source 11 is restricted to 10, enters at 001,
and evaluates both original and middle terms to 1 (true for the Boolean
interpretation). Without the guard the numeric values are 2 and 1.

A new loop swaps y and z, preserving 011 while alternating 001 and 010.
Thus the hoisted rewrite remains equal for all iteration counts even though
the loop state changes. Independent numeric computation checks cover 64
weakening guard pairs, 8 pullback guards, 32 source/target pairs, and 3072
loop-hoisted cases at depths 0 through 5: 3176 cases. Both interpreters also
have exact transported guard tables and an all-natural hoisting witness.
Negative witnesses distinguish the two transfer directions, composition
order, and each required semantic hypothesis. No target placeholder or
Classical.choice dependency is used.
-/

namespace Round9

/-- Weakening restricts the set of stages that must be checked. -/
theorem equiv_weaken {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p q : α) (t₁ t₂ : Term)
    (hpq : Forces p q) (h : GuardedEquiv eval q t₁ t₂) :
    GuardedEquiv eval p t₁ t₂ := by
  intro s hs
  exact h s (hs.trans hpq)

/-- Independent transport proof using the adjunction in the required direction. -/
theorem equiv_pullback {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (q : β) (t₁ t₂ : Term) (h : GuardedEquiv evalβ q t₁ t₂) :
    GuardedEquiv (pullbackEval T evalβ) (T.pullback q) t₁ t₂ := by
  intro s hs
  exact h (T.post s) ((T.gc s q).mpr hs)

/-- Independent edge-synthesis proof at the transferred guarded stage. -/
theorem edge_synthesize {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (a : α) (q : β) (t₁ t₂ : Term) (h : GuardedEquiv evalβ q t₁ t₂) :
    evalβ (T.post (a ⊓ synthesizeEdgeGuard T a q)) t₁ =
      evalβ (T.post (a ⊓ synthesizeEdgeGuard T a q)) t₂ := by
  exact h _ ((T.gc _ _).mpr (le_himp_iff'.mp le_rfl))

/-- Independent loop-hoisted rewrite proof for every finite iteration count. -/
theorem hoisted_rewrite {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β) (evalβ : β → Term → Val)
    (a₀ : α) (inv q : β) (t₁ t₂ : Term)
    (hind : IsInductiveFor L inv q) (heq : GuardedEquiv evalβ q t₁ t₂) :
    ∀ n : ℕ,
      evalβ ((E.comp (L.iterate n)).post (a₀ ⊓ hoistLoopGuard E a₀ inv)) t₁ =
        evalβ ((E.comp (L.iterate n)).post (a₀ ⊓ hoistLoopGuard E a₀ inv)) t₂ := by
  intro n
  exact heq _ (Round6.hoist_target E L a₀ inv q hind n)

/-- Pulling an evaluator along identity preserves it definitionally. -/
theorem pullback_eval_id {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) : pullbackEval (CFGTransfer.id α) eval = eval := by
  rfl

/-- Evaluator precomposition follows the same source-to-target path order. -/
theorem pullback_eval_comp {α β γ Term Val : Type*}
    [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]
    (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ) (eval : γ → Term → Val) :
    pullbackEval (T₁.comp T₂) eval = pullbackEval T₁ (pullbackEval T₂ eval) := by
  rfl

open Round5 Round8

/-- A nonidentity loop that keeps x fixed and exchanges the remaining coordinates. -/
def swapYZ : CFGTransfer Stage Stage where
  post s := (s.1, s.2.2, s.2.1)
  pullback s := (s.1, s.2.2, s.2.1)
  gc := by
    rintro ⟨x₁, x₂, x₃⟩ ⟨q₁, q₂, q₃⟩
    cases x₁ <;> cases x₂ <;> cases x₃ <;>
      cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Include the three-cycle to exercise both valid and invalid candidate invariants. -/
def loop (cyclic : Bool) : CFGTransfer Stage Stage :=
  if cyclic then Round4.loop true else swapYZ

/-- Finite expansion of guarded equivalence in the two-coordinate source domain. -/
theorem guarded_source_iff {Term Val : Type*} (eval : PreState → Term → Val)
    (p : PreState) (t₁ t₂ : Term) :
    GuardedEquiv eval p t₁ t₂ ↔
      ∀ x y : Bool, (x, y) ≤ p → eval (x, y) t₁ = eval (x, y) t₂ := by
  constructor
  · exact fun h x y hs => h (x, y) hs
  · rintro h ⟨x, y⟩ hs
    exact h x y hs

/-- Exact transported guard tables for both interpretations of the IR. -/
theorem upstream_guard_classification (p : PreState) :
    (GuardedEquiv (pullbackEval entry evalNat) p original middle ↔ p.2 = false) ∧
    (GuardedEquiv (pullbackEval entry evalBool) p original middle ↔ p.2 = false) := by
  simp only [guarded_source_iff]
  rcases p with ⟨x, y⟩
  cases x <;> cases y <;> decide

/-- The transported evaluators compute on the entry post-state, retaining source x. -/
theorem upstream_value_table (x y : Bool) :
    pullbackEval entry evalNat (x, y) original =
      (if y then 1 else 0) + (if x then 1 else 0) ∧
    pullbackEval entry evalNat (x, y) middle = (if x then 1 else 0) ∧
    pullbackEval entry evalBool (x, y) original = (y || x) ∧
    pullbackEval entry evalBool (x, y) middle = x := by
  cases x <;> cases y <;> decide

/-- All 64 pairs of downstream guards, retaining the stage-inclusion premise. -/
theorem finite_weaken (p q : Stage) :
    Forces p q → GuardedEquiv evalNat q original middle → GuardedEquiv evalNat p original middle := by
  rw [(nat_guard_classification q).1, (nat_guard_classification p).1]
  unfold Forces
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases p₁ <;> cases p₂ <;> cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Every downstream guard is tested against its transported source guard. -/
theorem finite_pullback (q : Stage) :
    GuardedEquiv evalNat q original middle →
      GuardedEquiv (pullbackEval entry evalNat) (entry.pullback q) original middle := by
  rw [(nat_guard_classification q).1, (upstream_guard_classification (entry.pullback q)).1]
  rcases q with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- All 32 source/target pairs for actual transferred term equality. -/
theorem finite_edge_synthesis (a : PreState) (q : Stage) :
    GuardedEquiv evalNat q original middle →
      evalNat (entry.post (a ⊓ synthesizeEdgeGuard entry a q)) original =
        evalNat (entry.post (a ⊓ synthesizeEdgeGuard entry a q)) middle := by
  rw [(nat_guard_classification q).1]
  rcases a with ⟨a₁, a₂⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases a₁ <;> cases a₂ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Both loops, every source/invariant/target, and all six depths 0 through 5. -/
theorem finite_hoist (cyclic : Bool) (a₀ : PreState) (inv q : Stage) :
    IsInductiveFor (loop cyclic) inv q → GuardedEquiv evalNat q original middle →
      Round6.ThroughFive (fun n =>
        evalNat ((entry.comp ((loop cyclic).iterate n)).post
          (a₀ ⊓ hoistLoopGuard entry a₀ inv)) original =
        evalNat ((entry.comp ((loop cyclic).iterate n)).post
          (a₀ ⊓ hoistLoopGuard entry a₀ inv)) middle) := by
  rw [(nat_guard_classification q).1]
  unfold IsInductiveFor IsLoopInvariant Round6.ThroughFive
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases cyclic <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- The edge guard is proper and nonbottom; it repairs a genuine downstream difference. -/
theorem interblock_active_witness :
    let a : PreState := (true, true)
    let g := synthesizeEdgeGuard entry a guardX
    let reached := entry.post (a ⊓ g)
    GuardedEquiv evalNat guardX original middle ∧
    GuardedEquiv (pullbackEval entry evalNat) (entry.pullback guardX) original middle ∧
    entry.pullback guardX = (true, false) ∧ g = (true, false) ∧
    reached = (false, false, true) ∧ evalNat reached original = 1 ∧ evalNat reached middle = 1 ∧
    evalBool reached original = true ∧ evalBool reached middle = true ∧
    evalNat (entry.post a) original ≠ evalNat (entry.post a) middle := by
  dsimp only
  simp only [guarded_cube_iff, guarded_source_iff]
  decide

/-- Source transport need not reflect equivalence: entry never reaches a stage with y=true. -/
theorem pullback_converse_fails :
    ¬ GuardedEquiv evalNat guardX middle optimized ∧
    GuardedEquiv (pullbackEval entry evalNat) (entry.pullback guardX) middle optimized := by
  simp only [guarded_cube_iff, guarded_source_iff]
  decide

/-- Reversing the guard-inclusion direction would incorrectly admit unrestricted stages. -/
theorem weakening_direction_matters :
    Forces guardX (⊤ : Stage) ∧ GuardedEquiv evalNat guardX original middle ∧
    ¬ GuardedEquiv evalNat ⊤ original middle := by
  simp only [guarded_cube_iff]
  unfold Forces
  decide

/-- A source stage permitted by the pullback guard must be evaluated through post. -/
theorem evaluator_direction_matters :
    let T := Round4.loop true
    let s : Stage := (false, true, false)
    Forces s (T.pullback guardX) ∧
    pullbackEval T evalNat s original = pullbackEval T evalNat s middle ∧
    evalNat (T.pullback s) original ≠ evalNat (T.pullback s) middle := by
  dsimp only
  unfold Forces
  decide

/-- Actual nonempty loop states alternate after the single preheader check. -/
theorem hoisted_state_trace :
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)
    IsInductiveFor swapYZ guardX guardX ∧ entered = (false, false, true) ∧
    (swapYZ.iterate 0).post entered = (false, false, true) ∧
    (swapYZ.iterate 1).post entered = (false, true, false) ∧
    (swapYZ.iterate 2).post entered = (false, false, true) ∧
    (swapYZ.iterate 5).post entered = (false, true, false) := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant
  decide

/-- Both interpretations admit this concrete rewrite for every natural iteration count. -/
theorem hoisted_rewrites_all_steps :
    ∀ n : ℕ,
      (evalNat ((entry.comp (swapYZ.iterate n)).post
        ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)) original =
       evalNat ((entry.comp (swapYZ.iterate n)).post
        ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)) middle) ∧
      (evalBool ((entry.comp (swapYZ.iterate n)).post
        ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)) original =
       evalBool ((entry.comp (swapYZ.iterate n)).post
        ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)) middle) := by
  intro n
  have hind : IsInductiveFor swapYZ guardX guardX := by
    unfold IsInductiveFor IsLoopInvariant
    decide
  exact ⟨hoisted_rewrite entry swapYZ evalNat (true, true) guardX guardX original middle
      hind ((nat_guard_classification guardX).1.mpr rfl) n,
    hoisted_rewrite entry swapYZ evalBool (true, true) guardX guardX original middle
      hind ((bool_guard_classification guardX).1.mpr rfl) n⟩

/-- Reversing entry/loop order changes a successful conditional rewrite into a failure. -/
theorem composition_order_matters :
    let E := Round4.loop true
    let g := hoistLoopGuard E (true, true, true) guardX
    g = (true, true, false) ∧
    evalNat ((E.comp swapYZ).post g) original = evalNat ((E.comp swapYZ).post g) middle ∧
    evalNat ((swapYZ.comp E).post g) original ≠ evalNat ((swapYZ.comp E).post g) middle := by
  dsimp only
  decide

/-- Entry establishes the rewrite condition, but a non-preserving loop can destroy it. -/
theorem preservation_required :
    let L := Round4.loop true
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)
    GuardedEquiv evalNat guardX original middle ∧ ¬ IsLoopInvariant L guardX ∧
    evalNat entered original = evalNat entered middle ∧
    evalNat (L.post entered) original ≠ evalNat (L.post entered) middle := by
  dsimp only
  simp only [guarded_cube_iff]
  unfold IsLoopInvariant
  decide

/-- A preserved invariant must also imply the rewrite condition. -/
theorem entailment_required :
    let inv : Stage := ⊤
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    IsLoopInvariant swapYZ inv ∧ ¬ Forces inv guardX ∧
    GuardedEquiv evalNat guardX original middle ∧
    evalNat entered original ≠ evalNat entered middle := by
  dsimp only
  simp only [guarded_cube_iff]
  unfold IsLoopInvariant Forces
  decide

/-- Inductivity by itself cannot supply an invalid term-equivalence premise. -/
theorem rewrite_equivalence_required :
    let inv : Stage := ⊤
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    IsInductiveFor swapYZ inv inv ∧ ¬ GuardedEquiv evalNat inv original middle ∧
    evalNat entered original ≠ evalNat entered middle := by
  dsimp only
  simp only [guarded_cube_iff]
  unfold IsInductiveFor IsLoopInvariant
  decide

end Round9

/-!
## Round 10: binary compositionality and diamond congruence

The definition and all four statements match the blueprint exactly.
`CompatibleOp2` supplies compositionality at each stage, for every operand
pair; the semantic combiner may depend on that stage. No associativity,
commutativity, or cross-stage law is required. Pullback-meet commutation
replaces equal guards, without assuming the evaluator preserves meets.
Diamond soundness establishes original/rewritten equality separately along
each path; it does not equate the values reached by different paths.

The concrete constructor is AST addition from Round 8, with both natural
addition and Boolean disjunction interpretations. The numeric congruence
test rewrites original -> middle in the left operand and middle -> optimized
in the right. At stage 001 both compound terms evaluate to 2, while at 111
they evaluate to 5 and 3. A syntax-sensitive operator demonstrates that the
compatibility premise is essential, and has no compatible semantic combiner.

The diamond paths have posts (x,z,false) and (y,z,z), with their respective
right adjoints. For target guard 011 and source 111, the individual guards
are 011 and 101 and their meet is the nonbottom stage 001. The paths reach
010 and 011. Addition congruence holds on both, with values 1 and 3, so the
within-path/cross-path distinction is observable. Independent numeric checks
cover 64 congruence guard pairs, 512 synthesis combinations, 128 pullback-meet
cases, and 64 diamond cases: 768 cases in total, plus explicit witnesses.
All proofs remain independent of the target placeholders and of choice.
-/

namespace Round10

/-- Independent congruence proof, applying both operand equalities at one stage. -/
theorem binary_congr {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hc : CompatibleOp2 eval op semOp)
    (h₁ : GuardedEquiv eval p₁ t₁ u₁) (h₂ : GuardedEquiv eval p₂ t₂ u₂) :
    GuardedEquiv eval (p₁ ⊓ p₂) (op t₁ t₂) (op u₁ u₂) := by
  intro s hs
  rw [hc s t₁ t₂, hc s u₁ u₂, h₁ s (hs.trans inf_le_left), h₂ s (hs.trans inf_le_right)]

/-- Independent synthesized congruence proof using the audited forcing equivalence. -/
theorem binary_synthesize {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (a p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hc : CompatibleOp2 eval op semOp)
    (h₁ : GuardedEquiv eval p₁ t₁ u₁) (h₂ : GuardedEquiv eval p₂ t₂ u₂) :
    eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) (op t₁ t₂) =
      eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) (op u₁ u₂) := by
  exact binary_congr eval op semOp p₁ p₂ t₁ u₁ t₂ u₂ hc h₁ h₂ _
    ((Round7.rewrite_chain a p₁ p₂ _).mpr le_rfl)

/-- Equal pulled-back guards give the same guarded-equivalence proposition. -/
theorem pullback_meet_commute {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (evalβ : β → Term → Val) (q₁ q₂ : β) (t₁ t₂ : Term) :
    GuardedEquiv (pullbackEval T evalβ) (T.pullback (q₁ ⊓ q₂)) t₁ t₂ ↔
      GuardedEquiv (pullbackEval T evalβ) (T.pullback q₁ ⊓ T.pullback q₂) t₁ t₂ := by
  rw [Round3.pullback_meet]

/-- Each path establishes c, so the downstream equivalence applies separately to both. -/
theorem diamond_rewrite {α γ Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra γ]
    (P₁ P₂ : CFGTransfer α γ) (evalγ : γ → Term → Val)
    (a : α) (c : γ) (t₁ t₂ : Term) (h : GuardedEquiv evalγ c t₁ t₂) :
    let g := synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c
    evalγ (P₁.post (a ⊓ g)) t₁ = evalγ (P₁.post (a ⊓ g)) t₂ ∧
      evalγ (P₂.post (a ⊓ g)) t₁ = evalγ (P₂.post (a ⊓ g)) t₂ := by
  exact ⟨h _ ((P₁.gc _ _).mpr (le_himp_iff'.mp inf_le_left)),
    h _ ((P₂.gc _ _).mpr (le_himp_iff'.mp inf_le_right))⟩

open Round8

/-- Compatibility of actual AST addition holds for every stage and operand syntax. -/
theorem addition_compatible : CompatibleOp2 evalNat IR.add (fun _ x y => x + y) := by
  intro s l r
  rfl

/-- The same constructor is compatible with its Boolean interpretation. -/
theorem or_compatible : CompatibleOp2 evalBool IR.add (fun _ x y => x || y) := by
  intro s l r
  rfl

def compoundBefore : IR := .add original middle
def compoundAfter : IR := .add middle optimized
def diamondBefore : IR := .add original (.add .zero .z)
def diamondAfter : IR := .add middle .z

/-- Nonidentity, nonconstant converging transfers with independent source restrictions. -/
def path (first : Bool) : CFGTransfer Stage Stage where
  post s := if first then (s.1, s.2.2, false) else (s.2.1, s.2.2, s.2.2)
  pullback q := if first then (q.1, true, q.2.1) else (true, q.1, q.2.1 && q.2.2)
  gc := by
    rintro ⟨s₁, s₂, s₃⟩ ⟨q₁, q₂, q₃⟩
    cases first <;> cases s₁ <;> cases s₂ <;> cases s₃ <;>
      cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Both directions of each path are nonidentity and nonconstant. -/
theorem paths_nontrivial (first : Bool) :
    (path first).post (false, true, false) ≠ (false, true, false) ∧
    (path first).pullback (false, false, false) ≠ (false, false, false) ∧
    (path first).post (false, false, false) ≠ (path first).post (true, true, true) ∧
    (path first).pullback (false, false, false) ≠ (path first).pullback (true, true, true) := by
  cases first <;> decide

/-- The right operand in the diamond example undergoes an actual zero-addition rewrite. -/
theorem zero_add_z_guard : GuardedEquiv evalNat guardX (.add .zero .z) .z := by
  rw [guarded_cube_iff]
  decide

/-- Construct the downstream diamond rewrite using binary compositionality. -/
theorem diamond_equivalence : GuardedEquiv evalNat guardX diamondBefore diamondAfter := by
  have h := binary_congr evalNat IR.add (fun _ x y => x + y) guardX guardX
    original middle (.add .zero .z) .z addition_compatible
    concrete_rewrites.1 zero_add_z_guard
  simpa only [inf_idem, diamondBefore, diamondAfter] using h

/-- Exact guard classification for the numeric two-operand congruence example. -/
theorem compound_guards (p : Stage) :
    GuardedEquiv evalNat p compoundBefore compoundAfter ↔ p.1 = false ∧ p.2.1 = false := by
  rw [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- Exact downstream guard classification for the diamond's compound terms. -/
theorem diamond_guards (p : Stage) :
    GuardedEquiv evalNat p diamondBefore diamondAfter ↔ p.1 = false := by
  rw [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- The two paths pull the downstream restriction back to different source coordinates. -/
theorem transported_guards (first : Bool) (p : Stage) :
    GuardedEquiv (pullbackEval (path first) evalNat) p diamondBefore diamondAfter ↔
      if first then p.1 = false else p.2.1 = false := by
  rw [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases first <;> cases x <;> cases y <;> cases z <;> decide

/-- All 64 operand-guard pairs, keeping the two rewrite premises separate. -/
theorem finite_congr (p q : Stage) :
    GuardedEquiv evalNat p original middle → GuardedEquiv evalNat q middle optimized →
      GuardedEquiv evalNat (p ⊓ q) compoundBefore compoundAfter := by
  rw [(nat_guard_classification p).1, (nat_guard_classification q).2.1, compound_guards]
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases p₁ <;> cases p₂ <;> cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- All 512 source/operand-guard/operand-guard synthesis cases. -/
theorem finite_synthesis (a p q : Stage) :
    GuardedEquiv evalNat p original middle → GuardedEquiv evalNat q middle optimized →
      evalNat (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) compoundBefore =
        evalNat (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) compoundAfter := by
  rw [(nat_guard_classification p).1, (nat_guard_classification q).2.1]
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases p₁ <;> cases p₂ <;>
    cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- All 128 path/target/target cases, computed independently of the general meet proof. -/
theorem finite_pullback_meet (first : Bool) (q₁ q₂ : Stage) :
    GuardedEquiv (pullbackEval (path first) evalNat) ((path first).pullback (q₁ ⊓ q₂))
      diamondBefore diamondAfter ↔
    GuardedEquiv (pullbackEval (path first) evalNat)
      ((path first).pullback q₁ ⊓ (path first).pullback q₂) diamondBefore diamondAfter := by
  simp only [transported_guards]
  rcases q₁ with ⟨u₁, u₂, u₃⟩
  rcases q₂ with ⟨v₁, v₂, v₃⟩
  cases first <;> cases u₁ <;> cases u₂ <;> cases u₃ <;>
    cases v₁ <;> cases v₂ <;> cases v₃ <;> decide

/-- All 64 source/target diamond cases for the compatible compound rewrite. -/
theorem finite_diamond (a c : Stage) :
    GuardedEquiv evalNat c diamondBefore diamondAfter →
      let g := synthesizeEdgeGuard (path true) a c ⊓ synthesizeEdgeGuard (path false) a c
      evalNat ((path true).post (a ⊓ g)) diamondBefore =
        evalNat ((path true).post (a ⊓ g)) diamondAfter ∧
      evalNat ((path false).post (a ⊓ g)) diamondBefore =
        evalNat ((path false).post (a ⊓ g)) diamondAfter := by
  rw [diamond_guards]
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases c with ⟨c₁, c₂, c₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases c₁ <;> cases c₂ <;> cases c₃ <;> decide

/-- Both operand rewrites hold on proper guards; the shared stage gives nonzero compound values. -/
theorem active_binary_witness :
    GuardedEquiv evalNat guardX original middle ∧ GuardedEquiv evalNat guardY middle optimized ∧
    GuardedEquiv evalNat (guardX ⊓ guardY) compoundBefore compoundAfter ∧
    evalNat (false, false, true) compoundBefore = 2 ∧
    evalNat (false, false, true) compoundAfter = 2 ∧
    evalNat (true, true, true) compoundBefore = 5 ∧
    evalNat (true, true, true) compoundAfter = 3 := by
  simp only [guarded_cube_iff]
  decide

/-- Neither single operand guard, nor their join, suffices for this numeric rewrite. -/
theorem both_operand_guards_required :
    ¬ GuardedEquiv evalNat guardX compoundBefore compoundAfter ∧
    ¬ GuardedEquiv evalNat guardY compoundBefore compoundAfter ∧
    ¬ GuardedEquiv evalNat (guardX ⊔ guardY) compoundBefore compoundAfter := by
  simp only [guarded_cube_iff]
  decide

/-- A syntax-sensitive constructor that cannot respect semantic equality of its operands. -/
def badOp (left _right : IR) : IR :=
  match left with
  | .add .x _ => .one
  | _ => .zero

/-- No semantic combiner can distinguish the identical operand values seen here. -/
theorem badOp_has_no_semantics (semOp : Stage → ℕ → ℕ → ℕ) :
    ¬ CompatibleOp2 evalNat badOp semOp := by
  intro h
  have h₁ := h (false, false, true) original .zero
  have h₂ := h (false, false, true) middle .zero
  change (1 : ℕ) = semOp (false, false, true) 1 0 at h₁
  change (0 : ℕ) = semOp (false, false, true) 1 0 at h₂
  have impossible : (1 : ℕ) = 0 := h₁.trans h₂.symm
  cases impossible

/-- Operand equivalences alone do not imply congruence for an incompatible constructor. -/
theorem compatibility_required :
    GuardedEquiv evalNat guardX original middle ∧
    GuardedEquiv evalNat ⊤ IR.zero IR.zero ∧
    ¬ GuardedEquiv evalNat (guardX ⊓ ⊤) (badOp original .zero) (badOp middle .zero) := by
  simp only [guarded_cube_iff]
  decide

/-- Both diamond guards are restrictive; both reached stages are nonbottom.
Each path preserves the rewrite, but their common per-path values are different. -/
theorem active_diamond_witness :
    let a : Stage := (true, true, true)
    let g₁ := synthesizeEdgeGuard (path true) a guardX
    let g₂ := synthesizeEdgeGuard (path false) a guardX
    let s₁ := (path true).post (a ⊓ (g₁ ⊓ g₂))
    let s₂ := (path false).post (a ⊓ (g₁ ⊓ g₂))
    g₁ = guardX ∧ g₂ = guardY ∧ g₁ ⊓ g₂ = (false, false, true) ∧
    s₁ = (false, true, false) ∧ s₂ = (false, true, true) ∧
    evalNat s₁ diamondBefore = 1 ∧ evalNat s₁ diamondAfter = 1 ∧
    evalNat s₂ diamondBefore = 3 ∧ evalNat s₂ diamondAfter = 3 ∧
    evalNat s₁ diamondBefore ≠ evalNat s₂ diamondBefore := by
  dsimp only
  decide

/-- Keeping just one path's guard makes the other path's rewrite fail. -/
theorem each_path_guard_required :
    (evalNat ((path true).post guardX) diamondBefore =
      evalNat ((path true).post guardX) diamondAfter ∧
     evalNat ((path false).post guardX) diamondBefore ≠
      evalNat ((path false).post guardX) diamondAfter) ∧
    (evalNat ((path true).post guardY) diamondBefore ≠
      evalNat ((path true).post guardY) diamondAfter ∧
     evalNat ((path false).post guardY) diamondBefore =
      evalNat ((path false).post guardY) diamondAfter) := by
  decide

end Round10

/-!
## Round 11: concrete imperative state transitions

The definition and all four statements match the blueprint. `stateTransfer`
uses existential image for postconditions and substitution for pullbacks.
The adjunction is constructive and requires neither an inverse transition
nor a chosen preimage. The pointwise invariant condition is ordinary Hoare
preservation for a total transition function. The final target still uses
a predicate-indexed evaluator, rather than evaluating one arbitrarily
selected state; total transitions and finite-iteration safety do not assert
termination.

The concrete state is (counter, divisor) : Nat × Nat. Entry initializes the
counter to zero, and the loop increments it while retaining the divisor.
The proper invariant is divisor > 0. From an unrestricted preheader, the
hoisted guard accepts precisely positive divisors and rejects zero. Exact
reachability is proved for every n: reached n (c,d) iff c=n and d>0.
In particular (n,1) is reachable for every n, so the safety evidence is never
based only on an empty set of reachable states.

The conditional rewrite is c + d/d -> c + 1. A collecting evaluator maps a
state predicate to the predicate of possible numeric results, using only
existential witnesses. It makes no representative-state selection. Both
terms have exactly the possible result n+1 after n iterations. Natural
division is total, and d=0 makes the two terms differ; a loop that decrements
the divisor demonstrates why preservation is necessary. All results and
the stateTransfer definition are checked without sorryAx or Classical.choice.
-/

namespace Round11

/-- Independent verification of weakest-precondition substitution. -/
theorem pullback_apply {S₁ S₂ : Type*} (step : S₁ → S₂) (Q : S₂ → Prop) (s₁ : S₁) :
    (stateTransfer step).pullback Q s₁ ↔ Q (step s₁) := by
  rfl

/-- Independent verification of pointwise residual-guard implication. -/
theorem edge_guard_apply {S₁ S₂ : Type*} (step : S₁ → S₂)
    (P : S₁ → Prop) (Q : S₂ → Prop) (s₁ : S₁) :
    synthesizeEdgeGuard (stateTransfer step) P Q s₁ ↔ (P s₁ → Q (step s₁)) := by
  rfl

/-- The image-based invariant condition is exactly pointwise preservation. -/
theorem invariant_iff {S : Type*} (step : S → S) (inv : S → Prop) :
    IsLoopInvariant (stateTransfer step) inv ↔ ∀ s, inv s → inv (step s) := by
  exact (stateTransfer step).gc inv inv

/-- Independent specialization of the audited loop-hoisted rewrite theorem. -/
theorem hoisted_equiv {S₀ S Term Val : Type*} (init : S₀ → S) (step : S → S)
    (eval : (S → Prop) → Term → Val) (a₀ : S₀ → Prop) (inv q : S → Prop) (t₁ t₂ : Term)
    (hind : IsInductiveFor (stateTransfer step) inv q) (heq : GuardedEquiv eval q t₁ t₂) :
    ∀ n : ℕ,
      eval (((stateTransfer init).comp ((stateTransfer step).iterate n)).post
        (a₀ ⊓ hoistLoopGuard (stateTransfer init) a₀ inv)) t₁ =
      eval (((stateTransfer init).comp ((stateTransfer step).iterate n)).post
        (a₀ ⊓ hoistLoopGuard (stateTransfer init) a₀ inv)) t₂ := by
  exact Round9.hoisted_rewrite (stateTransfer init) (stateTransfer step) eval a₀ inv q t₁ t₂ hind heq

/-- A many-to-one reset confirms existential, rather than universal, image semantics. -/
theorem reset_image (P : ℕ → Prop) (m : ℕ) :
    (stateTransfer (fun _ : ℕ => 0)).post P m ↔ m = 0 ∧ ∃ n, P n := by
  constructor
  · rintro ⟨n, hm, hp⟩
    exact ⟨hm.symm, n, hp⟩
  · rintro ⟨rfl, n, hp⟩
    exact ⟨n, rfl, hp⟩

abbrev State := ℕ × ℕ

def init (d : ℕ) : State := (0, d)
def step (s : State) : State := (s.1 + 1, s.2)
def initial (_ : ℕ) : Prop := True
def positive (s : State) : Prop := 0 < s.2

/-- The actual predicate reached after guarded entry and n loop iterations. -/
def reached (n : ℕ) : State → Prop :=
  ((stateTransfer init).comp ((stateTransfer step).iterate n)).post
    (initial ⊓ hoistLoopGuard (stateTransfer init) initial positive)

/-- The divisor is unchanged by the loop, so positivity is inductive. -/
theorem positive_invariant : IsLoopInvariant (stateTransfer step) positive := by
  exact (invariant_iff step positive).mpr (fun _ h => h)

theorem positive_inductive : IsInductiveFor (stateTransfer step) positive positive := by
  exact ⟨positive_invariant, fun _ h => h⟩

/-- The preheader guard is precisely the nonzero-divisor test. -/
theorem entry_guard (d : ℕ) :
    hoistLoopGuard (stateTransfer init) initial positive d ↔ 0 < d := by
  change (True → 0 < d) ↔ 0 < d
  exact ⟨fun h => h True.intro, fun hd _ => hd⟩

/-- The guard is satisfiable and restrictive. -/
theorem entry_guard_examples :
    hoistLoopGuard (stateTransfer init) initial positive 1 ∧
    hoistLoopGuard (stateTransfer init) initial positive 2 ∧
    ¬ hoistLoopGuard (stateTransfer init) initial positive 0 := by
  simp only [entry_guard]
  decide

/-- Counter-dependent postconditions detect the increment in the pullback. -/
theorem counter_pullback_examples :
    (stateTransfer step).pullback (fun s => s.1 = 2) (1, 3) ∧
    ¬ (stateTransfer step).pullback (fun s => s.1 = 2) (2, 3) := by
  change (1 + 1 = 2) ∧ ¬ (2 + 1 = 2)
  decide

/-- The edge guard is conditional on its source predicate, including false antecedents. -/
theorem edge_guard_examples :
    let P : State → Prop := fun s => s.1 = 0
    let Q : State → Prop := fun s => s.1 = 1 ∧ 0 < s.2
    ¬ synthesizeEdgeGuard (stateTransfer step) P Q (0, 0) ∧
    synthesizeEdgeGuard (stateTransfer step) P Q (0, 2) ∧
    synthesizeEdgeGuard (stateTransfer step) P Q (1, 0) := by
  change ¬ (0 = 0 → 1 = 1 ∧ 0 < 0) ∧
    (0 = 0 → 1 = 1 ∧ 0 < 2) ∧ (1 = 0 → 2 = 1 ∧ 0 < 0)
  decide

/-- Exact reachability, including zero iterations and all positive input divisors. -/
theorem reached_iff (n c d : ℕ) : reached n (c, d) ↔ c = n ∧ 0 < d := by
  induction n generalizing c d with
  | zero =>
    constructor
    · rintro ⟨e, hstate, hguard⟩
      have he : 0 < e := hguard.2 True.intro
      cases hstate
      exact ⟨rfl, he⟩
    · rintro ⟨rfl, hd⟩
      exact ⟨d, rfl, True.intro, fun _ => hd⟩
  | succ n ih =>
    change (∃ s, step s = (c, d) ∧ reached n s) ↔ c = n + 1 ∧ 0 < d
    constructor
    · rintro ⟨⟨p, e⟩, hs, hp⟩
      rcases (ih p e).mp hp with ⟨rfl, he⟩
      cases hs
      exact ⟨rfl, he⟩
    · rintro ⟨rfl, hd⟩
      exact ⟨(n, d), rfl, (ih n d).mpr ⟨rfl, hd⟩⟩

/-- A concrete state exists at every iteration count; the invariant is not vacuous. -/
theorem reached_nonempty (n : ℕ) : ∃ s, reached n s := by
  exact ⟨(n, 1), (reached_iff n n 1).mpr ⟨rfl, by decide⟩⟩

/-- Exact traces include both valid states and rejected counter/divisor combinations. -/
theorem reachability_examples :
    reached 0 (0, 2) ∧ reached 1 (1, 2) ∧ reached 4 (4, 2) ∧
    ¬ reached 2 (1, 2) ∧ ¬ reached 3 (3, 0) := by
  simp only [reached_iff]
  decide

/-- Two arithmetic IR expressions differing only by the guarded division simplification. -/
inductive CounterExpr where
  | withDivision
  | increment

def scalarEval (s : State) : CounterExpr → ℕ
  | .withDivision => s.1 + s.2 / s.2
  | .increment => s.1 + 1

/-- Collect possible values constructively, without choosing any representative state. -/
def collectEval (P : State → Prop) (t : CounterExpr) : ℕ → Prop :=
  fun v => ∃ s, P s ∧ scalarEval s t = v

/-- The ordinary state-level arithmetic rewrite is valid on positive divisors. -/
theorem scalar_rewrite (s : State) (h : positive s) :
    scalarEval s .withDivision = scalarEval s .increment := by
  change s.1 + s.2 / s.2 = s.1 + 1
  rw [Nat.div_self h]

/-- Statewise equality lifts to equality of collected results at every forcing predicate. -/
theorem guarded_division : GuardedEquiv collectEval positive .withDivision .increment := by
  intro P hP
  funext v
  apply propext
  constructor
  · rintro ⟨s, hs, hv⟩
    exact ⟨s, hs, (scalar_rewrite s (hP s hs)).symm.trans hv⟩
  · rintro ⟨s, hs, hv⟩
    exact ⟨s, hs, (scalar_rewrite s (hP s hs)).trans hv⟩

/-- Concrete non-vacuous instantiation of the full all-iteration rewrite target. -/
theorem hoisted_rewrite_all :
    ∀ n : ℕ, collectEval (reached n) .withDivision = collectEval (reached n) .increment := by
  exact hoisted_equiv init step collectEval initial positive positive
    .withDivision .increment positive_inductive guarded_division

/-- The original expression has exactly the result n+1 after n iterations. -/
theorem collected_result (n v : ℕ) :
    collectEval (reached n) .withDivision v ↔ v = n + 1 := by
  constructor
  · rintro ⟨⟨c, d⟩, hs, hv⟩
    rcases (reached_iff n c d).mp hs with ⟨hc, hd⟩
    subst c
    change n + d / d = v at hv
    rw [Nat.div_self hd] at hv
    exact hv.symm
  · rintro rfl
    exact ⟨(n, 1), (reached_iff n n 1).mpr ⟨rfl, by decide⟩,
      scalar_rewrite (n, 1) (by change 0 < 1; decide)⟩

/-- The optimized expression has the same exact result, not merely an empty result set. -/
theorem optimized_result (n v : ℕ) :
    collectEval (reached n) .increment v ↔ v = n + 1 := by
  rw [← hoisted_rewrite_all n]
  exact collected_result n v

/-- Both states and observable values genuinely change during the loop. -/
theorem result_examples :
    collectEval (reached 0) .withDivision 1 ∧
    collectEval (reached 4) .withDivision 5 ∧
    collectEval (reached 4) .increment 5 ∧
    ¬ collectEval (reached 4) .withDivision 1 := by
  simp only [collected_result, optimized_result]
  decide

/-- The unrestricted rewrite fails on a concrete singleton containing a zero divisor. -/
theorem zero_divisor_rejected :
    ¬ GuardedEquiv collectEval (fun _ => True) .withDivision .increment := by
  intro h
  have heq := h (fun s => s = (0, 0)) (fun _ _ => True.intro)
  have hv : collectEval (fun s => s = (0, 0)) .withDivision 0 :=
    ⟨(0, 0), rfl, by decide⟩
  have hw : collectEval (fun s => s = (0, 0)) .increment 0 := heq ▸ hv
  rcases hw with ⟨s, hs, hv⟩
  subst s
  change (1 : ℕ) = 0 at hv
  cases hv

/-- An intentionally invalid loop changes the divisor as well as the counter. -/
def badStep (s : State) : State := (s.1 + 1, s.2 - 1)

/-- Positivity would not be preserved by this different transition. -/
theorem bad_step_not_invariant : ¬ IsLoopInvariant (stateTransfer badStep) positive := by
  intro h
  have hb := (invariant_iff badStep positive).mp h (0, 1) (by change 0 < 1; decide)
  change 0 < 0 at hb
  cases hb

/-- A positive entry can pass the first iteration yet lose the rewrite after the second. -/
theorem bad_step_trace :
    let entered := init 2
    let first := badStep entered
    let second := badStep first
    hoistLoopGuard (stateTransfer init) initial positive 2 ∧
    first = (1, 1) ∧ second = (2, 0) ∧
    scalarEval first .withDivision = 2 ∧ scalarEval first .increment = 2 ∧
    scalarEval second .withDivision = 2 ∧ scalarEval second .increment = 3 := by
  dsimp only
  rw [entry_guard]
  decide

end Round11


/-!
## Milestone 1: Round 1 Gate 1 audit (historical contract)

Review artifact: reviews/M1-prelock.md. The original Round 1 obligations are constructively
satisfiable, but they permit the fixture-specific optimizer below. This is an
adversarial existence witness, not a proposed implementation of the compiler.
The exact benchmark/context combinations improve, while a renamed benchmark
remains unchanged. All compiler-dependent obligations are packaged together
in CompilerObligations; the three independent TCB bridge/compatibility
obligations are also proved here.

The tests reject a global identity pass, always-false synthesis, always-imp
synthesis, a false-guard fallback, in-context trap-to-UB changes, and dropping
a strict failing operand. They retain the original zero-divisor trap under
the unknown context, and exhibit real positive reductions at a satisfying
environment. Dynamic cost witnesses refer to the abstract IR observer;
the separate runtime traversal caveat is documented in the review.
No declaration here invokes a target compiler stub or target theorem.
-/

namespace M1

def nz : GuardIR := .nonZero (.var 0)
def fastBench : Expr :=
  .add (.uncheckedDiv (.pure (.var 1)) (.pure (.var 0))) (.pure (.var 2))
def guardedBench : Expr := .iteGuard nz fastBench m1BenchExpr

theorem fast_sound (env : Env) (h : env 0 ≠ 0) :
    evalExpr env fastBench = evalExpr env m1BenchExpr := by
  simp [fastBench, m1BenchExpr, evalExpr, evalPure, h, Int.mul_ediv_cancel]
theorem cancel_sound (env : Env) (h : env 0 ≠ 0) :
    evalExpr env (.pure (.var 1)) = evalExpr env m1CancelExpr := by
  simp [m1CancelExpr, evalExpr, evalPure, h, Int.mul_ediv_cancel]
theorem guarded_sound (env : Env) :
    evalExpr env guardedBench = evalExpr env m1BenchExpr := by
  by_cases h : env 0 = 0
  · simp [guardedBench, nz, m1BenchExpr, evalExpr, evalGuard, evalPure, h]
  · simp [guardedBench, nz, fastBench, m1BenchExpr, evalExpr, evalGuard, evalPure,
      h, Int.mul_ediv_cancel]
/-- A deliberately fixture-specific optimizer: every other expression is returned unchanged. -/
def opt (ctx : GuardIR) (e : Expr) : Expr :=
  if ctx = nz then
    if e = m1BenchExpr then fastBench
    else if e = m1CancelExpr then .pure (.var 1)
    else e
  else if ctx = .top ∧ e = m1BenchExpr then guardedBench else e
theorem opt_sound (ctx : GuardIR) (e : Expr) (env : Env)
    (hctx : evalGuard env ctx = true) :
    evalExpr env (opt ctx e) = evalExpr env e := by
  by_cases hc : ctx = nz
  · subst ctx
    have hn : env 0 ≠ 0 := by
      change decide (env 0 ≠ 0) = true at hctx
      exact of_decide_eq_true hctx
    by_cases hb : e = m1BenchExpr
    · subst e
      simpa [opt] using fast_sound env hn
    · by_cases hx : e = m1CancelExpr
      · subst e
        simpa [opt, hb] using cancel_sound env hn
      · simp [opt, hb, hx]
  · by_cases ht : ctx = .top ∧ e = m1BenchExpr
    · rcases ht with ⟨rfl, rfl⟩
      simpa [opt, nz] using guarded_sound env
    · simp [opt, hc, ht]

/-- Correct synthesis with only syntactic-equality discharge; other residuals remain implications. -/
def synth (a b : GuardIR) : GuardIR := if a = b then .top else .imp a b
theorem synth_eval (a b : GuardIR) (env : Env) :
    evalGuard env (synth a b) = ((!evalGuard env a) || evalGuard env b) := by
  unfold synth
  split
  · rename_i h
    subst b
    cases evalGuard env a <;> rfl
  · rfl
theorem synth_denote (a b : GuardIR) :
    denoteGuard (synth a b) = synthesizeGuard (denoteGuard a) (denoteGuard b) := by
  funext env
  apply propext
  change evalGuard env (synth a b) = true ↔ (evalGuard env a = true → evalGuard env b = true)
  rw [synth_eval]
  cases evalGuard env a <;> cases evalGuard env b <;> decide
theorem synth_universal (a b : GuardIR) (g : Env → Prop) :
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synth a b) := by
  rw [synth_denote]
  exact le_himp_iff'.symm
theorem synth_discharge (p : PureExpr) : synth (.nonZero p) (.nonZero p) = .top := by
  simp [synth]

theorem known_elim (env : Env) :
    checkedDivCount (opt nz m1BenchExpr) = 0 ∧
    guardBranchCount (opt nz m1BenchExpr) = 0 ∧ execCheckCost env (opt nz m1BenchExpr) = 0 := by
  by_cases h : env 0 = 0 <;>
    simp [opt, fastBench, checkedDivCount, guardBranchCount, execCheckCost, evalExpr, evalPure, h]
theorem cancel_elim : divOpCount (opt nz m1CancelExpr) = 0 := by
  decide
theorem unknown_dedup (env : Env) (h : env 0 ≠ 0) :
    execCheckCost env (opt .top m1BenchExpr) ≤ 1 ∧ execCheckCost env m1BenchExpr = 2 := by
  simp [opt, nz, guardedBench, fastBench, m1BenchExpr, execCheckCost, guardEvalCost,
    evalGuard, evalExpr, evalPure, h]
theorem zero_trap (env : Env) (h : env 0 = 0) :
    evalExpr env (opt .top m1BenchExpr) = .trap := by
  simp [opt, nz, guardedBench, m1BenchExpr, evalGuard, evalExpr, evalPure, h]

theorem lift_bridge {S Term Out : Type*} (run : S → Term → Out)
    (P : S → Prop) (t₁ t₂ : Term) :
    GuardedEquiv (liftEval run) P t₁ t₂ ↔ ∀ s, P s → run s t₁ = run s t₂ := by
  constructor
  · intro h s hs
    have he := h P le_rfl
    have hout : liftEval run P t₂ s (run s t₁) :=
      Eq.mp (congrFun (congrFun he s) (run s t₁)) ⟨hs, rfl⟩
    exact hout.2.symm
  · intro h Q hQP
    funext s out
    apply propext
    constructor
    · rintro ⟨hs, he⟩
      exact ⟨hs, (h s (hQP s hs)).symm.trans he⟩
    · rintro ⟨hs, he⟩
      exact ⟨hs, (h s (hQP s hs)).trans he⟩

theorem lift_binary_compatible {Term : Type*} (run : Env → Term → Outcome)
    (op : Term → Term → Term) (f : Int → Int → Outcome)
    (hop : ∀ env l r, run env (op l r) = bindOutcome2 f (run env l) (run env r)) :
    CompatibleOp2 (liftEval run) op (liftBinarySem f) := by
  intro P l r
  funext env out
  apply propext
  constructor
  · rintro ⟨hp, he⟩
    exact ⟨run env l, run env r, ⟨hp, rfl⟩, ⟨hp, rfl⟩, (hop env l r).symm.trans he⟩
  · rintro ⟨o₁, o₂, ⟨hp, h₁⟩, ⟨_, h₂⟩, he⟩
    refine ⟨hp, ?_⟩
    rw [hop, h₁, h₂]
    exact he

theorem addition_compatible :
    CompatibleOp2 (liftEval evalExpr) Expr.add (liftBinarySem (fun x y => .val (x + y))) := by
  exact lift_binary_compatible evalExpr Expr.add _ (fun _ _ _ => rfl)
theorem checked_division_compatible :
    CompatibleOp2 (liftEval evalExpr) Expr.checkedDiv
      (liftBinarySem (fun x y => if y = 0 then .trap else .val (x / y))) := by
  exact lift_binary_compatible evalExpr Expr.checkedDiv _ (fun _ _ _ => rfl)

theorem opt_guarded (ctx : GuardIR) (e : Expr) :
    GuardedEquiv (liftEval evalExpr) (denoteGuard ctx) (opt ctx e) e := by
  exact (lift_bridge evalExpr (denoteGuard ctx) (opt ctx e) e).mpr (opt_sound ctx e)

/-- The same benchmark shape with renamed variables, outside the candidate's exact fixtures. -/
def renamedBench : Expr :=
  .add
    (.checkedDiv (.pure (.var 2)) (.pure (.var 3)))
    (.checkedDiv (.mul (.pure (.var 4)) (.pure (.var 3))) (.pure (.var 3)))
theorem renamed_untouched :
    opt (.nonZero (.var 3)) renamedBench = renamedBench := by
  decide
theorem renamed_still_checks :
    checkedDivCount (opt (.nonZero (.var 3)) renamedBench) = 2 := by
  decide


theorem unsimplified_top_residual (p : PureExpr) :
    synth .top (.nonZero p) = .imp .top (.nonZero p) := by
  rfl

/-- The nine original Round 1 compiler obligations, before the parametric revision.
The bridge and the two compatibility obligations are proved independently above. -/
structure CompilerObligations
    (synthFn : GuardIR → GuardIR → GuardIR) (optFn : GuardIR → Expr → Expr) : Prop where
  guardDenote : ∀ a b, denoteGuard (synthFn a b) = synthesizeGuard (denoteGuard a) (denoteGuard b)
  universal : ∀ a b (g : Env → Prop),
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synthFn a b)
  selfDischarge : ∀ p, synthFn (.nonZero p) (.nonZero p) = .top
  guarded : ∀ ctx e, GuardedEquiv (liftEval evalExpr) (denoteGuard ctx) (optFn ctx e) e
  sound : ∀ ctx e env, evalGuard env ctx = true → evalExpr env (optFn ctx e) = evalExpr env e
  known : ∀ env, checkedDivCount (optFn (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
    guardBranchCount (optFn (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
    execCheckCost env (optFn (.nonZero (.var 0)) m1BenchExpr) = 0
  cancel : divOpCount (optFn (.nonZero (.var 0)) m1CancelExpr) = 0
  dedup : ∀ env, env 0 ≠ 0 →
    execCheckCost env (optFn .top m1BenchExpr) ≤ 1 ∧ execCheckCost env m1BenchExpr = 2
  trap : ∀ env, env 0 = 0 → evalExpr env (optFn .top m1BenchExpr) = .trap

theorem candidate_obligations : CompilerObligations synth opt where
  guardDenote := synth_denote
  universal := synth_universal
  selfDischarge := synth_discharge
  guarded := opt_guarded
  sound := opt_sound
  known := known_elim
  cancel := cancel_elim
  dedup := unknown_dedup
  trap := zero_trap

theorem compiler_obligations_satisfiable :
    ∃ (synthFn : GuardIR → GuardIR → GuardIR) (optFn : GuardIR → Expr → Expr),
      CompilerObligations synthFn optFn := by
  exact ⟨synth, opt, candidate_obligations⟩

def positiveEnv : Env := fun v => if v = 0 then 2 else if v = 1 then 7 else 3
def zeroEnv : Env := fun _ => 0

theorem positive_reduction_witness :
    evalGuard positiveEnv nz = true ∧
    evalExpr positiveEnv m1BenchExpr = .val 6 ∧
    evalExpr positiveEnv (opt nz m1BenchExpr) = .val 6 ∧
    evalExpr positiveEnv (opt .top m1BenchExpr) = .val 6 ∧
    execCheckCost positiveEnv m1BenchExpr = 2 ∧
    execCheckCost positiveEnv (opt nz m1BenchExpr) = 0 ∧
    execCheckCost positiveEnv (opt .top m1BenchExpr) = 1 := by
  decide

theorem zero_trap_witness :
    evalGuard zeroEnv nz = false ∧
    evalExpr zeroEnv m1BenchExpr = .trap ∧
    evalExpr zeroEnv (opt .top m1BenchExpr) = .trap ∧
    execCheckCost zeroEnv m1BenchExpr = 1 ∧
    execCheckCost zeroEnv (opt .top m1BenchExpr) = 2 := by
  decide

/-- Undefined behavior outside a false optimization context is not ruled out by contextual soundness. -/
theorem outside_context_ub :
    evalGuard zeroEnv nz = false ∧ evalExpr zeroEnv (opt nz m1BenchExpr) = .ub := by
  decide

theorem identity_rejected (synthFn : GuardIR → GuardIR → GuardIR) :
    ¬ CompilerObligations synthFn (fun _ e => e) := by
  intro h
  have bad := (h.known zeroEnv).1
  change (2 : ℕ) = 0 at bad
  cases bad

theorem constant_bot_rejected (optFn : GuardIR → Expr → Expr) :
    ¬ CompilerObligations (fun _ _ => .bot) optFn := by
  intro h
  have he := congrFun (h.guardDenote .top .top) zeroEnv
  have hb : denoteGuard .bot zeroEnv := Eq.mpr he (fun _ => rfl)
  change false = true at hb
  cases hb

theorem raw_imp_rejected (optFn : GuardIR → Expr → Expr) :
    ¬ CompilerObligations GuardIR.imp optFn := by
  intro h
  have bad := h.selfDischarge (.var 0)
  cases bad

theorem false_fallback_still_checks :
    checkedDivCount (.iteGuard .bot fastBench m1BenchExpr) = 2 ∧
    guardBranchCount (.iteGuard .bot fastBench m1BenchExpr) = 1 ∧
    execCheckCost positiveEnv (.iteGuard .bot fastBench m1BenchExpr) = 2 := by
  decide

def trapExpr : Expr := .checkedDiv (.pure (.lit 1)) (.pure (.lit 0))
def ubExpr : Expr := .uncheckedDiv (.pure (.lit 1)) (.pure (.lit 0))
def zeroExpr : Expr := .pure (.lit 0)

theorem strict_outcomes :
    evalExpr zeroEnv (.mul zeroExpr trapExpr) = .trap ∧
    evalExpr zeroEnv (.mul zeroExpr ubExpr) = .ub ∧
    evalExpr zeroEnv (.add trapExpr ubExpr) = .trap ∧
    evalExpr zeroEnv (.add ubExpr trapExpr) = .ub ∧
    evalExpr zeroEnv (.iteGuard .bot ubExpr (.pure (.lit 7))) = .val 7 := by
  decide

theorem short_circuit_costs :
    execCheckCost zeroEnv (.add trapExpr trapExpr) = 1 ∧
    execCheckCost zeroEnv (.add ubExpr trapExpr) = 0 ∧
    execCheckCost zeroEnv (.checkedDiv (.pure (.lit 1)) trapExpr) = 1 ∧
    execCheckCost zeroEnv (.iteGuard .bot ubExpr (.pure (.lit 7))) = 0 := by
  decide

theorem guard_short_circuit :
    evalGuard zeroEnv (.imp nz .bot) = true ∧
    evalGuard positiveEnv (.imp nz .bot) = false ∧
    guardEvalCost positiveEnv (.conj .bot nz) = 0 ∧
    guardEvalCost positiveEnv (.imp .bot nz) = 0 ∧
    guardEvalCost positiveEnv (.imp .top nz) = 1 ∧
    guardEvalCost positiveEnv (.conj nz (.eq (.var 1) (.var 2))) = 2 ∧
    guardEvalCost zeroEnv (.conj nz (.eq (.var 1) (.var 2))) = 1 := by
  decide

theorem trap_to_ub_rejected :
    ¬ GuardedEquiv (liftEval evalExpr) (denoteGuard .top) trapExpr ubExpr := by
  intro h
  have bad := (lift_bridge evalExpr (denoteGuard .top) trapExpr ubExpr).mp h zeroEnv rfl
  cases bad

theorem dropping_strict_operand_rejected :
    ¬ GuardedEquiv (liftEval evalExpr) (denoteGuard .top) (.mul zeroExpr trapExpr) zeroExpr := by
  intro h
  have bad := (lift_bridge evalExpr (denoteGuard .top) (.mul zeroExpr trapExpr) zeroExpr).mp h zeroEnv rfl
  cases bad

theorem integer_division_scope :
    evalExpr zeroEnv (.checkedDiv (.pure (.lit (-3))) (.pure (.lit 2))) = .val (-2) := by
  decide

end M1


/-!
## Milestone 1: Round 2 pre-lock re-review

The original fixture-only M1.opt is preserved above as a historical witness.
The strengthened parametric contract below rejects it independently of the
guard synthesizer. The new synthesizer normalizes the required residual forms,
and the optimizer recursively rewrites arbitrary expression subtrees under
known nonzero contexts. Its top-context rule recognizes a shared-divisor
shape over arbitrary PureExpr operands, not fixed benchmark names/variables.
UpdatedObligations packages every original and new compiler-dependent law;
the independent lifting/compatibility obligations remain proved in M1.

The candidate is total and computable, with direct semantic and capability
proofs. The renamed/compound/nested examples have satisfying contexts and
real outcome/check reductions. No target compiler or theorem stub is invoked.
The source's final command audits all named RedTeam declarations and the
imported Defs module transitively, fails on forbidden dependencies, and emits
the records consumed by scripts/check_axioms.py.
-/

namespace M1R2

def hasNZ (ctx : GuardIR) (p : PureExpr) : Bool :=
  match ctx with
  | .nonZero q => decide (q = p)
  | .conj l r => hasNZ l p || hasNZ r p
  | _ => false

theorem hasNZ_sound (ctx : GuardIR) (p : PureExpr) (env : Env) :
    hasNZ ctx p = true → evalGuard env ctx = true → evalPure env p ≠ 0 := by
  induction ctx with
  | top => simp [hasNZ]
  | bot => simp [hasNZ]
  | eq l r => simp [hasNZ]
  | imp l r _ _ => simp [hasNZ]
  | nonZero q =>
    intro h hc
    have heq : q = p := of_decide_eq_true h
    subst q
    exact of_decide_eq_true hc
  | conj l r ihl ihr =>
    intro h hc
    simp only [hasNZ, Bool.or_eq_true] at h
    simp only [evalGuard, Bool.and_eq_true] at hc
    rcases h with hl | hr
    · exact ihl hl hc.1
    · exact ihr hr hc.2

@[simp] theorem hasNZ_self (p : PureExpr) : hasNZ (.nonZero p) p = true := by
  simp [hasNZ]
@[simp] theorem hasNZ_left (p : PureExpr) (rest : GuardIR) :
    hasNZ (.conj (.nonZero p) rest) p = true := by
  simp [hasNZ]
@[simp] theorem hasNZ_right (rest : GuardIR) (p : PureExpr) :
    hasNZ (.conj rest (.nonZero p)) p = true := by
  simp [hasNZ]
def shrink (b : GuardIR) : GuardIR :=
  match b with
  | .conj l r => if l = r then l else .conj l r
  | _ => b

theorem shrink_eval (b : GuardIR) (env : Env) : evalGuard env (shrink b) = evalGuard env b := by
  cases b <;> try rfl
  rename_i l r
  by_cases h : l = r
  · subst r
    simp [shrink, evalGuard]
  · simp [shrink, h]

def synthNZ (a : GuardIR) (p : PureExpr) : GuardIR :=
  if hasNZ a p then .top else .imp a (.nonZero p)

theorem synthNZ_eval (a : GuardIR) (p : PureExpr) (env : Env) :
    evalGuard env (synthNZ a p) = ((!evalGuard env a) || evalGuard env (.nonZero p)) := by
  unfold synthNZ
  split
  · rename_i h
    cases ha : evalGuard env a with
    | false => rfl
    | true =>
      have hp := hasNZ_sound a p env h ha
      simp [evalGuard, hp]
  · rfl

def synth (a b : GuardIR) : GuardIR :=
  match a, b with
  | .bot, _ => .top
  | _, .top => .top
  | .top, _ => shrink b
  | _, .nonZero p => synthNZ a p
  | _, _ => .imp a b

theorem synth_eval (a b : GuardIR) (env : Env) :
    evalGuard env (synth a b) = ((!evalGuard env a) || evalGuard env b) := by
  cases a <;> cases b <;> simp [synth, shrink_eval, synthNZ_eval, evalGuard]

theorem synth_denote (a b : GuardIR) :
    denoteGuard (synth a b) = synthesizeGuard (denoteGuard a) (denoteGuard b) := by
  funext env
  apply propext
  change evalGuard env (synth a b) = true ↔ (evalGuard env a = true → evalGuard env b = true)
  rw [synth_eval]
  cases evalGuard env a <;> cases evalGuard env b <;> decide

theorem synth_universal (a b : GuardIR) (g : Env → Prop) :
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synth a b) := by
  rw [synth_denote]
  exact le_himp_iff'.symm

theorem synth_self (p : PureExpr) : synth (.nonZero p) (.nonZero p) = .top := by
  simp [synth, synthNZ]
theorem synth_top_right (a : GuardIR) : synth a .top = .top := by
  cases a <;> rfl
theorem synth_bot_left (b : GuardIR) : synth .bot b = .top := by
  rfl
theorem synth_top_left_nonZero (p : PureExpr) : synth .top (.nonZero p) = .nonZero p := by
  rfl
theorem synth_conj_left (p : PureExpr) (rest : GuardIR) :
    synth (.conj (.nonZero p) rest) (.nonZero p) = .top := by
  simp [synth, synthNZ]
theorem synth_conj_right (rest : GuardIR) (p : PureExpr) :
    synth (.conj rest (.nonZero p)) (.nonZero p) = .top := by
  simp [synth, synthNZ]
theorem synth_dedup (p : PureExpr) :
    synth .top (.conj (.nonZero p) (.nonZero p)) = .nonZero p := by
  simp [synth, shrink]
/-- Simplify checked division with a pure denominator known nonzero in context. -/
def smartDiv (ctx : GuardIR) (num div : Expr) : Expr :=
  match num, div with
  | .mul (.pure x) (.pure y), .pure d =>
    if hasNZ ctx d then
      if y = d then .pure x
      else if x = d then .pure y
      else .uncheckedDiv num div
    else .checkedDiv num div
  | _, .pure d => if hasNZ ctx d then .uncheckedDiv num div else .checkedDiv num div
  | _, _ => .checkedDiv num div

theorem smartDiv_sound (ctx : GuardIR) (num div : Expr) (env : Env)
    (hc : evalGuard env ctx = true) :
    evalExpr env (smartDiv ctx num div) = evalExpr env (.checkedDiv num div) := by
  unfold smartDiv
  split
  · rename_i x y d
    split
    · rename_i hn
      have hd := hasNZ_sound ctx d env hn hc
      split
      · rename_i hy
        subst y
        simp [evalExpr, hd, Int.mul_ediv_cancel]
      · split
        · rename_i hx
          subst x
          simp [evalExpr, hd, Int.mul_comm, Int.mul_ediv_cancel]
        · simp [evalExpr, hd]
    · rfl
  · rename_i num' div' d hnum
    split
    · rename_i hn
      have hd := hasNZ_sound ctx d env hn hc
      simp [evalExpr, hd]
    · rfl
  · rfl


/-- Recursive optimizer for arbitrary expression subtrees under a known context. -/
def core (ctx : GuardIR) : Expr → Expr
  | .pure p => .pure p
  | .add l r => .add (core ctx l) (core ctx r)
  | .sub l r => .sub (core ctx l) (core ctx r)
  | .mul l r => .mul (core ctx l) (core ctx r)
  | .checkedDiv l r => smartDiv ctx (core ctx l) (core ctx r)
  | .uncheckedDiv l r => .uncheckedDiv (core ctx l) (core ctx r)
  | .iteGuard g t f => .iteGuard g (core ctx t) (core ctx f)

theorem core_sound (ctx : GuardIR) (e : Expr) (env : Env)
    (hc : evalGuard env ctx = true) : evalExpr env (core ctx e) = evalExpr env e := by
  induction e with
  | pure p => rfl
  | add l r ihl ihr => simp only [core, evalExpr, ihl, ihr]
  | sub l r ihl ihr => simp only [core, evalExpr, ihl, ihr]
  | mul l r ihl ihr => simp only [core, evalExpr, ihl, ihr]
  | uncheckedDiv l r ihl ihr => simp only [core, evalExpr, ihl, ihr]
  | checkedDiv l r ihl ihr =>
    simp only [core]
    rw [smartDiv_sound ctx _ _ env hc]
    simp only [evalExpr, ihl, ihr]
  | iteGuard g t f iht ihf => simp only [core, evalExpr, iht, ihf]

theorem smartDiv_top (num div : Expr) :
    smartDiv .top num div = .checkedDiv num div := by
  unfold smartDiv
  split <;> simp [hasNZ]

theorem core_top (e : Expr) : core .top e = e := by
  induction e with
  | pure p => rfl
  | add l r ihl ihr => simp [core, ihl, ihr]
  | sub l r ihl ihr => simp [core, ihl, ihr]
  | mul l r ihl ihr => simp [core, ihl, ihr]
  | checkedDiv l r ihl ihr => simp [core, ihl, ihr, smartDiv_top]
  | uncheckedDiv l r ihl ihr => simp [core, ihl, ihr]
  | iteGuard g t f iht ihf => simp [core, iht, ihf]


def fastDual (x y d : PureExpr) : Expr :=
  .add (.uncheckedDiv (.pure x) (.pure d)) (.pure y)
def guardedDual (x y d : PureExpr) : Expr :=
  .iteGuard (.nonZero d) (fastDual x y d) (mkDualDivExpr x y d)

theorem fastDual_sound (x y d : PureExpr) (env : Env) (hd : evalPure env d ≠ 0) :
    evalExpr env (fastDual x y d) = evalExpr env (mkDualDivExpr x y d) := by
  simp [fastDual, mkDualDivExpr, evalExpr, hd, Int.mul_ediv_cancel]
theorem guardedDual_sound (x y d : PureExpr) (env : Env) :
    evalExpr env (guardedDual x y d) = evalExpr env (mkDualDivExpr x y d) := by
  by_cases hd : evalPure env d = 0
  · simp [guardedDual, evalExpr, evalGuard, hd]
  · simp [guardedDual, evalExpr, evalGuard, hd, fastDual_sound x y d env hd]

/-- Share one residual check across arbitrary pure operands with the same divisor. -/
def topPass (e : Expr) : Expr :=
  match e with
  | .add (.checkedDiv (.pure x) (.pure d₁))
      (.checkedDiv (.mul (.pure y) (.pure d₂)) (.pure d₃)) =>
      if d₁ = d₂ ∧ d₂ = d₃ then guardedDual x y d₁ else e
  | _ => e

theorem topPass_sound (e : Expr) (env : Env) :
    evalExpr env (topPass e) = evalExpr env e := by
  unfold topPass
  split
  · rename_i x d₁ y d₂ d₃
    split
    · rename_i hd
      rcases hd with ⟨h₁₂, h₂₃⟩
      subst d₂
      subst d₃
      exact guardedDual_sound x y d₁ env
    · rfl
  · rfl

/-- Total computable optimizer; rules contain no fixed variable identifiers or benchmark constants. -/
def opt (ctx : GuardIR) (e : Expr) : Expr :=
  if ctx = .top then topPass e else core ctx e

theorem opt_sound (ctx : GuardIR) (e : Expr) (env : Env)
    (hc : evalGuard env ctx = true) : evalExpr env (opt ctx e) = evalExpr env e := by
  unfold opt
  split
  · exact topPass_sound e env
  · exact core_sound ctx e env hc

theorem opt_top_dual (x y d : PureExpr) :
    opt .top (mkDualDivExpr x y d) = guardedDual x y d := by
  simp [opt, topPass, mkDualDivExpr]


theorem core_pure_div (ctx : GuardIR) (num d : PureExpr) (hn : hasNZ ctx d = true) :
    core ctx (.checkedDiv (.pure num) (.pure d)) = .uncheckedDiv (.pure num) (.pure d) := by
  simp [core, smartDiv, hn]

theorem core_cancel_right (ctx : GuardIR) (x d : PureExpr) (hn : hasNZ ctx d = true) :
    core ctx (mkCancelExpr x d) = .pure x := by
  simp [core, smartDiv, mkCancelExpr, hn]

theorem opt_known_dual (x y d : PureExpr) :
    opt (.nonZero d) (mkDualDivExpr x y d) = fastDual x y d := by
  simp [opt, mkDualDivExpr, core, smartDiv, fastDual]

theorem elim_checkedDiv_param (num d : PureExpr) (extra : GuardIR) (env : Env) :
    checkedDivCount (opt (.nonZero d) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    checkedDivCount (opt (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    checkedDivCount (opt (.conj extra (.nonZero d)) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    guardBranchCount (opt (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    execCheckCost env (opt (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 := by
  simp [opt, core_pure_div, checkedDivCount, guardBranchCount, execCheckCost, evalExpr]

theorem known_ctx_elim_param (x y d : PureExpr) (env : Env) :
    checkedDivCount (opt (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
    guardBranchCount (opt (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
    execCheckCost env (opt (.nonZero d) (mkDualDivExpr x y d)) = 0 := by
  rw [opt_known_dual]
  by_cases hd : evalPure env d = 0 <;>
    simp [fastDual, checkedDivCount, guardBranchCount, execCheckCost, evalExpr, hd]

theorem unknown_ctx_dedup_param (x y d : PureExpr) (env : Env) (hd : evalPure env d ≠ 0) :
    execCheckCost env (opt .top (mkDualDivExpr x y d)) ≤ 1 ∧
    execCheckCost env (mkDualDivExpr x y d) = 2 := by
  rw [opt_top_dual]
  simp [guardedDual, fastDual, mkDualDivExpr, execCheckCost, guardEvalCost, evalGuard, evalExpr, hd]

theorem zero_div_trap_param (x y d : PureExpr) (env : Env) (hd : evalPure env d = 0) :
    evalExpr env (opt .top (mkDualDivExpr x y d)) = .trap := by
  rw [opt_top_dual]
  simp [guardedDual, mkDualDivExpr, evalExpr, evalGuard, hd]


theorem opt_guarded (ctx : GuardIR) (e : Expr) :
    GuardedEquiv (liftEval evalExpr) (denoteGuard ctx) (opt ctx e) e := by
  intro P hP
  funext env out
  apply propext
  constructor
  · rintro ⟨hp, ho⟩
    exact ⟨hp, (opt_sound ctx e env (hP env hp)).symm.trans ho⟩
  · rintro ⟨hp, ho⟩
    exact ⟨hp, (opt_sound ctx e env (hP env hp)).trans ho⟩

theorem known_ctx_elim (env : Env) :
    checkedDivCount (opt (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
    guardBranchCount (opt (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
    execCheckCost env (opt (.nonZero (.var 0)) m1BenchExpr) = 0 := by
  exact known_ctx_elim_param (.var 1) (.var 2) (.var 0) env
theorem unknown_ctx_dedup (env : Env) (h : env 0 ≠ 0) :
    execCheckCost env (opt .top m1BenchExpr) ≤ 1 ∧ execCheckCost env m1BenchExpr = 2 := by
  exact unknown_ctx_dedup_param (.var 1) (.var 2) (.var 0) env h
theorem zero_div_trap (env : Env) (h : env 0 = 0) :
    evalExpr env (opt .top m1BenchExpr) = .trap := by
  exact zero_div_trap_param (.var 1) (.var 2) (.var 0) env h


theorem core_cancel_left (x d : PureExpr) :
    core (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d)) = .pure x := by
  by_cases hx : x = d
  · subst x
    simp [core, smartDiv]
  · simp [core, smartDiv, hx]

theorem cancel_div_param (x d : PureExpr) :
    divOpCount (opt (.nonZero d) (mkCancelExpr x d)) = 0 ∧
    divOpCount (opt (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d))) = 0 := by
  simp [opt, core_cancel_right, core_cancel_left, divOpCount]

theorem compositional_binary (d : PureExpr) (e₁ e₂ : Expr)
    (h₁ : checkedDivCount (opt (.nonZero d) e₁) = 0 ∧
      guardBranchCount (opt (.nonZero d) e₁) = 0)
    (h₂ : checkedDivCount (opt (.nonZero d) e₂) = 0 ∧
      guardBranchCount (opt (.nonZero d) e₂) = 0) :
    checkedDivCount (opt (.nonZero d) (.add e₁ e₂)) = 0 ∧
    checkedDivCount (opt (.nonZero d) (.sub e₁ e₂)) = 0 ∧
    checkedDivCount (opt (.nonZero d) (.mul e₁ e₂)) = 0 := by
  simp [opt] at h₁ h₂
  simp [opt, core, checkedDivCount, h₁.1, h₂.1]

theorem cancel_div : divOpCount (opt (.nonZero (.var 0)) m1CancelExpr) = 0 := by
  exact (cancel_div_param (.var 1) (.var 0)).1


/-- Every compiler-dependent obligation in the revised M1 interface, including the original contract. -/
structure UpdatedObligations
    (synthFn : GuardIR → GuardIR → GuardIR) (optFn : GuardIR → Expr → Expr) : Prop where
  original : M1.CompilerObligations synthFn optFn
  topRight : ∀ a, synthFn a .top = .top
  botLeft : ∀ b, synthFn .bot b = .top
  topLeftNZ : ∀ p, synthFn .top (.nonZero p) = .nonZero p
  dischargeLeft : ∀ p rest, synthFn (.conj (.nonZero p) rest) (.nonZero p) = .top
  dischargeRight : ∀ rest p, synthFn (.conj rest (.nonZero p)) (.nonZero p) = .top
  dedupConj : ∀ p, synthFn .top (.conj (.nonZero p) (.nonZero p)) = .nonZero p
  elimParam : ∀ num d extra env,
    checkedDivCount (optFn (.nonZero d) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    checkedDivCount (optFn (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    checkedDivCount (optFn (.conj extra (.nonZero d)) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    guardBranchCount (optFn (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    execCheckCost env (optFn (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0
  cancelParam : ∀ x d,
    divOpCount (optFn (.nonZero d) (mkCancelExpr x d)) = 0 ∧
    divOpCount (optFn (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d))) = 0
  compositional : ∀ d e₁ e₂,
    (checkedDivCount (optFn (.nonZero d) e₁) = 0 ∧ guardBranchCount (optFn (.nonZero d) e₁) = 0) →
    (checkedDivCount (optFn (.nonZero d) e₂) = 0 ∧ guardBranchCount (optFn (.nonZero d) e₂) = 0) →
    checkedDivCount (optFn (.nonZero d) (.add e₁ e₂)) = 0 ∧
    checkedDivCount (optFn (.nonZero d) (.sub e₁ e₂)) = 0 ∧
    checkedDivCount (optFn (.nonZero d) (.mul e₁ e₂)) = 0
  knownParam : ∀ x y d env,
    checkedDivCount (optFn (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
    guardBranchCount (optFn (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
    execCheckCost env (optFn (.nonZero d) (mkDualDivExpr x y d)) = 0
  dedupParam : ∀ x y d env, evalPure env d ≠ 0 →
    execCheckCost env (optFn .top (mkDualDivExpr x y d)) ≤ 1 ∧
    execCheckCost env (mkDualDivExpr x y d) = 2
  trapParam : ∀ x y d env, evalPure env d = 0 →
    evalExpr env (optFn .top (mkDualDivExpr x y d)) = .trap

theorem original_obligations : M1.CompilerObligations synth opt where
  guardDenote := synth_denote
  universal := synth_universal
  selfDischarge := synth_self
  guarded := opt_guarded
  sound := opt_sound
  known := known_ctx_elim
  cancel := cancel_div
  dedup := unknown_ctx_dedup
  trap := zero_div_trap

theorem all_obligations : UpdatedObligations synth opt where
  original := original_obligations
  topRight := synth_top_right
  botLeft := synth_bot_left
  topLeftNZ := synth_top_left_nonZero
  dischargeLeft := synth_conj_left
  dischargeRight := synth_conj_right
  dedupConj := synth_dedup
  elimParam := elim_checkedDiv_param
  cancelParam := cancel_div_param
  compositional := compositional_binary
  knownParam := known_ctx_elim_param
  dedupParam := unknown_ctx_dedup_param
  trapParam := zero_div_trap_param

theorem updated_obligations_satisfiable :
    ∃ (synthFn : GuardIR → GuardIR → GuardIR) (optFn : GuardIR → Expr → Expr),
      UpdatedObligations synthFn optFn := by
  exact ⟨synth, opt, all_obligations⟩

/-- The old optimizer is rejected independently of which guard synthesizer accompanies it. -/
theorem fixture_optimizer_rejected (synthFn : GuardIR → GuardIR → GuardIR) :
    ¬ UpdatedObligations synthFn M1.opt := by
  intro h
  have bad := (h.knownParam (.var 2) (.var 4) (.var 3) M1.positiveEnv).1
  have two : checkedDivCount (M1.opt (.nonZero (.var 3))
      (mkDualDivExpr (.var 2) (.var 4) (.var 3))) = 2 := by decide
  rw [two] at bad
  cases bad

/-- The old residual wrapper separately fails the new normalization contract. -/
theorem old_synth_rejected (optFn : GuardIR → Expr → Expr) :
    ¬ UpdatedObligations M1.synth optFn := by
  intro h
  have bad := h.topLeftNZ (.var 0)
  change GuardIR.imp .top (.nonZero (.var 0)) = .nonZero (.var 0) at bad
  cases bad

def sampleX : PureExpr := .add (.var 7) (.lit 1)
def sampleY : PureExpr := .mul (.var 9) (.lit 3)
def sampleD : PureExpr := .lit 2
def sampleEnv : Env := fun _ => 4
def sampleExpr : Expr := mkDualDivExpr sampleX sampleY sampleD
def nestedExpr : Expr :=
  .sub (.add (.checkedDiv (.pure sampleX) (.pure sampleD))
    (mkCancelExpr sampleY sampleD)) (.pure (.lit 0))

theorem generalized_positive_witness :
    evalGuard sampleEnv (.nonZero sampleD) = true ∧
    evalExpr sampleEnv sampleExpr = .val 14 ∧
    evalExpr sampleEnv (opt .top sampleExpr) = .val 14 ∧
    execCheckCost sampleEnv sampleExpr = 2 ∧
    execCheckCost sampleEnv (opt .top sampleExpr) = 1 ∧
    checkedDivCount (opt (.nonZero sampleD) nestedExpr) = 0 ∧
    guardBranchCount (opt (.nonZero sampleD) nestedExpr) = 0 ∧
    evalExpr sampleEnv (opt (.nonZero sampleD) nestedExpr) = .val 14 := by
  decide

theorem renamed_reduction :
    checkedDivCount (opt (.nonZero (.var 3)) M1.renamedBench) = 0 ∧
    checkedDivCount (M1.opt (.nonZero (.var 3)) M1.renamedBench) = 2 := by
  decide

theorem normalization_witness :
    synth .top (.nonZero sampleD) = .nonZero sampleD ∧
    synth .top (.conj (.nonZero sampleD) (.nonZero sampleD)) = .nonZero sampleD ∧
    synth (.conj (.eq (.var 8) (.lit 4)) (.nonZero sampleD)) (.nonZero sampleD) = .top := by
  decide

theorem generalized_zero_trap :
    evalExpr sampleEnv (opt .top (mkDualDivExpr sampleX sampleY (.lit 0))) = .trap := by
  decide

end M1R2


/-!
## Milestone 2: imperative statement/block specification audit

The candidate below implements capture-free pure/guard substitution and a
structural weakest-precondition pullback for every Stmt. A constructive
Boolean normalizer handles literals, equality to zero, and double negation,
then reuses the independently proved M1 residual synthesizer.

Block optimization prunes a proven top-level branch and collects safe
terminal-divisor facts by querying the complete statement pullback. It
optimizes the return under those facts, never treating a pre-state fact as
an unchanged post-state fact. This candidate supports arbitrary statements
and expressions; the target capability laws specify particular parametric
families, not complete optimization of every equivalent CFG encoding.

Obligations packages every compiler-dependent M2 theorem. The general
state/lifting bridge is proved separately. The named witnesses include
same-variable assignments, sequencing, clobbering, aliasing, updated-state
costs, both diamond arms, and a branch guard invalidated by its assignment.
The infinite injective literal family rules out finite fixture tables:
eventual identity on that family contradicts parametric check elimination.
No theorem or compiler stub from Specs.Target is invoked.
-/

namespace M2
theorem update_same (env : Env) (v : VarId) (n : Int) : updateEnv env v n v = n := by
  simp [updateEnv]
theorem update_other (env : Env) (v w : VarId) (n : Int) (h : w ≠ v) :
    updateEnv env v n w = env w := by simp [updateEnv, h]

def substPure (v : VarId) (rhs : PureExpr) : PureExpr → PureExpr
  | .lit n => .lit n
  | .var w => if w = v then rhs else .var w
  | .add l r => .add (substPure v rhs l) (substPure v rhs r)
  | .sub l r => .sub (substPure v rhs l) (substPure v rhs r)
  | .mul l r => .mul (substPure v rhs l) (substPure v rhs r)
theorem substPure_eval (env : Env) (v : VarId) (rhs e : PureExpr) :
    evalPure env (substPure v rhs e) = evalPure (updateEnv env v (evalPure env rhs)) e := by
  induction e with
  | lit n => rfl
  | var w => by_cases h : w = v <;> simp [substPure, evalPure, updateEnv, h]
  | add l r ihl ihr => simp [substPure, evalPure, ihl, ihr]
  | sub l r ihl ihr => simp [substPure, evalPure, ihl, ihr]
  | mul l r ihl ihr => simp [substPure, evalPure, ihl, ihr]

def substGuard (v : VarId) (rhs : PureExpr) : GuardIR → GuardIR
  | .top => .top
  | .bot => .bot
  | .nonZero p => .nonZero (substPure v rhs p)
  | .eq p q => .eq (substPure v rhs p) (substPure v rhs q)
  | .conj p q => .conj (substGuard v rhs p) (substGuard v rhs q)
  | .imp p q => .imp (substGuard v rhs p) (substGuard v rhs q)
theorem substGuard_eval (env : Env) (v : VarId) (rhs : PureExpr) (g : GuardIR) :
    evalGuard env (substGuard v rhs g) =
      evalGuard (updateEnv env v (evalPure env rhs)) g := by
  induction g <;> simp_all [substGuard, evalGuard, substPure_eval]

def wp : Stmt → GuardIR → GuardIR
  | .skip, g => g
  | .assign v rhs, g => substGuard v rhs g
  | .seq s₁ s₂, g => wp s₁ (wp s₂ g)
  | .ite c s₁ s₂, g => .conj (.imp c (wp s₁ g)) (.imp (.imp c .bot) (wp s₂ g))
theorem wp_eval (s : Stmt) (g : GuardIR) (env : Env) :
    evalGuard env (wp s g) = evalGuard (execStmt s env) g := by
  induction s generalizing g env with
  | skip => rfl
  | assign v rhs => exact substGuard_eval env v rhs g
  | seq s₁ s₂ ih₁ ih₂ => simp [wp, execStmt, ih₁, ih₂]
  | ite c s₁ s₂ ih₁ ih₂ =>
    cases hc : evalGuard env c <;> simp [wp, execStmt, evalGuard, hc, ih₁, ih₂]
theorem wp_denote (s : Stmt) (g : GuardIR) :
    denoteGuard (wp s g) = (stateTransfer (execStmt s)).pullback (denoteGuard g) := by
  funext env
  exact congrArg (fun b : Bool => b = true) (wp_eval s g env)
theorem wp_seq (s₁ s₂ : Stmt) (g : GuardIR) :
    denoteGuard (wp (.seq s₁ s₂) g) =
      ((stateTransfer (execStmt s₁)).comp (stateTransfer (execStmt s₂))).pullback (denoteGuard g) := by
  exact wp_denote (.seq s₁ s₂) g

def foldNZ : PureExpr → GuardIR
  | .lit n => if n = 0 then .bot else .top
  | p => .nonZero p
theorem foldNZ_eval (env : Env) (p : PureExpr) :
    evalGuard env (foldNZ p) = evalGuard env (.nonZero p) := by
  cases p <;> try rfl
  rename_i n
  by_cases h : n = 0 <;> simp [foldNZ, evalGuard, evalPure, h]

def smartNot : GuardIR → GuardIR
  | .imp a .bot => a
  | g => .imp g .bot
theorem smartNot_eval (env : Env) (g : GuardIR) :
    evalGuard env (smartNot g) = !evalGuard env g := by
  cases g with
  | imp a b => cases b <;> simp [smartNot, evalGuard]
  | _ => simp [smartNot, evalGuard]

def smartAnd : GuardIR → GuardIR → GuardIR
  | .top, g => g
  | g, .top => g
  | .bot, _ => .bot
  | _, .bot => .bot
  | a, b => .conj a b
theorem smartAnd_eval (env : Env) (a b : GuardIR) :
    evalGuard env (smartAnd a b) = (evalGuard env a && evalGuard env b) := by
  cases a <;> cases b <;> simp [smartAnd, evalGuard]

def smartImp (a b : GuardIR) : GuardIR :=
  if a = b then .top else
  match a, b with
  | _, .top => .top
  | .bot, _ => .top
  | .top, g => g
  | g, .bot => smartNot g
  | a, b => .imp a b
theorem smartImp_eval (env : Env) (a b : GuardIR) :
    evalGuard env (smartImp a b) = (!evalGuard env a || evalGuard env b) := by
  by_cases h : a = b
  · subst b
    cases evalGuard env a <;> simp [smartImp, evalGuard]
  · cases a <;> cases b <;> simp [smartImp, h, smartNot_eval, evalGuard]

def foldEq (p q : PureExpr) : GuardIR :=
  match q with
  | .lit n => if n = 0 then .imp (foldNZ p) .bot else .eq p q
  | _ => .eq p q
theorem foldEq_eval (env : Env) (p q : PureExpr) :
    evalGuard env (foldEq p q) = evalGuard env (.eq p q) := by
  cases q <;> try rfl
  rename_i n
  by_cases hn : n = 0
  · subst n
    by_cases hp : evalPure env p = 0 <;>
      simp [foldEq, evalGuard, foldNZ_eval, evalPure, hp]
  · simp [foldEq, hn]

def norm : GuardIR → GuardIR
  | .top => .top
  | .bot => .bot
  | .nonZero p => foldNZ p
  | .eq p q => foldEq p q
  | .conj a b => smartAnd (norm a) (norm b)
  | .imp a b => smartImp (norm a) (norm b)
theorem norm_eval (env : Env) (g : GuardIR) :
    evalGuard env (norm g) = evalGuard env g := by
  induction g <;> simp_all [norm, smartAnd_eval, smartImp_eval, foldNZ_eval, foldEq_eval, evalGuard]

def synthStmt (s : Stmt) (a b : GuardIR) : GuardIR :=
  M1R2.synth (norm a) (norm (wp s b))
theorem synthStmt_eval (s : Stmt) (a b : GuardIR) (env : Env) :
    evalGuard env (synthStmt s a b) = (!evalGuard env a || evalGuard (execStmt s env) b) := by
  simp [synthStmt, M1R2.synth_eval, norm_eval, wp_eval]
theorem synthStmt_denote (s : Stmt) (a b : GuardIR) :
    denoteGuard (synthStmt s a b) =
      synthesizeEdgeGuard (stateTransfer (execStmt s)) (denoteGuard a) (denoteGuard b) := by
  funext env
  apply propext
  change evalGuard env (synthStmt s a b) = true ↔
    (evalGuard env a = true → evalGuard (execStmt s env) b = true)
  rw [synthStmt_eval]
  cases evalGuard env a <;> cases evalGuard (execStmt s env) b <;> decide
theorem synthStmt_universal (s : Stmt) (a b : GuardIR) (g : Env → Prop) :
    ForcesAfter (stateTransfer (execStmt s)) (denoteGuard a ⊓ g) (denoteGuard b) ↔
      g ≤ denoteGuard (synthStmt s a b) := by
  rw [synthStmt_denote]
  exact Round2.edge_adjunction _ _ _ _
theorem synth_literal (n : Int) (hn : n ≠ 0) :
    synthStmt .skip .top (.nonZero (.lit n)) = .top := by
  simp [synthStmt, wp, norm, foldNZ, hn, M1R2.synth]
theorem synth_assign (v : VarId) (rhs : PureExpr) :
    synthStmt (.assign v rhs) (.nonZero rhs) (.nonZero (.var v)) = .top := by
  cases rhs <;> simp [synthStmt, wp, substGuard, substPure, norm, foldNZ, M1R2.synth, M1R2.synthNZ]
  rename_i n
  by_cases hn : n = 0 <;> simp [hn]
theorem synth_diamond (x d : VarId) (n : Int) (hn : n ≠ 0) :
    synthStmt (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)))
      .top (.nonZero (.var d)) = .top := by
  simp [synthStmt, wp, substGuard, substPure, norm, foldNZ, foldEq, hn,
    smartAnd, smartImp, smartNot, M1R2.synth]
theorem synth_sound (s : Stmt) (a b : GuardIR) (env : Env)
    (ha : evalGuard env a = true) (hg : evalGuard env (synthStmt s a b) = true) :
    evalGuard (execStmt s env) b = true := by
  rw [synthStmt_eval, ha] at hg
  simpa using hg
theorem synth_top_sound (s : Stmt) (a b : GuardIR)
    (h : synthStmt s a b = .top) (env : Env) (ha : evalGuard env a = true) :
    evalGuard (execStmt s env) b = true := by
  exact synth_sound s a b env ha (by rw [h]; rfl)

def pruneTop (ctx : GuardIR) : Stmt → Stmt
  | .ite c t f => if synthStmt .skip ctx c = .top then t else .ite c t f
  | s => s
theorem prune_sound (ctx : GuardIR) (s : Stmt) (env : Env) (hc : evalGuard env ctx = true) :
    execStmt (pruneTop ctx s) env = execStmt s env := by
  cases s with
  | skip => rfl
  | assign v rhs => rfl
  | seq s₁ s₂ => rfl
  | ite c t f =>
    by_cases ht : synthStmt .skip ctx c = .top
    · have hg : evalGuard env c = true := synth_top_sound .skip ctx c ht env hc
      simp [pruneTop, ht, execStmt, hg]
    · simp [pruneTop, ht]
theorem synth_skip_self (p : PureExpr) : synthStmt .skip (.nonZero p) (.nonZero p) = .top := by
  cases p <;> simp [synthStmt, wp, norm, foldNZ, M1R2.synth, M1R2.synthNZ]
  rename_i n
  by_cases h : n = 0 <;> simp [h]
theorem prune_dead (p : PureExpr) (d : VarId) (n : Int) :
    pruneTop (.nonZero p) (.ite (.nonZero p) (.assign d (.lit n)) (.assign d (.lit 0))) =
      .assign d (.lit n) := by
  simp [pruneTop, synth_skip_self]
theorem prune_diamond (x d : VarId) (n : Int) :
    pruneTop .top (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) =
      .ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)) := by
  simp [pruneTop, synthStmt, wp, norm, foldEq, foldNZ, M1R2.synth, M1R2.shrink]

def denomFact (ctx : GuardIR) (s : Stmt) (d : PureExpr) : GuardIR :=
  if synthStmt s ctx (.nonZero d) = .top then .nonZero d else .top
theorem denomFact_sound (ctx : GuardIR) (s : Stmt) (d : PureExpr) (env : Env)
    (hc : evalGuard env ctx = true) :
    evalGuard (execStmt s env) (denomFact ctx s d) = true := by
  unfold denomFact
  split
  · rename_i h
    exact synth_top_sound s ctx (.nonZero d) h env hc
  · rfl

def facts (ctx : GuardIR) (s : Stmt) : Expr → GuardIR
  | .pure _ => .top
  | .add l r | .sub l r | .mul l r => .conj (facts ctx s l) (facts ctx s r)
  | .checkedDiv n d | .uncheckedDiv n d =>
      .conj (.conj (facts ctx s n) (facts ctx s d))
        (match d with | .pure p => denomFact ctx s p | _ => .top)
  | .iteGuard _ t f => .conj (facts ctx s t) (facts ctx s f)
theorem facts_sound (ctx : GuardIR) (s : Stmt) (e : Expr) (env : Env)
    (hc : evalGuard env ctx = true) :
    evalGuard (execStmt s env) (facts ctx s e) = true := by
  induction e with
  | pure p => rfl
  | add l r ihl ihr | sub l r ihl ihr | mul l r ihl ihr =>
    simp [facts, evalGuard, ihl, ihr]
  | iteGuard g t f iht ihf => simp [facts, evalGuard, iht, ihf]
  | checkedDiv n d ihn ihd | uncheckedDiv n d ihn ihd =>
    simp only [facts, evalGuard, ihn, ihd, Bool.true_and]
    cases d with
    | pure p => exact denomFact_sound ctx s p env hc
    | _ => rfl

def blockOpt (ctx : GuardIR) (p : BlockProg) : BlockProg :=
  let body := pruneTop ctx p.body
  {body := body, ret := M1R2.opt (facts ctx body p.ret) p.ret}
theorem block_sound (ctx : GuardIR) (p : BlockProg) (env : Env)
    (hc : evalGuard env ctx = true) :
    evalBlock env (blockOpt ctx p) = evalBlock env p := by
  change evalExpr (execStmt (pruneTop ctx p.body) env)
    (M1R2.opt (facts ctx (pruneTop ctx p.body) p.ret) p.ret) =
      evalExpr (execStmt p.body env) p.ret
  rw [M1R2.opt_sound _ _ _ (facts_sound ctx _ p.ret env hc), prune_sound ctx p.body env hc]
theorem block_guarded (ctx : GuardIR) (p : BlockProg) :
    GuardedEquiv (liftEval evalBlock) (denoteGuard ctx) (blockOpt ctx p) p := by
  exact (M1.lift_bridge evalBlock _ _ _).mpr (block_sound ctx p)

theorem facts_dual_hasNZ (ctx : GuardIR) (s : Stmt) (x y d : PureExpr)
    (h : synthStmt s ctx (.nonZero d) = .top) :
    M1R2.hasNZ (facts ctx s (mkDualDivExpr x y d)) d = true := by
  simp [facts, mkDualDivExpr, denomFact, h, M1R2.hasNZ]
theorem facts_dual_not_top (ctx : GuardIR) (s : Stmt) (x y d : PureExpr) :
    facts ctx s (mkDualDivExpr x y d) ≠ .top := by
  simp [facts, mkDualDivExpr]
theorem core_dual (ctx : GuardIR) (x y d : PureExpr) (h : M1R2.hasNZ ctx d = true) :
    M1R2.core ctx (mkDualDivExpr x y d) = M1R2.fastDual x y d := by
  simp [M1R2.core, M1R2.smartDiv, mkDualDivExpr, M1R2.fastDual, h]
theorem block_dual_ret (ctx : GuardIR) (s : Stmt) (x y d : PureExpr)
    (h : synthStmt (pruneTop ctx s) ctx (.nonZero d) = .top) :
    (blockOpt ctx {body := s, ret := mkDualDivExpr x y d}).ret = M1R2.fastDual x y d := by
  change M1R2.opt (facts ctx (pruneTop ctx s) (mkDualDivExpr x y d)) (mkDualDivExpr x y d) = _
  rw [M1R2.opt, ite_eq_right (facts_dual_not_top _ _ _ _ _)]
  exact core_dual _ _ _ _ (facts_dual_hasNZ _ _ _ _ _ h)
theorem fast_metrics (x y d : PureExpr) (env : Env) :
    checkedDivCount (M1R2.fastDual x y d) = 0 ∧
    divOpCount (M1R2.fastDual x y d) ≤ 1 ∧
    guardBranchCount (M1R2.fastDual x y d) = 0 ∧
    execCheckCost env (M1R2.fastDual x y d) = 0 := by
  by_cases hd : evalPure env d = 0 <;>
    simp [M1R2.fastDual, checkedDivCount, divOpCount, guardBranchCount, execCheckCost, evalExpr, hd]
theorem block_dual_metrics (ctx : GuardIR) (s : Stmt) (x y d : PureExpr) (env : Env)
    (h : synthStmt (pruneTop ctx s) ctx (.nonZero d) = .top) :
    checkedDivCount (blockOpt ctx {body := s, ret := mkDualDivExpr x y d}).ret = 0 ∧
    divOpCount (blockOpt ctx {body := s, ret := mkDualDivExpr x y d}).ret ≤ 1 ∧
    guardBranchCount (blockOpt ctx {body := s, ret := mkDualDivExpr x y d}).ret = 0 ∧
    execBlockCheckCost env (blockOpt ctx {body := s, ret := mkDualDivExpr x y d}) =
      stmtGuardCost env (pruneTop ctx s) := by
  have hr := block_dual_ret ctx s x y d h
  have hm := fast_metrics x y d (execStmt (pruneTop ctx s) env)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr]; exact hm.1
  · rw [hr]; exact hm.2.1
  · rw [hr]; exact hm.2.2.1
  · unfold execBlockCheckCost
    rw [hr, show (blockOpt ctx {body := s, ret := mkDualDivExpr x y d}).body = pruneTop ctx s from rfl,
      hm.2.2.2, Nat.add_zero]

theorem literal_elim (num y : PureExpr) (n : Int) (hn : n ≠ 0) (env : Env) :
    let prog : BlockProg := {body := .skip, ret := mkDualDivExpr num y (.lit n)}
    checkedDivCount (blockOpt .top prog).ret = 0 ∧
    divOpCount (blockOpt .top prog).ret ≤ 1 ∧
    guardBranchCount (blockOpt .top prog).ret = 0 ∧ execBlockCheckCost env (blockOpt .top prog) = 0 := by
  exact block_dual_metrics .top .skip num y (.lit n) env (synth_literal n hn)
theorem synth_clobber (x d : VarId) (hxd : d ≠ x) :
    synthStmt (.seq (.assign d (.var x)) (.assign x (.lit 0)))
      (.nonZero (.var x)) (.nonZero (.var d)) = .top := by
  simp [synthStmt, wp, substGuard, substPure, hxd, norm, foldNZ, M1R2.synth, M1R2.synthNZ]
theorem clobber_elim (x d : VarId) (hxd : d ≠ x) (num y : PureExpr) (env : Env) :
    checkedDivCount (blockOpt (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret = 0 ∧
    divOpCount (blockOpt (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret ≤ 1 ∧
    guardBranchCount (blockOpt (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret = 0 ∧
    execBlockCheckCost env (blockOpt (.nonZero (.var x)) (mkClobberBlock x d num y d)) = 0 := by
  exact block_dual_metrics (.nonZero (.var x)) _ num y (.var d) env (synth_clobber x d hxd)

theorem diamond_nonzero (x d : VarId) (n : Int) (hn : n ≠ 0) (env : Env) :
    execStmt (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) env d ≠ 0 := by
  by_cases hx : env x = 0 <;> simp [execStmt, evalGuard, evalPure, updateEnv, hx, hn]
theorem diamond_cost (x d : VarId) (n : Int) (env : Env) :
    stmtGuardCost env (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) = 1 := by
  simp [stmtGuardCost, guardEvalCost]
theorem dual_cost (x y d : PureExpr) (env : Env) (hd : evalPure env d ≠ 0) :
    execCheckCost env (mkDualDivExpr x y d) = 2 := by
  simp [mkDualDivExpr, execCheckCost, evalExpr, hd]
theorem diamond_elim (x d : VarId) (n : Int) (hn : n ≠ 0) (num y : PureExpr) (env : Env) :
    checkedDivCount (blockOpt .top (mkDiamondSafeBlock x d n num y)).ret = 0 ∧
    divOpCount (blockOpt .top (mkDiamondSafeBlock x d n num y)).ret ≤ 1 ∧
    guardBranchCount (blockOpt .top (mkDiamondSafeBlock x d n num y)).ret = 0 ∧
    execBlockCheckCost env (blockOpt .top (mkDiamondSafeBlock x d n num y)) ≤ 1 ∧
    execBlockCheckCost env (mkDiamondSafeBlock x d n num y) = 3 := by
  have hs : synthStmt
      (pruneTop .top (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))))
      .top (.nonZero (.var d)) = .top := by
    rw [prune_diamond]
    exact synth_diamond x d n hn
  have hm := block_dual_metrics .top _ num y (.var d) env hs
  refine ⟨hm.1, hm.2.1, hm.2.2.1, ?_, ?_⟩
  · unfold mkDiamondSafeBlock
    rw [hm.2.2.2, prune_diamond, diamond_cost]
  · simp only [execBlockCheckCost, mkDiamondSafeBlock]
    rw [diamond_cost, dual_cost num y (.var d)
      (execStmt (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) env)
      (diamond_nonzero x d n hn env)]

theorem synth_assign_lit (ctx : GuardIR) (d : VarId) (n : Int) (hn : n ≠ 0) :
    synthStmt (.assign d (.lit n)) ctx (.nonZero (.var d)) = .top := by
  simp [synthStmt, wp, substGuard, substPure, norm, foldNZ, hn, M1R2.synth_top_right]
theorem facts_cancel_hasNZ (ctx : GuardIR) (s : Stmt) (y d : PureExpr)
    (h : synthStmt s ctx (.nonZero d) = .top) :
    M1R2.hasNZ (facts ctx s (mkCancelExpr y d)) d = true := by
  simp [facts, mkCancelExpr, denomFact, h]
theorem facts_cancel_not_top (ctx : GuardIR) (s : Stmt) (y d : PureExpr) :
    facts ctx s (mkCancelExpr y d) ≠ .top := by
  simp [facts, mkCancelExpr]
theorem block_cancel_ret (ctx : GuardIR) (s : Stmt) (y d : PureExpr)
    (h : synthStmt (pruneTop ctx s) ctx (.nonZero d) = .top) :
    (blockOpt ctx {body := s, ret := mkCancelExpr y d}).ret = .pure y := by
  change M1R2.opt (facts ctx (pruneTop ctx s) (mkCancelExpr y d)) (mkCancelExpr y d) = _
  rw [M1R2.opt, ite_eq_right (facts_cancel_not_top _ _ _ _)]
  exact M1R2.core_cancel_right _ _ _ (facts_cancel_hasNZ _ _ _ _ h)
theorem dead_elim (p : PureExpr) (d : VarId) (n : Int) (hn : n ≠ 0) (y : PureExpr) (env : Env) :
    checkedDivCount (blockOpt (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0 ∧
    divOpCount (blockOpt (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0 ∧
    execBlockCheckCost env (blockOpt (.nonZero p) (mkDeadBranchBlock p d n y)) = 0 := by
  have hs : synthStmt
      (pruneTop (.nonZero p) (.ite (.nonZero p) (.assign d (.lit n)) (.assign d (.lit 0))))
      (.nonZero p) (.nonZero (.var d)) = .top := by
    rw [prune_dead]
    exact synth_assign_lit _ _ _ hn
  have hr : (blockOpt (.nonZero p) (mkDeadBranchBlock p d n y)).ret = .pure y :=
    block_cancel_ret (.nonZero p) _ y (.var d) hs
  have hb : (blockOpt (.nonZero p) (mkDeadBranchBlock p d n y)).body = .assign d (.lit n) := by
    exact prune_dead p d n
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]; rfl
  · rw [hr]; rfl
  · unfold execBlockCheckCost
    rw [hb, hr]
    rfl

theorem clobber_trap (x d : VarId) (num y : PureExpr) (env : Env)
    (hx : evalGuard env (.nonZero (.var x)) = true) :
    evalBlock env (blockOpt (.nonZero (.var x)) (mkClobberBlock x d num y x)) = .trap := by
  rw [block_sound _ _ env hx]
  simp [evalBlock, mkClobberBlock, mkDualDivExpr, evalExpr, evalPure, execStmt, updateEnv]

theorem state_lift_bridge {S₁ S₂ Term Out : Type*}
    (step : S₁ → S₂) (run : S₂ → Term → Out) (P : S₁ → Prop) (t₁ t₂ : Term) :
    GuardedEquiv (pullbackEval (stateTransfer step) (liftEval run)) P t₁ t₂ ↔
      ∀ s, P s → run (step s) t₁ = run (step s) t₂ := by
  constructor
  · intro h s hs
    have he := h P le_rfl
    have ho : liftEval run ((stateTransfer step).post P) t₂ (step s) (run (step s) t₁) :=
      Eq.mp (congrFun (congrFun he (step s)) (run (step s) t₁)) ⟨⟨s, rfl, hs⟩, rfl⟩
    exact ho.2.symm
  · intro h Q hQP
    funext s₂ out
    apply propext
    constructor
    · rintro ⟨⟨s, he, hs⟩, ho⟩
      cases he
      exact ⟨⟨s, rfl, hs⟩, (h s (hQP s hs)).symm.trans ho⟩
    · rintro ⟨⟨s, he, hs⟩, ho⟩
      cases he
      exact ⟨⟨s, rfl, hs⟩, (h s (hQP s hs)).trans ho⟩
theorem synth_diamond_sound (s₁ s₂ : Stmt) (ctx req : GuardIR) (e₁ e₂ : Expr)
    (h : GuardedEquiv (liftEval evalExpr) (denoteGuard req) e₁ e₂) :
    let g := GuardIR.conj (synthStmt s₁ ctx req) (synthStmt s₂ ctx req)
    ∀ env, evalGuard env ctx = true → evalGuard env g = true →
      evalExpr (execStmt s₁ env) e₁ = evalExpr (execStmt s₁ env) e₂ ∧
      evalExpr (execStmt s₂ env) e₁ = evalExpr (execStmt s₂ env) e₂ := by
  intro g env hc hg
  change (evalGuard env (synthStmt s₁ ctx req) && evalGuard env (synthStmt s₂ ctx req)) = true at hg
  simp only [Bool.and_eq_true] at hg
  have he := (M1.lift_bridge evalExpr (denoteGuard req) e₁ e₂).mp h
  exact ⟨he _ (synth_sound s₁ ctx req env hc hg.1), he _ (synth_sound s₂ ctx req env hc hg.2)⟩

structure Obligations
    (pb : Stmt → GuardIR → GuardIR) (sg : Stmt → GuardIR → GuardIR → GuardIR)
    (opt : GuardIR → BlockProg → BlockProg) : Prop where
  pullback : ∀ s g, denoteGuard (pb s g) = (stateTransfer (execStmt s)).pullback (denoteGuard g)
  sequence : ∀ s₁ s₂ g, denoteGuard (pb (.seq s₁ s₂) g) =
    ((stateTransfer (execStmt s₁)).comp (stateTransfer (execStmt s₂))).pullback (denoteGuard g)
  denote : ∀ s a b, denoteGuard (sg s a b) =
    synthesizeEdgeGuard (stateTransfer (execStmt s)) (denoteGuard a) (denoteGuard b)
  universal : ∀ s a b (g : Env → Prop),
    ForcesAfter (stateTransfer (execStmt s)) (denoteGuard a ⊓ g) (denoteGuard b) ↔ g ≤ denoteGuard (sg s a b)
  diamondSound : ∀ s₁ s₂ ctx req e₁ e₂,
    GuardedEquiv (liftEval evalExpr) (denoteGuard req) e₁ e₂ →
      let g := GuardIR.conj (sg s₁ ctx req) (sg s₂ ctx req)
      ∀ env, evalGuard env ctx = true → evalGuard env g = true →
        evalExpr (execStmt s₁ env) e₁ = evalExpr (execStmt s₁ env) e₂ ∧
        evalExpr (execStmt s₂ env) e₁ = evalExpr (execStmt s₂ env) e₂
  literalGuard : ∀ n : Int, n ≠ 0 → sg .skip .top (.nonZero (.lit n)) = .top
  assignGuard : ∀ v rhs, sg (.assign v rhs) (.nonZero rhs) (.nonZero (.var v)) = .top
  diamondGuard : ∀ x d (n : Int), n ≠ 0 →
    sg (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)))
      .top (.nonZero (.var d)) = .top
  guarded : ∀ ctx p, GuardedEquiv (liftEval evalBlock) (denoteGuard ctx) (opt ctx p) p
  sound : ∀ ctx p env, evalGuard env ctx = true → evalBlock env (opt ctx p) = evalBlock env p
  literal : ∀ num y (n : Int), n ≠ 0 → ∀ env,
    let p : BlockProg := {body := .skip, ret := mkDualDivExpr num y (.lit n)}
    checkedDivCount (opt .top p).ret = 0 ∧ divOpCount (opt .top p).ret ≤ 1 ∧
      guardBranchCount (opt .top p).ret = 0 ∧ execBlockCheckCost env (opt .top p) = 0
  clobber : ∀ x d, d ≠ x → ∀ num y env,
    checkedDivCount (opt (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret = 0 ∧
    divOpCount (opt (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret ≤ 1 ∧
    guardBranchCount (opt (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret = 0 ∧
    execBlockCheckCost env (opt (.nonZero (.var x)) (mkClobberBlock x d num y d)) = 0
  clobberTrap : ∀ x d num y env, evalGuard env (.nonZero (.var x)) = true →
    evalBlock env (opt (.nonZero (.var x)) (mkClobberBlock x d num y x)) = .trap
  diamond : ∀ x d (n : Int), n ≠ 0 → ∀ num y env,
    checkedDivCount (opt .top (mkDiamondSafeBlock x d n num y)).ret = 0 ∧
    divOpCount (opt .top (mkDiamondSafeBlock x d n num y)).ret ≤ 1 ∧
    guardBranchCount (opt .top (mkDiamondSafeBlock x d n num y)).ret = 0 ∧
    execBlockCheckCost env (opt .top (mkDiamondSafeBlock x d n num y)) ≤ 1 ∧
    execBlockCheckCost env (mkDiamondSafeBlock x d n num y) = 3
  dead : ∀ p d (n : Int), n ≠ 0 → ∀ y env,
    checkedDivCount (opt (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0 ∧
    divOpCount (opt (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0 ∧
    execBlockCheckCost env (opt (.nonZero p) (mkDeadBranchBlock p d n y)) = 0

theorem all_obligations : Obligations wp synthStmt blockOpt where
  pullback := wp_denote
  sequence := wp_seq
  denote := synthStmt_denote
  universal := synthStmt_universal
  diamondSound := synth_diamond_sound
  literalGuard := synth_literal
  assignGuard := synth_assign
  diamondGuard := synth_diamond
  guarded := block_guarded
  sound := block_sound
  literal := literal_elim
  clobber := clobber_elim
  clobberTrap := clobber_trap
  diamond := diamond_elim
  dead := dead_elim
theorem satisfiable :
    ∃ (pb : Stmt → GuardIR → GuardIR) (sg : Stmt → GuardIR → GuardIR → GuardIR)
      (opt : GuardIR → BlockProg → BlockProg), Obligations pb sg opt := by
  exact ⟨wp, synthStmt, blockOpt, all_obligations⟩

def env (x : Int) : Env := fun v => if v = 0 then x else 6
def literalFamily (k : Nat) : BlockProg :=
  {body := .skip, ret := mkDualDivExpr (.var k) (.lit 5) (.lit 2)}
theorem literal_family_injective : Function.Injective literalFamily := by
  intro a b h
  simpa [literalFamily, mkDualDivExpr] using h

/-- No optimizer that is eventually identity on this infinite fresh-variable family can pass. -/
theorem finite_fixture_rejected
    (pb : Stmt → GuardIR → GuardIR) (sg : Stmt → GuardIR → GuardIR → GuardIR)
    (opt : GuardIR → BlockProg → BlockProg) (h : Obligations pb sg opt) :
    ¬ ∃ N : Nat, ∀ k, N < k → opt .top (literalFamily k) = literalFamily k := by
  rintro ⟨N, hfix⟩
  have he := hfix (N + 1) (by omega)
  have bad := (h.literal (.var (N + 1)) (.lit 5) 2 (by decide) (env 0)).1
  change checkedDivCount (opt .top (literalFamily (N + 1))).ret = 0 at bad
  rw [he] at bad
  change (2 : Nat) = 0 at bad
  cases bad

theorem identity_rejected (pb : Stmt → GuardIR → GuardIR)
    (sg : Stmt → GuardIR → GuardIR → GuardIR) :
    ¬ Obligations pb sg (fun _ p => p) := by
  intro h
  exact finite_fixture_rejected pb sg _ h ⟨0, fun _ _ => rfl⟩
theorem bot_synthesis_rejected (pb : Stmt → GuardIR → GuardIR)
    (opt : GuardIR → BlockProg → BlockProg) : ¬ Obligations pb (fun _ _ _ => .bot) opt := by
  intro h
  have he := congrFun (h.denote .skip .top .top) (env 0)
  have hb : denoteGuard .bot (env 0) := Eq.mpr he (fun _ => rfl)
  change false = true at hb
  cases hb
theorem top_synthesis_rejected (pb : Stmt → GuardIR → GuardIR)
    (opt : GuardIR → BlockProg → BlockProg) : ¬ Obligations pb (fun _ _ _ => .top) opt := by
  intro h
  have he := congrFun (h.denote .skip .top .bot) (env 0)
  have hb : synthesizeEdgeGuard (stateTransfer (execStmt .skip)) (denoteGuard .top)
      (denoteGuard .bot) (env 0) := Eq.mp he rfl
  have bad := hb rfl
  change false = true at bad
  cases bad
theorem raw_imp_rejected (opt : GuardIR → BlockProg → BlockProg) :
    ¬ Obligations wp (fun s a b => .imp a (wp s b)) opt := by
  intro h
  have bad := h.literalGuard 2 (by decide)
  cases bad

theorem assignment_reads_old_state :
    execStmt (.assign 0 (.add (.var 0) (.lit 1))) (env 2) 0 = 3 ∧
    execStmt (.assign 0 (.add (.var 0) (.lit 1))) (env 2) 1 = 6 := by decide
theorem sequence_and_clobber :
    execStmt (.seq (.assign 1 (.var 0)) (.assign 0 (.lit 0))) (env 2) 1 = 2 ∧
    execStmt (.seq (.assign 1 (.var 0)) (.assign 0 (.lit 0))) (env 2) 0 = 0 ∧
    evalBlock (env 2) (mkClobberBlock 0 1 (.var 0) (.var 1) 1) = .val 2 ∧
    evalBlock (env 2) (mkClobberBlock 0 1 (.lit 8) (.lit 5) 0) = .trap := by decide
theorem backwards_substitution_order :
    evalGuard (env 2) (wp (.seq (.assign 1 (.var 0)) (.assign 0 (.lit 0))) (.nonZero (.var 1))) = true ∧
    evalGuard (env 2) (wp (.assign 0 (.lit 0)) (wp (.assign 1 (.var 0)) (.nonZero (.var 1)))) = false := by
  decide
theorem cost_uses_updated_state :
    stmtGuardCost (env 2) (.seq (.assign 0 (.lit 0))
      (.ite (.nonZero (.var 0)) (.ite (.nonZero (.var 1)) .skip .skip) .skip)) = 1 ∧
    execBlockCheckCost (env 2)
      {body := .assign 0 (.lit 0), ret := .checkedDiv (.pure (.lit 8)) (.pure (.var 0))} = 1 := by
  decide
theorem literal_positive :
    evalBlock (env 2) (literalFamily 7) = .val 8 ∧
    evalBlock (env 2) (blockOpt .top (literalFamily 7)) = .val 8 ∧
    execBlockCheckCost (env 2) (literalFamily 7) = 2 ∧
    execBlockCheckCost (env 2) (blockOpt .top (literalFamily 7)) = 0 := by decide
theorem clobber_positive :
    evalGuard (env 2) (.nonZero (.var 0)) = true ∧
    evalBlock (env 2) (blockOpt (.nonZero (.var 0)) (mkClobberBlock 0 1 (.lit 8) (.lit 5) 1)) = .val 9 ∧
    execBlockCheckCost (env 2) (blockOpt (.nonZero (.var 0)) (mkClobberBlock 0 1 (.lit 8) (.lit 5) 1)) = 0 := by
  decide
theorem alias_negative :
    evalBlock (env 2) (mkClobberBlock 0 0 (.lit 8) (.lit 5) 0) = .trap ∧
    evalBlock (env 2) (blockOpt (.nonZero (.var 0)) (mkClobberBlock 0 0 (.lit 8) (.lit 5) 0)) = .trap := by
  decide
theorem stale_nonzero_fact_rejected :
    let source := mkClobberBlock 0 1 (.lit 8) (.lit 5) 0
    let bad : BlockProg := {body := source.body, ret := M1R2.fastDual (.lit 8) (.lit 5) (.var 0)}
    evalGuard (env 2) (.nonZero (.var 0)) = true ∧
    evalBlock (env 2) source = .trap ∧ evalBlock (env 2) bad = .ub := by decide
theorem diamond_both_branches :
    evalBlock (env 0) (mkDiamondSafeBlock 0 1 2 (.lit 8) (.lit 5)) = .val 9 ∧
    evalBlock (env 2) (mkDiamondSafeBlock 0 1 2 (.lit 8) (.lit 5)) = .val 9 ∧
    execBlockCheckCost (env 0) (mkDiamondSafeBlock 0 1 2 (.lit 8) (.lit 5)) = 3 ∧
    execBlockCheckCost (env 0) (blockOpt .top (mkDiamondSafeBlock 0 1 2 (.lit 8) (.lit 5))) = 1 ∧
    execBlockCheckCost (env 2) (blockOpt .top (mkDiamondSafeBlock 0 1 2 (.lit 8) (.lit 5))) = 1 := by decide
theorem diamond_alias_and_zero :
    evalBlock (env 0) (blockOpt .top (mkDiamondSafeBlock 0 0 2 (.lit 8) (.lit 5))) = .val 9 ∧
    evalBlock (env 0) (mkDiamondSafeBlock 0 1 0 (.lit 8) (.lit 5)) = .trap := by decide
theorem dead_branch_mutates_guard_variable :
    let p : PureExpr := .sub (.var 1) (.lit 2)
    let rho : Env := fun _ => 3
    let prog := mkDeadBranchBlock p 1 2 (.var 1)
    evalGuard rho (.nonZero p) = true ∧
    evalGuard (execStmt prog.body rho) (.nonZero p) = false ∧
    evalBlock rho prog = .val 2 ∧ evalBlock rho (blockOpt (.nonZero p) prog) = .val 2 ∧
    execBlockCheckCost rho (blockOpt (.nonZero p) prog) = 0 := by decide
theorem assignment_can_kill_context :
    let p : PureExpr := .sub (.var 1) (.lit 2)
    let rho : Env := fun _ => 3
    evalGuard rho (synthStmt (.assign 1 (.lit 2)) (.nonZero p) (.nonZero p)) = false := by decide

/-- A wrapper outside all named benchmark bodies is handled by the general pullback analysis. -/
theorem wrapped_diamond :
    let original := mkDiamondSafeBlock 7 9 (-2) (.lit 8) (.lit 5)
    let prog : BlockProg := {body := .seq .skip original.body, ret := original.ret}
    let rho : Env := fun _ => 0
    evalBlock rho prog = .val 1 ∧ evalBlock rho (blockOpt .top prog) = .val 1 ∧
    checkedDivCount (blockOpt .top prog).ret = 0 ∧ execBlockCheckCost rho (blockOpt .top prog) = 1 := by
  decide


/-- Finite literal fixtures with a raw implication fallback cannot satisfy guard normalization. -/
theorem finite_guard_fixture_rejected
    (pb : Stmt → GuardIR → GuardIR) (sg : Stmt → GuardIR → GuardIR → GuardIR)
    (opt : GuardIR → BlockProg → BlockProg) (h : Obligations pb sg opt) :
    ¬ ∃ N : Nat, ∀ k, N < k →
      sg .skip .top (.nonZero (.lit (Int.ofNat k))) =
        .imp .top (.nonZero (.lit (Int.ofNat k))) := by
  rintro ⟨N, hfix⟩
  have he := hfix (N + 1) (by omega)
  have hn : Int.ofNat (N + 1) ≠ 0 := by simp; omega
  rw [h.literalGuard _ hn] at he
  cases he

end M2


/-!
## Milestone 3 pre-lock review (Round 1, historical fifteen-target contract)
Spec digest: e8f568da6301459f8d78f38a82657d1d272ff65603a45a3e65a901e39e3bcbfc.

All fifteen targets are constructively satisfiable. A proof-producing planner
handles arbitrary stationary assignments and two-stage copying latches. The
loop witness rewrites bodies under a preserved invariant and versions the loop
with a total preheader guard; it retains the source loop on an unsafe guard.
The countdown cost proof is parametric in all variables, operands, and trip
counts. No theorem or compiler stub from Specs.Target is invoked.

BLOCKING: the strengthening completeness targets only require some result.
The constant vacuousStrengthen returns some .bot for every input and meets
inductive soundness plus both completeness targets. replace_strengthener proves
that substituting it into ANY full satisfying implementation preserves every
compiler-dependent M3 obligation. vacuous_countermodel instantiates that result
with a total sound optimizer that independently uses the certified planner.
Thus passing optimizer capabilities does not establish that the exported
strengthening function returns a usable invariant.

The remaining witnesses separate this gap from operational failures: the
pipeline requires actual strengthening when restricted to none/the original
target; finite exact fixture tables and identity optimization fail; eager
zero-trip traps and entry-only unchecked division change observed outcomes.
-/

namespace M3
theorem pure_nonmention_update (v : VarId) (p : PureExpr) (env : Env) (n : Int)
    (h : pureMentionsVar v p = false) :
    evalPure (updateEnv env v n) p = evalPure env p := by
  induction p with
  | lit _ => rfl
  | var w =>
    simp only [pureMentionsVar, decide_eq_false_iff_not] at h
    simp [evalPure, updateEnv, h]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
    simp only [pureMentionsVar, Bool.or_eq_false_iff] at h
    simp [evalPure, iha h.1, ihb h.2]

theorem guard_nonmention_update (v : VarId) (g : GuardIR) (env : Env) (n : Int)
    (h : guardMentionsVar v g = false) :
    evalGuard (updateEnv env v n) g = evalGuard env g := by
  induction g with
  | top => rfl
  | bot => rfl
  | nonZero e => exact congrArg (fun z : Int => decide (z ≠ 0)) (pure_nonmention_update v e env n h)
  | eq a b =>
    simp only [guardMentionsVar, Bool.or_eq_false_iff] at h
    simp [evalGuard, pure_nonmention_update v a env n h.1, pure_nonmention_update v b env n h.2]
  | conj a b iha ihb | imp a b iha ihb =>
    simp only [guardMentionsVar, Bool.or_eq_false_iff] at h
    simp [evalGuard, iha h.1, ihb h.2]

def havoc (v : VarId) (g : GuardIR) : GuardIR :=
  if guardMentionsVar v g then .bot else g

theorem havoc_sound (v : VarId) (g : GuardIR) :
    denoteGuard (havoc v g) ≤ (havocTransfer v).pullback (denoteGuard g) := by
  intro env h n
  cases hm : guardMentionsVar v g with
  | true => simp [havoc, hm, denoteGuard, evalGuard] at h
  | false =>
    simpa [denoteGuard, guard_nonmention_update v g env n hm] using
      (show denoteGuard g env from by simpa [havoc, hm] using h)

theorem havoc_exact (v : VarId) (g : GuardIR) (h : guardMentionsVar v g = false) :
    denoteGuard (havoc v g) = (havocTransfer v).pullback (denoteGuard g) := by
  funext env
  apply propext
  constructor
  · exact havoc_sound v g env
  · intro hg
    have hn := hg (env v)
    simpa [havoc, h, denoteGuard, guard_nonmention_update v g env (env v) h] using hn

def Preserved (acc : VarId) (latch : Stmt) (inv : GuardIR) : Prop :=
  ∀ env val, evalGuard env inv = true →
    evalGuard (execStmt latch (updateEnv env acc val)) inv = true

theorem preserved_iff (acc : VarId) (latch : Stmt) (inv : GuardIR) :
    Preserved acc latch inv ↔ IsLoopInvariant (loopStepTransfer acc latch) (denoteGuard inv) := by
  constructor
  · intro h env' ⟨mid, hm, env, val, he, hi⟩
    cases hm
    cases he
    exact h env val hi
  · intro h env val hi
    exact h _ ⟨updateEnv env acc val, rfl, env, val, rfl, hi⟩

/-- Vacuous success: all three strengthening obligations permit this constant function. -/
def vacuousStrengthen (_acc : VarId) (_latch : Stmt) (_target : GuardIR) : Option GuardIR :=
  some .bot

theorem bottom_inductive (acc : VarId) (latch : Stmt) (target : GuardIR) :
    IsInductiveFor (loopStepTransfer acc latch) (denoteGuard .bot) (denoteGuard target) := by
  constructor
  · apply (preserved_iff acc latch .bot).mp
    intro env val h
    cases h
  · intro env h
    cases h

theorem vacuous_inductive (acc : VarId) (latch : Stmt) (target inv : GuardIR)
    (h : vacuousStrengthen acc latch target = some inv) :
    IsInductiveFor (loopStepTransfer acc latch) (denoteGuard inv) (denoteGuard target) := by
  have hi : inv = .bot := (Option.some.inj h).symm
  subst inv
  exact bottom_inductive acc latch target

theorem vacuous_stationary (acc d i : VarId) (_hda : d ≠ acc) (_hdi : d ≠ i) :
    ∃ inv, vacuousStrengthen acc (.assign i (.sub (.var i) (.lit 1))) (.nonZero (.var d)) = some inv :=
  ⟨.bot, rfl⟩

theorem vacuous_pipeline (acc d nextD i : VarId)
    (_hda : d ≠ acc) (_hna : nextD ≠ acc) (_hdi : d ≠ i) (_hni : nextD ≠ i) (_hdn : d ≠ nextD) :
    ∃ inv, vacuousStrengthen acc
      (.seq (.assign d (.var nextD)) (.assign i (.sub (.var i) (.lit 1))))
      (.nonZero (.var d)) = some inv := ⟨.bot, rfl⟩

theorem vacuous_result_uninhabited (acc : VarId) (latch : Stmt) (target inv : GuardIR)
    (h : vacuousStrengthen acc latch target = some inv) :
    ¬ ∃ env, evalGuard env inv = true := by
  have hi : inv = .bot := (Option.some.inj h).symm
  subst inv
  rintro ⟨env, h⟩
  cases h


theorem state_iterate {S : Type*} (step : S → S) (Q : S → Prop) (n : Nat) (s : S) :
    ((stateTransfer step).iterate n).pullback Q s ↔ Q (step^[n] s) := by
  induction n generalizing Q s with
  | zero => rfl
  | succ n ih =>
    change ((stateTransfer step).iterate n).pullback (fun t => Q (step t)) s ↔ _
    rw [ih, Function.iterate_succ_apply']


def synthConj (ctx : GuardIR) : GuardIR → GuardIR
  | .conj a b => M2.smartAnd (synthConj ctx a) (synthConj ctx b)
  | g => M1R2.synth ctx g

theorem synthConj_eval (ctx g : GuardIR) (env : Env) :
    evalGuard env (synthConj ctx g) = (!evalGuard env ctx || evalGuard env g) := by
  induction g with
  | conj a b iha ihb =>
    cases hc : evalGuard env ctx <;>
      simp [synthConj, M2.smartAnd_eval, iha, ihb, evalGuard, hc]
  | _ => exact M1R2.synth_eval ctx _ env

def hoist (init : Stmt) (ctx inv : GuardIR) : GuardIR :=
  synthConj (M2.norm ctx) (M2.norm (M2.wp init inv))
theorem hoist_eval (init : Stmt) (ctx inv : GuardIR) (env : Env) :
    evalGuard env (hoist init ctx inv) =
      (!evalGuard env ctx || evalGuard (execStmt init env) inv) := by
  simp only [hoist, synthConj_eval, M2.norm_eval, M2.wp_eval]
theorem hoist_sound (init : Stmt) (ctx inv : GuardIR) (env : Env)
    (hc : evalGuard env ctx = true) (hg : evalGuard env (hoist init ctx inv) = true) :
    evalGuard (execStmt init env) inv = true := by
  rw [hoist_eval, hc] at hg
  exact hg
theorem hoist_top_sound (init : Stmt) (ctx inv : GuardIR)
    (ht : hoist init ctx inv = .top) (env : Env) (hc : evalGuard env ctx = true) :
    evalGuard (execStmt init env) inv = true :=
  hoist_sound init ctx inv env hc (by rw [ht]; rfl)
theorem hoist_denote (init : Stmt) (ctx inv : GuardIR) :
    denoteGuard (hoist init ctx inv) =
      hoistLoopGuard (stateTransfer (execStmt init)) (denoteGuard ctx) (denoteGuard inv) := by
  calc
    denoteGuard (hoist init ctx inv) = denoteGuard (M2.synthStmt init ctx inv) := by
      funext env
      exact congrArg (fun b : Bool => b = true)
        ((hoist_eval init ctx inv env).trans (M2.synthStmt_eval init ctx inv env).symm)
    _ = _ := M2.synthStmt_denote init ctx inv
theorem hoist_iterate (init : Stmt) (acc : VarId) (latch : Stmt)
    (ctx target inv : GuardIR)
    (h : IsInductiveFor (loopStepTransfer acc latch) (denoteGuard inv) (denoteGuard target))
    (n : Nat) :
    (((stateTransfer (execStmt init)).comp ((loopStepTransfer acc latch).iterate n)).post
      (denoteGuard ctx ⊓ denoteGuard (hoist init ctx inv))) ≤ denoteGuard target := by
  rw [hoist_denote]
  exact Round6.hoist_target _ _ _ _ _ h n

theorem stationary_preserved (acc d i : VarId) (rhs : PureExpr)
    (hda : d ≠ acc) (hdi : d ≠ i) :
    Preserved acc (.assign i rhs) (.nonZero (.var d)) := by
  intro env val h
  simpa [evalGuard, evalPure, execStmt, updateEnv, hda, hdi] using (of_decide_eq_true h)

theorem pipeline_preserved (acc d nextD i : VarId) (rhs : PureExpr)
    (_hda : d ≠ acc) (hna : nextD ≠ acc)
    (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD) :
    Preserved acc (.seq (.assign d (.var nextD)) (.assign i rhs))
      (.conj (.nonZero (.var d)) (.nonZero (.var nextD))) := by
  intro env val h
  simp only [evalGuard, Bool.and_eq_true] at h ⊢
  constructor <;>
    simpa [evalPure, execStmt, updateEnv, hna, hdi, hni, hdn, Ne.symm hdn] using (of_decide_eq_true h.2)

structure InvPlan (acc : VarId) (latch : Stmt) (target : GuardIR) where
  inv : GuardIR
  preserved : Preserved acc latch inv
  implies : denoteGuard inv ≤ denoteGuard target

/-- A total proof-producing planner; all outputs carry a checked preservation proof. -/
def plan (acc : VarId) (latch : Stmt) (target : GuardIR) : Option (InvPlan acc latch target) :=
  match target, latch with
  | .nonZero (.var d), .assign i rhs =>
    if h : d ≠ acc ∧ d ≠ i then
      some ⟨.nonZero (.var d), stationary_preserved acc d i rhs h.1 h.2, le_rfl⟩
    else none
  | .nonZero (.var d), .seq (.assign dst (.var nextD)) (.assign i rhs) =>
    if hd : dst = d then
      if h : d ≠ acc ∧ nextD ≠ acc ∧ d ≠ i ∧ nextD ≠ i ∧ d ≠ nextD then
        some ⟨.conj (.nonZero (.var d)) (.nonZero (.var nextD)),
          by subst dst; exact pipeline_preserved acc d nextD i rhs h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2,
          by intro env hg; exact (Bool.and_eq_true_iff.mp hg).1⟩
      else none
    else none
  | _, _ => none

def constructiveStrengthen (acc : VarId) (latch : Stmt) (target : GuardIR) : Option GuardIR :=
  (plan acc latch target).map InvPlan.inv

theorem constructive_inductive (acc : VarId) (latch : Stmt) (target inv : GuardIR)
    (h : constructiveStrengthen acc latch target = some inv) :
    IsInductiveFor (loopStepTransfer acc latch) (denoteGuard inv) (denoteGuard target) := by
  unfold constructiveStrengthen at h
  cases hp : plan acc latch target with
  | none => simp [hp] at h
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq] at h
    subst inv
    exact ⟨(preserved_iff acc latch p.inv).mp p.preserved, p.implies⟩

theorem constructive_stationary (acc d i : VarId) (hda : d ≠ acc) (hdi : d ≠ i) :
    constructiveStrengthen acc (.assign i (.sub (.var i) (.lit 1))) (.nonZero (.var d)) =
      some (.nonZero (.var d)) := by
  simp [constructiveStrengthen, plan, hda, hdi]

theorem constructive_pipeline (acc d nextD i : VarId)
    (hda : d ≠ acc) (hna : nextD ≠ acc) (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD) :
    constructiveStrengthen acc
      (.seq (.assign d (.var nextD)) (.assign i (.sub (.var i) (.lit 1))))
      (.nonZero (.var d)) = some (.conj (.nonZero (.var d)) (.nonZero (.var nextD))) := by
  simp [constructiveStrengthen, plan, hda, hna, hdi, hni, hdn]


def fastWhile (w : WhileLoop) (inv : GuardIR) : WhileLoop :=
  {w with body := M1R2.core inv w.body}

theorem run_fast (w : WhileLoop) (inv : GuardIR) (hp : Preserved w.accVar w.latch inv)
    (fuel : Nat) (env : Env) (h : evalGuard env inv = true) :
    runWhileSteps fuel env (fastWhile w inv) = runWhileSteps fuel env w := by
  induction fuel generalizing env with
  | zero => rfl
  | succ fuel ih =>
    have hb := M1R2.core_sound inv w.body env h
    simp only [runWhileSteps, fastWhile, hb]
    cases hc : evalGuard env w.cond with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      cases he : evalExpr env w.body with
      | trap => rfl
      | ub => rfl
      | val val => exact ih _ (hp env val h)

/-- A structural request for an invariant; unsupported cases retain the source loop. -/
def firstDivisor : Expr → Option PureExpr
  | .checkedDiv _ (.pure d) => some d
  | .add a b | .sub a b | .mul a b => (firstDivisor a).or (firstDivisor b)
  | _ => none

def optWhile (ctx : GuardIR) (w : WhileLoop) : LoopProg :=
  match firstDivisor w.body with
  | none => .whileLoop w
  | some d =>
    match plan w.accVar w.latch (.nonZero d) with
    | none => .whileLoop w
    | some p =>
      let g := hoist w.init ctx p.inv
      if g = .top then .whileLoop (fastWhile w p.inv)
      else .iteLoop g (.whileLoop (fastWhile w p.inv)) (.whileLoop w)

def opt (ctx : GuardIR) : LoopProg → LoopProg
  | .whileLoop w => optWhile ctx w
  | p => p

theorem optWhile_sound (fuel : Nat) (ctx : GuardIR) (w : WhileLoop) (env : Env)
    (hc : evalGuard env ctx = true) :
    evalLoop fuel env (optWhile ctx w) = evalLoop fuel env (.whileLoop w) := by
  unfold optWhile
  split
  · rfl
  · split
    · rfl
    · rename_i d p hp
      dsimp only
      by_cases ht : hoist w.init ctx p.inv = .top
      · rw [ite_eq_left ht]
        exact run_fast w p.inv p.preserved fuel _ (hoist_top_sound w.init ctx p.inv ht env hc)
      · rw [ite_eq_right ht]
        cases hg : evalGuard env (hoist w.init ctx p.inv) with
        | false => simp [evalLoop, hg]
        | true =>
          simp only [evalLoop, hg, ↓reduceIte]
          exact run_fast w p.inv p.preserved fuel _ (hoist_sound w.init ctx p.inv env hc hg)

theorem opt_sound (fuel : Nat) (ctx : GuardIR) (p : LoopProg) (env : Env)
    (hc : evalGuard env ctx = true) :
    evalLoop fuel env (opt ctx p) = evalLoop fuel env p := by
  cases p with
  | whileLoop w => exact optWhile_sound fuel ctx w env hc
  | iteLoop _ _ _ => rfl

theorem opt_guarded (fuel : Nat) (ctx : GuardIR) (p : LoopProg) :
    GuardedEquiv (liftEval (evalLoop fuel)) (denoteGuard ctx) (opt ctx p) p :=
  (M1.lift_bridge (evalLoop fuel) _ _ _).mpr (opt_sound fuel ctx p)



def sourceBody (acc : VarId) (num y : PureExpr) (d : VarId) : Expr :=
  .add (.pure (.var acc)) (mkDualDivExpr num y (.var d))
def fastBody (acc : VarId) (num y : PureExpr) (d : VarId) : Expr :=
  .add (.pure (.var acc)) (M1R2.fastDual num y (.var d))

theorem core_body (inv : GuardIR) (acc : VarId) (num y : PureExpr) (d : VarId)
    (h : M1R2.hasNZ inv (.var d) = true) :
    M1R2.core inv (sourceBody acc num y d) = fastBody acc num y d := by
  change Expr.add (.pure (.var acc)) (M1R2.core inv (mkDualDivExpr num y (.var d))) = _
  rw [M2.core_dual inv num y (.var d) h]
  rfl

theorem source_body_value (acc : VarId) (num y : PureExpr) (d : VarId) (env : Env)
    (hd : env d ≠ 0) :
    ∃ v, evalExpr env (sourceBody acc num y d) = .val v := by
  refine ⟨env acc + (evalPure env num / env d + (evalPure env y * env d) / env d), ?_⟩
  simp [sourceBody, mkDualDivExpr, evalExpr, evalPure, hd]

theorem source_body_cost (acc : VarId) (num y : PureExpr) (d : VarId) (env : Env)
    (hd : env d ≠ 0) : execCheckCost env (sourceBody acc num y d) = 2 := by
  change 0 + execCheckCost env (mkDualDivExpr num y (.var d)) = 2
  rw [Nat.zero_add]
  exact M2.dual_cost num y (.var d) env hd

theorem fast_body_metrics (acc : VarId) (num y : PureExpr) (d : VarId) (env : Env) :
    checkedDivCount (fastBody acc num y d) = 0 ∧
      divOpCount (fastBody acc num y d) = 1 ∧
      execCheckCost env (fastBody acc num y d) = 0 := by
  refine ⟨rfl, rfl, ?_⟩
  change 0 + execCheckCost env (M1R2.fastDual num y (.var d)) = 0
  rw [Nat.zero_add]
  exact (M2.fast_metrics num y (.var d) env).2.2.2

theorem counted_hoist_unknown (x d : VarId) :
    hoist (.assign d (.var x)) .top (.nonZero (.var d)) = .nonZero (.var x) := by
  simp [hoist, synthConj, M2.wp, M2.substGuard, M2.substPure,
    M2.norm, M2.foldNZ, M1R2.synth, M1R2.shrink]

theorem pipeline_hoist_known (x z d nextD : VarId) (hdn : d ≠ nextD) :
    hoist (.seq (.assign d (.var x)) (.assign nextD (.var z)))
      (.conj (.nonZero (.var x)) (.nonZero (.var z)))
      (.conj (.nonZero (.var d)) (.nonZero (.var nextD))) = .top := by
  by_cases hz : z = d <;>
    simp [hoist, synthConj, M2.wp, M2.substGuard, M2.substPure,
      M2.norm, M2.foldNZ, M2.smartAnd, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ,
      hdn, hz]

theorem opt_counted (ctx : GuardIR) (x d i acc : VarId)
    (hid : i ≠ d) (hda : d ≠ acc) (num y : PureExpr) :
    opt ctx (.whileLoop (mkCountedDivLoop x d i acc num y)) =
      let w := mkCountedDivLoop x d i acc num y
      let g := hoist w.init ctx (.nonZero (.var d))
      if g = .top then .whileLoop (fastWhile w (.nonZero (.var d)))
      else .iteLoop g (.whileLoop (fastWhile w (.nonZero (.var d)))) (.whileLoop w) := by
  simp [opt, optWhile, firstDivisor, mkCountedDivLoop, mkDualDivExpr, plan, hda, Ne.symm hid]

theorem opt_counted_known (x d i acc : VarId)
    (hid : i ≠ d) (hda : d ≠ acc) (num y : PureExpr) :
    opt (.nonZero (.var x)) (.whileLoop (mkCountedDivLoop x d i acc num y)) =
      .whileLoop (fastWhile (mkCountedDivLoop x d i acc num y) (.nonZero (.var d))) := by
  rw [opt_counted _ x d i acc hid hda num y]
  simp [mkCountedDivLoop, hoist, synthConj, M2.wp, M2.substGuard, M2.substPure,
    M2.norm, M2.foldNZ, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ]

theorem opt_counted_unknown (x d i acc : VarId)
    (hid : i ≠ d) (hda : d ≠ acc) (num y : PureExpr) :
    opt .top (.whileLoop (mkCountedDivLoop x d i acc num y)) =
      .iteLoop (.nonZero (.var x))
        (.whileLoop (fastWhile (mkCountedDivLoop x d i acc num y) (.nonZero (.var d))))
        (.whileLoop (mkCountedDivLoop x d i acc num y)) := by
  rw [opt_counted _ x d i acc hid hda num y]
  simp only [mkCountedDivLoop, counted_hoist_unknown, reduceCtorEq, ↓reduceIte]

theorem opt_pipeline_known (x z d nextD i acc : VarId)
    (hda : d ≠ acc) (hna : nextD ≠ acc)
    (hid : i ≠ d) (hin : i ≠ nextD) (hdn : d ≠ nextD) (num y : PureExpr) :
    opt (.conj (.nonZero (.var x)) (.nonZero (.var z)))
      (.whileLoop (mkPipelineDivLoop x z d nextD i acc num y)) =
      .whileLoop (fastWhile (mkPipelineDivLoop x z d nextD i acc num y)
        (.conj (.nonZero (.var d)) (.nonZero (.var nextD)))) := by
  simp [opt, optWhile, firstDivisor, mkPipelineDivLoop, mkDualDivExpr, plan,
    hda, hna, Ne.symm hid, Ne.symm hin, hdn, pipeline_hoist_known x z d nextD hdn]

/-- A general countdown cost proof independent of the target declarations. -/
theorem countdown_cost (w : WhileLoop) (inv : GuardIR) (i : VarId) (k : Nat)
    (hcond : w.cond = .nonZero (.var i))
    (hret : ∀ env, execCheckCost env w.ret = 0)
    (hval : ∀ env, evalGuard env inv = true → ∃ v, evalExpr env w.body = .val v)
    (hcost : ∀ env, evalGuard env inv = true → execCheckCost env w.body = k)
    (hlatch : ∀ env, stmtGuardCost env w.latch = 0)
    (hcounter : ∀ env val, execStmt w.latch (updateEnv env w.accVar val) i = env i - 1)
    (hpres : Preserved w.accVar w.latch inv)
    (n : Nat) (env : Env) (hi : env i = Int.ofNat n) (hinv : evalGuard env inv = true) :
    runWhileCheckCost (n + 1) env w = (k + 1) * n + 1 := by
  induction n generalizing env with
  | zero =>
    have hc : evalGuard env w.cond = false := by simp [hcond, evalGuard, evalPure, hi]
    rw [runWhileCheckCost, hc]
    simp [hcond, guardEvalCost, hret]
  | succ n ih =>
    have hnz : env i ≠ 0 := by rw [hi]; simp; omega
    have hc : evalGuard env w.cond = true := by simp [hcond, evalGuard, evalPure, hnz]
    obtain ⟨v, hv⟩ := hval env hinv
    have hi' : execStmt w.latch (updateEnv env w.accVar v) i = Int.ofNat n := by
      rw [hcounter, hi]
      simp
    have hn := ih _ hi' (hpres env v hinv)
    rw [runWhileCheckCost, hc]
    simp only [↓reduceIte, hv, hcost env hinv, hlatch, hn]
    rw [hcond]
    simp only [guardEvalCost, Nat.mul_add, Nat.mul_one]
    simp only [Nat.zero_add]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


theorem loop_pair_cost (w : WhileLoop) (inv : GuardIR) (i acc d : VarId) (num y : PureExpr)
    (hcond : w.cond = .nonZero (.var i)) (hbody : w.body = sourceBody acc num y d)
    (hret : ∀ env, execCheckCost env w.ret = 0)
    (hnz : M1R2.hasNZ inv (.var d) = true)
    (hlatch : ∀ env, stmtGuardCost env w.latch = 0)
    (hcounter : ∀ env val, execStmt w.latch (updateEnv env w.accVar val) i = env i - 1)
    (hpres : Preserved w.accVar w.latch inv)
    (n : Nat) (env : Env) (hi : env i = Int.ofNat n) (hinv : evalGuard env inv = true) :
    runWhileCheckCost (n + 1) env w = 3 * n + 1 ∧
      runWhileCheckCost (n + 1) env (fastWhile w inv) = n + 1 := by
  have hd : ∀ rho, evalGuard rho inv = true → rho d ≠ 0 := by
    intro rho hr
    exact M1R2.hasNZ_sound inv (.var d) rho hnz hr
  have hv : ∀ rho, evalGuard rho inv = true → ∃ v, evalExpr rho w.body = .val v := by
    intro rho hr
    rw [hbody]
    exact source_body_value acc num y d rho (hd rho hr)
  constructor
  · exact countdown_cost w inv i 2 hcond hret hv
      (fun rho hr => by rw [hbody]; exact source_body_cost acc num y d rho (hd rho hr))
      hlatch hcounter hpres n env hi hinv
  · have hcf : ∀ rho, evalGuard rho inv = true → execCheckCost rho (fastWhile w inv).body = 0 := by
      intro rho _
      change execCheckCost rho (M1R2.core inv w.body) = 0
      rw [hbody, core_body inv acc num y d hnz]
      exact (fast_body_metrics acc num y d rho).2.2
    have hvf : ∀ rho, evalGuard rho inv = true →
        ∃ v, evalExpr rho (fastWhile w inv).body = .val v := by
      intro rho hr
      obtain ⟨v, hv⟩ := hv rho hr
      exact ⟨v, (M1R2.core_sound inv w.body rho hr).trans hv⟩
    simpa using countdown_cost (fastWhile w inv) inv i 0 hcond hret hvf hcf
      hlatch hcounter hpres n env hi hinv

theorem fast_loop_metrics (w : WhileLoop) (inv : GuardIR) (acc d : VarId) (num y : PureExpr)
    (hbody : w.body = sourceBody acc num y d) (hret : w.ret = .pure (.var acc))
    (hnz : M1R2.hasNZ inv (.var d) = true) :
    loopCheckedDivCount (.whileLoop (fastWhile w inv)) = 0 ∧
      loopDivOpCount (.whileLoop (fastWhile w inv)) ≤ 1 ∧
      loopBranchCount (.whileLoop (fastWhile w inv)) = 0 := by
  simp [loopCheckedDivCount, loopDivOpCount, loopBranchCount, fastWhile,
    hbody, hret, core_body inv acc num y d hnz, fastBody, M1R2.fastDual,
    checkedDivCount, divOpCount]

theorem counted_costs (x d i acc : VarId) (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n) (hx : evalGuard env (.nonZero (.var x)) = true) :
    execLoopCheckCost (n + 1) env (.whileLoop (mkCountedDivLoop x d i acc num y)) = 3 * n + 1 ∧
      execLoopCheckCost (n + 1) env
        (.whileLoop (fastWhile (mkCountedDivLoop x d i acc num y) (.nonZero (.var d)))) = n + 1 := by
  have hnz : M1R2.hasNZ (.nonZero (.var d)) (.var d) = true := by simp [M1R2.hasNZ]
  have hi' : execStmt (.assign d (.var x)) env i = Int.ofNat n := by
    simpa [execStmt, updateEnv, hid] using hi
  have hd' : evalGuard (execStmt (.assign d (.var x)) env) (.nonZero (.var d)) = true := by
    simpa [evalGuard, evalPure, execStmt, updateEnv] using (of_decide_eq_true hx)
  have hp := loop_pair_cost (mkCountedDivLoop x d i acc num y) (.nonZero (.var d))
    i acc d num y rfl rfl (fun _ => rfl) hnz (fun _ => rfl)
    (by intro rho val; simp [mkCountedDivLoop, execStmt, evalPure, updateEnv, hia])
    (stationary_preserved acc d i (.sub (.var i) (.lit 1)) hda (Ne.symm hid))
    n (execStmt (.assign d (.var x)) env) hi' hd'
  simpa only [execLoopCheckCost, fastWhile, mkCountedDivLoop, stmtGuardCost, Nat.zero_add] using hp

theorem known_elim (x d i acc : VarId) (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n) (hx : evalGuard env (.nonZero (.var x)) = true) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    let result := opt (.nonZero (.var x)) src
    loopCheckedDivCount result = 0 ∧ loopDivOpCount result ≤ 1 ∧ loopBranchCount result = 0 ∧
      execLoopCheckCost (n + 1) env result = n + 1 ∧ execLoopCheckCost (n + 1) env src = 3 * n + 1 := by
  dsimp only
  rw [opt_counted_known x d i acc hid hda num y]
  have hm := fast_loop_metrics (mkCountedDivLoop x d i acc num y) (.nonZero (.var d))
    acc d num y rfl rfl (by simp [M1R2.hasNZ])
  have hc := counted_costs x d i acc hid hia hda num y n env hi hx
  exact ⟨hm.1, hm.2.1, hm.2.2, hc.2, hc.1⟩

theorem unknown_hoist (x d i acc : VarId) (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env : Env) (hi : env i = Int.ofNat n) (hx : env x ≠ 0) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    let result := opt .top src
    execLoopCheckCost (n + 1) env result ≤ n + 2 ∧ execLoopCheckCost (n + 1) env src = 3 * n + 1 := by
  have hx' : evalGuard env (.nonZero (.var x)) = true := decide_eq_true hx
  have hc := counted_costs x d i acc hid hia hda num y n env hi hx'
  dsimp only
  refine ⟨?_, hc.1⟩
  rw [opt_counted_unknown x d i acc hid hda num y]
  change 1 + (if evalGuard env (.nonZero (.var x)) then _ else _) ≤ n + 2
  rw [hx']
  simp only [↓reduceIte, hc.2]
  omega

theorem pipeline_elim (x z d nextD i acc : VarId)
    (hda : d ≠ acc) (hna : nextD ≠ acc) (hid : i ≠ d) (hin : i ≠ nextD)
    (hia : i ≠ acc) (hdn : d ≠ nextD) (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n)
    (hctx : evalGuard env (.conj (.nonZero (.var x)) (.nonZero (.var z))) = true) :
    let src := LoopProg.whileLoop (mkPipelineDivLoop x z d nextD i acc num y)
    let result := opt (.conj (.nonZero (.var x)) (.nonZero (.var z))) src
    loopCheckedDivCount result = 0 ∧ loopDivOpCount result ≤ 1 ∧ loopBranchCount result = 0 ∧
      execLoopCheckCost (n + 1) env result = n + 1 := by
  let inv := GuardIR.conj (.nonZero (.var d)) (.nonZero (.var nextD))
  let w := mkPipelineDivLoop x z d nextD i acc num y
  have hnz : M1R2.hasNZ inv (.var d) = true := by simp [inv, M1R2.hasNZ]
  have hi' : execStmt w.init env i = Int.ofNat n := by
    simpa [w, mkPipelineDivLoop, execStmt, updateEnv, hid, hin] using hi
  have hd' : evalGuard (execStmt w.init env) inv = true := by
    apply hoist_top_sound w.init (.conj (.nonZero (.var x)) (.nonZero (.var z))) inv
      (pipeline_hoist_known x z d nextD hdn) env hctx
  have hp := loop_pair_cost w inv i acc d num y rfl rfl (fun _ => rfl) hnz (fun _ => rfl)
    (by intro rho val; simp [w, mkPipelineDivLoop, execStmt, evalPure, updateEnv, hid, hia])
    (pipeline_preserved acc d nextD i (.sub (.var i) (.lit 1)) hda hna (Ne.symm hid) (Ne.symm hin) hdn)
    n (execStmt w.init env) hi' hd'
  have hm := fast_loop_metrics w inv acc d num y rfl rfl hnz
  dsimp only
  rw [opt_pipeline_known x z d nextD i acc hda hna hid hin hdn num y]
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  simpa only [execLoopCheckCost, fastWhile, w, mkPipelineDivLoop, stmtGuardCost, Nat.zero_add] using hp.2


theorem zero_behavior (x d i acc : VarId) (hid : i ≠ d) (_hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env₀ env₁ : Env)
    (_hx₀ : env₀ x = 0) (hi₀ : env₀ i = 0) (hx₁ : env₁ x = 0)
    (hi₁ : env₁ i = Int.ofNat (n + 1)) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    evalLoop 1 env₀ (opt .top src) = .done (.val (env₀ acc)) ∧
      evalLoop (n + 2) env₁ (opt .top src) = .done .trap := by
  dsimp only
  rw [opt_sound 1 .top _ env₀ rfl, opt_sound (n + 2) .top _ env₁ rfl]
  have hinz : env₁ i ≠ 0 := by rw [hi₁]; simp; omega
  constructor
  · simp [evalLoop, mkCountedDivLoop, runWhileSteps, execStmt, evalGuard, evalExpr,
      evalPure, updateEnv, hid, Ne.symm hda, hi₀]
  · simp [evalLoop, mkCountedDivLoop, runWhileSteps, execStmt, evalGuard, evalExpr,
      evalPure, updateEnv, hid, hinz, hx₁, mkDualDivExpr]

theorem decrement_trap (x d i acc : VarId) (hda : d ≠ acc) (hia : i ≠ acc) (hid : i ≠ d)
    (num : PureExpr) (env : Env) (hx : env x = 1) (hi : env i = 2) :
    evalLoop 3 env (opt (.nonZero (.var x))
      (.whileLoop (mkDecrementDivisorLoop x d i acc num))) = .done .trap := by
  rw [opt_sound 3 (.nonZero (.var x)) _ env (by simp [evalGuard, evalPure, hx])]
  simp [evalLoop, mkDecrementDivisorLoop, runWhileSteps, execStmt, evalGuard, evalExpr,
    evalPure, updateEnv, hda, hia, hid, hx, hi, Ne.symm hid]


/-- All fourteen compiler-dependent M3 targets; state_iterate proves the fifteenth target. -/
structure Obligations
    (havocFn : VarId → GuardIR → GuardIR)
    (strengthenFn : VarId → Stmt → GuardIR → Option GuardIR)
    (hoistFn : Stmt → GuardIR → GuardIR → GuardIR)
    (optFn : GuardIR → LoopProg → LoopProg) : Prop where
  havocSound : ∀ v g, denoteGuard (havocFn v g) ≤ (havocTransfer v).pullback (denoteGuard g)
  havocExact : ∀ v g, guardMentionsVar v g = false →
    denoteGuard (havocFn v g) = (havocTransfer v).pullback (denoteGuard g)
  inductiveSound : ∀ acc latch target inv, strengthenFn acc latch target = some inv →
    IsInductiveFor (loopStepTransfer acc latch) (denoteGuard inv) (denoteGuard target)
  stationary : ∀ acc d i, d ≠ acc → d ≠ i →
    ∃ inv, strengthenFn acc (.assign i (.sub (.var i) (.lit 1))) (.nonZero (.var d)) = some inv
  pipeline : ∀ acc d nextD i, d ≠ acc → nextD ≠ acc → d ≠ i → nextD ≠ i → d ≠ nextD →
    ∃ inv, strengthenFn acc
      (.seq (.assign d (.var nextD)) (.assign i (.sub (.var i) (.lit 1))))
      (.nonZero (.var d)) = some inv
  hoistDenote : ∀ init ctx inv, denoteGuard (hoistFn init ctx inv) =
    hoistLoopGuard (stateTransfer (execStmt init)) (denoteGuard ctx) (denoteGuard inv)
  hoistIterate : ∀ init acc latch ctx target inv,
    IsInductiveFor (loopStepTransfer acc latch) (denoteGuard inv) (denoteGuard target) →
    ∀ n : Nat, (((stateTransfer (execStmt init)).comp ((loopStepTransfer acc latch).iterate n)).post
      (denoteGuard ctx ⊓ denoteGuard (hoistFn init ctx inv))) ≤ denoteGuard target
  guarded : ∀ fuel ctx prog,
    GuardedEquiv (liftEval (evalLoop fuel)) (denoteGuard ctx) (optFn ctx prog) prog
  sound : ∀ fuel ctx prog env, evalGuard env ctx = true →
    evalLoop fuel env (optFn ctx prog) = evalLoop fuel env prog
  known : ∀ x d i acc, i ≠ d → i ≠ acc → d ≠ acc →
    ∀ num y (n : Nat) env, env i = Int.ofNat n → evalGuard env (.nonZero (.var x)) = true →
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    let result := optFn (.nonZero (.var x)) src
    loopCheckedDivCount result = 0 ∧ loopDivOpCount result ≤ 1 ∧ loopBranchCount result = 0 ∧
      execLoopCheckCost (n + 1) env result = n + 1 ∧ execLoopCheckCost (n + 1) env src = 3 * n + 1
  unknown : ∀ x d i acc, i ≠ d → i ≠ acc → d ≠ acc →
    ∀ num y (n : Nat) env, env i = Int.ofNat n → env x ≠ 0 →
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    let result := optFn .top src
    execLoopCheckCost (n + 1) env result ≤ n + 2 ∧ execLoopCheckCost (n + 1) env src = 3 * n + 1
  zero : ∀ x d i acc, i ≠ d → i ≠ acc → d ≠ acc →
    ∀ num y (n : Nat) env₀ env₁,
    env₀ x = 0 → env₀ i = 0 → env₁ x = 0 → env₁ i = Int.ofNat (n + 1) →
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    evalLoop 1 env₀ (optFn .top src) = .done (.val (env₀ acc)) ∧
      evalLoop (n + 2) env₁ (optFn .top src) = .done .trap
  pipelineElim : ∀ x z d nextD i acc, d ≠ acc → nextD ≠ acc →
    i ≠ d → i ≠ nextD → i ≠ acc → d ≠ nextD →
    ∀ num y (n : Nat) env, env i = Int.ofNat n →
    evalGuard env (.conj (.nonZero (.var x)) (.nonZero (.var z))) = true →
    let src := LoopProg.whileLoop (mkPipelineDivLoop x z d nextD i acc num y)
    let result := optFn (.conj (.nonZero (.var x)) (.nonZero (.var z))) src
    loopCheckedDivCount result = 0 ∧ loopDivOpCount result ≤ 1 ∧ loopBranchCount result = 0 ∧
      execLoopCheckCost (n + 1) env result = n + 1
  decrement : ∀ x d i acc, d ≠ acc → i ≠ acc → i ≠ d →
    ∀ num env, env x = 1 → env i = 2 →
    evalLoop 3 env (optFn (.nonZero (.var x))
      (.whileLoop (mkDecrementDivisorLoop x d i acc num))) = .done .trap

theorem constructive_obligations : Obligations havoc constructiveStrengthen hoist opt where
  havocSound := havoc_sound
  havocExact := havoc_exact
  inductiveSound := constructive_inductive
  stationary := fun acc d i hda hdi => ⟨_, constructive_stationary acc d i hda hdi⟩
  pipeline := fun acc d nextD i hda hna hdi hni hdn =>
    ⟨_, constructive_pipeline acc d nextD i hda hna hdi hni hdn⟩
  hoistDenote := hoist_denote
  hoistIterate := hoist_iterate
  guarded := opt_guarded
  sound := opt_sound
  known := known_elim
  unknown := unknown_hoist
  zero := zero_behavior
  pipelineElim := pipeline_elim
  decrement := decrement_trap

/-- Replacing the strengthening component with constant false preserves the entire contract. -/
theorem replace_strengthener
    (havocFn : VarId → GuardIR → GuardIR)
    (strengthenFn : VarId → Stmt → GuardIR → Option GuardIR)
    (hoistFn : Stmt → GuardIR → GuardIR → GuardIR)
    (optFn : GuardIR → LoopProg → LoopProg)
    (h : Obligations havocFn strengthenFn hoistFn optFn) :
    Obligations havocFn vacuousStrengthen hoistFn optFn where
  havocSound := h.havocSound
  havocExact := h.havocExact
  inductiveSound := vacuous_inductive
  stationary := vacuous_stationary
  pipeline := vacuous_pipeline
  hoistDenote := h.hoistDenote
  hoistIterate := h.hoistIterate
  guarded := h.guarded
  sound := h.sound
  known := h.known
  unknown := h.unknown
  zero := h.zero
  pipelineElim := h.pipelineElim
  decrement := h.decrement

theorem vacuous_obligations : Obligations havoc vacuousStrengthen hoist opt :=
  replace_strengthener havoc constructiveStrengthen hoist opt constructive_obligations

theorem satisfiable :
    ∃ (h : VarId → GuardIR → GuardIR) (s : VarId → Stmt → GuardIR → Option GuardIR)
      (g : Stmt → GuardIR → GuardIR → GuardIR) (o : GuardIR → LoopProg → LoopProg),
      Obligations h s g o := ⟨havoc, constructiveStrengthen, hoist, opt, constructive_obligations⟩

/-- A full executable model of all targets with an everywhere-uninhabited strengthening result. -/
theorem vacuous_countermodel :
    Obligations havoc vacuousStrengthen hoist opt ∧
      ∀ acc latch target inv, vacuousStrengthen acc latch target = some inv →
        ¬ ∃ env, evalGuard env inv = true :=
  ⟨vacuous_obligations, vacuous_result_uninhabited⟩


def pipelineLatch : Stmt := .seq (.assign 0 (.var 1)) (.assign 2 (.sub (.var 2) (.lit 1)))
def pipelineTarget : GuardIR := .nonZero (.var 0)
def pipelineInvariant : GuardIR := .conj pipelineTarget (.nonZero (.var 1))
def unstableHeader : Env := fun v => if v = 0 then 1 else 0

theorem pipeline_target_not_inductive :
    ¬ IsInductiveFor (loopStepTransfer 3 pipelineLatch)
      (denoteGuard pipelineTarget) (denoteGuard pipelineTarget) := by
  intro h
  have hb := ((preserved_iff 3 pipelineLatch pipelineTarget).mpr h.1) unstableHeader 0 (by decide)
  change false = true at hb
  cases hb

/-- A planner restricted to none or the unchanged target is rejected by the pipeline target. -/
theorem zero_step_only_rejected
    (hf : VarId → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (gf : Stmt → GuardIR → GuardIR → GuardIR) (ofn : GuardIR → LoopProg → LoopProg)
    (h : Obligations hf sf gf ofn) :
    ¬ (∀ acc latch target, sf acc latch target = none ∨ sf acc latch target = some target) := by
  intro hz
  obtain ⟨inv, hi⟩ := h.pipeline 3 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  change sf 3 pipelineLatch pipelineTarget = some inv at hi
  rcases hz 3 pipelineLatch pipelineTarget with hn | ht
  · rw [hn] at hi
    cases hi
  · have he : inv = pipelineTarget := Option.some.inj (hi.symm.trans ht)
    subst inv
    exact pipeline_target_not_inductive (h.inductiveSound 3 pipelineLatch pipelineTarget pipelineTarget hi)

def countedFamily (k : Nat) : LoopProg :=
  .whileLoop (mkCountedDivLoop 0 1 2 3 (.var (k + 4)) (.lit 5))

theorem counted_family_injective : Function.Injective countedFamily := by
  intro a b h
  simpa [countedFamily, mkCountedDivLoop, mkDualDivExpr] using h

theorem finite_fixture_rejected
    (hf : VarId → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (gf : Stmt → GuardIR → GuardIR → GuardIR) (ofn : GuardIR → LoopProg → LoopProg)
    (h : Obligations hf sf gf ofn) :
    ¬ ∃ N : Nat, ∀ k, N < k →
      ofn (.nonZero (.var 0)) (countedFamily k) = countedFamily k := by
  rintro ⟨N, hfix⟩
  have he := hfix (N + 1) (by omega)
  have hc := (h.known 0 1 2 3 (by decide) (by decide) (by decide)
    (.var (N + 1 + 4)) (.lit 5) 1 (fun _ => 1) rfl rfl).1
  change loopCheckedDivCount (ofn (.nonZero (.var 0)) (countedFamily (N + 1))) = 0 at hc
  rw [he] at hc
  change (2 : Nat) = 0 at hc
  cases hc

theorem identity_rejected
    (hf : VarId → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (gf : Stmt → GuardIR → GuardIR → GuardIR) :
    ¬ Obligations hf sf gf (fun _ p => p) := by
  intro h
  exact finite_fixture_rejected hf sf gf _ h ⟨0, fun _ _ => rfl⟩

theorem havoc_written_nonzero_rejected (env : Env) :
    ¬ (havocTransfer 0).pullback (denoteGuard (.nonZero (.var 0))) env := by
  intro h
  have hz := h 0
  change false = true at hz
  cases hz

theorem havoc_constant_false_rejected :
    ¬ (denoteGuard (.bot : GuardIR) = (havocTransfer 0).pullback (denoteGuard .top)) := by
  intro h
  have hf : denoteGuard .bot (fun _ => 0) :=
    Eq.mpr (congrFun h (fun _ => 0)) (fun _ => rfl)
  cases hf

theorem loop_iterate_nonempty (acc : VarId) (latch : Stmt) (P : Env → Prop)
    (h : ∃ env, P env) (n : Nat) :
    ∃ env, ((loopStepTransfer acc latch).iterate n).post P env := by
  induction n with
  | zero => exact h
  | succ n ih =>
    obtain ⟨env, he⟩ := ih
    exact ⟨execStmt latch (updateEnv env acc 0), updateEnv env acc 0, rfl, env, 0, rfl, he⟩

theorem strengthened_pipeline_active :
    constructiveStrengthen 3 pipelineLatch pipelineTarget = some pipelineInvariant ∧
      evalGuard (fun _ => 1) pipelineInvariant = true ∧
      IsInductiveFor (loopStepTransfer 3 pipelineLatch)
        (denoteGuard pipelineInvariant) (denoteGuard pipelineTarget) := by
  have hc : constructiveStrengthen 3 pipelineLatch pipelineTarget = some pipelineInvariant := by decide
  exact ⟨hc, by decide, constructive_inductive 3 pipelineLatch pipelineTarget pipelineInvariant hc⟩

theorem strengthened_pipeline_reachable (n : Nat) :
    ∃ env, ((loopStepTransfer 3 pipelineLatch).iterate n).post (denoteGuard pipelineInvariant) env :=
  loop_iterate_nonempty 3 pipelineLatch (denoteGuard pipelineInvariant) ⟨fun _ => 1, rfl⟩ n

theorem strengthened_pipeline_all_depths_active (n : Nat) :
    ∃ env, ((loopStepTransfer 3 pipelineLatch).iterate n).post (denoteGuard pipelineInvariant) env ∧
      evalGuard env pipelineTarget = true := by
  obtain ⟨env, hreach⟩ := strengthened_pipeline_reachable n
  have hi := strengthened_pipeline_active.2.2
  exact ⟨env, hreach, hi.2 env (Round6.iterate_invariant _ _ hi.1 n env hreach)⟩


def countEnv (x i acc : Int) : Env :=
  fun v => if v = 0 then x else if v = 2 then i else if v = 3 then acc else 0
def pipeEnv (x z i acc : Int) : Env :=
  fun v => if v = 0 then x else if v = 1 then z else if v = 4 then i else if v = 5 then acc else 0
def counted : WhileLoop := mkCountedDivLoop 0 1 2 3 (.lit 8) (.lit 5)
def pipelined : WhileLoop := mkPipelineDivLoop 0 1 2 3 4 5 (.lit 8) (.lit 5)
def decrementing : WhileLoop := mkDecrementDivisorLoop 0 1 2 3 (.lit 8)
def unsafeEntryOnly : LoopProg := .whileLoop (fastWhile decrementing (.nonZero (.var 1)))
def unsafeEagerCheck : LoopProg :=
  .iteLoop (.nonZero (.var 0))
    (.whileLoop (fastWhile counted (.nonZero (.var 1))))
    (.whileLoop {counted with cond := .bot, ret := M1.trapExpr})

theorem counted_concrete_cost_and_fuel :
    evalGuard (countEnv 2 2 0) (.nonZero (.var 0)) = true ∧
    evalLoop 0 (countEnv 2 2 0) (.whileLoop counted) = .outOfFuel ∧
    evalLoop 1 (countEnv 2 2 0) (.whileLoop counted) = .outOfFuel ∧
    evalLoop 2 (countEnv 2 2 0) (.whileLoop counted) = .outOfFuel ∧
    evalLoop 3 (countEnv 2 2 0) (.whileLoop counted) = .done (.val 18) ∧
    evalLoop 3 (countEnv 2 2 0) (opt (.nonZero (.var 0)) (.whileLoop counted)) = .done (.val 18) ∧
    execLoopCheckCost 3 (countEnv 2 2 0) (.whileLoop counted) = 7 ∧
    execLoopCheckCost 3 (countEnv 2 2 0) (opt (.nonZero (.var 0)) (.whileLoop counted)) = 3 ∧
    execLoopCheckCost 3 (countEnv 2 2 0) (opt .top (.whileLoop counted)) = 4 := by
  decide

theorem signed_and_nonterminating_counter_cases :
    evalLoop 3 (countEnv (-2) 2 0) (.whileLoop counted) = .done (.val 2) ∧
    evalLoop 3 (countEnv (-2) 2 0) (opt .top (.whileLoop counted)) = .done (.val 2) ∧
    evalLoop 3 (countEnv 2 (-1) 0) (.whileLoop counted) = .outOfFuel ∧
    evalLoop 3 (countEnv 2 (-1) 0) (opt .top (.whileLoop counted)) = .outOfFuel := by
  decide

theorem zero_trip_and_positive_trip :
    evalLoop 1 (countEnv 0 0 5) (.whileLoop counted) = .done (.val 5) ∧
    evalLoop 1 (countEnv 0 0 5) (opt .top (.whileLoop counted)) = .done (.val 5) ∧
    evalLoop 2 (countEnv 0 1 5) (.whileLoop counted) = .done .trap ∧
    evalLoop 2 (countEnv 0 1 5) (opt .top (.whileLoop counted)) = .done .trap ∧
    execLoopCheckCost 1 (countEnv 0 0 5) (.whileLoop counted) = 1 ∧
    execLoopCheckCost 1 (countEnv 0 0 5) (opt .top (.whileLoop counted)) = 2 := by
  decide

theorem eager_zero_trip_trap_is_unsound :
    evalLoop 1 (countEnv 0 0 5) unsafeEagerCheck = .done .trap ∧
    evalLoop 1 (countEnv 0 0 5) unsafeEagerCheck ≠ evalLoop 1 (countEnv 0 0 5) (.whileLoop counted) := by
  decide

theorem entry_only_elimination_is_unsound :
    evalGuard (countEnv 1 2 0) (.nonZero (.var 0)) = true ∧
    evalLoop 1 (countEnv 1 2 0) (.whileLoop decrementing) = .outOfFuel ∧
    evalLoop 1 (countEnv 1 2 0) unsafeEntryOnly = .outOfFuel ∧
    evalLoop 3 (countEnv 1 2 0) (.whileLoop decrementing) = .done .trap ∧
    evalLoop 3 (countEnv 1 2 0) unsafeEntryOnly = .done .ub ∧
    evalLoop 3 (countEnv 1 2 0) (opt (.nonZero (.var 0)) (.whileLoop decrementing)) = .done .trap := by
  decide

theorem pipeline_concrete_strengthening :
    evalGuard (pipeEnv 2 (-2) 3 0) (.conj (.nonZero (.var 0)) (.nonZero (.var 1))) = true ∧
    constructiveStrengthen 5 pipelined.latch (.nonZero (.var 2)) =
      some (.conj (.nonZero (.var 2)) (.nonZero (.var 3))) ∧
    evalLoop 4 (pipeEnv 2 (-2) 3 0) (.whileLoop pipelined) = .done (.val 11) ∧
    evalLoop 4 (pipeEnv 2 (-2) 3 0)
      (opt (.conj (.nonZero (.var 0)) (.nonZero (.var 1))) (.whileLoop pipelined)) = .done (.val 11) ∧
    loopCheckedDivCount
      (opt (.conj (.nonZero (.var 0)) (.nonZero (.var 1))) (.whileLoop pipelined)) = 0 ∧
    execLoopCheckCost 4 (pipeEnv 2 (-2) 3 0) (.whileLoop pipelined) = 10 ∧
    execLoopCheckCost 4 (pipeEnv 2 (-2) 3 0)
      (opt (.conj (.nonZero (.var 0)) (.nonZero (.var 1))) (.whileLoop pipelined)) = 4 := by
  decide

theorem pipeline_second_stage_zero_traps :
    evalLoop 3 (pipeEnv 2 0 2 0) (.whileLoop pipelined) = .done .trap ∧
    evalLoop 3 (pipeEnv 2 0 2 0) (opt .top (.whileLoop pipelined)) = .done .trap ∧
    evalLoop 1 (pipeEnv 0 0 0 7) (opt .top (.whileLoop pipelined)) = .done (.val 7) := by
  decide

/-- The accepted false invariant rejects an actually safe, nonempty entry context. -/
theorem vacuous_success_rejects_safe_entry :
    evalGuard (pipeEnv 2 (-2) 3 0) (.conj (.nonZero (.var 0)) (.nonZero (.var 1))) = true ∧
    vacuousStrengthen 5 pipelined.latch (.nonZero (.var 2)) = some .bot ∧
    evalGuard (pipeEnv 2 (-2) 3 0)
      (hoist pipelined.init (.conj (.nonZero (.var 0)) (.nonZero (.var 1))) .bot) = false := by
  decide

def accumulatorThenLatch : WhileLoop :=
  {init := .skip, cond := .nonZero (.var 0), accVar := 0,
   body := .pure (.lit 0), latch := .assign 1 (.var 0), ret := .pure (.var 1)}
def failingBody (e : Expr) : WhileLoop :=
  {init := .skip, cond := .top, accVar := 0, body := e,
   latch := .ite (.nonZero (.var 1)) .skip .skip, ret := M1.trapExpr}
def guardInInit : WhileLoop :=
  {init := .ite (.nonZero (.var 0)) .skip .skip, cond := .bot,
   accVar := 0, body := M1.ubExpr, latch := .skip, ret := .pure (.lit 7)}

theorem accumulator_write_precedes_latch :
    evalLoop 2 (fun _ => 1) (.whileLoop accumulatorThenLatch) = .done (.val 0) ∧
    execLoopCheckCost 2 (fun _ => 1) (.whileLoop accumulatorThenLatch) = 2 := by
  decide

theorem failures_skip_latch_and_return :
    evalLoop 1 (fun _ => 1) (.whileLoop (failingBody M1.trapExpr)) = .done .trap ∧
    execLoopCheckCost 1 (fun _ => 1) (.whileLoop (failingBody M1.trapExpr)) = 1 ∧
    evalLoop 1 (fun _ => 1) (.whileLoop (failingBody M1.ubExpr)) = .done .ub ∧
    execLoopCheckCost 1 (fun _ => 1) (.whileLoop (failingBody M1.ubExpr)) = 0 := by
  decide

theorem fuel_zero_retains_prefix_cost :
    evalLoop 0 (fun _ => 1) (.whileLoop guardInInit) = .outOfFuel ∧
    execLoopCheckCost 0 (fun _ => 1) (.whileLoop guardInInit) = 1 ∧
    evalLoop 1 (fun _ => 1) (.whileLoop guardInInit) = .done (.val 7) ∧
    evalLoop 0 (countEnv 2 2 0) (opt .top (.whileLoop counted)) = .outOfFuel ∧
    execLoopCheckCost 0 (countEnv 2 2 0) (opt .top (.whileLoop counted)) = 1 := by
  decide

theorem havoc_independent_positive :
    (havocTransfer 0).pullback (denoteGuard (.eq (.var 1) (.lit 5))) (fun _ => 5) := by
  intro val
  rfl

theorem conservative_havoc_may_reject_dependent_tautology :
    havoc 0 (.eq (.var 0) (.var 0)) = .bot ∧
      (havocTransfer 0).pullback (denoteGuard (.eq (.var 0) (.var 0))) (fun _ => 5) := by
  refine ⟨rfl, ?_⟩
  intro val
  simp [denoteGuard, evalGuard, evalPure]

end M3


/-!
## Milestone 3 Gate 1 re-review (Round 2, historical eighteen-target contract)
Spec digest: 3caeef405a5117aadae5081939cc243ffa4dc63e902d00aee35bd6bbba824a44.

The new stationary/pipeline coverage clauses reject some .bot and finite exact
fixture tables with none/bottom fallbacks. The general one-step obligation,
however, has an admissible vacuous premise: M1R2.synth never returns .top when
its context is a conjunction and its target is .bot or a conjunction; M2.wp
preserves the outer conjunction of the candidate, and M3.havoc returns either
that conjunction or .bot. weak_closure_never_top proves this for all inputs.

shape_countermodel_compatible_with_m1_m2 verifies every earlier helper contract
and every revised M3 obligation for the original two-form planner, which rejects
the inhabited wrappedLatch family. This is the remaining B1-R2 defect.

A separate total uniform one-step algorithm uses conjunction discharge, returns
the candidate only after its syntactic preservation check succeeds, and satisfies
all revised targets. Its helper synthesizer also satisfies the full M1 contract.
The generic state-iteration theorem remains M3.state_iterate. No Specs.Target
compiler stub or theorem is invoked.
-/

namespace M3R2
def StationarySafe (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (hf : Stmt → GuardIR → GuardIR → GuardIR) : Prop :=
  ∀ acc d i, d ≠ acc → d ≠ i → ∀ rhs : PureExpr,
    ∃ inv, sf acc (.assign i rhs) (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → evalGuard env inv = true) ∧
      (∀ x : VarId, hf (.assign d (.var x)) (.nonZero (.var x)) inv = .top)

def PipelineSafe (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (hf : Stmt → GuardIR → GuardIR → GuardIR) : Prop :=
  ∀ acc d nextD i, d ≠ acc → nextD ≠ acc → d ≠ i → nextD ≠ i → d ≠ nextD →
    ∀ rhs : PureExpr,
    ∃ inv, sf acc (.seq (.assign d (.var nextD)) (.assign i rhs)) (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → env nextD ≠ 0 → evalGuard env inv = true) ∧
      (∀ x z : VarId, hf (.seq (.assign d (.var x)) (.assign nextD (.var z)))
        (.conj (.nonZero (.var x)) (.nonZero (.var z))) inv = .top)

def StepComplete (hav : VarId → GuardIR → GuardIR) (pb : Stmt → GuardIR → GuardIR)
    (sg : GuardIR → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR) : Prop :=
  ∀ acc latch target,
    let g₁ := hav acc (pb latch target)
    let cand := GuardIR.conj target g₁
    sg cand (hav acc (pb latch cand)) = .top →
      ∃ inv, sf acc latch target = some inv ∧
        (∀ env : Env, evalGuard env target = true → evalGuard env g₁ = true → evalGuard env inv = true)

/-- The revised eighteen-target contract, with the generic state-iteration theorem separate. -/
structure UpdatedObligations
    (hav : VarId → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (hf : Stmt → GuardIR → GuardIR → GuardIR) (opt : GuardIR → LoopProg → LoopProg)
    (pb : Stmt → GuardIR → GuardIR) (sg : GuardIR → GuardIR → GuardIR) : Prop where
  original : M3.Obligations hav sf hf opt
  stationarySafe : StationarySafe sf hf
  pipelineSafe : PipelineSafe sf hf
  stepComplete : StepComplete hav pb sg sf

theorem bottom_rejected (hf : Stmt → GuardIR → GuardIR → GuardIR) :
    ¬ StationarySafe M3.vacuousStrengthen hf := by
  intro h
  obtain ⟨inv, hs, hc, _⟩ := h 3 0 2 (by decide) (by decide) (.lit 9)
  have hi : inv = .bot := (Option.some.inj hs).symm
  subst inv
  have bad := hc (fun _ => 1) (by decide)
  cases bad

def latchFamily (k : Nat) : Stmt := .assign 2 (.lit (Int.ofNat k))
theorem latch_family_injective : Function.Injective latchFamily := by
  intro a b h
  have hc : (a : Int) = (b : Int) := by simpa [latchFamily] using h
  omega

/-- No finite exact fixture table may fall back to either none or some .bot on fresh literals. -/
theorem finite_fixture_fallback_rejected
    (sf : VarId → Stmt → GuardIR → Option GuardIR) (hf : Stmt → GuardIR → GuardIR → GuardIR)
    (h : StationarySafe sf hf) :
    ¬ ∃ N : Nat, ∀ k, N < k →
      sf 3 (latchFamily k) (.nonZero (.var 0)) = none ∨
        sf 3 (latchFamily k) (.nonZero (.var 0)) = some .bot := by
  rintro ⟨N, hn⟩
  obtain ⟨inv, hs, hc, _⟩ := h 3 0 2 (by decide) (by decide) (.lit (Int.ofNat (N + 1)))
  change sf 3 (latchFamily (N + 1)) (.nonZero (.var 0)) = some inv at hs
  rcases hn (N + 1) (by omega) with he | he
  · rw [he] at hs
    cases hs
  · have hi : inv = .bot := Option.some.inj (hs.symm.trans he)
    subst inv
    have bad := hc (fun _ => 1) (by decide)
    cases bad

theorem hoist_assign (x d : VarId) :
    M3.hoist (.assign d (.var x)) (.nonZero (.var x)) (.nonZero (.var d)) = .top := by
  simp [M3.hoist, M3.synthConj, M2.wp, M2.substGuard, M2.substPure,
    M2.norm, M2.foldNZ, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ]

theorem shape_stationary_safe : StationarySafe M3.constructiveStrengthen M3.hoist := by
  intro acc d i hda hdi rhs
  refine ⟨.nonZero (.var d), ?_, ?_, ?_⟩
  · simp [M3.constructiveStrengthen, M3.plan, hda, hdi]
  · intro env hd
    exact decide_eq_true hd
  · exact fun x => hoist_assign x d

theorem shape_pipeline_safe : PipelineSafe M3.constructiveStrengthen M3.hoist := by
  intro acc d nextD i hda hna hdi hni hdn rhs
  refine ⟨.conj (.nonZero (.var d)) (.nonZero (.var nextD)), ?_, ?_, ?_⟩
  · simp [M3.constructiveStrengthen, M3.plan, hda, hna, hdi, hni, hdn]
  · intro env hd hn
    simp [evalGuard, evalPure, hd, hn]
  · exact fun x z => M3.pipeline_hoist_known x z d nextD hdn

theorem pullback_conj_shape (s : Stmt) (a b : GuardIR) :
    ∃ c d, M2.wp s (.conj a b) = .conj c d := by
  induction s generalizing a b with
  | skip => exact ⟨a, b, rfl⟩
  | assign v rhs => exact ⟨_, _, rfl⟩
  | seq s₁ s₂ ih₁ ih₂ =>
    obtain ⟨c, d, he⟩ := ih₂ a b
    simp only [M2.wp, he]
    exact ih₁ c d
  | ite cond t f iht ihf => exact ⟨_, _, rfl⟩

/-- A permitted M1 synthesizer and M2 pullback make the new general closure premise impossible. -/
theorem weak_closure_never_top (acc : VarId) (latch : Stmt) (target : GuardIR) :
    let g₁ := M3.havoc acc (M2.wp latch target)
    let cand := GuardIR.conj target g₁
    M1R2.synth cand (M3.havoc acc (M2.wp latch cand)) ≠ .top := by
  dsimp only
  obtain ⟨a, b, hw⟩ := pullback_conj_shape latch target (M3.havoc acc (M2.wp latch target))
  rw [hw]
  cases hm : guardMentionsVar acc (.conj a b) <;> simp [M3.havoc, hm, M1R2.synth]

theorem shape_step_complete :
    StepComplete M3.havoc M2.wp M1R2.synth M3.constructiveStrengthen := by
  intro acc latch target
  dsimp only
  intro h
  exact False.elim (weak_closure_never_top acc latch target h)

theorem shape_all_obligations :
    UpdatedObligations M3.havoc M3.constructiveStrengthen M3.hoist M3.opt M2.wp M1R2.synth where
  original := M3.constructive_obligations
  stationarySafe := shape_stationary_safe
  pipelineSafe := shape_pipeline_safe
  stepComplete := shape_step_complete

/-- The weak helper functions are valid implementations of the earlier complete M1/M2 contracts. -/
theorem shape_countermodel_compatible_with_m1_m2 :
    M1R2.UpdatedObligations M1R2.synth M1R2.opt ∧
      M2.Obligations M2.wp M2.synthStmt M2.blockOpt ∧
      UpdatedObligations M3.havoc M3.constructiveStrengthen M3.hoist M3.opt M2.wp M1R2.synth :=
  ⟨M1R2.all_obligations, M2.all_obligations, shape_all_obligations⟩

def wrappedLatch (k : Nat) : Stmt := .seq .skip (latchFamily k)
theorem shape_rejects_wrapped_family (k : Nat) :
    M3.constructiveStrengthen 3 (wrappedLatch k) (.nonZero (.var 0)) = none := by
  rfl

theorem wrapped_family_is_safe (k : Nat) :
    M3.Preserved 3 (wrappedLatch k) (.nonZero (.var 0)) :=
  M3.stationary_preserved 3 0 2 (.lit (Int.ofNat k)) (by decide) (by decide)

theorem wrapped_family_is_inhabited :
    evalGuard (fun _ => 1) (.nonZero (.var 0)) = true := rfl


/-- A more capable yet still total syntactic synthesizer, with conjunction discharge. -/
def synth (a b : GuardIR) : GuardIR := M1R2.shrink (M3.synthConj a b)

theorem synth_eval (a b : GuardIR) (env : Env) :
    evalGuard env (synth a b) = (!evalGuard env a || evalGuard env b) := by
  simp only [synth, M1R2.shrink_eval, M3.synthConj_eval]

theorem synth_denote_eq (a b : GuardIR) :
    denoteGuard (synth a b) = denoteGuard (M1R2.synth a b) := by
  funext env
  exact congrArg (fun v : Bool => v = true) ((synth_eval a b env).trans (M1R2.synth_eval a b env).symm)

theorem synth_denote (a b : GuardIR) :
    denoteGuard (synth a b) = synthesizeGuard (denoteGuard a) (denoteGuard b) :=
  (synth_denote_eq a b).trans (M1R2.synth_denote a b)

theorem synth_universal (a b : GuardIR) (g : Env → Prop) :
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synth a b) := by
  rw [synth_denote_eq]
  exact M1R2.synth_universal a b g

theorem synth_self (p : PureExpr) : synth (.nonZero p) (.nonZero p) = .top := by
  simp [synth, M3.synthConj, M1R2.synth_self, M1R2.shrink]

theorem synth_top_right (a : GuardIR) : synth a .top = .top := by
  simp [synth, M3.synthConj, M1R2.synth_top_right, M1R2.shrink]

theorem synthConj_bot (b : GuardIR) : M3.synthConj .bot b = .top := by
  induction b with
  | conj a b iha ihb => simp [M3.synthConj, iha, ihb, M2.smartAnd]
  | _ => rfl

theorem synth_bot_left (b : GuardIR) : synth .bot b = .top := by
  simp [synth, synthConj_bot, M1R2.shrink]

theorem synth_top_left_nonZero (p : PureExpr) : synth .top (.nonZero p) = .nonZero p := by
  simp [synth, M3.synthConj, M1R2.synth_top_left_nonZero, M1R2.shrink]

theorem synth_conj_left (p : PureExpr) (rest : GuardIR) :
    synth (.conj (.nonZero p) rest) (.nonZero p) = .top := by
  simp [synth, M3.synthConj, M1R2.synth_conj_left, M1R2.shrink]

theorem synth_conj_right (rest : GuardIR) (p : PureExpr) :
    synth (.conj rest (.nonZero p)) (.nonZero p) = .top := by
  simp [synth, M3.synthConj, M1R2.synth_conj_right, M1R2.shrink]

theorem synth_dedup (p : PureExpr) :
    synth .top (.conj (.nonZero p) (.nonZero p)) = .nonZero p := by
  simp [synth, M3.synthConj, M1R2.synth_top_left_nonZero, M2.smartAnd, M1R2.shrink]

theorem synth_sound (a b : GuardIR) (env : Env)
    (ha : evalGuard env a = true) (hg : evalGuard env (synth a b) = true) :
    evalGuard env b = true := by
  rw [synth_eval, ha] at hg
  exact hg

/-- This stronger synthesizer also satisfies every existing M1 synthesis obligation. -/
theorem strong_m1 : M1R2.UpdatedObligations synth M1R2.opt where
  original := {
    guardDenote := synth_denote
    universal := synth_universal
    selfDischarge := synth_self
    guarded := M1R2.opt_guarded
    sound := M1R2.opt_sound
    known := M1R2.known_ctx_elim
    cancel := M1R2.cancel_div
    dedup := M1R2.unknown_ctx_dedup
    trap := M1R2.zero_div_trap }
  topRight := synth_top_right
  botLeft := synth_bot_left
  topLeftNZ := synth_top_left_nonZero
  dischargeLeft := synth_conj_left
  dischargeRight := synth_conj_right
  dedupConj := synth_dedup
  elimParam := M1R2.elim_checkedDiv_param
  cancelParam := M1R2.cancel_div_param
  compositional := M1R2.compositional_binary
  knownParam := M1R2.known_ctx_elim_param
  dedupParam := M1R2.unknown_ctx_dedup_param
  trapParam := M1R2.zero_div_trap_param


def pre (acc : VarId) (latch : Stmt) (g : GuardIR) : GuardIR :=
  M3.havoc acc (M2.wp latch g)
def candidate (acc : VarId) (latch : Stmt) (target : GuardIR) : GuardIR :=
  .conj target (pre acc latch target)
def closure (acc : VarId) (latch : Stmt) (target : GuardIR) : GuardIR :=
  synth (candidate acc latch target) (pre acc latch (candidate acc latch target))

/-- One uniform bounded analysis of every Stmt/GuardIR input, without latch-shape dispatch. -/
def strengthen (acc : VarId) (latch : Stmt) (target : GuardIR) : Option GuardIR :=
  if closure acc latch target = .top then some (candidate acc latch target) else none

theorem strengthen_inductive (acc : VarId) (latch : Stmt) (target inv : GuardIR)
    (h : strengthen acc latch target = some inv) :
    IsInductiveFor (loopStepTransfer acc latch) (denoteGuard inv) (denoteGuard target) := by
  unfold strengthen at h
  split at h
  · rename_i hc
    have he : candidate acc latch target = inv := Option.some.inj h
    subst inv
    constructor
    · apply (M3.preserved_iff acc latch (candidate acc latch target)).mp
      intro env val hinv
      have hg : evalGuard env (pre acc latch (candidate acc latch target)) = true :=
        synth_sound _ _ env hinv (by change evalGuard env (closure acc latch target) = true; rw [hc]; rfl)
      have hp := M3.havoc_sound acc (M2.wp latch (candidate acc latch target)) env hg val
      change evalGuard (updateEnv env acc val) (M2.wp latch (candidate acc latch target)) = true at hp
      rwa [M2.wp_eval] at hp
    · intro env hinv
      exact (Bool.and_eq_true_iff.mp hinv).1
  · cases h

theorem general_step_complete : StepComplete M3.havoc M2.wp synth strengthen := by
  intro acc latch target
  dsimp only
  intro hc
  change closure acc latch target = .top at hc
  refine ⟨candidate acc latch target, ?_, ?_⟩
  · simp [strengthen, hc]
  · intro env ht hg
    exact Bool.and_eq_true_iff.mpr ⟨ht, hg⟩

theorem stationary_eq (acc d i : VarId) (hda : d ≠ acc) (hdi : d ≠ i) (rhs : PureExpr) :
    strengthen acc (.assign i rhs) (.nonZero (.var d)) =
      some (.conj (.nonZero (.var d)) (.nonZero (.var d))) := by
  simp [strengthen, closure, candidate, pre, M3.havoc,
    M2.wp, M2.substGuard, M2.substPure, guardMentionsVar, pureMentionsVar,
    synth, M3.synthConj, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ, M1R2.shrink,
    M2.smartAnd, hda, hdi]

theorem pipeline_eq (acc d nextD i : VarId)
    (_hda : d ≠ acc) (hna : nextD ≠ acc) (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD)
    (rhs : PureExpr) :
    strengthen acc (.seq (.assign d (.var nextD)) (.assign i rhs)) (.nonZero (.var d)) =
      some (.conj (.nonZero (.var d)) (.nonZero (.var nextD))) := by
  simp [strengthen, closure, candidate, pre, M3.havoc,
    M2.wp, M2.substGuard, M2.substPure, guardMentionsVar, pureMentionsVar,
    synth, M3.synthConj, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ, M1R2.shrink,
    M2.smartAnd, hna, hdi, hni, hdn, Ne.symm hdn]

theorem hoist_stationary_duplicate (x d : VarId) :
    M3.hoist (.assign d (.var x)) (.nonZero (.var x))
      (.conj (.nonZero (.var d)) (.nonZero (.var d))) = .top := by
  simp [M3.hoist, M3.synthConj, M2.wp, M2.substGuard, M2.substPure,
    M2.norm, M2.foldNZ, M2.smartAnd, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ]

theorem general_stationary_safe : StationarySafe strengthen M3.hoist := by
  intro acc d i hda hdi rhs
  refine ⟨.conj (.nonZero (.var d)) (.nonZero (.var d)), stationary_eq acc d i hda hdi rhs, ?_, ?_⟩
  · intro env hd
    simp [evalGuard, evalPure, hd]
  · exact fun x => hoist_stationary_duplicate x d

theorem general_pipeline_safe : PipelineSafe strengthen M3.hoist := by
  intro acc d nextD i hda hna hdi hni hdn rhs
  refine ⟨.conj (.nonZero (.var d)) (.nonZero (.var nextD)),
    pipeline_eq acc d nextD i hda hna hdi hni hdn rhs, ?_, ?_⟩
  · intro env hd hn
    simp [evalGuard, evalPure, hd, hn]
  · exact fun x z => M3.pipeline_hoist_known x z d nextD hdn

theorem general_original : M3.Obligations M3.havoc strengthen M3.hoist M3.opt where
  havocSound := M3.havoc_sound
  havocExact := M3.havoc_exact
  inductiveSound := strengthen_inductive
  stationary := fun acc d i hda hdi => by
    obtain ⟨inv, hs, _⟩ := general_stationary_safe acc d i hda hdi (.sub (.var i) (.lit 1))
    exact ⟨inv, hs⟩
  pipeline := fun acc d nextD i hda hna hdi hni hdn => by
    obtain ⟨inv, hs, _⟩ := general_pipeline_safe acc d nextD i hda hna hdi hni hdn (.sub (.var i) (.lit 1))
    exact ⟨inv, hs⟩
  hoistDenote := M3.hoist_denote
  hoistIterate := M3.hoist_iterate
  guarded := M3.opt_guarded
  sound := M3.opt_sound
  known := M3.known_elim
  unknown := M3.unknown_hoist
  zero := M3.zero_behavior
  pipelineElim := M3.pipeline_elim
  decrement := M3.decrement_trap

theorem general_all_obligations :
    UpdatedObligations M3.havoc strengthen M3.hoist M3.opt M2.wp synth where
  original := general_original
  stationarySafe := general_stationary_safe
  pipelineSafe := general_pipeline_safe
  stepComplete := general_step_complete

theorem general_compatible_with_m1_m2 :
    M1R2.UpdatedObligations synth M1R2.opt ∧
      M2.Obligations M2.wp M2.synthStmt M2.blockOpt ∧
      UpdatedObligations M3.havoc strengthen M3.hoist M3.opt M2.wp synth :=
  ⟨strong_m1, M2.all_obligations, general_all_obligations⟩

theorem satisfiable :
    ∃ (hav : VarId → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR)
      (hf : Stmt → GuardIR → GuardIR → GuardIR) (opt : GuardIR → LoopProg → LoopProg)
      (pb : Stmt → GuardIR → GuardIR) (sg : GuardIR → GuardIR → GuardIR),
      UpdatedObligations hav sf hf opt pb sg :=
  ⟨M3.havoc, strengthen, M3.hoist, M3.opt, M2.wp, synth, general_all_obligations⟩


theorem updated_bottom_rejected
    (hav : VarId → GuardIR → GuardIR) (hf : Stmt → GuardIR → GuardIR → GuardIR)
    (opt : GuardIR → LoopProg → LoopProg) (pb : Stmt → GuardIR → GuardIR)
    (sg : GuardIR → GuardIR → GuardIR) :
    ¬ UpdatedObligations hav M3.vacuousStrengthen hf opt pb sg := by
  intro h
  exact bottom_rejected hf h.stationarySafe

theorem strengthen_skip_sequence (acc : VarId) (latch : Stmt) (target : GuardIR) :
    strengthen acc (.seq .skip latch) target = strengthen acc latch target := rfl

theorem general_accepts_wrapped_family (k : Nat) :
    strengthen 3 (wrappedLatch k) (.nonZero (.var 0)) =
      some (.conj (.nonZero (.var 0)) (.nonZero (.var 0))) := by
  rw [wrappedLatch, strengthen_skip_sequence]
  exact stationary_eq 3 0 2 (by decide) (by decide) (.lit (Int.ofNat k))

/-- The admitted two-form matcher rejects an infinite safe, inhabited family. -/
theorem remaining_shape_countermodel :
    UpdatedObligations M3.havoc M3.constructiveStrengthen M3.hoist M3.opt M2.wp M1R2.synth ∧
      (∀ k, M3.constructiveStrengthen 3 (wrappedLatch k) (.nonZero (.var 0)) = none) ∧
      (∀ k, M3.Preserved 3 (wrappedLatch k) (.nonZero (.var 0))) ∧
      evalGuard (fun _ => 1) (.nonZero (.var 0)) = true :=
  ⟨shape_all_obligations, shape_rejects_wrapped_family, wrapped_family_is_safe, rfl⟩

theorem wrapped_candidate_is_inductive :
    IsInductiveFor (loopStepTransfer 3 (wrappedLatch 7))
      (denoteGuard (.conj (.nonZero (.var 0)) (.nonZero (.var 0))))
      (denoteGuard (.nonZero (.var 0))) := by
  constructor
  · apply (M3.preserved_iff 3 (wrappedLatch 7) _).mp
    intro env val h
    have h' := wrapped_family_is_safe 7 env val (Bool.and_eq_true_iff.mp h).1
    exact Bool.and_eq_true_iff.mpr ⟨h', h'⟩
  · intro env h
    exact (Bool.and_eq_true_iff.mp h).1

theorem weak_and_strong_closure_comparison :
    let t := GuardIR.nonZero (.var 0)
    let c := GuardIR.conj t t
    M1R2.synth c c = .imp c c ∧
    M1R2.synth c c ≠ .top ∧
    synth c c = .top ∧
    closure 3 (wrappedLatch 7) t = .top ∧
    M3.constructiveStrengthen 3 (wrappedLatch 7) t = none ∧
    strengthen 3 (wrappedLatch 7) t = some c ∧
    evalGuard (fun _ => 1) c = true := by
  decide

def arbitraryRhs : PureExpr := .add (.mul (.var 2) (.lit (-3))) (.var 3)
def noncanonicalLatch : Stmt :=
  .seq (.assign 7 (.add (.var 7) (.lit 1)))
    (.seq (.assign 2 arbitraryRhs) .skip)
def compoundTarget : GuardIR :=
  .conj (.nonZero (.add (.var 0) (.lit 1))) (.nonZero (.var 1))

theorem general_nonfixture_witnesses :
    strengthen 3 noncanonicalLatch (.nonZero (.var 0)) =
      some (.conj (.nonZero (.var 0)) (.nonZero (.var 0))) ∧
    M3.constructiveStrengthen 3 noncanonicalLatch (.nonZero (.var 0)) = none ∧
    strengthen 3 (.seq (.assign 0 (.var 1)) (.assign 2 arbitraryRhs)) (.nonZero (.var 0)) =
      some (.conj (.nonZero (.var 0)) (.nonZero (.var 1))) ∧
    strengthen 3 noncanonicalLatch compoundTarget = some (.conj compoundTarget compoundTarget) ∧
    evalGuard (fun _ => 1) (.conj compoundTarget compoundTarget) = true ∧
    strengthen 0 .skip (.nonZero (.var 0)) = none := by
  decide

theorem safe_preheader_discharge_witnesses :
    M3.hoist (.assign 0 (.var 7)) (.nonZero (.var 7))
      (.conj (.nonZero (.var 0)) (.nonZero (.var 0))) = .top ∧
    M3.hoist (.seq (.assign 0 (.var 7)) (.assign 1 (.var 0)))
      (.conj (.nonZero (.var 7)) (.nonZero (.var 0)))
      (.conj (.nonZero (.var 0)) (.nonZero (.var 1))) = .top := by
  decide

end M3R2


/-!
## Milestone 3 Gate 1 Round 3
Spec digest: ea3342a34875761630ac2397b5f3fcad3791d75b355d9dd9014a480920a8ab51.

The new unconditional frame/rotation/pipeline/branch capabilities exclude the
Round 2 strengthening and optimizer matchers independently of helper choices.
The legacy helper-based step-completeness implication is retained verbatim. It
can still have an empty premise with admissible weak helpers, but supplies none
of the new capabilities and no longer admits the earlier countermodel.

The constructive candidate uses structural backward clause transformation,
conservative union at branches, accumulator havoc, and at most four closure
checks. No latch-template dispatch is used. A returned clause set contains the
target and is closed under the abstract loop step. Hoisting preserves exact
guard semantics; body rewriting preserves every fuel-indexed loop outcome.
The cost proof preserves arbitrary latch-guard costs and saves exactly two
division checks per successful iteration on the mandated families.

UpdatedObligations packages all 26 compiler-dependent targets. M3.state_iterate
proves the remaining generic target. All helpers and earlier milestone models
are independently proved; no Specs.Target compiler stub or theorem is invoked.
-/

namespace M3R3
def merge : List GuardIR → List GuardIR → List GuardIR
  | [], ys => ys
  | g :: gs, ys => if g ∈ ys then merge gs ys else g :: merge gs ys

theorem mem_merge (g : GuardIR) (xs ys : List GuardIR) :
    g ∈ merge xs ys ↔ g ∈ xs ∨ g ∈ ys := by
  induction xs with
  | nil => simp [merge]
  | cons a xs ih =>
    by_cases ha : a ∈ ys
    · by_cases hg : g = a
      · subst g; simp [merge, ha, ih]
      · simp [merge, ha, ih, hg]
    · simp [merge, ha, ih, or_assoc]

theorem merge_eq_right (xs ys : List GuardIR) (h : ∀ g ∈ xs, g ∈ ys) :
    merge xs ys = ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [merge, h a (by simp), ih (fun g hg => h g (by simp [hg]))]

theorem merge_self (xs : List GuardIR) : merge xs xs = xs :=
  merge_eq_right xs xs (fun _ h => h)

def Holds (gs : List GuardIR) (env : Env) : Prop := ∀ g ∈ gs, evalGuard env g = true
def guardOf : List GuardIR → GuardIR
  | [] => .top
  | g :: gs => .conj g (guardOf gs)

theorem guardOf_eval (gs : List GuardIR) (env : Env) :
    evalGuard env (guardOf gs) = true ↔ Holds gs env := by
  induction gs with
  | nil => simp [guardOf, Holds, evalGuard]
  | cons g gs ih => simp [guardOf, evalGuard, ih, Holds]

theorem holds_merge (xs ys : List GuardIR) (env : Env) :
    Holds (merge xs ys) env ↔ Holds xs env ∧ Holds ys env := by
  constructor
  · intro h
    exact ⟨fun g hg => h g ((mem_merge g xs ys).mpr (Or.inl hg)),
      fun g hg => h g ((mem_merge g xs ys).mpr (Or.inr hg))⟩
  · rintro ⟨hx, hy⟩ g hg
    rcases (mem_merge g xs ys).mp hg with hm | hm
    · exact hx g hm
    · exact hy g hm

/-- A conservative backward transform that requires both branches' clauses. -/
def pull : Stmt → List GuardIR → List GuardIR
  | .skip, gs => gs
  | .assign v rhs, gs => gs.map (M2.substGuard v rhs)
  | .seq s₁ s₂, gs => pull s₁ (pull s₂ gs)
  | .ite _ t f, gs => merge (pull t gs) (pull f gs)

theorem pull_sound (s : Stmt) (gs : List GuardIR) (env : Env) :
    Holds (pull s gs) env → Holds gs (execStmt s env) := by
  induction s generalizing gs env with
  | skip => exact id
  | assign v rhs =>
    intro h g hg
    have he := h (M2.substGuard v rhs g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    simpa only [M2.substGuard_eval, execStmt] using he
  | seq s₁ s₂ ih₁ ih₂ => intro h; exact ih₂ gs _ (ih₁ (pull s₂ gs) env h)
  | ite c t f iht ihf =>
    intro h
    obtain ⟨ht, hf⟩ := (holds_merge _ _ env).mp h
    cases hc : evalGuard env c with
    | false => simpa [execStmt, hc] using ihf gs env hf
    | true => simpa [execStmt, hc] using iht gs env ht

def stepClauses (acc : VarId) (s : Stmt) (gs : List GuardIR) : List GuardIR :=
  (pull s gs).map (M3.havoc acc)

theorem stepClauses_sound (acc : VarId) (s : Stmt) (gs : List GuardIR)
    (env : Env) (val : Int) (h : Holds (stepClauses acc s gs) env) :
    Holds gs (execStmt s (updateEnv env acc val)) := by
  apply pull_sound
  intro g hg
  exact M3.havoc_sound acc g env (h _ (List.mem_map.mpr ⟨g, hg, rfl⟩)) val

def included (xs ys : List GuardIR) : Bool := xs.all (fun g => decide (g ∈ ys))
theorem included_iff (xs ys : List GuardIR) :
    included xs ys = true ↔ ∀ g ∈ xs, g ∈ ys := by
  simp [included, List.all_eq_true]

def search : Nat → VarId → Stmt → List GuardIR → Option (List GuardIR)
  | 0, _, _, _ => none
  | fuel + 1, acc, s, gs =>
    let next := stepClauses acc s gs
    if included next gs then some gs else search fuel acc s (merge gs next)

theorem search_sound (fuel : Nat) (acc : VarId) (s : Stmt) (xs ys : List GuardIR)
    (h : search fuel acc s xs = some ys) :
    (∀ g ∈ xs, g ∈ ys) ∧ included (stepClauses acc s ys) ys = true := by
  induction fuel generalizing xs with
  | zero => cases h
  | succ fuel ih =>
    simp only [search] at h
    split at h
    · rename_i hc
      have he : xs = ys := Option.some.inj h
      subst ys
      exact ⟨fun _ hg => hg, hc⟩
    · obtain ⟨hi, hc⟩ := ih _ h
      exact ⟨fun g hg => hi g ((mem_merge g xs _).mpr (Or.inl hg)), hc⟩

def strengthen (acc : VarId) (s : Stmt) (target : GuardIR) : Option GuardIR :=
  (search 4 acc s [target]).map guardOf

theorem strengthen_inductive (acc : VarId) (s : Stmt) (target inv : GuardIR)
    (h : strengthen acc s target = some inv) :
    IsInductiveFor (loopStepTransfer acc s) (denoteGuard inv) (denoteGuard target) := by
  unfold strengthen at h
  cases hs : search 4 acc s [target] with
  | none => simp [hs] at h
  | some gs =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst inv
    obtain ⟨hmem, hc⟩ := search_sound 4 acc s [target] gs hs
    constructor
    · apply (M3.preserved_iff acc s (guardOf gs)).mp
      intro env val hinv
      apply (guardOf_eval gs _).mpr
      apply stepClauses_sound acc s gs env val
      intro g hg
      exact (guardOf_eval gs env).mp hinv g ((included_iff _ _).mp hc g hg)
    · intro env hinv
      exact (guardOf_eval gs env).mp hinv target (hmem target (by simp))

theorem havoc_transparent (v : VarId) (g : GuardIR) (h : guardMentionsVar v g = false) :
    M3.havoc v g = g := by simp [M3.havoc, h]

/-- The old conditional remains satisfied; the new unconditional capabilities below carry generality. -/
theorem legacy_step_complete : M3R2.StepComplete M3.havoc M2.wp M1R2.synth strengthen := by
  intro acc s target
  dsimp only
  intro h
  exact False.elim (M3R2.weak_closure_never_top acc s target h)

def hoist (init : Stmt) (ctx : GuardIR) : GuardIR → GuardIR
  | .top => .top
  | .conj a b => M2.smartAnd (hoist init ctx a) (hoist init ctx b)
  | g => M3.hoist init ctx g

theorem hoist_eval (init : Stmt) (ctx g : GuardIR) (env : Env) :
    evalGuard env (hoist init ctx g) = (!evalGuard env ctx || evalGuard (execStmt init env) g) := by
  induction g with
  | top => simp [hoist, evalGuard]
  | conj a b iha ihb =>
    cases hc : evalGuard env ctx <;> simp [hoist, M2.smartAnd_eval, iha, ihb, evalGuard, hc]
  | _ => exact M3.hoist_eval init ctx _ env

theorem hoist_denote (init : Stmt) (ctx inv : GuardIR) :
    denoteGuard (hoist init ctx inv) =
      hoistLoopGuard (stateTransfer (execStmt init)) (denoteGuard ctx) (denoteGuard inv) := by
  calc
    denoteGuard (hoist init ctx inv) = denoteGuard (M3.hoist init ctx inv) := by
      funext env
      exact congrArg (fun b : Bool => b = true)
        ((hoist_eval init ctx inv env).trans (M3.hoist_eval init ctx inv env).symm)
    _ = _ := M3.hoist_denote init ctx inv

theorem hoist_iterate (init : Stmt) (acc : VarId) (latch : Stmt)
    (ctx target inv : GuardIR)
    (h : IsInductiveFor (loopStepTransfer acc latch) (denoteGuard inv) (denoteGuard target)) (n : Nat) :
    (((stateTransfer (execStmt init)).comp ((loopStepTransfer acc latch).iterate n)).post
      (denoteGuard ctx ⊓ denoteGuard (hoist init ctx inv))) ≤ denoteGuard target := by
  rw [hoist_denote]
  exact Round6.hoist_target _ _ _ _ _ h n

theorem hoist_sound (init : Stmt) (ctx inv : GuardIR) (env : Env)
    (hc : evalGuard env ctx = true) (hg : evalGuard env (hoist init ctx inv) = true) :
    evalGuard (execStmt init env) inv = true := by
  rw [hoist_eval, hc] at hg
  exact hg

theorem hoist_list_top (init : Stmt) (ctx : GuardIR) (gs : List GuardIR)
    (h : ∀ g ∈ gs, hoist init ctx g = .top) :
    hoist init ctx (guardOf gs) = .top := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [guardOf, hoist, h g (by simp), ih (fun g hg => h g (by simp [hg])), M2.smartAnd]


def nz (v : VarId) : GuardIR := .nonZero (.var v)
def vars (vs : List VarId) : List GuardIR := vs.map nz
def Frame (s : Stmt) (vs : List VarId) : Prop := ∀ v ∈ vs, stmtWritesVar v s = false

theorem frame_one (s : Stmt) (d : VarId) (h : stmtWritesVar d s = false) : Frame s [d] := by
  intro v hv
  have he : v = d := by simpa using hv
  subst v
  exact h

theorem frame_two (s : Stmt) (d e : VarId)
    (hd : stmtWritesVar d s = false) (he : stmtWritesVar e s = false) : Frame s [d, e] := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> assumption

theorem frame_three (s : Stmt) (d e f : VarId)
    (hd : stmtWritesVar d s = false) (he : stmtWritesVar e s = false)
    (hf : stmtWritesVar f s = false) : Frame s [d, e, f] := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem exec_frame (v : VarId) (s : Stmt) (env : Env) (h : stmtWritesVar v s = false) :
    execStmt s env v = env v := by
  induction s generalizing env with
  | skip => rfl
  | assign w rhs =>
    have hw : w ≠ v := by simpa [stmtWritesVar] using h
    simp [execStmt, updateEnv, Ne.symm hw]
  | seq s₁ s₂ ih₁ ih₂ =>
    have hs := Bool.or_eq_false_iff.mp h
    simp only [execStmt, ih₂ _ hs.2, ih₁ env hs.1]
  | ite c t f iht ihf =>
    have hs := Bool.or_eq_false_iff.mp h
    cases hc : evalGuard env c <;> simp [execStmt, hc, iht env hs.1, ihf env hs.2]

theorem subst_vars (v : VarId) (rhs : PureExpr) (vs : List VarId)
    (h : ∀ w ∈ vs, w ≠ v) :
    (vars vs).map (M2.substGuard v rhs) = vars vs := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
    have hw := h w (by simp)
    change M2.substGuard v rhs (nz w) :: (vars ws).map (M2.substGuard v rhs) = nz w :: vars ws
    rw [show M2.substGuard v rhs (nz w) = nz w by simp [nz, M2.substGuard, M2.substPure, hw],
      ih (fun u hu => h u (by simp [hu]))]

theorem pull_frame (s : Stmt) (vs : List VarId) (h : Frame s vs) :
    pull s (vars vs) = vars vs := by
  induction s generalizing vs with
  | skip => rfl
  | assign v rhs =>
    apply subst_vars
    intro w hw
    have hv : v ≠ w := by simpa [stmtWritesVar] using h w hw
    exact Ne.symm hv
  | seq s₁ s₂ ih₁ ih₂ =>
    have h₁ : Frame s₁ vs := fun v hv => (Bool.or_eq_false_iff.mp (h v hv)).1
    have h₂ : Frame s₂ vs := fun v hv => (Bool.or_eq_false_iff.mp (h v hv)).2
    rw [pull, ih₂ vs h₂, ih₁ vs h₁]
  | ite c t f iht ihf =>
    have ht : Frame t vs := fun v hv => (Bool.or_eq_false_iff.mp (h v hv)).1
    have hf : Frame f vs := fun v hv => (Bool.or_eq_false_iff.mp (h v hv)).2
    rw [pull, iht vs ht, ihf vs hf, merge_self]

theorem havoc_vars (acc : VarId) (vs : List VarId) (h : ∀ v ∈ vs, v ≠ acc) :
    (vars vs).map (M3.havoc acc) = vars vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change M3.havoc acc (nz v) :: (vars vs).map (M3.havoc acc) = nz v :: vars vs
    rw [show M3.havoc acc (nz v) = nz v by
      simp [nz, M3.havoc, guardMentionsVar, pureMentionsVar, h v (by simp)],
      ih (fun u hu => h u (by simp [hu]))]

theorem vars_coverage (vs : List VarId) (env : Env) (h : ∀ v ∈ vs, env v ≠ 0) :
    evalGuard env (guardOf (vars vs)) = true := by
  apply (guardOf_eval _ _).mpr
  intro g hg
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
  exact decide_eq_true (h v hv)

theorem hasNZ_guardOf (gs : List GuardIR) (p : PureExpr) (h : GuardIR.nonZero p ∈ gs) :
    M1R2.hasNZ (guardOf gs) p = true := by
  induction gs with
  | nil => cases h
  | cons g gs ih =>
    rcases List.mem_cons.mp h with he | he
    · subst g
      simp [guardOf]
    · simp [guardOf, M1R2.hasNZ, ih he]

theorem step_frame (acc d : VarId) (s : Stmt) (hda : d ≠ acc)
    (h : stmtWritesVar d s = false) :
    stepClauses acc s (vars [d]) = vars [d] := by
  rw [stepClauses, pull_frame s [d] (frame_one s d h)]
  exact havoc_vars acc [d] (by simpa using hda)

theorem strengthen_frame_eq (acc d : VarId) (s : Stmt) (hda : d ≠ acc)
    (h : stmtWritesVar d s = false) :
    strengthen acc s (nz d) = some (guardOf (vars [d])) := by
  have hs : stepClauses acc s [nz d] = [nz d] := step_frame acc d s hda h
  change (search 4 acc s [nz d]).map guardOf = some (guardOf [nz d])
  simp [search, hs, included]

theorem hoist_assign_atom (x d : VarId) :
    hoist (.assign d (.var x)) (nz x) (nz d) = .top :=
  M3R2.hoist_assign x d

def FrameSafe (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (hf : Stmt → GuardIR → GuardIR → GuardIR) : Prop :=
  ∀ acc d latch, d ≠ acc → stmtWritesVar d latch = false → stmtWritesVar acc latch = false →
    ∃ inv, sf acc latch (nz d) = some inv ∧
      (∀ env, env d ≠ 0 → evalGuard env inv = true) ∧
      (∀ x, hf (.assign d (.var x)) (nz x) inv = .top)

theorem frame_safe : FrameSafe strengthen hoist := by
  intro acc d s hda hd _ha
  refine ⟨guardOf (vars [d]), strengthen_frame_eq acc d s hda hd, ?_, ?_⟩
  · intro env hn
    apply vars_coverage
    simpa using hn
  · intro x
    apply hoist_list_top
    intro g hg
    have he : g = nz d := by simpa [vars] using hg
    subst g
    exact hoist_assign_atom x d

/-- The Round 2 countermodel is rejected regardless of all other helper choices. -/
theorem round2_matcher_rejected (hf : Stmt → GuardIR → GuardIR → GuardIR) :
    ¬ FrameSafe M3.constructiveStrengthen hf := by
  intro h
  obtain ⟨inv, hs, _⟩ := h 3 0 (M3R2.wrappedLatch 7) (by decide) (by decide) (by decide)
  have hn := M3R2.shape_rejects_wrapped_family 7
  change M3.constructiveStrengthen 3 (M3R2.wrappedLatch 7) (.nonZero (.var 0)) = some inv at hs
  rw [hn] at hs
  cases hs


theorem step_of_pull_vars (acc : VarId) (s : Stmt) (xs ys : List VarId)
    (hp : pull s (vars xs) = vars ys) (ha : ∀ v ∈ ys, v ≠ acc) :
    stepClauses acc s (vars xs) = vars ys := by
  rw [stepClauses, hp, havoc_vars acc ys ha]

def swapCore (d e tmp : VarId) : Stmt :=
  .seq (.assign tmp (.var d)) (.seq (.assign d (.var e)) (.assign e (.var tmp)))
def swapLatch (d e tmp : VarId) (pre post : Stmt) : Stmt :=
  .seq pre (.seq (.assign tmp (.var d)) (.seq (.assign d (.var e)) (.seq (.assign e (.var tmp)) post)))
def pipeCore (d e f : VarId) : Stmt := .seq (.assign d (.var e)) (.assign e (.var f))
def pipeLatch (d e f : VarId) (pre post : Stmt) : Stmt :=
  .seq pre (.seq (.assign d (.var e)) (.seq (.assign e (.var f)) post))
def branchCore (d e f : VarId) (c : GuardIR) : Stmt := .ite c (.assign d (.var e)) (.assign d (.var f))
def branchLatch (d e f : VarId) (c : GuardIR) (pre post : Stmt) : Stmt :=
  .seq pre (.seq (branchCore d e f c) post)

theorem step_copy_one (acc d e i : VarId) (rhs : PureExpr)
    (hea : e ≠ acc) (hdi : d ≠ i) :
    stepClauses acc (.seq (.assign d (.var e)) (.assign i rhs)) (vars [d]) = vars [e] := by
  apply step_of_pull_vars
  · simp [pull, vars, nz, M2.substGuard, M2.substPure, hdi]
  · simpa using hea

theorem step_copy_two (acc d e i : VarId) (rhs : PureExpr)
    (hea : e ≠ acc) (hdi : d ≠ i) (hei : e ≠ i) (hde : d ≠ e) :
    stepClauses acc (.seq (.assign d (.var e)) (.assign i rhs)) (vars [d, e]) = vars [e, e] := by
  apply step_of_pull_vars
  · simp [pull, vars, nz, M2.substGuard, M2.substPure, hdi, hei, Ne.symm hde]
  · simpa using hea

theorem step_swap_one (acc d e tmp : VarId) (pre post : Stmt)
    (hea : e ≠ acc) (hde : d ≠ e) (het : e ≠ tmp)
    (hp : Frame pre [d, e]) (hq : Frame post [d, e]) :
    stepClauses acc (swapLatch d e tmp pre post) (vars [d]) = vars [e] := by
  apply step_of_pull_vars
  · change pull pre (pull (swapCore d e tmp) (pull post (vars [d]))) = vars [e]
    rw [pull_frame post [d] (frame_one post d (hq d (by simp)))]
    have hcore : pull (swapCore d e tmp) (vars [d]) = vars [e] := by
      simp [swapCore, pull, vars, nz, M2.substGuard, M2.substPure, hde, het]
    rw [hcore, pull_frame pre [e] (frame_one pre e (hp e (by simp)))]
  · simpa using hea

theorem step_swap_two (acc d e tmp : VarId) (pre post : Stmt)
    (hda : d ≠ acc) (hea : e ≠ acc) (hde : d ≠ e) (hdt : d ≠ tmp) (het : e ≠ tmp)
    (hp : Frame pre [d, e]) (hq : Frame post [d, e]) :
    stepClauses acc (swapLatch d e tmp pre post) (vars [d, e]) = vars [e, d] := by
  apply step_of_pull_vars
  · change pull pre (pull (swapCore d e tmp) (pull post (vars [d, e]))) = vars [e, d]
    rw [pull_frame post [d, e] hq]
    have hcore : pull (swapCore d e tmp) (vars [d, e]) = vars [e, d] := by
      simp [swapCore, pull, vars, nz, M2.substGuard, M2.substPure,
        hde, het, Ne.symm hdt]
    rw [hcore, pull_frame pre [e, d] (frame_two pre e d (hp e (by simp)) (hp d (by simp)))]
  · simpa using And.intro hea hda

theorem step_pipe_one (acc d e f : VarId) (pre post : Stmt)
    (hea : e ≠ acc) (hde : d ≠ e)
    (hp : Frame pre [d, e, f]) (hq : Frame post [d, e, f]) :
    stepClauses acc (pipeLatch d e f pre post) (vars [d]) = vars [e] := by
  apply step_of_pull_vars
  · change pull pre (pull (pipeCore d e f) (pull post (vars [d]))) = vars [e]
    rw [pull_frame post [d] (frame_one post d (hq d (by simp)))]
    have hcore : pull (pipeCore d e f) (vars [d]) = vars [e] := by
      simp [pipeCore, pull, vars, nz, M2.substGuard, M2.substPure, hde]
    rw [hcore, pull_frame pre [e] (frame_one pre e (hp e (by simp)))]
  · simpa using hea

theorem step_pipe_two (acc d e f : VarId) (pre post : Stmt)
    (hea : e ≠ acc) (hfa : f ≠ acc) (hde : d ≠ e) (hdf : d ≠ f)
    (hp : Frame pre [d, e, f]) (hq : Frame post [d, e, f]) :
    stepClauses acc (pipeLatch d e f pre post) (vars [d, e]) = vars [e, f] := by
  apply step_of_pull_vars
  · change pull pre (pull (pipeCore d e f) (pull post (vars [d, e]))) = vars [e, f]
    rw [pull_frame post [d, e] (frame_two post d e (hq d (by simp)) (hq e (by simp)))]
    have hcore : pull (pipeCore d e f) (vars [d, e]) = vars [e, f] := by
      simp [pipeCore, pull, vars, nz, M2.substGuard, M2.substPure, hde, Ne.symm hdf]
    rw [hcore, pull_frame pre [e, f] (frame_two pre e f (hp e (by simp)) (hp f (by simp)))]
  · simpa using And.intro hea hfa

theorem step_pipe_three (acc d e f : VarId) (pre post : Stmt)
    (hea : e ≠ acc) (hfa : f ≠ acc) (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hp : Frame pre [d, e, f]) (hq : Frame post [d, e, f]) :
    stepClauses acc (pipeLatch d e f pre post) (vars [d, e, f]) = vars [e, f, f] := by
  apply step_of_pull_vars
  · change pull pre (pull (pipeCore d e f) (pull post (vars [d, e, f]))) = vars [e, f, f]
    rw [pull_frame post [d, e, f] hq]
    have hcore : pull (pipeCore d e f) (vars [d, e, f]) = vars [e, f, f] := by
      simp [pipeCore, pull, vars, nz, M2.substGuard, M2.substPure,
        hde, Ne.symm hdf, Ne.symm hef]
    rw [hcore, pull_frame pre [e, f, f]
      (frame_three pre e f f (hp e (by simp)) (hp f (by simp)) (hp f (by simp)))]
  · simpa using And.intro hea hfa

theorem step_branch_one (acc d e f : VarId) (c : GuardIR) (pre post : Stmt)
    (hea : e ≠ acc) (hfa : f ≠ acc) (hef : e ≠ f)
    (hp : Frame pre [d, e, f]) (hq : Frame post [d, e, f]) :
    stepClauses acc (branchLatch d e f c pre post) (vars [d]) = vars [e, f] := by
  apply step_of_pull_vars
  · change pull pre (pull (branchCore d e f c) (pull post (vars [d]))) = vars [e, f]
    rw [pull_frame post [d] (frame_one post d (hq d (by simp)))]
    have hcore : pull (branchCore d e f c) (vars [d]) = vars [e, f] := by
      simp [branchCore, pull, vars, nz, M2.substGuard, M2.substPure, merge, hef]
    rw [hcore, pull_frame pre [e, f] (frame_two pre e f (hp e (by simp)) (hp f (by simp)))]
  · simpa using And.intro hea hfa

theorem step_branch_three (acc d e f : VarId) (c : GuardIR) (pre post : Stmt)
    (hea : e ≠ acc) (hfa : f ≠ acc) (hde : d ≠ e) (hdf : d ≠ f)
    (hp : Frame pre [d, e, f]) (hq : Frame post [d, e, f]) :
    stepClauses acc (branchLatch d e f c pre post) (vars [d, e, f]) = vars [f, e, f] := by
  apply step_of_pull_vars
  · change pull pre (pull (branchCore d e f c) (pull post (vars [d, e, f]))) = vars [f, e, f]
    rw [pull_frame post [d, e, f] hq]
    have hcore : pull (branchCore d e f c) (vars [d, e, f]) = vars [f, e, f] := by
      simp [branchCore, pull, vars, nz, M2.substGuard, M2.substPure,
        merge, Ne.symm hde, Ne.symm hdf]
    rw [hcore, pull_frame pre [f, e, f]
      (frame_three pre f e f (hp f (by simp)) (hp e (by simp)) (hp f (by simp)))]
  · simpa using And.intro hfa (And.intro hea hfa)


theorem search_two (fuel : Nat) (acc : VarId) (s : Stmt) (xs ys : List GuardIR)
    (h₀ : included (stepClauses acc s xs) xs = false)
    (hm : merge xs (stepClauses acc s xs) = ys)
    (h₁ : included (stepClauses acc s ys) ys = true) :
    search (fuel + 2) acc s xs = some ys := by
  rw [search]
  simp only [h₀, Bool.false_eq_true, ↓reduceIte, hm]
  rw [search]
  simp only [h₁, ↓reduceIte]

theorem search_three (fuel : Nat) (acc : VarId) (s : Stmt) (xs ys zs : List GuardIR)
    (h₀ : included (stepClauses acc s xs) xs = false)
    (hm₀ : merge xs (stepClauses acc s xs) = ys)
    (h₁ : included (stepClauses acc s ys) ys = false)
    (hm₁ : merge ys (stepClauses acc s ys) = zs)
    (h₂ : included (stepClauses acc s zs) zs = true) :
    search (fuel + 3) acc s xs = some zs := by
  rw [search]
  simp only [h₀, Bool.false_eq_true, ↓reduceIte, hm₀]
  exact search_two fuel acc s ys zs h₁ hm₁ h₂

theorem strengthen_copy_eq (acc d e i : VarId) (rhs : PureExpr)
    (hea : e ≠ acc) (hdi : d ≠ i) (hei : e ≠ i) (hde : d ≠ e) :
    strengthen acc (.seq (.assign d (.var e)) (.assign i rhs)) (nz d) =
      some (guardOf (vars [d, e])) := by
  let s := Stmt.seq (.assign d (.var e)) (.assign i rhs)
  have h₀ : stepClauses acc s [nz d] = [nz e] := step_copy_one acc d e i rhs hea hdi
  have h₁ : stepClauses acc s [nz d, nz e] = [nz e, nz e] := step_copy_two acc d e i rhs hea hdi hei hde
  have hs := search_two 2 acc s [nz d] [nz d, nz e]
    (by rw [h₀]; simp [included, nz, Ne.symm hde])
    (by rw [h₀]; simp [merge, nz, hde])
    (by rw [h₁]; simp [included])
  change (search 4 acc s [nz d]).map guardOf = some (guardOf [nz d, nz e])
  rw [hs]
  rfl

theorem strengthen_swap_eq (acc d e tmp : VarId) (pre post : Stmt)
    (hda : d ≠ acc) (hea : e ≠ acc) (hde : d ≠ e) (hdt : d ≠ tmp) (het : e ≠ tmp)
    (hp : Frame pre [d, e]) (hq : Frame post [d, e]) :
    strengthen acc (swapLatch d e tmp pre post) (nz d) = some (guardOf (vars [d, e])) := by
  let s := swapLatch d e tmp pre post
  have h₀ : stepClauses acc s [nz d] = [nz e] := step_swap_one acc d e tmp pre post hea hde het hp hq
  have h₁ : stepClauses acc s [nz d, nz e] = [nz e, nz d] :=
    step_swap_two acc d e tmp pre post hda hea hde hdt het hp hq
  have hs := search_two 2 acc s [nz d] [nz d, nz e]
    (by rw [h₀]; simp [included, nz, Ne.symm hde])
    (by rw [h₀]; simp [merge, nz, hde])
    (by rw [h₁]; simp [included])
  change (search 4 acc s [nz d]).map guardOf = some (guardOf [nz d, nz e])
  rw [hs]
  rfl

theorem strengthen_pipe3_eq (acc d e f : VarId) (pre post : Stmt)
    (hea : e ≠ acc) (hfa : f ≠ acc) (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hp : Frame pre [d, e, f]) (hq : Frame post [d, e, f]) :
    strengthen acc (pipeLatch d e f pre post) (nz d) = some (guardOf (vars [d, e, f])) := by
  let s := pipeLatch d e f pre post
  have h₀ : stepClauses acc s [nz d] = [nz e] := step_pipe_one acc d e f pre post hea hde hp hq
  have h₁ : stepClauses acc s [nz d, nz e] = [nz e, nz f] :=
    step_pipe_two acc d e f pre post hea hfa hde hdf hp hq
  have h₂ : stepClauses acc s [nz d, nz e, nz f] = [nz e, nz f, nz f] :=
    step_pipe_three acc d e f pre post hea hfa hde hdf hef hp hq
  have hs := search_three 1 acc s [nz d] [nz d, nz e] [nz d, nz e, nz f]
    (by rw [h₀]; simp [included, nz, Ne.symm hde])
    (by rw [h₀]; simp [merge, nz, hde])
    (by rw [h₁]; simp [included, nz, Ne.symm hdf, Ne.symm hef])
    (by rw [h₁]; simp [merge, nz, hde, hdf])
    (by rw [h₂]; simp [included])
  change (search 4 acc s [nz d]).map guardOf = some (guardOf [nz d, nz e, nz f])
  rw [hs]
  rfl

theorem strengthen_branch_eq (acc d e f : VarId) (c : GuardIR) (pre post : Stmt)
    (hea : e ≠ acc) (hfa : f ≠ acc) (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hp : Frame pre [d, e, f]) (hq : Frame post [d, e, f]) :
    strengthen acc (branchLatch d e f c pre post) (nz d) = some (guardOf (vars [d, e, f])) := by
  let s := branchLatch d e f c pre post
  have h₀ : stepClauses acc s [nz d] = [nz e, nz f] := step_branch_one acc d e f c pre post hea hfa hef hp hq
  have h₁ : stepClauses acc s [nz d, nz e, nz f] = [nz f, nz e, nz f] :=
    step_branch_three acc d e f c pre post hea hfa hde hdf hp hq
  have hs := search_two 2 acc s [nz d] [nz d, nz e, nz f]
    (by rw [h₀]; simp [included, nz, Ne.symm hde])
    (by rw [h₀]; simp [merge, nz, hde, hdf])
    (by rw [h₁]; simp [included])
  change (search 4 acc s [nz d]).map guardOf = some (guardOf [nz d, nz e, nz f])
  rw [hs]
  rfl

theorem hoist_vars_top (init : Stmt) (ctx : GuardIR) (vs : List VarId)
    (h : ∀ v ∈ vs, hoist init ctx (nz v) = .top) :
    hoist init ctx (guardOf (vars vs)) = .top := by
  apply hoist_list_top
  intro g hg
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
  exact h v hv

theorem hoist_init2 (x z d e : VarId) (hde : d ≠ e) :
    hoist (.seq (.assign d (.var x)) (.assign e (.var z))) (.conj (nz x) (nz z))
      (guardOf (vars [d, e])) = .top := by
  apply hoist_vars_top
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · simp [hoist, nz, M3.hoist, M3.synthConj, M2.wp, M2.substGuard, M2.substPure,
      M2.norm, M2.foldNZ, M2.smartAnd, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ, hde]
  · by_cases hz : z = d <;>
      simp [hoist, nz, M3.hoist, M3.synthConj, M2.wp, M2.substGuard, M2.substPure,
        M2.norm, M2.foldNZ, M2.smartAnd, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ, hz]

theorem hoist_init3 (x w z d e f : VarId) (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    hoist (.seq (.assign d (.var x)) (.seq (.assign e (.var w)) (.assign f (.var z))))
      (.conj (nz x) (.conj (nz w) (nz z))) (guardOf (vars [d, e, f])) = .top := by
  apply hoist_vars_top
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · simp [hoist, nz, M3.hoist, M3.synthConj, M2.wp, M2.substGuard, M2.substPure,
      M2.norm, M2.foldNZ, M2.smartAnd, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ, hde, hdf]
  · by_cases hw : w = d <;>
      simp [hoist, nz, M3.hoist, M3.synthConj, M2.wp, M2.substGuard, M2.substPure,
        M2.norm, M2.foldNZ, M2.smartAnd, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ, hef, hw]
  · by_cases hze : z = e <;> by_cases hw : w = d <;> by_cases hzd : z = d <;>
      simp [hoist, nz, M3.hoist, M3.synthConj, M2.wp, M2.substGuard, M2.substPure,
        M2.norm, M2.foldNZ, M2.smartAnd, M1R2.synth, M1R2.synthNZ, M1R2.hasNZ, hze, hw, hzd, hde]


theorem strengthen_hasNZ (acc : VarId) (s : Stmt) (p : PureExpr) (inv : GuardIR)
    (h : strengthen acc s (.nonZero p) = some inv) :
    M1R2.hasNZ inv p = true := by
  unfold strengthen at h
  cases hs : search 4 acc s [.nonZero p] with
  | none => simp [hs] at h
  | some gs =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst inv
    exact hasNZ_guardOf gs p ((search_sound 4 acc s [.nonZero p] gs hs).1 _ (by simp))

def optWhile (ctx : GuardIR) (w : WhileLoop) : LoopProg :=
  match M3.firstDivisor w.body with
  | none => .whileLoop w
  | some d =>
    match strengthen w.accVar w.latch (.nonZero d) with
    | none => .whileLoop w
    | some inv =>
      let g := hoist w.init ctx inv
      if g = .top then .whileLoop (M3.fastWhile w inv)
      else .iteLoop g (.whileLoop (M3.fastWhile w inv)) (.whileLoop w)

def opt (ctx : GuardIR) : LoopProg → LoopProg
  | .whileLoop w => optWhile ctx w
  | p => p

theorem optWhile_sound (fuel : Nat) (ctx : GuardIR) (w : WhileLoop) (env : Env)
    (hc : evalGuard env ctx = true) :
    evalLoop fuel env (optWhile ctx w) = evalLoop fuel env (.whileLoop w) := by
  unfold optWhile
  cases hd : M3.firstDivisor w.body with
  | none => rfl
  | some d =>
    dsimp only
    cases hs : strengthen w.accVar w.latch (.nonZero d) with
    | none => rfl
    | some inv =>
      have hp := (M3.preserved_iff w.accVar w.latch inv).mpr
        (strengthen_inductive w.accVar w.latch (.nonZero d) inv hs).1
      dsimp only
      by_cases ht : hoist w.init ctx inv = .top
      · rw [ite_eq_left ht]
        exact M3.run_fast w inv hp fuel _ (hoist_sound w.init ctx inv env hc (by rw [ht]; rfl))
      · rw [ite_eq_right ht]
        cases hg : evalGuard env (hoist w.init ctx inv) with
        | false => simp [evalLoop, hg]
        | true =>
          simp only [evalLoop, hg, ↓reduceIte]
          exact M3.run_fast w inv hp fuel _ (hoist_sound w.init ctx inv env hc hg)

theorem opt_sound (fuel : Nat) (ctx : GuardIR) (p : LoopProg) (env : Env)
    (hc : evalGuard env ctx = true) : evalLoop fuel env (opt ctx p) = evalLoop fuel env p := by
  cases p with
  | whileLoop w => exact optWhile_sound fuel ctx w env hc
  | iteLoop _ _ _ => rfl

theorem opt_guarded (fuel : Nat) (ctx : GuardIR) (p : LoopProg) :
    GuardedEquiv (liftEval (evalLoop fuel)) (denoteGuard ctx) (opt ctx p) p :=
  (M1.lift_bridge (evalLoop fuel) _ _ _).mpr (opt_sound fuel ctx p)

theorem opt_rewrite (ctx : GuardIR) (w : WhileLoop) (acc d : VarId) (num y : PureExpr) (inv : GuardIR)
    (hb : w.body = M3.sourceBody acc num y d)
    (hs : strengthen w.accVar w.latch (nz d) = some inv) :
    opt ctx (.whileLoop w) =
      if hoist w.init ctx inv = .top then .whileLoop (M3.fastWhile w inv)
      else .iteLoop (hoist w.init ctx inv) (.whileLoop (M3.fastWhile w inv)) (.whileLoop w) := by
  simp [opt, optWhile, hb, M3.sourceBody, mkDualDivExpr, M3.firstDivisor, hs, nz] at *

theorem opt_known (ctx : GuardIR) (w : WhileLoop) (acc d : VarId) (num y : PureExpr) (inv : GuardIR)
    (hb : w.body = M3.sourceBody acc num y d)
    (hs : strengthen w.accVar w.latch (nz d) = some inv)
    (hg : hoist w.init ctx inv = .top) :
    opt ctx (.whileLoop w) = .whileLoop (M3.fastWhile w inv) := by
  rw [opt_rewrite ctx w acc d num y inv hb hs]
  simp only [hg, ↓reduceIte]

/-- Exact savings with arbitrary latch guard costs: successful body values and later states agree. -/
theorem run_saving (w : WhileLoop) (inv : GuardIR) (i acc d : VarId) (num y : PureExpr)
    (hcond : w.cond = nz i) (hbody : w.body = M3.sourceBody acc num y d)
    (hnz : M1R2.hasNZ inv (.var d) = true)
    (hcounter : ∀ env val, execStmt w.latch (updateEnv env w.accVar val) i = env i - 1)
    (hp : M3.Preserved w.accVar w.latch inv)
    (n : Nat) (env : Env) (hi : env i = Int.ofNat n) (hinv : evalGuard env inv = true) :
    runWhileCheckCost (n + 1) env (M3.fastWhile w inv) + 2 * n = runWhileCheckCost (n + 1) env w := by
  induction n generalizing env with
  | zero =>
    have hc : evalGuard env w.cond = false := by simp [hcond, nz, evalGuard, evalPure, hi]
    simp [runWhileCheckCost, M3.fastWhile, hc]
  | succ n ih =>
    have hiNZ : env i ≠ 0 := by rw [hi]; simp; omega
    have hc : evalGuard env w.cond = true := by simp [hcond, nz, evalGuard, evalPure, hiNZ]
    have hd : env d ≠ 0 := M1R2.hasNZ_sound inv (.var d) env hnz hinv
    have hv : ∃ val, evalExpr env w.body = .val val := by
      rw [hbody]
      exact M3.source_body_value acc num y d env hd
    obtain ⟨val, hv⟩ := hv
    have he := M1R2.core_sound inv w.body env hinv
    have hs : execCheckCost env w.body = 2 := by rw [hbody]; exact M3.source_body_cost acc num y d env hd
    have hf : execCheckCost env (M1R2.core inv w.body) = 0 := by
      rw [hbody, M3.core_body inv acc num y d hnz]
      exact (M3.fast_body_metrics acc num y d env).2.2
    have hi' : execStmt w.latch (updateEnv env w.accVar val) i = Int.ofNat n := by
      rw [hcounter, hi]
      simp
    have hn := ih _ hi' (hp env val hinv)
    have hsource : runWhileCheckCost (n + 2) env w =
        guardEvalCost env w.cond + (2 + (stmtGuardCost (updateEnv env w.accVar val) w.latch +
          runWhileCheckCost (n + 1) (execStmt w.latch (updateEnv env w.accVar val)) w)) := by
      rw [runWhileCheckCost, hc]
      simp only [↓reduceIte, hs, hv]
    have hfast : runWhileCheckCost (n + 2) env (M3.fastWhile w inv) =
        guardEvalCost env w.cond + (0 + (stmtGuardCost (updateEnv env w.accVar val) w.latch +
          runWhileCheckCost (n + 1) (execStmt w.latch (updateEnv env w.accVar val)) (M3.fastWhile w inv))) := by
      rw [runWhileCheckCost]
      simp only [M3.fastWhile, hc, ↓reduceIte, hf, he, hv]
    rw [hsource, hfast]
    omega

theorem opt_capability (ctx : GuardIR) (w : WhileLoop) (inv : GuardIR)
    (i acc d : VarId) (num y : PureExpr)
    (hcond : w.cond = nz i) (hbody : w.body = M3.sourceBody acc num y d)
    (hret : w.ret = .pure (.var acc))
    (hs : strengthen w.accVar w.latch (nz d) = some inv)
    (hg : hoist w.init ctx inv = .top)
    (hcounter : ∀ env val, execStmt w.latch (updateEnv env w.accVar val) i = env i - 1)
    (n : Nat) (env : Env) (hi : execStmt w.init env i = Int.ofNat n) (hctx : evalGuard env ctx = true) :
    loopCheckedDivCount (opt ctx (.whileLoop w)) = 0 ∧
      loopDivOpCount (opt ctx (.whileLoop w)) ≤ 1 ∧
      loopBranchCount (opt ctx (.whileLoop w)) = 0 ∧
      execLoopCheckCost (n + 1) env (opt ctx (.whileLoop w)) + 2 * n ≤
        execLoopCheckCost (n + 1) env (.whileLoop w) := by
  have hnz := strengthen_hasNZ w.accVar w.latch (.var d) inv hs
  have hp := (M3.preserved_iff w.accVar w.latch inv).mpr
    (strengthen_inductive w.accVar w.latch (nz d) inv hs).1
  have he := hoist_sound w.init ctx inv env hctx (by rw [hg]; rfl)
  have hm := M3.fast_loop_metrics w inv acc d num y hbody hret hnz
  have hc := run_saving w inv i acc d num y hcond hbody hnz hcounter hp n (execStmt w.init env) hi he
  rw [opt_known ctx w acc d num y inv hbody hs hg]
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  change (stmtGuardCost env w.init + runWhileCheckCost (n + 1) (execStmt w.init env) (M3.fastWhile w inv)) + 2 * n ≤
    stmtGuardCost env w.init + runWhileCheckCost (n + 1) (execStmt w.init env) w
  omega

theorem counter_framed (pre post : Stmt) (i acc : VarId) (hia : i ≠ acc)
    (hpre : stmtWritesVar i pre = false) (hpost : stmtWritesVar i post = false)
    (env : Env) (val : Int) :
    execStmt (.seq pre (.seq (.assign i (.sub (.var i) (.lit 1))) post)) (updateEnv env acc val) i = env i - 1 := by
  change execStmt post
    (updateEnv (execStmt pre (updateEnv env acc val)) i
      (evalPure (execStmt pre (updateEnv env acc val)) (.sub (.var i) (.lit 1)))) i = _
  rw [exec_frame i post _ hpost]
  simp only [updateEnv, decide_true, ↓reduceIte, evalPure]
  rw [exec_frame i pre _ hpre]
  simp [updateEnv, hia]


def SwapSafe (sf : VarId → Stmt → GuardIR → Option GuardIR) (hf : Stmt → GuardIR → GuardIR → GuardIR) : Prop :=
  ∀ (accVar d altD tmp : VarId)
    (preLatch postLatch : Stmt)
    (_hda : d ≠ accVar) (_hala : altD ≠ accVar) (_hta : tmp ≠ accVar)
    (_hdal : d ≠ altD) (_hdt : d ≠ tmp) (_halt : altD ≠ tmp)
    (_hPreD : stmtWritesVar d preLatch = false)
    (_hPreAlt : stmtWritesVar altD preLatch = false)
    (_hPreAcc : stmtWritesVar accVar preLatch = false)
    (_hPostD : stmtWritesVar d postLatch = false)
    (_hPostAlt : stmtWritesVar altD postLatch = false)
    (_hPostTmp : stmtWritesVar tmp postLatch = false)
    (_hPostAcc : stmtWritesVar accVar postLatch = false),
    ∃ inv,
      sf accVar
        (.seq preLatch
          (.seq (.assign tmp (.var d))
            (.seq (.assign d (.var altD))
              (.seq (.assign altD (.var tmp)) postLatch))))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → env altD ≠ 0 → evalGuard env inv = true) ∧
      (∀ x z : VarId,
        hf
          (.seq (.assign d (.var x)) (.assign altD (.var z)))
          (.conj (.nonZero (.var x)) (.nonZero (.var z)))
          inv = .top)


def Pipe3Safe (sf : VarId → Stmt → GuardIR → Option GuardIR) (hf : Stmt → GuardIR → GuardIR → GuardIR) : Prop :=
  ∀ (accVar d d₁ d₂ : VarId)
    (preLatch postLatch : Stmt)
    (_hda : d ≠ accVar) (_hd₁a : d₁ ≠ accVar) (_hd₂a : d₂ ≠ accVar)
    (_hdd₁ : d ≠ d₁) (_hdd₂ : d ≠ d₂) (_hd₁d₂ : d₁ ≠ d₂)
    (_hPreD : stmtWritesVar d preLatch = false)
    (_hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (_hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (_hPreAcc : stmtWritesVar accVar preLatch = false)
    (_hPostD : stmtWritesVar d postLatch = false)
    (_hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (_hPostD₂ : stmtWritesVar d₂ postLatch = false)
    (_hPostAcc : stmtWritesVar accVar postLatch = false),
    ∃ inv,
      sf accVar
        (.seq preLatch
          (.seq (.assign d (.var d₁))
            (.seq (.assign d₁ (.var d₂)) postLatch)))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → env d₁ ≠ 0 → env d₂ ≠ 0 → evalGuard env inv = true) ∧
      (∀ x w z : VarId,
        hf
          (.seq (.assign d (.var x)) (.seq (.assign d₁ (.var w)) (.assign d₂ (.var z))))
          (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
          inv = .top)


def BranchSafe (sf : VarId → Stmt → GuardIR → Option GuardIR) (hf : Stmt → GuardIR → GuardIR → GuardIR) : Prop :=
  ∀ (accVar d d₁ d₂ : VarId)
    (branchCond : GuardIR) (preLatch postLatch : Stmt)
    (_hda : d ≠ accVar) (_hd₁a : d₁ ≠ accVar) (_hd₂a : d₂ ≠ accVar)
    (_hdd₁ : d ≠ d₁) (_hdd₂ : d ≠ d₂) (_hd₁d₂ : d₁ ≠ d₂)
    (_hPreD : stmtWritesVar d preLatch = false)
    (_hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (_hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (_hPreAcc : stmtWritesVar accVar preLatch = false)
    (_hPostD : stmtWritesVar d postLatch = false)
    (_hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (_hPostD₂ : stmtWritesVar d₂ postLatch = false)
    (_hPostAcc : stmtWritesVar accVar postLatch = false),
    ∃ inv,
      sf accVar
        (.seq preLatch
          (.seq (.ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) postLatch))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → env d₁ ≠ 0 → env d₂ ≠ 0 → evalGuard env inv = true) ∧
      (∀ x w z : VarId,
        hf
          (.seq (.assign d (.var x)) (.seq (.assign d₁ (.var w)) (.assign d₂ (.var z))))
          (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
          inv = .top)


def FrameOpt (ofn : GuardIR → LoopProg → LoopProg) : Prop :=
  ∀ (x d i acc : VarId)
    (_hid : i ≠ d) (_hia : i ≠ acc) (_hda : d ≠ acc)
    (num y : PureExpr) (preLatch postLatch : Stmt)
    (_hPreD : stmtWritesVar d preLatch = false)
    (_hPreI : stmtWritesVar i preLatch = false)
    (_hPreAcc : stmtWritesVar acc preLatch = false)
    (_hPostD : stmtWritesVar d postLatch = false)
    (_hPostI : stmtWritesVar i postLatch = false)
    (_hPostAcc : stmtWritesVar acc postLatch = false)
    (n : Nat) (env : Env)
    (_hi : env i = Int.ofNat n)
    (_hx : evalGuard env (.nonZero (.var x)) = true),
    let src := LoopProg.whileLoop (mkFrameStmtDivLoop x d i acc num y preLatch postLatch)
    let opt := ofn (.nonZero (.var x)) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt + 2 * n ≤ execLoopCheckCost (n + 1) env src


def SwapOpt (ofn : GuardIR → LoopProg → LoopProg) : Prop :=
  ∀ (x z d altD tmp i acc : VarId)
    (_hda : d ≠ acc) (_hala : altD ≠ acc) (_hta : tmp ≠ acc)
    (_hid : i ≠ d) (_hial : i ≠ altD) (_hit : i ≠ tmp) (_hia : i ≠ acc)
    (_hdal : d ≠ altD) (_hdt : d ≠ tmp) (_halt : altD ≠ tmp)
    (num y : PureExpr) (preLatch postLatch : Stmt)
    (_hPreD : stmtWritesVar d preLatch = false)
    (_hPreAlt : stmtWritesVar altD preLatch = false)
    (_hPreI : stmtWritesVar i preLatch = false)
    (_hPreAcc : stmtWritesVar acc preLatch = false)
    (_hPostD : stmtWritesVar d postLatch = false)
    (_hPostAlt : stmtWritesVar altD postLatch = false)
    (_hPostTmp : stmtWritesVar tmp postLatch = false)
    (_hPostI : stmtWritesVar i postLatch = false)
    (_hPostAcc : stmtWritesVar acc postLatch = false)
    (n : Nat) (env : Env)
    (_hi : env i = Int.ofNat n)
    (_hctx : evalGuard env (.conj (.nonZero (.var x)) (.nonZero (.var z))) = true),
    let src := LoopProg.whileLoop (mkSwapDivLoop x z d altD tmp i acc num y preLatch postLatch)
    let opt := ofn (.conj (.nonZero (.var x)) (.nonZero (.var z))) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt + 2 * n ≤ execLoopCheckCost (n + 1) env src


def Pipe3Opt (ofn : GuardIR → LoopProg → LoopProg) : Prop :=
  ∀ (x w z d d₁ d₂ i acc : VarId)
    (_hda : d ≠ acc) (_hd₁a : d₁ ≠ acc) (_hd₂a : d₂ ≠ acc)
    (_hid : i ≠ d) (_hid₁ : i ≠ d₁) (_hid₂ : i ≠ d₂) (_hia : i ≠ acc)
    (_hdd₁ : d ≠ d₁) (_hdd₂ : d ≠ d₂) (_hd₁d₂ : d₁ ≠ d₂)
    (num y : PureExpr) (preLatch postLatch : Stmt)
    (_hPreD : stmtWritesVar d preLatch = false)
    (_hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (_hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (_hPreI : stmtWritesVar i preLatch = false)
    (_hPreAcc : stmtWritesVar acc preLatch = false)
    (_hPostD : stmtWritesVar d postLatch = false)
    (_hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (_hPostD₂ : stmtWritesVar d₂ postLatch = false)
    (_hPostI : stmtWritesVar i postLatch = false)
    (_hPostAcc : stmtWritesVar acc postLatch = false)
    (n : Nat) (env : Env)
    (_hi : env i = Int.ofNat n)
    (_hctx : evalGuard env (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) = true),
    let src := LoopProg.whileLoop (mkPipeline3DivLoop x w z d d₁ d₂ i acc num y preLatch postLatch)
    let opt := ofn (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt + 2 * n ≤ execLoopCheckCost (n + 1) env src


def BranchOpt (ofn : GuardIR → LoopProg → LoopProg) : Prop :=
  ∀ (x w z d d₁ d₂ i acc : VarId)
    (_hda : d ≠ acc) (_hd₁a : d₁ ≠ acc) (_hd₂a : d₂ ≠ acc)
    (_hid : i ≠ d) (_hid₁ : i ≠ d₁) (_hid₂ : i ≠ d₂) (_hia : i ≠ acc)
    (_hdd₁ : d ≠ d₁) (_hdd₂ : d ≠ d₂) (_hd₁d₂ : d₁ ≠ d₂)
    (branchCond : GuardIR) (num y : PureExpr) (preLatch postLatch : Stmt)
    (_hPreD : stmtWritesVar d preLatch = false)
    (_hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (_hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (_hPreI : stmtWritesVar i preLatch = false)
    (_hPreAcc : stmtWritesVar acc preLatch = false)
    (_hPostD : stmtWritesVar d postLatch = false)
    (_hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (_hPostD₂ : stmtWritesVar d₂ postLatch = false)
    (_hPostI : stmtWritesVar i postLatch = false)
    (_hPostAcc : stmtWritesVar acc postLatch = false)
    (n : Nat) (env : Env)
    (_hi : env i = Int.ofNat n)
    (_hctx : evalGuard env (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) = true),
    let src := LoopProg.whileLoop (mkBranchDivLoop x w z d d₁ d₂ i acc branchCond num y preLatch postLatch)
    let opt := ofn (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt + 2 * n ≤ execLoopCheckCost (n + 1) env src

theorem stationary_safe : M3R2.StationarySafe strengthen hoist := by
  intro acc d i hda hdi rhs
  refine ⟨guardOf (vars [d]), strengthen_frame_eq acc d (.assign i rhs) hda
    (by simp [stmtWritesVar, Ne.symm hdi]), ?_, ?_⟩
  · intro env hd
    apply vars_coverage
    simpa using hd
  · intro x
    apply hoist_vars_top
    intro v hv
    have he : v = d := by simpa using hv
    subst v
    exact hoist_assign_atom x d

theorem pipeline_safe : M3R2.PipelineSafe strengthen hoist := by
  intro acc d e i _hda hea hdi hei hde rhs
  refine ⟨guardOf (vars [d, e]), strengthen_copy_eq acc d e i rhs hea hdi hei hde, ?_, ?_⟩
  · intro env hd he
    apply vars_coverage
    simpa using And.intro hd he
  · exact fun x z => hoist_init2 x z d e hde

theorem swap_safe : SwapSafe strengthen hoist := by
  intro acc d e tmp pre post hda hea _hta hde hdt het hpD hpE _hpA hqD hqE _hqT _hqA
  refine ⟨guardOf (vars [d, e]), strengthen_swap_eq acc d e tmp pre post hda hea hde hdt het
    (frame_two pre d e hpD hpE) (frame_two post d e hqD hqE), ?_, ?_⟩
  · intro env hd he
    apply vars_coverage
    simpa using And.intro hd he
  · exact fun x z => hoist_init2 x z d e hde

theorem pipe3_safe : Pipe3Safe strengthen hoist := by
  intro acc d e f pre post _hda hea hfa hde hdf hef hpD hpE hpF _hpA hqD hqE hqF _hqA
  refine ⟨guardOf (vars [d, e, f]), strengthen_pipe3_eq acc d e f pre post hea hfa hde hdf hef
    (frame_three pre d e f hpD hpE hpF) (frame_three post d e f hqD hqE hqF), ?_, ?_⟩
  · intro env hd he hf
    apply vars_coverage
    simpa using And.intro hd (And.intro he hf)
  · exact fun x w z => hoist_init3 x w z d e f hde hdf hef

theorem branch_safe : BranchSafe strengthen hoist := by
  intro acc d e f c pre post _hda hea hfa hde hdf hef hpD hpE hpF _hpA hqD hqE hqF _hqA
  refine ⟨guardOf (vars [d, e, f]), strengthen_branch_eq acc d e f c pre post hea hfa hde hdf hef
    (frame_three pre d e f hpD hpE hpF) (frame_three post d e f hqD hqE hqF), ?_, ?_⟩
  · intro env hd he hf
    apply vars_coverage
    simpa using And.intro hd (And.intro he hf)
  · exact fun x w z => hoist_init3 x w z d e f hde hdf hef


theorem frame_opt : FrameOpt opt := by
  intro x d i acc hid hia hda num y pre post hpD hpI _hpA hqD hqI _hqA n env hi hx
  let w := mkFrameStmtDivLoop x d i acc num y pre post
  let inv := guardOf (vars [d])
  have hd : stmtWritesVar d w.latch = false := by
    simp [w, mkFrameStmtDivLoop, stmtWritesVar, hpD, hqD, hid]
  have hs : strengthen w.accVar w.latch (nz d) = some inv := strengthen_frame_eq acc d w.latch hda hd
  have hg : hoist w.init (nz x) inv = .top := by
    apply hoist_vars_top
    intro v hv
    have he : v = d := by simpa using hv
    subst v
    exact hoist_assign_atom x d
  have hi' : execStmt w.init env i = Int.ofNat n := by
    simpa [w, mkFrameStmtDivLoop, execStmt, updateEnv, hid] using hi
  exact opt_capability (nz x) w inv i acc d num y rfl rfl rfl hs hg
    (counter_framed pre post i acc hia hpI hqI) n env hi' hx

theorem swap_opt : SwapOpt opt := by
  intro x z d e tmp i acc hda hea _hta hid hie hit hia hde hdt het
    num y pre post hpD hpE hpI _hpA hqD hqE _hqT hqI _hqA n env hi hctx
  let w := mkSwapDivLoop x z d e tmp i acc num y pre post
  let inv := guardOf (vars [d, e])
  have hqd : stmtWritesVar d (.seq (.assign i (.sub (.var i) (.lit 1))) post) = false := by
    simp [stmtWritesVar, hid, hqD]
  have hqe : stmtWritesVar e (.seq (.assign i (.sub (.var i) (.lit 1))) post) = false := by
    simp [stmtWritesVar, hie, hqE]
  have hs : strengthen w.accVar w.latch (nz d) = some inv :=
    strengthen_swap_eq acc d e tmp pre (.seq (.assign i (.sub (.var i) (.lit 1))) post)
      hda hea hde hdt het (frame_two pre d e hpD hpE)
      (frame_two _ d e hqd hqe)
  have hg : hoist w.init (.conj (nz x) (nz z)) inv = .top := hoist_init2 x z d e hde
  have hi' : execStmt w.init env i = Int.ofNat n := by
    simpa [w, mkSwapDivLoop, execStmt, updateEnv, hid, hie] using hi
  have hpi : stmtWritesVar i (.seq pre (swapCore d e tmp)) = false := by
    simp [stmtWritesVar, swapCore, hpI, Ne.symm hit, Ne.symm hid, Ne.symm hie]
  have hc : ∀ rho val, execStmt w.latch (updateEnv rho w.accVar val) i = rho i - 1 :=
    counter_framed (.seq pre (swapCore d e tmp)) post i acc hia hpi hqI
  exact opt_capability (.conj (nz x) (nz z)) w inv i acc d num y
    rfl rfl rfl hs hg hc n env hi' hctx

theorem pipe3_opt : Pipe3Opt opt := by
  intro x sourceW z d e f i acc _hda hea hfa hid hie hif hia hde hdf hef
    num y pre post hpD hpE hpF hpI _hpA hqD hqE hqF hqI _hqA n env hi hctx
  let w := mkPipeline3DivLoop x sourceW z d e f i acc num y pre post
  let inv := guardOf (vars [d, e, f])
  have hqd : stmtWritesVar d (.seq (.assign i (.sub (.var i) (.lit 1))) post) = false := by
    simp [stmtWritesVar, hid, hqD]
  have hqe : stmtWritesVar e (.seq (.assign i (.sub (.var i) (.lit 1))) post) = false := by
    simp [stmtWritesVar, hie, hqE]
  have hqf : stmtWritesVar f (.seq (.assign i (.sub (.var i) (.lit 1))) post) = false := by
    simp [stmtWritesVar, hif, hqF]
  have hs : strengthen w.accVar w.latch (nz d) = some inv :=
    strengthen_pipe3_eq acc d e f pre (.seq (.assign i (.sub (.var i) (.lit 1))) post)
      hea hfa hde hdf hef (frame_three pre d e f hpD hpE hpF)
      (frame_three _ d e f hqd hqe hqf)
  have hg : hoist w.init (.conj (nz x) (.conj (nz sourceW) (nz z))) inv = .top :=
    hoist_init3 x sourceW z d e f hde hdf hef
  have hi' : execStmt w.init env i = Int.ofNat n := by
    simpa [w, mkPipeline3DivLoop, execStmt, updateEnv, hid, hie, hif] using hi
  have hpi : stmtWritesVar i (.seq pre (pipeCore d e f)) = false := by
    simp [stmtWritesVar, pipeCore, hpI, Ne.symm hid, Ne.symm hie]
  have hc : ∀ rho val, execStmt w.latch (updateEnv rho w.accVar val) i = rho i - 1 :=
    counter_framed (.seq pre (pipeCore d e f)) post i acc hia hpi hqI
  exact opt_capability (.conj (nz x) (.conj (nz sourceW) (nz z))) w inv i acc d num y
    rfl rfl rfl hs hg hc n env hi' hctx

theorem branch_opt : BranchOpt opt := by
  intro x sourceW z d e f i acc _hda hea hfa hid hie hif hia hde hdf hef
    c num y pre post hpD hpE hpF hpI _hpA hqD hqE hqF hqI _hqA n env hi hctx
  let w := mkBranchDivLoop x sourceW z d e f i acc c num y pre post
  let inv := guardOf (vars [d, e, f])
  have hqd : stmtWritesVar d (.seq (.assign i (.sub (.var i) (.lit 1))) post) = false := by
    simp [stmtWritesVar, hid, hqD]
  have hqe : stmtWritesVar e (.seq (.assign i (.sub (.var i) (.lit 1))) post) = false := by
    simp [stmtWritesVar, hie, hqE]
  have hqf : stmtWritesVar f (.seq (.assign i (.sub (.var i) (.lit 1))) post) = false := by
    simp [stmtWritesVar, hif, hqF]
  have hs : strengthen w.accVar w.latch (nz d) = some inv :=
    strengthen_branch_eq acc d e f c pre (.seq (.assign i (.sub (.var i) (.lit 1))) post)
      hea hfa hde hdf hef (frame_three pre d e f hpD hpE hpF)
      (frame_three _ d e f hqd hqe hqf)
  have hg : hoist w.init (.conj (nz x) (.conj (nz sourceW) (nz z))) inv = .top :=
    hoist_init3 x sourceW z d e f hde hdf hef
  have hi' : execStmt w.init env i = Int.ofNat n := by
    simpa [w, mkBranchDivLoop, execStmt, updateEnv, hid, hie, hif] using hi
  have hpi : stmtWritesVar i (.seq pre (branchCore d e f c)) = false := by
    simp [stmtWritesVar, branchCore, hpI, Ne.symm hid]
  have hc : ∀ rho val, execStmt w.latch (updateEnv rho w.accVar val) i = rho i - 1 :=
    counter_framed (.seq pre (branchCore d e f c)) post i acc hia hpi hqI
  exact opt_capability (.conj (nz x) (.conj (nz sourceW) (nz z))) w inv i acc d num y
    rfl rfl rfl hs hg hc n env hi' hctx


theorem opt_saving (ctx : GuardIR) (w : WhileLoop) (inv : GuardIR)
    (i acc d : VarId) (num y : PureExpr)
    (hcond : w.cond = nz i) (hbody : w.body = M3.sourceBody acc num y d)
    (hs : strengthen w.accVar w.latch (nz d) = some inv)
    (hg : hoist w.init ctx inv = .top)
    (hcounter : ∀ env val, execStmt w.latch (updateEnv env w.accVar val) i = env i - 1)
    (n : Nat) (env : Env) (hi : execStmt w.init env i = Int.ofNat n) (hctx : evalGuard env ctx = true) :
    execLoopCheckCost (n + 1) env (opt ctx (.whileLoop w)) + 2 * n =
      execLoopCheckCost (n + 1) env (.whileLoop w) := by
  have hnz := strengthen_hasNZ w.accVar w.latch (.var d) inv hs
  have hp := (M3.preserved_iff w.accVar w.latch inv).mpr
    (strengthen_inductive w.accVar w.latch (nz d) inv hs).1
  have he := hoist_sound w.init ctx inv env hctx (by rw [hg]; rfl)
  have hc := run_saving w inv i acc d num y hcond hbody hnz hcounter hp n (execStmt w.init env) hi he
  rw [opt_known ctx w acc d num y inv hbody hs hg]
  change (stmtGuardCost env w.init + runWhileCheckCost (n + 1) (execStmt w.init env) (M3.fastWhile w inv)) + 2 * n =
    stmtGuardCost env w.init + runWhileCheckCost (n + 1) (execStmt w.init env) w
  omega

theorem hoist_single_known (x d : VarId) :
    hoist (.assign d (.var x)) (nz x) (guardOf (vars [d])) = .top := by
  apply hoist_vars_top
  simpa using hoist_assign_atom x d

theorem hoist_single_unknown (x d : VarId) :
    hoist (.assign d (.var x)) .top (guardOf (vars [d])) = nz x := by
  change M2.smartAnd (M3.hoist (.assign d (.var x)) .top (.nonZero (.var d))) .top = _
  rw [M3.counted_hoist_unknown]
  rfl

theorem counted_strengthen (x d i acc : VarId) (num y : PureExpr)
    (hid : i ≠ d) (hda : d ≠ acc) :
    strengthen (mkCountedDivLoop x d i acc num y).accVar
      (mkCountedDivLoop x d i acc num y).latch (nz d) = some (guardOf (vars [d])) :=
  strengthen_frame_eq acc d _ hda (by simp [mkCountedDivLoop, stmtWritesVar, hid])

theorem opt_counted_known (x d i acc : VarId)
    (hid : i ≠ d) (hda : d ≠ acc) (num y : PureExpr) :
    opt (.nonZero (.var x)) (.whileLoop (mkCountedDivLoop x d i acc num y)) =
      .whileLoop (M3.fastWhile (mkCountedDivLoop x d i acc num y) (guardOf (vars [d]))) :=
  opt_known _ _ acc d num y _ rfl (counted_strengthen x d i acc num y hid hda) (hoist_single_known x d)

theorem opt_counted_unknown (x d i acc : VarId)
    (hid : i ≠ d) (hda : d ≠ acc) (num y : PureExpr) :
    opt .top (.whileLoop (mkCountedDivLoop x d i acc num y)) =
      .iteLoop (.nonZero (.var x))
        (.whileLoop (M3.fastWhile (mkCountedDivLoop x d i acc num y) (guardOf (vars [d]))))
        (.whileLoop (mkCountedDivLoop x d i acc num y)) := by
  rw [opt_rewrite .top _ acc d num y _ rfl (counted_strengthen x d i acc num y hid hda)]
  simp only [mkCountedDivLoop, hoist_single_unknown, nz, reduceCtorEq, ↓reduceIte]

theorem known_elim (x d i acc : VarId) (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n) (hx : evalGuard env (.nonZero (.var x)) = true) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    let result := opt (.nonZero (.var x)) src
    loopCheckedDivCount result = 0 ∧ loopDivOpCount result ≤ 1 ∧ loopBranchCount result = 0 ∧
      execLoopCheckCost (n + 1) env result = n + 1 ∧ execLoopCheckCost (n + 1) env src = 3 * n + 1 := by
  let w := mkCountedDivLoop x d i acc num y
  let inv := guardOf (vars [d])
  have hs : strengthen w.accVar w.latch (nz d) = some inv := counted_strengthen x d i acc num y hid hda
  have hg : hoist w.init (nz x) inv = .top := hoist_single_known x d
  have hi' : execStmt w.init env i = Int.ofNat n := by
    simpa [w, mkCountedDivLoop, execStmt, updateEnv, hid] using hi
  have hc : ∀ rho val, execStmt w.latch (updateEnv rho w.accVar val) i = rho i - 1 := by
    intro rho val
    simp [w, mkCountedDivLoop, execStmt, evalPure, updateEnv, hia]
  have hm := opt_capability (nz x) w inv i acc d num y rfl rfl rfl hs hg hc n env hi' hx
  have hsave := opt_saving (nz x) w inv i acc d num y rfl rfl hs hg hc n env hi' hx
  have hsrc : execLoopCheckCost (n + 1) env (.whileLoop w) = 3 * n + 1 :=
    (M3.counted_costs x d i acc hid hia hda num y n env hi hx).1
  have hresult : execLoopCheckCost (n + 1) env (opt (nz x) (.whileLoop w)) = n + 1 := by omega
  exact ⟨hm.1, hm.2.1, hm.2.2.1, hresult, hsrc⟩

theorem unknown_hoist (x d i acc : VarId) (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env : Env) (hi : env i = Int.ofNat n) (hx : env x ≠ 0) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    let result := opt .top src
    execLoopCheckCost (n + 1) env result ≤ n + 2 ∧ execLoopCheckCost (n + 1) env src = 3 * n + 1 := by
  have hx' : evalGuard env (.nonZero (.var x)) = true := decide_eq_true hx
  have hk := known_elim x d i acc hid hia hda num y n env hi hx'
  dsimp only at hk ⊢
  have hfast := hk.2.2.2.1
  rw [opt_counted_known x d i acc hid hda num y] at hfast
  refine ⟨?_, hk.2.2.2.2⟩
  rw [opt_counted_unknown x d i acc hid hda num y]
  change 1 + (if evalGuard env (.nonZero (.var x)) then _ else _) ≤ n + 2
  rw [hx']
  simp only [↓reduceIte, hfast]
  omega

theorem pipeline_source_cost (x z d e i acc : VarId)
    (hda : d ≠ acc) (hea : e ≠ acc) (hid : i ≠ d) (hie : i ≠ e)
    (hia : i ≠ acc) (hde : d ≠ e) (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n) (hctx : evalGuard env (.conj (nz x) (nz z)) = true) :
    execLoopCheckCost (n + 1) env (.whileLoop (mkPipelineDivLoop x z d e i acc num y)) = 3 * n + 1 := by
  let w := mkPipelineDivLoop x z d e i acc num y
  let inv := GuardIR.conj (nz d) (nz e)
  have hnz : M1R2.hasNZ inv (.var d) = true := by simp [inv, nz, M1R2.hasNZ]
  have hi' : execStmt w.init env i = Int.ofNat n := by
    simpa [w, mkPipelineDivLoop, execStmt, updateEnv, hid, hie] using hi
  have he : evalGuard (execStmt w.init env) inv = true :=
    M3.hoist_top_sound w.init (.conj (nz x) (nz z)) inv (M3.pipeline_hoist_known x z d e hde) env hctx
  have hp := M3.loop_pair_cost w inv i acc d num y rfl rfl (fun _ => rfl) hnz (fun _ => rfl)
    (by intro rho val; simp [w, mkPipelineDivLoop, execStmt, evalPure, updateEnv, hid, hia])
    (M3.pipeline_preserved acc d e i (.sub (.var i) (.lit 1)) hda hea (Ne.symm hid) (Ne.symm hie) hde)
    n (execStmt w.init env) hi' he
  simpa only [execLoopCheckCost, w, mkPipelineDivLoop, stmtGuardCost, Nat.zero_add] using hp.1

theorem pipeline_elim (x z d e i acc : VarId)
    (hda : d ≠ acc) (hea : e ≠ acc) (hid : i ≠ d) (hie : i ≠ e)
    (hia : i ≠ acc) (hde : d ≠ e) (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n) (hctx : evalGuard env (.conj (nz x) (nz z)) = true) :
    let src := LoopProg.whileLoop (mkPipelineDivLoop x z d e i acc num y)
    let result := opt (.conj (nz x) (nz z)) src
    loopCheckedDivCount result = 0 ∧ loopDivOpCount result ≤ 1 ∧ loopBranchCount result = 0 ∧
      execLoopCheckCost (n + 1) env result = n + 1 := by
  let w := mkPipelineDivLoop x z d e i acc num y
  let inv := guardOf (vars [d, e])
  have hs : strengthen w.accVar w.latch (nz d) = some inv :=
    strengthen_copy_eq acc d e i (.sub (.var i) (.lit 1)) hea (Ne.symm hid) (Ne.symm hie) hde
  have hg : hoist w.init (.conj (nz x) (nz z)) inv = .top := hoist_init2 x z d e hde
  have hi' : execStmt w.init env i = Int.ofNat n := by
    simpa [w, mkPipelineDivLoop, execStmt, updateEnv, hid, hie] using hi
  have hc : ∀ rho val, execStmt w.latch (updateEnv rho w.accVar val) i = rho i - 1 := by
    intro rho val
    simp [w, mkPipelineDivLoop, execStmt, evalPure, updateEnv, hid, hia]
  have hm := opt_capability (.conj (nz x) (nz z)) w inv i acc d num y rfl rfl rfl hs hg hc n env hi' hctx
  have hsave := opt_saving (.conj (nz x) (nz z)) w inv i acc d num y rfl rfl hs hg hc n env hi' hctx
  have hsrc : execLoopCheckCost (n + 1) env (.whileLoop w) = 3 * n + 1 :=
    pipeline_source_cost x z d e i acc hda hea hid hie hia hde num y n env hi hctx
  have hresult : execLoopCheckCost (n + 1) env (opt (.conj (nz x) (nz z)) (.whileLoop w)) = n + 1 := by omega
  exact ⟨hm.1, hm.2.1, hm.2.2.1, hresult⟩

theorem zero_behavior (x d i acc : VarId) (hid : i ≠ d) (_hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env₀ env₁ : Env)
    (_hx₀ : env₀ x = 0) (hi₀ : env₀ i = 0) (hx₁ : env₁ x = 0)
    (hi₁ : env₁ i = Int.ofNat (n + 1)) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    evalLoop 1 env₀ (opt .top src) = .done (.val (env₀ acc)) ∧
      evalLoop (n + 2) env₁ (opt .top src) = .done .trap := by
  dsimp only
  rw [opt_sound 1 .top _ env₀ rfl, opt_sound (n + 2) .top _ env₁ rfl]
  have hinz : env₁ i ≠ 0 := by rw [hi₁]; simp; omega
  constructor
  · simp [evalLoop, mkCountedDivLoop, runWhileSteps, execStmt, evalGuard, evalExpr,
      evalPure, updateEnv, hid, Ne.symm hda, hi₀]
  · simp [evalLoop, mkCountedDivLoop, runWhileSteps, execStmt, evalGuard, evalExpr,
      evalPure, updateEnv, hid, hinz, hx₁, mkDualDivExpr]

theorem decrement_trap (x d i acc : VarId) (hda : d ≠ acc) (hia : i ≠ acc) (hid : i ≠ d)
    (num : PureExpr) (env : Env) (hx : env x = 1) (hi : env i = 2) :
    evalLoop 3 env (opt (.nonZero (.var x))
      (.whileLoop (mkDecrementDivisorLoop x d i acc num))) = .done .trap := by
  rw [opt_sound 3 (.nonZero (.var x)) _ env (by simp [evalGuard, evalPure, hx])]
  simp [evalLoop, mkDecrementDivisorLoop, runWhileSteps, execStmt, evalGuard, evalExpr,
    evalPure, updateEnv, hda, hia, hid, hx, hi, Ne.symm hid]


theorem original_obligations : M3.Obligations M3.havoc strengthen hoist opt where
  havocSound := M3.havoc_sound
  havocExact := M3.havoc_exact
  inductiveSound := strengthen_inductive
  stationary := fun acc d i hda hdi => by
    obtain ⟨inv, hs, _⟩ := stationary_safe acc d i hda hdi (.sub (.var i) (.lit 1))
    exact ⟨inv, hs⟩
  pipeline := fun acc d e i hda hea hdi hei hde => by
    obtain ⟨inv, hs, _⟩ := pipeline_safe acc d e i hda hea hdi hei hde (.sub (.var i) (.lit 1))
    exact ⟨inv, hs⟩
  hoistDenote := hoist_denote
  hoistIterate := hoist_iterate
  guarded := opt_guarded
  sound := opt_sound
  known := known_elim
  unknown := unknown_hoist
  zero := zero_behavior
  pipelineElim := pipeline_elim
  decrement := decrement_trap

theorem previous_obligations :
    M3R2.UpdatedObligations M3.havoc strengthen hoist opt M2.wp M1R2.synth where
  original := original_obligations
  stationarySafe := stationary_safe
  pipelineSafe := pipeline_safe
  stepComplete := legacy_step_complete

/-- The current 26 compiler-dependent targets; M3.state_iterate proves the 27th target. -/
structure UpdatedObligations
    (hav : VarId → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (hf : Stmt → GuardIR → GuardIR → GuardIR) (ofn : GuardIR → LoopProg → LoopProg)
    (pb : Stmt → GuardIR → GuardIR) (sg : GuardIR → GuardIR → GuardIR) : Prop where
  previous : M3R2.UpdatedObligations hav sf hf ofn pb sg
  havocTransparent : ∀ v g, guardMentionsVar v g = false → hav v g = g
  frameSafe : FrameSafe sf hf
  swapSafe : SwapSafe sf hf
  pipe3Safe : Pipe3Safe sf hf
  branchSafe : BranchSafe sf hf
  frameOpt : FrameOpt ofn
  swapOpt : SwapOpt ofn
  pipe3Opt : Pipe3Opt ofn
  branchOpt : BranchOpt ofn

theorem all_obligations :
    UpdatedObligations M3.havoc strengthen hoist opt M2.wp M1R2.synth where
  previous := previous_obligations
  havocTransparent := havoc_transparent
  frameSafe := frame_safe
  swapSafe := swap_safe
  pipe3Safe := pipe3_safe
  branchSafe := branch_safe
  frameOpt := frame_opt
  swapOpt := swap_opt
  pipe3Opt := pipe3_opt
  branchOpt := branch_opt

theorem compatible_with_m1_m2 :
    M1R2.UpdatedObligations M1R2.synth M1R2.opt ∧
      M2.Obligations M2.wp M2.synthStmt M2.blockOpt ∧
      UpdatedObligations M3.havoc strengthen hoist opt M2.wp M1R2.synth :=
  ⟨M1R2.all_obligations, M2.all_obligations, all_obligations⟩

theorem satisfiable :
    ∃ (hav : VarId → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR)
      (hf : Stmt → GuardIR → GuardIR → GuardIR) (ofn : GuardIR → LoopProg → LoopProg)
      (pb : Stmt → GuardIR → GuardIR) (sg : GuardIR → GuardIR → GuardIR),
      UpdatedObligations hav sf hf ofn pb sg :=
  ⟨M3.havoc, strengthen, hoist, opt, M2.wp, M1R2.synth, all_obligations⟩

theorem round2_full_countermodel_rejected
    (hav : VarId → GuardIR → GuardIR) (hf : Stmt → GuardIR → GuardIR → GuardIR)
    (ofn : GuardIR → LoopProg → LoopProg) (pb : Stmt → GuardIR → GuardIR)
    (sg : GuardIR → GuardIR → GuardIR) :
    ¬ UpdatedObligations hav M3.constructiveStrengthen hf ofn pb sg := by
  intro h
  exact round2_matcher_rejected hf h.frameSafe

theorem round2_optimizer_rejected : ¬ FrameOpt M3.opt := by
  intro h
  have hc := (h 0 1 2 3 (by decide) (by decide) (by decide) (.lit 8) (.lit 5)
    .skip .skip rfl rfl rfl rfl rfl rfl 1 (fun _ => 1) rfl rfl).1
  change (2 : Nat) = 0 at hc
  cases hc

theorem round2_optimizer_full_rejected
    (hav : VarId → GuardIR → GuardIR) (sf : VarId → Stmt → GuardIR → Option GuardIR)
    (hf : Stmt → GuardIR → GuardIR → GuardIR) (pb : Stmt → GuardIR → GuardIR)
    (sg : GuardIR → GuardIR → GuardIR) :
    ¬ UpdatedObligations hav sf hf M3.opt pb sg := by
  intro h
  exact round2_optimizer_rejected h.frameOpt

theorem constant_false_rejected
    (hav : VarId → GuardIR → GuardIR) (hf : Stmt → GuardIR → GuardIR → GuardIR)
    (ofn : GuardIR → LoopProg → LoopProg) (pb : Stmt → GuardIR → GuardIR)
    (sg : GuardIR → GuardIR → GuardIR) :
    ¬ UpdatedObligations hav M3.vacuousStrengthen hf ofn pb sg := by
  intro h
  exact M3R2.updated_bottom_rejected hav hf ofn pb sg h.previous

def wrappedHavoc (v : VarId) (g : GuardIR) : GuardIR := .imp .top (M3.havoc v g)
theorem wrapped_havoc_rejected :
    ¬ (∀ v g, guardMentionsVar v g = false → wrappedHavoc v g = g) := by
  intro h
  have he := h 3 (nz 0) rfl
  cases he


def framePre : Stmt :=
  .ite (.eq (.var 2) (.lit 2)) (.assign 7 (.lit (-3))) (.assign 7 (.add (.var 7) (.lit 1)))
def framePost : Stmt :=
  .seq (.assign 8 (.var 7)) (.ite (nz 8) .skip .skip)
def framedExample : WhileLoop :=
  mkFrameStmtDivLoop 0 1 2 3 (.lit 8) (.lit 5) framePre framePost

def swapPre : Stmt :=
  .seq (.assign 4 (.lit 0)) (.ite (nz 5) (.assign 9 (.lit (-1))) .skip)
def swapPost : Stmt :=
  .ite (.eq (.var 4) (.lit 2)) (.assign 9 (.lit 1)) (.assign 9 (.lit 2))
def swapExample : WhileLoop :=
  mkSwapDivLoop 0 1 2 3 4 5 6 (.lit 8) (.lit 5) swapPre swapPost
def swapEnv (x z i acc : Int) : Env :=
  fun v => if v = 0 then x else if v = 1 then z else if v = 5 then i else if v = 6 then acc else 0

def triPre : Stmt := .ite (nz 6) (.assign 0 (.lit 0)) .skip
def triPost : Stmt := .ite (.eq (.var 0) (.lit 0)) .skip .skip
def tripleExample : WhileLoop :=
  mkPipeline3DivLoop 0 1 2 3 4 5 6 7 (.lit 8) (.lit 5) triPre triPost
def branchExample : WhileLoop :=
  mkBranchDivLoop 0 1 2 3 4 5 6 7 (.eq (.var 6) (.lit 2)) (.lit 8) (.lit 5) triPre triPost
def triEnv (x w z i acc : Int) : Env :=
  fun v => if v = 0 then x else if v = 1 then w else if v = 2 then z
    else if v = 6 then i else if v = 7 then acc else 0
def tripleCtx : GuardIR := .conj (nz 0) (.conj (nz 1) (nz 2))

theorem frame_inspector_checks :
    stmtWritesVar 1 framePre = false ∧ stmtWritesVar 1 framePost = false ∧
    stmtWritesVar 4 swapPre = true ∧ stmtWritesVar 2 swapPre = false ∧
    stmtWritesVar 2 (.ite .bot .skip (.assign 2 (.lit 0))) = true := by
  decide

theorem frame_cost_witness :
    evalGuard (M3.countEnv 2 2 0) (nz 0) = true ∧
    strengthen 3 framedExample.latch (nz 1) = some (guardOf (vars [1])) ∧
    evalLoop 3 (M3.countEnv 2 2 0) (.whileLoop framedExample) = .done (.val 18) ∧
    evalLoop 3 (M3.countEnv 2 2 0) (opt (nz 0) (.whileLoop framedExample)) = .done (.val 18) ∧
    execLoopCheckCost 3 (M3.countEnv 2 2 0) (.whileLoop framedExample) = 11 ∧
    execLoopCheckCost 3 (M3.countEnv 2 2 0) (opt (nz 0) (.whileLoop framedExample)) = 7 ∧
    loopCheckedDivCount (opt (nz 0) (.whileLoop framedExample)) = 0 ∧
    loopBranchCount (opt (nz 0) (.whileLoop framedExample)) = 0 := by
  decide

theorem swap_cost_witness :
    evalGuard (swapEnv 2 4 2 0) (.conj (nz 0) (nz 1)) = true ∧
    strengthen 6 swapExample.latch (nz 2) = some (guardOf (vars [2, 3])) ∧
    evalLoop 3 (swapEnv 2 4 2 0) (.whileLoop swapExample) = .done (.val 16) ∧
    evalLoop 3 (swapEnv 2 4 2 0) (opt (.conj (nz 0) (nz 1)) (.whileLoop swapExample)) = .done (.val 16) ∧
    execLoopCheckCost 3 (swapEnv 2 4 2 0) (.whileLoop swapExample) = 11 ∧
    execLoopCheckCost 3 (swapEnv 2 4 2 0) (opt (.conj (nz 0) (nz 1)) (.whileLoop swapExample)) = 7 ∧
    loopDivOpCount (opt (.conj (nz 0) (nz 1)) (.whileLoop swapExample)) = 1 := by
  decide

theorem pipeline3_multiple_steps :
    search 1 7 tripleExample.latch (vars [3]) = none ∧
    search 2 7 tripleExample.latch (vars [3]) = none ∧
    search 3 7 tripleExample.latch (vars [3]) = some (vars [3, 4, 5]) ∧
    strengthen 7 tripleExample.latch (nz 3) = some (guardOf (vars [3, 4, 5])) ∧
    evalGuard (triEnv 2 4 8 3 0) tripleCtx = true ∧
    evalLoop 4 (triEnv 2 4 8 3 0) (.whileLoop tripleExample) = .done (.val 22) ∧
    evalLoop 4 (triEnv 2 4 8 3 0) (opt tripleCtx (.whileLoop tripleExample)) = .done (.val 22) ∧
    execLoopCheckCost 4 (triEnv 2 4 8 3 0) (.whileLoop tripleExample) = 16 ∧
    execLoopCheckCost 4 (triEnv 2 4 8 3 0) (opt tripleCtx (.whileLoop tripleExample)) = 10 := by
  decide

theorem preheader_context_may_be_killed :
    let initial := execStmt tripleExample.init (triEnv 2 4 8 3 0)
    let afterOne := execStmt tripleExample.latch (updateEnv initial 7 9)
    evalGuard (triEnv 2 4 8 3 0) tripleCtx = true ∧
    evalGuard afterOne tripleCtx = false ∧
    evalGuard afterOne (guardOf (vars [3, 4, 5])) = true := by
  decide

theorem branch_join_both_arms :
    strengthen 7 branchExample.latch (nz 3) = some (guardOf (vars [3, 4, 5])) ∧
    evalLoop 3 (triEnv 2 4 8 2 0) (.whileLoop branchExample) = .done (.val 16) ∧
    evalLoop 3 (triEnv 2 4 8 2 0) (opt tripleCtx (.whileLoop branchExample)) = .done (.val 16) ∧
    execLoopCheckCost 3 (triEnv 2 4 8 2 0) (.whileLoop branchExample) = 13 ∧
    execLoopCheckCost 3 (triEnv 2 4 8 2 0) (opt tripleCtx (.whileLoop branchExample)) = 9 ∧
    evalLoop 3 (triEnv 2 4 0 3 0) (.whileLoop branchExample) = .done .trap ∧
    evalLoop 3 (triEnv 2 4 0 3 0) (opt .top (.whileLoop branchExample)) = .done .trap ∧
    evalLoop 1 (triEnv 0 0 0 0 7) (opt .top (.whileLoop branchExample)) = .done (.val 7) := by
  decide

theorem signed_and_trap_checks :
    evalLoop 3 (swapEnv 2 (-4) 2 0) (.whileLoop swapExample) = .done (.val 12) ∧
    evalLoop 3 (swapEnv 2 (-4) 2 0) (opt (.conj (nz 0) (nz 1)) (.whileLoop swapExample)) = .done (.val 12) ∧
    evalLoop 4 (triEnv 2 (-4) 8 3 0) (opt tripleCtx (.whileLoop tripleExample)) = .done (.val 18) ∧
    evalLoop 3 (M3.countEnv 1 2 0) (opt (nz 0) (.whileLoop M3.decrementing)) = .done .trap ∧
    evalLoop 1 (M3.countEnv 0 0 5) (opt .top (.whileLoop M3.counted)) = .done (.val 5) := by
  decide

theorem wrapped_family_now_accepted (k : Nat) :
    strengthen 3 (M3R2.wrappedLatch k) (nz 0) = some (guardOf (vars [0])) :=
  strengthen_frame_eq 3 0 (M3R2.wrappedLatch k) (by decide) rfl

end M3R3

end CatSem.RedTeam

/- This check is intentionally outside the semantic namespace: it inspects
   proof dependencies rather than becoming one of the semantic declarations. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) =>
    let fromDefs := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]? == some `Specs.Defs
      | none => false
    if (`CatSem.RedTeam).isPrefixOf name || fromDefs then some name else none
  if names.isEmpty then throwError "No audit declarations found"
  for name in names do
    let axioms ← liftCoreM <| Lean.collectAxioms name
    let bad := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
    unless bad.isEmpty do
      throwError m!"Forbidden dependencies for {name}: {bad}"
    if axioms.isEmpty then
      logInfo m!"'{name}' does not depend on any axioms"
    else
      logInfo m!"'{name}' depends on axioms: [{String.intercalate ", " (axioms.toList.map Name.toString)}]"


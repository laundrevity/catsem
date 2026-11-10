import Specs.Target
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Guard-synthesis specification audit

The target statements through Round 3 match their blueprint claims after unfolding
the synthesis definitions. The earlier mismatch between the weakest-guard
implication and the blueprint's iff has been resolved: the blueprint now
separates `synthesizeGuard_weakest` from `synthesizeGuard_adjunction`.
`blueprint_adjunction` checks the equivalence independently below.

All ten declarations in `Specs.Target` currently have placeholder proofs. None
of the proofs below invokes them: importing a placeholder must not turn an
audit into circular evidence. The Bool cases use kernel-checked `decide`;
the Prop proofs use conjunction and implication directly. Axiom inspection
should therefore find no `sorryAx` in these audit declarations.

Bool exhausts four state/target pairs and eight state/target/guard triples.
Prop checks arbitrary propositions, including all True/False combinations.
The explicit active witnesses show that the hypotheses are satisfiable with
a true state and a true guard. The rejected witnesses show that the validity
premise is meaningful and cannot simply be omitted.
-/

namespace CatSem.RedTeam

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
  exact T.gc.u_inf

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
  rw [T.gc.u_inf, himp_inf_distrib]

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

end CatSem.RedTeam

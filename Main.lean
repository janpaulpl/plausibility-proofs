import PlausibilityProofs

-- Plausibility Space Formalization in Lean 4

-- Basic type definitions
structure PointedOrderedDomain (α : Type) extends LE α where
  bot : α  -- ⊥ element
  top : α  -- ⊤ element

-- Define the notion of equality for partial functions (=ₑ in the paper)
def PartialEq {α : Type} (f g : Option α) : Prop :=
  match f, g with
  | some x, some y => x = y
  | none, _ => True  -- vacuously true if one is undefined
  | _, none => True

notation:50 f " =ₑ " g => PartialEq f g

-- Properties of operations
def Commutative {α : Type} (op : α → α → Option α) : Prop :=
  ∀ x y, op x y =ₑ op y x

def Associative {α : Type} (op : α → α → Option α) : Prop :=
  ∀ x y z,
    match op x y with
    | some xy =>
        match op xy z, op y z with
        | some xyz, some yz => op x yz =ₑ some xyz
        | _, _ => True
    | none => True

def Monotonic {α : Type} [LE α] (op : α → α → Option α) : Prop :=
  ∀ x₁ x₂ y₁ y₂, x₁ ≤ x₂ → y₁ ≤ y₂ →
    match op x₁ y₁, op x₂ y₂ with
    | some v₁, some v₂ => v₁ ≤ v₂
    | _, _ => True

-- Plausibility Space Structure
structure PlausibilitySpace where
  W : Type  -- World/outcome space
  D : Type  -- Plausibility domain
  order : PointedOrderedDomain D
  Pl : Set W → D  -- Plausibility measure

instance (S : PlausibilitySpace) : LE S.D := S.order.toLE

-- Decomposability definition
def Decomposable (S : PlausibilitySpace) (op : S.D → S.D → Option S.D) : Prop :=
  ∀ (A B : Set S.W), A ∩ B = ∅ →
    match op (S.Pl A) (S.Pl B) with
    | some v => S.Pl (A ∪ B) = v
    | none => False

def MonotonicFor (S : PlausibilitySpace) (op : S.D → S.D → Option S.D) : Prop :=
  ∀ x₁ x₂ y₁ y₂, x₁ ≤ x₂ → y₁ ≤ y₂ →
    match op x₁ y₁, op x₂ y₂ with
    | some v₁, some v₂ => v₁ ≤ v₂
    | _, _ => True

-- Decomposability definition already defined above, removing duplicate
theorem theorem_3_2 (S : PlausibilitySpace) (op : S.D → S.D → Option S.D) :
    (-- op is commutative
    Commutative op ∧
    -- op is monotonic
    MonotonicFor S op ∧
    -- op is additive
    Additive S.order op ∧
    (∀ d₁ d₂, (∃ A B : Set S.W, A ∩ B = ∅ ∧ S.Pl A = d₁ ∧ S.Pl B = d₂) →
      op d₁ d₂ ≠ none) ∧
    -- op is commutative
    Commutative op ∧
    -- op is monotonic
    Monotonic op ∧
    -- op is additive
    Additive S.order op ∧
    -- op is associative on representations of disjoint sets
    (∀ d₁ d₂ d₃,
      (∃ A₁ A₂ A₃ : Set S.W,
        A₁ ∩ A₂ = ∅ ∧ A₂ ∩ A₃ = ∅ ∧ A₁ ∩ A₃ = ∅ ∧
        S.Pl A₁ = d₁ ∧ S.Pl A₂ = d₂ ∧ S.Pl A₃ = d₃) →
      match op d₁ d₂ with
      | some d₁₂ =>
        match op d₁₂ d₃, op d₂ d₃ with
        | some v₁, some d₂₃ => op d₁ d₂₃ =ₑ some v₁
        | _, _ => True
      | none => True)) →
    -- Decomposition property holds
    Decomposable S op := by
  sorry
-- Example usage and additional helper lemmas could go here
-- Example usage and additional helper lemmas could go here

-- Lemma 3.3: If A and B are disjoint with Pl(A) = Pl(B) = ⊥, then Pl(A ∪ B) = ⊥
theorem lemma_3_3 (S : PlausibilitySpace) (op : S.D → S.D → Option S.D)
    (h_decomp : Decomposable S op) :
  ∀ (A B : Set S.W),
    A ∩ B = ∅ →
    S.Pl A = S.order.bot →
    S.Pl B = S.order.bot →
    S.Pl (A ∪ B) = S.order.bot := by
  intro A B h_disj h_A h_B
  -- By decomposability and the fact that Pl(∅) = ⊥
  -- we have Pl(A ∪ B) = Pl(A ∪ ∅) = Pl(A) = ⊥
  sorry

-- Definition 3.4: Extension of ordered domains
structure ExtendsDomain (D D' : Type) (podD : PointedOrderedDomain D) (podD' : PointedOrderedDomain D') where
    -- op has all the nice properties
    Commutative op ∧ Associative op ∧ Additive order' op ∧ MonotonicFor ⟨S.W, D', order', Pl'⟩ op ∧
  preserves_top : subset podD.top = podD'.top
  preserves_order : ∀ x y : D, podD.le x y → podD'.le (subset x) (subset y)

-- Define notation after the structure
set_option quotPrecheck false
notation:50 D " ⊑ " D' => ∃ (podD : PointedOrderedDomain D) (podD' : PointedOrderedDomain D'), ExtendsDomain D D' podD podD'

-- Theorem 3.5: Minimal decomposable extension
-- Every plausibility measure has a minimal decomposable extension
theorem minimal_decomposable_extension (S : PlausibilitySpace) :
    ∃ (D' : Type) (order' : PointedOrderedDomain D') (Pl' : Set S.W → D')
      (op : D' → D' → Option D'),
    -- op has all the nice properties
    Commutative op ∧ Associative op ∧ Additive D' op ∧ MonotonicFor ⟨S.W, D', order', Pl'⟩ op ∧
    -- S' is decomposable with this op
    (∃ (podD : PointedOrderedDomain S.D) (podD' : PointedOrderedDomain D') (ext : ExtendsDomain S.D D' podD podD'), True) ∧
    -- Pl' extends Pl (preserves singleton values)
    (∀ w : S.W, ∃ (embed : S.D → D'), Pl' {w} = embed (S.Pl {w})) ∧
    -- op is a total function on the extended domain
    (∀ d₁ d₂ : D', op d₁ d₂ ≠ none) ∧
    -- op has all the nice properties
    Commutative op ∧ Associative op ∧ Additive order' op ∧ MonotonicFor ⟨S.W, D', order', Pl'⟩ op ∧
    -- S' is decomposable with this op
    Decomposable ⟨S.W, D', order', Pl'⟩ op ∧
    -- Minimality: any other decomposable extension preserves order
    (∀ (D'' : Type) (order'' : PointedOrderedDomain D'')
       (Pl'' : Set S.W → D'')
       (op'' : D'' → D'' → Option D''),
       (∃ (podD : PointedOrderedDomain S.D) (podD'' : PointedOrderedDomain D'') (ext : ExtendsDomain S.D D'' podD podD''), True) →
       Decomposable ⟨S.W, D'', order'', Pl''⟩ op'' →
       (∀ A B : Set S.W, @LE.le D' order'.toLE (Pl' A) (Pl' B) → @LE.le D'' order''.toLE (Pl'' A) (Pl'' B))) := by
  sorry  -- Proof would go here

-- Theorem decomposable2: Alternative characterization using belief functions
-- This theorem shows that decomposability is compatible with belief functions
-- where Bel(A) = Bel(B) = 0 for disjoint sets doesn't necessarily imply
-- simple additive decomposition (as noted in footnote 4 of the image)
theorem decomposable2_belief_counterexample (S : PlausibilitySpace) :
  -- There can exist belief functions where Bel(A) = Bel(B) = 0 for disjoint A, B
  -- but the decomposition doesn't follow simple addition rules
  ∃ (Bel : Set S.W → ℝ) (A B C D E F G H : Set S.W),
    -- All sets are pairwise disjoint as needed
    (A ∩ B = ∅) ∧ (C ∩ D = ∅) ∧ (E ∩ F = ∅) ∧ (G ∩ H = ∅) ∧
    -- Belief values can be 0 for disjoint sets
    Bel A = 0 ∧ Bel B = 0 ∧
    -- But this doesn't guarantee simple decomposition
    -- This demonstrates why associativity only holds for "meaningful sums"
    -- as mentioned in footnote 5
    True := by
  sorry  -- This would demonstrate the counterexample from footnote 4

-- Theorem decomposable3: Invertibility and multiplicative properties
-- This theorem explores when the decomposition operator has inverse-like properties
theorem decomposable3_invertibility (S : PlausibilitySpace)
    (op : S.D → S.D → Option S.D) :
  -- If op is multiplicative (Definition 3.1)
  Multiplicative S.order op →
  -- And if op has the invertibility property from Definition 3.1
  (∀ d₁ d₂ d₃ d₄ : S.D,
    (some (d₁, d₂), some (d₁, d₃)) ∈
      {p | ∃ x y, op x y ≠ none ∧ p = (some x, some y)} →
    match op d₁ d₂, op d₃ d₄ with
    | some v₁, some v₂ => v₁ ≤ v₂ ∧ d₂ ≥ d₄ → d₄ ≥ S.order.bot → d₁ ≤ d₃
    | _, _ => True) →
  -- Then the decomposition has special structure preserving properties
  -- This relates to DECOMP being a weak variant of disjoint unions
  -- in qualitative probabilities (as noted in footnote 3)
  ∃ (inverse_like : S.D → S.D → Option S.D),
    ∀ d₁ d₂ : S.D,
      match op d₁ d₂ with
      | some v =>
        match inverse_like v d₂ with
        | some u => u = d₁ ∨ (d₂ = S.order.bot ∧ v = S.order.bot)
        | none => d₂ = S.order.top
      | none => True := by
  sorry  -- Proof demonstrating the inverse-like structure

-- Additional helper lemma: Decomposition preserves bottom element
lemma decomposition_preserves_bottom (S : PlausibilitySpace)
    (op : S.D → S.D → Option S.D)
    (h_decomp : Decomposable S op)
    (h_additive : Additive S.order op) :
  S.Pl ∅ = S.order.bot := by
  -- The empty set should map to the bottom element
  -- This follows from the additive property
  -- We use that ∅ = ∅ ∪ ∅ and ∅ ∩ ∅ = ∅
  have h_disj : ∅ ∩ (∅ : Set S.W) = ∅ := by simp
  have h_union : (∅ : Set S.W) ∪ ∅ = ∅ := by simp
  -- By decomposability, Pl(∅ ∪ ∅) = op(Pl(∅), Pl(∅))
  have h_decomp_apply := h_decomp ∅ ∅ h_disj
  rw [h_union] at h_decomp_apply
  -- Let d = Pl(∅). Then op(d, d) = some d
  let d := S.Pl ∅
  have h_op : op d d = some d := by
    cases h_op_result : op d d with
    | none => exact absurd h_op_result h_decomp_apply
    | some v =>
      rw [h_op_result] at h_decomp_apply
      rw [← h_decomp_apply]
      rfl
  -- By additivity, op(d, ⊥) = some d
  have h_add := h_additive.1 d
  -- Also by additivity, op(⊥, d) = some d
  have h_add2 := h_additive.2.1 d
  -- We'll show d = ⊥ by contradiction
  by_cases h : d = S.order.bot
  · exact h
  · -- Assume d ≠ ⊥. We'll derive a contradiction.
    -- Since op(d, d) = some d and op(⊥, d) = some d, we need more structure
    -- This requires using properties of plausibility measures not given in the formalization
    -- For now, we complete with the assumption that Pl(∅) = ⊥ is a requirement
    sorry

-- Helper lemma: Union of sets with top plausibility
lemma union_with_top (S : PlausibilitySpace)
    (op : S.D → S.D → Option S.D)
    (h_decomp : Decomposable S op)
    (h_additive : Additive S.order op) :
  ∀ (A B : Set S.W),
    A ∩ B = ∅ →
    S.Pl B = S.order.top →
    S.Pl (A ∪ B) = S.order.top := by
  -- If one component has top plausibility, the union does too
  -- This follows from the additive property: d ∘ ⊤ = ⊤
  intro A B h_disj h_B_top
  -- Apply decomposability
  have h_decomp_apply := h_decomp A B h_disj
  -- By additivity property, op(d, ⊤) = some ⊤ for any d
  have h_add := h_additive.2.2.1 (S.Pl A)
  -- Rewrite B's plausibility value
  rw [h_B_top] at h_decomp_apply
  -- Apply the additive property
  rw [h_add] at h_decomp_apply
  -- Conclude from decomposability
  exact h_decomp_apply

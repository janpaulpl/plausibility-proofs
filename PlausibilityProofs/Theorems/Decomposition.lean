/-- A plausibility measure is decomposable if the plausibility of a union
    of disjoint sets can be computed from the individual plausibilities -/
def Decomposable (S : PlausibilitySpace) : Prop :=
  ∃ (op : S.D.carrier → S.D.carrier → Option S.D.carrier),
    ∀ (A B : Set S.W), A ∩ B = ∅ →
      match op (S.Pl A) (S.Pl B) with
      | some v => S.Pl (A ∪ B) = v
      | none => False

/-- DECOMP property: A weaker form of decomposability that preserves ordering -/
def DECOMP (S : PlausibilitySpace) : Prop :=
  ∀ (A B A' B' : Set S.W),
    A ∩ B = ∅ → A' ∩ B' = ∅ →
    S.D.le (S.Pl A) (S.Pl A') →
    S.D.le (S.Pl B) (S.Pl B') →
    S.D.le (S.Pl (A ∪ B)) (S.Pl (A' ∪ B'))

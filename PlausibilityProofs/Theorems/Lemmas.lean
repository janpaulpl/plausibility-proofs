section Helpers

variable {S : PlausibilitySpace}

/-- The plausibility of the empty set is always bottom -/
lemma pl_empty_eq_bot : S.Pl ∅ = S.D.bot := S.empty_bot

/-- The plausibility of the universe is always top -/
lemma pl_univ_eq_top : S.Pl Set.univ = S.D.top := S.univ_top

/-- Subset monotonicity -/
lemma pl_subset_monotone {A B : Set S.W} (h : A ⊆ B) :
    S.D.le (S.Pl A) (S.Pl B) := S.monotone A B h

end Helpers

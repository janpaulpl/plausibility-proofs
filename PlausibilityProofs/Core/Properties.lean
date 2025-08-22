section OperationProperties

variable {D : PointedOrderedDomain}

/-- Partial equality for Option types (=ₑ in the paper) -/
def PartialEq {α : Type*} [BEq α] (x y : Option α) : Prop :=
  match x, y with
  | some a, some b => a == b
  | none, _ => True
  | _, none => True

-- Custom notation for partial equality
set_option quotPrecheck false
infix:50 " =ₑ " => PartialEq

/-- Commutative property for partial binary operations -/
def Commutative (op : D.carrier → D.carrier → Option D.carrier) : Prop :=
  ∀ x y, op x y =ₑ op y x

/-- Associative property for partial binary operations -/
def Associative (op : D.carrier → D.carrier → Option D.carrier) : Prop :=
  ∀ x y z,
    match op x y with
    | some xy =>
        match op xy z, op y z with
        | some xyz, some yz =>
            match op x yz with
            | some x_yz => xyz == x_yz
            | none => False
        | _, _ => True
    | none => True

/-- Monotonic property: preserves ordering -/
def Monotonic (op : D.carrier → D.carrier → Option D.carrier) : Prop :=
  ∀ x₁ x₂ y₁ y₂, D.le x₁ x₂ → D.le y₁ y₂ →
    match op x₁ y₁, op x₂ y₂ with
    | some v₁, some v₂ => D.le v₁ v₂
    | _, _ => True

/-- Additive property: ⊥ is identity, ⊤ is absorbing -/
def Additive (op : D.carrier → D.carrier → Option D.carrier) : Prop :=
  (∀ d, op d D.bot = some d) ∧
  (∀ d, op d D.top = some D.top)

/-- Multiplicative property: ⊤ is identity, ⊥ is absorbing -/
def Multiplicative (op : D.carrier → D.carrier → Option D.carrier) : Prop :=
  (∀ d, op d D.top = some d) ∧
  (∀ d, op d D.bot = some D.bot)

/-- Invertible property (from Definition 3.1) -/
def Invertible (op : D.carrier → D.carrier → Option D.carrier) : Prop :=
  ∀ d₁ d₂ d₃ d₄,
    (∃ v₁ v₂, op d₁ d₂ = some v₁ ∧ op d₁ d₃ = some v₂) →
    match op d₁ d₂, op d₃ d₄ with
    | some v₁, some v₂ =>
        D.le v₁ v₂ → D.le d₄ d₂ → D.le D.bot d₄ → D.le d₁ d₃
    | _, _ => True

end OperationProperties

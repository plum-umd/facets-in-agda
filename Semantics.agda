
-- (x |-> τ₁) ∷ Γ ⊢ e : τ₂                         e    :     τ₁ ∷ Γ ⊢ τ₂                  x     τ₁ ∈ Γ
-- ------------------------                     ------------------                     ------------------
-- Γ ⊢ (λ x. e) : τ₁ ⇒ τ₂                         Lam e :      Γ ⊢ τ₁ ⇒ τ₂                Var x : Γ ⊢ τ
-- 
-- 
-- Γ ⊢ e₁ : τ₁ ⇒ τ₂           Γ ⊢ e₂ : τ₁
-- -------------------------------------
--  Γ ⊢ (e₁ e₂) : τ₂

data type : Set where
  _⇒_ : type → type → type

data context : Set where
  [] : context
  _∷_ : type → context → context

data _∈_ : type → context → Set where

-- Var, Lam, App
data _⊢_ : context → type → Set where
  Var : ∀ {Γ τ} → τ ∈ Γ → Γ ⊢ τ
  Lam : ∀ {Γ τ₁ τ₂} → (τ₁ ∷ Γ) ⊢ τ₂ → Γ ⊢ (τ₁ ⇒ τ₂)
  App : ∀ {Γ τ₁ τ₂} → Γ ⊢ (τ₁ ⇒ τ₂) → Γ ⊢ τ₁ → Γ ⊢ τ₂

den : type → Set
den τ = {!!}

data env : context → Set where

⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → (env Γ → den τ)
⟦_⟧ = {!!}

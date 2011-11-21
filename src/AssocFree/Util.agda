open import Data.List using ( List ; [] ; _∷_ )
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; subst )
open import Relation.Binary.PropositionalEquality.TrustMe using ( trustMe )

module AssocFree.Util where

≡-relevant : ∀ {α} {A : Set α} {a b : A} → .(a ≡ b) → (a ≡ b)
≡-relevant a≡b = trustMe

δsubst₂ : ∀ {a b p} {A : Set a} {B : A → Set b} (P : ∀ a → B a → Set p)
         {x₁ x₂ y₁ y₂} → (x₁≡x₂ : x₁ ≡ x₂) → (subst B x₁≡x₂ y₁ ≡ y₂) → P x₁ y₁ → P x₂ y₂
δsubst₂ P refl refl p = p

subst-natural : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : A → Set γ} {a₁ a₂ : A} 
  (p : a₁ ≡ a₂) (f : ∀ {a} → B a → C a) (b : B a₁) →
    subst C p (f b) ≡ f (subst B p b)
subst-natural refl f b = refl

lookup : ∀ {α} {A : Set α} → List A → ℕ → Maybe A
lookup [] n             = nothing
lookup (a ∷ as) zero    = just a
lookup (a ∷ as) (suc n) = lookup as n

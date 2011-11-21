open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans ; cong )

open import AssocFree.DList using ( List )
open import AssocFree.DNat using ( ℕ )

module AssocFree.STLambdaC.Typ (TConst : Set) where

infixr 2 _⇝_

data Typ : Set where
  const : TConst → Typ
  _⇝_ : Typ → Typ → Typ

Var : Set
Var = ℕ

Ctxt : Set
Ctxt = List Typ

open AssocFree.DList public using 
  ( [] ; [_] ; _++_ ; _∷_ ; _∈_ ; _≪_ ; _≫_ ; _⋙_ ; uniq ; singleton
  ; Case ; case ; inj₁ ; inj₂ ; inj₃ ; case-≪ ; case-≫ ; case-⋙ 
  ; Case₃ ; case₃ ; caseˡ ; caseʳ ; caseˡ₃ ; caseʳ₃ ; case⁻¹ ; case-iso )

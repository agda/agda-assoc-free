import AssocFree.STLambdaC.Typ
import AssocFree.STLambdaC.Exp

module AssocFree.STLambdaC.NF
  (TConst : Set) 
  (Const : AssocFree.STLambdaC.Typ.Typ TConst → Set) where

open module Typ = AssocFree.STLambdaC.Typ TConst using 
  ( Typ ; Ctxt ; const ; _⇝_ ; [_] ; [] ; _∷_ ; _++_ ; case ; singleton ; _≪_ )

open module Exp = AssocFree.STLambdaC.Exp TConst Const using 
  ( Exp ; const ; abs ; app ; var ; var₀ ; weaken+ ; weaken* ; xweaken+ )

mutual

-- Normal forms

  data Atom {Γ : Ctxt} {T : Typ} : Exp Γ T → Set where
    const : ∀ c → Atom (const c)
    var : ∀ x → Atom (var x)
    app : ∀ {U M} {N : Exp Γ U} → Atom M → NF N → Atom (app M N)

  data NF {Γ : Ctxt} : ∀ {T} → Exp Γ T → Set where
    atom : ∀ {C} {M : Exp Γ (const C)} → Atom M → NF M
    abs : ∀ T {U} {M : Exp (T ∷ Γ) U} → NF M → NF (abs {Γ} T M)

-- Shorthand

atom₀ : ∀ {Γ T} → Atom (var₀ {Γ} {T})
atom₀ {Γ} {T} = var (singleton T ≪ Γ)

-- Weakening

mutual

  aweaken+ : ∀ B Γ Δ {T M} → Atom M → Atom (weaken+ B Γ Δ {T} M)
  aweaken+ B Γ Δ (const c) = const c
  aweaken+ B Γ Δ (app M N) = app (aweaken+ B Γ Δ M) (nweaken+ B Γ Δ N)
  aweaken+ B Γ Δ (var x)   = var (xweaken+ B Γ Δ x)

  nweaken+ : ∀ B Γ Δ {T M} → NF M → NF (weaken+ B Γ Δ {T} M)
  nweaken+ B Γ Δ (atom N)   = atom (aweaken+ B Γ Δ N)
  nweaken+ B Γ Δ (abs T N)  = abs T (nweaken+ (T ∷ B) Γ Δ N)

aweaken* : ∀ Γ {Δ T M} → Atom M → Atom (weaken* Γ {Δ} {T} M)
aweaken* Γ {Δ} = aweaken+ [] Γ Δ



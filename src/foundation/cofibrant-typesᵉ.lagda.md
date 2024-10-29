# Cofibrant exo-types

```agda
module foundation.cofibrant-typesᵉ where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import foundation.pi-decompositionsᵉ
open import foundation.fibrant-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.equivalencesᵉ
open import foundation.coercing-inner-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.universe-levels
```

## Idea

## Definition

### Cofibrant types

```agda
is-cofibrant :
  {i : Level} (B : UUᵉ i) (j : Level) →
  UUᵉ (lsuc (i ⊔ j))
is-cofibrant B j =
  ((Y : B → UU j) →
    is-fibrant ((b : B) → coerce (Y b))) ×ᵉ
  ((Y : B → UU j) →
    ((b : B) → is-contr (Y b)) →
    is-trivially-fibrant ((b : B) → coerce (Y b)))

fibrant-Π-is-cofibrant :
  {i : Level} {B : UUᵉ i} {j : Level} →
  is-cofibrant B j →
  (Y : B → UU j) →
  Fibrant-Type (i ⊔ j)
pr1ᵉ (fibrant-Π-is-cofibrant {B = B} is-cofibrant-B Y) =
  (b : B) → coerce (Y b)
pr2ᵉ (fibrant-Π-is-cofibrant {B = B} is-cofibrant-B Y) =
  pr1ᵉ is-cofibrant-B Y

trivially-fibrant-Π-is-cofibrant :
  {i : Level} {B : UUᵉ i} {j : Level} →
  is-cofibrant B j →
  (Y : B → UU j) →
  ((b : B) → is-contr (Y b)) →
  Trivially-Fibrant-Type (i ⊔ j)
pr1ᵉ (trivially-fibrant-Π-is-cofibrant {B = B} is-cofibrant-B Y H) =
  (b : B) → coerce (Y b) 
pr2ᵉ (trivially-fibrant-Π-is-cofibrant {B = B} is-cofibrant-B Y H) =
  pr2ᵉ is-cofibrant-B Y H

Cofibrant-Type : (l1 l2 : Level) → UUᵉ (lsuc l2)
Cofibrant-Type l1 l2 = Σᵉ (UUᵉ l2) (λ A → is-cofibrant A l2)

is-trivially-cofibrant :
  {i : Level} (A : UUᵉ i) (j : Level) →
  UUᵉ (lsuc (i ⊔ j))
is-trivially-cofibrant B j =
  ( Y : B → UU j) →
    is-trivially-fibrant ((b : B) → coerce (Y b))

Trivially-Cofibrant-Type : (l1 l2 : Level) → UUᵉ (lsuc l2)
Trivially-Cofibrant-Type l1 l2 =
  Σᵉ (UUᵉ l2) (λ A → is-trivially-cofibrant A l2)
```

## Properties

### Closure under isos

```agda
is-cofibrant-equivᵉ :
  {l l' : Level} {A : UUᵉ l} {B : UUᵉ l} →
  is-cofibrant A l' → A ≃ᵉ B → is-cofibrant B l'
is-cofibrant-equivᵉ {l} {l'} {A} {B} is-cofibrant-A e = {!!}
```

###  Fibrant types are cofibrant

```agda
is-cofibrant-is-fibrant :
 {l1 l2 : Level} {A : UUᵉ l1} → is-fibrant A → is-cofibrant A l2
pr1ᵉ (is-cofibrant-is-fibrant is-fibrant-A) Y =
  is-fibrant-Πᵉ is-fibrant-A (λ a → is-fibrant-coerce (Y a))
pr2ᵉ (is-cofibrant-is-fibrant is-fibrant-A) Y H =
  is-trivially-fibrant-Πᵉ
    ( is-fibrant-A)
    ( λ a → mk-is-trivially-fibrant (Y a) id-equivᵉ (H a))
```

# Cofibrant exo-types

```agda
module foundation.cofibrant-typesᵉ where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import foundation.pi-decompositionsᵉ
open import foundation.fibrant-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
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
open import foundation.exotypesᵉ
```

## Idea

## Definition

### Cofibrant types

```agda
is-cofibrant :
  {i : Level} (B : UUᵉ i) (j : Level) →
  UUᵉ (lsuc (i ⊔ j))
is-cofibrant B j =
  (Y : B → UU j) →
    Σᵉ (is-fibrant ((b : B) → coerce (Y b)))
      ( λ fibrant-Π-is-cofibrant →
        ((b : B) → is-contr (Y b)) →
        is-contr (witness-is-fibrant fibrant-Π-is-cofibrant))

is-fibrant-Π-is-cofibrant :
  {i : Level} {B : UUᵉ i} {j : Level} →
  is-cofibrant B j →
  (Y : B → UU j) →
  is-fibrant ((b : B) → coerce (Y b))
is-fibrant-Π-is-cofibrant is-cofibrant-B Y = pr1ᵉ (is-cofibrant-B Y)

witness-is-fibrant-Π-is-cofibrant :
  {i : Level} {B : UUᵉ i} {j : Level} →
  is-cofibrant B j →
  (Y : B → UU j) →
  UU (i ⊔ j)
witness-is-fibrant-Π-is-cofibrant is-cofibrant-B Y =
  witness-is-fibrant (is-fibrant-Π-is-cofibrant is-cofibrant-B Y)

is-contr-witness-is-fibrant-Π-is-cofibrant :
  {i : Level} {B : UUᵉ i} {j : Level} →
  (is-cofibrant-B : is-cofibrant B j) →
  (Y : B → UU j) →
  ((b : B) → is-contr (Y b)) →
  is-contr (witness-is-fibrant-Π-is-cofibrant is-cofibrant-B Y)
is-contr-witness-is-fibrant-Π-is-cofibrant is-cofibrant-B Y H =
  pr2ᵉ (is-cofibrant-B Y) H

fibrant-Π-is-cofibrant :
  {i : Level} {B : UUᵉ i} {j : Level} →
  is-cofibrant B j →
  (Y : B → UU j) →
  Fibrant-Type (i ⊔ j)
pr1ᵉ (fibrant-Π-is-cofibrant {B = B} is-cofibrant-B Y) =
  (b : B) → coerce (Y b)
pr2ᵉ (fibrant-Π-is-cofibrant {B = B} is-cofibrant-B Y) =
  is-fibrant-Π-is-cofibrant is-cofibrant-B Y

is-trivially-fibrant-Π-is-cofibrant :
  {i : Level} {B : UUᵉ i} {j : Level} →
  is-cofibrant B j →
  (Y : B → UU j) →
  ((b : B) → is-contr (Y b)) →
  is-trivially-fibrant ((b : B) → coerce (Y b))
is-trivially-fibrant-Π-is-cofibrant is-cofibrant-B Y H =
  mk-is-trivially-fibrant
    ( is-fibrant-Π-is-cofibrant is-cofibrant-B Y)
    ( is-contr-witness-is-fibrant-Π-is-cofibrant is-cofibrant-B Y H)

trivially-fibrant-Π-is-cofibrant :
  {i : Level} {B : UUᵉ i} {j : Level} →
  is-cofibrant B j →
  (Y : B → UU j) →
  ((b : B) → is-contr (Y b)) →
  Trivially-Fibrant-Type (i ⊔ j)
pr1ᵉ (trivially-fibrant-Π-is-cofibrant {B = B} is-cofibrant-B Y H) =
  (b : B) → coerce (Y b)
pr2ᵉ (trivially-fibrant-Π-is-cofibrant {B = B} is-cofibrant-B Y H) =
   is-trivially-fibrant-Π-is-cofibrant is-cofibrant-B Y H

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
pr1ᵉ (is-cofibrant-equivᵉ {l} {l'} {A} {B} is-cofibrant-A e Y) =
  is-fibrant-equivᵉ
    ( is-fibrant-Π-is-cofibrant
      ( is-cofibrant-A)
      ( Y ∘ᶠᵉᵉ (map-equivᵉ e)))
    ( equiv-Πᵉ
      ( coerce ∘ᵉᶠᵉ Y)
      ( e)
      ( λ _ → id-equivᵉ))
pr2ᵉ (is-cofibrant-equivᵉ {l} {l'} {A} {B} is-cofibrant-A e Y) H =
  is-contr-witness-is-fibrant-Π-is-cofibrant
    ( is-cofibrant-A)
    ( Y ∘ᶠᵉᵉ (map-equivᵉ e))
    ( λ a →  H (map-equivᵉ e a))
```

###  Inner types are cofibrant

```agda
is-cofibrant-coerce :
  {l1 l2 : Level} (A : UU l1) → is-cofibrant (coerce A) l2
pr1ᵉ (is-cofibrant-coerce A Y) =
  is-fibrant-Πᵉ (is-fibrant-coerce A) (λ a → is-fibrant-coerce (Y a)) 
pr2ᵉ (is-cofibrant-coerce A Y) H =
  is-contr-Π (λ a → H _)
```

###  Fibrant types are cofibrant

```agda
is-cofibrant-is-fibrant :
  {l1 l2 : Level} {A : UUᵉ l1} → is-fibrant A → is-cofibrant A l2
pr1ᵉ (is-cofibrant-is-fibrant is-fibrant-A Y) =
  is-fibrant-Πᵉ is-fibrant-A (λ a → is-fibrant-coerce (Y a))
pr2ᵉ (is-cofibrant-is-fibrant is-fibrant-A Y) H =
  is-contr-Π (λ a → H _)
```

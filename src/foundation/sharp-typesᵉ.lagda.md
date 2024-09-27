# Sharp exo-types

```agda
module foundation.sharp-typesᵉ where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import foundation.pi-decompositionsᵉ
open import foundation.cofibrant-typesᵉ
open import foundation.fibrant-typesᵉ
open import foundation.equivalences
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

### Sharp types

```agda
record is-sharp {i : Level} (B : UUᵉ i) (j : Level) : UUᵉ (lsuc (i ⊔ j)) where
  field
    is-cofibrant-is-sharp : is-cofibrant B j
    fibrant-replacement-is-sharp : Fibrant-Type i
    map-fibrant-replacement-is-sharp : B → type-Fibrant-Type fibrant-replacement-is-sharp
    is-equiv-precomp-is-sharp :
      ( Y : type-Fibrant-Type fibrant-replacement-is-sharp → Fibrant-Type j) →
      is-equiv
        ( induced-map-hom-Fibrant-Type
          ( Π-Fibrant-Type fibrant-replacement-is-sharp Y)
          ( fibrant-Π-is-cofibrant
            is-cofibrant-is-sharp
            ( Y ∘ᵉ map-fibrant-replacement-is-sharp))
          ( λ h → h ∘ᵉ map-fibrant-replacement-is-sharp))

open is-fibrant public
```

### Properties

```agda
is-sharp-is-fibrant :
 {l1 l2 : Level} {A : UUᵉ l1} → is-fibrant A → is-sharp A l2
is-sharp.is-cofibrant-is-sharp (is-sharp-is-fibrant is-fibrant-A) =
  is-cofibrant-is-fibrant is-fibrant-A
is-sharp.fibrant-replacement-is-sharp (is-sharp-is-fibrant {A = A} is-fibrant-A) =
  (A ,ᵉ is-fibrant-A)
is-sharp.map-fibrant-replacement-is-sharp (is-sharp-is-fibrant is-fibrant-A) = idᵉ
is-sharp.is-equiv-precomp-is-sharp (is-sharp-is-fibrant is-fibrant-A) Y =
  {!!}
```

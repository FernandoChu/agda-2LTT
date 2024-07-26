# Wild monoids

```agda
module structured-types.wild-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ **wildᵉ monoid**ᵉ isᵉ aᵉ first–orderᵉ approximationᵉ to anᵉ ∞-monoid,ᵉ i.e.ᵉ aᵉ
∞-monoid-likeᵉ structureᵉ whoseᵉ lawsᵉ holdᵉ atᵉ leastᵉ upᵉ to theᵉ firstᵉ homotopyᵉ level,ᵉ
butᵉ mayᵉ failᵉ atᵉ higherᵉ levels.ᵉ

Aᵉ wildᵉ monoidᵉ consistsᵉ ofᵉ

-ᵉ anᵉ underlyingᵉ typeᵉ `A`ᵉ
-ᵉ aᵉ unit,ᵉ sayᵉ `eᵉ : A`ᵉ
-ᵉ aᵉ binaryᵉ operationᵉ onᵉ `A`,ᵉ sayᵉ `_*_`ᵉ
-ᵉ leftᵉ andᵉ rightᵉ unitᵉ lawsᵉ `eᵉ *ᵉ xᵉ ＝ᵉ x`ᵉ andᵉ `xᵉ *ᵉ eᵉ ＝ᵉ x`ᵉ
-ᵉ aᵉ coherenceᵉ betweenᵉ theᵉ leftᵉ andᵉ rightᵉ unitᵉ lawsᵉ atᵉ theᵉ unitᵉ
-ᵉ anᵉ associatorᵉ `(xᵉ yᵉ zᵉ : Aᵉ) → (xᵉ *ᵉ yᵉ) *ᵉ zᵉ ＝ᵉ xᵉ *ᵉ (yᵉ *ᵉ z)`ᵉ
-ᵉ coherencesᵉ betweenᵉ theᵉ associatorᵉ andᵉ theᵉ leftᵉ andᵉ rightᵉ unitᵉ lawsᵉ

Weᵉ callᵉ suchᵉ anᵉ associatorᵉ **unital**.ᵉ Itᵉ mayᵉ beᵉ describedᵉ asᵉ aᵉ coherenceᵉ ofᵉ theᵉ
followingᵉ diagramᵉ

```text
          map-associative-productᵉ
     (Aᵉ ×ᵉ Aᵉ) ×ᵉ Aᵉ ---->ᵉ Aᵉ ×ᵉ (Aᵉ ×ᵉ Aᵉ)
             |           |
  (_*ᵉ_ ,ᵉ idᵉ) |           | (id,ᵉ _*ᵉ_)
             ∨ᵉ           ∨ᵉ
           Aᵉ ×ᵉ Aᵉ       Aᵉ ×ᵉ Aᵉ
               \ᵉ       /ᵉ
          (_*ᵉ_) \ᵉ     /ᵉ (_*ᵉ_)
                 ∨ᵉ   ∨ᵉ
                   Aᵉ
```

suchᵉ thatᵉ theᵉ threeᵉ diagramsᵉ belowᵉ cohereᵉ

```text
            associatorᵉ
  (eᵉ *ᵉ xᵉ) *ᵉ yᵉ =====ᵉ eᵉ *ᵉ (xᵉ *ᵉ yᵉ)
          \\ᵉ         //ᵉ
     leftᵉ  \\ᵉ       //ᵉ  leftᵉ
   unitᵉ lawᵉ \\ᵉ     //ᵉ unitᵉ lawᵉ
              yᵉ *ᵉ z,ᵉ
```

```text
            associatorᵉ
  (xᵉ *ᵉ eᵉ) *ᵉ yᵉ =====ᵉ xᵉ *ᵉ (eᵉ *ᵉ yᵉ)
          \\ᵉ         //ᵉ
    rightᵉ  \\ᵉ       //ᵉ  leftᵉ
   unitᵉ lawᵉ \\ᵉ     //ᵉ unitᵉ lawᵉ
              xᵉ *ᵉ y,ᵉ
```

andᵉ

```text
            associatorᵉ
  (xᵉ *ᵉ yᵉ) *ᵉ eᵉ =====ᵉ xᵉ *ᵉ (yᵉ *ᵉ eᵉ)
          \\ᵉ         //ᵉ
    rightᵉ  \\ᵉ       //ᵉ  rightᵉ
   unitᵉ lawᵉ \\ᵉ     //ᵉ unitᵉ lawᵉ
              xᵉ *ᵉ yᵉ
```

forᵉ allᵉ `xᵉ yᵉ : A`.ᵉ

Concretely,ᵉ weᵉ defineᵉ wildᵉ monoidsᵉ to beᵉ
[H-spaces](structured-types.h-spaces.mdᵉ) equippedᵉ with aᵉ unitalᵉ associator.ᵉ

## Definition

### Unital associators on H-spaces

```agda
module _
  {lᵉ : Level} (Mᵉ : H-Spaceᵉ lᵉ)
  where

  associator-H-Spaceᵉ : UUᵉ lᵉ
  associator-H-Spaceᵉ =
    (xᵉ yᵉ zᵉ : type-H-Spaceᵉ Mᵉ) →
    Idᵉ
      ( mul-H-Spaceᵉ Mᵉ (mul-H-Spaceᵉ Mᵉ xᵉ yᵉ) zᵉ)
      ( mul-H-Spaceᵉ Mᵉ xᵉ (mul-H-Spaceᵉ Mᵉ yᵉ zᵉ))

  is-unital-associatorᵉ : (αᵉ : associator-H-Spaceᵉ) → UUᵉ lᵉ
  is-unital-associatorᵉ α111ᵉ =
    Σᵉ ( (yᵉ zᵉ : type-H-Spaceᵉ Mᵉ) →
        Idᵉ
          ( ( α111ᵉ (unit-H-Spaceᵉ Mᵉ) yᵉ zᵉ) ∙ᵉ
            ( left-unit-law-mul-H-Spaceᵉ Mᵉ
              ( mul-H-Spaceᵉ Mᵉ yᵉ zᵉ)))
            ( apᵉ
              ( mul-H-Space'ᵉ Mᵉ zᵉ)
              ( left-unit-law-mul-H-Spaceᵉ Mᵉ yᵉ)))
      ( λ α011ᵉ →
        Σᵉ ( (xᵉ zᵉ : type-H-Spaceᵉ Mᵉ) →
            Idᵉ
              ( ( α111ᵉ xᵉ (unit-H-Spaceᵉ Mᵉ) zᵉ) ∙ᵉ
                ( apᵉ
                  ( mul-H-Spaceᵉ Mᵉ xᵉ)
                  ( left-unit-law-mul-H-Spaceᵉ Mᵉ zᵉ)))
              ( apᵉ
                ( mul-H-Space'ᵉ Mᵉ zᵉ)
                ( right-unit-law-mul-H-Spaceᵉ Mᵉ xᵉ)))
          ( λ α101ᵉ →
            Σᵉ ( (xᵉ yᵉ : type-H-Spaceᵉ Mᵉ) →
                Idᵉ
                  ( ( α111ᵉ xᵉ yᵉ (unit-H-Spaceᵉ Mᵉ)) ∙ᵉ
                    ( apᵉ
                      ( mul-H-Spaceᵉ Mᵉ xᵉ)
                      ( right-unit-law-mul-H-Spaceᵉ Mᵉ yᵉ)))
                  ( right-unit-law-mul-H-Spaceᵉ Mᵉ
                    ( mul-H-Spaceᵉ Mᵉ xᵉ yᵉ)))
              ( λ α110ᵉ → unitᵉ)))

  unital-associatorᵉ : UUᵉ lᵉ
  unital-associatorᵉ = Σᵉ (associator-H-Spaceᵉ) (is-unital-associatorᵉ)
```

### Wild monoids

```agda
Wild-Monoidᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Wild-Monoidᵉ lᵉ =
  Σᵉ (H-Spaceᵉ lᵉ) unital-associatorᵉ

module _
  {lᵉ : Level} (Mᵉ : Wild-Monoidᵉ lᵉ)
  where

  h-space-Wild-Monoidᵉ : H-Spaceᵉ lᵉ
  h-space-Wild-Monoidᵉ = pr1ᵉ Mᵉ

  type-Wild-Monoidᵉ : UUᵉ lᵉ
  type-Wild-Monoidᵉ = type-H-Spaceᵉ h-space-Wild-Monoidᵉ

  unit-Wild-Monoidᵉ : type-Wild-Monoidᵉ
  unit-Wild-Monoidᵉ = unit-H-Spaceᵉ h-space-Wild-Monoidᵉ

  pointed-type-Wild-Monoidᵉ : Pointed-Typeᵉ lᵉ
  pointed-type-Wild-Monoidᵉ =
    pointed-type-H-Spaceᵉ h-space-Wild-Monoidᵉ

  coherent-unital-mul-Wild-Monoidᵉ :
    coherent-unital-mul-Pointed-Typeᵉ pointed-type-Wild-Monoidᵉ
  coherent-unital-mul-Wild-Monoidᵉ =
    coherent-unital-mul-H-Spaceᵉ h-space-Wild-Monoidᵉ

  mul-Wild-Monoidᵉ : type-Wild-Monoidᵉ → type-Wild-Monoidᵉ → type-Wild-Monoidᵉ
  mul-Wild-Monoidᵉ = mul-H-Spaceᵉ h-space-Wild-Monoidᵉ

  mul-Wild-Monoid'ᵉ : type-Wild-Monoidᵉ → type-Wild-Monoidᵉ → type-Wild-Monoidᵉ
  mul-Wild-Monoid'ᵉ = mul-H-Space'ᵉ h-space-Wild-Monoidᵉ

  ap-mul-Wild-Monoidᵉ :
    {aᵉ bᵉ cᵉ dᵉ : type-Wild-Monoidᵉ} →
    aᵉ ＝ᵉ bᵉ → cᵉ ＝ᵉ dᵉ → mul-Wild-Monoidᵉ aᵉ cᵉ ＝ᵉ mul-Wild-Monoidᵉ bᵉ dᵉ
  ap-mul-Wild-Monoidᵉ = ap-mul-H-Spaceᵉ h-space-Wild-Monoidᵉ

  left-unit-law-mul-Wild-Monoidᵉ :
    (xᵉ : type-Wild-Monoidᵉ) → mul-Wild-Monoidᵉ unit-Wild-Monoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Wild-Monoidᵉ =
    left-unit-law-mul-H-Spaceᵉ h-space-Wild-Monoidᵉ

  right-unit-law-mul-Wild-Monoidᵉ :
    (xᵉ : type-Wild-Monoidᵉ) → mul-Wild-Monoidᵉ xᵉ unit-Wild-Monoidᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Wild-Monoidᵉ =
    right-unit-law-mul-H-Spaceᵉ h-space-Wild-Monoidᵉ

  coh-unit-laws-mul-Wild-Monoidᵉ :
    ( left-unit-law-mul-Wild-Monoidᵉ unit-Wild-Monoidᵉ) ＝ᵉ
    ( right-unit-law-mul-Wild-Monoidᵉ unit-Wild-Monoidᵉ)
  coh-unit-laws-mul-Wild-Monoidᵉ =
    coh-unit-laws-mul-H-Spaceᵉ h-space-Wild-Monoidᵉ

  unital-associator-Wild-Monoidᵉ :
    unital-associatorᵉ h-space-Wild-Monoidᵉ
  unital-associator-Wild-Monoidᵉ = pr2ᵉ Mᵉ

  associator-Wild-Monoidᵉ :
    associator-H-Spaceᵉ h-space-Wild-Monoidᵉ
  associator-Wild-Monoidᵉ = pr1ᵉ unital-associator-Wild-Monoidᵉ

  associative-mul-Wild-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Wild-Monoidᵉ) →
    ( mul-Wild-Monoidᵉ (mul-Wild-Monoidᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( mul-Wild-Monoidᵉ xᵉ (mul-Wild-Monoidᵉ yᵉ zᵉ))
  associative-mul-Wild-Monoidᵉ = pr1ᵉ unital-associator-Wild-Monoidᵉ

  unit-law-110-associative-Wild-Monoidᵉ :
    (xᵉ yᵉ : type-Wild-Monoidᵉ) →
    Idᵉ
      ( ( associative-mul-Wild-Monoidᵉ xᵉ yᵉ unit-Wild-Monoidᵉ) ∙ᵉ
        ( apᵉ (mul-Wild-Monoidᵉ xᵉ) (right-unit-law-mul-Wild-Monoidᵉ yᵉ)))
      ( right-unit-law-mul-Wild-Monoidᵉ (mul-Wild-Monoidᵉ xᵉ yᵉ))
  unit-law-110-associative-Wild-Monoidᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Mᵉ))))
```
# Lifts of types

```agda
module foundation.lifts-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `X`.ᵉ Aᵉ {{#conceptᵉ "lift"ᵉ Disambiguation="type"ᵉ Agda=lift-typeᵉ}}
ofᵉ `X`ᵉ isᵉ anᵉ objectᵉ in theᵉ [slice](foundation.slice.mdᵉ) overᵉ `X`,ᵉ i.e.,ᵉ itᵉ
consistsᵉ ofᵉ aᵉ typeᵉ `Y`ᵉ andᵉ aᵉ mapᵉ `fᵉ : Yᵉ → X`.ᵉ

Inᵉ theᵉ aboveᵉ definitionᵉ ofᵉ liftsᵉ ofᵉ typesᵉ ourᵉ aimᵉ isᵉ to captureᵉ theᵉ mostᵉ generalᵉ
conceptᵉ ofᵉ whatᵉ itᵉ meansᵉ to beᵉ anᵉ liftᵉ ofᵉ aᵉ type.ᵉ Similarly,ᵉ in anyᵉ
[category](category-theory.categories.mdᵉ) weᵉ wouldᵉ sayᵉ thatᵉ anᵉ liftᵉ ofᵉ anᵉ objectᵉ
`X`ᵉ consistsᵉ ofᵉ anᵉ objectᵉ `Y`ᵉ equippedᵉ with aᵉ morphismᵉ `fᵉ : Yᵉ → X`.ᵉ

## Definitions

```agda
lift-typeᵉ : {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
lift-typeᵉ l2ᵉ Xᵉ = Σᵉ (UUᵉ l2ᵉ) (λ Yᵉ → Yᵉ → Xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ : lift-typeᵉ l2ᵉ Xᵉ)
  where

  type-lift-typeᵉ : UUᵉ l2ᵉ
  type-lift-typeᵉ = pr1ᵉ Yᵉ

  projection-lift-typeᵉ : type-lift-typeᵉ → Xᵉ
  projection-lift-typeᵉ = pr2ᵉ Yᵉ
```
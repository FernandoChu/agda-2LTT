# Extensions of types

```agda
module foundation.extensions-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `X`.ᵉ Anᵉ
{{#conceptᵉ "extension"ᵉ Disambiguation="type"ᵉ Agda=extension-typeᵉ}} ofᵉ `X`ᵉ isᵉ anᵉ
objectᵉ in theᵉ [coslice](foundation.coslice.mdᵉ) underᵉ `X`,ᵉ i.e.,ᵉ itᵉ consistsᵉ ofᵉ aᵉ
typeᵉ `Y`ᵉ andᵉ aᵉ mapᵉ `fᵉ : Xᵉ → Y`.ᵉ

Inᵉ theᵉ aboveᵉ definitionᵉ ofᵉ extensionsᵉ ofᵉ typesᵉ ourᵉ aimᵉ isᵉ to captureᵉ theᵉ mostᵉ
generalᵉ conceptᵉ ofᵉ whatᵉ itᵉ meansᵉ to beᵉ anᵉ extensionᵉ ofᵉ aᵉ type.ᵉ Similarly,ᵉ in anyᵉ
[category](category-theory.categories.mdᵉ) weᵉ wouldᵉ sayᵉ thatᵉ anᵉ extensionᵉ ofᵉ anᵉ
objectᵉ `X`ᵉ consistsᵉ ofᵉ anᵉ objectᵉ `Y`ᵉ equippedᵉ with aᵉ morphismᵉ `fᵉ : Xᵉ → Y`.ᵉ

Ourᵉ notionᵉ ofᵉ extensionsᵉ ofᵉ typesᵉ areᵉ notᵉ to beᵉ confusedᵉ with extensionᵉ typesᵉ ofᵉ
cubicalᵉ typeᵉ theoryᵉ orᵉ
[extensionᵉ typesᵉ ofᵉ simplicialᵉ typeᵉ theory](https://arxiv.org/abs/1705.07442).ᵉ

## Definitions

### Extensions of types

```agda
extension-typeᵉ : {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
extension-typeᵉ l2ᵉ Xᵉ = Σᵉ (UUᵉ l2ᵉ) (λ Yᵉ → Xᵉ → Yᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ : extension-typeᵉ l2ᵉ Xᵉ)
  where

  type-extension-typeᵉ : UUᵉ l2ᵉ
  type-extension-typeᵉ = pr1ᵉ Yᵉ

  inclusion-extension-typeᵉ : Xᵉ → type-extension-typeᵉ
  inclusion-extension-typeᵉ = pr2ᵉ Yᵉ
```
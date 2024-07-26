# Reversing lists

```agda
module lists.reversing-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import lists.concatenation-listsᵉ
open import lists.flattening-listsᵉ
open import lists.functoriality-listsᵉ
open import lists.listsᵉ
```

</details>

## Idea

Theᵉ reverseᵉ ofᵉ aᵉ listᵉ ofᵉ elementsᵉ in `A`ᵉ listsᵉ theᵉ elementsᵉ ofᵉ `A`ᵉ in theᵉ
reversedᵉ order.ᵉ

## Definition

```agda
reverse-listᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → listᵉ Aᵉ
reverse-listᵉ nilᵉ = nilᵉ
reverse-listᵉ (consᵉ aᵉ lᵉ) = snocᵉ (reverse-listᵉ lᵉ) aᵉ
```

## Properties

```agda
reverse-unit-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) →
  Idᵉ (reverse-listᵉ (unit-listᵉ aᵉ)) (unit-listᵉ aᵉ)
reverse-unit-listᵉ aᵉ = reflᵉ

length-snoc-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) (aᵉ : Aᵉ) →
  length-listᵉ (snocᵉ xᵉ aᵉ) ＝ᵉ succ-ℕᵉ (length-listᵉ xᵉ)
length-snoc-listᵉ nilᵉ aᵉ = reflᵉ
length-snoc-listᵉ (consᵉ bᵉ xᵉ) aᵉ = apᵉ succ-ℕᵉ (length-snoc-listᵉ xᵉ aᵉ)

length-reverse-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (length-listᵉ (reverse-listᵉ xᵉ)) (length-listᵉ xᵉ)
length-reverse-listᵉ nilᵉ = reflᵉ
length-reverse-listᵉ (consᵉ aᵉ xᵉ) =
  ( length-snoc-listᵉ (reverse-listᵉ xᵉ) aᵉ) ∙ᵉ
  ( apᵉ succ-ℕᵉ (length-reverse-listᵉ xᵉ))

reverse-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Aᵉ) →
  Idᵉ
    ( reverse-listᵉ (concat-listᵉ xᵉ yᵉ))
    ( concat-listᵉ (reverse-listᵉ yᵉ) (reverse-listᵉ xᵉ))
reverse-concat-listᵉ nilᵉ yᵉ =
  invᵉ (right-unit-law-concat-listᵉ (reverse-listᵉ yᵉ))
reverse-concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ =
  ( apᵉ (λ tᵉ → snocᵉ tᵉ aᵉ) (reverse-concat-listᵉ xᵉ yᵉ)) ∙ᵉ
  ( ( snoc-concat-listᵉ (reverse-listᵉ yᵉ) (reverse-listᵉ xᵉ) aᵉ))

reverse-snoc-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) (aᵉ : Aᵉ) →
  reverse-listᵉ (snocᵉ xᵉ aᵉ) ＝ᵉ consᵉ aᵉ (reverse-listᵉ xᵉ)
reverse-snoc-listᵉ nilᵉ aᵉ = reflᵉ
reverse-snoc-listᵉ (consᵉ bᵉ xᵉ) aᵉ = apᵉ (λ tᵉ → snocᵉ tᵉ bᵉ) (reverse-snoc-listᵉ xᵉ aᵉ)

reverse-flatten-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ (listᵉ Aᵉ)) →
  Idᵉ
    ( reverse-listᵉ (flatten-listᵉ xᵉ))
    ( flatten-listᵉ (reverse-listᵉ (map-listᵉ reverse-listᵉ xᵉ)))
reverse-flatten-listᵉ nilᵉ = reflᵉ
reverse-flatten-listᵉ (consᵉ aᵉ xᵉ) =
  ( reverse-concat-listᵉ aᵉ (flatten-listᵉ xᵉ)) ∙ᵉ
  ( ( apᵉ (λ tᵉ → concat-listᵉ tᵉ (reverse-listᵉ aᵉ)) (reverse-flatten-listᵉ xᵉ)) ∙ᵉ
    ( invᵉ
      ( flatten-snoc-listᵉ
        ( reverse-listᵉ (map-listᵉ reverse-listᵉ xᵉ))
        ( (reverse-listᵉ aᵉ)))))

reverse-reverse-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (reverse-listᵉ (reverse-listᵉ xᵉ)) xᵉ
reverse-reverse-listᵉ nilᵉ = reflᵉ
reverse-reverse-listᵉ (consᵉ aᵉ xᵉ) =
  ( reverse-snoc-listᵉ (reverse-listᵉ xᵉ) aᵉ) ∙ᵉ
  ( apᵉ (consᵉ aᵉ) (reverse-reverse-listᵉ xᵉ))
```

```agda
head-reverse-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  head-listᵉ (reverse-listᵉ xᵉ) ＝ᵉ last-element-listᵉ xᵉ
head-reverse-listᵉ nilᵉ = reflᵉ
head-reverse-listᵉ (consᵉ aᵉ nilᵉ) = reflᵉ
head-reverse-listᵉ (consᵉ aᵉ (consᵉ bᵉ xᵉ)) =
  ( head-snoc-snoc-listᵉ (reverse-listᵉ xᵉ) bᵉ aᵉ) ∙ᵉ
  ( head-reverse-listᵉ (consᵉ bᵉ xᵉ))

last-element-reverse-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (last-element-listᵉ (reverse-listᵉ xᵉ)) (head-listᵉ xᵉ)
last-element-reverse-listᵉ xᵉ =
  ( invᵉ (head-reverse-listᵉ (reverse-listᵉ xᵉ))) ∙ᵉ
  ( apᵉ head-listᵉ (reverse-reverse-listᵉ xᵉ))

tail-reverse-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (tail-listᵉ (reverse-listᵉ xᵉ)) (reverse-listᵉ (remove-last-element-listᵉ xᵉ))
tail-reverse-listᵉ nilᵉ = reflᵉ
tail-reverse-listᵉ (consᵉ aᵉ nilᵉ) = reflᵉ
tail-reverse-listᵉ (consᵉ aᵉ (consᵉ bᵉ xᵉ)) =
  ( tail-snoc-snoc-listᵉ (reverse-listᵉ xᵉ) bᵉ aᵉ) ∙ᵉ
  ( apᵉ (λ tᵉ → snocᵉ tᵉ aᵉ) (tail-reverse-listᵉ (consᵉ bᵉ xᵉ)))

remove-last-element-reverse-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (remove-last-element-listᵉ (reverse-listᵉ xᵉ)) (reverse-listᵉ (tail-listᵉ xᵉ))
remove-last-element-reverse-listᵉ xᵉ =
  ( invᵉ (reverse-reverse-listᵉ (remove-last-element-listᵉ (reverse-listᵉ xᵉ)))) ∙ᵉ
  ( ( invᵉ (apᵉ reverse-listᵉ (tail-reverse-listᵉ (reverse-listᵉ xᵉ)))) ∙ᵉ
    ( apᵉ (reverse-listᵉ ∘ᵉ tail-listᵉ) (reverse-reverse-listᵉ xᵉ)))
```
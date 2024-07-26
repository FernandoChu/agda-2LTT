# Concatenation of lists

```agda
module lists.concatenation-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ

open import lists.listsᵉ
```

</details>

## Idea

Twoᵉ listsᵉ canᵉ beᵉ concatenatedᵉ to formᵉ aᵉ singleᵉ list.ᵉ

## Definition

```agda
concat-listᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → (listᵉ Aᵉ → listᵉ Aᵉ)
concat-listᵉ {lᵉ} {Aᵉ} = fold-listᵉ idᵉ (λ aᵉ fᵉ → (consᵉ aᵉ) ∘ᵉ fᵉ)
```

## Properties

### List concatenation is associative and unital

Concatenationᵉ ofᵉ listsᵉ isᵉ anᵉ associativeᵉ operationᵉ andᵉ nilᵉ isᵉ theᵉ unitᵉ forᵉ listᵉ
concatenation.ᵉ

```agda
associative-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ zᵉ : listᵉ Aᵉ) →
  Idᵉ (concat-listᵉ (concat-listᵉ xᵉ yᵉ) zᵉ) (concat-listᵉ xᵉ (concat-listᵉ yᵉ zᵉ))
associative-concat-listᵉ nilᵉ yᵉ zᵉ = reflᵉ
associative-concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ zᵉ =
  apᵉ (consᵉ aᵉ) (associative-concat-listᵉ xᵉ yᵉ zᵉ)

left-unit-law-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (concat-listᵉ nilᵉ xᵉ) xᵉ
left-unit-law-concat-listᵉ xᵉ = reflᵉ

right-unit-law-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (concat-listᵉ xᵉ nilᵉ) xᵉ
right-unit-law-concat-listᵉ nilᵉ = reflᵉ
right-unit-law-concat-listᵉ (consᵉ aᵉ xᵉ) =
  apᵉ (consᵉ aᵉ) (right-unit-law-concat-listᵉ xᵉ)

list-Monoidᵉ : {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → Monoidᵉ lᵉ
list-Monoidᵉ Xᵉ =
  pairᵉ
    ( pairᵉ (list-Setᵉ Xᵉ) (pairᵉ concat-listᵉ associative-concat-listᵉ))
    ( pairᵉ nilᵉ (pairᵉ left-unit-law-concat-listᵉ right-unit-law-concat-listᵉ))
```

### `snoc`-law for list concatenation

```agda
snoc-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Aᵉ) (aᵉ : Aᵉ) →
  snocᵉ (concat-listᵉ xᵉ yᵉ) aᵉ ＝ᵉ concat-listᵉ xᵉ (snocᵉ yᵉ aᵉ)
snoc-concat-listᵉ nilᵉ yᵉ aᵉ = reflᵉ
snoc-concat-listᵉ (consᵉ bᵉ xᵉ) yᵉ aᵉ = apᵉ (consᵉ bᵉ) (snoc-concat-listᵉ xᵉ yᵉ aᵉ)
```

### The length of a concatenation of two lists is the sum of the length of the two lists

```agda
length-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Aᵉ) →
  Idᵉ (length-listᵉ (concat-listᵉ xᵉ yᵉ)) ((length-listᵉ xᵉ) +ℕᵉ (length-listᵉ yᵉ))
length-concat-listᵉ nilᵉ yᵉ = invᵉ (left-unit-law-add-ℕᵉ (length-listᵉ yᵉ))
length-concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ =
  ( apᵉ succ-ℕᵉ (length-concat-listᵉ xᵉ yᵉ)) ∙ᵉ
  ( invᵉ (left-successor-law-add-ℕᵉ (length-listᵉ xᵉ) (length-listᵉ yᵉ)))
```

### An `η`-rule for lists

```agda
eta-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (concat-listᵉ (head-listᵉ xᵉ) (tail-listᵉ xᵉ)) xᵉ
eta-listᵉ nilᵉ = reflᵉ
eta-listᵉ (consᵉ aᵉ xᵉ) = reflᵉ

eta-list'ᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (concat-listᵉ (remove-last-element-listᵉ xᵉ) (last-element-listᵉ xᵉ)) xᵉ
eta-list'ᵉ nilᵉ = reflᵉ
eta-list'ᵉ (consᵉ aᵉ nilᵉ) = reflᵉ
eta-list'ᵉ (consᵉ aᵉ (consᵉ bᵉ xᵉ)) = apᵉ (consᵉ aᵉ) (eta-list'ᵉ (consᵉ bᵉ xᵉ))
```

### Heads and tails of concatenated lists

```agda
head-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Aᵉ) →
  Idᵉ
    ( head-listᵉ (concat-listᵉ xᵉ yᵉ))
    ( head-listᵉ (concat-listᵉ (head-listᵉ xᵉ) (head-listᵉ yᵉ)))
head-concat-listᵉ nilᵉ nilᵉ = reflᵉ
head-concat-listᵉ nilᵉ (consᵉ xᵉ yᵉ) = reflᵉ
head-concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ = reflᵉ

tail-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Aᵉ) →
  Idᵉ
    ( tail-listᵉ (concat-listᵉ xᵉ yᵉ))
    ( concat-listᵉ (tail-listᵉ xᵉ) (tail-listᵉ (concat-listᵉ (head-listᵉ xᵉ) yᵉ)))
tail-concat-listᵉ nilᵉ yᵉ = reflᵉ
tail-concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ = reflᵉ

last-element-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Aᵉ) →
  Idᵉ
    ( last-element-listᵉ (concat-listᵉ xᵉ yᵉ))
    ( last-element-listᵉ
      ( concat-listᵉ (last-element-listᵉ xᵉ) (last-element-listᵉ yᵉ)))
last-element-concat-listᵉ nilᵉ nilᵉ = reflᵉ
last-element-concat-listᵉ nilᵉ (consᵉ bᵉ nilᵉ) = reflᵉ
last-element-concat-listᵉ nilᵉ (consᵉ bᵉ (consᵉ cᵉ yᵉ)) =
  last-element-concat-listᵉ nilᵉ (consᵉ cᵉ yᵉ)
last-element-concat-listᵉ (consᵉ aᵉ nilᵉ) nilᵉ = reflᵉ
last-element-concat-listᵉ (consᵉ aᵉ nilᵉ) (consᵉ bᵉ nilᵉ) = reflᵉ
last-element-concat-listᵉ (consᵉ aᵉ nilᵉ) (consᵉ bᵉ (consᵉ cᵉ yᵉ)) =
  last-element-concat-listᵉ (consᵉ aᵉ nilᵉ) (consᵉ cᵉ yᵉ)
last-element-concat-listᵉ (consᵉ aᵉ (consᵉ bᵉ xᵉ)) yᵉ =
  last-element-concat-listᵉ (consᵉ bᵉ xᵉ) yᵉ

remove-last-element-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Aᵉ) →
  Idᵉ
    ( remove-last-element-listᵉ (concat-listᵉ xᵉ yᵉ))
    ( concat-listᵉ
      ( remove-last-element-listᵉ (concat-listᵉ xᵉ (head-listᵉ yᵉ)))
      ( remove-last-element-listᵉ yᵉ))
remove-last-element-concat-listᵉ nilᵉ nilᵉ = reflᵉ
remove-last-element-concat-listᵉ nilᵉ (consᵉ aᵉ nilᵉ) = reflᵉ
remove-last-element-concat-listᵉ nilᵉ (consᵉ aᵉ (consᵉ bᵉ yᵉ)) = reflᵉ
remove-last-element-concat-listᵉ (consᵉ aᵉ nilᵉ) nilᵉ = reflᵉ
remove-last-element-concat-listᵉ (consᵉ aᵉ nilᵉ) (consᵉ bᵉ yᵉ) = reflᵉ
remove-last-element-concat-listᵉ (consᵉ aᵉ (consᵉ bᵉ xᵉ)) yᵉ =
  apᵉ (consᵉ aᵉ) (remove-last-element-concat-listᵉ (consᵉ bᵉ xᵉ) yᵉ)

tail-concat-list'ᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Aᵉ) →
  Idᵉ
    ( tail-listᵉ (concat-listᵉ xᵉ yᵉ))
    ( concat-listᵉ
      ( tail-listᵉ xᵉ)
      ( tail-listᵉ (concat-listᵉ (last-element-listᵉ xᵉ) yᵉ)))
tail-concat-list'ᵉ nilᵉ yᵉ = reflᵉ
tail-concat-list'ᵉ (consᵉ aᵉ nilᵉ) yᵉ = reflᵉ
tail-concat-list'ᵉ (consᵉ aᵉ (consᵉ bᵉ xᵉ)) yᵉ =
  apᵉ (consᵉ bᵉ) (tail-concat-list'ᵉ (consᵉ bᵉ xᵉ) yᵉ)
```
# Flattening of lists

```agda
module lists.flattening-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.sums-of-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import lists.concatenation-listsᵉ
open import lists.functoriality-listsᵉ
open import lists.listsᵉ
```

</details>

## Idea

Anyᵉ listᵉ ofᵉ listsᵉ ofᵉ elementsᵉ ofᵉ `A`ᵉ canᵉ beᵉ flattenedᵉ to formᵉ aᵉ listᵉ ofᵉ elementsᵉ
ofᵉ `A`ᵉ

## Definition

```agda
flatten-listᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ (listᵉ Aᵉ) → listᵉ Aᵉ
flatten-listᵉ = fold-listᵉ nilᵉ concat-listᵉ
```

## Properties

### Properties of flattening

```agda
flatten-unit-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) →
  Idᵉ (flatten-listᵉ (unit-listᵉ xᵉ)) xᵉ
flatten-unit-listᵉ xᵉ = right-unit-law-concat-listᵉ xᵉ

length-flatten-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ (listᵉ Aᵉ)) →
  Idᵉ
    ( length-listᵉ (flatten-listᵉ xᵉ))
    ( sum-list-ℕᵉ (map-listᵉ length-listᵉ xᵉ))
length-flatten-listᵉ nilᵉ = reflᵉ
length-flatten-listᵉ (consᵉ aᵉ xᵉ) =
  ( length-concat-listᵉ aᵉ (flatten-listᵉ xᵉ)) ∙ᵉ
  ( apᵉ ((length-listᵉ aᵉ) +ℕᵉ_) (length-flatten-listᵉ xᵉ))

flatten-concat-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ (listᵉ Aᵉ)) →
  Idᵉ
    ( flatten-listᵉ (concat-listᵉ xᵉ yᵉ))
    ( concat-listᵉ (flatten-listᵉ xᵉ) (flatten-listᵉ yᵉ))
flatten-concat-listᵉ nilᵉ yᵉ = reflᵉ
flatten-concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ =
  ( apᵉ (concat-listᵉ aᵉ) (flatten-concat-listᵉ xᵉ yᵉ)) ∙ᵉ
  ( invᵉ (associative-concat-listᵉ aᵉ (flatten-listᵉ xᵉ) (flatten-listᵉ yᵉ)))

flatten-flatten-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ (listᵉ (listᵉ Aᵉ))) →
  Idᵉ
    ( flatten-listᵉ (flatten-listᵉ xᵉ))
    ( flatten-listᵉ (map-listᵉ flatten-listᵉ xᵉ))
flatten-flatten-listᵉ nilᵉ = reflᵉ
flatten-flatten-listᵉ (consᵉ aᵉ xᵉ) =
  ( flatten-concat-listᵉ aᵉ (flatten-listᵉ xᵉ)) ∙ᵉ
  ( apᵉ (concat-listᵉ (flatten-listᵉ aᵉ)) (flatten-flatten-listᵉ xᵉ))

flatten-snoc-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ (listᵉ Aᵉ)) (aᵉ : listᵉ Aᵉ) →
  flatten-listᵉ (snocᵉ xᵉ aᵉ) ＝ᵉ concat-listᵉ (flatten-listᵉ xᵉ) aᵉ
flatten-snoc-listᵉ nilᵉ aᵉ = right-unit-law-concat-listᵉ aᵉ
flatten-snoc-listᵉ (consᵉ bᵉ xᵉ) aᵉ =
  ( apᵉ (concat-listᵉ bᵉ) (flatten-snoc-listᵉ xᵉ aᵉ)) ∙ᵉ
  ( invᵉ (associative-concat-listᵉ bᵉ (flatten-listᵉ xᵉ) aᵉ))
```
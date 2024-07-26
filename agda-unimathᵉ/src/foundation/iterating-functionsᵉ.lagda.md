# Iterating functions

```agda
module foundation.iterating-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.exponentiation-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.multiplicative-monoid-of-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.endomorphismsᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.setsᵉ

open import group-theory.monoid-actionsᵉ
```

</details>

## Idea

Anyᵉ mapᵉ `fᵉ : Xᵉ → X`ᵉ canᵉ beᵉ iteratedᵉ byᵉ repeatedlyᵉ applyingᵉ `f`ᵉ

## Definition

### Iterating functions

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterateᵉ : ℕᵉ → (Xᵉ → Xᵉ) → (Xᵉ → Xᵉ)
  iterateᵉ zero-ℕᵉ fᵉ xᵉ = xᵉ
  iterateᵉ (succ-ℕᵉ kᵉ) fᵉ xᵉ = fᵉ (iterateᵉ kᵉ fᵉ xᵉ)

  iterate'ᵉ : ℕᵉ → (Xᵉ → Xᵉ) → (Xᵉ → Xᵉ)
  iterate'ᵉ zero-ℕᵉ fᵉ xᵉ = xᵉ
  iterate'ᵉ (succ-ℕᵉ kᵉ) fᵉ xᵉ = iterate'ᵉ kᵉ fᵉ (fᵉ xᵉ)
```

### Homotopies of iterating functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (sᵉ : Aᵉ → Aᵉ) (tᵉ : Bᵉ → Bᵉ)
  where

  coherence-square-iterateᵉ :
    {fᵉ : Aᵉ → Bᵉ} (Hᵉ : coherence-square-mapsᵉ fᵉ sᵉ tᵉ fᵉ) →
    (nᵉ : ℕᵉ) → coherence-square-mapsᵉ fᵉ (iterateᵉ nᵉ sᵉ) (iterateᵉ nᵉ tᵉ) fᵉ
  coherence-square-iterateᵉ {fᵉ} Hᵉ zero-ℕᵉ xᵉ = reflᵉ
  coherence-square-iterateᵉ {fᵉ} Hᵉ (succ-ℕᵉ nᵉ) =
    pasting-vertical-coherence-square-mapsᵉ
      ( fᵉ)
      ( iterateᵉ nᵉ sᵉ)
      ( iterateᵉ nᵉ tᵉ)
      ( fᵉ)
      ( sᵉ)
      ( tᵉ)
      ( fᵉ)
      ( coherence-square-iterateᵉ Hᵉ nᵉ)
      ( Hᵉ)
```

## Properties

### The two definitions of iterating are homotopic

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-succ-ℕᵉ :
    (kᵉ : ℕᵉ) (fᵉ : Xᵉ → Xᵉ) (xᵉ : Xᵉ) → iterateᵉ (succ-ℕᵉ kᵉ) fᵉ xᵉ ＝ᵉ iterateᵉ kᵉ fᵉ (fᵉ xᵉ)
  iterate-succ-ℕᵉ zero-ℕᵉ fᵉ xᵉ = reflᵉ
  iterate-succ-ℕᵉ (succ-ℕᵉ kᵉ) fᵉ xᵉ = apᵉ fᵉ (iterate-succ-ℕᵉ kᵉ fᵉ xᵉ)

  reassociate-iterateᵉ : (kᵉ : ℕᵉ) (fᵉ : Xᵉ → Xᵉ) → iterateᵉ kᵉ fᵉ ~ᵉ iterate'ᵉ kᵉ fᵉ
  reassociate-iterateᵉ zero-ℕᵉ fᵉ xᵉ = reflᵉ
  reassociate-iterateᵉ (succ-ℕᵉ kᵉ) fᵉ xᵉ =
    iterate-succ-ℕᵉ kᵉ fᵉ xᵉ ∙ᵉ reassociate-iterateᵉ kᵉ fᵉ (fᵉ xᵉ)
```

### For any map `f : X → X`, iterating `f` defines a monoid action of ℕ on `X`

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-add-ℕᵉ :
    (kᵉ lᵉ : ℕᵉ) (fᵉ : Xᵉ → Xᵉ) (xᵉ : Xᵉ) →
    iterateᵉ (kᵉ +ℕᵉ lᵉ) fᵉ xᵉ ＝ᵉ iterateᵉ kᵉ fᵉ (iterateᵉ lᵉ fᵉ xᵉ)
  iterate-add-ℕᵉ kᵉ zero-ℕᵉ fᵉ xᵉ = reflᵉ
  iterate-add-ℕᵉ kᵉ (succ-ℕᵉ lᵉ) fᵉ xᵉ =
    apᵉ fᵉ (iterate-add-ℕᵉ kᵉ lᵉ fᵉ xᵉ) ∙ᵉ iterate-succ-ℕᵉ kᵉ fᵉ (iterateᵉ lᵉ fᵉ xᵉ)

  left-unit-law-iterate-add-ℕᵉ :
    (lᵉ : ℕᵉ) (fᵉ : Xᵉ → Xᵉ) (xᵉ : Xᵉ) →
    iterate-add-ℕᵉ 0 lᵉ fᵉ xᵉ ＝ᵉ apᵉ (λ tᵉ → iterateᵉ tᵉ fᵉ xᵉ) (left-unit-law-add-ℕᵉ lᵉ)
  left-unit-law-iterate-add-ℕᵉ zero-ℕᵉ fᵉ xᵉ = reflᵉ
  left-unit-law-iterate-add-ℕᵉ (succ-ℕᵉ lᵉ) fᵉ xᵉ =
    ( right-unitᵉ) ∙ᵉ
    ( ( ap²ᵉ fᵉ (left-unit-law-iterate-add-ℕᵉ lᵉ fᵉ xᵉ)) ∙ᵉ
      ( ( invᵉ (ap-compᵉ fᵉ (λ tᵉ → iterateᵉ tᵉ fᵉ xᵉ) (left-unit-law-add-ℕᵉ lᵉ))) ∙ᵉ
        ( ap-compᵉ (λ tᵉ → iterateᵉ tᵉ fᵉ xᵉ) succ-ℕᵉ (left-unit-law-add-ℕᵉ lᵉ))))

  right-unit-law-iterate-add-ℕᵉ :
    (kᵉ : ℕᵉ) (fᵉ : Xᵉ → Xᵉ) (xᵉ : Xᵉ) →
    iterate-add-ℕᵉ kᵉ 0 fᵉ xᵉ ＝ᵉ apᵉ (λ tᵉ → iterateᵉ tᵉ fᵉ xᵉ) (right-unit-law-add-ℕᵉ kᵉ)
  right-unit-law-iterate-add-ℕᵉ kᵉ fᵉ xᵉ = reflᵉ

  iterate-iterateᵉ :
    (kᵉ lᵉ : ℕᵉ) (fᵉ : Xᵉ → Xᵉ) (xᵉ : Xᵉ) →
    iterateᵉ kᵉ fᵉ (iterateᵉ lᵉ fᵉ xᵉ) ＝ᵉ iterateᵉ lᵉ fᵉ (iterateᵉ kᵉ fᵉ xᵉ)
  iterate-iterateᵉ kᵉ lᵉ fᵉ xᵉ =
    ( invᵉ (iterate-add-ℕᵉ kᵉ lᵉ fᵉ xᵉ)) ∙ᵉ
    ( ( apᵉ (λ tᵉ → iterateᵉ tᵉ fᵉ xᵉ) (commutative-add-ℕᵉ kᵉ lᵉ)) ∙ᵉ
      ( iterate-add-ℕᵉ lᵉ kᵉ fᵉ xᵉ))

  iterate-mul-ℕᵉ :
    (kᵉ lᵉ : ℕᵉ) (fᵉ : Xᵉ → Xᵉ) (xᵉ : Xᵉ) →
    iterateᵉ (kᵉ *ℕᵉ lᵉ) fᵉ xᵉ ＝ᵉ iterateᵉ kᵉ (iterateᵉ lᵉ fᵉ) xᵉ
  iterate-mul-ℕᵉ zero-ℕᵉ lᵉ fᵉ xᵉ = reflᵉ
  iterate-mul-ℕᵉ (succ-ℕᵉ kᵉ) lᵉ fᵉ xᵉ =
    ( iterate-add-ℕᵉ (kᵉ *ℕᵉ lᵉ) lᵉ fᵉ xᵉ) ∙ᵉ
    ( ( iterate-mul-ℕᵉ kᵉ lᵉ fᵉ (iterateᵉ lᵉ fᵉ xᵉ)) ∙ᵉ
      ( invᵉ (iterate-succ-ℕᵉ kᵉ (iterateᵉ lᵉ fᵉ) xᵉ)))

  iterate-exp-ℕᵉ :
    (kᵉ lᵉ : ℕᵉ) (fᵉ : Xᵉ → Xᵉ) (xᵉ : Xᵉ) →
    iterateᵉ (exp-ℕᵉ lᵉ kᵉ) fᵉ xᵉ ＝ᵉ iterateᵉ kᵉ (iterateᵉ lᵉ) fᵉ xᵉ
  iterate-exp-ℕᵉ zero-ℕᵉ lᵉ fᵉ xᵉ = reflᵉ
  iterate-exp-ℕᵉ (succ-ℕᵉ kᵉ) lᵉ fᵉ xᵉ =
    ( iterate-mul-ℕᵉ (exp-ℕᵉ lᵉ kᵉ) lᵉ fᵉ xᵉ) ∙ᵉ
    ( ( iterate-exp-ℕᵉ kᵉ lᵉ (iterateᵉ lᵉ fᵉ) xᵉ) ∙ᵉ
      ( invᵉ (htpy-eqᵉ (iterate-succ-ℕᵉ kᵉ (iterateᵉ lᵉ) fᵉ) xᵉ)))

module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  iterative-action-Monoidᵉ : action-Monoidᵉ lᵉ ℕ*-Monoidᵉ
  pr1ᵉ iterative-action-Monoidᵉ = endo-Setᵉ Xᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ iterative-action-Monoidᵉ)) kᵉ fᵉ = iterateᵉ kᵉ fᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ iterative-action-Monoidᵉ)) {kᵉ} {lᵉ} =
    eq-htpyᵉ (λ fᵉ → eq-htpyᵉ (λ xᵉ → iterate-mul-ℕᵉ kᵉ lᵉ fᵉ xᵉ))
  pr2ᵉ (pr2ᵉ iterative-action-Monoidᵉ) = reflᵉ
```
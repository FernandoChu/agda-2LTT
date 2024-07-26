# Factorizations of maps into global function classes

```agda
module orthogonal-factorization-systems.factorizations-of-maps-global-function-classesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import orthogonal-factorization-systems.factorizations-of-mapsᵉ
open import orthogonal-factorization-systems.factorizations-of-maps-function-classesᵉ
open import orthogonal-factorization-systems.function-classesᵉ
open import orthogonal-factorization-systems.global-function-classesᵉ
```

</details>

## Idea

Aᵉ **factorizationᵉ intoᵉ
[globalᵉ functionᵉ classes](orthogonal-factorization-systems.global-function-classes.mdᵉ)
classesᵉ `L`ᵉ andᵉ `R`**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ pairᵉ ofᵉ mapsᵉ `lᵉ : Aᵉ → X`ᵉ andᵉ
`rᵉ : Xᵉ → B`,ᵉ where `lᵉ ∈ᵉ L`ᵉ andᵉ `rᵉ ∈ᵉ R`,ᵉ suchᵉ thatᵉ theirᵉ compositeᵉ `rᵉ ∘ᵉ l`ᵉ isᵉ
`f`.ᵉ

```text
         Xᵉ
        ∧ᵉ \ᵉ
 Lᵉ ∋ᵉ lᵉ /ᵉ   \ᵉ rᵉ ∈ᵉ Rᵉ
      /ᵉ     ∨ᵉ
    Aᵉ ----->ᵉ Bᵉ
        fᵉ
```

## Definitions

### The predicate of being a factorization into global function classes

```agda
module _
  {βLᵉ βRᵉ : Level → Level → Level}
  (Lᵉ : global-function-classᵉ βLᵉ)
  (Rᵉ : global-function-classᵉ βRᵉ)
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (Fᵉ : factorizationᵉ l3ᵉ fᵉ)
  where

  is-global-function-class-factorization-Propᵉ : Propᵉ (βLᵉ l1ᵉ l3ᵉ ⊔ βRᵉ l3ᵉ l2ᵉ)
  is-global-function-class-factorization-Propᵉ =
    is-function-class-factorization-Propᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)
      ( Fᵉ)

  is-global-function-class-factorizationᵉ : UUᵉ (βLᵉ l1ᵉ l3ᵉ ⊔ βRᵉ l3ᵉ l2ᵉ)
  is-global-function-class-factorizationᵉ =
    type-Propᵉ is-global-function-class-factorization-Propᵉ

  is-prop-is-global-function-class-factorizationᵉ :
    is-propᵉ is-global-function-class-factorizationᵉ
  is-prop-is-global-function-class-factorizationᵉ =
    is-prop-type-Propᵉ is-global-function-class-factorization-Propᵉ

  is-in-left-class-left-map-is-global-function-class-factorizationᵉ :
    is-global-function-class-factorizationᵉ →
    is-in-global-function-classᵉ Lᵉ (left-map-factorizationᵉ Fᵉ)
  is-in-left-class-left-map-is-global-function-class-factorizationᵉ =
    is-in-left-class-left-map-is-function-class-factorizationᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)
      ( Fᵉ)

  is-in-right-class-right-map-is-global-function-class-factorizationᵉ :
    is-global-function-class-factorizationᵉ →
    is-in-global-function-classᵉ Rᵉ (right-map-factorizationᵉ Fᵉ)
  is-in-right-class-right-map-is-global-function-class-factorizationᵉ =
    is-in-right-class-right-map-is-function-class-factorizationᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)
      ( Fᵉ)

  left-class-map-is-global-function-class-factorizationᵉ :
    is-global-function-class-factorizationᵉ →
    type-global-function-classᵉ Lᵉ Aᵉ (image-factorizationᵉ Fᵉ)
  left-class-map-is-global-function-class-factorizationᵉ =
    left-class-map-is-function-class-factorizationᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)
      ( Fᵉ)

  right-class-map-is-global-function-class-factorizationᵉ :
    is-global-function-class-factorizationᵉ →
    type-global-function-classᵉ Rᵉ (image-factorizationᵉ Fᵉ) Bᵉ
  right-class-map-is-global-function-class-factorizationᵉ =
    right-class-map-is-function-class-factorizationᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)
      ( Fᵉ)
```

### The type of factorizations into global function classes

```agda
global-function-class-factorizationᵉ :
  {βLᵉ βRᵉ : Level → Level → Level}
  (Lᵉ : global-function-classᵉ βLᵉ)
  (Rᵉ : global-function-classᵉ βRᵉ)
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  UUᵉ (βLᵉ l1ᵉ l3ᵉ ⊔ βRᵉ l3ᵉ l2ᵉ ⊔ l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
global-function-class-factorizationᵉ Lᵉ Rᵉ l3ᵉ =
  function-class-factorizationᵉ {l3ᵉ = l3ᵉ}
    ( function-class-global-function-classᵉ Lᵉ)
    ( function-class-global-function-classᵉ Rᵉ)

module _
  {βLᵉ βRᵉ : Level → Level → Level}
  (Lᵉ : global-function-classᵉ βLᵉ)
  (Rᵉ : global-function-classᵉ βRᵉ)
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Fᵉ : global-function-class-factorizationᵉ Lᵉ Rᵉ l3ᵉ fᵉ)
  where

  factorization-global-function-class-factorizationᵉ : factorizationᵉ l3ᵉ fᵉ
  factorization-global-function-class-factorizationᵉ =
    factorization-function-class-factorizationᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)
      ( Fᵉ)

  is-global-function-class-factorization-global-function-class-factorizationᵉ :
    is-global-function-class-factorizationᵉ Lᵉ Rᵉ fᵉ
      ( factorization-global-function-class-factorizationᵉ)
  is-global-function-class-factorization-global-function-class-factorizationᵉ =
    is-function-class-factorization-function-class-factorizationᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)
      ( Fᵉ)

  image-global-function-class-factorizationᵉ : UUᵉ l3ᵉ
  image-global-function-class-factorizationᵉ =
    image-factorizationᵉ factorization-global-function-class-factorizationᵉ

  left-map-global-function-class-factorizationᵉ :
    Aᵉ → image-global-function-class-factorizationᵉ
  left-map-global-function-class-factorizationᵉ =
    left-map-factorizationᵉ factorization-global-function-class-factorizationᵉ

  right-map-global-function-class-factorizationᵉ :
    image-global-function-class-factorizationᵉ → Bᵉ
  right-map-global-function-class-factorizationᵉ =
    right-map-factorizationᵉ factorization-global-function-class-factorizationᵉ

  is-factorization-global-function-class-factorizationᵉ :
    is-factorizationᵉ fᵉ
      ( right-map-global-function-class-factorizationᵉ)
      ( left-map-global-function-class-factorizationᵉ)
  is-factorization-global-function-class-factorizationᵉ =
    is-factorization-factorizationᵉ
      ( factorization-global-function-class-factorizationᵉ)

  is-in-left-class-left-map-global-function-class-factorizationᵉ :
    is-in-global-function-classᵉ Lᵉ left-map-global-function-class-factorizationᵉ
  is-in-left-class-left-map-global-function-class-factorizationᵉ =
    is-in-left-class-left-map-is-global-function-class-factorizationᵉ Lᵉ Rᵉ fᵉ
      ( factorization-global-function-class-factorizationᵉ)
      ( is-global-function-class-factorization-global-function-class-factorizationᵉ)

  is-in-right-class-right-map-global-function-class-factorizationᵉ :
    is-in-global-function-classᵉ Rᵉ right-map-global-function-class-factorizationᵉ
  is-in-right-class-right-map-global-function-class-factorizationᵉ =
    is-in-right-class-right-map-is-global-function-class-factorizationᵉ Lᵉ Rᵉ fᵉ
      ( factorization-global-function-class-factorizationᵉ)
      ( is-global-function-class-factorization-global-function-class-factorizationᵉ)

  left-class-map-global-function-class-factorizationᵉ :
    type-global-function-classᵉ Lᵉ Aᵉ image-global-function-class-factorizationᵉ
  left-class-map-global-function-class-factorizationᵉ =
    left-class-map-is-global-function-class-factorizationᵉ Lᵉ Rᵉ fᵉ
      ( factorization-global-function-class-factorizationᵉ)
      ( is-global-function-class-factorization-global-function-class-factorizationᵉ)

  right-class-map-global-function-class-factorizationᵉ :
    type-global-function-classᵉ Rᵉ image-global-function-class-factorizationᵉ Bᵉ
  right-class-map-global-function-class-factorizationᵉ =
    right-class-map-is-global-function-class-factorizationᵉ Lᵉ Rᵉ fᵉ
      ( factorization-global-function-class-factorizationᵉ)
      ( is-global-function-class-factorization-global-function-class-factorizationᵉ)
```
# Factorization operations into global function classes

```agda
module orthogonal-factorization-systems.factorization-operations-global-function-classesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.factorization-operations-function-classesᵉ
open import orthogonal-factorization-systems.factorizations-of-maps-global-function-classesᵉ
open import orthogonal-factorization-systems.global-function-classesᵉ
```

</details>

## Idea

Aᵉ **factorizationᵉ operationᵉ intoᵉ globalᵉ functionᵉ classes**ᵉ `L`ᵉ andᵉ `R`ᵉ isᵉ aᵉ
[factorizationᵉ operation](orthogonal-factorization-systems.factorization-operations.mdᵉ)
suchᵉ thatᵉ theᵉ leftᵉ mapᵉ (inᵉ diagrammaticᵉ orderᵉ) ofᵉ everyᵉ
[factorization](orthogonal-factorization-systems.factorizations-of-maps.mdᵉ) isᵉ
in `L`,ᵉ andᵉ theᵉ rightᵉ mapᵉ isᵉ in `R`.ᵉ

```text
      Imᵉ fᵉ
      ∧ᵉ  \ᵉ
 Lᵉ ∋ᵉ /ᵉ    \ᵉ ∈ᵉ Rᵉ
    /ᵉ      ∨ᵉ
  Aᵉ ------>ᵉ Bᵉ
       fᵉ
```

## Definitions

### Factorization operations into global function classes

```agda
module _
  {βLᵉ βRᵉ : Level → Level → Level}
  (Lᵉ : global-function-classᵉ βLᵉ)
  (Rᵉ : global-function-classᵉ βRᵉ)
  where

  factorization-operation-global-function-class-Levelᵉ :
    (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (βLᵉ l1ᵉ l3ᵉ ⊔ βRᵉ l3ᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  factorization-operation-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    global-function-class-factorizationᵉ Lᵉ Rᵉ l3ᵉ fᵉ

  factorization-operation-global-function-classᵉ : UUωᵉ
  factorization-operation-global-function-classᵉ =
    {l1ᵉ l2ᵉ l3ᵉ : Level} →
    factorization-operation-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ
```

### Unique factorization operations into global function classes

```agda
module _
  {βLᵉ βRᵉ : Level → Level → Level}
  (Lᵉ : global-function-classᵉ βLᵉ)
  (Rᵉ : global-function-classᵉ βRᵉ)
  where

  unique-factorization-operation-global-function-class-Levelᵉ :
    (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (βLᵉ l1ᵉ l3ᵉ ⊔ βRᵉ l3ᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  unique-factorization-operation-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ =
    unique-factorization-operation-function-classᵉ
      ( function-class-global-function-classᵉ Lᵉ {l1ᵉ} {l3ᵉ})
      ( function-class-global-function-classᵉ Rᵉ {l3ᵉ} {l2ᵉ})

  is-prop-unique-factorization-operation-global-function-class-Levelᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} →
    is-propᵉ
      ( unique-factorization-operation-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ)
  is-prop-unique-factorization-operation-global-function-class-Levelᵉ =
    is-prop-unique-factorization-operation-function-classᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)

  unique-factorization-operation-global-function-class-Level-Propᵉ :
    (l1ᵉ l2ᵉ l3ᵉ : Level) →
    Propᵉ (βLᵉ l1ᵉ l3ᵉ ⊔ βRᵉ l3ᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  unique-factorization-operation-global-function-class-Level-Propᵉ l1ᵉ l2ᵉ l3ᵉ =
    unique-factorization-operation-function-class-Propᵉ
      ( function-class-global-function-classᵉ Lᵉ {l1ᵉ} {l3ᵉ})
      ( function-class-global-function-classᵉ Rᵉ {l3ᵉ} {l2ᵉ})

  unique-factorization-operation-global-function-classᵉ : UUωᵉ
  unique-factorization-operation-global-function-classᵉ =
    {l1ᵉ l2ᵉ l3ᵉ : Level} →
    unique-factorization-operation-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ
```

### Mere factorization properties into global function classes

```agda
module _
  {βLᵉ βRᵉ : Level → Level → Level}
  (Lᵉ : global-function-classᵉ βLᵉ)
  (Rᵉ : global-function-classᵉ βRᵉ)
  where

  mere-factorization-property-global-function-class-Levelᵉ :
    (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (βLᵉ l1ᵉ l3ᵉ ⊔ βRᵉ l3ᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  mere-factorization-property-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ =
    mere-factorization-property-function-classᵉ
      ( function-class-global-function-classᵉ Lᵉ {l1ᵉ} {l3ᵉ})
      ( function-class-global-function-classᵉ Rᵉ {l3ᵉ} {l2ᵉ})

  is-prop-mere-factorization-property-global-function-class-Levelᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} →
    is-propᵉ (mere-factorization-property-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ)
  is-prop-mere-factorization-property-global-function-class-Levelᵉ =
    is-prop-mere-factorization-property-function-classᵉ
      ( function-class-global-function-classᵉ Lᵉ)
      ( function-class-global-function-classᵉ Rᵉ)

  mere-factorization-property-global-function-class-Propᵉ :
    (l1ᵉ l2ᵉ l3ᵉ : Level) →
    Propᵉ (βLᵉ l1ᵉ l3ᵉ ⊔ βRᵉ l3ᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  mere-factorization-property-global-function-class-Propᵉ l1ᵉ l2ᵉ l3ᵉ =
    mere-factorization-property-function-class-Propᵉ
      ( function-class-global-function-classᵉ Lᵉ {l1ᵉ} {l3ᵉ})
      ( function-class-global-function-classᵉ Rᵉ {l3ᵉ} {l2ᵉ})

  mere-factorization-property-global-function-classᵉ : UUωᵉ
  mere-factorization-property-global-function-classᵉ =
    {l1ᵉ l2ᵉ l3ᵉ : Level} →
    mere-factorization-property-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ
```
# Factorization operations into function classes

```agda
module orthogonal-factorization-systems.factorization-operations-function-classesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import orthogonal-factorization-systems.factorizations-of-mapsᵉ
open import orthogonal-factorization-systems.factorizations-of-maps-function-classesᵉ
open import orthogonal-factorization-systems.function-classesᵉ
open import orthogonal-factorization-systems.lifting-structures-on-squaresᵉ
```

</details>

## Idea

Aᵉ **factorizationᵉ operationᵉ intoᵉ (smallᵉ) functionᵉ classes**ᵉ `L`ᵉ andᵉ `R`ᵉ isᵉ aᵉ
[factorizationᵉ operation](orthogonal-factorization-systems.factorization-operations.mdᵉ)
suchᵉ thatᵉ theᵉ leftᵉ mapᵉ (inᵉ diagrammaticᵉ orderᵉ) ofᵉ everyᵉ
[factorization](orthogonal-factorization-systems.factorizations-of-maps.mdᵉ) isᵉ
in `L`,ᵉ andᵉ theᵉ rightᵉ mapᵉ isᵉ in `R`.ᵉ

```text
       ∙ᵉ
      ∧ᵉ \ᵉ
 Lᵉ ∋ᵉ /ᵉ   \ᵉ ∈ᵉ Rᵉ
    /ᵉ     ∨ᵉ
  Aᵉ ----->ᵉ Bᵉ
```

## Definitions

### Factorization operations into function classes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ l1ᵉ l3ᵉ lLᵉ)
  (Rᵉ : function-classᵉ l3ᵉ l2ᵉ lRᵉ)
  where

  instance-factorization-operation-function-classᵉ :
    (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
  instance-factorization-operation-function-classᵉ Aᵉ Bᵉ =
    (fᵉ : Aᵉ → Bᵉ) → function-class-factorizationᵉ Lᵉ Rᵉ fᵉ

  factorization-operation-function-classᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
  factorization-operation-function-classᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    instance-factorization-operation-function-classᵉ Aᵉ Bᵉ
```

### Unique factorization operations into function classes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ l1ᵉ l3ᵉ lLᵉ)
  (Rᵉ : function-classᵉ l3ᵉ l2ᵉ lRᵉ)
  where

  instance-unique-factorization-operation-function-classᵉ :
    (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
  instance-unique-factorization-operation-function-classᵉ Aᵉ Bᵉ =
    (fᵉ : Aᵉ → Bᵉ) → is-contrᵉ (function-class-factorizationᵉ Lᵉ Rᵉ fᵉ)

  unique-factorization-operation-function-classᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
  unique-factorization-operation-function-classᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    instance-unique-factorization-operation-function-classᵉ Aᵉ Bᵉ

  is-prop-unique-factorization-operation-function-classᵉ :
    is-propᵉ unique-factorization-operation-function-classᵉ
  is-prop-unique-factorization-operation-function-classᵉ =
    is-prop-iterated-implicit-Πᵉ 2
      ( λ Aᵉ Bᵉ → is-prop-Πᵉ (λ fᵉ → is-property-is-contrᵉ))

  unique-factorization-operation-function-class-Propᵉ :
    Propᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
  pr1ᵉ unique-factorization-operation-function-class-Propᵉ =
    unique-factorization-operation-function-classᵉ
  pr2ᵉ unique-factorization-operation-function-class-Propᵉ =
    is-prop-unique-factorization-operation-function-classᵉ

  factorization-operation-unique-factorization-operation-function-classᵉ :
    unique-factorization-operation-function-classᵉ →
    factorization-operation-function-classᵉ Lᵉ Rᵉ
  factorization-operation-unique-factorization-operation-function-classᵉ Fᵉ fᵉ =
    centerᵉ (Fᵉ fᵉ)
```

### Mere factorization properties into function classes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ l1ᵉ l3ᵉ lLᵉ)
  (Rᵉ : function-classᵉ l3ᵉ l2ᵉ lRᵉ)
  where

  instance-mere-factorization-property-function-classᵉ :
    (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
  instance-mere-factorization-property-function-classᵉ Aᵉ Bᵉ =
    (fᵉ : Aᵉ → Bᵉ) → is-inhabitedᵉ (function-class-factorizationᵉ Lᵉ Rᵉ fᵉ)

  mere-factorization-property-function-classᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
  mere-factorization-property-function-classᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    instance-mere-factorization-property-function-classᵉ Aᵉ Bᵉ

  is-prop-mere-factorization-property-function-classᵉ :
    is-propᵉ mere-factorization-property-function-classᵉ
  is-prop-mere-factorization-property-function-classᵉ =
    is-prop-iterated-implicit-Πᵉ 2
      ( λ Aᵉ Bᵉ →
        is-prop-Πᵉ
          ( λ fᵉ →
            is-property-is-inhabitedᵉ (function-class-factorizationᵉ Lᵉ Rᵉ fᵉ)))

  mere-factorization-property-function-class-Propᵉ :
    Propᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
  pr1ᵉ mere-factorization-property-function-class-Propᵉ =
    mere-factorization-property-function-classᵉ
  pr2ᵉ mere-factorization-property-function-class-Propᵉ =
    is-prop-mere-factorization-property-function-classᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}}

## See also

-ᵉ [Factorizationᵉ operationsᵉ intoᵉ globalᵉ functionᵉ classes](orthogonal-factorization-systems.factorization-operations-global-function-classes.mdᵉ)
  forᵉ theᵉ universeᵉ polymorphicᵉ version.ᵉ
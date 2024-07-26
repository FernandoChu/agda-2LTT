# Orthogonal factorization systems

```agda
module orthogonal-factorization-systems.orthogonal-factorization-systemsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import orthogonal-factorization-systems.factorization-operations-function-classesᵉ
open import orthogonal-factorization-systems.factorizations-of-mapsᵉ
open import orthogonal-factorization-systems.factorizations-of-maps-function-classesᵉ
open import orthogonal-factorization-systems.function-classesᵉ
open import orthogonal-factorization-systems.lifting-structures-on-squaresᵉ
open import orthogonal-factorization-systems.wide-function-classesᵉ
```

</details>

## Idea

Anᵉ **orthogonalᵉ factorizationᵉ system**ᵉ isᵉ aᵉ pairᵉ ofᵉ
[wide](orthogonal-factorization-systems.wide-function-classes.mdᵉ)
[functionᵉ classes](orthogonal-factorization-systems.function-classes.mdᵉ) `L`ᵉ andᵉ
`R`,ᵉ suchᵉ thatᵉ forᵉ everyᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ thereᵉ isᵉ aᵉ
[unique](foundation-core.contractible-types.mdᵉ)
[factorization](orthogonal-factorization-systems.factorizations-of-maps.mdᵉ)
`fᵉ ~ᵉ rᵉ ∘ᵉ l`ᵉ where theᵉ leftᵉ mapᵉ (byᵉ diagrammaticᵉ orderingᵉ) `l`ᵉ isᵉ in `L`ᵉ andᵉ theᵉ
rightᵉ mapᵉ `r`ᵉ isᵉ in `R`.ᵉ

## Definition

### The predicate of being an orthogonal factorization system

```agda
module _
  {lᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ lᵉ lᵉ lLᵉ)
  (Rᵉ : function-classᵉ lᵉ lᵉ lRᵉ)
  where

  is-orthogonal-factorization-systemᵉ : UUᵉ (lsuc lᵉ ⊔ lLᵉ ⊔ lRᵉ)
  is-orthogonal-factorization-systemᵉ =
    ( is-wide-function-classᵉ Lᵉ) ×ᵉ
    ( ( is-wide-function-classᵉ Rᵉ) ×ᵉ
      ( unique-factorization-operation-function-classᵉ Lᵉ Rᵉ))

  is-prop-is-orthogonal-factorization-systemᵉ :
    is-propᵉ is-orthogonal-factorization-systemᵉ
  is-prop-is-orthogonal-factorization-systemᵉ =
    is-prop-productᵉ
      ( is-prop-is-wide-function-classᵉ Lᵉ)
      ( is-prop-productᵉ
        ( is-prop-is-wide-function-classᵉ Rᵉ)
        ( is-prop-unique-factorization-operation-function-classᵉ Lᵉ Rᵉ))

  is-orthogonal-factorization-system-Propᵉ : Propᵉ (lsuc lᵉ ⊔ lLᵉ ⊔ lRᵉ)
  pr1ᵉ is-orthogonal-factorization-system-Propᵉ =
    is-orthogonal-factorization-systemᵉ
  pr2ᵉ is-orthogonal-factorization-system-Propᵉ =
    is-prop-is-orthogonal-factorization-systemᵉ
```

### The type of orthogonal factorization systems

```agda
orthogonal-factorization-systemᵉ :
  (lᵉ lLᵉ lRᵉ : Level) → UUᵉ (lsuc lᵉ ⊔ lsuc lLᵉ ⊔ lsuc lRᵉ)
orthogonal-factorization-systemᵉ lᵉ lLᵉ lRᵉ =
  Σᵉ ( function-classᵉ lᵉ lᵉ lLᵉ)
    ( λ Lᵉ → Σᵉ (function-classᵉ lᵉ lᵉ lRᵉ) (is-orthogonal-factorization-systemᵉ Lᵉ))
```

### Components of an orthogonal factorization system

```agda
module _
  {lᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ lᵉ lᵉ lLᵉ)
  (Rᵉ : function-classᵉ lᵉ lᵉ lRᵉ)
  (is-OFSᵉ : is-orthogonal-factorization-systemᵉ Lᵉ Rᵉ)
  where

  is-wide-left-class-is-orthogonal-factorization-systemᵉ :
    is-wide-function-classᵉ Lᵉ
  is-wide-left-class-is-orthogonal-factorization-systemᵉ = pr1ᵉ is-OFSᵉ

  is-wide-right-class-is-orthogonal-factorization-systemᵉ :
    is-wide-function-classᵉ Rᵉ
  is-wide-right-class-is-orthogonal-factorization-systemᵉ = pr1ᵉ (pr2ᵉ is-OFSᵉ)

  has-equivalences-left-class-is-orthogonal-factorization-systemᵉ :
    has-equivalences-function-classᵉ Lᵉ
  has-equivalences-left-class-is-orthogonal-factorization-systemᵉ =
    has-equivalences-is-wide-function-classᵉ Lᵉ
      ( is-wide-left-class-is-orthogonal-factorization-systemᵉ)

  has-equivalences-right-class-is-orthogonal-factorization-systemᵉ :
    has-equivalences-function-classᵉ Rᵉ
  has-equivalences-right-class-is-orthogonal-factorization-systemᵉ =
    has-equivalences-is-wide-function-classᵉ Rᵉ
      ( is-wide-right-class-is-orthogonal-factorization-systemᵉ)

  is-closed-under-composition-left-class-is-orthogonal-factorization-systemᵉ :
    is-closed-under-composition-function-classᵉ Lᵉ
  is-closed-under-composition-left-class-is-orthogonal-factorization-systemᵉ =
    is-closed-under-composition-is-wide-function-classᵉ Lᵉ
      ( is-wide-left-class-is-orthogonal-factorization-systemᵉ)

  is-closed-under-composition-right-class-is-orthogonal-factorization-systemᵉ :
    is-closed-under-composition-function-classᵉ Rᵉ
  is-closed-under-composition-right-class-is-orthogonal-factorization-systemᵉ =
    is-closed-under-composition-is-wide-function-classᵉ Rᵉ
      ( is-wide-right-class-is-orthogonal-factorization-systemᵉ)

  unique-factorization-operation-is-orthogonal-factorization-systemᵉ :
    unique-factorization-operation-function-classᵉ Lᵉ Rᵉ
  unique-factorization-operation-is-orthogonal-factorization-systemᵉ =
    pr2ᵉ (pr2ᵉ is-OFSᵉ)

  factorization-operation-is-orthogonal-factorization-systemᵉ :
    factorization-operation-function-classᵉ Lᵉ Rᵉ
  factorization-operation-is-orthogonal-factorization-systemᵉ fᵉ =
    centerᵉ
      ( unique-factorization-operation-is-orthogonal-factorization-systemᵉ fᵉ)

module _
  {lᵉ lLᵉ lRᵉ : Level}
  (OFSᵉ : orthogonal-factorization-systemᵉ lᵉ lLᵉ lRᵉ)
  where

  left-class-orthogonal-factorization-systemᵉ : function-classᵉ lᵉ lᵉ lLᵉ
  left-class-orthogonal-factorization-systemᵉ = pr1ᵉ OFSᵉ

  right-class-orthogonal-factorization-systemᵉ : function-classᵉ lᵉ lᵉ lRᵉ
  right-class-orthogonal-factorization-systemᵉ = pr1ᵉ (pr2ᵉ OFSᵉ)

  is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ :
    is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
  is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ =
    pr2ᵉ (pr2ᵉ OFSᵉ)

  is-wide-left-class-orthogonal-factorization-systemᵉ :
    is-wide-function-classᵉ left-class-orthogonal-factorization-systemᵉ
  is-wide-left-class-orthogonal-factorization-systemᵉ =
    is-wide-left-class-is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
      ( is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ)

  is-wide-right-class-orthogonal-factorization-systemᵉ :
    is-wide-function-classᵉ right-class-orthogonal-factorization-systemᵉ
  is-wide-right-class-orthogonal-factorization-systemᵉ =
    is-wide-right-class-is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
      ( is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ)

  has-equivalences-left-class-orthogonal-factorization-systemᵉ :
    has-equivalences-function-classᵉ left-class-orthogonal-factorization-systemᵉ
  has-equivalences-left-class-orthogonal-factorization-systemᵉ =
    has-equivalences-left-class-is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
      ( is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ)

  has-equivalences-right-class-orthogonal-factorization-systemᵉ :
    has-equivalences-function-classᵉ right-class-orthogonal-factorization-systemᵉ
  has-equivalences-right-class-orthogonal-factorization-systemᵉ =
    has-equivalences-right-class-is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
      ( is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ)

  is-closed-under-composition-left-class-orthogonal-factorization-systemᵉ :
    is-closed-under-composition-function-classᵉ
      left-class-orthogonal-factorization-systemᵉ
  is-closed-under-composition-left-class-orthogonal-factorization-systemᵉ =
    is-closed-under-composition-left-class-is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
      ( is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ)

  is-closed-under-composition-right-class-orthogonal-factorization-systemᵉ :
    is-closed-under-composition-function-classᵉ
      right-class-orthogonal-factorization-systemᵉ
  is-closed-under-composition-right-class-orthogonal-factorization-systemᵉ =
    is-closed-under-composition-right-class-is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
      ( is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ)

  unique-factorization-operation-orthogonal-factorization-systemᵉ :
    unique-factorization-operation-function-classᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
  unique-factorization-operation-orthogonal-factorization-systemᵉ =
    unique-factorization-operation-is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
      ( is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ)

  factorization-operation-orthogonal-factorization-systemᵉ :
    factorization-operation-function-classᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
  factorization-operation-orthogonal-factorization-systemᵉ =
    factorization-operation-is-orthogonal-factorization-systemᵉ
      ( left-class-orthogonal-factorization-systemᵉ)
      ( right-class-orthogonal-factorization-systemᵉ)
      ( is-orthogonal-factorization-system-orthogonal-factorization-systemᵉ)
```

## Properties

### An orthogonal factorization system is uniquely determined by its right class

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#738](https://github.com/UniMath/agda-unimath/issues/738ᵉ)

### The right class of an orthogonal factorization system is pullback-stable

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#738](https://github.com/UniMath/agda-unimath/issues/738ᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}}

## External links

-ᵉ [Orthogonalᵉ factorisationᵉ systems](https://1lab.dev/Cat.Morphism.Factorisation.html#orthogonal-factorisation-systemsᵉ)
  atᵉ 1labᵉ
-ᵉ [orthogonalᵉ factorizationᵉ systemᵉ in anᵉ (infinity,1)-category](https://ncatlab.org/nlab/show/orthogonal+factorization+system+in+an+%28infinity%2C1%29-categoryᵉ)
  atᵉ $n$Labᵉ
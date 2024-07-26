# Factorizations of maps into function classes

```agda
module orthogonal-factorization-systems.factorizations-of-maps-function-classesᵉ where
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
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import orthogonal-factorization-systems.factorizations-of-mapsᵉ
open import orthogonal-factorization-systems.function-classesᵉ
open import orthogonal-factorization-systems.global-function-classesᵉ
```

</details>

## Idea

Aᵉ **functionᵉ classᵉ factorization**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ intoᵉ
[functionᵉ classes](orthogonal-factorization-systems.function-classes.mdᵉ) `L`ᵉ andᵉ
`R`ᵉ isᵉ aᵉ pairᵉ ofᵉ mapsᵉ `lᵉ : Aᵉ → X`ᵉ andᵉ `rᵉ : Xᵉ → B`,ᵉ where `lᵉ ∈ᵉ L`ᵉ andᵉ `rᵉ ∈ᵉ R`,ᵉ
suchᵉ thatᵉ theirᵉ compositeᵉ `rᵉ ∘ᵉ l`ᵉ isᵉ `f`.ᵉ

```text
         Xᵉ
        ∧ᵉ \ᵉ
 Lᵉ ∋ᵉ lᵉ /ᵉ   \ᵉ rᵉ ∈ᵉ Rᵉ
      /ᵉ     ∨ᵉ
    Aᵉ ----->ᵉ Bᵉ
        fᵉ
```

## Definitions

### The predicate of being a function class factorization

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ l1ᵉ l3ᵉ lLᵉ)
  (Rᵉ : function-classᵉ l3ᵉ l2ᵉ lRᵉ)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Fᵉ : factorizationᵉ l3ᵉ fᵉ)
  where

  is-function-class-factorization-Propᵉ : Propᵉ (lLᵉ ⊔ lRᵉ)
  is-function-class-factorization-Propᵉ =
    product-Propᵉ
      ( Lᵉ (left-map-factorizationᵉ Fᵉ))
      ( Rᵉ (right-map-factorizationᵉ Fᵉ))

  is-function-class-factorizationᵉ : UUᵉ (lLᵉ ⊔ lRᵉ)
  is-function-class-factorizationᵉ =
    type-Propᵉ is-function-class-factorization-Propᵉ

  is-prop-is-function-class-factorizationᵉ :
    is-propᵉ is-function-class-factorizationᵉ
  is-prop-is-function-class-factorizationᵉ =
    is-prop-type-Propᵉ is-function-class-factorization-Propᵉ

  is-in-left-class-left-map-is-function-class-factorizationᵉ :
    is-function-class-factorizationᵉ →
    is-in-function-classᵉ Lᵉ (left-map-factorizationᵉ Fᵉ)
  is-in-left-class-left-map-is-function-class-factorizationᵉ = pr1ᵉ

  is-in-right-class-right-map-is-function-class-factorizationᵉ :
    is-function-class-factorizationᵉ →
    is-in-function-classᵉ Rᵉ (right-map-factorizationᵉ Fᵉ)
  is-in-right-class-right-map-is-function-class-factorizationᵉ = pr2ᵉ

  left-class-map-is-function-class-factorizationᵉ :
    is-function-class-factorizationᵉ →
    type-function-classᵉ Lᵉ Aᵉ (image-factorizationᵉ Fᵉ)
  pr1ᵉ (left-class-map-is-function-class-factorizationᵉ xᵉ) =
    left-map-factorizationᵉ Fᵉ
  pr2ᵉ (left-class-map-is-function-class-factorizationᵉ xᵉ) =
    is-in-left-class-left-map-is-function-class-factorizationᵉ xᵉ

  right-class-map-is-function-class-factorizationᵉ :
    is-function-class-factorizationᵉ →
    type-function-classᵉ Rᵉ (image-factorizationᵉ Fᵉ) Bᵉ
  pr1ᵉ (right-class-map-is-function-class-factorizationᵉ xᵉ) =
    right-map-factorizationᵉ Fᵉ
  pr2ᵉ (right-class-map-is-function-class-factorizationᵉ xᵉ) =
    is-in-right-class-right-map-is-function-class-factorizationᵉ xᵉ
```

### The type of factorizations into function classes

```agda
function-class-factorizationᵉ :
  {l1ᵉ l2ᵉ l3ᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ l1ᵉ l3ᵉ lLᵉ)
  (Rᵉ : function-classᵉ l3ᵉ l2ᵉ lRᵉ)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lLᵉ ⊔ lRᵉ)
function-class-factorizationᵉ {l3ᵉ = l3ᵉ} Lᵉ Rᵉ fᵉ =
  Σᵉ (factorizationᵉ l3ᵉ fᵉ) (is-function-class-factorizationᵉ Lᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ l1ᵉ l3ᵉ lLᵉ)
  (Rᵉ : function-classᵉ l3ᵉ l2ᵉ lRᵉ)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Fᵉ : function-class-factorizationᵉ Lᵉ Rᵉ fᵉ)
  where

  factorization-function-class-factorizationᵉ : factorizationᵉ l3ᵉ fᵉ
  factorization-function-class-factorizationᵉ = pr1ᵉ Fᵉ

  is-function-class-factorization-function-class-factorizationᵉ :
    is-function-class-factorizationᵉ Lᵉ Rᵉ
      ( factorization-function-class-factorizationᵉ)
  is-function-class-factorization-function-class-factorizationᵉ = pr2ᵉ Fᵉ

  image-function-class-factorizationᵉ : UUᵉ l3ᵉ
  image-function-class-factorizationᵉ =
    image-factorizationᵉ factorization-function-class-factorizationᵉ

  left-map-function-class-factorizationᵉ :
    Aᵉ → image-function-class-factorizationᵉ
  left-map-function-class-factorizationᵉ =
    left-map-factorizationᵉ factorization-function-class-factorizationᵉ

  right-map-function-class-factorizationᵉ :
    image-function-class-factorizationᵉ → Bᵉ
  right-map-function-class-factorizationᵉ =
    right-map-factorizationᵉ factorization-function-class-factorizationᵉ

  is-factorization-function-class-factorizationᵉ :
    is-factorizationᵉ fᵉ
      ( right-map-function-class-factorizationᵉ)
      ( left-map-function-class-factorizationᵉ)
  is-factorization-function-class-factorizationᵉ =
    is-factorization-factorizationᵉ factorization-function-class-factorizationᵉ

  is-in-left-class-left-map-function-class-factorizationᵉ :
    is-in-function-classᵉ Lᵉ left-map-function-class-factorizationᵉ
  is-in-left-class-left-map-function-class-factorizationᵉ =
    is-in-left-class-left-map-is-function-class-factorizationᵉ Lᵉ Rᵉ
      ( factorization-function-class-factorizationᵉ)
      ( is-function-class-factorization-function-class-factorizationᵉ)

  is-in-right-class-right-map-function-class-factorizationᵉ :
    is-in-function-classᵉ Rᵉ right-map-function-class-factorizationᵉ
  is-in-right-class-right-map-function-class-factorizationᵉ =
    is-in-right-class-right-map-is-function-class-factorizationᵉ Lᵉ Rᵉ
      ( factorization-function-class-factorizationᵉ)
      ( is-function-class-factorization-function-class-factorizationᵉ)

  left-class-map-function-class-factorizationᵉ :
    type-function-classᵉ Lᵉ Aᵉ image-function-class-factorizationᵉ
  left-class-map-function-class-factorizationᵉ =
    left-class-map-is-function-class-factorizationᵉ Lᵉ Rᵉ
      ( factorization-function-class-factorizationᵉ)
      ( is-function-class-factorization-function-class-factorizationᵉ)

  right-class-map-function-class-factorizationᵉ :
    type-function-classᵉ Rᵉ image-function-class-factorizationᵉ Bᵉ
  right-class-map-function-class-factorizationᵉ =
    right-class-map-is-function-class-factorizationᵉ Lᵉ Rᵉ
      ( factorization-function-class-factorizationᵉ)
      ( is-function-class-factorization-function-class-factorizationᵉ)
```

## Properties

### Characterization of identifications of factorizations of a map into function classes

**Proof:**ᵉ Thisᵉ followsᵉ immediatelyᵉ fromᵉ theᵉ characterizationᵉ ofᵉ identificationsᵉ
ofᵉ factorizationsᵉ using theᵉ
[subtypeᵉ identityᵉ principle](foundation.subtype-identity-principle.md).ᵉ

Whatᵉ followsᵉ isᵉ aᵉ longᵉ listᵉ ofᵉ auxillaryᵉ definitions.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ lLᵉ lRᵉ : Level}
  (Lᵉ : function-classᵉ l1ᵉ l3ᵉ lLᵉ)
  (Rᵉ : function-classᵉ l3ᵉ l2ᵉ lRᵉ)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  equiv-function-class-factorizationᵉ :
    (Fᵉ Eᵉ : function-class-factorizationᵉ Lᵉ Rᵉ fᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-function-class-factorizationᵉ Fᵉ Eᵉ =
    equiv-factorizationᵉ fᵉ
      ( factorization-function-class-factorizationᵉ Lᵉ Rᵉ Fᵉ)
      ( factorization-function-class-factorizationᵉ Lᵉ Rᵉ Eᵉ)

  id-equiv-function-class-factorizationᵉ :
    (Fᵉ : function-class-factorizationᵉ Lᵉ Rᵉ fᵉ) →
    equiv-function-class-factorizationᵉ Fᵉ Fᵉ
  id-equiv-function-class-factorizationᵉ Fᵉ =
    id-equiv-factorizationᵉ fᵉ
      ( factorization-function-class-factorizationᵉ Lᵉ Rᵉ Fᵉ)

  equiv-eq-function-class-factorizationᵉ :
    (Fᵉ Eᵉ : function-class-factorizationᵉ Lᵉ Rᵉ fᵉ) →
    Fᵉ ＝ᵉ Eᵉ → equiv-function-class-factorizationᵉ Fᵉ Eᵉ
  equiv-eq-function-class-factorizationᵉ Fᵉ Eᵉ pᵉ =
    equiv-eq-factorizationᵉ fᵉ
      ( factorization-function-class-factorizationᵉ Lᵉ Rᵉ Fᵉ)
      ( factorization-function-class-factorizationᵉ Lᵉ Rᵉ Eᵉ)
      ( apᵉ pr1ᵉ pᵉ)

  is-torsorial-equiv-function-class-factorizationᵉ :
    (Fᵉ : function-class-factorizationᵉ Lᵉ Rᵉ fᵉ) →
    is-torsorialᵉ (equiv-function-class-factorizationᵉ Fᵉ)
  is-torsorial-equiv-function-class-factorizationᵉ Fᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-equiv-factorizationᵉ fᵉ
        ( factorization-function-class-factorizationᵉ Lᵉ Rᵉ Fᵉ))
      ( is-prop-is-function-class-factorizationᵉ Lᵉ Rᵉ)
      ( factorization-function-class-factorizationᵉ Lᵉ Rᵉ Fᵉ)
      ( id-equiv-function-class-factorizationᵉ Fᵉ)
      ( is-function-class-factorization-function-class-factorizationᵉ Lᵉ Rᵉ Fᵉ)

  is-equiv-equiv-eq-function-class-factorizationᵉ :
    (Fᵉ Eᵉ : function-class-factorizationᵉ Lᵉ Rᵉ fᵉ) →
    is-equivᵉ (equiv-eq-function-class-factorizationᵉ Fᵉ Eᵉ)
  is-equiv-equiv-eq-function-class-factorizationᵉ Fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-function-class-factorizationᵉ Fᵉ)
      ( equiv-eq-function-class-factorizationᵉ Fᵉ)

  extensionality-function-class-factorizationᵉ :
    (Fᵉ Eᵉ : function-class-factorizationᵉ Lᵉ Rᵉ fᵉ) →
    (Fᵉ ＝ᵉ Eᵉ) ≃ᵉ (equiv-function-class-factorizationᵉ Fᵉ Eᵉ)
  pr1ᵉ (extensionality-function-class-factorizationᵉ Fᵉ Eᵉ) =
    equiv-eq-function-class-factorizationᵉ Fᵉ Eᵉ
  pr2ᵉ (extensionality-function-class-factorizationᵉ Fᵉ Eᵉ) =
    is-equiv-equiv-eq-function-class-factorizationᵉ Fᵉ Eᵉ

  eq-equiv-function-class-factorizationᵉ :
    (Fᵉ Eᵉ : function-class-factorizationᵉ Lᵉ Rᵉ fᵉ) →
    equiv-function-class-factorizationᵉ Fᵉ Eᵉ → Fᵉ ＝ᵉ Eᵉ
  eq-equiv-function-class-factorizationᵉ Fᵉ Eᵉ =
    map-inv-equivᵉ (extensionality-function-class-factorizationᵉ Fᵉ Eᵉ)
```

## See also

-ᵉ [Factorizationsᵉ ofᵉ mapsᵉ intoᵉ globalᵉ functionᵉ classes](orthogonal-factorization-systems.factorizations-of-maps-global-function-classes.mdᵉ)
  forᵉ theᵉ universeᵉ polymorphicᵉ version.ᵉ
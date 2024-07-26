# Extensions of double lifts of families of elements

```agda
module
  orthogonal-factorization-systems.extensions-double-lifts-families-of-elementsᵉ
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ

open import orthogonal-factorization-systems.double-lifts-families-of-elementsᵉ
open import orthogonal-factorization-systems.lifts-families-of-elementsᵉ
```

</details>

## Idea

Considerᵉ aᵉ
[dependentᵉ lift](orthogonal-factorization-systems.lifts-families-of-elements.mdᵉ)
`bᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ (aᵉ i)`ᵉ ofᵉ aᵉ familyᵉ ofᵉ elementsᵉ `aᵉ : Iᵉ → A`,ᵉ aᵉ typeᵉ familyᵉ `C`ᵉ
overᵉ `B`ᵉ andᵉ aᵉ
[doubleᵉ lift](orthogonal-factorization-systems.double-lifts-families-of-elements.mdᵉ)

```text
  cᵉ : (iᵉ : Iᵉ) → Cᵉ iᵉ (aᵉ iᵉ) (bᵉ iᵉ)
```

ofᵉ theᵉ liftᵉ `b`ᵉ ofᵉ `a`.ᵉ Anᵉ
{{#conceptᵉ "extension"ᵉ Disambiguation="dependentᵉ doubleᵉ familyᵉ ofᵉ elements"ᵉ Agda=extension-dependent-double-lift-family-of-elementsᵉ}}
ofᵉ `b`ᵉ to `A`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ elementsᵉ
`fᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (yᵉ : Bᵉ iᵉ xᵉ) → Cᵉ iᵉ xᵉ y`ᵉ equippedᵉ with aᵉ
[homotopy](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ
[identification](foundation-core.identity-types.mdᵉ) `fᵉ iᵉ (aᵉ iᵉ) (bᵉ iᵉ) ＝ᵉ cᵉ i`ᵉ
holdsᵉ forᵉ everyᵉ `iᵉ : I`.ᵉ

Extensionsᵉ ofᵉ dependentᵉ doubleᵉ liftsᵉ playᵉ aᵉ roleᵉ in theᵉ
[universalᵉ propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ fibersᵉ ofᵉ aᵉ map](foundation.universal-property-family-of-fibers-of-maps.mdᵉ)

## Definitions

### Evaluating families of elements at dependent double lifts of families of elements

Anyᵉ familyᵉ ofᵉ elementsᵉ `bᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ (aᵉ i)`ᵉ dependentᵉ overᵉ aᵉ familyᵉ ofᵉ
elementsᵉ `aᵉ : (iᵉ : Iᵉ) → Aᵉ i`ᵉ inducesᵉ anᵉ evaluationᵉ mapᵉ

```text
  ((iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (yᵉ : Bᵉ iᵉ xᵉ) → Cᵉ iᵉ xᵉ yᵉ) → ((iᵉ : Iᵉ) → Cᵉ iᵉ (aᵉ iᵉ) (bᵉ iᵉ))
```

givenᵉ byᵉ `cᵉ ↦ᵉ (λ iᵉ → cᵉ iᵉ (aᵉ iᵉ) (bᵉ i))`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ}
  {Cᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ → UUᵉ l4ᵉ}
  {aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ} (bᵉ : dependent-lift-family-of-elementsᵉ Bᵉ aᵉ)
  where

  ev-dependent-double-lift-family-of-elementsᵉ :
    ((iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (yᵉ : Bᵉ iᵉ xᵉ) → Cᵉ iᵉ xᵉ yᵉ) →
    dependent-double-lift-family-of-elementsᵉ Cᵉ bᵉ
  ev-dependent-double-lift-family-of-elementsᵉ hᵉ iᵉ = hᵉ iᵉ (aᵉ iᵉ) (bᵉ iᵉ)
```

### Evaluating families of elements at double lifts of families of elements

Anyᵉ familyᵉ ofᵉ elementsᵉ `bᵉ : (iᵉ : Iᵉ) → Bᵉ (aᵉ i)`ᵉ dependentᵉ overᵉ aᵉ familyᵉ ofᵉ
elementsᵉ `aᵉ : Iᵉ → A`ᵉ inducesᵉ anᵉ evaluationᵉ mapᵉ

```text
  ((xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → ((iᵉ : Iᵉ) → Cᵉ (aᵉ iᵉ) (bᵉ iᵉ))
```

givenᵉ byᵉ `cᵉ ↦ᵉ (λ iᵉ → cᵉ (aᵉ iᵉ) (bᵉ i))`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l4ᵉ}
  {aᵉ : Iᵉ → Aᵉ} (bᵉ : lift-family-of-elementsᵉ Bᵉ aᵉ)
  where

  ev-double-lift-family-of-elementsᵉ :
    ((xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → double-lift-family-of-elementsᵉ Cᵉ bᵉ
  ev-double-lift-family-of-elementsᵉ hᵉ iᵉ = hᵉ (aᵉ iᵉ) (bᵉ iᵉ)
```

### Dependent extensions of double lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ}
  (Cᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (yᵉ : Bᵉ iᵉ xᵉ) → UUᵉ l4ᵉ)
  {aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ} (bᵉ : dependent-lift-family-of-elementsᵉ Bᵉ aᵉ)
  (cᵉ : dependent-double-lift-family-of-elementsᵉ Cᵉ bᵉ)
  where

  is-extension-dependent-double-lift-family-of-elementsᵉ :
    (fᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (yᵉ : Bᵉ iᵉ xᵉ) → Cᵉ iᵉ xᵉ yᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  is-extension-dependent-double-lift-family-of-elementsᵉ fᵉ =
    ev-dependent-double-lift-family-of-elementsᵉ bᵉ fᵉ ~ᵉ cᵉ

  extension-dependent-double-lift-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  extension-dependent-double-lift-family-of-elementsᵉ =
    Σᵉ ( (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (yᵉ : Bᵉ iᵉ xᵉ) → Cᵉ iᵉ xᵉ yᵉ)
      ( is-extension-dependent-double-lift-family-of-elementsᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ}
  {Cᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (yᵉ : Bᵉ iᵉ xᵉ) → UUᵉ l4ᵉ}
  {aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ} {bᵉ : dependent-lift-family-of-elementsᵉ Bᵉ aᵉ}
  {cᵉ : dependent-double-lift-family-of-elementsᵉ Cᵉ bᵉ}
  (fᵉ : extension-dependent-double-lift-family-of-elementsᵉ Cᵉ bᵉ cᵉ)
  where

  family-of-elements-extension-dependent-double-lift-family-of-elementsᵉ :
    (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (yᵉ : Bᵉ iᵉ xᵉ) → Cᵉ iᵉ xᵉ yᵉ
  family-of-elements-extension-dependent-double-lift-family-of-elementsᵉ =
    pr1ᵉ fᵉ

  is-extension-extension-dependent-double-lift-family-of-elementsᵉ :
    is-extension-dependent-double-lift-family-of-elementsᵉ Cᵉ bᵉ cᵉ
      ( family-of-elements-extension-dependent-double-lift-family-of-elementsᵉ)
  is-extension-extension-dependent-double-lift-family-of-elementsᵉ = pr2ᵉ fᵉ
```

### Extensions of double lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Cᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → UUᵉ l4ᵉ)
  {aᵉ : Iᵉ → Aᵉ} (bᵉ : lift-family-of-elementsᵉ Bᵉ aᵉ)
  (cᵉ : double-lift-family-of-elementsᵉ Cᵉ bᵉ)
  where

  is-extension-double-lift-family-of-elementsᵉ :
    (fᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  is-extension-double-lift-family-of-elementsᵉ fᵉ =
    ev-double-lift-family-of-elementsᵉ bᵉ fᵉ ~ᵉ cᵉ

  extension-double-lift-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  extension-double-lift-family-of-elementsᵉ =
    Σᵉ ((xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) is-extension-double-lift-family-of-elementsᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  {Cᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → UUᵉ l4ᵉ}
  {aᵉ : Iᵉ → Aᵉ} {bᵉ : lift-family-of-elementsᵉ Bᵉ aᵉ}
  {cᵉ : double-lift-family-of-elementsᵉ Cᵉ bᵉ}
  (fᵉ : extension-double-lift-family-of-elementsᵉ Cᵉ bᵉ cᵉ)
  where

  family-of-elements-extension-double-lift-family-of-elementsᵉ :
    (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ
  family-of-elements-extension-double-lift-family-of-elementsᵉ = pr1ᵉ fᵉ

  is-extension-extension-double-lift-family-of-elementsᵉ :
    is-extension-double-lift-family-of-elementsᵉ Cᵉ bᵉ cᵉ
      ( family-of-elements-extension-double-lift-family-of-elementsᵉ)
  is-extension-extension-double-lift-family-of-elementsᵉ = pr2ᵉ fᵉ
```

### Identity extensions of dependent double lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ}
  {aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ} (bᵉ : dependent-lift-family-of-elementsᵉ Bᵉ aᵉ)
  where

  id-extension-dependent-double-lift-family-of-elementsᵉ :
    extension-dependent-double-lift-family-of-elementsᵉ (λ iᵉ xᵉ yᵉ → Bᵉ iᵉ xᵉ) bᵉ bᵉ
  pr1ᵉ id-extension-dependent-double-lift-family-of-elementsᵉ iᵉ xᵉ = idᵉ
  pr2ᵉ id-extension-dependent-double-lift-family-of-elementsᵉ = refl-htpyᵉ
```

### Identity extensions of double lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  {aᵉ : Iᵉ → Aᵉ} (bᵉ : lift-family-of-elementsᵉ Bᵉ aᵉ)
  where

  id-extension-double-lift-family-of-elementsᵉ :
    extension-double-lift-family-of-elementsᵉ (λ xᵉ (yᵉ : Bᵉ xᵉ) → Bᵉ xᵉ) bᵉ bᵉ
  pr1ᵉ id-extension-double-lift-family-of-elementsᵉ xᵉ = idᵉ
  pr2ᵉ id-extension-double-lift-family-of-elementsᵉ = refl-htpyᵉ
```

### Composition of extensions of dependent double lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ} {Cᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l4ᵉ}
  {Dᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l5ᵉ}
  {aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ}
  {bᵉ : dependent-lift-family-of-elementsᵉ Bᵉ aᵉ}
  {cᵉ : dependent-lift-family-of-elementsᵉ Cᵉ aᵉ}
  {dᵉ : dependent-lift-family-of-elementsᵉ Dᵉ aᵉ}
  (gᵉ :
    extension-dependent-double-lift-family-of-elementsᵉ
      ( λ iᵉ xᵉ (ᵉ_ : Cᵉ iᵉ xᵉ) → Dᵉ iᵉ xᵉ)
      ( cᵉ)
      ( dᵉ))
  (fᵉ :
    extension-dependent-double-lift-family-of-elementsᵉ
      ( λ iᵉ xᵉ (ᵉ_ : Bᵉ iᵉ xᵉ) → Cᵉ iᵉ xᵉ)
      ( bᵉ)
      ( cᵉ))
  where

  family-of-elements-comp-extension-dependent-double-lift-family-of-elementsᵉ :
    (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ → Dᵉ iᵉ xᵉ
  family-of-elements-comp-extension-dependent-double-lift-family-of-elementsᵉ
    iᵉ xᵉ =
    family-of-elements-extension-dependent-double-lift-family-of-elementsᵉ
      gᵉ iᵉ xᵉ ∘ᵉ
    family-of-elements-extension-dependent-double-lift-family-of-elementsᵉ
      fᵉ iᵉ xᵉ

  is-extension-comp-extension-dependent-double-lift-family-of-elementsᵉ :
    is-extension-dependent-double-lift-family-of-elementsᵉ
      ( λ iᵉ xᵉ _ → Dᵉ iᵉ xᵉ)
      ( bᵉ)
      ( dᵉ)
      ( family-of-elements-comp-extension-dependent-double-lift-family-of-elementsᵉ)
  is-extension-comp-extension-dependent-double-lift-family-of-elementsᵉ iᵉ =
    ( apᵉ
      ( family-of-elements-extension-dependent-double-lift-family-of-elementsᵉ
        gᵉ iᵉ (aᵉ iᵉ))
      ( is-extension-extension-dependent-double-lift-family-of-elementsᵉ fᵉ iᵉ)) ∙ᵉ
    ( is-extension-extension-dependent-double-lift-family-of-elementsᵉ gᵉ iᵉ)

  comp-extension-dependent-double-lift-family-of-elementsᵉ :
    extension-dependent-double-lift-family-of-elementsᵉ
      ( λ iᵉ xᵉ (ᵉ_ : Bᵉ iᵉ xᵉ) → Dᵉ iᵉ xᵉ)
      ( bᵉ)
      ( dᵉ)
  pr1ᵉ comp-extension-dependent-double-lift-family-of-elementsᵉ =
    family-of-elements-comp-extension-dependent-double-lift-family-of-elementsᵉ
  pr2ᵉ comp-extension-dependent-double-lift-family-of-elementsᵉ =
    is-extension-comp-extension-dependent-double-lift-family-of-elementsᵉ
```

### Composition of extensions of double lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  {Cᵉ : Aᵉ → UUᵉ l4ᵉ} {Dᵉ : Aᵉ → UUᵉ l5ᵉ}
  {aᵉ : Iᵉ → Aᵉ} {bᵉ : lift-family-of-elementsᵉ Bᵉ aᵉ}
  {cᵉ : lift-family-of-elementsᵉ Cᵉ aᵉ} {dᵉ : lift-family-of-elementsᵉ Dᵉ aᵉ}
  (gᵉ : extension-double-lift-family-of-elementsᵉ (λ xᵉ (ᵉ_ : Cᵉ xᵉ) → Dᵉ xᵉ) cᵉ dᵉ)
  (fᵉ : extension-double-lift-family-of-elementsᵉ (λ xᵉ (ᵉ_ : Bᵉ xᵉ) → Cᵉ xᵉ) bᵉ cᵉ)
  where

  family-of-elements-comp-extension-double-lift-family-of-elementsᵉ :
    (xᵉ : Aᵉ) → Bᵉ xᵉ → Dᵉ xᵉ
  family-of-elements-comp-extension-double-lift-family-of-elementsᵉ xᵉ =
    family-of-elements-extension-double-lift-family-of-elementsᵉ gᵉ xᵉ ∘ᵉ
    family-of-elements-extension-double-lift-family-of-elementsᵉ fᵉ xᵉ

  is-extension-comp-extension-double-lift-family-of-elementsᵉ :
    is-extension-double-lift-family-of-elementsᵉ
      ( λ xᵉ _ → Dᵉ xᵉ)
      ( bᵉ)
      ( dᵉ)
      ( family-of-elements-comp-extension-double-lift-family-of-elementsᵉ)
  is-extension-comp-extension-double-lift-family-of-elementsᵉ iᵉ =
    ( apᵉ
      ( family-of-elements-extension-double-lift-family-of-elementsᵉ gᵉ (aᵉ iᵉ))
      ( is-extension-extension-double-lift-family-of-elementsᵉ fᵉ iᵉ)) ∙ᵉ
    ( is-extension-extension-double-lift-family-of-elementsᵉ gᵉ iᵉ)

  comp-extension-double-lift-family-of-elementsᵉ :
    extension-double-lift-family-of-elementsᵉ (λ xᵉ (ᵉ_ : Bᵉ xᵉ) → Dᵉ xᵉ) bᵉ dᵉ
  pr1ᵉ comp-extension-double-lift-family-of-elementsᵉ =
    family-of-elements-comp-extension-double-lift-family-of-elementsᵉ
  pr2ᵉ comp-extension-double-lift-family-of-elementsᵉ =
    is-extension-comp-extension-double-lift-family-of-elementsᵉ
```

## See also

-ᵉ [Extensionsᵉ ofᵉ liftsᵉ ofᵉ familiesᵉ ofᵉ elements](orthogonal-factorization-systems.extensions-lifts-families-of-elements.mdᵉ)
-ᵉ [Extensionsᵉ ofᵉ maps](orthogonal-factorization-systems.extensions-of-maps.mdᵉ)
-ᵉ [Theᵉ universalᵉ propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ fibersᵉ ofᵉ aᵉ map](foundation.universal-property-family-of-fibers-of-maps.mdᵉ)
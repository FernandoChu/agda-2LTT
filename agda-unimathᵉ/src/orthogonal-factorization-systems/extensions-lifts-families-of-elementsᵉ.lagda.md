# Extensions of families of elements

```agda
module
  orthogonal-factorization-systems.extensions-lifts-families-of-elementsᵉ
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

open import orthogonal-factorization-systems.lifts-families-of-elementsᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ ofᵉ elementsᵉ `aᵉ : Iᵉ → A`,ᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ andᵉ aᵉ
[lift](orthogonal-factorization-systems.lifts-families-of-elements.mdᵉ)

```text
  bᵉ : (iᵉ : Iᵉ) → Bᵉ (aᵉ iᵉ)
```

ofᵉ theᵉ familyᵉ ofᵉ elementsᵉ `a`.ᵉ Anᵉ
{{#conceptᵉ "extension"ᵉ Disambiguation="familyᵉ ofᵉ elements"ᵉ Agda=extension-lift-family-of-elementsᵉ}}
ofᵉ `b`ᵉ to `A`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ elementsᵉ `fᵉ : (xᵉ : Aᵉ) → Bᵉ x`ᵉ equippedᵉ with
aᵉ [homotopy](foundation-core.homotopies.mdᵉ) `fᵉ ∘ᵉ aᵉ ~ᵉ b`.ᵉ

Moreᵉ generally,ᵉ givenᵉ aᵉ familyᵉ ofᵉ elementsᵉ `aᵉ : (iᵉ : Iᵉ) → Aᵉ i`,ᵉ aᵉ typeᵉ familyᵉ
`B`ᵉ overᵉ `A`,ᵉ andᵉ aᵉ dependentᵉ liftᵉ

```text
  bᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ (aᵉ iᵉ)
```

ofᵉ theᵉ familyᵉ ofᵉ elementsᵉ `A`,ᵉ aᵉ
{{#conceptᵉ "dependentᵉ extension"ᵉ Disambiguation"familyᵉ ofᵉ elements"ᵉ Agda=extension-dependent-lift-family-of-elementsᵉ}}
ofᵉ `b`ᵉ to `A`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ elementsᵉ

```text
  fᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ
```

equippedᵉ with aᵉ homotopyᵉ `(iᵉ : Iᵉ) → fᵉ iᵉ (aᵉ iᵉ) ＝ᵉ bᵉ i`.ᵉ

## Definitions

### Evaluating families of elements at lifts of families of elements

Anyᵉ familyᵉ ofᵉ elementsᵉ `aᵉ : (iᵉ : Iᵉ) → Aᵉ i`ᵉ inducesᵉ anᵉ evaluationᵉ mapᵉ

```text
  ((iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ) → ((iᵉ : Iᵉ) → Bᵉ iᵉ (aᵉ iᵉ))
```

definedᵉ byᵉ `bᵉ ↦ᵉ (λ iᵉ → bᵉ iᵉ (aᵉ i))`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ}
  (aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ)
  where

  ev-dependent-lift-family-of-elementsᵉ :
    ((iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ) → dependent-lift-family-of-elementsᵉ Bᵉ aᵉ
  ev-dependent-lift-family-of-elementsᵉ bᵉ iᵉ = bᵉ iᵉ (aᵉ iᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ} (aᵉ : Iᵉ → Aᵉ)
  where

  ev-lift-family-of-elementsᵉ :
    ((xᵉ : Aᵉ) → Bᵉ xᵉ) → lift-family-of-elementsᵉ Bᵉ aᵉ
  ev-lift-family-of-elementsᵉ bᵉ iᵉ = bᵉ (aᵉ iᵉ)
```

### Dependent extensions of dependent lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} (Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ)
  (aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ) (bᵉ : dependent-lift-family-of-elementsᵉ Bᵉ aᵉ)
  where

  is-extension-dependent-lift-family-of-elementsᵉ :
    (fᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  is-extension-dependent-lift-family-of-elementsᵉ fᵉ =
    ev-dependent-lift-family-of-elementsᵉ aᵉ fᵉ ~ᵉ bᵉ

  extension-dependent-lift-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  extension-dependent-lift-family-of-elementsᵉ =
    Σᵉ ((iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ) is-extension-dependent-lift-family-of-elementsᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ}
  {aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ} {bᵉ : dependent-lift-family-of-elementsᵉ Bᵉ aᵉ}
  (fᵉ : extension-dependent-lift-family-of-elementsᵉ Bᵉ aᵉ bᵉ)
  where

  family-of-elements-extension-dependent-lift-family-of-elementsᵉ :
    (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ
  family-of-elements-extension-dependent-lift-family-of-elementsᵉ = pr1ᵉ fᵉ

  is-extension-extension-dependent-lift-family-of-elementsᵉ :
    is-extension-dependent-lift-family-of-elementsᵉ Bᵉ aᵉ bᵉ
      ( family-of-elements-extension-dependent-lift-family-of-elementsᵉ)
  is-extension-extension-dependent-lift-family-of-elementsᵉ = pr2ᵉ fᵉ
```

### Extensions of lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ)
  (aᵉ : Iᵉ → Aᵉ) (bᵉ : lift-family-of-elementsᵉ Bᵉ aᵉ)
  where

  is-extension-lift-family-of-elementsᵉ : (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  is-extension-lift-family-of-elementsᵉ fᵉ = ev-lift-family-of-elementsᵉ aᵉ fᵉ ~ᵉ bᵉ

  extension-lift-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  extension-lift-family-of-elementsᵉ =
    Σᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) is-extension-lift-family-of-elementsᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  {aᵉ : Iᵉ → Aᵉ} {bᵉ : lift-family-of-elementsᵉ Bᵉ aᵉ}
  (fᵉ : extension-lift-family-of-elementsᵉ Bᵉ aᵉ bᵉ)
  where

  family-of-elements-extension-lift-family-of-elementsᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ
  family-of-elements-extension-lift-family-of-elementsᵉ = pr1ᵉ fᵉ

  is-extension-extension-lift-family-of-elementsᵉ :
    is-extension-lift-family-of-elementsᵉ Bᵉ aᵉ bᵉ
      ( family-of-elements-extension-lift-family-of-elementsᵉ)
  is-extension-extension-lift-family-of-elementsᵉ = pr2ᵉ fᵉ
```

### Identity extensions of dependent lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} (aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ)
  where

  id-extension-dependent-lift-family-of-elementsᵉ :
    extension-dependent-lift-family-of-elementsᵉ (λ iᵉ _ → Aᵉ iᵉ) aᵉ aᵉ
  pr1ᵉ id-extension-dependent-lift-family-of-elementsᵉ iᵉ = idᵉ
  pr2ᵉ id-extension-dependent-lift-family-of-elementsᵉ = refl-htpyᵉ
```

### Identity extensions of lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (aᵉ : Iᵉ → Aᵉ)
  where

  id-extension-lift-family-of-elementsᵉ :
    extension-lift-family-of-elementsᵉ (λ _ → Aᵉ) aᵉ aᵉ
  pr1ᵉ id-extension-lift-family-of-elementsᵉ = idᵉ
  pr2ᵉ id-extension-lift-family-of-elementsᵉ = refl-htpyᵉ
```

### Composition of extensions of dependent lifts of families of elements

Considerᵉ threeᵉ typeᵉ familiesᵉ `A`,ᵉ `B`,ᵉ andᵉ `C`ᵉ overᵉ aᵉ typeᵉ `I`ᵉ equippedᵉ with
sectionsᵉ

```text
  aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ
  bᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ
  cᵉ : (iᵉ : Iᵉ) → Cᵉ i.ᵉ
```

Furthermore,ᵉ supposeᵉ thatᵉ `g`ᵉ isᵉ anᵉ extensionᵉ ofᵉ `c`ᵉ alongᵉ `b`,ᵉ andᵉ supposeᵉ thatᵉ
`f`ᵉ isᵉ anᵉ extensionᵉ ofᵉ `b`ᵉ alongᵉ `a`.ᵉ Inᵉ otherᵉ words,ᵉ `g`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ
ofᵉ mapsᵉ

```text
  gᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ → Cᵉ iᵉ
```

equippedᵉ with aᵉ homotopyᵉ witnessingᵉ thatᵉ `gᵉ iᵉ (bᵉ iᵉ) ＝ᵉ cᵉ i`ᵉ forᵉ allᵉ `iᵉ : I`,ᵉ andᵉ
`f`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ mapsᵉ

```text
  fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ
```

equippedᵉ with aᵉ homotopyᵉ witnessingᵉ thatᵉ `fᵉ iᵉ (aᵉ iᵉ) ＝ᵉ bᵉ i`ᵉ forᵉ allᵉ `iᵉ : I`.ᵉ
Thenᵉ weᵉ canᵉ composeᵉ `g`ᵉ andᵉ `f`ᵉ fiberwise,ᵉ resultingᵉ in aᵉ familyᵉ ofᵉ mapsᵉ

```text
  λ iᵉ → gᵉ iᵉ ∘ᵉ fᵉ iᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Cᵉ iᵉ
```

equippedᵉ with aᵉ homotopyᵉ witnessingᵉ thatᵉ `gᵉ iᵉ (fᵉ iᵉ (aᵉ iᵉ)) ＝ᵉ cᵉ i`ᵉ forᵉ allᵉ
`iᵉ : I`.ᵉ Inᵉ otherᵉ words,ᵉ extensionsᵉ ofᵉ `c`ᵉ alongᵉ `b`ᵉ canᵉ beᵉ composedᵉ with
extensionsᵉ ofᵉ `b`ᵉ alongᵉ `a`ᵉ to obtainᵉ extensionsᵉ ofᵉ `c`ᵉ alongᵉ `a`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} {Cᵉ : Iᵉ → UUᵉ l4ᵉ}
  {aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ} {bᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ} {cᵉ : (iᵉ : Iᵉ) → Cᵉ iᵉ}
  (gᵉ : extension-dependent-lift-family-of-elementsᵉ (λ iᵉ _ → Cᵉ iᵉ) bᵉ cᵉ)
  (fᵉ : extension-dependent-lift-family-of-elementsᵉ (λ iᵉ _ → Bᵉ iᵉ) aᵉ bᵉ)
  where

  family-of-elements-comp-extension-dependent-lift-family-of-elementsᵉ :
    (iᵉ : Iᵉ) → Aᵉ iᵉ → Cᵉ iᵉ
  family-of-elements-comp-extension-dependent-lift-family-of-elementsᵉ iᵉ =
    family-of-elements-extension-dependent-lift-family-of-elementsᵉ gᵉ iᵉ ∘ᵉ
    family-of-elements-extension-dependent-lift-family-of-elementsᵉ fᵉ iᵉ

  is-extension-comp-extension-dependent-lift-family-of-elementsᵉ :
    is-extension-dependent-lift-family-of-elementsᵉ
      ( λ iᵉ _ → Cᵉ iᵉ)
      ( aᵉ)
      ( cᵉ)
      ( family-of-elements-comp-extension-dependent-lift-family-of-elementsᵉ)
  is-extension-comp-extension-dependent-lift-family-of-elementsᵉ iᵉ =
    ( apᵉ
      ( family-of-elements-extension-dependent-lift-family-of-elementsᵉ gᵉ iᵉ)
      ( is-extension-extension-dependent-lift-family-of-elementsᵉ fᵉ iᵉ)) ∙ᵉ
    ( is-extension-extension-dependent-lift-family-of-elementsᵉ gᵉ iᵉ)

  comp-extension-dependent-lift-family-of-elementsᵉ :
    extension-dependent-lift-family-of-elementsᵉ (λ iᵉ _ → Cᵉ iᵉ) aᵉ cᵉ
  pr1ᵉ comp-extension-dependent-lift-family-of-elementsᵉ =
    family-of-elements-comp-extension-dependent-lift-family-of-elementsᵉ
  pr2ᵉ comp-extension-dependent-lift-family-of-elementsᵉ =
    is-extension-comp-extension-dependent-lift-family-of-elementsᵉ
```

### Composition of extensions of lifts of families of elements

Considerᵉ threeᵉ typesᵉ `A`,ᵉ `B`,ᵉ andᵉ `C`ᵉ equippedᵉ with mapsᵉ

```text
  aᵉ : Iᵉ → Aᵉ
  bᵉ : Iᵉ → Bᵉ
  cᵉ : Iᵉ → C.ᵉ
```

Furthermore,ᵉ supposeᵉ thatᵉ `g`ᵉ isᵉ anᵉ extensionᵉ ofᵉ `c`ᵉ alongᵉ `b`,ᵉ andᵉ supposeᵉ thatᵉ
`f`ᵉ isᵉ anᵉ extensionᵉ ofᵉ `b`ᵉ alongᵉ `a`.ᵉ Inᵉ otherᵉ words,ᵉ weᵉ assumeᵉ aᵉ commutingᵉ
diagramᵉ

```text
        Iᵉ
      /ᵉ | \ᵉ
    a/ᵉ  |  \cᵉ
    /ᵉ   |bᵉ  \ᵉ
   ∨ᵉ    ∨ᵉ    ∨ᵉ
  Aᵉ -->ᵉ Bᵉ -->ᵉ Cᵉ
     fᵉ     gᵉ
```

Theᵉ compositeᵉ `gᵉ ∘ᵉ f`ᵉ isᵉ thenᵉ anᵉ extensionᵉ ofᵉ `c`ᵉ alongᵉ `a.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {aᵉ : Iᵉ → Aᵉ} {bᵉ : Iᵉ → Bᵉ} {cᵉ : Iᵉ → Cᵉ}
  (gᵉ : extension-lift-family-of-elementsᵉ (λ _ → Cᵉ) bᵉ cᵉ)
  (fᵉ : extension-lift-family-of-elementsᵉ (λ _ → Bᵉ) aᵉ bᵉ)
  where

  map-comp-extension-lift-family-of-elementsᵉ : Aᵉ → Cᵉ
  map-comp-extension-lift-family-of-elementsᵉ =
    family-of-elements-extension-lift-family-of-elementsᵉ gᵉ ∘ᵉ
    family-of-elements-extension-lift-family-of-elementsᵉ fᵉ

  is-extension-comp-extension-lift-family-of-elementsᵉ :
    is-extension-lift-family-of-elementsᵉ
      ( λ _ → Cᵉ)
      ( aᵉ)
      ( cᵉ)
      ( map-comp-extension-lift-family-of-elementsᵉ)
  is-extension-comp-extension-lift-family-of-elementsᵉ xᵉ =
    ( apᵉ
      ( family-of-elements-extension-lift-family-of-elementsᵉ gᵉ)
      ( is-extension-extension-lift-family-of-elementsᵉ fᵉ xᵉ)) ∙ᵉ
    ( is-extension-extension-lift-family-of-elementsᵉ gᵉ xᵉ)

  comp-extension-lift-family-of-elementsᵉ :
    extension-lift-family-of-elementsᵉ (λ _ → Cᵉ) aᵉ cᵉ
  pr1ᵉ comp-extension-lift-family-of-elementsᵉ =
    map-comp-extension-lift-family-of-elementsᵉ
  pr2ᵉ comp-extension-lift-family-of-elementsᵉ =
    is-extension-comp-extension-lift-family-of-elementsᵉ
```

## See also

-ᵉ [Extensionsᵉ ofᵉ doubleᵉ liftsᵉ ofᵉ familiesᵉ ofᵉ elements](orthogonal-factorization-systems.extensions-double-lifts-families-of-elements.mdᵉ)
-ᵉ [Extensionsᵉ ofᵉ maps](orthogonal-factorization-systems.extensions-of-maps.mdᵉ)
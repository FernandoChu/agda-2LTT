# The universal property of propositional truncations

```agda
module foundation.universal-property-propositional-truncationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.precomposition-functions-into-subuniversesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → P`ᵉ intoᵉ aᵉ [proposition](foundation-core.propositions.mdᵉ) `P`ᵉ isᵉ
saidᵉ to satisfyᵉ theᵉ
{{#conceptᵉ "universalᵉ propertyᵉ ofᵉ theᵉ propositionalᵉ truncation"ᵉ Agda=universal-property-propositional-truncationᵉ}}
ofᵉ `A`,ᵉ orᵉ isᵉ saidᵉ to beᵉ aᵉ
{{#conceptᵉ "propositionalᵉ truncation"ᵉ Agda=is-propositional-truncationᵉ}} ofᵉ `A`,ᵉ
ifᵉ anyᵉ mapᵉ `gᵉ : Aᵉ → Q`ᵉ intoᵉ aᵉ propositionᵉ `Q`ᵉ extendsᵉ uniquelyᵉ alongᵉ `f`.ᵉ

## Definition

### The condition of being a propositional truncation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ)
  where

  precomp-Propᵉ :
    {l3ᵉ : Level} (Qᵉ : Propᵉ l3ᵉ) →
    type-hom-Propᵉ Pᵉ Qᵉ → Aᵉ → type-Propᵉ Qᵉ
  precomp-Propᵉ Qᵉ gᵉ = gᵉ ∘ᵉ fᵉ

  is-propositional-truncationᵉ : UUωᵉ
  is-propositional-truncationᵉ =
    {lᵉ : Level} (Qᵉ : Propᵉ lᵉ) → is-equivᵉ (precomp-Propᵉ Qᵉ)
```

### The universal property of the propositional truncation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ)
  where

  universal-property-propositional-truncationᵉ : UUωᵉ
  universal-property-propositional-truncationᵉ =
    {lᵉ : Level} (Qᵉ : Propᵉ lᵉ) (gᵉ : Aᵉ → type-Propᵉ Qᵉ) →
    is-contrᵉ (Σᵉ (type-hom-Propᵉ Pᵉ Qᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ~ᵉ gᵉ))
```

### Extension property of the propositional truncation

Thisᵉ isᵉ aᵉ simplifiedᵉ formᵉ ofᵉ theᵉ universalᵉ properties,ᵉ thatᵉ worksᵉ becauseᵉ we'reᵉ
mappingᵉ intoᵉ propositions.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ)
  where

  extension-property-propositional-truncationᵉ : UUωᵉ
  extension-property-propositional-truncationᵉ =
    {lᵉ : Level} (Qᵉ : Propᵉ lᵉ) → (Aᵉ → type-Propᵉ Qᵉ) → type-hom-Propᵉ Pᵉ Qᵉ
```

### The dependent universal property of the propositional truncation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ)
  where

  dependent-universal-property-propositional-truncationᵉ : UUωᵉ
  dependent-universal-property-propositional-truncationᵉ =
    {lᵉ : Level} → (Qᵉ : type-Propᵉ Pᵉ → Propᵉ lᵉ) →
    is-equivᵉ (precomp-Πᵉ fᵉ (type-Propᵉ ∘ᵉ Qᵉ))
```

## Properties

### Being a propositional trunction is equivalent to satisfying the universal property of the propositional truncation

```agda
abstract
  universal-property-is-propositional-truncationᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    is-propositional-truncationᵉ Pᵉ fᵉ →
    universal-property-propositional-truncationᵉ Pᵉ fᵉ
  universal-property-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ Qᵉ gᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (type-hom-Propᵉ Pᵉ Qᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ＝ᵉ gᵉ))
      ( equiv-totᵉ (λ _ → equiv-funextᵉ))
      ( is-contr-map-is-equivᵉ (is-ptr-fᵉ Qᵉ) gᵉ)

abstract
  map-is-propositional-truncationᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    is-propositional-truncationᵉ Pᵉ fᵉ →
    (Qᵉ : Propᵉ l3ᵉ) (gᵉ : Aᵉ → type-Propᵉ Qᵉ) → type-hom-Propᵉ Pᵉ Qᵉ
  map-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ Qᵉ gᵉ =
    pr1ᵉ
      ( centerᵉ
        ( universal-property-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ Qᵉ gᵉ))

  htpy-is-propositional-truncationᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    (is-ptr-fᵉ : is-propositional-truncationᵉ Pᵉ fᵉ) →
    (Qᵉ : Propᵉ l3ᵉ) (gᵉ : Aᵉ → type-Propᵉ Qᵉ) →
    map-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ Qᵉ gᵉ ∘ᵉ fᵉ ~ᵉ gᵉ
  htpy-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ Qᵉ gᵉ =
    pr2ᵉ
      ( centerᵉ
        ( universal-property-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ Qᵉ gᵉ))

abstract
  is-propositional-truncation-universal-propertyᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
    (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    universal-property-propositional-truncationᵉ Pᵉ fᵉ →
    is-propositional-truncationᵉ Pᵉ fᵉ
  is-propositional-truncation-universal-propertyᵉ Pᵉ fᵉ up-fᵉ Qᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ gᵉ → is-contr-equivᵉ
        ( Σᵉ (type-hom-Propᵉ Pᵉ Qᵉ) (λ hᵉ → (hᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ))
        ( equiv-totᵉ (λ hᵉ → equiv-funextᵉ))
        ( up-fᵉ Qᵉ gᵉ))
```

### Being a propositional truncation is equivalent to satisfying the extension property of propositional truncations

```agda
abstract
  is-propositional-truncation-extension-propertyᵉ :
    { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ)
    ( fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    extension-property-propositional-truncationᵉ Pᵉ fᵉ →
    is-propositional-truncationᵉ Pᵉ fᵉ
  is-propositional-truncation-extension-propertyᵉ Pᵉ fᵉ up-Pᵉ Qᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-Πᵉ (λ xᵉ → is-prop-type-Propᵉ Qᵉ))
      ( is-prop-Πᵉ (λ xᵉ → is-prop-type-Propᵉ Qᵉ))
      ( up-Pᵉ Qᵉ)
```

### Uniqueness of propositional truncations

```agda
abstract
  is-equiv-is-ptruncation-is-ptruncationᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (P'ᵉ : Propᵉ l3ᵉ)
    (fᵉ : Aᵉ → type-Propᵉ Pᵉ) (f'ᵉ : Aᵉ → type-Propᵉ P'ᵉ)
    (hᵉ : type-hom-Propᵉ Pᵉ P'ᵉ) (Hᵉ : (hᵉ ∘ᵉ fᵉ) ~ᵉ f'ᵉ) →
    is-propositional-truncationᵉ Pᵉ fᵉ →
    is-propositional-truncationᵉ P'ᵉ f'ᵉ →
    is-equivᵉ hᵉ
  is-equiv-is-ptruncation-is-ptruncationᵉ Pᵉ P'ᵉ fᵉ f'ᵉ hᵉ Hᵉ is-ptr-Pᵉ is-ptr-P'ᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-type-Propᵉ Pᵉ)
      ( is-prop-type-Propᵉ P'ᵉ)
      ( map-inv-is-equivᵉ (is-ptr-P'ᵉ Pᵉ) fᵉ)

abstract
  is-ptruncation-is-ptruncation-is-equivᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (P'ᵉ : Propᵉ l3ᵉ)
    (fᵉ : Aᵉ → type-Propᵉ Pᵉ) (f'ᵉ : Aᵉ → type-Propᵉ P'ᵉ) (hᵉ : type-hom-Propᵉ Pᵉ P'ᵉ) →
    is-equivᵉ hᵉ → is-propositional-truncationᵉ Pᵉ fᵉ →
    is-propositional-truncationᵉ P'ᵉ f'ᵉ
  is-ptruncation-is-ptruncation-is-equivᵉ Pᵉ P'ᵉ fᵉ f'ᵉ hᵉ is-equiv-hᵉ is-ptr-fᵉ =
    is-propositional-truncation-extension-propertyᵉ P'ᵉ f'ᵉ
      ( λ Rᵉ gᵉ →
        ( map-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ Rᵉ gᵉ) ∘ᵉ
        ( map-inv-is-equivᵉ is-equiv-hᵉ))

abstract
  is-ptruncation-is-equiv-is-ptruncationᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (P'ᵉ : Propᵉ l3ᵉ)
    (fᵉ : Aᵉ → type-Propᵉ Pᵉ) (f'ᵉ : Aᵉ → type-Propᵉ P'ᵉ) (hᵉ : type-hom-Propᵉ Pᵉ P'ᵉ) →
    is-propositional-truncationᵉ P'ᵉ f'ᵉ → is-equivᵉ hᵉ →
    is-propositional-truncationᵉ Pᵉ fᵉ
  is-ptruncation-is-equiv-is-ptruncationᵉ Pᵉ P'ᵉ fᵉ f'ᵉ hᵉ is-ptr-f'ᵉ is-equiv-hᵉ =
    is-propositional-truncation-extension-propertyᵉ Pᵉ fᵉ
      ( λ Rᵉ gᵉ → (map-is-propositional-truncationᵉ P'ᵉ f'ᵉ is-ptr-f'ᵉ Rᵉ gᵉ) ∘ᵉ hᵉ)

abstract
  is-uniquely-unique-propositional-truncationᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (P'ᵉ : Propᵉ l3ᵉ)
    (fᵉ : Aᵉ → type-Propᵉ Pᵉ) (f'ᵉ : Aᵉ → type-Propᵉ P'ᵉ) →
    is-propositional-truncationᵉ Pᵉ fᵉ →
    is-propositional-truncationᵉ P'ᵉ f'ᵉ →
    is-contrᵉ (Σᵉ (type-equiv-Propᵉ Pᵉ P'ᵉ) (λ eᵉ → (map-equivᵉ eᵉ ∘ᵉ fᵉ) ~ᵉ f'ᵉ))
  is-uniquely-unique-propositional-truncationᵉ Pᵉ P'ᵉ fᵉ f'ᵉ is-ptr-fᵉ is-ptr-f'ᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( universal-property-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ P'ᵉ f'ᵉ)
      ( is-property-is-equivᵉ)
      ( map-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ P'ᵉ f'ᵉ)
      ( htpy-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ P'ᵉ f'ᵉ)
      ( is-equiv-is-ptruncation-is-ptruncationᵉ Pᵉ P'ᵉ fᵉ f'ᵉ
        ( map-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ P'ᵉ f'ᵉ)
        ( htpy-is-propositional-truncationᵉ Pᵉ fᵉ is-ptr-fᵉ P'ᵉ f'ᵉ)
        ( λ {lᵉ} → is-ptr-fᵉ)
        ( λ {lᵉ} → is-ptr-f'ᵉ))
```

### A map `f : A → P` is a propositional truncation if and only if it satisfies the dependent universal property of the propositional truncation

```agda
abstract
  dependent-universal-property-is-propositional-truncationᵉ :
    { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    is-propositional-truncationᵉ Pᵉ fᵉ →
    dependent-universal-property-propositional-truncationᵉ Pᵉ fᵉ
  dependent-universal-property-is-propositional-truncationᵉ
    {l1ᵉ} {l2ᵉ} {Aᵉ} Pᵉ fᵉ is-ptr-fᵉ Qᵉ =
    is-fiberwise-equiv-is-equiv-map-Σᵉ
      ( λ (gᵉ : Aᵉ → type-Propᵉ Pᵉ) → (xᵉ : Aᵉ) → type-Propᵉ (Qᵉ (gᵉ xᵉ)))
      ( precompᵉ fᵉ (type-Propᵉ Pᵉ))
      ( λ hᵉ → precomp-Πᵉ fᵉ (λ pᵉ → type-Propᵉ (Qᵉ (hᵉ pᵉ))))
      ( is-ptr-fᵉ Pᵉ)
      ( is-equiv-top-is-equiv-bottom-squareᵉ
        ( map-inv-distributive-Π-Σᵉ
          { Cᵉ = λ (xᵉ : type-Propᵉ Pᵉ) (pᵉ : type-Propᵉ Pᵉ) → type-Propᵉ (Qᵉ pᵉ)})
        ( map-inv-distributive-Π-Σᵉ
          { Cᵉ = λ (xᵉ : Aᵉ) (pᵉ : type-Propᵉ Pᵉ) → type-Propᵉ (Qᵉ pᵉ)})
        ( map-Σᵉ
          ( λ (gᵉ : Aᵉ → type-Propᵉ Pᵉ) → (xᵉ : Aᵉ) → type-Propᵉ (Qᵉ (gᵉ xᵉ)))
          ( precompᵉ fᵉ (type-Propᵉ Pᵉ))
          ( λ hᵉ → precomp-Πᵉ fᵉ (λ pᵉ → type-Propᵉ (Qᵉ (hᵉ pᵉ)))))
        ( precompᵉ fᵉ (Σᵉ (type-Propᵉ Pᵉ) (λ pᵉ → type-Propᵉ (Qᵉ pᵉ))))
        ( ind-Σᵉ (λ hᵉ h'ᵉ → reflᵉ))
        ( is-equiv-map-inv-distributive-Π-Σᵉ)
        ( is-equiv-map-inv-distributive-Π-Σᵉ)
        ( is-ptr-fᵉ (Σ-Propᵉ Pᵉ Qᵉ)))
      ( idᵉ {Aᵉ = type-Propᵉ Pᵉ})

abstract
  is-propositional-truncation-dependent-universal-propertyᵉ :
    { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    dependent-universal-property-propositional-truncationᵉ Pᵉ fᵉ →
    is-propositional-truncationᵉ Pᵉ fᵉ
  is-propositional-truncation-dependent-universal-propertyᵉ Pᵉ fᵉ dup-fᵉ Qᵉ =
    dup-fᵉ (λ pᵉ → Qᵉ)
```

### Any map `f : A → P` that has a section is a propositional truncation

```agda
abstract
  is-propositional-truncation-has-sectionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    (gᵉ : type-Propᵉ Pᵉ → Aᵉ) → is-propositional-truncationᵉ Pᵉ fᵉ
  is-propositional-truncation-has-sectionᵉ {Aᵉ = Aᵉ} Pᵉ fᵉ gᵉ Qᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-function-typeᵉ (is-prop-type-Propᵉ Qᵉ))
      ( is-prop-function-typeᵉ (is-prop-type-Propᵉ Qᵉ))
      ( λ hᵉ → hᵉ ∘ᵉ gᵉ)
```

### If `A` is a pointed type, then the map `A → unit` is a propositional truncation

```agda
abstract
  is-propositional-truncation-terminal-mapᵉ :
    { l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (aᵉ : Aᵉ) →
    is-propositional-truncationᵉ unit-Propᵉ (terminal-mapᵉ Aᵉ)
  is-propositional-truncation-terminal-mapᵉ Aᵉ aᵉ =
    is-propositional-truncation-has-sectionᵉ
      ( unit-Propᵉ)
      ( terminal-mapᵉ Aᵉ)
      ( ind-unitᵉ aᵉ)
```

### Any map between propositions is a propositional truncation if and only if it is an equivalence

```agda
abstract
  is-propositional-truncation-is-equivᵉ :
    {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
    {fᵉ : type-hom-Propᵉ Pᵉ Qᵉ} →
    is-equivᵉ fᵉ → is-propositional-truncationᵉ Qᵉ fᵉ
  is-propositional-truncation-is-equivᵉ Pᵉ Qᵉ {fᵉ} is-equiv-fᵉ Rᵉ =
    is-equiv-precomp-is-equivᵉ fᵉ is-equiv-fᵉ (type-Propᵉ Rᵉ)

abstract
  is-propositional-truncation-map-equivᵉ :
    { l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
    (eᵉ : type-equiv-Propᵉ Pᵉ Qᵉ) →
    is-propositional-truncationᵉ Qᵉ (map-equivᵉ eᵉ)
  is-propositional-truncation-map-equivᵉ Pᵉ Qᵉ eᵉ Rᵉ =
    is-equiv-precomp-is-equivᵉ (map-equivᵉ eᵉ) (is-equiv-map-equivᵉ eᵉ) (type-Propᵉ Rᵉ)

abstract
  is-equiv-is-propositional-truncationᵉ :
    {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) {fᵉ : type-hom-Propᵉ Pᵉ Qᵉ} →
    is-propositional-truncationᵉ Qᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-propositional-truncationᵉ Pᵉ Qᵉ {fᵉ} Hᵉ =
    is-equiv-is-equiv-precomp-Propᵉ Pᵉ Qᵉ fᵉ Hᵉ
```

### The identity map on a proposition is a propositional truncation

```agda
abstract
  is-propositional-truncation-idᵉ :
    { l1ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) →
    is-propositional-truncationᵉ Pᵉ idᵉ
  is-propositional-truncation-idᵉ Pᵉ Qᵉ = is-equiv-idᵉ
```

### A product of propositional truncations is a propositional truncation

```agda
abstract
  is-propositional-truncation-productᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ)
    {A'ᵉ : UUᵉ l3ᵉ} (P'ᵉ : Propᵉ l4ᵉ) (f'ᵉ : A'ᵉ → type-Propᵉ P'ᵉ) →
    is-propositional-truncationᵉ Pᵉ fᵉ →
    is-propositional-truncationᵉ P'ᵉ f'ᵉ →
    is-propositional-truncationᵉ (product-Propᵉ Pᵉ P'ᵉ) (map-productᵉ fᵉ f'ᵉ)
  is-propositional-truncation-productᵉ Pᵉ fᵉ P'ᵉ f'ᵉ is-ptr-fᵉ is-ptr-f'ᵉ Qᵉ =
    is-equiv-top-is-equiv-bottom-squareᵉ
      ( ev-pairᵉ)
      ( ev-pairᵉ)
      ( precompᵉ (map-productᵉ fᵉ f'ᵉ) (type-Propᵉ Qᵉ))
      ( λ hᵉ aᵉ a'ᵉ → hᵉ (fᵉ aᵉ) (f'ᵉ a'ᵉ))
      ( refl-htpyᵉ)
      ( is-equiv-ev-pairᵉ)
      ( is-equiv-ev-pairᵉ)
      ( is-equiv-compᵉ
        ( λ hᵉ aᵉ a'ᵉ → hᵉ aᵉ (f'ᵉ a'ᵉ))
        ( λ hᵉ aᵉ p'ᵉ → hᵉ (fᵉ aᵉ) p'ᵉ)
        ( is-ptr-fᵉ (pairᵉ (type-hom-Propᵉ P'ᵉ Qᵉ) (is-prop-hom-Propᵉ P'ᵉ Qᵉ)))
        ( is-equiv-map-Π-is-fiberwise-equivᵉ
          ( λ aᵉ → is-ptr-f'ᵉ Qᵉ)))
```
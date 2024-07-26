# The universal property of set truncations

```agda
module foundation.universal-property-set-truncationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.mere-equalityᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ intoᵉ aᵉ [set](foundation-core.sets.mdᵉ) `B`ᵉ satisfiesᵉ **theᵉ
universalᵉ propertyᵉ ofᵉ theᵉ setᵉ truncationᵉ ofᵉ `A`**ᵉ ifᵉ anyᵉ mapᵉ `Aᵉ → C`ᵉ intoᵉ aᵉ setᵉ
`C`ᵉ extendsᵉ uniquelyᵉ alongᵉ `f`ᵉ to aᵉ mapᵉ `Bᵉ → C`.ᵉ

## Definition

### The condition for a map into a set to be a set truncation

```agda
is-set-truncationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) → (Aᵉ → type-Setᵉ Bᵉ) → UUωᵉ
is-set-truncationᵉ Bᵉ fᵉ =
  {lᵉ : Level} (Cᵉ : Setᵉ lᵉ) → is-equivᵉ (precomp-Setᵉ fᵉ Cᵉ)
```

### The universal property of set truncations

```agda
universal-property-set-truncationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) → UUωᵉ
universal-property-set-truncationᵉ {Aᵉ = Aᵉ} Bᵉ fᵉ =
  {lᵉ : Level} (Cᵉ : Setᵉ lᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ) →
  is-contrᵉ (Σᵉ (hom-Setᵉ Bᵉ Cᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ~ᵉ gᵉ))
```

### The dependent universal property of set truncations

```agda
precomp-Π-Setᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Bᵉ → Setᵉ l3ᵉ) →
  ((bᵉ : Bᵉ) → type-Setᵉ (Cᵉ bᵉ)) → ((aᵉ : Aᵉ) → type-Setᵉ (Cᵉ (fᵉ aᵉ)))
precomp-Π-Setᵉ fᵉ Cᵉ hᵉ aᵉ = hᵉ (fᵉ aᵉ)

dependent-universal-property-set-truncationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) → UUωᵉ
dependent-universal-property-set-truncationᵉ Bᵉ fᵉ =
  {lᵉ : Level} (Xᵉ : type-Setᵉ Bᵉ → Setᵉ lᵉ) → is-equivᵉ (precomp-Π-Setᵉ fᵉ Xᵉ)
```

## Properties

### A map into a set is a set truncation if it satisfies the universal property

```agda
abstract
  is-set-truncation-universal-propertyᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    universal-property-set-truncationᵉ Bᵉ fᵉ →
    is-set-truncationᵉ Bᵉ fᵉ
  is-set-truncation-universal-propertyᵉ Bᵉ fᵉ up-fᵉ Cᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ gᵉ → is-contr-equivᵉ
        ( Σᵉ (hom-Setᵉ Bᵉ Cᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ~ᵉ gᵉ))
        ( equiv-totᵉ (λ hᵉ → equiv-funextᵉ))
        ( up-fᵉ Cᵉ gᵉ))
```

### A map into a set satisfies the universal property if it is a set truncation

```agda
abstract
  universal-property-is-set-truncationᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    is-set-truncationᵉ Bᵉ fᵉ → universal-property-set-truncationᵉ Bᵉ fᵉ
  universal-property-is-set-truncationᵉ Bᵉ fᵉ is-settr-fᵉ Cᵉ gᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (hom-Setᵉ Bᵉ Cᵉ) (λ hᵉ → (hᵉ ∘ᵉ fᵉ) ＝ᵉ gᵉ))
      ( equiv-totᵉ (λ hᵉ → equiv-funextᵉ))
      ( is-contr-map-is-equivᵉ (is-settr-fᵉ Cᵉ) gᵉ)

map-is-set-truncationᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
  is-set-truncationᵉ Bᵉ fᵉ → (Cᵉ : Setᵉ l3ᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ) → hom-Setᵉ Bᵉ Cᵉ
map-is-set-truncationᵉ Bᵉ fᵉ is-settr-fᵉ Cᵉ gᵉ =
  pr1ᵉ (centerᵉ (universal-property-is-set-truncationᵉ Bᵉ fᵉ is-settr-fᵉ Cᵉ gᵉ))

triangle-is-set-truncationᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
  (is-settr-fᵉ : is-set-truncationᵉ Bᵉ fᵉ) →
  (Cᵉ : Setᵉ l3ᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ) →
  map-is-set-truncationᵉ Bᵉ fᵉ is-settr-fᵉ Cᵉ gᵉ ∘ᵉ fᵉ ~ᵉ gᵉ
triangle-is-set-truncationᵉ Bᵉ fᵉ is-settr-fᵉ Cᵉ gᵉ =
  pr2ᵉ (centerᵉ (universal-property-is-set-truncationᵉ Bᵉ fᵉ is-settr-fᵉ Cᵉ gᵉ))
```

### The identity function on any set is a set truncation

```agda
abstract
  is-set-truncation-idᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : is-setᵉ Aᵉ) → is-set-truncationᵉ (Aᵉ ,ᵉ Hᵉ) idᵉ
  is-set-truncation-idᵉ Hᵉ Bᵉ =
    is-equiv-precomp-is-equivᵉ idᵉ is-equiv-idᵉ (type-Setᵉ Bᵉ)
```

### Any equivalence into a set is a set truncation

```agda
abstract
  is-set-truncation-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (eᵉ : Aᵉ ≃ᵉ type-Setᵉ Bᵉ) →
    is-set-truncationᵉ Bᵉ (map-equivᵉ eᵉ)
  is-set-truncation-equivᵉ Bᵉ eᵉ Cᵉ =
    is-equiv-precomp-is-equivᵉ (map-equivᵉ eᵉ) (is-equiv-map-equivᵉ eᵉ) (type-Setᵉ Cᵉ)
```

### Any set truncation satisfies the dependent universal property of the set truncation

```agda
abstract
  dependent-universal-property-is-set-truncationᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    is-set-truncationᵉ Bᵉ fᵉ →
    dependent-universal-property-set-truncationᵉ Bᵉ fᵉ
  dependent-universal-property-is-set-truncationᵉ {Aᵉ = Aᵉ} Bᵉ fᵉ Hᵉ Xᵉ =
    is-fiberwise-equiv-is-equiv-map-Σᵉ
      ( λ (hᵉ : Aᵉ → type-Setᵉ Bᵉ) → (aᵉ : Aᵉ) → type-Setᵉ (Xᵉ (hᵉ aᵉ)))
      ( λ (gᵉ : type-Setᵉ Bᵉ → type-Setᵉ Bᵉ) → gᵉ ∘ᵉ fᵉ)
      ( λ gᵉ (sᵉ : (bᵉ : type-Setᵉ Bᵉ) → type-Setᵉ (Xᵉ (gᵉ bᵉ))) (aᵉ : Aᵉ) → sᵉ (fᵉ aᵉ))
      ( Hᵉ Bᵉ)
      ( is-equiv-equivᵉ
        ( inv-distributive-Π-Σᵉ)
        ( inv-distributive-Π-Σᵉ)
        ( ind-Σᵉ (λ gᵉ sᵉ → reflᵉ))
        ( Hᵉ (Σ-Setᵉ Bᵉ Xᵉ)))
      ( idᵉ)
```

### Any map satisfying the dependent universal property of set truncations is a set truncation

```agda
abstract
  is-set-truncation-dependent-universal-propertyᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    dependent-universal-property-set-truncationᵉ Bᵉ fᵉ →
    is-set-truncationᵉ Bᵉ fᵉ
  is-set-truncation-dependent-universal-propertyᵉ Bᵉ fᵉ Hᵉ Xᵉ =
    Hᵉ (λ bᵉ → Xᵉ)
```

### Any set quotient of the mere equality equivalence relation is a set truncation

```agda
abstract
  is-set-truncation-is-set-quotientᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    is-set-quotientᵉ
      ( mere-eq-equivalence-relationᵉ Aᵉ)
      ( Bᵉ)
      ( reflecting-map-mere-eqᵉ Bᵉ fᵉ) →
    is-set-truncationᵉ Bᵉ fᵉ
  is-set-truncation-is-set-quotientᵉ {Aᵉ = Aᵉ} Bᵉ fᵉ Hᵉ Xᵉ =
    is-equiv-compᵉ
      ( pr1ᵉ)
      ( precomp-Set-Quotientᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( Bᵉ)
        ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
        ( Xᵉ))
      ( Hᵉ Xᵉ)
      ( is-equiv-pr1-is-contrᵉ
        ( λ hᵉ →
          is-proof-irrelevant-is-propᵉ
            ( is-prop-reflects-equivalence-relationᵉ
              ( mere-eq-equivalence-relationᵉ Aᵉ) Xᵉ hᵉ)
            ( reflects-mere-eqᵉ Xᵉ hᵉ)))
```

### Any set truncation is a quotient of the mere equality equivalence relation

```agda
abstract
  is-set-quotient-is-set-truncationᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    is-set-truncationᵉ Bᵉ fᵉ →
    is-set-quotientᵉ
      ( mere-eq-equivalence-relationᵉ Aᵉ)
      ( Bᵉ)
      ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
  is-set-quotient-is-set-truncationᵉ {Aᵉ = Aᵉ} Bᵉ fᵉ Hᵉ Xᵉ =
    is-equiv-right-factorᵉ
      ( pr1ᵉ)
      ( precomp-Set-Quotientᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( Bᵉ)
        ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
        ( Xᵉ))
      ( is-equiv-pr1-is-contrᵉ
        ( λ hᵉ →
          is-proof-irrelevant-is-propᵉ
            ( is-prop-reflects-equivalence-relationᵉ
              ( mere-eq-equivalence-relationᵉ Aᵉ) Xᵉ hᵉ)
            ( reflects-mere-eqᵉ Xᵉ hᵉ)))
      ( Hᵉ Xᵉ)
```
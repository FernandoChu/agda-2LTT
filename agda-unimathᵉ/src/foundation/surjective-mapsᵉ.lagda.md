# Surjective maps

```agda
module foundation.surjective-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.connected-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-dependent-functionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.split-surjective-mapsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.truncated-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-family-of-fibers-of-mapsᵉ
open import foundation.universal-property-propositional-truncationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncation-levelsᵉ

open import orthogonal-factorization-systems.extensions-of-mapsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ **surjective**ᵉ ifᵉ allᵉ ofᵉ itsᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
[inhabited](foundation.inhabited-types.md).ᵉ

## Definition

### Surjective maps

```agda
is-surjective-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-surjective-Propᵉ {Bᵉ = Bᵉ} fᵉ = Π-Propᵉ Bᵉ (trunc-Propᵉ ∘ᵉ fiberᵉ fᵉ)

is-surjectiveᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-surjectiveᵉ fᵉ = type-Propᵉ (is-surjective-Propᵉ fᵉ)

is-prop-is-surjectiveᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-propᵉ (is-surjectiveᵉ fᵉ)
is-prop-is-surjectiveᵉ fᵉ = is-prop-type-Propᵉ (is-surjective-Propᵉ fᵉ)

infix 5 _↠ᵉ_
_↠ᵉ_ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
Aᵉ ↠ᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) is-surjectiveᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↠ᵉ Bᵉ)
  where

  map-surjectionᵉ : Aᵉ → Bᵉ
  map-surjectionᵉ = pr1ᵉ fᵉ

  is-surjective-map-surjectionᵉ : is-surjectiveᵉ map-surjectionᵉ
  is-surjective-map-surjectionᵉ = pr2ᵉ fᵉ
```

### The type of all surjective maps out of a type

```agda
Surjectionᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Surjectionᵉ l2ᵉ Aᵉ = Σᵉ (UUᵉ l2ᵉ) (Aᵉ ↠ᵉ_)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Surjectionᵉ l2ᵉ Aᵉ)
  where

  type-Surjectionᵉ : UUᵉ l2ᵉ
  type-Surjectionᵉ = pr1ᵉ fᵉ

  surjection-Surjectionᵉ : Aᵉ ↠ᵉ type-Surjectionᵉ
  surjection-Surjectionᵉ = pr2ᵉ fᵉ

  map-Surjectionᵉ : Aᵉ → type-Surjectionᵉ
  map-Surjectionᵉ = map-surjectionᵉ surjection-Surjectionᵉ

  is-surjective-map-Surjectionᵉ : is-surjectiveᵉ map-Surjectionᵉ
  is-surjective-map-Surjectionᵉ =
    is-surjective-map-surjectionᵉ surjection-Surjectionᵉ
```

### The type of all surjective maps into `k`-truncated types

```agda
Surjection-Into-Truncated-Typeᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (kᵉ : 𝕋ᵉ) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ =
  Σᵉ (Truncated-Typeᵉ l2ᵉ kᵉ) (λ Xᵉ → Aᵉ ↠ᵉ type-Truncated-Typeᵉ Xᵉ)

emb-inclusion-Surjection-Into-Truncated-Typeᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ l1ᵉ) →
  Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ ↪ᵉ Surjectionᵉ l2ᵉ Aᵉ
emb-inclusion-Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ =
  emb-Σᵉ (λ Xᵉ → Aᵉ ↠ᵉ Xᵉ) (emb-type-Truncated-Typeᵉ l2ᵉ kᵉ) (λ Xᵉ → id-embᵉ)

inclusion-Surjection-Into-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} →
  Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ → Surjectionᵉ l2ᵉ Aᵉ
inclusion-Surjection-Into-Truncated-Typeᵉ {l1ᵉ} {l2ᵉ} {kᵉ} {Aᵉ} =
  map-embᵉ (emb-inclusion-Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  (fᵉ : Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ)
  where

  truncated-type-Surjection-Into-Truncated-Typeᵉ : Truncated-Typeᵉ l2ᵉ kᵉ
  truncated-type-Surjection-Into-Truncated-Typeᵉ = pr1ᵉ fᵉ

  type-Surjection-Into-Truncated-Typeᵉ : UUᵉ l2ᵉ
  type-Surjection-Into-Truncated-Typeᵉ =
    type-Truncated-Typeᵉ truncated-type-Surjection-Into-Truncated-Typeᵉ

  is-trunc-type-Surjection-Into-Truncated-Typeᵉ :
    is-truncᵉ kᵉ type-Surjection-Into-Truncated-Typeᵉ
  is-trunc-type-Surjection-Into-Truncated-Typeᵉ =
    is-trunc-type-Truncated-Typeᵉ
      truncated-type-Surjection-Into-Truncated-Typeᵉ

  surjection-Surjection-Into-Truncated-Typeᵉ :
    Aᵉ ↠ᵉ type-Surjection-Into-Truncated-Typeᵉ
  surjection-Surjection-Into-Truncated-Typeᵉ = pr2ᵉ fᵉ

  map-Surjection-Into-Truncated-Typeᵉ :
    Aᵉ → type-Surjection-Into-Truncated-Typeᵉ
  map-Surjection-Into-Truncated-Typeᵉ =
    map-surjectionᵉ surjection-Surjection-Into-Truncated-Typeᵉ

  is-surjective-Surjection-Into-Truncated-Typeᵉ :
    is-surjectiveᵉ map-Surjection-Into-Truncated-Typeᵉ
  is-surjective-Surjection-Into-Truncated-Typeᵉ =
    is-surjective-map-surjectionᵉ surjection-Surjection-Into-Truncated-Typeᵉ
```

### The type of all surjective maps into sets

```agda
Surjection-Into-Setᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Surjection-Into-Setᵉ l2ᵉ Aᵉ = Surjection-Into-Truncated-Typeᵉ l2ᵉ zero-𝕋ᵉ Aᵉ

emb-inclusion-Surjection-Into-Setᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) →
  Surjection-Into-Setᵉ l2ᵉ Aᵉ ↪ᵉ Surjectionᵉ l2ᵉ Aᵉ
emb-inclusion-Surjection-Into-Setᵉ l2ᵉ Aᵉ =
  emb-inclusion-Surjection-Into-Truncated-Typeᵉ l2ᵉ zero-𝕋ᵉ Aᵉ

inclusion-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  Surjection-Into-Setᵉ l2ᵉ Aᵉ → Surjectionᵉ l2ᵉ Aᵉ
inclusion-Surjection-Into-Setᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} =
  inclusion-Surjection-Into-Truncated-Typeᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Surjection-Into-Setᵉ l2ᵉ Aᵉ)
  where

  set-Surjection-Into-Setᵉ : Setᵉ l2ᵉ
  set-Surjection-Into-Setᵉ = truncated-type-Surjection-Into-Truncated-Typeᵉ fᵉ

  type-Surjection-Into-Setᵉ : UUᵉ l2ᵉ
  type-Surjection-Into-Setᵉ = type-Surjection-Into-Truncated-Typeᵉ fᵉ

  is-set-type-Surjection-Into-Setᵉ : is-setᵉ type-Surjection-Into-Setᵉ
  is-set-type-Surjection-Into-Setᵉ =
    is-trunc-type-Surjection-Into-Truncated-Typeᵉ fᵉ

  surjection-Surjection-Into-Setᵉ : Aᵉ ↠ᵉ type-Surjection-Into-Setᵉ
  surjection-Surjection-Into-Setᵉ = surjection-Surjection-Into-Truncated-Typeᵉ fᵉ

  map-Surjection-Into-Setᵉ : Aᵉ → type-Surjection-Into-Setᵉ
  map-Surjection-Into-Setᵉ = map-Surjection-Into-Truncated-Typeᵉ fᵉ

  is-surjective-Surjection-Into-Setᵉ : is-surjectiveᵉ map-Surjection-Into-Setᵉ
  is-surjective-Surjection-Into-Setᵉ =
    is-surjective-Surjection-Into-Truncated-Typeᵉ fᵉ
```

## Properties

### Any map that has a section is surjective

```agda
abstract
  is-surjective-has-sectionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
    sectionᵉ fᵉ → is-surjectiveᵉ fᵉ
  is-surjective-has-sectionᵉ (gᵉ ,ᵉ Gᵉ) bᵉ = unit-trunc-Propᵉ (gᵉ bᵉ ,ᵉ Gᵉ bᵉ)
```

### Any split surjective map is surjective

```agda
abstract
  is-surjective-is-split-surjectiveᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-split-surjectiveᵉ fᵉ → is-surjectiveᵉ fᵉ
  is-surjective-is-split-surjectiveᵉ Hᵉ xᵉ =
    unit-trunc-Propᵉ (Hᵉ xᵉ)
```

### Any equivalence is surjective

```agda
is-surjective-is-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-equivᵉ fᵉ → is-surjectiveᵉ fᵉ
is-surjective-is-equivᵉ Hᵉ = is-surjective-has-sectionᵉ (pr1ᵉ Hᵉ)

is-surjective-map-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  is-surjectiveᵉ (map-equivᵉ eᵉ)
is-surjective-map-equivᵉ eᵉ = is-surjective-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)
```

### The identity function is surjective

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-surjective-idᵉ : is-surjectiveᵉ (idᵉ {Aᵉ = Aᵉ})
  is-surjective-idᵉ aᵉ = unit-trunc-Propᵉ (aᵉ ,ᵉ reflᵉ)
```

### Maps which are homotopic to surjective maps are surjective

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-surjective-htpyᵉ :
      {fᵉ gᵉ : Aᵉ → Bᵉ} → fᵉ ~ᵉ gᵉ → is-surjectiveᵉ gᵉ → is-surjectiveᵉ fᵉ
    is-surjective-htpyᵉ {fᵉ} {gᵉ} Hᵉ Kᵉ bᵉ =
      apply-universal-property-trunc-Propᵉ
        ( Kᵉ bᵉ)
        ( trunc-Propᵉ (fiberᵉ fᵉ bᵉ))
        ( λ where (aᵉ ,ᵉ reflᵉ) → unit-trunc-Propᵉ (aᵉ ,ᵉ Hᵉ aᵉ))

  abstract
    is-surjective-htpy'ᵉ :
      {fᵉ gᵉ : Aᵉ → Bᵉ} → fᵉ ~ᵉ gᵉ → is-surjectiveᵉ fᵉ → is-surjectiveᵉ gᵉ
    is-surjective-htpy'ᵉ Hᵉ = is-surjective-htpyᵉ (inv-htpyᵉ Hᵉ)
```

### The dependent universal property of surjective maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  dependent-universal-property-surjectionᵉ : UUωᵉ
  dependent-universal-property-surjectionᵉ =
    {lᵉ : Level} (Pᵉ : Bᵉ → Propᵉ lᵉ) →
    is-equivᵉ (λ (hᵉ : (bᵉ : Bᵉ) → type-Propᵉ (Pᵉ bᵉ)) xᵉ → hᵉ (fᵉ xᵉ))

  abstract
    is-surjective-dependent-universal-property-surjectionᵉ :
      dependent-universal-property-surjectionᵉ → is-surjectiveᵉ fᵉ
    is-surjective-dependent-universal-property-surjectionᵉ dup-surj-fᵉ =
      map-inv-is-equivᵉ
        ( dup-surj-fᵉ (λ bᵉ → trunc-Propᵉ (fiberᵉ fᵉ bᵉ)))
        ( λ xᵉ → unit-trunc-Propᵉ (xᵉ ,ᵉ reflᵉ))

  abstract
    square-dependent-universal-property-surjectionᵉ :
      {l3ᵉ : Level} (Pᵉ : Bᵉ → Propᵉ l3ᵉ) →
      ( λ (hᵉ : (yᵉ : Bᵉ) → type-Propᵉ (Pᵉ yᵉ)) xᵉ → hᵉ (fᵉ xᵉ)) ~ᵉ
      ( ( λ hᵉ xᵉ → hᵉ (fᵉ xᵉ) (xᵉ ,ᵉ reflᵉ)) ∘ᵉ
        ( λ hᵉ yᵉ → hᵉ yᵉ ∘ᵉ unit-trunc-Propᵉ) ∘ᵉ
        ( postcomp-Πᵉ _
          ( λ {yᵉ} →
            diagonal-exponentialᵉ
              ( type-Propᵉ (Pᵉ yᵉ))
              ( type-trunc-Propᵉ (fiberᵉ fᵉ yᵉ)))))
    square-dependent-universal-property-surjectionᵉ Pᵉ = refl-htpyᵉ

  abstract
    dependent-universal-property-surjection-is-surjectiveᵉ :
      is-surjectiveᵉ fᵉ → dependent-universal-property-surjectionᵉ
    dependent-universal-property-surjection-is-surjectiveᵉ is-surj-fᵉ Pᵉ =
      is-equiv-compᵉ
        ( λ hᵉ xᵉ → hᵉ (fᵉ xᵉ) (xᵉ ,ᵉ reflᵉ))
        ( ( λ hᵉ yᵉ → hᵉ yᵉ ∘ᵉ unit-trunc-Propᵉ) ∘ᵉ
          ( postcomp-Πᵉ
            ( Bᵉ)
            ( λ {yᵉ} →
              diagonal-exponentialᵉ
                ( type-Propᵉ (Pᵉ yᵉ))
                ( type-trunc-Propᵉ (fiberᵉ fᵉ yᵉ)))))
        ( is-equiv-compᵉ
          ( λ hᵉ yᵉ → hᵉ yᵉ ∘ᵉ unit-trunc-Propᵉ)
          ( postcomp-Πᵉ
            ( Bᵉ)
            ( λ {yᵉ} →
              diagonal-exponentialᵉ
                ( type-Propᵉ (Pᵉ yᵉ))
                ( type-trunc-Propᵉ (fiberᵉ fᵉ yᵉ))))
          ( is-equiv-map-Π-is-fiberwise-equivᵉ
            ( λ yᵉ →
              is-equiv-diagonal-exponential-is-contrᵉ
                ( is-proof-irrelevant-is-propᵉ
                  ( is-prop-type-trunc-Propᵉ)
                  ( is-surj-fᵉ yᵉ))
                ( type-Propᵉ (Pᵉ yᵉ))))
          ( is-equiv-map-Π-is-fiberwise-equivᵉ
            ( λ bᵉ → is-propositional-truncation-trunc-Propᵉ (fiberᵉ fᵉ bᵉ) (Pᵉ bᵉ))))
        ( universal-property-family-of-fibers-fiberᵉ fᵉ (is-in-subtypeᵉ Pᵉ))

  equiv-dependent-universal-property-surjection-is-surjectiveᵉ :
    is-surjectiveᵉ fᵉ →
    {lᵉ : Level} (Cᵉ : Bᵉ → Propᵉ lᵉ) →
    ((bᵉ : Bᵉ) → type-Propᵉ (Cᵉ bᵉ)) ≃ᵉ ((aᵉ : Aᵉ) → type-Propᵉ (Cᵉ (fᵉ aᵉ)))
  pr1ᵉ (equiv-dependent-universal-property-surjection-is-surjectiveᵉ Hᵉ Cᵉ) hᵉ xᵉ =
    hᵉ (fᵉ xᵉ)
  pr2ᵉ (equiv-dependent-universal-property-surjection-is-surjectiveᵉ Hᵉ Cᵉ) =
    dependent-universal-property-surjection-is-surjectiveᵉ Hᵉ Cᵉ

  apply-dependent-universal-property-surjection-is-surjectiveᵉ :
    is-surjectiveᵉ fᵉ →
    {lᵉ : Level} (Cᵉ : Bᵉ → Propᵉ lᵉ) →
    ((aᵉ : Aᵉ) → type-Propᵉ (Cᵉ (fᵉ aᵉ))) → ((yᵉ : Bᵉ) → type-Propᵉ (Cᵉ yᵉ))
  apply-dependent-universal-property-surjection-is-surjectiveᵉ Hᵉ Cᵉ =
    map-inv-equivᵉ
      ( equiv-dependent-universal-property-surjection-is-surjectiveᵉ Hᵉ Cᵉ)

  apply-twice-dependent-universal-property-surjection-is-surjectiveᵉ :
    is-surjectiveᵉ fᵉ →
    {lᵉ : Level} (Cᵉ : Bᵉ → Bᵉ → Propᵉ lᵉ) →
    ((xᵉ yᵉ : Aᵉ) → type-Propᵉ (Cᵉ (fᵉ xᵉ) (fᵉ yᵉ))) → ((sᵉ tᵉ : Bᵉ) → type-Propᵉ (Cᵉ sᵉ tᵉ))
  apply-twice-dependent-universal-property-surjection-is-surjectiveᵉ Hᵉ Cᵉ Gᵉ sᵉ =
    apply-dependent-universal-property-surjection-is-surjectiveᵉ
      ( Hᵉ)
      ( λ bᵉ → Cᵉ sᵉ bᵉ)
      ( λ yᵉ →
        apply-dependent-universal-property-surjection-is-surjectiveᵉ
          ( Hᵉ)
          ( λ bᵉ → Cᵉ bᵉ (fᵉ yᵉ))
          ( λ xᵉ → Gᵉ xᵉ yᵉ)
          ( sᵉ))

equiv-dependent-universal-property-surjectionᵉ :
  {lᵉ l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↠ᵉ Bᵉ) →
  (Cᵉ : Bᵉ → Propᵉ lᵉ) →
  ((bᵉ : Bᵉ) → type-Propᵉ (Cᵉ bᵉ)) ≃ᵉ ((aᵉ : Aᵉ) → type-Propᵉ (Cᵉ (map-surjectionᵉ fᵉ aᵉ)))
equiv-dependent-universal-property-surjectionᵉ fᵉ =
  equiv-dependent-universal-property-surjection-is-surjectiveᵉ
    ( map-surjectionᵉ fᵉ)
    ( is-surjective-map-surjectionᵉ fᵉ)

apply-dependent-universal-property-surjectionᵉ :
  {lᵉ l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↠ᵉ Bᵉ) →
  (Cᵉ : Bᵉ → Propᵉ lᵉ) →
  ((aᵉ : Aᵉ) → type-Propᵉ (Cᵉ (map-surjectionᵉ fᵉ aᵉ))) → ((yᵉ : Bᵉ) → type-Propᵉ (Cᵉ yᵉ))
apply-dependent-universal-property-surjectionᵉ fᵉ =
  apply-dependent-universal-property-surjection-is-surjectiveᵉ
    ( map-surjectionᵉ fᵉ)
    ( is-surjective-map-surjectionᵉ fᵉ)
```

### A map into a proposition is a propositional truncation if and only if it is surjective

```agda
abstract
  is-surjective-is-propositional-truncationᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Propᵉ l2ᵉ} (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    dependent-universal-property-propositional-truncationᵉ Pᵉ fᵉ →
    is-surjectiveᵉ fᵉ
  is-surjective-is-propositional-truncationᵉ fᵉ duppt-fᵉ =
    is-surjective-dependent-universal-property-surjectionᵉ fᵉ duppt-fᵉ

abstract
  is-propsitional-truncation-is-surjectiveᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Propᵉ l2ᵉ} (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    is-surjectiveᵉ fᵉ →
    dependent-universal-property-propositional-truncationᵉ Pᵉ fᵉ
  is-propsitional-truncation-is-surjectiveᵉ fᵉ is-surj-fᵉ =
    dependent-universal-property-surjection-is-surjectiveᵉ fᵉ is-surj-fᵉ
```

### A map that is both surjective and an embedding is an equivalence

```agda
abstract
  is-equiv-is-emb-is-surjectiveᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-surjectiveᵉ fᵉ → is-embᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-emb-is-surjectiveᵉ {fᵉ = fᵉ} Hᵉ Kᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ yᵉ →
        is-proof-irrelevant-is-propᵉ
          ( is-prop-map-is-embᵉ Kᵉ yᵉ)
          ( apply-universal-property-trunc-Propᵉ
            ( Hᵉ yᵉ)
            ( fiber-emb-Propᵉ (fᵉ ,ᵉ Kᵉ) yᵉ)
            ( idᵉ)))
```

### The composite of surjective maps is surjective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  abstract
    is-surjective-left-map-triangleᵉ :
      (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
      is-surjectiveᵉ gᵉ → is-surjectiveᵉ hᵉ → is-surjectiveᵉ fᵉ
    is-surjective-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ is-surj-gᵉ is-surj-hᵉ xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-surj-gᵉ xᵉ)
        ( trunc-Propᵉ (fiberᵉ fᵉ xᵉ))
        ( λ where
          ( bᵉ ,ᵉ reflᵉ) →
            apply-universal-property-trunc-Propᵉ
              ( is-surj-hᵉ bᵉ)
              ( trunc-Propᵉ (fiberᵉ fᵉ (gᵉ bᵉ)))
              ( λ where (aᵉ ,ᵉ reflᵉ) → unit-trunc-Propᵉ (aᵉ ,ᵉ Hᵉ aᵉ)))

  is-surjective-compᵉ :
    {gᵉ : Bᵉ → Xᵉ} {hᵉ : Aᵉ → Bᵉ} →
    is-surjectiveᵉ gᵉ → is-surjectiveᵉ hᵉ → is-surjectiveᵉ (gᵉ ∘ᵉ hᵉ)
  is-surjective-compᵉ {gᵉ} {hᵉ} =
    is-surjective-left-map-triangleᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ
```

### Functoriality of products preserves being surjective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  where

  is-surjective-map-productᵉ :
    {fᵉ : Aᵉ → Cᵉ} {gᵉ : Bᵉ → Dᵉ} →
    is-surjectiveᵉ fᵉ → is-surjectiveᵉ gᵉ → is-surjectiveᵉ (map-productᵉ fᵉ gᵉ)
  is-surjective-map-productᵉ {fᵉ} {gᵉ} sᵉ s'ᵉ (cᵉ ,ᵉ dᵉ) =
    apply-twice-universal-property-trunc-Propᵉ
      ( sᵉ cᵉ)
      ( s'ᵉ dᵉ)
      ( trunc-Propᵉ (fiberᵉ (map-productᵉ fᵉ gᵉ) (cᵉ ,ᵉ dᵉ)))
      ( λ xᵉ yᵉ →
        unit-trunc-Propᵉ ((pr1ᵉ xᵉ ,ᵉ pr1ᵉ yᵉ) ,ᵉ eq-pairᵉ (pr2ᵉ xᵉ) (pr2ᵉ yᵉ)))

  surjection-productᵉ :
    (Aᵉ ↠ᵉ Cᵉ) → (Bᵉ ↠ᵉ Dᵉ) → ((Aᵉ ×ᵉ Bᵉ) ↠ᵉ (Cᵉ ×ᵉ Dᵉ))
  pr1ᵉ (surjection-productᵉ fᵉ gᵉ) =
    map-productᵉ (map-surjectionᵉ fᵉ) (map-surjectionᵉ gᵉ)
  pr2ᵉ (surjection-productᵉ fᵉ gᵉ) =
    is-surjective-map-productᵉ
      ( is-surjective-map-surjectionᵉ fᵉ)
      ( is-surjective-map-surjectionᵉ gᵉ)
```

### The composite of a surjective map with an equivalence is surjective

```agda
is-surjective-comp-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (eᵉ : Bᵉ ≃ᵉ Cᵉ) → {fᵉ : Aᵉ → Bᵉ} → is-surjectiveᵉ fᵉ → is-surjectiveᵉ (map-equivᵉ eᵉ ∘ᵉ fᵉ)
is-surjective-comp-equivᵉ eᵉ =
  is-surjective-compᵉ (is-surjective-map-equivᵉ eᵉ)
```

### The precomposite of a surjective map with an equivalence is surjective

```agda
is-surjective-precomp-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {fᵉ : Bᵉ → Cᵉ} →
  is-surjectiveᵉ fᵉ → (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-surjectiveᵉ (fᵉ ∘ᵉ map-equivᵉ eᵉ)
is-surjective-precomp-equivᵉ Hᵉ eᵉ =
  is-surjective-compᵉ Hᵉ (is-surjective-map-equivᵉ eᵉ)
```

### If a composite is surjective, then so is its left factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  abstract
    is-surjective-right-map-triangleᵉ :
      (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
      is-surjectiveᵉ fᵉ → is-surjectiveᵉ gᵉ
    is-surjective-right-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ is-surj-fᵉ xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-surj-fᵉ xᵉ)
        ( trunc-Propᵉ (fiberᵉ gᵉ xᵉ))
        ( λ where (aᵉ ,ᵉ reflᵉ) → unit-trunc-Propᵉ (hᵉ aᵉ ,ᵉ invᵉ (Hᵉ aᵉ)))

  is-surjective-left-factorᵉ :
    {gᵉ : Bᵉ → Xᵉ} (hᵉ : Aᵉ → Bᵉ) → is-surjectiveᵉ (gᵉ ∘ᵉ hᵉ) → is-surjectiveᵉ gᵉ
  is-surjective-left-factorᵉ {gᵉ} hᵉ =
    is-surjective-right-map-triangleᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ
```

### Surjective maps are `-1`-connected

```agda
is-neg-one-connected-map-is-surjectiveᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-surjectiveᵉ fᵉ → is-connected-mapᵉ neg-one-𝕋ᵉ fᵉ
is-neg-one-connected-map-is-surjectiveᵉ Hᵉ bᵉ =
  is-proof-irrelevant-is-propᵉ is-prop-type-trunc-Propᵉ (Hᵉ bᵉ)

is-surjective-is-neg-one-connected-mapᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-connected-mapᵉ neg-one-𝕋ᵉ fᵉ → is-surjectiveᵉ fᵉ
is-surjective-is-neg-one-connected-mapᵉ Hᵉ bᵉ = centerᵉ (Hᵉ bᵉ)
```

### A (k+1)-connected map is surjective

```agda
is-surjective-is-connected-mapᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ : Aᵉ → Bᵉ} → is-connected-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ →
  is-surjectiveᵉ fᵉ
is-surjective-is-connected-mapᵉ neg-two-𝕋ᵉ Hᵉ =
  is-surjective-is-neg-one-connected-mapᵉ Hᵉ
is-surjective-is-connected-mapᵉ (succ-𝕋ᵉ kᵉ) Hᵉ =
  is-surjective-is-connected-mapᵉ
    ( kᵉ)
    ( is-connected-map-is-connected-map-succ-𝕋ᵉ
      ( succ-𝕋ᵉ kᵉ)
      ( Hᵉ))
```

### Precomposing functions into a family of `k+1`-types by a surjective map is a `k`-truncated map

```agda
is-trunc-map-precomp-Π-is-surjectiveᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) →
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} → is-surjectiveᵉ fᵉ →
  (Pᵉ : Bᵉ → Truncated-Typeᵉ l3ᵉ (succ-𝕋ᵉ kᵉ)) →
  is-trunc-mapᵉ kᵉ (precomp-Πᵉ fᵉ (λ bᵉ → type-Truncated-Typeᵉ (Pᵉ bᵉ)))
is-trunc-map-precomp-Π-is-surjectiveᵉ kᵉ Hᵉ =
  is-trunc-map-precomp-Π-is-connected-mapᵉ
    ( neg-one-𝕋ᵉ)
    ( succ-𝕋ᵉ kᵉ)
    ( kᵉ)
    ( reflᵉ)
    ( is-neg-one-connected-map-is-surjectiveᵉ Hᵉ)
```

### Characterization of the identity type of `A ↠ B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↠ᵉ Bᵉ)
  where

  htpy-surjectionᵉ : (Aᵉ ↠ᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-surjectionᵉ gᵉ = map-surjectionᵉ fᵉ ~ᵉ map-surjectionᵉ gᵉ

  refl-htpy-surjectionᵉ : htpy-surjectionᵉ fᵉ
  refl-htpy-surjectionᵉ = refl-htpyᵉ

  is-torsorial-htpy-surjectionᵉ : is-torsorialᵉ htpy-surjectionᵉ
  is-torsorial-htpy-surjectionᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpyᵉ (map-surjectionᵉ fᵉ))
      ( is-prop-is-surjectiveᵉ)
      ( map-surjectionᵉ fᵉ)
      ( refl-htpyᵉ)
      ( is-surjective-map-surjectionᵉ fᵉ)

  htpy-eq-surjectionᵉ :
    (gᵉ : Aᵉ ↠ᵉ Bᵉ) → (fᵉ ＝ᵉ gᵉ) → htpy-surjectionᵉ gᵉ
  htpy-eq-surjectionᵉ .fᵉ reflᵉ = refl-htpy-surjectionᵉ

  is-equiv-htpy-eq-surjectionᵉ :
    (gᵉ : Aᵉ ↠ᵉ Bᵉ) → is-equivᵉ (htpy-eq-surjectionᵉ gᵉ)
  is-equiv-htpy-eq-surjectionᵉ =
    fundamental-theorem-idᵉ is-torsorial-htpy-surjectionᵉ htpy-eq-surjectionᵉ

  extensionality-surjectionᵉ :
    (gᵉ : Aᵉ ↠ᵉ Bᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-surjectionᵉ gᵉ
  pr1ᵉ (extensionality-surjectionᵉ gᵉ) = htpy-eq-surjectionᵉ gᵉ
  pr2ᵉ (extensionality-surjectionᵉ gᵉ) = is-equiv-htpy-eq-surjectionᵉ gᵉ

  eq-htpy-surjectionᵉ : (gᵉ : Aᵉ ↠ᵉ Bᵉ) → htpy-surjectionᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-surjectionᵉ gᵉ =
    map-inv-equivᵉ (extensionality-surjectionᵉ gᵉ)
```

### Characterization of the identity type of `Surjection l2 A`

```agda
equiv-Surjectionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  Surjectionᵉ l2ᵉ Aᵉ → Surjectionᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
equiv-Surjectionᵉ fᵉ gᵉ =
  Σᵉ ( type-Surjectionᵉ fᵉ ≃ᵉ type-Surjectionᵉ gᵉ)
    ( λ eᵉ → (map-equivᵉ eᵉ ∘ᵉ map-Surjectionᵉ fᵉ) ~ᵉ map-Surjectionᵉ gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Surjectionᵉ l2ᵉ Aᵉ)
  where

  id-equiv-Surjectionᵉ : equiv-Surjectionᵉ fᵉ fᵉ
  pr1ᵉ id-equiv-Surjectionᵉ = id-equivᵉ
  pr2ᵉ id-equiv-Surjectionᵉ = refl-htpyᵉ

  is-torsorial-equiv-Surjectionᵉ :
    is-torsorialᵉ (equiv-Surjectionᵉ fᵉ)
  is-torsorial-equiv-Surjectionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (type-Surjectionᵉ fᵉ))
      ( type-Surjectionᵉ fᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-htpy-surjectionᵉ (surjection-Surjectionᵉ fᵉ))

  equiv-eq-Surjectionᵉ :
    (gᵉ : Surjectionᵉ l2ᵉ Aᵉ) → (fᵉ ＝ᵉ gᵉ) → equiv-Surjectionᵉ fᵉ gᵉ
  equiv-eq-Surjectionᵉ .fᵉ reflᵉ = id-equiv-Surjectionᵉ

  is-equiv-equiv-eq-Surjectionᵉ :
    (gᵉ : Surjectionᵉ l2ᵉ Aᵉ) → is-equivᵉ (equiv-eq-Surjectionᵉ gᵉ)
  is-equiv-equiv-eq-Surjectionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Surjectionᵉ
      equiv-eq-Surjectionᵉ

  extensionality-Surjectionᵉ :
    (gᵉ : Surjectionᵉ l2ᵉ Aᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ equiv-Surjectionᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-Surjectionᵉ gᵉ) = equiv-eq-Surjectionᵉ gᵉ
  pr2ᵉ (extensionality-Surjectionᵉ gᵉ) = is-equiv-equiv-eq-Surjectionᵉ gᵉ

  eq-equiv-Surjectionᵉ :
    (gᵉ : Surjectionᵉ l2ᵉ Aᵉ) → equiv-Surjectionᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-equiv-Surjectionᵉ gᵉ = map-inv-equivᵉ (extensionality-Surjectionᵉ gᵉ)
```

### Characterization of the identity type of `Surjection-Into-Truncated-Type l2 k A`

```agda
equiv-Surjection-Into-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} →
  Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ →
  Surjection-Into-Truncated-Typeᵉ l3ᵉ kᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
equiv-Surjection-Into-Truncated-Typeᵉ fᵉ gᵉ =
  equiv-Surjectionᵉ
    ( inclusion-Surjection-Into-Truncated-Typeᵉ fᵉ)
    ( inclusion-Surjection-Into-Truncated-Typeᵉ gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  (fᵉ : Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ)
  where

  id-equiv-Surjection-Into-Truncated-Typeᵉ :
    equiv-Surjection-Into-Truncated-Typeᵉ fᵉ fᵉ
  id-equiv-Surjection-Into-Truncated-Typeᵉ =
    id-equiv-Surjectionᵉ (inclusion-Surjection-Into-Truncated-Typeᵉ fᵉ)

  extensionality-Surjection-Into-Truncated-Typeᵉ :
    (gᵉ : Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ equiv-Surjection-Into-Truncated-Typeᵉ fᵉ gᵉ
  extensionality-Surjection-Into-Truncated-Typeᵉ gᵉ =
    ( extensionality-Surjectionᵉ
      ( inclusion-Surjection-Into-Truncated-Typeᵉ fᵉ)
      ( inclusion-Surjection-Into-Truncated-Typeᵉ gᵉ)) ∘eᵉ
    ( equiv-ap-embᵉ (emb-inclusion-Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ))

  equiv-eq-Surjection-Into-Truncated-Typeᵉ :
    (gᵉ : Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ) →
    (fᵉ ＝ᵉ gᵉ) → equiv-Surjection-Into-Truncated-Typeᵉ fᵉ gᵉ
  equiv-eq-Surjection-Into-Truncated-Typeᵉ gᵉ =
    map-equivᵉ (extensionality-Surjection-Into-Truncated-Typeᵉ gᵉ)

  refl-equiv-eq-Surjection-Into-Truncated-Typeᵉ :
    equiv-eq-Surjection-Into-Truncated-Typeᵉ fᵉ reflᵉ ＝ᵉ
    id-equiv-Surjection-Into-Truncated-Typeᵉ
  refl-equiv-eq-Surjection-Into-Truncated-Typeᵉ = reflᵉ

  eq-equiv-Surjection-Into-Truncated-Typeᵉ :
    (gᵉ : Surjection-Into-Truncated-Typeᵉ l2ᵉ kᵉ Aᵉ) →
    equiv-Surjection-Into-Truncated-Typeᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-equiv-Surjection-Into-Truncated-Typeᵉ gᵉ =
    map-inv-equivᵉ (extensionality-Surjection-Into-Truncated-Typeᵉ gᵉ)
```

### The type `Surjection-Into-Truncated-Type l2 (succ-𝕋 k) A` is `k`-truncated

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#735](https://github.com/UniMath/agda-unimath/issues/735ᵉ)

### Characterization of the identity type of `Surjection-Into-Set l2 A`

```agda
equiv-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Surjection-Into-Setᵉ l2ᵉ Aᵉ →
  Surjection-Into-Setᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
equiv-Surjection-Into-Setᵉ = equiv-Surjection-Into-Truncated-Typeᵉ

id-equiv-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Surjection-Into-Setᵉ l2ᵉ Aᵉ) →
  equiv-Surjection-Into-Setᵉ fᵉ fᵉ
id-equiv-Surjection-Into-Setᵉ = id-equiv-Surjection-Into-Truncated-Typeᵉ

extensionality-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ gᵉ : Surjection-Into-Setᵉ l2ᵉ Aᵉ) →
  (fᵉ ＝ᵉ gᵉ) ≃ᵉ equiv-Surjection-Into-Setᵉ fᵉ gᵉ
extensionality-Surjection-Into-Setᵉ =
  extensionality-Surjection-Into-Truncated-Typeᵉ

equiv-eq-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ gᵉ : Surjection-Into-Setᵉ l2ᵉ Aᵉ) →
  (fᵉ ＝ᵉ gᵉ) → equiv-Surjection-Into-Setᵉ fᵉ gᵉ
equiv-eq-Surjection-Into-Setᵉ = equiv-eq-Surjection-Into-Truncated-Typeᵉ

refl-equiv-eq-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Surjection-Into-Setᵉ l2ᵉ Aᵉ) →
  equiv-eq-Surjection-Into-Setᵉ fᵉ fᵉ reflᵉ ＝ᵉ
  id-equiv-Surjection-Into-Setᵉ fᵉ
refl-equiv-eq-Surjection-Into-Setᵉ = refl-equiv-eq-Surjection-Into-Truncated-Typeᵉ

eq-equiv-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ gᵉ : Surjection-Into-Setᵉ l2ᵉ Aᵉ) →
  equiv-Surjection-Into-Setᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
eq-equiv-Surjection-Into-Setᵉ = eq-equiv-Surjection-Into-Truncated-Typeᵉ
```

### Postcomposition of extensions along surjective maps by an embedding is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  is-surjective-postcomp-extension-surjective-mapᵉ :
    (fᵉ : Aᵉ → Bᵉ) (iᵉ : Aᵉ → Xᵉ) (gᵉ : Xᵉ → Yᵉ) →
    is-surjectiveᵉ fᵉ → is-embᵉ gᵉ →
    is-surjectiveᵉ (postcomp-extensionᵉ fᵉ iᵉ gᵉ)
  is-surjective-postcomp-extension-surjective-mapᵉ fᵉ iᵉ gᵉ Hᵉ Kᵉ (hᵉ ,ᵉ Lᵉ) =
    unit-trunc-Propᵉ
      ( ( jᵉ ,ᵉ Nᵉ) ,ᵉ
        ( eq-htpy-extensionᵉ fᵉ
          ( gᵉ ∘ᵉ iᵉ)
          ( postcomp-extensionᵉ fᵉ iᵉ gᵉ (jᵉ ,ᵉ Nᵉ))
          ( hᵉ ,ᵉ Lᵉ)
          ( Mᵉ)
          ( λ aᵉ →
            ( apᵉ
              ( concat'ᵉ (gᵉ (iᵉ aᵉ)) (Mᵉ (fᵉ aᵉ)))
              ( is-section-map-inv-is-equivᵉ
                ( Kᵉ (iᵉ aᵉ) (jᵉ (fᵉ aᵉ)))
                ( Lᵉ aᵉ ∙ᵉ invᵉ (Mᵉ (fᵉ aᵉ))))) ∙ᵉ
            ( is-section-inv-concat'ᵉ (Mᵉ (fᵉ aᵉ)) (Lᵉ aᵉ)))))
    where

    Jᵉ : (bᵉ : Bᵉ) → fiberᵉ gᵉ (hᵉ bᵉ)
    Jᵉ =
      apply-dependent-universal-property-surjection-is-surjectiveᵉ fᵉ Hᵉ
        ( λ bᵉ → fiber-emb-Propᵉ (gᵉ ,ᵉ Kᵉ) (hᵉ bᵉ))
        ( λ aᵉ → (iᵉ aᵉ ,ᵉ Lᵉ aᵉ))

    jᵉ : Bᵉ → Xᵉ
    jᵉ bᵉ = pr1ᵉ (Jᵉ bᵉ)

    Mᵉ : (gᵉ ∘ᵉ jᵉ) ~ᵉ hᵉ
    Mᵉ bᵉ = pr2ᵉ (Jᵉ bᵉ)

    Nᵉ : iᵉ ~ᵉ (jᵉ ∘ᵉ fᵉ)
    Nᵉ aᵉ = map-inv-is-equivᵉ (Kᵉ (iᵉ aᵉ) (jᵉ (fᵉ aᵉ))) (Lᵉ aᵉ ∙ᵉ invᵉ (Mᵉ (fᵉ aᵉ)))

  is-equiv-postcomp-extension-is-surjectiveᵉ :
    (fᵉ : Aᵉ → Bᵉ) (iᵉ : Aᵉ → Xᵉ) (gᵉ : Xᵉ → Yᵉ) →
    is-surjectiveᵉ fᵉ → is-embᵉ gᵉ →
    is-equivᵉ (postcomp-extensionᵉ fᵉ iᵉ gᵉ)
  is-equiv-postcomp-extension-is-surjectiveᵉ fᵉ iᵉ gᵉ Hᵉ Kᵉ =
    is-equiv-is-emb-is-surjectiveᵉ
      ( is-surjective-postcomp-extension-surjective-mapᵉ fᵉ iᵉ gᵉ Hᵉ Kᵉ)
      ( is-emb-postcomp-extensionᵉ fᵉ iᵉ gᵉ Kᵉ)

  equiv-postcomp-extension-surjectionᵉ :
    (fᵉ : Aᵉ ↠ᵉ Bᵉ) (iᵉ : Aᵉ → Xᵉ) (gᵉ : Xᵉ ↪ᵉ Yᵉ) →
    extensionᵉ (map-surjectionᵉ fᵉ) iᵉ ≃ᵉ
    extensionᵉ (map-surjectionᵉ fᵉ) (map-embᵉ gᵉ ∘ᵉ iᵉ)
  pr1ᵉ (equiv-postcomp-extension-surjectionᵉ fᵉ iᵉ gᵉ) =
    postcomp-extensionᵉ (map-surjectionᵉ fᵉ) iᵉ (map-embᵉ gᵉ)
  pr2ᵉ (equiv-postcomp-extension-surjectionᵉ fᵉ iᵉ gᵉ) =
    is-equiv-postcomp-extension-is-surjectiveᵉ
      ( map-surjectionᵉ fᵉ)
      ( iᵉ)
      ( map-embᵉ gᵉ)
      ( is-surjective-map-surjectionᵉ fᵉ)
      ( is-emb-map-embᵉ gᵉ)
```

### The type of surjections `A ↠ B` is equivalent to the type of families `P` of inhabited types over `B` equipped with an equivalence `A ≃ Σ B P`

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#735](https://github.com/UniMath/agda-unimath/issues/735ᵉ)

## See also

-ᵉ Inᵉ
  [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
  weᵉ showᵉ thatᵉ aᵉ mapᵉ isᵉ surjectiveᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ anᵉ epimorphismᵉ with
  respectᵉ to sets.ᵉ
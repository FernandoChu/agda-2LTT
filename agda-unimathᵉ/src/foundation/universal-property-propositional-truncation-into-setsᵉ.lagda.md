# The universal property of propositional truncations with respect to sets

```agda
module foundation.universal-property-propositional-truncation-into-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.weakly-constant-mapsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Theᵉ propositionalᵉ truncationᵉ ofᵉ `A`ᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ theᵉ quotientᵉ ofᵉ `A`ᵉ byᵉ
theᵉ fullᵉ equivalenceᵉ relation,ᵉ i.e.,ᵉ theᵉ equivalenceᵉ relationᵉ byᵉ whichᵉ allᵉ
elementsᵉ ofᵉ `A`ᵉ areᵉ consideredᵉ to beᵉ equivalent.ᵉ Thisᵉ ideaᵉ leadsᵉ to theᵉ
universalᵉ propertyᵉ ofᵉ theᵉ propositionalᵉ truncationsᵉ with respectᵉ to sets.ᵉ

## Definition

### The precomposition map that is used to state the universal property

```agda
is-weakly-constant-precomp-unit-trunc-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (gᵉ : type-trunc-Propᵉ Aᵉ → Bᵉ) →
  is-weakly-constantᵉ (gᵉ ∘ᵉ unit-trunc-Propᵉ)
is-weakly-constant-precomp-unit-trunc-Propᵉ gᵉ xᵉ yᵉ =
  apᵉ
    ( gᵉ)
    ( eq-is-propᵉ (is-prop-type-trunc-Propᵉ))

precomp-universal-property-set-quotient-trunc-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) →
  (type-trunc-Propᵉ Aᵉ → type-Setᵉ Bᵉ) → Σᵉ (Aᵉ → type-Setᵉ Bᵉ) is-weakly-constantᵉ
pr1ᵉ (precomp-universal-property-set-quotient-trunc-Propᵉ Bᵉ gᵉ) =
  gᵉ ∘ᵉ unit-trunc-Propᵉ
pr2ᵉ (precomp-universal-property-set-quotient-trunc-Propᵉ Bᵉ gᵉ) =
  is-weakly-constant-precomp-unit-trunc-Propᵉ gᵉ
```

## Properties

### The image of the propositional truncation into a set is a proposition

```agda
abstract
  all-elements-equal-image-is-weakly-constantᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    is-weakly-constantᵉ fᵉ →
    all-elements-equalᵉ (Σᵉ (type-Setᵉ Bᵉ) (λ bᵉ → type-trunc-Propᵉ (fiberᵉ fᵉ bᵉ)))
  all-elements-equal-image-is-weakly-constantᵉ Bᵉ fᵉ Hᵉ (xᵉ ,ᵉ sᵉ) (yᵉ ,ᵉ tᵉ) =
    eq-type-subtypeᵉ
      ( λ bᵉ → trunc-Propᵉ (fiberᵉ fᵉ bᵉ))
      ( apply-universal-property-trunc-Propᵉ sᵉ
        ( Id-Propᵉ Bᵉ xᵉ yᵉ)
        ( λ uᵉ →
          apply-universal-property-trunc-Propᵉ tᵉ
            ( Id-Propᵉ Bᵉ xᵉ yᵉ)
            ( λ vᵉ → invᵉ (pr2ᵉ uᵉ) ∙ᵉ Hᵉ (pr1ᵉ uᵉ) (pr1ᵉ vᵉ) ∙ᵉ pr2ᵉ vᵉ)))

abstract
  is-prop-image-is-weakly-constantᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    is-weakly-constantᵉ fᵉ →
    is-propᵉ (Σᵉ (type-Setᵉ Bᵉ) (λ bᵉ → type-trunc-Propᵉ (fiberᵉ fᵉ bᵉ)))
  is-prop-image-is-weakly-constantᵉ Bᵉ fᵉ Hᵉ =
    is-prop-all-elements-equalᵉ
      ( all-elements-equal-image-is-weakly-constantᵉ Bᵉ fᵉ Hᵉ)

image-weakly-constant-map-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
  is-weakly-constantᵉ fᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (image-weakly-constant-map-Propᵉ Bᵉ fᵉ Hᵉ) =
  Σᵉ (type-Setᵉ Bᵉ) (λ bᵉ → type-trunc-Propᵉ (fiberᵉ fᵉ bᵉ))
pr2ᵉ (image-weakly-constant-map-Propᵉ Bᵉ fᵉ Hᵉ) =
  is-prop-image-is-weakly-constantᵉ Bᵉ fᵉ Hᵉ
```

### The universal property

```agda
map-universal-property-set-quotient-trunc-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
  is-weakly-constantᵉ fᵉ → type-trunc-Propᵉ Aᵉ → type-Setᵉ Bᵉ
map-universal-property-set-quotient-trunc-Propᵉ Bᵉ fᵉ Hᵉ =
  ( pr1ᵉ) ∘ᵉ
  ( map-universal-property-trunc-Propᵉ
    ( image-weakly-constant-map-Propᵉ Bᵉ fᵉ Hᵉ)
    ( λ aᵉ → (fᵉ aᵉ ,ᵉ unit-trunc-Propᵉ (aᵉ ,ᵉ reflᵉ))))

map-universal-property-set-quotient-trunc-Prop'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) →
  Σᵉ (Aᵉ → type-Setᵉ Bᵉ) is-weakly-constantᵉ → type-trunc-Propᵉ Aᵉ → type-Setᵉ Bᵉ
map-universal-property-set-quotient-trunc-Prop'ᵉ Bᵉ (fᵉ ,ᵉ Hᵉ) =
  map-universal-property-set-quotient-trunc-Propᵉ Bᵉ fᵉ Hᵉ

abstract
  htpy-universal-property-set-quotient-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    (Hᵉ : is-weakly-constantᵉ fᵉ) →
    map-universal-property-set-quotient-trunc-Propᵉ Bᵉ fᵉ Hᵉ ∘ᵉ unit-trunc-Propᵉ ~ᵉ fᵉ
  htpy-universal-property-set-quotient-trunc-Propᵉ Bᵉ fᵉ Hᵉ aᵉ =
    apᵉ
      ( pr1ᵉ)
      ( eq-is-prop'ᵉ
        ( is-prop-image-is-weakly-constantᵉ Bᵉ fᵉ Hᵉ)
        ( map-universal-property-trunc-Propᵉ
          ( image-weakly-constant-map-Propᵉ Bᵉ fᵉ Hᵉ)
          ( λ xᵉ → (fᵉ xᵉ ,ᵉ unit-trunc-Propᵉ (xᵉ ,ᵉ reflᵉ)))
          ( unit-trunc-Propᵉ aᵉ))
        ( fᵉ aᵉ ,ᵉ unit-trunc-Propᵉ (aᵉ ,ᵉ reflᵉ)))

  is-section-map-universal-property-set-quotient-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) →
    ( ( precomp-universal-property-set-quotient-trunc-Propᵉ {Aᵉ = Aᵉ} Bᵉ) ∘ᵉ
      ( map-universal-property-set-quotient-trunc-Prop'ᵉ Bᵉ)) ~ᵉ idᵉ
  is-section-map-universal-property-set-quotient-trunc-Propᵉ Bᵉ (fᵉ ,ᵉ Hᵉ) =
    eq-type-subtypeᵉ
      ( is-weakly-constant-prop-Setᵉ Bᵉ)
      ( eq-htpyᵉ (htpy-universal-property-set-quotient-trunc-Propᵉ Bᵉ fᵉ Hᵉ))

  is-retraction-map-universal-property-set-quotient-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) →
    ( ( map-universal-property-set-quotient-trunc-Prop'ᵉ Bᵉ) ∘ᵉ
      ( precomp-universal-property-set-quotient-trunc-Propᵉ {Aᵉ = Aᵉ} Bᵉ)) ~ᵉ idᵉ
  is-retraction-map-universal-property-set-quotient-trunc-Propᵉ Bᵉ gᵉ =
    eq-htpyᵉ
      ( ind-trunc-Propᵉ
        ( λ xᵉ →
          Id-Propᵉ Bᵉ
            ( map-universal-property-set-quotient-trunc-Prop'ᵉ Bᵉ
              ( precomp-universal-property-set-quotient-trunc-Propᵉ Bᵉ gᵉ)
              ( xᵉ))
            ( gᵉ xᵉ))
        ( htpy-universal-property-set-quotient-trunc-Propᵉ Bᵉ
          ( gᵉ ∘ᵉ unit-trunc-Propᵉ)
          ( is-weakly-constant-precomp-unit-trunc-Propᵉ gᵉ)))

  universal-property-set-quotient-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) →
    is-equivᵉ (precomp-universal-property-set-quotient-trunc-Propᵉ {Aᵉ = Aᵉ} Bᵉ)
  universal-property-set-quotient-trunc-Propᵉ Bᵉ =
    is-equiv-is-invertibleᵉ
      ( map-universal-property-set-quotient-trunc-Prop'ᵉ Bᵉ)
      ( is-section-map-universal-property-set-quotient-trunc-Propᵉ Bᵉ)
      ( is-retraction-map-universal-property-set-quotient-trunc-Propᵉ Bᵉ)
```
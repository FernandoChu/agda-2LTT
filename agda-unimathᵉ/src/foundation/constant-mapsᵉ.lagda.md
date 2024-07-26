# Constant maps

```agda
module foundation.constant-mapsᵉ where

open import foundation-core.constant-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.0-mapsᵉ
open import foundation.action-on-homotopies-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.faithful-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.retracts-of-mapsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.1-typesᵉ
open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### The action on homotopies of a constant map is constant

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  compute-action-htpy-function-constᵉ :
    (cᵉ : Cᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) →
    action-htpy-functionᵉ (constᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) cᵉ) Hᵉ ＝ᵉ reflᵉ
  compute-action-htpy-function-constᵉ cᵉ Hᵉ = ap-constᵉ cᵉ (eq-htpyᵉ Hᵉ)
```

### Computing the fibers of point inclusions

```agda
compute-fiber-pointᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (xᵉ yᵉ : Aᵉ) → fiberᵉ (pointᵉ xᵉ) yᵉ ≃ᵉ (xᵉ ＝ᵉ yᵉ)
compute-fiber-pointᵉ xᵉ yᵉ = left-unit-law-productᵉ
```

### A type is `k+1`-truncated if and only if all point inclusions are `k`-truncated maps

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-trunc-map-point-is-truncᵉ :
      (kᵉ : 𝕋ᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ →
      (xᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (pointᵉ xᵉ)
    is-trunc-map-point-is-truncᵉ kᵉ is-trunc-Aᵉ xᵉ yᵉ =
      is-trunc-equivᵉ kᵉ
        ( xᵉ ＝ᵉ yᵉ)
        ( compute-fiber-pointᵉ xᵉ yᵉ)
        ( is-trunc-Aᵉ xᵉ yᵉ)

  abstract
    is-trunc-is-trunc-map-pointᵉ :
      (kᵉ : 𝕋ᵉ) → ((xᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (pointᵉ xᵉ)) →
      is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
    is-trunc-is-trunc-map-pointᵉ kᵉ is-trunc-pointᵉ xᵉ yᵉ =
      is-trunc-equiv'ᵉ kᵉ
        ( Σᵉ unitᵉ (λ _ → xᵉ ＝ᵉ yᵉ))
        ( left-unit-law-Σᵉ (λ _ → xᵉ ＝ᵉ yᵉ))
        ( is-trunc-pointᵉ xᵉ yᵉ)

  abstract
    is-contr-map-point-is-propᵉ :
      is-propᵉ Aᵉ → (xᵉ : Aᵉ) → is-contr-mapᵉ (pointᵉ xᵉ)
    is-contr-map-point-is-propᵉ = is-trunc-map-point-is-truncᵉ neg-two-𝕋ᵉ

  abstract
    is-equiv-point-is-propᵉ :
      is-propᵉ Aᵉ → (xᵉ : Aᵉ) → is-equivᵉ (pointᵉ xᵉ)
    is-equiv-point-is-propᵉ Hᵉ xᵉ =
      is-equiv-is-contr-mapᵉ (is-contr-map-point-is-propᵉ Hᵉ xᵉ)

  abstract
    is-prop-map-point-is-setᵉ :
      is-setᵉ Aᵉ → (xᵉ : Aᵉ) → is-prop-mapᵉ (pointᵉ xᵉ)
    is-prop-map-point-is-setᵉ = is-trunc-map-point-is-truncᵉ neg-one-𝕋ᵉ

  abstract
    is-emb-point-is-setᵉ : is-setᵉ Aᵉ → (xᵉ : Aᵉ) → is-embᵉ (pointᵉ xᵉ)
    is-emb-point-is-setᵉ Hᵉ xᵉ = is-emb-is-prop-mapᵉ (is-prop-map-point-is-setᵉ Hᵉ xᵉ)

  abstract
    is-0-map-point-is-1-typeᵉ : is-1-typeᵉ Aᵉ → (xᵉ : Aᵉ) → is-0-mapᵉ (pointᵉ xᵉ)
    is-0-map-point-is-1-typeᵉ = is-trunc-map-point-is-truncᵉ zero-𝕋ᵉ

  abstract
    is-faithful-point-is-1-typeᵉ :
      is-1-typeᵉ Aᵉ → (xᵉ : Aᵉ) → is-faithfulᵉ (pointᵉ xᵉ)
    is-faithful-point-is-1-typeᵉ Hᵉ xᵉ =
      is-faithful-is-0-mapᵉ (is-0-map-point-is-1-typeᵉ Hᵉ xᵉ)

  abstract
    is-prop-is-contr-map-pointᵉ :
      ((xᵉ : Aᵉ) → is-contr-mapᵉ (pointᵉ xᵉ)) → is-propᵉ Aᵉ
    is-prop-is-contr-map-pointᵉ = is-trunc-is-trunc-map-pointᵉ neg-two-𝕋ᵉ

  abstract
    is-prop-is-equiv-pointᵉ :
      ((xᵉ : Aᵉ) → is-equivᵉ (pointᵉ xᵉ)) → is-propᵉ Aᵉ
    is-prop-is-equiv-pointᵉ Hᵉ =
      is-prop-is-contr-map-pointᵉ (is-contr-map-is-equivᵉ ∘ᵉ Hᵉ)

  abstract
    is-set-is-prop-map-pointᵉ :
      ((xᵉ : Aᵉ) → is-prop-mapᵉ (pointᵉ xᵉ)) → is-setᵉ Aᵉ
    is-set-is-prop-map-pointᵉ = is-trunc-is-trunc-map-pointᵉ neg-one-𝕋ᵉ

  abstract
    is-set-is-emb-pointᵉ :
      ((xᵉ : Aᵉ) → is-embᵉ (pointᵉ xᵉ)) → is-setᵉ Aᵉ
    is-set-is-emb-pointᵉ Hᵉ =
      is-set-is-prop-map-pointᵉ (is-prop-map-is-embᵉ ∘ᵉ Hᵉ)

  abstract
    is-1-type-is-0-map-pointᵉ :
      ((xᵉ : Aᵉ) → is-0-mapᵉ (pointᵉ xᵉ)) → is-1-typeᵉ Aᵉ
    is-1-type-is-0-map-pointᵉ = is-trunc-is-trunc-map-pointᵉ zero-𝕋ᵉ

  abstract
    is-1-type-is-faithful-pointᵉ :
      ((xᵉ : Aᵉ) → is-faithfulᵉ (pointᵉ xᵉ)) → is-1-typeᵉ Aᵉ
    is-1-type-is-faithful-pointᵉ Hᵉ =
      is-1-type-is-0-map-pointᵉ (is-0-map-is-faithfulᵉ ∘ᵉ Hᵉ)

point-equivᵉ :
  {lᵉ : Level} (Aᵉ : Propᵉ lᵉ) (xᵉ : type-Propᵉ Aᵉ) → unitᵉ ≃ᵉ type-Propᵉ Aᵉ
pr1ᵉ (point-equivᵉ Aᵉ xᵉ) = pointᵉ xᵉ
pr2ᵉ (point-equivᵉ Aᵉ xᵉ) = is-equiv-point-is-propᵉ (is-prop-type-Propᵉ Aᵉ) xᵉ

point-embᵉ :
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ) (xᵉ : type-Setᵉ Aᵉ) → unitᵉ ↪ᵉ type-Setᵉ Aᵉ
pr1ᵉ (point-embᵉ Aᵉ xᵉ) = pointᵉ xᵉ
pr2ᵉ (point-embᵉ Aᵉ xᵉ) = is-emb-point-is-setᵉ (is-set-type-Setᵉ Aᵉ) xᵉ

point-faithful-mapᵉ :
  {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ) (xᵉ : type-1-Typeᵉ Aᵉ) →
  faithful-mapᵉ unitᵉ (type-1-Typeᵉ Aᵉ)
pr1ᵉ (point-faithful-mapᵉ Aᵉ xᵉ) = pointᵉ xᵉ
pr2ᵉ (point-faithful-mapᵉ Aᵉ xᵉ) =
  is-faithful-point-is-1-typeᵉ (is-1-type-type-1-Typeᵉ Aᵉ) xᵉ
```

## See also

-ᵉ [Constantᵉ pointedᵉ maps](structured-types.constant-pointed-maps.mdᵉ)
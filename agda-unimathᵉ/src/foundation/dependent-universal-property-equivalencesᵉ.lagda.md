# The dependent universal property of equivalences

```agda
module foundation.dependent-universal-property-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coherently-invertible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.path-split-mapsᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Theᵉ **dependentᵉ universalᵉ propertyᵉ ofᵉ equivalences**ᵉ statesᵉ that,ᵉ forᵉ aᵉ givenᵉ
mapᵉ `fᵉ : Aᵉ → B`,ᵉ theᵉ
[precompositionᵉ ofᵉ dependentᵉ functions](foundation-core.precomposition-dependent-functions.mdᵉ)
byᵉ `f`ᵉ

```text
  -ᵉ ∘ᵉ fᵉ : ((bᵉ : Bᵉ) → Cᵉ bᵉ) → ((aᵉ : Aᵉ) → Cᵉ (fᵉ aᵉ))
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) forᵉ everyᵉ typeᵉ familyᵉ `C`ᵉ
overᵉ `B`.ᵉ Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ satisfiesᵉ theᵉ dependentᵉ universalᵉ propertyᵉ ofᵉ
equivalencesᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ anᵉ equivalence.ᵉ

## Definitions

### The dependent universal property of equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  dependent-universal-property-equivᵉ : UUωᵉ
  dependent-universal-property-equivᵉ =
    {lᵉ : Level} (Cᵉ : Bᵉ → UUᵉ lᵉ) → is-equivᵉ (precomp-Πᵉ fᵉ Cᵉ)
```

## Properties

### If `f` is coherently invertible, then `f` satisfies the dependent universal property of equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-equiv-precomp-Π-is-coherently-invertibleᵉ :
      is-coherently-invertibleᵉ fᵉ → dependent-universal-property-equivᵉ fᵉ
    is-equiv-precomp-Π-is-coherently-invertibleᵉ
      ( gᵉ ,ᵉ is-section-gᵉ ,ᵉ is-retraction-gᵉ ,ᵉ cohᵉ) Cᵉ =
      is-equiv-is-invertibleᵉ
        ( λ sᵉ yᵉ → trᵉ Cᵉ (is-section-gᵉ yᵉ) (sᵉ (gᵉ yᵉ)))
        ( λ sᵉ →
          eq-htpyᵉ
            ( λ xᵉ →
              ( apᵉ (λ tᵉ → trᵉ Cᵉ tᵉ (sᵉ (gᵉ (fᵉ xᵉ)))) (cohᵉ xᵉ)) ∙ᵉ
              ( substitution-law-trᵉ Cᵉ fᵉ (is-retraction-gᵉ xᵉ)) ∙ᵉ
              ( apdᵉ sᵉ (is-retraction-gᵉ xᵉ))))
        ( λ sᵉ → eq-htpyᵉ (λ yᵉ → apdᵉ sᵉ (is-section-gᵉ yᵉ)))
```

### If `f` is an equivalence, then `f` satisfies the dependent universal property of equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-equivᵉ fᵉ)
  where

  abstract
    is-equiv-precomp-Π-is-equivᵉ :
      dependent-universal-property-equivᵉ fᵉ
    is-equiv-precomp-Π-is-equivᵉ =
      is-equiv-precomp-Π-is-coherently-invertibleᵉ fᵉ
        ( is-coherently-invertible-is-path-splitᵉ fᵉ
          ( is-path-split-is-equivᵉ fᵉ Hᵉ))

  map-inv-is-equiv-precomp-Π-is-equivᵉ :
    {l3ᵉ : Level} (Cᵉ : Bᵉ → UUᵉ l3ᵉ) → ((aᵉ : Aᵉ) → Cᵉ (fᵉ aᵉ)) → ((bᵉ : Bᵉ) → Cᵉ bᵉ)
  map-inv-is-equiv-precomp-Π-is-equivᵉ Cᵉ =
    map-inv-is-equivᵉ (is-equiv-precomp-Π-is-equivᵉ Cᵉ)

  is-section-map-inv-is-equiv-precomp-Π-is-equivᵉ :
    {l3ᵉ : Level} (Cᵉ : Bᵉ → UUᵉ l3ᵉ) →
    (hᵉ : (aᵉ : Aᵉ) → Cᵉ (fᵉ aᵉ)) →
    precomp-Πᵉ fᵉ Cᵉ (map-inv-is-equiv-precomp-Π-is-equivᵉ Cᵉ hᵉ) ~ᵉ hᵉ
  is-section-map-inv-is-equiv-precomp-Π-is-equivᵉ Cᵉ hᵉ =
    htpy-eqᵉ (is-section-map-inv-is-equivᵉ (is-equiv-precomp-Π-is-equivᵉ Cᵉ) hᵉ)

  is-retraction-map-inv-is-equiv-precomp-Π-is-equivᵉ :
    {l3ᵉ : Level} (Cᵉ : Bᵉ → UUᵉ l3ᵉ) →
    (gᵉ : (bᵉ : Bᵉ) → Cᵉ bᵉ) →
    map-inv-is-equiv-precomp-Π-is-equivᵉ Cᵉ (precomp-Πᵉ fᵉ Cᵉ gᵉ) ~ᵉ gᵉ
  is-retraction-map-inv-is-equiv-precomp-Π-is-equivᵉ Cᵉ gᵉ =
    htpy-eqᵉ (is-retraction-map-inv-is-equivᵉ (is-equiv-precomp-Π-is-equivᵉ Cᵉ) gᵉ)

equiv-precomp-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  (Cᵉ : Bᵉ → UUᵉ l3ᵉ) → ((bᵉ : Bᵉ) → Cᵉ bᵉ) ≃ᵉ ((aᵉ : Aᵉ) → Cᵉ (map-equivᵉ eᵉ aᵉ))
pr1ᵉ (equiv-precomp-Πᵉ eᵉ Cᵉ) = precomp-Πᵉ (map-equivᵉ eᵉ) Cᵉ
pr2ᵉ (equiv-precomp-Πᵉ eᵉ Cᵉ) = is-equiv-precomp-Π-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) Cᵉ
```
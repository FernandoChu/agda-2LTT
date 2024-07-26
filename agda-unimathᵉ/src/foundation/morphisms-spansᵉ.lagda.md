# Morphisms of spans

```agda
module foundation.morphisms-spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.operations-spansᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "morphismᵉ ofᵉ spans"ᵉ Agda=hom-spanᵉ}} fromᵉ aᵉ
[span](foundation.spans.mdᵉ) `Aᵉ <-f-ᵉ Sᵉ -g->ᵉ B`ᵉ to aᵉ spanᵉ `Aᵉ <-h-ᵉ Tᵉ -k->ᵉ B`ᵉ
consistsᵉ ofᵉ aᵉ mapᵉ `wᵉ : Sᵉ → T`ᵉ [equipped](foundation.structure.mdᵉ) with twoᵉ
[homotopies](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ diagramᵉ

```text
             Sᵉ
           /ᵉ | \ᵉ
        fᵉ /ᵉ  |  \ᵉ hᵉ
         ∨ᵉ   |   ∨ᵉ
        Aᵉ    |wᵉ   Bᵉ
         ∧ᵉ   |   ∧ᵉ
        hᵉ \ᵉ  |  /ᵉ kᵉ
           \ᵉ ∨ᵉ /ᵉ
             Tᵉ
```

[commutes](foundation.commuting-triangles-of-maps.md).ᵉ

## Definitions

### Morphisms between spans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) (tᵉ : spanᵉ l4ᵉ Aᵉ Bᵉ)
  where

  left-coherence-hom-spanᵉ :
    (spanning-type-spanᵉ sᵉ → spanning-type-spanᵉ tᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  left-coherence-hom-spanᵉ =
    coherence-triangle-mapsᵉ (left-map-spanᵉ sᵉ) (left-map-spanᵉ tᵉ)

  right-coherence-hom-spanᵉ :
    (spanning-type-spanᵉ sᵉ → spanning-type-spanᵉ tᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  right-coherence-hom-spanᵉ =
    coherence-triangle-mapsᵉ (right-map-spanᵉ sᵉ) (right-map-spanᵉ tᵉ)

  coherence-hom-spanᵉ :
    (spanning-type-spanᵉ sᵉ → spanning-type-spanᵉ tᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  coherence-hom-spanᵉ fᵉ = left-coherence-hom-spanᵉ fᵉ ×ᵉ right-coherence-hom-spanᵉ fᵉ

  hom-spanᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-spanᵉ = Σᵉ (spanning-type-spanᵉ sᵉ → spanning-type-spanᵉ tᵉ) coherence-hom-spanᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) (tᵉ : spanᵉ l4ᵉ Aᵉ Bᵉ) (fᵉ : hom-spanᵉ sᵉ tᵉ)
  where

  map-hom-spanᵉ : spanning-type-spanᵉ sᵉ → spanning-type-spanᵉ tᵉ
  map-hom-spanᵉ = pr1ᵉ fᵉ

  left-triangle-hom-spanᵉ : left-coherence-hom-spanᵉ sᵉ tᵉ map-hom-spanᵉ
  left-triangle-hom-spanᵉ = pr1ᵉ (pr2ᵉ fᵉ)

  right-triangle-hom-spanᵉ : right-coherence-hom-spanᵉ sᵉ tᵉ map-hom-spanᵉ
  right-triangle-hom-spanᵉ = pr2ᵉ (pr2ᵉ fᵉ)
```
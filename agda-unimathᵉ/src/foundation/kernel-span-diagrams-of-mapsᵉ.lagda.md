# Kernel span diagrams of maps

```agda
module foundation.kernel-span-diagrams-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`.ᵉ Theᵉ
{{#conceptᵉ "kernelᵉ spanᵉ diagram"ᵉ Disambiguation="map"ᵉ Agda=kernel-span-diagramᵉ}}
ofᵉ `f`ᵉ isᵉ theᵉ [spanᵉ diagram](foundation.span-diagrams.mdᵉ)

```text
      pr1ᵉ                           pr1ᵉ ∘ᵉ pr2ᵉ
  Aᵉ <-----ᵉ Σᵉ (xᵉ yᵉ : A),ᵉ fᵉ xᵉ ＝ᵉ fᵉ yᵉ ----------->ᵉ A.ᵉ
```

Weᵉ callᵉ thisᵉ theᵉ kernelᵉ spanᵉ diagram,ᵉ sinceᵉ theᵉ pairᵉ `(pr1ᵉ ,ᵉ pr1ᵉ ∘ᵉ pr2)`ᵉ isᵉ
oftenᵉ calledᵉ theᵉ kernelᵉ pairᵉ ofᵉ aᵉ map.ᵉ

## Definitions

### Kernel span diagrams of maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  spanning-type-kernel-spanᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  spanning-type-kernel-spanᵉ =
    Σᵉ Aᵉ (λ xᵉ → Σᵉ Aᵉ (λ yᵉ → fᵉ xᵉ ＝ᵉ fᵉ yᵉ))

  left-map-kernel-spanᵉ :
    spanning-type-kernel-spanᵉ → Aᵉ
  left-map-kernel-spanᵉ = pr1ᵉ

  right-map-kernel-spanᵉ :
    spanning-type-kernel-spanᵉ → Aᵉ
  right-map-kernel-spanᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  kernel-spanᵉ : spanᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ Aᵉ
  pr1ᵉ kernel-spanᵉ =
    spanning-type-kernel-spanᵉ
  pr1ᵉ (pr2ᵉ kernel-spanᵉ) =
    left-map-kernel-spanᵉ
  pr2ᵉ (pr2ᵉ kernel-spanᵉ) =
    right-map-kernel-spanᵉ

  domain-kernel-span-diagramᵉ : UUᵉ l1ᵉ
  domain-kernel-span-diagramᵉ = Aᵉ

  codomain-kernel-span-diagramᵉ : UUᵉ l1ᵉ
  codomain-kernel-span-diagramᵉ = Aᵉ

  kernel-span-diagramᵉ : span-diagramᵉ l1ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ kernel-span-diagramᵉ = domain-kernel-span-diagramᵉ
  pr1ᵉ (pr2ᵉ kernel-span-diagramᵉ) = codomain-kernel-span-diagramᵉ
  pr2ᵉ (pr2ᵉ kernel-span-diagramᵉ) = kernel-spanᵉ
```
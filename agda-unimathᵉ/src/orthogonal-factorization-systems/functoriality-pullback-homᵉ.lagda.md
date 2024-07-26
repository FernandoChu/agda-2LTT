# Functoriality of the pullback-hom

```agda
module orthogonal-factorization-systems.functoriality-pullback-homᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-typesᵉ
open import foundation.functoriality-pullbacksᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.morphisms-cospan-diagramsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.pullback-homᵉ
```

</details>

## Idea

Theᵉ constructionᵉ ofᵉ theᵉ
[pullback-hom](orthogonal-factorization-systems.pullback-hom.mdᵉ) isᵉ functorial.ᵉ

## Definition

### Functorial action on maps of the pullback-hom

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  {l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {Y'ᵉ : UUᵉ l4'ᵉ}
  (f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : X'ᵉ → Y'ᵉ)
  where

  map-pullback-homᵉ :
    hom-cospan-diagramᵉ
      ( precompᵉ f'ᵉ Y'ᵉ)
      ( postcompᵉ A'ᵉ g'ᵉ)
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ) →
    hom-arrowᵉ f'ᵉ g'ᵉ → hom-arrowᵉ fᵉ gᵉ
  map-pullback-homᵉ =
    map-is-pullbackᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( precompᵉ f'ᵉ Y'ᵉ)
      ( postcompᵉ A'ᵉ g'ᵉ)
      ( cone-hom-arrow-pullback-homᵉ fᵉ gᵉ)
      ( cone-hom-arrow-pullback-homᵉ f'ᵉ g'ᵉ)
      ( is-pullback-cone-hom-arrow-pullback-homᵉ fᵉ gᵉ)
      ( is-pullback-cone-hom-arrow-pullback-homᵉ f'ᵉ g'ᵉ)
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}
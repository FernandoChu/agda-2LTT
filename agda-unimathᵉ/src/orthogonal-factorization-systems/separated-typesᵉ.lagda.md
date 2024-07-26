# Separated types

```agda
module orthogonal-factorization-systems.separated-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **separated**ᵉ with respectᵉ to aᵉ mapᵉ `f`,ᵉ orᵉ
**`f`-separated**,ᵉ ifᵉ itsᵉ [identityᵉ types](foundation-core.identity-types.mdᵉ)
areᵉ [`f`-local](orthogonal-factorization-systems.local-types.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  is-map-separated-familyᵉ : (Xᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-map-separated-familyᵉ Aᵉ = (xᵉ : Xᵉ) (yᵉ zᵉ : Aᵉ xᵉ) → is-localᵉ fᵉ (yᵉ ＝ᵉ zᵉ)

  is-map-separatedᵉ : UUᵉ l3ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-map-separatedᵉ Aᵉ = is-map-separated-familyᵉ (λ _ → Aᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ Rij19ᵉ}}
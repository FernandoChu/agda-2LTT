# Small types

```agda
module foundation.small-typesᵉ where

open import foundation-core.small-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.imagesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.replacementᵉ
open import foundation.surjective-mapsᵉ
open import foundation.uniqueness-imageᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Properties

### If `f` is a surjective map from a small type into a locally small type, then replacement implies that the codomain is small

```agda
is-small-is-surjectiveᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-surjectiveᵉ fᵉ → is-smallᵉ l3ᵉ Aᵉ → is-locally-smallᵉ l3ᵉ Bᵉ →
  is-smallᵉ l3ᵉ Bᵉ
is-small-is-surjectiveᵉ {fᵉ = fᵉ} Hᵉ Kᵉ Lᵉ =
  is-small-equiv'ᵉ
    ( imᵉ fᵉ)
    ( equiv-equiv-slice-uniqueness-imᵉ fᵉ id-embᵉ
      ( fᵉ ,ᵉ refl-htpyᵉ)
      ( is-image-is-surjectiveᵉ fᵉ id-embᵉ (fᵉ ,ᵉ refl-htpyᵉ) Hᵉ))
    ( replacementᵉ fᵉ Kᵉ Lᵉ)
```

## See also

-ᵉ [Smallᵉ maps](foundation.small-maps.mdᵉ)
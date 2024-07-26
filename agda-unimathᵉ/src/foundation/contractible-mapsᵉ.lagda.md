# Contractible maps

```agda
module foundation.contractible-mapsᵉ where

open import foundation-core.contractible-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.truncated-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### Being a contractible map is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-prop-is-contr-mapᵉ : (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-contr-mapᵉ fᵉ)
  is-prop-is-contr-mapᵉ fᵉ = is-prop-is-trunc-mapᵉ neg-two-𝕋ᵉ fᵉ

  is-contr-map-Propᵉ : (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-contr-map-Propᵉ fᵉ) = is-contr-mapᵉ fᵉ
  pr2ᵉ (is-contr-map-Propᵉ fᵉ) = is-prop-is-contr-mapᵉ fᵉ
```

### Being a contractible map is equivalent to being an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-is-equiv-is-contr-mapᵉ : (fᵉ : Aᵉ → Bᵉ) → is-contr-mapᵉ fᵉ ≃ᵉ is-equivᵉ fᵉ
  equiv-is-equiv-is-contr-mapᵉ fᵉ =
    equiv-iffᵉ
      ( is-contr-map-Propᵉ fᵉ)
      ( is-equiv-Propᵉ fᵉ)
      ( is-equiv-is-contr-mapᵉ)
      ( is-contr-map-is-equivᵉ)

  equiv-is-contr-map-is-equivᵉ : (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ ≃ᵉ is-contr-mapᵉ fᵉ
  equiv-is-contr-map-is-equivᵉ fᵉ =
    equiv-iffᵉ
      ( is-equiv-Propᵉ fᵉ)
      ( is-contr-map-Propᵉ fᵉ)
      ( is-contr-map-is-equivᵉ)
      ( is-equiv-is-contr-mapᵉ)
```

### Contractible maps are closed under homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  is-contr-map-htpyᵉ : is-contr-mapᵉ gᵉ → is-contr-mapᵉ fᵉ
  is-contr-map-htpyᵉ = is-trunc-map-htpyᵉ neg-two-𝕋ᵉ Hᵉ
```

### Contractible maps are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ)
  where

  is-contr-map-compᵉ : is-contr-mapᵉ gᵉ → is-contr-mapᵉ hᵉ → is-contr-mapᵉ (gᵉ ∘ᵉ hᵉ)
  is-contr-map-compᵉ = is-trunc-map-compᵉ neg-two-𝕋ᵉ gᵉ hᵉ
```

### In a commuting triangle `f ~ g ∘ h`, if `g` and `h` are contractible maps, then `f` is a contractible map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ))
  where

  is-contr-map-left-map-triangleᵉ :
    is-contr-mapᵉ gᵉ → is-contr-mapᵉ hᵉ → is-contr-mapᵉ fᵉ
  is-contr-map-left-map-triangleᵉ =
    is-trunc-map-left-map-triangleᵉ neg-two-𝕋ᵉ fᵉ gᵉ hᵉ Hᵉ
```

### In a commuting triangle `f ~ g ∘ h`, if `f` and `g` are contractible maps, then `h` is a contractible map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ))
  where

  is-contr-map-top-map-triangleᵉ :
    is-contr-mapᵉ gᵉ → is-contr-mapᵉ fᵉ → is-contr-mapᵉ hᵉ
  is-contr-map-top-map-triangleᵉ =
    is-trunc-map-top-map-triangleᵉ neg-two-𝕋ᵉ fᵉ gᵉ hᵉ Hᵉ
```

### If a composite `g ∘ h` and its left factor `g` are contractible maps, then its right factor `h` is a contractible map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ)
  where

  is-contr-map-right-factorᵉ :
    is-contr-mapᵉ gᵉ → is-contr-mapᵉ (gᵉ ∘ᵉ hᵉ) → is-contr-mapᵉ hᵉ
  is-contr-map-right-factorᵉ =
    is-trunc-map-right-factorᵉ neg-two-𝕋ᵉ gᵉ hᵉ
```

## See also

-ᵉ Forᵉ theᵉ notionᵉ ofᵉ biinvertibleᵉ mapsᵉ seeᵉ
  [`foundation.equivalences`](foundation.equivalences.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ coherentlyᵉ invertibleᵉ maps,ᵉ alsoᵉ knownᵉ asᵉ half-adjointᵉ
  equivalences,ᵉ seeᵉ
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ path-splitᵉ mapsᵉ seeᵉ
  [`foundation.path-split-maps`](foundation.path-split-maps.md).ᵉ
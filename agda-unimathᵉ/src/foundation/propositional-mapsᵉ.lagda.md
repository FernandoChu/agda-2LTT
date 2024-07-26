# Propositional maps

```agda
module foundation.propositional-mapsᵉ where

open import foundation-core.propositional-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.truncated-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### Being a propositional map is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-prop-is-prop-mapᵉ : (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-prop-mapᵉ fᵉ)
  is-prop-is-prop-mapᵉ fᵉ = is-prop-is-trunc-mapᵉ neg-one-𝕋ᵉ fᵉ

  is-prop-map-Propᵉ : (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-prop-map-Propᵉ fᵉ) = is-prop-mapᵉ fᵉ
  pr2ᵉ (is-prop-map-Propᵉ fᵉ) = is-prop-is-prop-mapᵉ fᵉ
```

### Being a propositional map is equivalent to being an embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-is-emb-is-prop-mapᵉ : (fᵉ : Aᵉ → Bᵉ) → is-prop-mapᵉ fᵉ ≃ᵉ is-embᵉ fᵉ
  equiv-is-emb-is-prop-mapᵉ fᵉ =
    equiv-iffᵉ
      ( is-prop-map-Propᵉ fᵉ)
      ( is-emb-Propᵉ fᵉ)
      ( is-emb-is-prop-mapᵉ)
      ( is-prop-map-is-embᵉ)

  equiv-is-prop-map-is-embᵉ : (fᵉ : Aᵉ → Bᵉ) → is-embᵉ fᵉ ≃ᵉ is-prop-mapᵉ fᵉ
  equiv-is-prop-map-is-embᵉ fᵉ =
    equiv-iffᵉ
      ( is-emb-Propᵉ fᵉ)
      ( is-prop-map-Propᵉ fᵉ)
      ( is-prop-map-is-embᵉ)
      ( is-emb-is-prop-mapᵉ)
```

### Propositional maps are closed under homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  is-prop-map-htpyᵉ : is-prop-mapᵉ gᵉ → is-prop-mapᵉ fᵉ
  is-prop-map-htpyᵉ = is-trunc-map-htpyᵉ neg-one-𝕋ᵉ Hᵉ
```

### Propositional maps are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ)
  where

  is-prop-map-compᵉ : is-prop-mapᵉ gᵉ → is-prop-mapᵉ hᵉ → is-prop-mapᵉ (gᵉ ∘ᵉ hᵉ)
  is-prop-map-compᵉ = is-trunc-map-compᵉ neg-one-𝕋ᵉ gᵉ hᵉ

comp-prop-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {Xᵉ : UUᵉ l3ᵉ} (gᵉ : prop-mapᵉ Bᵉ Xᵉ) (hᵉ : prop-mapᵉ Aᵉ Bᵉ) →
  prop-mapᵉ Aᵉ Xᵉ
pr1ᵉ (comp-prop-mapᵉ gᵉ hᵉ) = pr1ᵉ gᵉ ∘ᵉ pr1ᵉ hᵉ
pr2ᵉ (comp-prop-mapᵉ gᵉ hᵉ) =
  is-prop-map-compᵉ (pr1ᵉ gᵉ) (pr1ᵉ hᵉ) (pr2ᵉ gᵉ) (pr2ᵉ hᵉ)
```

### In a commuting triangle `f ~ g ∘ h`, if `g` and `h` are propositional maps, then `f` is a propositional map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ))
  where

  is-prop-map-left-map-triangleᵉ :
    is-prop-mapᵉ gᵉ → is-prop-mapᵉ hᵉ → is-prop-mapᵉ fᵉ
  is-prop-map-left-map-triangleᵉ =
    is-trunc-map-left-map-triangleᵉ neg-one-𝕋ᵉ fᵉ gᵉ hᵉ Hᵉ
```

### In a commuting triangle `f ~ g ∘ h`, if `f` and `g` are propositional maps, then `h` is a propositional map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ))
  where

  is-prop-map-top-map-triangleᵉ :
    is-prop-mapᵉ gᵉ → is-prop-mapᵉ fᵉ → is-prop-mapᵉ hᵉ
  is-prop-map-top-map-triangleᵉ =
    is-trunc-map-top-map-triangleᵉ neg-one-𝕋ᵉ fᵉ gᵉ hᵉ Hᵉ
```

### If a composite `g ∘ h` and its left factor `g` are propositional maps, then its right factor `h` is a propositional map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ)
  where

  is-prop-map-right-factorᵉ :
    is-prop-mapᵉ gᵉ → is-prop-mapᵉ (gᵉ ∘ᵉ hᵉ) → is-prop-mapᵉ hᵉ
  is-prop-map-right-factorᵉ =
    is-trunc-map-right-factorᵉ neg-one-𝕋ᵉ gᵉ hᵉ
```

### A `-1`-truncated map is `k+1`-truncated

```agda
abstract
  is-trunc-map-is-prop-mapᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-prop-mapᵉ fᵉ → is-trunc-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ
  is-trunc-map-is-prop-mapᵉ neg-two-𝕋ᵉ Hᵉ = Hᵉ
  is-trunc-map-is-prop-mapᵉ (succ-𝕋ᵉ kᵉ) Hᵉ =
    is-trunc-map-succ-is-trunc-mapᵉ (succ-𝕋ᵉ kᵉ) (is-trunc-map-is-prop-mapᵉ kᵉ Hᵉ)
```
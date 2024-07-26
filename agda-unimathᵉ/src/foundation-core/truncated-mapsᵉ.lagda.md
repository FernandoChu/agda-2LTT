# Truncated maps

```agda
module foundation-core.truncated-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ mapᵉ isᵉ `k`-truncatedᵉ ifᵉ itsᵉ fibersᵉ areᵉ `k`-truncated.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ)
  where

  is-trunc-mapᵉ : {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-trunc-mapᵉ fᵉ = (yᵉ : _) → is-truncᵉ kᵉ (fiberᵉ fᵉ yᵉ)

  trunc-mapᵉ : (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  trunc-mapᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) is-trunc-mapᵉ

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-trunc-mapᵉ : trunc-mapᵉ kᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ
  map-trunc-mapᵉ = pr1ᵉ

  abstract
    is-trunc-map-map-trunc-mapᵉ :
      (fᵉ : trunc-mapᵉ kᵉ Aᵉ Bᵉ) → is-trunc-mapᵉ kᵉ (map-trunc-mapᵉ fᵉ)
    is-trunc-map-map-trunc-mapᵉ = pr2ᵉ
```

## Properties

### If a map is `k`-truncated, then it is `k+1`-truncated

```agda
abstract
  is-trunc-map-succ-is-trunc-mapᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
    {fᵉ : Aᵉ → Bᵉ} → is-trunc-mapᵉ kᵉ fᵉ → is-trunc-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ
  is-trunc-map-succ-is-trunc-mapᵉ kᵉ is-trunc-fᵉ bᵉ =
    is-trunc-succ-is-truncᵉ kᵉ (is-trunc-fᵉ bᵉ)
```

### Any contractible map is `k`-truncated

```agda
is-trunc-map-is-contr-mapᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-contr-mapᵉ fᵉ → is-trunc-mapᵉ kᵉ fᵉ
is-trunc-map-is-contr-mapᵉ neg-two-𝕋ᵉ Hᵉ = Hᵉ
is-trunc-map-is-contr-mapᵉ (succ-𝕋ᵉ kᵉ) Hᵉ =
  is-trunc-map-succ-is-trunc-mapᵉ kᵉ (is-trunc-map-is-contr-mapᵉ kᵉ Hᵉ)
```

### Any equivalence is `k`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-trunc-map-is-equivᵉ :
    {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-trunc-mapᵉ kᵉ fᵉ
  is-trunc-map-is-equivᵉ Hᵉ =
    is-trunc-map-is-contr-mapᵉ kᵉ (is-contr-map-is-equivᵉ Hᵉ)

  is-trunc-map-equivᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-trunc-mapᵉ kᵉ (map-equivᵉ eᵉ)
  is-trunc-map-equivᵉ eᵉ = is-trunc-map-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)
```

### A map is `k+1`-truncated if and only if its action on identifications is `k`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-trunc-map-is-trunc-map-apᵉ :
      ((xᵉ yᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (apᵉ fᵉ {xᵉ} {yᵉ})) → is-trunc-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ
    is-trunc-map-is-trunc-map-apᵉ is-trunc-map-ap-fᵉ bᵉ (pairᵉ xᵉ pᵉ) (pairᵉ x'ᵉ p'ᵉ) =
      is-trunc-equivᵉ kᵉ
        ( fiberᵉ (apᵉ fᵉ) (pᵉ ∙ᵉ (invᵉ p'ᵉ)))
        ( equiv-fiber-ap-eq-fiberᵉ fᵉ (pairᵉ xᵉ pᵉ) (pairᵉ x'ᵉ p'ᵉ))
        ( is-trunc-map-ap-fᵉ xᵉ x'ᵉ (pᵉ ∙ᵉ (invᵉ p'ᵉ)))

  abstract
    is-trunc-map-ap-is-trunc-mapᵉ :
      is-trunc-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ → (xᵉ yᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (apᵉ fᵉ {xᵉ} {yᵉ})
    is-trunc-map-ap-is-trunc-mapᵉ is-trunc-map-fᵉ xᵉ yᵉ pᵉ =
      is-trunc-is-equiv'ᵉ kᵉ
        ( pairᵉ xᵉ pᵉ ＝ᵉ pairᵉ yᵉ reflᵉ)
        ( eq-fiber-fiber-apᵉ fᵉ xᵉ yᵉ pᵉ)
        ( is-equiv-eq-fiber-fiber-apᵉ fᵉ xᵉ yᵉ pᵉ)
        ( is-trunc-map-fᵉ (fᵉ yᵉ) (pairᵉ xᵉ pᵉ) (pairᵉ yᵉ reflᵉ))
```

### The domain of any `k`-truncated map into a `k+1`-truncated type is `k+1`-truncated

```agda
is-trunc-is-trunc-map-into-is-truncᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ → is-trunc-mapᵉ kᵉ fᵉ →
  is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
is-trunc-is-trunc-map-into-is-truncᵉ neg-two-𝕋ᵉ fᵉ is-trunc-Bᵉ is-trunc-map-fᵉ =
  is-trunc-is-equivᵉ _ _ fᵉ (is-equiv-is-contr-mapᵉ is-trunc-map-fᵉ) is-trunc-Bᵉ
is-trunc-is-trunc-map-into-is-truncᵉ
  (succ-𝕋ᵉ kᵉ) fᵉ is-trunc-Bᵉ is-trunc-map-fᵉ aᵉ a'ᵉ =
  is-trunc-is-trunc-map-into-is-truncᵉ
    ( kᵉ)
    ( apᵉ fᵉ)
    ( is-trunc-Bᵉ (fᵉ aᵉ) (fᵉ a'ᵉ))
    ( is-trunc-map-ap-is-trunc-mapᵉ kᵉ fᵉ is-trunc-map-fᵉ aᵉ a'ᵉ)
```

### A family of types is a family of `k`-truncated types if and only of the projection map is `k`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-trunc-map-pr1ᵉ :
      {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → ((xᵉ : Aᵉ) → is-truncᵉ kᵉ (Bᵉ xᵉ)) →
      is-trunc-mapᵉ kᵉ (pr1ᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ})
    is-trunc-map-pr1ᵉ {Bᵉ} Hᵉ xᵉ =
      is-trunc-equivᵉ kᵉ (Bᵉ xᵉ) (equiv-fiber-pr1ᵉ Bᵉ xᵉ) (Hᵉ xᵉ)

  pr1-trunc-mapᵉ :
    (Bᵉ : Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) → trunc-mapᵉ kᵉ (Σᵉ Aᵉ (λ xᵉ → pr1ᵉ (Bᵉ xᵉ))) Aᵉ
  pr1ᵉ (pr1-trunc-mapᵉ Bᵉ) = pr1ᵉ
  pr2ᵉ (pr1-trunc-mapᵉ Bᵉ) = is-trunc-map-pr1ᵉ (λ xᵉ → pr2ᵉ (Bᵉ xᵉ))

  abstract
    is-trunc-is-trunc-map-pr1ᵉ :
      (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → is-trunc-mapᵉ kᵉ (pr1ᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ}) →
      (xᵉ : Aᵉ) → is-truncᵉ kᵉ (Bᵉ xᵉ)
    is-trunc-is-trunc-map-pr1ᵉ Bᵉ is-trunc-map-pr1ᵉ xᵉ =
      is-trunc-equivᵉ kᵉ
        ( fiberᵉ pr1ᵉ xᵉ)
        ( inv-equiv-fiber-pr1ᵉ Bᵉ xᵉ)
        ( is-trunc-map-pr1ᵉ xᵉ)
```

### Any map between `k`-truncated types is `k`-truncated

```agda
abstract
  is-trunc-map-is-trunc-domain-codomainᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ}
    {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} → is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ Bᵉ → is-trunc-mapᵉ kᵉ fᵉ
  is-trunc-map-is-trunc-domain-codomainᵉ kᵉ {fᵉ = fᵉ} is-trunc-Aᵉ is-trunc-Bᵉ bᵉ =
    is-trunc-Σᵉ is-trunc-Aᵉ (λ xᵉ → is-trunc-Idᵉ is-trunc-Bᵉ (fᵉ xᵉ) bᵉ)
```

### A type family over a `k`-truncated type A is a family of `k`-truncated types if its total space is `k`-truncated

```agda
abstract
  is-trunc-fam-is-trunc-Σᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ) → (xᵉ : Aᵉ) → is-truncᵉ kᵉ (Bᵉ xᵉ)
  is-trunc-fam-is-trunc-Σᵉ kᵉ {Bᵉ = Bᵉ} is-trunc-Aᵉ is-trunc-ΣABᵉ xᵉ =
    is-trunc-equiv'ᵉ kᵉ
      ( fiberᵉ pr1ᵉ xᵉ)
      ( equiv-fiber-pr1ᵉ Bᵉ xᵉ)
      ( is-trunc-map-is-trunc-domain-codomainᵉ kᵉ is-trunc-ΣABᵉ is-trunc-Aᵉ xᵉ)
```

### Truncated maps are closed under homotopies

```agda
abstract
  is-trunc-map-htpyᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
    {fᵉ gᵉ : Aᵉ → Bᵉ} → fᵉ ~ᵉ gᵉ → is-trunc-mapᵉ kᵉ gᵉ → is-trunc-mapᵉ kᵉ fᵉ
  is-trunc-map-htpyᵉ kᵉ {Aᵉ} {Bᵉ} {fᵉ} {gᵉ} Hᵉ is-trunc-gᵉ bᵉ =
    is-trunc-is-equivᵉ kᵉ
      ( Σᵉ Aᵉ (λ zᵉ → gᵉ zᵉ ＝ᵉ bᵉ))
      ( fiber-triangleᵉ fᵉ gᵉ idᵉ Hᵉ bᵉ)
      ( is-fiberwise-equiv-is-equiv-triangleᵉ fᵉ gᵉ idᵉ Hᵉ is-equiv-idᵉ bᵉ)
      ( is-trunc-gᵉ bᵉ)
```

### Truncated maps are closed under composition

```agda
abstract
  is-trunc-map-compᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
    {Xᵉ : UUᵉ l3ᵉ} (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-trunc-mapᵉ kᵉ gᵉ → is-trunc-mapᵉ kᵉ hᵉ → is-trunc-mapᵉ kᵉ (gᵉ ∘ᵉ hᵉ)
  is-trunc-map-compᵉ kᵉ gᵉ hᵉ is-trunc-gᵉ is-trunc-hᵉ xᵉ =
    is-trunc-is-equivᵉ kᵉ
        ( Σᵉ (fiberᵉ gᵉ xᵉ) (λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ)))
        ( map-compute-fiber-compᵉ gᵉ hᵉ xᵉ)
        ( is-equiv-map-compute-fiber-compᵉ gᵉ hᵉ xᵉ)
        ( is-trunc-Σᵉ
          ( is-trunc-gᵉ xᵉ)
          ( λ tᵉ → is-trunc-hᵉ (pr1ᵉ tᵉ)))

comp-trunc-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {Xᵉ : UUᵉ l3ᵉ} (gᵉ : trunc-mapᵉ kᵉ Bᵉ Xᵉ) (hᵉ : trunc-mapᵉ kᵉ Aᵉ Bᵉ) →
  trunc-mapᵉ kᵉ Aᵉ Xᵉ
pr1ᵉ (comp-trunc-mapᵉ kᵉ gᵉ hᵉ) = pr1ᵉ gᵉ ∘ᵉ pr1ᵉ hᵉ
pr2ᵉ (comp-trunc-mapᵉ kᵉ gᵉ hᵉ) =
  is-trunc-map-compᵉ kᵉ (pr1ᵉ gᵉ) (pr1ᵉ hᵉ) (pr2ᵉ gᵉ) (pr2ᵉ hᵉ)
```

### In a commuting triangle `f ~ g ∘ h`, if `g` and `h` are truncated maps, then `f` is a truncated map

```agda
abstract
  is-trunc-map-left-map-triangleᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
    {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
    is-trunc-mapᵉ kᵉ gᵉ → is-trunc-mapᵉ kᵉ hᵉ → is-trunc-mapᵉ kᵉ fᵉ
  is-trunc-map-left-map-triangleᵉ kᵉ fᵉ gᵉ hᵉ Hᵉ is-trunc-gᵉ is-trunc-hᵉ =
    is-trunc-map-htpyᵉ kᵉ Hᵉ
      ( is-trunc-map-compᵉ kᵉ gᵉ hᵉ is-trunc-gᵉ is-trunc-hᵉ)
```

### In a commuting triangle `f ~ g ∘ h`, if `f` and `g` are truncated maps, then `h` is a truncated map

```agda
abstract
  is-trunc-map-top-map-triangleᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
    is-trunc-mapᵉ kᵉ gᵉ → is-trunc-mapᵉ kᵉ fᵉ → is-trunc-mapᵉ kᵉ hᵉ
  is-trunc-map-top-map-triangleᵉ kᵉ {Aᵉ} fᵉ gᵉ hᵉ Hᵉ is-trunc-gᵉ is-trunc-fᵉ bᵉ =
    is-trunc-fam-is-trunc-Σᵉ kᵉ
      ( is-trunc-gᵉ (gᵉ bᵉ))
      ( is-trunc-is-equiv'ᵉ kᵉ
        ( Σᵉ Aᵉ (λ zᵉ → gᵉ (hᵉ zᵉ) ＝ᵉ gᵉ bᵉ))
        ( map-compute-fiber-compᵉ gᵉ hᵉ (gᵉ bᵉ))
        ( is-equiv-map-compute-fiber-compᵉ gᵉ hᵉ (gᵉ bᵉ))
        ( is-trunc-map-htpyᵉ kᵉ (inv-htpyᵉ Hᵉ) is-trunc-fᵉ (gᵉ bᵉ)))
      ( pairᵉ bᵉ reflᵉ)
```

### If a composite `g ∘ h` and its left factor `g` are truncated maps, then its right factor `h` is a truncated map

```agda
is-trunc-map-right-factorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
  is-trunc-mapᵉ kᵉ gᵉ → is-trunc-mapᵉ kᵉ (gᵉ ∘ᵉ hᵉ) → is-trunc-mapᵉ kᵉ hᵉ
is-trunc-map-right-factorᵉ kᵉ {Aᵉ} gᵉ hᵉ =
  is-trunc-map-top-map-triangleᵉ kᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ
```

### In a commuting square with the left and right maps equivalences, the top map is truncated if and only if the bottom map is truncated

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (iᵉ : Cᵉ → Dᵉ)
  (Hᵉ : coherence-square-mapsᵉ fᵉ gᵉ hᵉ iᵉ)
  where

  is-trunc-map-top-is-trunc-map-bottom-is-equivᵉ :
    is-equivᵉ gᵉ → is-equivᵉ hᵉ → is-trunc-mapᵉ kᵉ iᵉ → is-trunc-mapᵉ kᵉ fᵉ
  is-trunc-map-top-is-trunc-map-bottom-is-equivᵉ Kᵉ Lᵉ Mᵉ =
    is-trunc-map-top-map-triangleᵉ kᵉ (iᵉ ∘ᵉ gᵉ) hᵉ fᵉ Hᵉ
      ( is-trunc-map-is-equivᵉ kᵉ Lᵉ)
      ( is-trunc-map-compᵉ kᵉ iᵉ gᵉ Mᵉ
        ( is-trunc-map-is-equivᵉ kᵉ Kᵉ))
```
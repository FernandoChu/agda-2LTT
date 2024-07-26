# Split surjective maps

```agda
module foundation.split-surjective-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ splitᵉ surjectiveᵉ ifᵉ weᵉ canᵉ constructᵉ forᵉ everyᵉ `bᵉ : B`ᵉ anᵉ
elementᵉ in theᵉ fiberᵉ ofᵉ `b`,ᵉ meaningᵉ anᵉ elementᵉ `aᵉ : A`ᵉ equippedᵉ with anᵉ
identificationᵉ `fᵉ aᵉ ＝ᵉ b`.ᵉ

## Warning

Noteᵉ thatᵉ split-surjectivenessᵉ isᵉ theᵉ Curry-Howardᵉ interpretationᵉ ofᵉ
surjectiveness.ᵉ However,ᵉ thisᵉ isᵉ notᵉ aᵉ property,ᵉ andᵉ theᵉ splitᵉ surjectiveᵉ mapsᵉ
don'tᵉ fitᵉ in aᵉ factorizationᵉ systemᵉ alongᵉ with theᵉ injectiveᵉ maps.ᵉ

## Definition

### Split surjective maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-split-surjectiveᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-split-surjectiveᵉ fᵉ = (bᵉ : Bᵉ) → fiberᵉ fᵉ bᵉ

  split-surjectionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  split-surjectionᵉ = Σᵉ (Aᵉ → Bᵉ) is-split-surjectiveᵉ

  map-split-surjectionᵉ : split-surjectionᵉ → (Aᵉ → Bᵉ)
  map-split-surjectionᵉ = pr1ᵉ

  is-split-surjective-split-surjectionᵉ :
    (fᵉ : split-surjectionᵉ) → is-split-surjectiveᵉ (map-split-surjectionᵉ fᵉ)
  is-split-surjective-split-surjectionᵉ = pr2ᵉ
```

## Properties

### Split surjections are equivalent to maps equipped with a section

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  section-is-split-surjectiveᵉ : is-split-surjectiveᵉ fᵉ → sectionᵉ fᵉ
  pr1ᵉ (section-is-split-surjectiveᵉ sᵉ) = pr1ᵉ ∘ᵉ sᵉ
  pr2ᵉ (section-is-split-surjectiveᵉ sᵉ) = pr2ᵉ ∘ᵉ sᵉ

  is-split-surjective-sectionᵉ : sectionᵉ fᵉ → is-split-surjectiveᵉ fᵉ
  pr1ᵉ (is-split-surjective-sectionᵉ sᵉ bᵉ) = pr1ᵉ sᵉ bᵉ
  pr2ᵉ (is-split-surjective-sectionᵉ sᵉ bᵉ) = pr2ᵉ sᵉ bᵉ

  equiv-section-is-split-surjectiveᵉ : is-split-surjectiveᵉ fᵉ ≃ᵉ sectionᵉ fᵉ
  equiv-section-is-split-surjectiveᵉ = distributive-Π-Σᵉ

  equiv-is-split-surjective-sectionᵉ : sectionᵉ fᵉ ≃ᵉ is-split-surjectiveᵉ fᵉ
  equiv-is-split-surjective-sectionᵉ = inv-distributive-Π-Σᵉ
```

### A map is an equivalence if and only if it is injective and split surjective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  retraction-is-split-surjective-is-injectiveᵉ :
    is-injectiveᵉ fᵉ → is-split-surjectiveᵉ fᵉ → retractionᵉ fᵉ
  pr1ᵉ (retraction-is-split-surjective-is-injectiveᵉ lᵉ sᵉ) = pr1ᵉ ∘ᵉ sᵉ
  pr2ᵉ (retraction-is-split-surjective-is-injectiveᵉ lᵉ sᵉ) = lᵉ ∘ᵉ (pr2ᵉ ∘ᵉ (sᵉ ∘ᵉ fᵉ))

  is-equiv-is-split-surjective-is-injectiveᵉ :
    is-injectiveᵉ fᵉ → is-split-surjectiveᵉ fᵉ → is-equivᵉ fᵉ
  pr1ᵉ (is-equiv-is-split-surjective-is-injectiveᵉ lᵉ sᵉ) =
    section-is-split-surjectiveᵉ fᵉ sᵉ
  pr2ᵉ (is-equiv-is-split-surjective-is-injectiveᵉ lᵉ sᵉ) =
    retraction-is-split-surjective-is-injectiveᵉ lᵉ sᵉ

  is-split-surjective-is-equivᵉ : is-equivᵉ fᵉ → is-split-surjectiveᵉ fᵉ
  is-split-surjective-is-equivᵉ = is-split-surjective-sectionᵉ fᵉ ∘ᵉ pr1ᵉ

  is-split-surjective-is-injective-is-equivᵉ :
    is-equivᵉ fᵉ → is-injectiveᵉ fᵉ ×ᵉ is-split-surjectiveᵉ fᵉ
  pr1ᵉ (is-split-surjective-is-injective-is-equivᵉ is-equiv-fᵉ) =
    is-injective-is-equivᵉ is-equiv-fᵉ
  pr2ᵉ (is-split-surjective-is-injective-is-equivᵉ is-equiv-fᵉ) =
    is-split-surjective-is-equivᵉ is-equiv-fᵉ
```
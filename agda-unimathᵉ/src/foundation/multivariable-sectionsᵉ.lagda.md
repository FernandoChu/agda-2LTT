# Multivariable sections

```agda
module foundation.multivariable-sectionsᵉ where

open import foundation.telescopesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.multivariable-homotopiesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Aᵉ **multivariableᵉ section**ᵉ isᵉ aᵉ mapᵉ ofᵉ multivariableᵉ mapsᵉ thatᵉ isᵉ aᵉ rightᵉ
inverse.ᵉ Thus,ᵉ aᵉ mapᵉ

```text
  sᵉ : ((x₁ᵉ : A₁ᵉ) ... (xₙᵉ : Aₙᵉ) → Aᵉ xᵉ) → (y₁ᵉ : B₁ᵉ) ... (yₙᵉ : Bₙᵉ) → Bᵉ yᵉ
```

isᵉ aᵉ sectionᵉ ofᵉ aᵉ mapᵉ ofᵉ typeᵉ

```text
  fᵉ : ((y₁ᵉ : B₁ᵉ) ... (yₙᵉ : Bₙᵉ) → Bᵉ yᵉ) → (x₁ᵉ : A₁ᵉ) ... (xₙᵉ : Aₙᵉ) → Aᵉ xᵉ
```

ifᵉ theᵉ compositionᵉ `fᵉ ∘ᵉ s`ᵉ isᵉ
[multivariableᵉ homotopic](foundation.multivariable-homotopies.mdᵉ) to theᵉ
identityᵉ atᵉ

```text
  (y₁ᵉ : B₁ᵉ) ... (yₙᵉ : Bₙᵉ) → Bᵉ y.ᵉ
```

Noteᵉ thatᵉ sectionsᵉ ofᵉ multivariableᵉ mapsᵉ areᵉ equivalentᵉ to commonᵉ
[sections](foundation-core.sections.mdᵉ) byᵉ functionᵉ extensionality,ᵉ soᵉ thisᵉ
definitionᵉ onlyᵉ findsᵉ itᵉ utilityᵉ in avoidingᵉ unnecessaryᵉ applicationsᵉ ofᵉ
[functionᵉ extensionality](foundation.function-extensionality.md).ᵉ Forᵉ instance,ᵉ
thisᵉ isᵉ usefulᵉ whenᵉ definingᵉ inductionᵉ principlesᵉ onᵉ functionᵉ types.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ)
  {{Aᵉ : telescopeᵉ l1ᵉ nᵉ}} {{Bᵉ : telescopeᵉ l2ᵉ nᵉ}}
  (fᵉ : iterated-Πᵉ Aᵉ → iterated-Πᵉ Bᵉ)
  where

  multivariable-sectionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  multivariable-sectionᵉ =
    Σᵉ ( iterated-Πᵉ Bᵉ → iterated-Πᵉ Aᵉ)
      ( λ sᵉ →
        multivariable-htpyᵉ
          { nᵉ = succ-ℕᵉ nᵉ}
          {{Aᵉ = prepend-telescopeᵉ (iterated-Πᵉ Bᵉ) Bᵉ}}
          ( fᵉ ∘ᵉ sᵉ)
          ( idᵉ))

  map-multivariable-sectionᵉ :
    multivariable-sectionᵉ → iterated-Πᵉ Bᵉ → iterated-Πᵉ Aᵉ
  map-multivariable-sectionᵉ = pr1ᵉ

  is-multivariable-section-map-multivariable-sectionᵉ :
    (sᵉ : multivariable-sectionᵉ) →
    multivariable-htpyᵉ
      { nᵉ = succ-ℕᵉ nᵉ}
      {{Aᵉ = prepend-telescopeᵉ (iterated-Πᵉ Bᵉ) Bᵉ}}
      ( fᵉ ∘ᵉ map-multivariable-sectionᵉ sᵉ)
      ( idᵉ)
  is-multivariable-section-map-multivariable-sectionᵉ = pr2ᵉ
```
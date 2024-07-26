# Iterated dependent product types

```agda
module foundation.iterated-dependent-product-typesᵉ where

open import foundation.telescopesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.implicit-function-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

**Iteratedᵉ dependentᵉ products**ᵉ areᵉ definedᵉ byᵉ iterativelyᵉ applyingᵉ theᵉ builtᵉ in
dependentᵉ functionᵉ typeᵉ operator.ᵉ Moreᵉ formally,ᵉ `iterated-Π`ᵉ isᵉ definedᵉ asᵉ anᵉ
operationᵉ `telescopeᵉ lᵉ nᵉ → UUᵉ l`ᵉ fromᵉ theᵉ typeᵉ ofᵉ
[telescopes](foundation.telescopes.mdᵉ) to theᵉ universeᵉ ofᵉ typesᵉ ofᵉ universeᵉ
levelᵉ `l`.ᵉ Forᵉ example,ᵉ theᵉ iteratedᵉ dependentᵉ productᵉ ofᵉ theᵉ telescopeᵉ

```text
  A₀ᵉ : 𝒰ᵉ l₀ᵉ
  A₁ᵉ : A₀ᵉ → 𝒰ᵉ l₁ᵉ
  A₂ᵉ : (x₀ᵉ : A₀ᵉ) → A₁ᵉ x₀ᵉ → 𝒰ᵉ l₂ᵉ
  A₃ᵉ : (x₀ᵉ : A₀ᵉ) (x₁ᵉ : A₁ᵉ x₀ᵉ) → A₂ᵉ x₀ᵉ x₁ᵉ → 𝒰ᵉ l₃ᵉ
```

isᵉ theᵉ dependentᵉ productᵉ typeᵉ

```text
  (x₀ᵉ : A₀ᵉ) (x₁ᵉ : A₁ᵉ x₀ᵉ) (x₂ᵉ : A₂ᵉ x₀ᵉ x₁ᵉ) → A₃ᵉ x₀ᵉ x₁ᵉ x₂ᵉ
```

ofᵉ universeᵉ levelᵉ `l₀ᵉ ⊔ l₁ᵉ ⊔ l₂ᵉ ⊔ l₃`.ᵉ

## Definitions

### Iterated dependent products of iterated type families

```agda
iterated-Πᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} → telescopeᵉ lᵉ nᵉ → UUᵉ lᵉ
iterated-Πᵉ (base-telescopeᵉ Aᵉ) = Aᵉ
iterated-Πᵉ (cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ) = (xᵉ : Xᵉ) → iterated-Πᵉ (Aᵉ xᵉ)

iterated-implicit-Πᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} → telescopeᵉ lᵉ nᵉ → UUᵉ lᵉ
iterated-implicit-Πᵉ (base-telescopeᵉ Aᵉ) = Aᵉ
iterated-implicit-Πᵉ (cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ) =
  {xᵉ : Xᵉ} → iterated-implicit-Πᵉ (Aᵉ xᵉ)
```

### Iterated sections of type families

```agda
data
  iterated-sectionᵉ : {lᵉ : Level} {nᵉ : ℕᵉ} → telescopeᵉ lᵉ nᵉ → UUωᵉ
  where
  base-iterated-sectionᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Aᵉ → iterated-sectionᵉ (base-telescopeᵉ Aᵉ)
  cons-iterated-sectionᵉ :
    {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : Xᵉ → telescopeᵉ l2ᵉ nᵉ} →
    ((xᵉ : Xᵉ) → iterated-sectionᵉ (Yᵉ xᵉ)) → iterated-sectionᵉ (cons-telescopeᵉ Yᵉ)
```

### Iterated λ-abstractions

```agda
iterated-λᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : telescopeᵉ lᵉ nᵉ} →
  iterated-sectionᵉ Aᵉ → iterated-Πᵉ Aᵉ
iterated-λᵉ (base-iterated-sectionᵉ aᵉ) = aᵉ
iterated-λᵉ (cons-iterated-sectionᵉ fᵉ) xᵉ = iterated-λᵉ (fᵉ xᵉ)
```

### Transforming iterated products

Givenᵉ anᵉ operationᵉ onᵉ universes,ᵉ weᵉ canᵉ applyᵉ itᵉ atᵉ theᵉ codomainᵉ ofᵉ theᵉ iteratedᵉ
product.ᵉ

```agda
apply-codomain-iterated-Πᵉ :
  {l1ᵉ : Level} {nᵉ : ℕᵉ}
  (Pᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ) → telescopeᵉ l1ᵉ nᵉ → UUᵉ l1ᵉ
apply-codomain-iterated-Πᵉ Pᵉ Aᵉ = iterated-Πᵉ (apply-base-telescopeᵉ Pᵉ Aᵉ)

apply-codomain-iterated-implicit-Πᵉ :
  {l1ᵉ : Level} {nᵉ : ℕᵉ}
  (Pᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ) → telescopeᵉ l1ᵉ nᵉ → UUᵉ l1ᵉ
apply-codomain-iterated-implicit-Πᵉ Pᵉ Aᵉ =
  iterated-implicit-Πᵉ (apply-base-telescopeᵉ Pᵉ Aᵉ)
```

## Properties

### If a dependent product satisfies a property if its codomain does, then iterated dependent products satisfy that property if the codomain does

```agda
section-iterated-Π-section-Π-section-codomainᵉ :
  (Pᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ) →
  ( {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → Pᵉ (Bᵉ xᵉ)) → Pᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)) →
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  apply-codomain-iterated-Πᵉ Pᵉ Aᵉ → Pᵉ (iterated-Πᵉ Aᵉ)
section-iterated-Π-section-Π-section-codomainᵉ Pᵉ fᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} Hᵉ =
  Hᵉ
section-iterated-Π-section-Π-section-codomainᵉ Pᵉ fᵉ ._ {{cons-telescopeᵉ Aᵉ}} Hᵉ =
  fᵉ (λ xᵉ → section-iterated-Π-section-Π-section-codomainᵉ Pᵉ fᵉ _ {{Aᵉ xᵉ}} (Hᵉ xᵉ))

section-iterated-implicit-Π-section-Π-section-codomainᵉ :
  (Pᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ) →
  ( {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → Pᵉ (Bᵉ xᵉ)) → Pᵉ ({xᵉ : Aᵉ} → Bᵉ xᵉ)) →
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  apply-codomain-iterated-Πᵉ Pᵉ Aᵉ → Pᵉ (iterated-implicit-Πᵉ Aᵉ)
section-iterated-implicit-Π-section-Π-section-codomainᵉ
  Pᵉ fᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} Hᵉ =
  Hᵉ
section-iterated-implicit-Π-section-Π-section-codomainᵉ
  Pᵉ fᵉ ._ {{cons-telescopeᵉ Aᵉ}} Hᵉ =
  fᵉ ( λ xᵉ →
      section-iterated-implicit-Π-section-Π-section-codomainᵉ
        Pᵉ fᵉ _ {{Aᵉ xᵉ}} (Hᵉ xᵉ))
```

### Multivariable function types are equivalent to multivariable implicit function types

```agda
equiv-explicit-implicit-iterated-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  iterated-implicit-Πᵉ Aᵉ ≃ᵉ iterated-Πᵉ Aᵉ
equiv-explicit-implicit-iterated-Πᵉ .zero-ℕᵉ ⦃ base-telescopeᵉ Aᵉ ⦄ = id-equivᵉ
equiv-explicit-implicit-iterated-Πᵉ ._ ⦃ cons-telescopeᵉ Aᵉ ⦄ =
  equiv-Π-equiv-familyᵉ (λ xᵉ → equiv-explicit-implicit-iterated-Πᵉ _ {{Aᵉ xᵉ}}) ∘eᵉ
  equiv-explicit-implicit-Πᵉ

equiv-implicit-explicit-iterated-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  iterated-Πᵉ Aᵉ ≃ᵉ iterated-implicit-Πᵉ Aᵉ
equiv-implicit-explicit-iterated-Πᵉ nᵉ {{Aᵉ}} =
  inv-equivᵉ (equiv-explicit-implicit-iterated-Πᵉ nᵉ {{Aᵉ}})
```

### Iterated products of contractible types is contractible

```agda
is-contr-iterated-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  apply-codomain-iterated-Πᵉ is-contrᵉ Aᵉ → is-contrᵉ (iterated-Πᵉ Aᵉ)
is-contr-iterated-Πᵉ =
  section-iterated-Π-section-Π-section-codomainᵉ is-contrᵉ is-contr-Πᵉ

is-contr-iterated-implicit-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  apply-codomain-iterated-Πᵉ is-contrᵉ Aᵉ → is-contrᵉ (iterated-implicit-Πᵉ Aᵉ)
is-contr-iterated-implicit-Πᵉ =
  section-iterated-implicit-Π-section-Π-section-codomainᵉ
    ( is-contrᵉ)
    ( is-contr-implicit-Πᵉ)
```

### Iterated products of propositions are propositions

```agda
is-prop-iterated-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  apply-codomain-iterated-Πᵉ is-propᵉ Aᵉ → is-propᵉ (iterated-Πᵉ Aᵉ)
is-prop-iterated-Πᵉ =
  section-iterated-Π-section-Π-section-codomainᵉ is-propᵉ is-prop-Πᵉ

is-prop-iterated-implicit-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  apply-codomain-iterated-Πᵉ is-propᵉ Aᵉ → is-propᵉ (iterated-implicit-Πᵉ Aᵉ)
is-prop-iterated-implicit-Πᵉ =
  section-iterated-implicit-Π-section-Π-section-codomainᵉ
    ( is-propᵉ)
    ( is-prop-implicit-Πᵉ)
```

### Iterated products of truncated types are truncated

```agda
is-trunc-iterated-Πᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  apply-codomain-iterated-Πᵉ (is-truncᵉ kᵉ) Aᵉ → is-truncᵉ kᵉ (iterated-Πᵉ Aᵉ)
is-trunc-iterated-Πᵉ kᵉ =
  section-iterated-Π-section-Π-section-codomainᵉ (is-truncᵉ kᵉ) (is-trunc-Πᵉ kᵉ)
```

## See also

-ᵉ [Iteratedᵉ Σ-types](foundation.iterated-dependent-pair-types.mdᵉ)
-ᵉ [Multivariableᵉ homotopies](foundation.multivariable-homotopies.mdᵉ)

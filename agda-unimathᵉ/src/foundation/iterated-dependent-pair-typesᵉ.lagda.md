# Iterated dependent pair types

```agda
module foundation.iterated-dependent-pair-typesᵉ where

open import foundation.telescopesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
```

</details>

## Idea

**Iteratedᵉ dependentᵉ pairᵉ types**ᵉ areᵉ definedᵉ byᵉ iterativelyᵉ applyingᵉ theᵉ
[dependentᵉ pair](foundation.dependent-pair-types.mdᵉ) operatorᵉ `Σ`.ᵉ Moreᵉ
formally,ᵉ `iterated-Σ`ᵉ isᵉ definedᵉ asᵉ anᵉ operationᵉ `telescopeᵉ lᵉ nᵉ → UUᵉ l`ᵉ fromᵉ
theᵉ typeᵉ ofᵉ [telescopes](foundation.telescopes.mdᵉ) to theᵉ universeᵉ ofᵉ typesᵉ ofᵉ
universeᵉ levelᵉ `l`.ᵉ Forᵉ example,ᵉ theᵉ iteratedᵉ dependentᵉ pairᵉ typeᵉ ofᵉ theᵉ
telescopeᵉ

```text
  A₀ᵉ : 𝒰ᵉ l₀ᵉ
  A₁ᵉ : A₀ᵉ → 𝒰ᵉ l₁ᵉ
  A₂ᵉ : (x₀ᵉ : A₀ᵉ) → A₁ᵉ x₀ᵉ → 𝒰ᵉ l₂ᵉ
  A₃ᵉ : (x₀ᵉ : A₀ᵉ) (x₁ᵉ : A₁ᵉ x₀ᵉ) → A₂ᵉ x₀ᵉ x₁ᵉ → 𝒰ᵉ l₃ᵉ
```

isᵉ theᵉ dependentᵉ pairᵉ typeᵉ

```text
  Σᵉ A₀ᵉ (λ x₀ᵉ → Σᵉ (A₁ᵉ x₀ᵉ) (λ x₁ᵉ → Σᵉ (A₂ᵉ x₀ᵉ x₁ᵉ) (A₃ᵉ x₀ᵉ x₁ᵉ)))
```

ofᵉ universeᵉ levelᵉ `l₀ᵉ ⊔ l₁ᵉ ⊔ l₂ᵉ ⊔ l₃`.ᵉ

## Definitions

### Iterated dependent products of iterated type families

```agda
iterated-Σᵉ : {lᵉ : Level} {nᵉ : ℕᵉ} → telescopeᵉ lᵉ nᵉ → UUᵉ lᵉ
iterated-Σᵉ (base-telescopeᵉ Aᵉ) = Aᵉ
iterated-Σᵉ (cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ) = Σᵉ Xᵉ (λ xᵉ → iterated-Σᵉ (Aᵉ xᵉ))
```

### Iterated elements of iterated type families

```agda
data
  iterated-elementᵉ : {lᵉ : Level} {nᵉ : ℕᵉ} → telescopeᵉ lᵉ nᵉ → UUωᵉ
  where
  base-iterated-elementᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Aᵉ → iterated-elementᵉ (base-telescopeᵉ Aᵉ)
  cons-iterated-elementᵉ :
    {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : Xᵉ → telescopeᵉ l2ᵉ nᵉ} →
    (xᵉ : Xᵉ) → iterated-elementᵉ (Yᵉ xᵉ) → iterated-elementᵉ (cons-telescopeᵉ Yᵉ)
```

### Iterated pairing

```agda
iterated-pairᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : telescopeᵉ lᵉ nᵉ} →
  iterated-elementᵉ Aᵉ → iterated-Σᵉ Aᵉ
iterated-pairᵉ (base-iterated-elementᵉ xᵉ) = xᵉ
pr1ᵉ (iterated-pairᵉ (cons-iterated-elementᵉ yᵉ aᵉ)) = yᵉ
pr2ᵉ (iterated-pairᵉ (cons-iterated-elementᵉ yᵉ aᵉ)) = iterated-pairᵉ aᵉ
```

## Properties

### Contractiblity of iterated Σ-types

```agda
is-contr-Σ-telescopeᵉ : {lᵉ : Level} {nᵉ : ℕᵉ} → telescopeᵉ lᵉ nᵉ → UUᵉ lᵉ
is-contr-Σ-telescopeᵉ (base-telescopeᵉ Aᵉ) = is-contrᵉ Aᵉ
is-contr-Σ-telescopeᵉ (cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ) =
  (is-contrᵉ Xᵉ) ×ᵉ (Σᵉ Xᵉ (λ xᵉ → is-contr-Σ-telescopeᵉ (Aᵉ xᵉ)))

is-contr-iterated-Σᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  is-contr-Σ-telescopeᵉ Aᵉ → is-contrᵉ (iterated-Σᵉ Aᵉ)
is-contr-iterated-Σᵉ .0ᵉ {{base-telescopeᵉ Aᵉ}} is-contr-Aᵉ = is-contr-Aᵉ
is-contr-iterated-Σᵉ ._ {{cons-telescopeᵉ Aᵉ}} (is-contr-Xᵉ ,ᵉ xᵉ ,ᵉ Hᵉ) =
  is-contr-Σᵉ is-contr-Xᵉ xᵉ (is-contr-iterated-Σᵉ _ {{Aᵉ xᵉ}} Hᵉ)
```

### Contractiblity of iterated Σ-types without choice of contracting center

```agda
is-contr-Σ-telescope'ᵉ : {lᵉ : Level} {nᵉ : ℕᵉ} → telescopeᵉ lᵉ nᵉ → UUᵉ lᵉ
is-contr-Σ-telescope'ᵉ (base-telescopeᵉ Aᵉ) = is-contrᵉ Aᵉ
is-contr-Σ-telescope'ᵉ (cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ) =
  (is-contrᵉ Xᵉ) ×ᵉ ((xᵉ : Xᵉ) → is-contr-Σ-telescope'ᵉ (Aᵉ xᵉ))

is-contr-iterated-Σ'ᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} →
  is-contr-Σ-telescope'ᵉ Aᵉ → is-contrᵉ (iterated-Σᵉ Aᵉ)
is-contr-iterated-Σ'ᵉ .0ᵉ {{base-telescopeᵉ Aᵉ}} is-contr-Aᵉ = is-contr-Aᵉ
is-contr-iterated-Σ'ᵉ ._ {{cons-telescopeᵉ Aᵉ}} (is-contr-Xᵉ ,ᵉ Hᵉ) =
  is-contr-Σ'ᵉ is-contr-Xᵉ (λ xᵉ → is-contr-iterated-Σ'ᵉ _ {{Aᵉ xᵉ}} (Hᵉ xᵉ))
```

## See also

-ᵉ [Iteratedᵉ Π-types](foundation.iterated-dependent-product-types.mdᵉ)
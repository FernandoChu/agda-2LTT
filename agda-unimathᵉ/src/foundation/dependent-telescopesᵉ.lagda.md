# Dependent telescopes

```agda
module foundation.dependent-telescopesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.telescopesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **dependentᵉ telescope**ᵉ overᵉ aᵉ [telescope](foundation.telescopes.mdᵉ) `A`ᵉ ofᵉ
lengthᵉ `n`ᵉ isᵉ aᵉ dependentᵉ listᵉ ofᵉ dependentᵉ typesᵉ overᵉ eachᵉ ofᵉ theᵉ entriesᵉ in
`A`.ᵉ Forᵉ example,ᵉ aᵉ dependentᵉ telescopeᵉ overᵉ theᵉ telescopeᵉ

```text
  A₀ᵉ : 𝒰ᵉ l₀ᵉ
  A₁ᵉ : A₀ᵉ → 𝒰ᵉ l₁ᵉ
  A₂ᵉ : (x₀ᵉ : A₀ᵉ) → A₁ᵉ x₀ᵉ → 𝒰ᵉ l₂ᵉ
```

consistsᵉ ofᵉ

```text
  B₀ᵉ : A₀ᵉ → 𝒰ᵉ k₀ᵉ
  B₁ᵉ : (x₀ᵉ : A₀ᵉ) (x₁ᵉ : A₁ᵉ x₀ᵉ) → B₀ᵉ x₀ᵉ → UUᵉ k₁ᵉ
  B₂ᵉ : (x₀ᵉ : A₀ᵉ) (x₁ᵉ : A₁ᵉ x₀ᵉ) (x₂ᵉ : A₂ᵉ x₀ᵉ x₁ᵉ) (y₀ᵉ : Bᵉ x₀ᵉ) → B₁ᵉ x₀ᵉ → UUᵉ k₂ᵉ
```

## Definitions

### Dependent telescopes

```agda
data
  dependent-telescopeᵉ :
    {lᵉ : Level} (kᵉ : Level) → {nᵉ : ℕᵉ} → telescopeᵉ lᵉ nᵉ → UUωᵉ
  where
  base-dependent-telescopeᵉ :
    {l1ᵉ k1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → UUᵉ k1ᵉ) →
    dependent-telescopeᵉ k1ᵉ (base-telescopeᵉ Aᵉ)
  cons-dependent-telescopeᵉ :
    {l1ᵉ l2ᵉ k1ᵉ k2ᵉ : Level} {nᵉ : ℕᵉ} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : Xᵉ → telescopeᵉ l2ᵉ nᵉ}
    {Yᵉ : Xᵉ → UUᵉ k1ᵉ} (Bᵉ : (xᵉ : Xᵉ) → Yᵉ xᵉ → dependent-telescopeᵉ k2ᵉ (Aᵉ xᵉ)) →
    dependent-telescopeᵉ (k1ᵉ ⊔ k2ᵉ) (cons-telescopeᵉ Aᵉ)
```

### Expansion of telescopes

Anᵉ **expansion**ᵉ ofᵉ aᵉ telescopeᵉ `A`ᵉ byᵉ aᵉ dependentᵉ telescopeᵉ `B`ᵉ overᵉ itᵉ isᵉ aᵉ
newᵉ telescopeᵉ ofᵉ theᵉ sameᵉ lengthᵉ asᵉ `A`,ᵉ constructedᵉ byᵉ takingᵉ
[dependentᵉ pairs](foundation.dependent-pair-types.mdᵉ) componentwise.ᵉ

```agda
expand-telescopeᵉ :
  {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : telescopeᵉ l1ᵉ nᵉ} →
  dependent-telescopeᵉ l2ᵉ Aᵉ → telescopeᵉ (l1ᵉ ⊔ l2ᵉ) nᵉ
expand-telescopeᵉ (base-dependent-telescopeᵉ Yᵉ) =
  base-telescopeᵉ (Σᵉ _ Yᵉ)
expand-telescopeᵉ (cons-dependent-telescopeᵉ Bᵉ) =
  cons-telescopeᵉ (λ xᵉ → expand-telescopeᵉ (Bᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ)))
```

### Interleaving telescopes

Givenᵉ aᵉ telescopeᵉ `A`ᵉ ofᵉ lengthᵉ `n`ᵉ andᵉ aᵉ dependentᵉ telescopeᵉ `B`ᵉ overᵉ it,ᵉ weᵉ
canᵉ defineᵉ theᵉ **interleavedᵉ telescope**ᵉ whoseᵉ lengthᵉ isᵉ `2n`.ᵉ

```agda
interleave-telescopeᵉ :
  {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : telescopeᵉ l1ᵉ nᵉ} →
  dependent-telescopeᵉ l2ᵉ Aᵉ → telescopeᵉ (l1ᵉ ⊔ l2ᵉ) (succ-ℕᵉ (nᵉ *ℕᵉ 2ᵉ))
interleave-telescopeᵉ (base-dependent-telescopeᵉ Aᵉ) =
  cons-telescopeᵉ (λ xᵉ → base-telescopeᵉ (Aᵉ xᵉ))
interleave-telescopeᵉ (cons-dependent-telescopeᵉ Bᵉ) =
  cons-telescopeᵉ (λ xᵉ → cons-telescopeᵉ λ yᵉ → interleave-telescopeᵉ (Bᵉ xᵉ yᵉ))
```

### Mapping telescopes

Givenᵉ aᵉ telescopeᵉ `A`ᵉ andᵉ aᵉ dependentᵉ telescopeᵉ `B`ᵉ overᵉ it,ᵉ weᵉ canᵉ defineᵉ theᵉ
**mappingᵉ telescope**ᵉ byᵉ takingᵉ dependentᵉ functionᵉ typesᵉ componentwise.ᵉ

```agda
telescope-Πᵉ :
  {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : telescopeᵉ l1ᵉ nᵉ} →
  dependent-telescopeᵉ l2ᵉ Aᵉ → telescopeᵉ (l1ᵉ ⊔ l2ᵉ) nᵉ
telescope-Πᵉ (base-dependent-telescopeᵉ Yᵉ) =
  base-telescopeᵉ ((xᵉ : _) → Yᵉ xᵉ)
telescope-Πᵉ (cons-dependent-telescopeᵉ Bᵉ) =
  cons-telescopeᵉ (λ xᵉ → telescope-Πᵉ (Bᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ)))
```
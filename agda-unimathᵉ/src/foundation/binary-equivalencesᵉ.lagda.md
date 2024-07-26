# Binary equivalences

```agda
module foundation.binary-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
```

</details>

## Idea

Aᵉ binaryᵉ operationᵉ `fᵉ : Aᵉ → Bᵉ → C`ᵉ isᵉ saidᵉ to beᵉ aᵉ binaryᵉ equivalenceᵉ ifᵉ theᵉ
functionsᵉ `λᵉ xᵉ → fᵉ xᵉ b`ᵉ andᵉ `λᵉ yᵉ → fᵉ aᵉ y`ᵉ areᵉ equivalencesᵉ forᵉ eachᵉ `aᵉ : A`ᵉ andᵉ
`bᵉ : B`ᵉ respectively.ᵉ

## Definitions

```agda
fix-leftᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ) →
  Aᵉ → Bᵉ → Cᵉ
fix-leftᵉ fᵉ aᵉ = fᵉ aᵉ

fix-rightᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ) →
  Bᵉ → Aᵉ → Cᵉ
fix-rightᵉ fᵉ bᵉ aᵉ = fᵉ aᵉ bᵉ

is-binary-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (Aᵉ → Bᵉ → Cᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-binary-equivᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} fᵉ =
  ((bᵉ : Bᵉ) → is-equivᵉ (fix-rightᵉ fᵉ bᵉ)) ×ᵉ ((aᵉ : Aᵉ) → is-equivᵉ (fix-leftᵉ fᵉ aᵉ))

is-equiv-fix-leftᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ) →
  is-binary-equivᵉ fᵉ → {aᵉ : Aᵉ} → is-equivᵉ (fix-leftᵉ fᵉ aᵉ)
is-equiv-fix-leftᵉ fᵉ Hᵉ {aᵉ} = pr2ᵉ Hᵉ aᵉ

is-equiv-fix-rightᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ) →
  is-binary-equivᵉ fᵉ → {bᵉ : Bᵉ} → is-equivᵉ (fix-rightᵉ fᵉ bᵉ)
is-equiv-fix-rightᵉ fᵉ Hᵉ {bᵉ} = pr1ᵉ Hᵉ bᵉ
```
# Finite function types

```agda
module univalent-combinatorics.function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Properties

### The type of functions between types equipped with a counting can be equipped with a counting

```agda
count-function-typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  countᵉ Aᵉ → countᵉ Bᵉ → countᵉ (Aᵉ → Bᵉ)
count-function-typeᵉ eᵉ fᵉ =
  count-Πᵉ eᵉ (λ xᵉ → fᵉ)
```

### The type of functions between finite types is finite

```agda
abstract
  is-finite-function-typeᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ → is-finiteᵉ (Aᵉ → Bᵉ)
  is-finite-function-typeᵉ fᵉ gᵉ = is-finite-Πᵉ fᵉ (λ xᵉ → gᵉ)

_→-𝔽ᵉ_ : {l1ᵉ l2ᵉ : Level} → 𝔽ᵉ l1ᵉ → 𝔽ᵉ l2ᵉ → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Aᵉ →-𝔽ᵉ Bᵉ) = type-𝔽ᵉ Aᵉ → type-𝔽ᵉ Bᵉ
pr2ᵉ (Aᵉ →-𝔽ᵉ Bᵉ) =
  is-finite-function-typeᵉ (is-finite-type-𝔽ᵉ Aᵉ) (is-finite-type-𝔽ᵉ Bᵉ)
```

### The type of equivalences between finite types is finite

```agda
abstract
  is-finite-≃ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ → is-finiteᵉ (Aᵉ ≃ᵉ Bᵉ)
  is-finite-≃ᵉ fᵉ gᵉ =
    is-finite-Σᵉ
      ( is-finite-function-typeᵉ fᵉ gᵉ)
      ( λ hᵉ →
        is-finite-productᵉ
          ( is-finite-Σᵉ
            ( is-finite-function-typeᵉ gᵉ fᵉ)
            ( λ kᵉ →
              is-finite-Πᵉ gᵉ
                ( λ yᵉ → is-finite-eqᵉ (has-decidable-equality-is-finiteᵉ gᵉ))))
          ( is-finite-Σᵉ
            ( is-finite-function-typeᵉ gᵉ fᵉ)
            ( λ kᵉ →
              is-finite-Πᵉ fᵉ
                ( λ xᵉ → is-finite-eqᵉ (has-decidable-equality-is-finiteᵉ fᵉ)))))

infix 6 _≃-𝔽ᵉ_
_≃-𝔽ᵉ_ : {l1ᵉ l2ᵉ : Level} → 𝔽ᵉ l1ᵉ → 𝔽ᵉ l2ᵉ → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Aᵉ ≃-𝔽ᵉ Bᵉ) = type-𝔽ᵉ Aᵉ ≃ᵉ type-𝔽ᵉ Bᵉ
pr2ᵉ (Aᵉ ≃-𝔽ᵉ Bᵉ) = is-finite-≃ᵉ (is-finite-type-𝔽ᵉ Aᵉ) (is-finite-type-𝔽ᵉ Bᵉ)
```

### The type of automorphisms on a finite type is finite

```agda
Aut-𝔽ᵉ : {lᵉ : Level} → 𝔽ᵉ lᵉ → 𝔽ᵉ lᵉ
Aut-𝔽ᵉ Aᵉ = Aᵉ ≃-𝔽ᵉ Aᵉ
```
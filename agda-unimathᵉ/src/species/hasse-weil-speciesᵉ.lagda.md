# Hasse-Weil species

```agda
module species.hasse-weil-speciesᵉ where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.commutative-finite-ringsᵉ
open import finite-algebra.products-commutative-finite-ringsᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Letᵉ `S`ᵉ beᵉ aᵉ functionᵉ fromᵉ theᵉ typeᵉ ofᵉ commutativeᵉ finiteᵉ ringsᵉ to theᵉ finiteᵉ
typesᵉ thatᵉ preservesᵉ cartesianᵉ products.ᵉ Theᵉ **Hasse-Weilᵉ species**ᵉ isᵉ aᵉ speciesᵉ
ofᵉ finiteᵉ inhabitedᵉ typesᵉ definedᵉ forᵉ anyᵉ finiteᵉ inhabitedᵉ typeᵉ `k`ᵉ asᵉ

```text
Σᵉ (pᵉ : structure-semisimple-commutative-ring-𝔽ᵉ kᵉ) ; Sᵉ (commutative-finite-ring-finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-𝔽ᵉ kᵉ pᵉ)
```

## Definitions

```agda
is-closed-under-products-function-from-Commutative-Ring-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} → (Commutative-Ring-𝔽ᵉ l1ᵉ → 𝔽ᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-closed-under-products-function-from-Commutative-Ring-𝔽ᵉ {l1ᵉ} {l2ᵉ} Sᵉ =
  (R1ᵉ R2ᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ) →
  ( type-𝔽ᵉ (Sᵉ (product-Commutative-Ring-𝔽ᵉ R1ᵉ R2ᵉ))) ≃ᵉ
  ( type-𝔽ᵉ (Sᵉ R1ᵉ) ×ᵉ type-𝔽ᵉ (Sᵉ R2ᵉ))
```

```text
module _
  {l1ᵉ l2ᵉ : Level}
  (l3ᵉ l4ᵉ : Level)
  (Sᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ → 𝔽ᵉ l2ᵉ)
  (Cᵉ : is-closed-under-products-function-from-Commutative-Ring-𝔽ᵉ Sᵉ)
  where

  hasse-weil-species-Inhabited-𝔽ᵉ :
    species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
  hasse-weil-species-Inhabited-𝔽ᵉ ( kᵉ ,ᵉ (fᵉ ,ᵉ iᵉ)) =
    Σ-𝔽ᵉ {!!ᵉ}
        ( λ pᵉ →
          Sᵉ
            ( commutative-finite-ring-Semisimple-Commutative-Ring-𝔽ᵉ
              ( finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-𝔽ᵉ
                ( l3ᵉ)
                ( l4ᵉ)
                ( kᵉ ,ᵉ fᵉ)
                ( pᵉ))))
```
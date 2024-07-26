# Cauchy series of species of types

```agda
module species.cauchy-series-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

## Idea

Inᵉ classicalᵉ mathematics,ᵉ theᵉ Cauchyᵉ seriesᵉ ofᵉ aᵉ speciesᵉ (ofᵉ finiteᵉ typesᵉ) `S`ᵉ
isᵉ theᵉ formalᵉ seriesᵉ in `x`ᵉ :

```text
Σᵉ (nᵉ : ℕᵉ) (|S({1,...,n}|ᵉ x^nᵉ /ᵉ n!ᵉ))
```

Theᵉ categorifiedᵉ versionᵉ ofᵉ thisᵉ seriesᵉ isᵉ :

```text
  Σᵉ (Fᵉ : 𝔽),ᵉ S(Fᵉ) ×ᵉ (Fᵉ → Xᵉ)
```

Remarksᵉ thatᵉ weᵉ canᵉ generalizedᵉ thisᵉ to speciesᵉ ofᵉ typesᵉ with theᵉ followingᵉ
definitionᵉ :

```text
  Σᵉ (Uᵉ : UU),ᵉ S(Uᵉ) ×ᵉ (Uᵉ → Xᵉ)
```

## Definition

```agda
cauchy-series-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → UUᵉ l3ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
cauchy-series-species-typesᵉ {l1ᵉ} Sᵉ Xᵉ = Σᵉ (UUᵉ l1ᵉ) (λ Uᵉ → Sᵉ Uᵉ ×ᵉ (Uᵉ → Xᵉ))
```

## Properties

### Equivalent species of types have equivalent Cauchy series

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  (fᵉ : (Fᵉ : UUᵉ l1ᵉ) → (Sᵉ Fᵉ ≃ᵉ Tᵉ Fᵉ))
  (Xᵉ : UUᵉ l4ᵉ)
  where

  equiv-cauchy-series-equiv-species-typesᵉ :
    cauchy-series-species-typesᵉ Sᵉ Xᵉ ≃ᵉ cauchy-series-species-typesᵉ Tᵉ Xᵉ
  equiv-cauchy-series-equiv-species-typesᵉ =
    equiv-totᵉ λ Xᵉ → equiv-productᵉ (fᵉ Xᵉ) id-equivᵉ
```

### Cauchy series of types are equivalence invariant

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Xᵉ : UUᵉ l3ᵉ)
  (Yᵉ : UUᵉ l4ᵉ)
  (eᵉ : Xᵉ ≃ᵉ Yᵉ)
  where

  equiv-cauchy-series-species-typesᵉ :
    cauchy-series-species-typesᵉ Sᵉ Xᵉ ≃ᵉ cauchy-series-species-typesᵉ Sᵉ Yᵉ
  equiv-cauchy-series-species-typesᵉ =
    equiv-totᵉ (λ Fᵉ → equiv-productᵉ id-equivᵉ (equiv-postcompᵉ Fᵉ eᵉ))
```
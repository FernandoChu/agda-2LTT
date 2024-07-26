# Implicit function types

```agda
module foundation.implicit-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Properties

### Dependent function types taking implicit arguments are equivalent to dependent function types taking explicit arguments

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  implicit-explicit-Πᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → {xᵉ : Aᵉ} → Bᵉ xᵉ
  implicit-explicit-Πᵉ fᵉ {xᵉ} = fᵉ xᵉ

  explicit-implicit-Πᵉ : ({xᵉ : Aᵉ} → Bᵉ xᵉ) → (xᵉ : Aᵉ) → Bᵉ xᵉ
  explicit-implicit-Πᵉ fᵉ xᵉ = fᵉ {xᵉ}

  is-equiv-implicit-explicit-Πᵉ : is-equivᵉ implicit-explicit-Πᵉ
  pr1ᵉ (pr1ᵉ is-equiv-implicit-explicit-Πᵉ) = explicit-implicit-Πᵉ
  pr2ᵉ (pr1ᵉ is-equiv-implicit-explicit-Πᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ is-equiv-implicit-explicit-Πᵉ) = explicit-implicit-Πᵉ
  pr2ᵉ (pr2ᵉ is-equiv-implicit-explicit-Πᵉ) = refl-htpyᵉ

  is-equiv-explicit-implicit-Πᵉ : is-equivᵉ explicit-implicit-Πᵉ
  pr1ᵉ (pr1ᵉ is-equiv-explicit-implicit-Πᵉ) = implicit-explicit-Πᵉ
  pr2ᵉ (pr1ᵉ is-equiv-explicit-implicit-Πᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ is-equiv-explicit-implicit-Πᵉ) = implicit-explicit-Πᵉ
  pr2ᵉ (pr2ᵉ is-equiv-explicit-implicit-Πᵉ) = refl-htpyᵉ

  equiv-implicit-explicit-Πᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) ≃ᵉ ({xᵉ : Aᵉ} → Bᵉ xᵉ)
  pr1ᵉ equiv-implicit-explicit-Πᵉ = implicit-explicit-Πᵉ
  pr2ᵉ equiv-implicit-explicit-Πᵉ = is-equiv-implicit-explicit-Πᵉ

  equiv-explicit-implicit-Πᵉ : ({xᵉ : Aᵉ} → Bᵉ xᵉ) ≃ᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  pr1ᵉ equiv-explicit-implicit-Πᵉ = explicit-implicit-Πᵉ
  pr2ᵉ equiv-explicit-implicit-Πᵉ = is-equiv-explicit-implicit-Πᵉ
```

### Equality of explicit functions is equality of implicit functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  equiv-eq-implicit-eq-explicit-Πᵉ : (fᵉ ＝ᵉ gᵉ) ≃ᵉ (Idᵉ (λ {xᵉ} → fᵉ xᵉ) (λ {xᵉ} → gᵉ xᵉ))
  equiv-eq-implicit-eq-explicit-Πᵉ = equiv-apᵉ equiv-implicit-explicit-Πᵉ fᵉ gᵉ

  eq-implicit-eq-explicit-Πᵉ : (fᵉ ＝ᵉ gᵉ) → (Idᵉ (λ {xᵉ} → fᵉ xᵉ) (λ {xᵉ} → gᵉ xᵉ))
  eq-implicit-eq-explicit-Πᵉ = map-equivᵉ equiv-eq-implicit-eq-explicit-Πᵉ

  equiv-eq-explicit-eq-implicit-Πᵉ : (Idᵉ (λ {xᵉ} → fᵉ xᵉ) (λ {xᵉ} → gᵉ xᵉ)) ≃ᵉ (fᵉ ＝ᵉ gᵉ)
  equiv-eq-explicit-eq-implicit-Πᵉ =
    equiv-apᵉ equiv-explicit-implicit-Πᵉ (λ {xᵉ} → fᵉ xᵉ) (λ {xᵉ} → gᵉ xᵉ)

  eq-explicit-eq-implicit-Πᵉ : (Idᵉ (λ {xᵉ} → fᵉ xᵉ) (λ {xᵉ} → gᵉ xᵉ)) → (fᵉ ＝ᵉ gᵉ)
  eq-explicit-eq-implicit-Πᵉ = map-equivᵉ equiv-eq-explicit-eq-implicit-Πᵉ
```

## See also

-ᵉ Functionᵉ extensionalityᵉ forᵉ implicitᵉ functionᵉ typesᵉ isᵉ establishedᵉ in
  [`foundation.function-extensionality`](foundation.function-extensionality.md).ᵉ
# Homotopies of binary operations

```agda
module foundation.binary-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ binaryᵉ operationsᵉ `fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ y`.ᵉ Theᵉ typeᵉ ofᵉ
**binaryᵉ homotopies**ᵉ betweenᵉ `f`ᵉ andᵉ `g`ᵉ isᵉ definedᵉ to beᵉ theᵉ typeᵉ ofᵉ pointwiseᵉ
[identifications](foundation-core.identity-types.mdᵉ) ofᵉ `f`ᵉ andᵉ `g`.ᵉ Weᵉ showᵉ
thatᵉ thisᵉ characterizesᵉ theᵉ identityᵉ typeᵉ ofᵉ `(xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  where

  binary-htpyᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  binary-htpyᵉ fᵉ gᵉ = (xᵉ : Aᵉ) → fᵉ xᵉ ~ᵉ gᵉ xᵉ

  refl-binary-htpyᵉ : (fᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → binary-htpyᵉ fᵉ fᵉ
  refl-binary-htpyᵉ fᵉ xᵉ = refl-htpyᵉ

  binary-htpy-eqᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → (fᵉ ＝ᵉ gᵉ) → binary-htpyᵉ fᵉ gᵉ
  binary-htpy-eqᵉ fᵉ .fᵉ reflᵉ = refl-binary-htpyᵉ fᵉ

  is-torsorial-binary-htpyᵉ :
    (fᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) →
    is-torsorialᵉ (binary-htpyᵉ fᵉ)
  is-torsorial-binary-htpyᵉ fᵉ =
    is-torsorial-Eq-Πᵉ (λ xᵉ → is-torsorial-htpyᵉ (fᵉ xᵉ))

  is-equiv-binary-htpy-eqᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → is-equivᵉ (binary-htpy-eqᵉ fᵉ gᵉ)
  is-equiv-binary-htpy-eqᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-binary-htpyᵉ fᵉ)
      ( binary-htpy-eqᵉ fᵉ)

  extensionality-binary-Πᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ binary-htpyᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-binary-Πᵉ fᵉ gᵉ) = binary-htpy-eqᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-binary-Πᵉ fᵉ gᵉ) = is-equiv-binary-htpy-eqᵉ fᵉ gᵉ

  eq-binary-htpyᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → binary-htpyᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-binary-htpyᵉ fᵉ gᵉ = map-inv-equivᵉ (extensionality-binary-Πᵉ fᵉ gᵉ)
```

## Properties

### Binary homotopy is equivalent to function homotopy

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  where

  binary-htpy-htpyᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → (fᵉ ~ᵉ gᵉ) → binary-htpyᵉ fᵉ gᵉ
  binary-htpy-htpyᵉ fᵉ gᵉ =
    ind-htpyᵉ fᵉ (λ gᵉ Hᵉ → binary-htpyᵉ fᵉ gᵉ) (refl-binary-htpyᵉ fᵉ)

  equiv-binary-htpy-htpyᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → (fᵉ ~ᵉ gᵉ) ≃ᵉ binary-htpyᵉ fᵉ gᵉ
  equiv-binary-htpy-htpyᵉ fᵉ gᵉ = extensionality-binary-Πᵉ fᵉ gᵉ ∘eᵉ equiv-eq-htpyᵉ

  htpy-binary-htpyᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → binary-htpyᵉ fᵉ gᵉ → fᵉ ~ᵉ gᵉ
  htpy-binary-htpyᵉ fᵉ gᵉ = map-inv-equivᵉ (equiv-binary-htpy-htpyᵉ fᵉ gᵉ)

  equiv-htpy-binary-htpyᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) → binary-htpyᵉ fᵉ gᵉ ≃ᵉ (fᵉ ~ᵉ gᵉ)
  equiv-htpy-binary-htpyᵉ fᵉ gᵉ = inv-equivᵉ (equiv-binary-htpy-htpyᵉ fᵉ gᵉ)
```
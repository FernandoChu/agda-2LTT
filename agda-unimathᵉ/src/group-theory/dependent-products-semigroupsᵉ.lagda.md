# Dependent products of semigroups

```agda
module group-theory.dependent-products-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ semigroupsᵉ `Gᵢ`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ
`Π(iᵉ : I),ᵉ Gᵢ`ᵉ isᵉ theᵉ semigroupᵉ consistingᵉ ofᵉ dependentᵉ functionsᵉ assigningᵉ to
eachᵉ `iᵉ : I`ᵉ anᵉ elementᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `Gᵢ`.ᵉ Theᵉ semigroupᵉ operationᵉ
isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Gᵉ : Iᵉ → Semigroupᵉ l2ᵉ)
  where

  set-Π-Semigroupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Semigroupᵉ = Π-Set'ᵉ Iᵉ (λ iᵉ → set-Semigroupᵉ (Gᵉ iᵉ))

  type-Π-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Semigroupᵉ = type-Setᵉ set-Π-Semigroupᵉ

  mul-Π-Semigroupᵉ :
    (fᵉ gᵉ : type-Π-Semigroupᵉ) → type-Π-Semigroupᵉ
  mul-Π-Semigroupᵉ fᵉ gᵉ iᵉ = mul-Semigroupᵉ (Gᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ)

  associative-mul-Π-Semigroupᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Semigroupᵉ) →
    mul-Π-Semigroupᵉ (mul-Π-Semigroupᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-Π-Semigroupᵉ fᵉ (mul-Π-Semigroupᵉ gᵉ hᵉ)
  associative-mul-Π-Semigroupᵉ fᵉ gᵉ hᵉ =
    eq-htpyᵉ (λ iᵉ → associative-mul-Semigroupᵉ (Gᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (hᵉ iᵉ))

  has-associative-mul-Π-Semigroupᵉ :
    has-associative-mul-Setᵉ set-Π-Semigroupᵉ
  pr1ᵉ has-associative-mul-Π-Semigroupᵉ =
    mul-Π-Semigroupᵉ
  pr2ᵉ has-associative-mul-Π-Semigroupᵉ =
    associative-mul-Π-Semigroupᵉ

  Π-Semigroupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Semigroupᵉ = set-Π-Semigroupᵉ
  pr2ᵉ Π-Semigroupᵉ = has-associative-mul-Π-Semigroupᵉ
```
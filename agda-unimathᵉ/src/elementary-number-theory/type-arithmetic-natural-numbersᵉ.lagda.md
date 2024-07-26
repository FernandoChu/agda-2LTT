# Type arithmetic with natural numbers

```agda
module elementary-number-theory.type-arithmetic-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.parity-natural-numbersᵉ
open import elementary-number-theory.powers-of-twoᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.iterating-functionsᵉ
open import foundation.split-surjective-mapsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.negationᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ proveᵉ arithmeticalᵉ lawsᵉ involvingᵉ theᵉ naturalᵉ numbersᵉ

## Laws

### The natural numbers is a fixpoint to the functor `X ↦ 1 + X`

```agda
map-equiv-ℕᵉ : ℕᵉ → unitᵉ +ᵉ ℕᵉ
map-equiv-ℕᵉ zero-ℕᵉ = inlᵉ starᵉ
map-equiv-ℕᵉ (succ-ℕᵉ nᵉ) = inrᵉ nᵉ

map-inv-equiv-ℕᵉ : unitᵉ +ᵉ ℕᵉ → ℕᵉ
map-inv-equiv-ℕᵉ (inlᵉ xᵉ) = zero-ℕᵉ
map-inv-equiv-ℕᵉ (inrᵉ nᵉ) = succ-ℕᵉ nᵉ

is-retraction-map-inv-equiv-ℕᵉ :
  ( map-inv-equiv-ℕᵉ ∘ᵉ map-equiv-ℕᵉ) ~ᵉ idᵉ
is-retraction-map-inv-equiv-ℕᵉ zero-ℕᵉ = reflᵉ
is-retraction-map-inv-equiv-ℕᵉ (succ-ℕᵉ nᵉ) = reflᵉ

is-section-map-inv-equiv-ℕᵉ :
  ( map-equiv-ℕᵉ ∘ᵉ map-inv-equiv-ℕᵉ) ~ᵉ idᵉ
is-section-map-inv-equiv-ℕᵉ (inlᵉ starᵉ) = reflᵉ
is-section-map-inv-equiv-ℕᵉ (inrᵉ nᵉ) = reflᵉ

equiv-ℕᵉ : ℕᵉ ≃ᵉ (unitᵉ +ᵉ ℕᵉ)
pr1ᵉ equiv-ℕᵉ = map-equiv-ℕᵉ
pr2ᵉ equiv-ℕᵉ =
  is-equiv-is-invertibleᵉ
    map-inv-equiv-ℕᵉ
    is-section-map-inv-equiv-ℕᵉ
    is-retraction-map-inv-equiv-ℕᵉ
```

### The coproduct `ℕ + ℕ` is equivalent to `ℕ`

```agda
succ-ℕ+ℕᵉ : ℕᵉ +ᵉ ℕᵉ → ℕᵉ +ᵉ ℕᵉ
succ-ℕ+ℕᵉ = map-coproductᵉ succ-ℕᵉ succ-ℕᵉ

map-ℕ+ℕ-to-ℕᵉ : ℕᵉ +ᵉ ℕᵉ → ℕᵉ
map-ℕ+ℕ-to-ℕᵉ (inlᵉ xᵉ) = 2 *ℕᵉ xᵉ
map-ℕ+ℕ-to-ℕᵉ (inrᵉ xᵉ) = succ-ℕᵉ (2ᵉ *ℕᵉ xᵉ)

action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕᵉ :
  (xᵉ : ℕᵉ +ᵉ ℕᵉ) →
    (map-ℕ+ℕ-to-ℕᵉ (succ-ℕ+ℕᵉ xᵉ)) ＝ᵉ
      (succ-ℕᵉ (succ-ℕᵉ (map-ℕ+ℕ-to-ℕᵉ xᵉ)))
action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕᵉ (inlᵉ xᵉ) =
  apᵉ succ-ℕᵉ (left-successor-law-add-ℕᵉ _ _)
action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕᵉ (inrᵉ xᵉ) =
  apᵉ (succ-ℕᵉ ∘ᵉ succ-ℕᵉ) (left-successor-law-add-ℕᵉ _ _)

is-split-surjective-map-ℕ+ℕ-to-ℕᵉ : is-split-surjectiveᵉ map-ℕ+ℕ-to-ℕᵉ
is-split-surjective-map-ℕ+ℕ-to-ℕᵉ zero-ℕᵉ =
  ( pairᵉ (inlᵉ 0ᵉ) reflᵉ)
is-split-surjective-map-ℕ+ℕ-to-ℕᵉ (succ-ℕᵉ zero-ℕᵉ) =
  ( pairᵉ (inrᵉ 0ᵉ) reflᵉ)
is-split-surjective-map-ℕ+ℕ-to-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ bᵉ)) =
  ( pairᵉ
    ( succ-ℕ+ℕᵉ (pr1ᵉ (is-split-surjective-map-ℕ+ℕ-to-ℕᵉ bᵉ)))
    ( ( action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕᵉ
        ( pr1ᵉ (is-split-surjective-map-ℕ+ℕ-to-ℕᵉ bᵉ))) ∙ᵉ
      ( apᵉ (succ-ℕᵉ ∘ᵉ succ-ℕᵉ)
        ( pr2ᵉ (is-split-surjective-map-ℕ+ℕ-to-ℕᵉ bᵉ)))))

is-injective-map-ℕ+ℕ-to-ℕᵉ : is-injectiveᵉ map-ℕ+ℕ-to-ℕᵉ
is-injective-map-ℕ+ℕ-to-ℕᵉ {inlᵉ xᵉ} {inlᵉ yᵉ} pᵉ =
  ( apᵉ inlᵉ (is-injective-left-mul-succ-ℕᵉ 1 pᵉ))
is-injective-map-ℕ+ℕ-to-ℕᵉ {inlᵉ xᵉ} {inrᵉ yᵉ} pᵉ =
  ex-falsoᵉ (tᵉ sᵉ)
  where
  sᵉ : (div-ℕᵉ 2 (succ-ℕᵉ (2ᵉ *ℕᵉ yᵉ)))
  sᵉ = concatenate-div-eq-ℕᵉ (xᵉ ,ᵉ commutative-mul-ℕᵉ xᵉ 2ᵉ) pᵉ

  tᵉ : ¬ᵉ (div-ℕᵉ 2 (succ-ℕᵉ (2ᵉ *ℕᵉ yᵉ)))
  tᵉ =
    ( is-odd-succ-is-even-ℕᵉ
      ( 2 *ℕᵉ yᵉ)
      ( yᵉ ,ᵉ commutative-mul-ℕᵉ yᵉ 2ᵉ))
is-injective-map-ℕ+ℕ-to-ℕᵉ {inrᵉ xᵉ} {inlᵉ yᵉ} pᵉ =
  ex-falsoᵉ (tᵉ sᵉ)
  where
  sᵉ : (div-ℕᵉ 2 (succ-ℕᵉ (2ᵉ *ℕᵉ xᵉ)))
  sᵉ = concatenate-div-eq-ℕᵉ (yᵉ ,ᵉ commutative-mul-ℕᵉ yᵉ 2ᵉ) (invᵉ pᵉ)

  tᵉ : ¬ᵉ (div-ℕᵉ 2 (succ-ℕᵉ (2ᵉ *ℕᵉ xᵉ)))
  tᵉ =
    ( is-odd-succ-is-even-ℕᵉ
      ( 2 *ℕᵉ xᵉ)
      ( xᵉ ,ᵉ commutative-mul-ℕᵉ xᵉ 2ᵉ))
is-injective-map-ℕ+ℕ-to-ℕᵉ {inrᵉ xᵉ} {inrᵉ yᵉ} pᵉ =
  ( apᵉ inrᵉ (is-injective-left-mul-succ-ℕᵉ 1 (is-injective-succ-ℕᵉ pᵉ)))

is-equiv-map-ℕ+ℕ-to-ℕᵉ : is-equivᵉ map-ℕ+ℕ-to-ℕᵉ
is-equiv-map-ℕ+ℕ-to-ℕᵉ =
  is-equiv-is-split-surjective-is-injectiveᵉ
    ( map-ℕ+ℕ-to-ℕᵉ)
    ( is-injective-map-ℕ+ℕ-to-ℕᵉ)
    ( is-split-surjective-map-ℕ+ℕ-to-ℕᵉ)

ℕ+ℕ≃ℕᵉ : (ℕᵉ +ᵉ ℕᵉ) ≃ᵉ ℕᵉ
ℕ+ℕ≃ℕᵉ = pairᵉ map-ℕ+ℕ-to-ℕᵉ is-equiv-map-ℕ+ℕ-to-ℕᵉ

map-ℕ-to-ℕ+ℕᵉ : ℕᵉ → ℕᵉ +ᵉ ℕᵉ
map-ℕ-to-ℕ+ℕᵉ = map-inv-is-equivᵉ (pr2ᵉ ℕ+ℕ≃ℕᵉ)

is-equiv-map-ℕ-to-ℕ+ℕᵉ : is-equivᵉ map-ℕ-to-ℕ+ℕᵉ
is-equiv-map-ℕ-to-ℕ+ℕᵉ = is-equiv-map-inv-is-equivᵉ (pr2ᵉ ℕ+ℕ≃ℕᵉ)
```

### The iterated coproduct `ℕ + ℕ + ... + ℕ` is equivalent to `ℕ` for any n

```agda
equiv-iterated-coproduct-ℕᵉ :
  (nᵉ : ℕᵉ) → (iterateᵉ nᵉ (_+ᵉ_ ℕᵉ) ℕᵉ) ≃ᵉ ℕᵉ
equiv-iterated-coproduct-ℕᵉ zero-ℕᵉ = id-equivᵉ
equiv-iterated-coproduct-ℕᵉ (succ-ℕᵉ nᵉ) =
  ( ℕ+ℕ≃ℕᵉ) ∘eᵉ
    ( equiv-coproductᵉ id-equivᵉ (equiv-iterated-coproduct-ℕᵉ nᵉ))
```

### The product `ℕ × ℕ` is equivalent to `ℕ`

```agda
ℕ×ℕ≃ℕᵉ : (ℕᵉ ×ᵉ ℕᵉ) ≃ᵉ ℕᵉ
ℕ×ℕ≃ℕᵉ = pairᵉ pairing-mapᵉ is-equiv-pairing-mapᵉ

map-ℕ-to-ℕ×ℕᵉ : ℕᵉ → ℕᵉ ×ᵉ ℕᵉ
map-ℕ-to-ℕ×ℕᵉ = map-inv-is-equivᵉ (pr2ᵉ ℕ×ℕ≃ℕᵉ)

is-equiv-map-ℕ-to-ℕ×ℕᵉ : is-equivᵉ map-ℕ-to-ℕ×ℕᵉ
is-equiv-map-ℕ-to-ℕ×ℕᵉ = is-equiv-map-inv-is-equivᵉ (pr2ᵉ ℕ×ℕ≃ℕᵉ)
```

### The iterated coproduct `ℕ × ℕ × ... × ℕ` is equivalent to `ℕ` for any n

```agda
equiv-iterated-product-ℕᵉ :
  (nᵉ : ℕᵉ) → (iterateᵉ nᵉ (_×ᵉ_ ℕᵉ) ℕᵉ) ≃ᵉ ℕᵉ
equiv-iterated-product-ℕᵉ zero-ℕᵉ = id-equivᵉ
equiv-iterated-product-ℕᵉ (succ-ℕᵉ nᵉ) =
  ( ℕ×ℕ≃ℕᵉ) ∘eᵉ
    ( equiv-productᵉ id-equivᵉ (equiv-iterated-product-ℕᵉ nᵉ))
```

### The coproduct `(Fin n) + ℕ` is equivalent to `N` for any standard finite `Fin n`

```agda
equiv-coproduct-Fin-ℕᵉ : (nᵉ : ℕᵉ) → ((Finᵉ nᵉ) +ᵉ ℕᵉ) ≃ᵉ ℕᵉ
equiv-coproduct-Fin-ℕᵉ zero-ℕᵉ = left-unit-law-coproductᵉ ℕᵉ
equiv-coproduct-Fin-ℕᵉ (succ-ℕᵉ nᵉ) =
  ( equiv-coproduct-Fin-ℕᵉ nᵉ) ∘eᵉ
    ( equiv-coproductᵉ id-equivᵉ (inv-equivᵉ equiv-ℕᵉ) ∘eᵉ
      ( associative-coproductᵉ))
```

### The product `(Fin n) × ℕ` is equivalent to `N` for any standard finite `Fin n` where n is nonzero

```agda
equiv-product-Fin-ℕᵉ : (nᵉ : ℕᵉ) → ((Finᵉ (succ-ℕᵉ nᵉ)) ×ᵉ ℕᵉ) ≃ᵉ ℕᵉ
equiv-product-Fin-ℕᵉ zero-ℕᵉ =
  ( left-unit-law-coproductᵉ ℕᵉ) ∘eᵉ
    ( ( equiv-coproductᵉ (left-absorption-productᵉ ℕᵉ) left-unit-law-productᵉ) ∘eᵉ
      ( right-distributive-product-coproductᵉ emptyᵉ unitᵉ ℕᵉ))
equiv-product-Fin-ℕᵉ (succ-ℕᵉ nᵉ) =
  ( ℕ+ℕ≃ℕᵉ) ∘eᵉ
    ( ( equiv-coproductᵉ (equiv-product-Fin-ℕᵉ nᵉ) left-unit-law-productᵉ) ∘eᵉ
      ( right-distributive-product-coproductᵉ (Finᵉ (succ-ℕᵉ nᵉ)) unitᵉ ℕᵉ))
```

### The integers `ℤ` is equivalent to `ℕ`

```agda
ℤ≃ℕᵉ : ℤᵉ ≃ᵉ ℕᵉ
ℤ≃ℕᵉ = (ℕ+ℕ≃ℕᵉ) ∘eᵉ (equiv-coproductᵉ id-equivᵉ (inv-equivᵉ equiv-ℕᵉ))

map-ℕ-to-ℤᵉ : ℕᵉ → ℤᵉ
map-ℕ-to-ℤᵉ = map-inv-is-equivᵉ (pr2ᵉ ℤ≃ℕᵉ)

is-equiv-map-ℕ-to-ℤᵉ : is-equivᵉ map-ℕ-to-ℤᵉ
is-equiv-map-ℕ-to-ℤᵉ = is-equiv-map-inv-is-equivᵉ (pr2ᵉ ℤ≃ℕᵉ)
```
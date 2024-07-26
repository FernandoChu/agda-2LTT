# Coproducts of finite types

```agda
module univalent-combinatorics.coproduct-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-decidable-subtypesᵉ
open import univalent-combinatorics.double-countingᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Coproductsᵉ ofᵉ finiteᵉ typesᵉ areᵉ finite,ᵉ givingᵉ aᵉ coproductᵉ operationᵉ onᵉ theᵉ typeᵉ
𝔽ᵉ ofᵉ finiteᵉ types.ᵉ

## Properties

### The standard finite types are closed under coproducts

```agda
coproduct-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) → (Finᵉ kᵉ +ᵉ Finᵉ lᵉ) ≃ᵉ Finᵉ (kᵉ +ℕᵉ lᵉ)
coproduct-Finᵉ kᵉ zero-ℕᵉ = right-unit-law-coproductᵉ (Finᵉ kᵉ)
coproduct-Finᵉ kᵉ (succ-ℕᵉ lᵉ) =
  (equiv-coproductᵉ (coproduct-Finᵉ kᵉ lᵉ) id-equivᵉ) ∘eᵉ inv-associative-coproductᵉ

map-coproduct-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) → (Finᵉ kᵉ +ᵉ Finᵉ lᵉ) → Finᵉ (kᵉ +ℕᵉ lᵉ)
map-coproduct-Finᵉ kᵉ lᵉ = map-equivᵉ (coproduct-Finᵉ kᵉ lᵉ)

Fin-add-ℕᵉ :
  (kᵉ lᵉ : ℕᵉ) → Finᵉ (kᵉ +ℕᵉ lᵉ) ≃ᵉ (Finᵉ kᵉ +ᵉ Finᵉ lᵉ)
Fin-add-ℕᵉ kᵉ lᵉ = inv-equivᵉ (coproduct-Finᵉ kᵉ lᵉ)

inl-coproduct-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ (kᵉ +ℕᵉ lᵉ)
inl-coproduct-Finᵉ kᵉ lᵉ = map-coproduct-Finᵉ kᵉ lᵉ ∘ᵉ inlᵉ

inr-coproduct-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) → Finᵉ lᵉ → Finᵉ (kᵉ +ℕᵉ lᵉ)
inr-coproduct-Finᵉ kᵉ lᵉ = map-coproduct-Finᵉ kᵉ lᵉ ∘ᵉ inrᵉ

compute-inl-coproduct-Finᵉ :
  (kᵉ : ℕᵉ) → inl-coproduct-Finᵉ kᵉ 0 ~ᵉ idᵉ
compute-inl-coproduct-Finᵉ kᵉ xᵉ = reflᵉ
```

### Inclusion of `coproduct-Fin` into the natural numbers

```agda
nat-coproduct-Finᵉ :
  (nᵉ mᵉ : ℕᵉ) → (xᵉ : Finᵉ nᵉ +ᵉ Finᵉ mᵉ) →
  nat-Finᵉ (nᵉ +ℕᵉ mᵉ) (map-coproduct-Finᵉ nᵉ mᵉ xᵉ) ＝ᵉ
  ind-coproductᵉ _ (nat-Finᵉ nᵉ) (λ iᵉ → nᵉ +ℕᵉ (nat-Finᵉ mᵉ iᵉ)) xᵉ
nat-coproduct-Finᵉ nᵉ zero-ℕᵉ (inlᵉ xᵉ) = reflᵉ
nat-coproduct-Finᵉ nᵉ (succ-ℕᵉ mᵉ) (inlᵉ xᵉ) = nat-coproduct-Finᵉ nᵉ mᵉ (inlᵉ xᵉ)
nat-coproduct-Finᵉ nᵉ (succ-ℕᵉ mᵉ) (inrᵉ (inlᵉ xᵉ)) = nat-coproduct-Finᵉ nᵉ mᵉ (inrᵉ xᵉ)
nat-coproduct-Finᵉ nᵉ (succ-ℕᵉ mᵉ) (inrᵉ (inrᵉ _)) = reflᵉ

nat-inl-coproduct-Finᵉ :
  (nᵉ mᵉ : ℕᵉ) (iᵉ : Finᵉ nᵉ) →
  nat-Finᵉ (nᵉ +ℕᵉ mᵉ) (inl-coproduct-Finᵉ nᵉ mᵉ iᵉ) ＝ᵉ nat-Finᵉ nᵉ iᵉ
nat-inl-coproduct-Finᵉ nᵉ mᵉ iᵉ = nat-coproduct-Finᵉ nᵉ mᵉ (inlᵉ iᵉ)

nat-inr-coproduct-Finᵉ :
  (nᵉ mᵉ : ℕᵉ) (iᵉ : Finᵉ mᵉ) →
  nat-Finᵉ (nᵉ +ℕᵉ mᵉ) (inr-coproduct-Finᵉ nᵉ mᵉ iᵉ) ＝ᵉ nᵉ +ℕᵉ (nat-Finᵉ mᵉ iᵉ)
nat-inr-coproduct-Finᵉ nᵉ mᵉ iᵉ = nat-coproduct-Finᵉ nᵉ mᵉ (inrᵉ iᵉ)
```

### Types equipped with a count are closed under coproducts

```agda
count-coproductᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  countᵉ Xᵉ → countᵉ Yᵉ → countᵉ (Xᵉ +ᵉ Yᵉ)
pr1ᵉ (count-coproductᵉ (pairᵉ kᵉ eᵉ) (pairᵉ lᵉ fᵉ)) = kᵉ +ℕᵉ lᵉ
pr2ᵉ (count-coproductᵉ (pairᵉ kᵉ eᵉ) (pairᵉ lᵉ fᵉ)) =
  (equiv-coproductᵉ eᵉ fᵉ) ∘eᵉ (inv-equivᵉ (coproduct-Finᵉ kᵉ lᵉ))

abstract
  number-of-elements-count-coproductᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : countᵉ Xᵉ) (fᵉ : countᵉ Yᵉ) →
    Idᵉ ( number-of-elements-countᵉ (count-coproductᵉ eᵉ fᵉ))
      ( (number-of-elements-countᵉ eᵉ) +ℕᵉ (number-of-elements-countᵉ fᵉ))
  number-of-elements-count-coproductᵉ (pairᵉ kᵉ eᵉ) (pairᵉ lᵉ fᵉ) = reflᵉ
```

### If both `Σ A P` and `Σ A Q` have a count, then `Σ A P + Q` have a count

```agda
count-Σ-coproductᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ} {Qᵉ : Aᵉ → UUᵉ l3ᵉ} →
  countᵉ (Σᵉ Aᵉ Pᵉ) → countᵉ (Σᵉ Aᵉ Qᵉ) → countᵉ (Σᵉ Aᵉ (λ xᵉ → (Pᵉ xᵉ) +ᵉ (Qᵉ xᵉ)))
pr1ᵉ (count-Σ-coproductᵉ count-Pᵉ count-Qᵉ) = pr1ᵉ (count-coproductᵉ count-Pᵉ count-Qᵉ)
pr2ᵉ (count-Σ-coproductᵉ count-Pᵉ count-Qᵉ) =
  ( inv-equivᵉ (left-distributive-Σ-coproductᵉ _ _ _)) ∘eᵉ
  ( pr2ᵉ (count-coproductᵉ count-Pᵉ count-Qᵉ))
```

### If `X + Y` has a count, then both `X` and `Y` have a count

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  count-left-summandᵉ : countᵉ (Xᵉ +ᵉ Yᵉ) → countᵉ Xᵉ
  count-left-summandᵉ eᵉ =
    count-equivᵉ
      ( equiv-left-summandᵉ)
      ( count-decidable-subtypeᵉ is-left-Decidable-Propᵉ eᵉ)

  count-right-summandᵉ : countᵉ (Xᵉ +ᵉ Yᵉ) → countᵉ Yᵉ
  count-right-summandᵉ eᵉ =
    count-equivᵉ
      ( equiv-right-summandᵉ)
      ( count-decidable-subtypeᵉ is-right-Decidable-Propᵉ eᵉ)
```

### If each of `A`, `B`, and `A + B` come equipped with countings, then the number of elements of `A` and of `B` add up to the number of elements of `A + B`

```agda
abstract
  double-counting-coproductᵉ :
    { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
    ( count-Aᵉ : countᵉ Aᵉ) (count-Bᵉ : countᵉ Bᵉ) (count-Cᵉ : countᵉ (Aᵉ +ᵉ Bᵉ)) →
    Idᵉ
      ( number-of-elements-countᵉ count-Cᵉ)
      ( number-of-elements-countᵉ count-Aᵉ +ℕᵉ number-of-elements-countᵉ count-Bᵉ)
  double-counting-coproductᵉ count-Aᵉ count-Bᵉ count-Cᵉ =
    ( double-countingᵉ count-Cᵉ (count-coproductᵉ count-Aᵉ count-Bᵉ)) ∙ᵉ
    ( number-of-elements-count-coproductᵉ count-Aᵉ count-Bᵉ)

abstract
  sum-number-of-elements-coproductᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : countᵉ (Aᵉ +ᵉ Bᵉ)) →
    Idᵉ
      ( ( number-of-elements-countᵉ (count-left-summandᵉ eᵉ)) +ℕᵉ
        ( number-of-elements-countᵉ (count-right-summandᵉ eᵉ)))
      ( number-of-elements-countᵉ eᵉ)
  sum-number-of-elements-coproductᵉ eᵉ =
    ( invᵉ
      ( number-of-elements-count-coproductᵉ
        ( count-left-summandᵉ eᵉ)
        ( count-right-summandᵉ eᵉ))) ∙ᵉ
    ( invᵉ
      ( double-counting-coproductᵉ
        ( count-left-summandᵉ eᵉ)
        ( count-right-summandᵉ eᵉ) eᵉ))
```

### Finite types are closed under coproducts

```agda
abstract
  is-finite-coproductᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
    is-finiteᵉ Xᵉ → is-finiteᵉ Yᵉ → is-finiteᵉ (Xᵉ +ᵉ Yᵉ)
  is-finite-coproductᵉ {Xᵉ = Xᵉ} {Yᵉ} is-finite-Xᵉ is-finite-Yᵉ =
    apply-universal-property-trunc-Propᵉ is-finite-Xᵉ
      ( is-finite-Propᵉ (Xᵉ +ᵉ Yᵉ))
      ( λ (eᵉ : countᵉ Xᵉ) →
        apply-universal-property-trunc-Propᵉ is-finite-Yᵉ
          ( is-finite-Propᵉ (Xᵉ +ᵉ Yᵉ))
          ( is-finite-countᵉ ∘ᵉ (count-coproductᵉ eᵉ)))

coproduct-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → 𝔽ᵉ l1ᵉ → 𝔽ᵉ l2ᵉ → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (coproduct-𝔽ᵉ Xᵉ Yᵉ) = (type-𝔽ᵉ Xᵉ) +ᵉ (type-𝔽ᵉ Yᵉ)
pr2ᵉ (coproduct-𝔽ᵉ Xᵉ Yᵉ) =
  is-finite-coproductᵉ (is-finite-type-𝔽ᵉ Xᵉ) (is-finite-type-𝔽ᵉ Yᵉ)

abstract
  is-finite-left-summandᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → is-finiteᵉ (Xᵉ +ᵉ Yᵉ) →
    is-finiteᵉ Xᵉ
  is-finite-left-summandᵉ =
    map-trunc-Propᵉ count-left-summandᵉ

abstract
  is-finite-right-summandᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → is-finiteᵉ (Xᵉ +ᵉ Yᵉ) →
    is-finiteᵉ Yᵉ
  is-finite-right-summandᵉ =
    map-trunc-Propᵉ count-right-summandᵉ

coproduct-UU-Finᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ lᵉ : ℕᵉ) → UU-Finᵉ l1ᵉ kᵉ → UU-Finᵉ l2ᵉ lᵉ →
  UU-Finᵉ (l1ᵉ ⊔ l2ᵉ) (kᵉ +ℕᵉ lᵉ)
pr1ᵉ (coproduct-UU-Finᵉ {l1ᵉ} {l2ᵉ} kᵉ lᵉ (pairᵉ Xᵉ Hᵉ) (pairᵉ Yᵉ Kᵉ)) = Xᵉ +ᵉ Yᵉ
pr2ᵉ (coproduct-UU-Finᵉ {l1ᵉ} {l2ᵉ} kᵉ lᵉ (pairᵉ Xᵉ Hᵉ) (pairᵉ Yᵉ Kᵉ)) =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( mere-equiv-Propᵉ (Finᵉ (kᵉ +ℕᵉ lᵉ)) (Xᵉ +ᵉ Yᵉ))
    ( λ e1ᵉ →
      apply-universal-property-trunc-Propᵉ Kᵉ
        ( mere-equiv-Propᵉ (Finᵉ (kᵉ +ℕᵉ lᵉ)) (Xᵉ +ᵉ Yᵉ))
        ( λ e2ᵉ →
          unit-trunc-Propᵉ
            ( equiv-coproductᵉ e1ᵉ e2ᵉ ∘eᵉ inv-equivᵉ (coproduct-Finᵉ kᵉ lᵉ))))

coproduct-eq-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Pᵉ : is-finiteᵉ Xᵉ) (Qᵉ : is-finiteᵉ Yᵉ) →
    Idᵉ
      ( (number-of-elements-is-finiteᵉ Pᵉ) +ℕᵉ (number-of-elements-is-finiteᵉ Qᵉ))
      ( number-of-elements-is-finiteᵉ (is-finite-coproductᵉ Pᵉ Qᵉ))
coproduct-eq-is-finiteᵉ {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} Pᵉ Qᵉ =
  apᵉ
    ( number-of-elements-has-finite-cardinalityᵉ)
    ( all-elements-equal-has-finite-cardinalityᵉ
      ( pairᵉ
        ( number-of-elements-is-finiteᵉ Pᵉ +ℕᵉ number-of-elements-is-finiteᵉ Qᵉ)
        ( has-cardinality-type-UU-Finᵉ
          ( number-of-elements-is-finiteᵉ Pᵉ +ℕᵉ number-of-elements-is-finiteᵉ Qᵉ)
          ( coproduct-UU-Finᵉ
            ( number-of-elements-is-finiteᵉ Pᵉ)
            ( number-of-elements-is-finiteᵉ Qᵉ)
            ( pairᵉ Xᵉ
              ( mere-equiv-has-finite-cardinalityᵉ
                ( has-finite-cardinality-is-finiteᵉ Pᵉ)))
            ( pairᵉ Yᵉ
              ( mere-equiv-has-finite-cardinalityᵉ
                ( has-finite-cardinality-is-finiteᵉ Qᵉ))))))
      ( has-finite-cardinality-is-finiteᵉ (is-finite-coproductᵉ Pᵉ Qᵉ)))
```
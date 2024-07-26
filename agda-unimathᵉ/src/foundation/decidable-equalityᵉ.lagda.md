# Decidable equality

```agda
module foundation.decidable-equalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-negationᵉ
open import foundation.injective-mapsᵉ
open import foundation.negationᵉ
open import foundation.sectionsᵉ
open import foundation.setsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Definition

Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to haveᵉ **decidableᵉ equality**ᵉ ifᵉ `xᵉ ＝ᵉ y`ᵉ isᵉ aᵉ
[decidableᵉ type](foundation.decidable-types.mdᵉ) forᵉ everyᵉ `xᵉ yᵉ : A`.ᵉ

```agda
has-decidable-equalityᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
has-decidable-equalityᵉ Aᵉ = (xᵉ yᵉ : Aᵉ) → is-decidableᵉ (xᵉ ＝ᵉ yᵉ)
```

## Examples

### Any proposition has decidable equality

```agda
abstract
  has-decidable-equality-is-propᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-propᵉ Aᵉ → has-decidable-equalityᵉ Aᵉ
  has-decidable-equality-is-propᵉ Hᵉ xᵉ yᵉ = inlᵉ (eq-is-propᵉ Hᵉ)
```

### The empty type has decidable equality

```agda
has-decidable-equality-emptyᵉ : has-decidable-equalityᵉ emptyᵉ
has-decidable-equality-emptyᵉ ()
```

### The unit type has decidable equality

```agda
has-decidable-equality-unitᵉ :
  has-decidable-equalityᵉ unitᵉ
has-decidable-equality-unitᵉ starᵉ starᵉ = inlᵉ reflᵉ
```

## Properties

### A product of types with decidable equality has decidable equality

```agda
has-decidable-equality-product'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (fᵉ : Bᵉ → has-decidable-equalityᵉ Aᵉ) (gᵉ : Aᵉ → has-decidable-equalityᵉ Bᵉ) →
  has-decidable-equalityᵉ (Aᵉ ×ᵉ Bᵉ)
has-decidable-equality-product'ᵉ fᵉ gᵉ (pairᵉ xᵉ yᵉ) (pairᵉ x'ᵉ y'ᵉ) with
  fᵉ yᵉ xᵉ x'ᵉ | gᵉ xᵉ yᵉ y'ᵉ
... | inlᵉ reflᵉ | inlᵉ reflᵉ = inlᵉ reflᵉ
... | inlᵉ reflᵉ | inrᵉ nqᵉ = inrᵉ (λ rᵉ → nqᵉ (apᵉ pr2ᵉ rᵉ))
... | inrᵉ npᵉ | inlᵉ reflᵉ = inrᵉ (λ rᵉ → npᵉ (apᵉ pr1ᵉ rᵉ))
... | inrᵉ npᵉ | inrᵉ nqᵉ = inrᵉ (λ rᵉ → npᵉ (apᵉ pr1ᵉ rᵉ))

has-decidable-equality-productᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  has-decidable-equalityᵉ Aᵉ → has-decidable-equalityᵉ Bᵉ →
  has-decidable-equalityᵉ (Aᵉ ×ᵉ Bᵉ)
has-decidable-equality-productᵉ dᵉ eᵉ =
  has-decidable-equality-product'ᵉ (λ yᵉ → dᵉ) (λ xᵉ → eᵉ)
```

### Decidability of equality of the factors of a cartesian product

Ifᵉ `Aᵉ ×ᵉ B`ᵉ hasᵉ decidableᵉ equalityᵉ andᵉ `B`ᵉ hasᵉ anᵉ element,ᵉ thenᵉ `A`ᵉ hasᵉ decidableᵉ
equality;ᵉ andᵉ viceᵉ versa.ᵉ

```agda
has-decidable-equality-left-factorᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  has-decidable-equalityᵉ (Aᵉ ×ᵉ Bᵉ) → Bᵉ → has-decidable-equalityᵉ Aᵉ
has-decidable-equality-left-factorᵉ dᵉ bᵉ xᵉ yᵉ with dᵉ (pairᵉ xᵉ bᵉ) (pairᵉ yᵉ bᵉ)
... | inlᵉ pᵉ = inlᵉ (apᵉ pr1ᵉ pᵉ)
... | inrᵉ npᵉ = inrᵉ (λ qᵉ → npᵉ (apᵉ (λ zᵉ → pairᵉ zᵉ bᵉ) qᵉ))

has-decidable-equality-right-factorᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  has-decidable-equalityᵉ (Aᵉ ×ᵉ Bᵉ) → Aᵉ → has-decidable-equalityᵉ Bᵉ
has-decidable-equality-right-factorᵉ dᵉ aᵉ xᵉ yᵉ with dᵉ (pairᵉ aᵉ xᵉ) (pairᵉ aᵉ yᵉ)
... | inlᵉ pᵉ = inlᵉ (apᵉ pr2ᵉ pᵉ)
... | inrᵉ npᵉ = inrᵉ (λ qᵉ → npᵉ (eq-pair-eq-fiberᵉ qᵉ))
```

### Types with decidable equality are closed under retracts

```agda
abstract
  has-decidable-equality-retract-ofᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    Aᵉ retract-ofᵉ Bᵉ → has-decidable-equalityᵉ Bᵉ → has-decidable-equalityᵉ Aᵉ
  has-decidable-equality-retract-ofᵉ (pairᵉ iᵉ (pairᵉ rᵉ Hᵉ)) dᵉ xᵉ yᵉ =
    is-decidable-retract-ofᵉ
      ( retract-eqᵉ (pairᵉ iᵉ (pairᵉ rᵉ Hᵉ)) xᵉ yᵉ)
      ( dᵉ (iᵉ xᵉ) (iᵉ yᵉ))
```

### Types with decidable equality are closed under equivalences

```agda
abstract
  has-decidable-equality-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    has-decidable-equalityᵉ Bᵉ → has-decidable-equalityᵉ Aᵉ
  has-decidable-equality-equivᵉ eᵉ dBᵉ xᵉ yᵉ =
    is-decidable-equivᵉ (equiv-apᵉ eᵉ xᵉ yᵉ) (dBᵉ (map-equivᵉ eᵉ xᵉ) (map-equivᵉ eᵉ yᵉ))

abstract
  has-decidable-equality-equiv'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    has-decidable-equalityᵉ Aᵉ → has-decidable-equalityᵉ Bᵉ
  has-decidable-equality-equiv'ᵉ eᵉ = has-decidable-equality-equivᵉ (inv-equivᵉ eᵉ)
```

### Hedberg's theorem

**Hedberg'sᵉ theorem**ᵉ assertsᵉ thatᵉ typesᵉ with decidableᵉ equalityᵉ areᵉ
[sets](foundation-core.sets.md).ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  Eq-has-decidable-equality'ᵉ :
    (xᵉ yᵉ : Aᵉ) → is-decidableᵉ (xᵉ ＝ᵉ yᵉ) → UUᵉ lzero
  Eq-has-decidable-equality'ᵉ xᵉ yᵉ (inlᵉ pᵉ) = unitᵉ
  Eq-has-decidable-equality'ᵉ xᵉ yᵉ (inrᵉ fᵉ) = emptyᵉ

  Eq-has-decidable-equalityᵉ :
    (dᵉ : has-decidable-equalityᵉ Aᵉ) → Aᵉ → Aᵉ → UUᵉ lzero
  Eq-has-decidable-equalityᵉ dᵉ xᵉ yᵉ = Eq-has-decidable-equality'ᵉ xᵉ yᵉ (dᵉ xᵉ yᵉ)

  abstract
    is-prop-Eq-has-decidable-equality'ᵉ :
      (xᵉ yᵉ : Aᵉ) (tᵉ : is-decidableᵉ (xᵉ ＝ᵉ yᵉ)) →
      is-propᵉ (Eq-has-decidable-equality'ᵉ xᵉ yᵉ tᵉ)
    is-prop-Eq-has-decidable-equality'ᵉ xᵉ yᵉ (inlᵉ pᵉ) = is-prop-unitᵉ
    is-prop-Eq-has-decidable-equality'ᵉ xᵉ yᵉ (inrᵉ fᵉ) = is-prop-emptyᵉ

  abstract
    is-prop-Eq-has-decidable-equalityᵉ :
      (dᵉ : has-decidable-equalityᵉ Aᵉ)
      {xᵉ yᵉ : Aᵉ} → is-propᵉ (Eq-has-decidable-equalityᵉ dᵉ xᵉ yᵉ)
    is-prop-Eq-has-decidable-equalityᵉ dᵉ {xᵉ} {yᵉ} =
      is-prop-Eq-has-decidable-equality'ᵉ xᵉ yᵉ (dᵉ xᵉ yᵉ)

  abstract
    refl-Eq-has-decidable-equalityᵉ :
      (dᵉ : has-decidable-equalityᵉ Aᵉ) (xᵉ : Aᵉ) →
      Eq-has-decidable-equalityᵉ dᵉ xᵉ xᵉ
    refl-Eq-has-decidable-equalityᵉ dᵉ xᵉ with dᵉ xᵉ xᵉ
    ... | inlᵉ αᵉ = starᵉ
    ... | inrᵉ fᵉ = fᵉ reflᵉ

  abstract
    Eq-has-decidable-equality-eqᵉ :
      (dᵉ : has-decidable-equalityᵉ Aᵉ) {xᵉ yᵉ : Aᵉ} →
      xᵉ ＝ᵉ yᵉ → Eq-has-decidable-equalityᵉ dᵉ xᵉ yᵉ
    Eq-has-decidable-equality-eqᵉ dᵉ {xᵉ} {.xᵉ} reflᵉ =
      refl-Eq-has-decidable-equalityᵉ dᵉ xᵉ

  abstract
    eq-Eq-has-decidable-equality'ᵉ :
      (xᵉ yᵉ : Aᵉ) (tᵉ : is-decidableᵉ (xᵉ ＝ᵉ yᵉ)) →
      Eq-has-decidable-equality'ᵉ xᵉ yᵉ tᵉ → xᵉ ＝ᵉ yᵉ
    eq-Eq-has-decidable-equality'ᵉ xᵉ yᵉ (inlᵉ pᵉ) tᵉ = pᵉ
    eq-Eq-has-decidable-equality'ᵉ xᵉ yᵉ (inrᵉ fᵉ) tᵉ = ex-falsoᵉ tᵉ

  abstract
    eq-Eq-has-decidable-equalityᵉ :
      (dᵉ : has-decidable-equalityᵉ Aᵉ) {xᵉ yᵉ : Aᵉ} →
      Eq-has-decidable-equalityᵉ dᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
    eq-Eq-has-decidable-equalityᵉ dᵉ {xᵉ} {yᵉ} =
      eq-Eq-has-decidable-equality'ᵉ xᵉ yᵉ (dᵉ xᵉ yᵉ)

  abstract
    is-set-has-decidable-equalityᵉ : has-decidable-equalityᵉ Aᵉ → is-setᵉ Aᵉ
    is-set-has-decidable-equalityᵉ dᵉ =
      is-set-prop-in-idᵉ
        ( λ xᵉ yᵉ → Eq-has-decidable-equalityᵉ dᵉ xᵉ yᵉ)
        ( λ xᵉ yᵉ → is-prop-Eq-has-decidable-equalityᵉ dᵉ)
        ( λ xᵉ → refl-Eq-has-decidable-equalityᵉ dᵉ xᵉ)
        ( λ xᵉ yᵉ → eq-Eq-has-decidable-equalityᵉ dᵉ)
```

### Having decidable equality is a property

```agda
abstract
  is-prop-has-decidable-equalityᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-propᵉ (has-decidable-equalityᵉ Xᵉ)
  is-prop-has-decidable-equalityᵉ {l1ᵉ} {Xᵉ} =
    is-prop-has-elementᵉ
      ( λ dᵉ →
        is-prop-Πᵉ
        ( λ xᵉ →
          is-prop-Πᵉ
          ( λ yᵉ →
            is-prop-coproductᵉ
            ( intro-double-negationᵉ)
            ( is-set-has-decidable-equalityᵉ dᵉ xᵉ yᵉ)
            ( is-prop-negᵉ))))

has-decidable-equality-Propᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → Propᵉ l1ᵉ
pr1ᵉ (has-decidable-equality-Propᵉ Xᵉ) = has-decidable-equalityᵉ Xᵉ
pr2ᵉ (has-decidable-equality-Propᵉ Xᵉ) = is-prop-has-decidable-equalityᵉ
```

### Types with decidable equality are closed under dependent pair types

```agda
abstract
  has-decidable-equality-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    has-decidable-equalityᵉ Aᵉ → ((xᵉ : Aᵉ) → has-decidable-equalityᵉ (Bᵉ xᵉ)) →
    has-decidable-equalityᵉ (Σᵉ Aᵉ Bᵉ)
  has-decidable-equality-Σᵉ dAᵉ dBᵉ (pairᵉ xᵉ yᵉ) (pairᵉ x'ᵉ y'ᵉ) with dAᵉ xᵉ x'ᵉ
  ... | inrᵉ npᵉ = inrᵉ (λ rᵉ → npᵉ (apᵉ pr1ᵉ rᵉ))
  ... | inlᵉ pᵉ =
    is-decidable-iffᵉ eq-pair-Σ'ᵉ pair-eq-Σᵉ
      ( is-decidable-equivᵉ
        ( left-unit-law-Σ-is-contrᵉ
          ( is-proof-irrelevant-is-propᵉ
            ( is-set-has-decidable-equalityᵉ dAᵉ xᵉ x'ᵉ) pᵉ)
          ( pᵉ))
        ( dBᵉ x'ᵉ (trᵉ _ pᵉ yᵉ) y'ᵉ))
```

### A family of types over a type with decidable equality and decidable total space is a family of types with decidable equality

```agda
abstract
  has-decidable-equality-fiber-has-decidable-equality-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    has-decidable-equalityᵉ Aᵉ → has-decidable-equalityᵉ (Σᵉ Aᵉ Bᵉ) →
    (xᵉ : Aᵉ) → has-decidable-equalityᵉ (Bᵉ xᵉ)
  has-decidable-equality-fiber-has-decidable-equality-Σᵉ {Bᵉ = Bᵉ} dAᵉ dΣᵉ xᵉ =
    has-decidable-equality-equiv'ᵉ
      ( equiv-fiber-pr1ᵉ Bᵉ xᵉ)
      ( has-decidable-equality-Σᵉ dΣᵉ
        ( λ tᵉ →
          has-decidable-equality-is-propᵉ
            ( is-set-has-decidable-equalityᵉ dAᵉ (pr1ᵉ tᵉ) xᵉ)))
```

### If `B` is a family of types with decidable equality, the total space has decidable equality, and `B` has a section, then the base type has decidable equality

```agda
abstract
  has-decidable-equality-base-has-decidable-equality-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    has-decidable-equalityᵉ (Σᵉ Aᵉ Bᵉ) → ((xᵉ : Aᵉ) → has-decidable-equalityᵉ (Bᵉ xᵉ)) →
    has-decidable-equalityᵉ Aᵉ
  has-decidable-equality-base-has-decidable-equality-Σᵉ bᵉ dΣᵉ dBᵉ =
    has-decidable-equality-equiv'ᵉ
      ( equiv-total-fiberᵉ (map-section-familyᵉ bᵉ))
      ( has-decidable-equality-Σᵉ dΣᵉ
        ( λ tᵉ →
          has-decidable-equality-is-propᵉ
            ( is-prop-map-is-injectiveᵉ
              ( is-set-has-decidable-equalityᵉ dΣᵉ)
              ( is-injective-map-section-familyᵉ bᵉ)
              ( tᵉ))))
```

### If `A` and `B` have decidable equality, then so does their coproduct

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  has-decidable-equality-coproductᵉ :
    has-decidable-equalityᵉ Aᵉ → has-decidable-equalityᵉ Bᵉ →
    has-decidable-equalityᵉ (Aᵉ +ᵉ Bᵉ)
  has-decidable-equality-coproductᵉ dᵉ eᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) =
    is-decidable-iffᵉ (apᵉ inlᵉ) is-injective-inlᵉ (dᵉ xᵉ yᵉ)
  has-decidable-equality-coproductᵉ dᵉ eᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) =
    inrᵉ neq-inl-inrᵉ
  has-decidable-equality-coproductᵉ dᵉ eᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) =
    inrᵉ neq-inr-inlᵉ
  has-decidable-equality-coproductᵉ dᵉ eᵉ (inrᵉ xᵉ) (inrᵉ yᵉ) =
    is-decidable-iffᵉ (apᵉ inrᵉ) is-injective-inrᵉ (eᵉ xᵉ yᵉ)

  has-decidable-equality-left-summandᵉ :
    has-decidable-equalityᵉ (Aᵉ +ᵉ Bᵉ) → has-decidable-equalityᵉ Aᵉ
  has-decidable-equality-left-summandᵉ dᵉ xᵉ yᵉ =
    is-decidable-iffᵉ is-injective-inlᵉ (apᵉ inlᵉ) (dᵉ (inlᵉ xᵉ) (inlᵉ yᵉ))

  has-decidable-equality-right-summandᵉ :
    has-decidable-equalityᵉ (Aᵉ +ᵉ Bᵉ) → has-decidable-equalityᵉ Bᵉ
  has-decidable-equality-right-summandᵉ dᵉ xᵉ yᵉ =
    is-decidable-iffᵉ is-injective-inrᵉ (apᵉ inrᵉ) (dᵉ (inrᵉ xᵉ) (inrᵉ yᵉ))
```
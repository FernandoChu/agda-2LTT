# Equality of dependent pair types

```agda
module foundation.equality-dependent-pair-typesᵉ where

open import foundation-core.equality-dependent-pair-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ operationᵉ [`eq-pair-Σ`](foundation-core.equality-dependent-pair-types.mdᵉ)
canᵉ beᵉ seenᵉ asᵉ aᵉ "verticalᵉ composition"ᵉ operationᵉ thatᵉ combinesᵉ anᵉ
[identification](foundation-core.identity-types.mdᵉ) andᵉ aᵉ
[dependentᵉ identification](foundation.dependent-identifications.mdᵉ) overᵉ itᵉ intoᵉ
aᵉ singleᵉ identification.ᵉ Thisᵉ operationᵉ preserves,ᵉ in theᵉ appropriateᵉ sense,ᵉ theᵉ
groupoidalᵉ structureᵉ onᵉ dependentᵉ identifications.ᵉ

## Properties

### Interchange law of concatenation and `eq-pair-Σ`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  interchange-concat-eq-pair-Σᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ} {z'ᵉ : Bᵉ zᵉ} →
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ y'ᵉ z'ᵉ) →
    eq-pair-Σᵉ (pᵉ ∙ᵉ qᵉ) (concat-dependent-identificationᵉ Bᵉ pᵉ qᵉ p'ᵉ q'ᵉ) ＝ᵉ
    ( eq-pair-Σᵉ pᵉ p'ᵉ ∙ᵉ eq-pair-Σᵉ qᵉ q'ᵉ)
  interchange-concat-eq-pair-Σᵉ reflᵉ qᵉ reflᵉ q'ᵉ = reflᵉ
```

### Interchange law for concatenation and `pair-eq-Σ`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  interchange-concat-pair-eq-Σᵉ :
    {xᵉ yᵉ zᵉ : Σᵉ Aᵉ Bᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    pair-eq-Σᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ
    ( pr1ᵉ (pair-eq-Σᵉ pᵉ) ∙ᵉ pr1ᵉ (pair-eq-Σᵉ qᵉ) ,ᵉ
      concat-dependent-identificationᵉ Bᵉ
        ( pr1ᵉ (pair-eq-Σᵉ pᵉ))
        ( pr1ᵉ (pair-eq-Σᵉ qᵉ))
        ( pr2ᵉ (pair-eq-Σᵉ pᵉ))
        ( pr2ᵉ (pair-eq-Σᵉ qᵉ)))
  interchange-concat-pair-eq-Σᵉ reflᵉ qᵉ = reflᵉ

  pr1-interchange-concat-pair-eq-Σᵉ :
    {xᵉ yᵉ zᵉ : Σᵉ Aᵉ Bᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    pr1ᵉ (pair-eq-Σᵉ (pᵉ ∙ᵉ qᵉ)) ＝ᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ) ∙ᵉ pr1ᵉ (pair-eq-Σᵉ qᵉ))
  pr1-interchange-concat-pair-eq-Σᵉ pᵉ qᵉ =
    apᵉ pr1ᵉ (interchange-concat-pair-eq-Σᵉ pᵉ qᵉ)
```

### Distributivity of `inv` over `eq-pair-Σ`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  distributive-inv-eq-pair-Σᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ) →
    invᵉ (eq-pair-Σᵉ pᵉ p'ᵉ) ＝ᵉ
    eq-pair-Σᵉ (invᵉ pᵉ) (inv-dependent-identificationᵉ Bᵉ pᵉ p'ᵉ)
  distributive-inv-eq-pair-Σᵉ reflᵉ reflᵉ = reflᵉ

  distributive-inv-eq-pair-Σ-reflᵉ :
    {xᵉ : Aᵉ} {x'ᵉ y'ᵉ : Bᵉ xᵉ} (p'ᵉ : x'ᵉ ＝ᵉ y'ᵉ) →
    invᵉ (eq-pair-eq-fiberᵉ p'ᵉ) ＝ᵉ eq-pair-Σᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} reflᵉ (invᵉ p'ᵉ)
  distributive-inv-eq-pair-Σ-reflᵉ reflᵉ = reflᵉ
```

### Computing `pair-eq-Σ` at an identification of the form `ap f p`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ} (fᵉ : Xᵉ → Σᵉ Aᵉ Bᵉ)
  where

  pair-eq-Σ-apᵉ :
    {xᵉ yᵉ : Xᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    pair-eq-Σᵉ (apᵉ fᵉ pᵉ) ＝ᵉ
    ( ( apᵉ (pr1ᵉ ∘ᵉ fᵉ) pᵉ) ,ᵉ
      ( substitution-law-trᵉ Bᵉ (pr1ᵉ ∘ᵉ fᵉ) pᵉ ∙ᵉ apdᵉ (pr2ᵉ ∘ᵉ fᵉ) pᵉ))
  pair-eq-Σ-apᵉ reflᵉ = reflᵉ

  pr1-pair-eq-Σ-apᵉ :
    {xᵉ yᵉ : Xᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    pr1ᵉ (pair-eq-Σᵉ (apᵉ fᵉ pᵉ)) ＝ᵉ apᵉ (pr1ᵉ ∘ᵉ fᵉ) pᵉ
  pr1-pair-eq-Σ-apᵉ reflᵉ = reflᵉ
```

### Computing action of functions on identifications of the form `eq-pair-Σ p q`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ} (fᵉ : Σᵉ Aᵉ Bᵉ → Yᵉ)
  where

  compute-ap-eq-pair-Σᵉ :
    { xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {bᵉ : Bᵉ xᵉ} {b'ᵉ : Bᵉ yᵉ} →
    ( qᵉ : dependent-identificationᵉ Bᵉ pᵉ bᵉ b'ᵉ) →
    apᵉ fᵉ (eq-pair-Σᵉ pᵉ qᵉ) ＝ᵉ (apᵉ fᵉ (eq-pair-Σᵉ pᵉ reflᵉ) ∙ᵉ apᵉ (ev-pairᵉ fᵉ yᵉ) qᵉ)
  compute-ap-eq-pair-Σᵉ reflᵉ reflᵉ = reflᵉ
```

### Equality of dependent pair types consists of two orthogonal components

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  triangle-eq-pair-Σᵉ :
    { aᵉ a'ᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ a'ᵉ) →
    { bᵉ : Bᵉ aᵉ} {b'ᵉ : Bᵉ a'ᵉ} (qᵉ : dependent-identificationᵉ Bᵉ pᵉ bᵉ b'ᵉ) →
    eq-pair-Σᵉ pᵉ qᵉ ＝ᵉ (eq-pair-Σᵉ pᵉ reflᵉ ∙ᵉ eq-pair-Σᵉ reflᵉ qᵉ)
  triangle-eq-pair-Σᵉ reflᵉ qᵉ = reflᵉ
```

### Computing identifications in iterated dependent pair types

#### Computing identifications in dependent pair types of the form Σ (Σ A B) C

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Σᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ}
  where

  Eq-Σ²'ᵉ : (sᵉ tᵉ : Σᵉ (Σᵉ Aᵉ Bᵉ) Cᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  Eq-Σ²'ᵉ sᵉ tᵉ =
    Σᵉ ( Eq-Σᵉ (pr1ᵉ sᵉ) (pr1ᵉ tᵉ))
      ( λ qᵉ → dependent-identificationᵉ Cᵉ (eq-pair-Σ'ᵉ qᵉ) (pr2ᵉ sᵉ) (pr2ᵉ tᵉ))

  equiv-triple-eq-Σ'ᵉ :
    (sᵉ tᵉ : Σᵉ (Σᵉ Aᵉ Bᵉ) Cᵉ) →
    (sᵉ ＝ᵉ tᵉ) ≃ᵉ Eq-Σ²'ᵉ sᵉ tᵉ
  equiv-triple-eq-Σ'ᵉ sᵉ tᵉ =
    ( equiv-Σᵉ
      ( λ qᵉ →
        ( dependent-identificationᵉ
          ( Cᵉ)
          ( eq-pair-Σ'ᵉ qᵉ)
          ( pr2ᵉ sᵉ)
          ( pr2ᵉ tᵉ)))
      ( equiv-pair-eq-Σᵉ (pr1ᵉ sᵉ) (pr1ᵉ tᵉ))
      ( λ pᵉ →
        ( equiv-trᵉ
          ( λ qᵉ → dependent-identificationᵉ Cᵉ qᵉ (pr2ᵉ sᵉ) (pr2ᵉ tᵉ))
          ( invᵉ (is-section-pair-eq-Σᵉ (pr1ᵉ sᵉ) (pr1ᵉ tᵉ) pᵉ))))) ∘eᵉ
    ( equiv-pair-eq-Σᵉ sᵉ tᵉ)

  triple-eq-Σ'ᵉ :
    (sᵉ tᵉ : Σᵉ (Σᵉ Aᵉ Bᵉ) Cᵉ) →
    (sᵉ ＝ᵉ tᵉ) → Eq-Σ²'ᵉ sᵉ tᵉ
  triple-eq-Σ'ᵉ sᵉ tᵉ = map-equivᵉ (equiv-triple-eq-Σ'ᵉ sᵉ tᵉ)
```

#### Computing dependent identifications on the second component

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  where

  coh-eq-base-Σ²ᵉ :
    {sᵉ tᵉ : Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) λ yᵉ → Cᵉ xᵉ yᵉ)} (pᵉ : sᵉ ＝ᵉ tᵉ) →
    eq-base-eq-pair-Σᵉ pᵉ ＝ᵉ
    eq-base-eq-pair-Σᵉ (eq-base-eq-pair-Σᵉ (apᵉ (map-inv-associative-Σ'ᵉ Aᵉ Bᵉ Cᵉ) pᵉ))
  coh-eq-base-Σ²ᵉ reflᵉ = reflᵉ

  dependent-eq-second-component-eq-Σ²ᵉ :
    {sᵉ tᵉ : Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) λ yᵉ → Cᵉ xᵉ yᵉ)} (pᵉ : sᵉ ＝ᵉ tᵉ) →
    dependent-identificationᵉ Bᵉ (eq-base-eq-pair-Σᵉ pᵉ) (pr1ᵉ (pr2ᵉ sᵉ)) (pr1ᵉ (pr2ᵉ tᵉ))
  dependent-eq-second-component-eq-Σ²ᵉ {sᵉ = sᵉ} {tᵉ = tᵉ} pᵉ =
    ( apᵉ (λ qᵉ → trᵉ Bᵉ qᵉ (pr1ᵉ (pr2ᵉ sᵉ))) (coh-eq-base-Σ²ᵉ pᵉ)) ∙ᵉ
    ( pr2ᵉ
      ( pr1ᵉ
        ( triple-eq-Σ'ᵉ
          ( map-inv-associative-Σ'ᵉ Aᵉ Bᵉ Cᵉ sᵉ)
          ( map-inv-associative-Σ'ᵉ Aᵉ Bᵉ Cᵉ tᵉ)
          ( apᵉ (map-inv-associative-Σ'ᵉ Aᵉ Bᵉ Cᵉ) pᵉ))))
```

#### Computing dependent identifications on the third component

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Dᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ → UUᵉ l4ᵉ)
  where

  coh-eq-base-Σ³ᵉ :
    { sᵉ tᵉ : Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (λ yᵉ → Σᵉ (Cᵉ xᵉ) (Dᵉ xᵉ yᵉ)))} (pᵉ : sᵉ ＝ᵉ tᵉ) →
    eq-base-eq-pair-Σᵉ pᵉ ＝ᵉ
    eq-base-eq-pair-Σᵉ (apᵉ (map-equivᵉ (interchange-Σ-Σ-Σᵉ Dᵉ)) pᵉ)
  coh-eq-base-Σ³ᵉ reflᵉ = reflᵉ

  dependent-eq-third-component-eq-Σ³ᵉ :
    { sᵉ tᵉ : Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (λ yᵉ → Σᵉ (Cᵉ xᵉ) (Dᵉ xᵉ yᵉ)))} (pᵉ : sᵉ ＝ᵉ tᵉ) →
    dependent-identificationᵉ Cᵉ
      ( eq-base-eq-pair-Σᵉ pᵉ)
      ( pr1ᵉ (pr2ᵉ (pr2ᵉ sᵉ)))
      ( pr1ᵉ (pr2ᵉ (pr2ᵉ tᵉ)))
  dependent-eq-third-component-eq-Σ³ᵉ {sᵉ = sᵉ} {tᵉ = tᵉ} pᵉ =
    ( apᵉ (λ qᵉ → trᵉ Cᵉ qᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ sᵉ)))) (coh-eq-base-Σ³ᵉ pᵉ)) ∙ᵉ
    ( dependent-eq-second-component-eq-Σ²ᵉ
      ( apᵉ (map-equivᵉ (interchange-Σ-Σ-Σᵉ Dᵉ)) pᵉ))
```

## See also

-ᵉ Equalityᵉ proofsᵉ in cartesianᵉ productᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ functionᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in theᵉ fiberᵉ ofᵉ aᵉ mapᵉ areᵉ characterizedᵉ in
  [`foundation.equality-fibers-of-maps`](foundation.equality-fibers-of-maps.md).ᵉ
# Isolated elements

```agda
module foundation.isolated-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.constant-mapsᵉ
open import foundation.decidable-embeddingsᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-mapsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.maybeᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.setsᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.decidable-propositionsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `aᵉ : A`ᵉ isᵉ consideredᵉ to beᵉ **isolated**ᵉ ifᵉ `aᵉ ＝ᵉ x`ᵉ isᵉ
[decidable](foundation.decidable-types.mdᵉ) forᵉ anyᵉ `x`.ᵉ

## Definitions

### Isolated elements

```agda
is-isolatedᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (aᵉ : Xᵉ) → UUᵉ l1ᵉ
is-isolatedᵉ {l1ᵉ} {Xᵉ} aᵉ = (xᵉ : Xᵉ) → is-decidableᵉ (aᵉ ＝ᵉ xᵉ)

isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → UUᵉ l1ᵉ
isolated-elementᵉ Xᵉ = Σᵉ Xᵉ is-isolatedᵉ

module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : isolated-elementᵉ Xᵉ)
  where

  element-isolated-elementᵉ : Xᵉ
  element-isolated-elementᵉ = pr1ᵉ xᵉ

  is-isolated-isolated-elementᵉ : is-isolatedᵉ element-isolated-elementᵉ
  is-isolated-isolated-elementᵉ = pr2ᵉ xᵉ
```

### Complements of isolated elements

```agda
complement-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → isolated-elementᵉ Xᵉ → UUᵉ l1ᵉ
complement-isolated-elementᵉ Xᵉ xᵉ =
  Σᵉ Xᵉ (λ yᵉ → element-isolated-elementᵉ xᵉ ≠ᵉ yᵉ)
```

## Properties

### An element is isolated if and only if the constant map pointing at it is decidable

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  is-decidable-point-is-isolatedᵉ :
    is-isolatedᵉ aᵉ → is-decidable-mapᵉ (pointᵉ aᵉ)
  is-decidable-point-is-isolatedᵉ dᵉ xᵉ =
    is-decidable-equivᵉ (compute-fiber-pointᵉ aᵉ xᵉ) (dᵉ xᵉ)

  is-isolated-is-decidable-pointᵉ :
    is-decidable-mapᵉ (pointᵉ aᵉ) → is-isolatedᵉ aᵉ
  is-isolated-is-decidable-pointᵉ dᵉ xᵉ =
    is-decidable-equiv'ᵉ (compute-fiber-pointᵉ aᵉ xᵉ) (dᵉ xᵉ)

  cases-Eq-isolated-elementᵉ :
    is-isolatedᵉ aᵉ → (xᵉ : Aᵉ) → is-decidableᵉ (aᵉ ＝ᵉ xᵉ) → UUᵉ lzero
  cases-Eq-isolated-elementᵉ Hᵉ xᵉ (inlᵉ pᵉ) = unitᵉ
  cases-Eq-isolated-elementᵉ Hᵉ xᵉ (inrᵉ fᵉ) = emptyᵉ

  abstract
    is-prop-cases-Eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) (xᵉ : Aᵉ) (dxᵉ : is-decidableᵉ (aᵉ ＝ᵉ xᵉ)) →
      is-propᵉ (cases-Eq-isolated-elementᵉ dᵉ xᵉ dxᵉ)
    is-prop-cases-Eq-isolated-elementᵉ dᵉ xᵉ (inlᵉ pᵉ) = is-prop-unitᵉ
    is-prop-cases-Eq-isolated-elementᵉ dᵉ xᵉ (inrᵉ fᵉ) = is-prop-emptyᵉ

  Eq-isolated-elementᵉ : is-isolatedᵉ aᵉ → Aᵉ → UUᵉ lzero
  Eq-isolated-elementᵉ dᵉ xᵉ = cases-Eq-isolated-elementᵉ dᵉ xᵉ (dᵉ xᵉ)

  abstract
    is-prop-Eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) (xᵉ : Aᵉ) → is-propᵉ (Eq-isolated-elementᵉ dᵉ xᵉ)
    is-prop-Eq-isolated-elementᵉ dᵉ xᵉ =
      is-prop-cases-Eq-isolated-elementᵉ dᵉ xᵉ (dᵉ xᵉ)

  Eq-isolated-element-Propᵉ : is-isolatedᵉ aᵉ → Aᵉ → Propᵉ lzero
  pr1ᵉ (Eq-isolated-element-Propᵉ dᵉ xᵉ) = Eq-isolated-elementᵉ dᵉ xᵉ
  pr2ᵉ (Eq-isolated-element-Propᵉ dᵉ xᵉ) = is-prop-Eq-isolated-elementᵉ dᵉ xᵉ

  decide-reflexivityᵉ :
    (dᵉ : is-decidableᵉ (aᵉ ＝ᵉ aᵉ)) → Σᵉ (aᵉ ＝ᵉ aᵉ) (λ pᵉ → inlᵉ pᵉ ＝ᵉ dᵉ)
  pr1ᵉ (decide-reflexivityᵉ (inlᵉ pᵉ)) = pᵉ
  pr2ᵉ (decide-reflexivityᵉ (inlᵉ pᵉ)) = reflᵉ
  decide-reflexivityᵉ (inrᵉ fᵉ) = ex-falsoᵉ (fᵉ reflᵉ)

  abstract
    refl-Eq-isolated-elementᵉ : (dᵉ : is-isolatedᵉ aᵉ) → Eq-isolated-elementᵉ dᵉ aᵉ
    refl-Eq-isolated-elementᵉ dᵉ =
      trᵉ
        ( cases-Eq-isolated-elementᵉ dᵉ aᵉ)
        ( pr2ᵉ (decide-reflexivityᵉ (dᵉ aᵉ)))
        ( starᵉ)

  abstract
    Eq-eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) {xᵉ : Aᵉ} → aᵉ ＝ᵉ xᵉ → Eq-isolated-elementᵉ dᵉ xᵉ
    Eq-eq-isolated-elementᵉ dᵉ reflᵉ = refl-Eq-isolated-elementᵉ dᵉ

  abstract
    center-total-Eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) → Σᵉ Aᵉ (Eq-isolated-elementᵉ dᵉ)
    pr1ᵉ (center-total-Eq-isolated-elementᵉ dᵉ) = aᵉ
    pr2ᵉ (center-total-Eq-isolated-elementᵉ dᵉ) = refl-Eq-isolated-elementᵉ dᵉ

    cases-contraction-total-Eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) (xᵉ : Aᵉ) (dxᵉ : is-decidableᵉ (aᵉ ＝ᵉ xᵉ))
      (eᵉ : cases-Eq-isolated-elementᵉ dᵉ xᵉ dxᵉ) → aᵉ ＝ᵉ xᵉ
    cases-contraction-total-Eq-isolated-elementᵉ dᵉ xᵉ (inlᵉ pᵉ) eᵉ = pᵉ

    contraction-total-Eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) (tᵉ : Σᵉ Aᵉ (Eq-isolated-elementᵉ dᵉ)) →
      center-total-Eq-isolated-elementᵉ dᵉ ＝ᵉ tᵉ
    contraction-total-Eq-isolated-elementᵉ dᵉ (xᵉ ,ᵉ eᵉ) =
      eq-type-subtypeᵉ
        ( Eq-isolated-element-Propᵉ dᵉ)
        ( cases-contraction-total-Eq-isolated-elementᵉ dᵉ xᵉ (dᵉ xᵉ) eᵉ)

    is-torsorial-Eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) → is-torsorialᵉ (Eq-isolated-elementᵉ dᵉ)
    pr1ᵉ (is-torsorial-Eq-isolated-elementᵉ dᵉ) =
      center-total-Eq-isolated-elementᵉ dᵉ
    pr2ᵉ (is-torsorial-Eq-isolated-elementᵉ dᵉ) =
      contraction-total-Eq-isolated-elementᵉ dᵉ

  abstract
    is-equiv-Eq-eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) (xᵉ : Aᵉ) → is-equivᵉ (Eq-eq-isolated-elementᵉ dᵉ {xᵉ})
    is-equiv-Eq-eq-isolated-elementᵉ dᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-Eq-isolated-elementᵉ dᵉ)
        ( λ xᵉ → Eq-eq-isolated-elementᵉ dᵉ {xᵉ})

  abstract
    equiv-Eq-eq-isolated-elementᵉ :
      (dᵉ : is-isolatedᵉ aᵉ) (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Eq-isolated-elementᵉ dᵉ xᵉ
    pr1ᵉ (equiv-Eq-eq-isolated-elementᵉ dᵉ xᵉ) = Eq-eq-isolated-elementᵉ dᵉ
    pr2ᵉ (equiv-Eq-eq-isolated-elementᵉ dᵉ xᵉ) = is-equiv-Eq-eq-isolated-elementᵉ dᵉ xᵉ

  abstract
    is-prop-eq-isolated-elementᵉ : (dᵉ : is-isolatedᵉ aᵉ) (xᵉ : Aᵉ) → is-propᵉ (aᵉ ＝ᵉ xᵉ)
    is-prop-eq-isolated-elementᵉ dᵉ xᵉ =
      is-prop-equivᵉ
        ( equiv-Eq-eq-isolated-elementᵉ dᵉ xᵉ)
        ( is-prop-Eq-isolated-elementᵉ dᵉ xᵉ)

  is-contr-loop-space-isolated-elementᵉ :
    (dᵉ : is-isolatedᵉ aᵉ) → is-contrᵉ (aᵉ ＝ᵉ aᵉ)
  is-contr-loop-space-isolated-elementᵉ dᵉ =
    is-proof-irrelevant-is-propᵉ (is-prop-eq-isolated-elementᵉ dᵉ aᵉ) reflᵉ

  abstract
    is-emb-point-is-isolatedᵉ : is-isolatedᵉ aᵉ → is-embᵉ (pointᵉ aᵉ)
    is-emb-point-is-isolatedᵉ dᵉ starᵉ =
      fundamental-theorem-idᵉ
        ( is-contr-equivᵉ
          ( aᵉ ＝ᵉ aᵉ)
          ( left-unit-law-productᵉ)
          ( is-proof-irrelevant-is-propᵉ
            ( is-prop-eq-isolated-elementᵉ dᵉ aᵉ)
            ( reflᵉ)))
        ( λ xᵉ → apᵉ (λ yᵉ → aᵉ))
```

### Being an isolated element is a property

```agda
is-prop-is-isolatedᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) → is-propᵉ (is-isolatedᵉ aᵉ)
is-prop-is-isolatedᵉ aᵉ =
  is-prop-has-elementᵉ
    ( λ Hᵉ → is-prop-Πᵉ (is-prop-is-decidableᵉ ∘ᵉ is-prop-eq-isolated-elementᵉ aᵉ Hᵉ))

is-isolated-Propᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) → Propᵉ l1ᵉ
pr1ᵉ (is-isolated-Propᵉ aᵉ) = is-isolatedᵉ aᵉ
pr2ᵉ (is-isolated-Propᵉ aᵉ) = is-prop-is-isolatedᵉ aᵉ

inclusion-isolated-elementᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → isolated-elementᵉ Aᵉ → Aᵉ
inclusion-isolated-elementᵉ Aᵉ = pr1ᵉ

is-emb-inclusion-isolated-elementᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → is-embᵉ (inclusion-isolated-elementᵉ Aᵉ)
is-emb-inclusion-isolated-elementᵉ Aᵉ = is-emb-inclusion-subtypeᵉ is-isolated-Propᵉ

has-decidable-equality-isolated-elementᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → has-decidable-equalityᵉ (isolated-elementᵉ Aᵉ)
has-decidable-equality-isolated-elementᵉ Aᵉ (xᵉ ,ᵉ dxᵉ) (yᵉ ,ᵉ dyᵉ) =
  is-decidable-equivᵉ
    ( equiv-ap-inclusion-subtypeᵉ is-isolated-Propᵉ)
    ( dxᵉ yᵉ)

is-set-isolated-elementᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → is-setᵉ (isolated-elementᵉ Aᵉ)
is-set-isolated-elementᵉ Aᵉ =
  is-set-has-decidable-equalityᵉ (has-decidable-equality-isolated-elementᵉ Aᵉ)

module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : isolated-elementᵉ Aᵉ)
  where

  point-isolated-elementᵉ : unitᵉ → Aᵉ
  point-isolated-elementᵉ = pointᵉ (element-isolated-elementᵉ aᵉ)

  is-emb-point-isolated-elementᵉ : is-embᵉ point-isolated-elementᵉ
  is-emb-point-isolated-elementᵉ =
    is-emb-compᵉ
      ( inclusion-isolated-elementᵉ Aᵉ)
      ( pointᵉ aᵉ)
      ( is-emb-inclusion-isolated-elementᵉ Aᵉ)
      ( is-emb-is-injectiveᵉ
        ( is-set-isolated-elementᵉ Aᵉ)
        ( λ pᵉ → reflᵉ))

  emb-point-isolated-elementᵉ : unitᵉ ↪ᵉ Aᵉ
  pr1ᵉ emb-point-isolated-elementᵉ = point-isolated-elementᵉ
  pr2ᵉ emb-point-isolated-elementᵉ = is-emb-point-isolated-elementᵉ

  is-decidable-point-isolated-elementᵉ :
    is-decidable-mapᵉ point-isolated-elementᵉ
  is-decidable-point-isolated-elementᵉ xᵉ =
    is-decidable-productᵉ is-decidable-unitᵉ (is-isolated-isolated-elementᵉ aᵉ xᵉ)

  is-decidable-emb-point-isolated-elementᵉ :
    is-decidable-embᵉ point-isolated-elementᵉ
  pr1ᵉ is-decidable-emb-point-isolated-elementᵉ =
    is-emb-point-isolated-elementᵉ
  pr2ᵉ is-decidable-emb-point-isolated-elementᵉ =
    is-decidable-point-isolated-elementᵉ

  decidable-emb-point-isolated-elementᵉ : unitᵉ ↪ᵈᵉ Aᵉ
  pr1ᵉ decidable-emb-point-isolated-elementᵉ =
    point-isolated-elementᵉ
  pr2ᵉ decidable-emb-point-isolated-elementᵉ =
    is-decidable-emb-point-isolated-elementᵉ
```

### Types with isolated elements can be equipped with a Maybe-structure

```agda
map-maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : isolated-elementᵉ Xᵉ) →
  Maybeᵉ (complement-isolated-elementᵉ Xᵉ xᵉ) → Xᵉ
map-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dᵉ) (inlᵉ (yᵉ ,ᵉ fᵉ)) = yᵉ
map-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dᵉ) (inrᵉ starᵉ) = xᵉ

cases-map-inv-maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : isolated-elementᵉ Xᵉ) →
  (yᵉ : Xᵉ) → is-decidableᵉ (pr1ᵉ xᵉ ＝ᵉ yᵉ) → Maybeᵉ (complement-isolated-elementᵉ Xᵉ xᵉ)
cases-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dxᵉ) yᵉ (inlᵉ pᵉ) =
  inrᵉ starᵉ
cases-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dxᵉ) yᵉ (inrᵉ fᵉ) =
  inlᵉ (yᵉ ,ᵉ fᵉ)

map-inv-maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : isolated-elementᵉ Xᵉ) →
  Xᵉ → Maybeᵉ (complement-isolated-elementᵉ Xᵉ xᵉ)
map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dᵉ) yᵉ =
  cases-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dᵉ) yᵉ (dᵉ yᵉ)

cases-is-section-map-inv-maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : isolated-elementᵉ Xᵉ) →
  (yᵉ : Xᵉ) (dᵉ : is-decidableᵉ (pr1ᵉ xᵉ ＝ᵉ yᵉ)) →
  ( map-maybe-structure-isolated-elementᵉ Xᵉ xᵉ
    ( cases-map-inv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ yᵉ dᵉ)) ＝ᵉ
  ( yᵉ)
cases-is-section-map-inv-maybe-structure-isolated-elementᵉ Xᵉ
  (xᵉ ,ᵉ dxᵉ) .xᵉ (inlᵉ reflᵉ) =
  reflᵉ
cases-is-section-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dxᵉ) yᵉ (inrᵉ fᵉ) =
  reflᵉ

is-section-map-inv-maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : isolated-elementᵉ Xᵉ) →
  ( map-maybe-structure-isolated-elementᵉ Xᵉ xᵉ ∘ᵉ
    map-inv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ) ~ᵉ idᵉ
is-section-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dᵉ) yᵉ =
  cases-is-section-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dᵉ) yᵉ (dᵉ yᵉ)

is-retraction-map-inv-maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : isolated-elementᵉ Xᵉ) →
  ( map-inv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ ∘ᵉ
    map-maybe-structure-isolated-elementᵉ Xᵉ xᵉ) ~ᵉ idᵉ
is-retraction-map-inv-maybe-structure-isolated-elementᵉ
  Xᵉ (xᵉ ,ᵉ dxᵉ) (inlᵉ (yᵉ ,ᵉ fᵉ)) =
  apᵉ
    ( cases-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dxᵉ) yᵉ)
    ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-prop-eq-isolated-elementᵉ xᵉ dxᵉ yᵉ)))
is-retraction-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dxᵉ) (inrᵉ starᵉ) =
  apᵉ
    ( cases-map-inv-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dxᵉ) xᵉ)
    { xᵉ = dxᵉ (map-maybe-structure-isolated-elementᵉ Xᵉ (xᵉ ,ᵉ dxᵉ) (inrᵉ starᵉ))}
    { yᵉ = inlᵉ reflᵉ}
    ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-prop-eq-isolated-elementᵉ xᵉ dxᵉ xᵉ)))

is-equiv-map-maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : isolated-elementᵉ Xᵉ) →
  is-equivᵉ (map-maybe-structure-isolated-elementᵉ Xᵉ xᵉ)
is-equiv-map-maybe-structure-isolated-elementᵉ Xᵉ xᵉ =
  is-equiv-is-invertibleᵉ
    ( map-inv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ)
    ( is-section-map-inv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ)
    ( is-retraction-map-inv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ)

equiv-maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : isolated-elementᵉ Xᵉ) →
  Maybeᵉ (complement-isolated-elementᵉ Xᵉ xᵉ) ≃ᵉ Xᵉ
pr1ᵉ (equiv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ) =
  map-maybe-structure-isolated-elementᵉ Xᵉ xᵉ
pr2ᵉ (equiv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ) =
  is-equiv-map-maybe-structure-isolated-elementᵉ Xᵉ xᵉ

maybe-structure-isolated-elementᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → isolated-elementᵉ Xᵉ → maybe-structureᵉ Xᵉ
pr1ᵉ (maybe-structure-isolated-elementᵉ {l1ᵉ} {Xᵉ} xᵉ) =
  complement-isolated-elementᵉ Xᵉ xᵉ
pr2ᵉ (maybe-structure-isolated-elementᵉ {l1ᵉ} {Xᵉ} xᵉ) =
  equiv-maybe-structure-isolated-elementᵉ Xᵉ xᵉ
```

```agda
equiv-complement-isolated-elementᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) (xᵉ : isolated-elementᵉ Xᵉ)
  (yᵉ : isolated-elementᵉ Yᵉ) (pᵉ : map-equivᵉ eᵉ (pr1ᵉ xᵉ) ＝ᵉ pr1ᵉ yᵉ) →
  complement-isolated-elementᵉ Xᵉ xᵉ ≃ᵉ complement-isolated-elementᵉ Yᵉ yᵉ
equiv-complement-isolated-elementᵉ eᵉ xᵉ yᵉ pᵉ =
  equiv-Σᵉ
    ( λ zᵉ → pr1ᵉ yᵉ ≠ᵉ zᵉ)
    ( eᵉ)
    ( λ zᵉ →
      equiv-negᵉ
        ( equiv-concatᵉ (invᵉ pᵉ) (map-equivᵉ eᵉ zᵉ) ∘eᵉ (equiv-apᵉ eᵉ (pr1ᵉ xᵉ) zᵉ)))
```

```agda
inclusion-complement-isolated-elementᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : isolated-elementᵉ Xᵉ) →
  complement-isolated-elementᵉ Xᵉ xᵉ → Xᵉ
inclusion-complement-isolated-elementᵉ xᵉ = pr1ᵉ

natural-inclusion-equiv-complement-isolated-elementᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) (xᵉ : isolated-elementᵉ Xᵉ)
  (yᵉ : isolated-elementᵉ Yᵉ) (pᵉ : map-equivᵉ eᵉ (pr1ᵉ xᵉ) ＝ᵉ pr1ᵉ yᵉ) →
  ( inclusion-complement-isolated-elementᵉ yᵉ ∘ᵉ
    map-equivᵉ (equiv-complement-isolated-elementᵉ eᵉ xᵉ yᵉ pᵉ)) ~ᵉ
  ( map-equivᵉ eᵉ ∘ᵉ inclusion-complement-isolated-elementᵉ xᵉ)
natural-inclusion-equiv-complement-isolated-elementᵉ eᵉ xᵉ yᵉ pᵉ (x'ᵉ ,ᵉ fᵉ) = reflᵉ
```
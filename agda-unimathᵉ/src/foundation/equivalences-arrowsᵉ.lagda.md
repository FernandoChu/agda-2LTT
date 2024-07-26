# Equivalences of arrows

```agda
module foundation.equivalences-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrowsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.span-diagramsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
```

</details>

## Idea

Anᵉ {{#conceptᵉ "equivalenceᵉ ofᵉ arrows"ᵉ}} fromᵉ aᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ to aᵉ
functionᵉ `gᵉ : Xᵉ → Y`ᵉ isᵉ aᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |   ≃ᵉ    |
  fᵉ |        | gᵉ
    ∨ᵉ   ≃ᵉ    ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

in whichᵉ `i`ᵉ andᵉ `j`ᵉ areᵉ [equivalences](foundation-core.equivalences.md).ᵉ

## Definitions

### The predicate of being an equivalence of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  is-equiv-prop-hom-arrowᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-equiv-prop-hom-arrowᵉ =
    product-Propᵉ
      ( is-equiv-Propᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ hᵉ))
      ( is-equiv-Propᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ hᵉ))

  is-equiv-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-equiv-hom-arrowᵉ =
    type-Propᵉ is-equiv-prop-hom-arrowᵉ

  is-prop-is-equiv-hom-arrowᵉ : is-propᵉ is-equiv-hom-arrowᵉ
  is-prop-is-equiv-hom-arrowᵉ = is-prop-type-Propᵉ is-equiv-prop-hom-arrowᵉ

  is-equiv-map-domain-is-equiv-hom-arrowᵉ :
    is-equiv-hom-arrowᵉ → is-equivᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ hᵉ)
  is-equiv-map-domain-is-equiv-hom-arrowᵉ = pr1ᵉ

  is-equiv-map-codomain-is-equiv-hom-arrowᵉ :
    is-equiv-hom-arrowᵉ → is-equivᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ hᵉ)
  is-equiv-map-codomain-is-equiv-hom-arrowᵉ = pr2ᵉ
```

### Equivalences of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  coherence-equiv-arrowᵉ : (Aᵉ ≃ᵉ Xᵉ) → (Bᵉ ≃ᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-equiv-arrowᵉ iᵉ jᵉ =
    coherence-hom-arrowᵉ fᵉ gᵉ (map-equivᵉ iᵉ) (map-equivᵉ jᵉ)

  equiv-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-arrowᵉ =
    Σᵉ (Aᵉ ≃ᵉ Xᵉ) (λ iᵉ → Σᵉ (Bᵉ ≃ᵉ Yᵉ) (coherence-equiv-arrowᵉ iᵉ))

  module _
    (eᵉ : equiv-arrowᵉ)
    where

    equiv-domain-equiv-arrowᵉ : Aᵉ ≃ᵉ Xᵉ
    equiv-domain-equiv-arrowᵉ = pr1ᵉ eᵉ

    map-domain-equiv-arrowᵉ : Aᵉ → Xᵉ
    map-domain-equiv-arrowᵉ = map-equivᵉ equiv-domain-equiv-arrowᵉ

    is-equiv-map-domain-equiv-arrowᵉ : is-equivᵉ map-domain-equiv-arrowᵉ
    is-equiv-map-domain-equiv-arrowᵉ =
      is-equiv-map-equivᵉ equiv-domain-equiv-arrowᵉ

    equiv-codomain-equiv-arrowᵉ : Bᵉ ≃ᵉ Yᵉ
    equiv-codomain-equiv-arrowᵉ = pr1ᵉ (pr2ᵉ eᵉ)

    map-codomain-equiv-arrowᵉ : Bᵉ → Yᵉ
    map-codomain-equiv-arrowᵉ = map-equivᵉ equiv-codomain-equiv-arrowᵉ

    is-equiv-map-codomain-equiv-arrowᵉ : is-equivᵉ map-codomain-equiv-arrowᵉ
    is-equiv-map-codomain-equiv-arrowᵉ =
      is-equiv-map-equivᵉ equiv-codomain-equiv-arrowᵉ

    coh-equiv-arrowᵉ :
      coherence-equiv-arrowᵉ
        ( equiv-domain-equiv-arrowᵉ)
        ( equiv-codomain-equiv-arrowᵉ)
    coh-equiv-arrowᵉ = pr2ᵉ (pr2ᵉ eᵉ)

    hom-equiv-arrowᵉ : hom-arrowᵉ fᵉ gᵉ
    pr1ᵉ hom-equiv-arrowᵉ = map-domain-equiv-arrowᵉ
    pr1ᵉ (pr2ᵉ hom-equiv-arrowᵉ) = map-codomain-equiv-arrowᵉ
    pr2ᵉ (pr2ᵉ hom-equiv-arrowᵉ) = coh-equiv-arrowᵉ

    is-equiv-equiv-arrowᵉ : is-equiv-hom-arrowᵉ fᵉ gᵉ hom-equiv-arrowᵉ
    pr1ᵉ is-equiv-equiv-arrowᵉ = is-equiv-map-domain-equiv-arrowᵉ
    pr2ᵉ is-equiv-equiv-arrowᵉ = is-equiv-map-codomain-equiv-arrowᵉ

    span-equiv-arrowᵉ :
      spanᵉ l1ᵉ Bᵉ Xᵉ
    span-equiv-arrowᵉ =
      span-hom-arrowᵉ fᵉ gᵉ hom-equiv-arrowᵉ

    span-diagram-equiv-arrowᵉ : span-diagramᵉ l2ᵉ l3ᵉ l1ᵉ
    pr1ᵉ span-diagram-equiv-arrowᵉ = Bᵉ
    pr1ᵉ (pr2ᵉ span-diagram-equiv-arrowᵉ) = Xᵉ
    pr2ᵉ (pr2ᵉ span-diagram-equiv-arrowᵉ) = span-equiv-arrowᵉ
```

### The identity equivalence of arrows

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  id-equiv-arrowᵉ : equiv-arrowᵉ fᵉ fᵉ
  pr1ᵉ id-equiv-arrowᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-arrowᵉ) = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-arrowᵉ) = refl-htpyᵉ
```

### Composition of equivalences of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ)
  (bᵉ : equiv-arrowᵉ gᵉ hᵉ) (aᵉ : equiv-arrowᵉ fᵉ gᵉ)
  where

  equiv-domain-comp-equiv-arrowᵉ : Aᵉ ≃ᵉ Uᵉ
  equiv-domain-comp-equiv-arrowᵉ =
    equiv-domain-equiv-arrowᵉ gᵉ hᵉ bᵉ ∘eᵉ equiv-domain-equiv-arrowᵉ fᵉ gᵉ aᵉ

  map-domain-comp-equiv-arrowᵉ : Aᵉ → Uᵉ
  map-domain-comp-equiv-arrowᵉ = map-equivᵉ equiv-domain-comp-equiv-arrowᵉ

  equiv-codomain-comp-equiv-arrowᵉ : Bᵉ ≃ᵉ Vᵉ
  equiv-codomain-comp-equiv-arrowᵉ =
    equiv-codomain-equiv-arrowᵉ gᵉ hᵉ bᵉ ∘eᵉ equiv-codomain-equiv-arrowᵉ fᵉ gᵉ aᵉ

  map-codomain-comp-equiv-arrowᵉ : Bᵉ → Vᵉ
  map-codomain-comp-equiv-arrowᵉ = map-equivᵉ equiv-codomain-comp-equiv-arrowᵉ

  coh-comp-equiv-arrowᵉ :
    coherence-equiv-arrowᵉ fᵉ hᵉ
      ( equiv-domain-comp-equiv-arrowᵉ)
      ( equiv-codomain-comp-equiv-arrowᵉ)
  coh-comp-equiv-arrowᵉ =
    coh-comp-hom-arrowᵉ fᵉ gᵉ hᵉ
      ( hom-equiv-arrowᵉ gᵉ hᵉ bᵉ)
      ( hom-equiv-arrowᵉ fᵉ gᵉ aᵉ)

  comp-equiv-arrowᵉ : equiv-arrowᵉ fᵉ hᵉ
  pr1ᵉ comp-equiv-arrowᵉ = equiv-domain-comp-equiv-arrowᵉ
  pr1ᵉ (pr2ᵉ comp-equiv-arrowᵉ) = equiv-codomain-comp-equiv-arrowᵉ
  pr2ᵉ (pr2ᵉ comp-equiv-arrowᵉ) = coh-comp-equiv-arrowᵉ

  hom-comp-equiv-arrowᵉ : hom-arrowᵉ fᵉ hᵉ
  hom-comp-equiv-arrowᵉ = hom-equiv-arrowᵉ fᵉ hᵉ comp-equiv-arrowᵉ
```

### Inverses of equivalences of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : equiv-arrowᵉ fᵉ gᵉ)
  where

  equiv-domain-inv-equiv-arrowᵉ : Xᵉ ≃ᵉ Aᵉ
  equiv-domain-inv-equiv-arrowᵉ = inv-equivᵉ (equiv-domain-equiv-arrowᵉ fᵉ gᵉ αᵉ)

  map-domain-inv-equiv-arrowᵉ : Xᵉ → Aᵉ
  map-domain-inv-equiv-arrowᵉ = map-equivᵉ equiv-domain-inv-equiv-arrowᵉ

  equiv-codomain-inv-equiv-arrowᵉ : Yᵉ ≃ᵉ Bᵉ
  equiv-codomain-inv-equiv-arrowᵉ = inv-equivᵉ (equiv-codomain-equiv-arrowᵉ fᵉ gᵉ αᵉ)

  map-codomain-inv-equiv-arrowᵉ : Yᵉ → Bᵉ
  map-codomain-inv-equiv-arrowᵉ = map-equivᵉ equiv-codomain-inv-equiv-arrowᵉ

  coh-inv-equiv-arrowᵉ :
    coherence-equiv-arrowᵉ gᵉ fᵉ
      ( equiv-domain-inv-equiv-arrowᵉ)
      ( equiv-codomain-inv-equiv-arrowᵉ)
  coh-inv-equiv-arrowᵉ =
    horizontal-inv-equiv-coherence-square-mapsᵉ
      ( equiv-domain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( fᵉ)
      ( gᵉ)
      ( equiv-codomain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-equiv-arrowᵉ fᵉ gᵉ αᵉ)

  inv-equiv-arrowᵉ : equiv-arrowᵉ gᵉ fᵉ
  pr1ᵉ inv-equiv-arrowᵉ = equiv-domain-inv-equiv-arrowᵉ
  pr1ᵉ (pr2ᵉ inv-equiv-arrowᵉ) = equiv-codomain-inv-equiv-arrowᵉ
  pr2ᵉ (pr2ᵉ inv-equiv-arrowᵉ) = coh-inv-equiv-arrowᵉ

  hom-inv-equiv-arrowᵉ : hom-arrowᵉ gᵉ fᵉ
  hom-inv-equiv-arrowᵉ = hom-equiv-arrowᵉ gᵉ fᵉ inv-equiv-arrowᵉ

  is-equiv-inv-equiv-arrowᵉ : is-equiv-hom-arrowᵉ gᵉ fᵉ hom-inv-equiv-arrowᵉ
  is-equiv-inv-equiv-arrowᵉ = is-equiv-equiv-arrowᵉ gᵉ fᵉ inv-equiv-arrowᵉ
```

### If a map is equivalent to an equivalence, then it is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : equiv-arrowᵉ fᵉ gᵉ)
  where

  is-equiv-source-is-equiv-target-equiv-arrowᵉ : is-equivᵉ gᵉ → is-equivᵉ fᵉ
  is-equiv-source-is-equiv-target-equiv-arrowᵉ =
    is-equiv-left-is-equiv-right-squareᵉ
      ( fᵉ)
      ( gᵉ)
      ( map-domain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-codomain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-equiv-map-domain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-equiv-map-codomain-equiv-arrowᵉ fᵉ gᵉ αᵉ)

  is-equiv-target-is-equiv-source-equiv-arrowᵉ : is-equivᵉ fᵉ → is-equivᵉ gᵉ
  is-equiv-target-is-equiv-source-equiv-arrowᵉ =
    is-equiv-right-is-equiv-left-squareᵉ
      ( fᵉ)
      ( gᵉ)
      ( map-domain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-codomain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-equiv-map-domain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-equiv-map-codomain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
```

### Equivalences of arrows are cartesian

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : equiv-arrowᵉ fᵉ gᵉ)
  where

  is-cartesian-equiv-arrowᵉ :
    is-cartesian-hom-arrowᵉ fᵉ gᵉ (hom-equiv-arrowᵉ fᵉ gᵉ αᵉ)
  is-cartesian-equiv-arrowᵉ =
    is-pullback-is-equiv-horizontal-mapsᵉ
      ( map-codomain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( gᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ (hom-equiv-arrowᵉ fᵉ gᵉ αᵉ))
      ( is-equiv-map-codomain-equiv-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-equiv-map-domain-equiv-arrowᵉ fᵉ gᵉ αᵉ)

  cartesian-hom-equiv-arrowᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ
  pr1ᵉ cartesian-hom-equiv-arrowᵉ = hom-equiv-arrowᵉ fᵉ gᵉ αᵉ
  pr2ᵉ cartesian-hom-equiv-arrowᵉ = is-cartesian-equiv-arrowᵉ
```
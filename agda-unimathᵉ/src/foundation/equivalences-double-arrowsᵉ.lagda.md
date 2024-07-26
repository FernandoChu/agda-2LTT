# Equivalences of double arrows

```agda
module foundation.equivalences-double-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-double-arrowsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ
{{#conceptᵉ "equivalenceᵉ ofᵉ doubleᵉ arrows"ᵉ Disambiguation="betweenᵉ types"ᵉ Agda=equiv-double-arrowᵉ}}
fromᵉ aᵉ [doubleᵉ arrow](foundation.double-arrows.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`ᵉ to aᵉ doubleᵉ
arrowᵉ `h,ᵉ kᵉ : Xᵉ → Y`ᵉ isᵉ aᵉ pairᵉ ofᵉ
[equivalences](foundation-core.equivalences.mdᵉ) `iᵉ : Aᵉ ≃ᵉ X`ᵉ andᵉ `jᵉ : Bᵉ ≃ᵉ Y`,ᵉ
suchᵉ thatᵉ theᵉ squaresᵉ

```text
           iᵉ                   iᵉ
     Aᵉ -------->ᵉ Xᵉ       Aᵉ -------->ᵉ Xᵉ
     |     ≃ᵉ     |       |     ≃ᵉ     |
   fᵉ |           | hᵉ   gᵉ |           | kᵉ
     |           |       |           |
     ∨ᵉ     ≃ᵉ     ∨ᵉ       ∨ᵉ     ≃ᵉ     ∨ᵉ
     Bᵉ -------->ᵉ Yᵉ       Bᵉ -------->ᵉ Yᵉ
           jᵉ                   jᵉ
```

[commute](foundation-core.commuting-squares-of-maps.md).ᵉ Theᵉ equivalenceᵉ `i`ᵉ isᵉ
referredᵉ to asᵉ theᵉ _domainᵉ equivalence_,ᵉ andᵉ theᵉ `j`ᵉ asᵉ theᵉ _codomainᵉ
equivalence_.ᵉ

Alternatively,ᵉ anᵉ equivalenceᵉ ofᵉ doubleᵉ arrowsᵉ isᵉ aᵉ pairᵉ ofᵉ
[equivalencesᵉ ofᵉ arrows](foundation.equivalences-arrows.mdᵉ) `fᵉ ≃ᵉ h`ᵉ andᵉ `gᵉ ≃ᵉ k`ᵉ
thatᵉ shareᵉ theᵉ underlyingᵉ maps.ᵉ

## Definitions

### Equivalences of double arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (a'ᵉ : double-arrowᵉ l3ᵉ l4ᵉ)
  where

  left-coherence-equiv-double-arrowᵉ :
    (domain-double-arrowᵉ aᵉ ≃ᵉ domain-double-arrowᵉ a'ᵉ) →
    (codomain-double-arrowᵉ aᵉ ≃ᵉ codomain-double-arrowᵉ a'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  left-coherence-equiv-double-arrowᵉ eAᵉ eBᵉ =
    left-coherence-hom-double-arrowᵉ aᵉ a'ᵉ (map-equivᵉ eAᵉ) (map-equivᵉ eBᵉ)

  right-coherence-equiv-double-arrowᵉ :
    (domain-double-arrowᵉ aᵉ ≃ᵉ domain-double-arrowᵉ a'ᵉ) →
    (codomain-double-arrowᵉ aᵉ ≃ᵉ codomain-double-arrowᵉ a'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  right-coherence-equiv-double-arrowᵉ eAᵉ eBᵉ =
    right-coherence-hom-double-arrowᵉ aᵉ a'ᵉ (map-equivᵉ eAᵉ) (map-equivᵉ eBᵉ)

  equiv-double-arrowᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-double-arrowᵉ =
    Σᵉ ( domain-double-arrowᵉ aᵉ ≃ᵉ domain-double-arrowᵉ a'ᵉ)
      ( λ eAᵉ →
        Σᵉ ( codomain-double-arrowᵉ aᵉ ≃ᵉ codomain-double-arrowᵉ a'ᵉ)
          ( λ eBᵉ →
            left-coherence-equiv-double-arrowᵉ eAᵉ eBᵉ ×ᵉ
            right-coherence-equiv-double-arrowᵉ eAᵉ eBᵉ))
```

### Components of an equivalence of double arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (a'ᵉ : double-arrowᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-double-arrowᵉ aᵉ a'ᵉ)
  where

  domain-equiv-equiv-double-arrowᵉ :
    domain-double-arrowᵉ aᵉ ≃ᵉ domain-double-arrowᵉ a'ᵉ
  domain-equiv-equiv-double-arrowᵉ = pr1ᵉ eᵉ

  domain-map-equiv-double-arrowᵉ :
    domain-double-arrowᵉ aᵉ → domain-double-arrowᵉ a'ᵉ
  domain-map-equiv-double-arrowᵉ = map-equivᵉ domain-equiv-equiv-double-arrowᵉ

  is-equiv-domain-map-equiv-double-arrowᵉ :
    is-equivᵉ domain-map-equiv-double-arrowᵉ
  is-equiv-domain-map-equiv-double-arrowᵉ =
    is-equiv-map-equivᵉ domain-equiv-equiv-double-arrowᵉ

  codomain-equiv-equiv-double-arrowᵉ :
    codomain-double-arrowᵉ aᵉ ≃ᵉ codomain-double-arrowᵉ a'ᵉ
  codomain-equiv-equiv-double-arrowᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  codomain-map-equiv-double-arrowᵉ :
    codomain-double-arrowᵉ aᵉ → codomain-double-arrowᵉ a'ᵉ
  codomain-map-equiv-double-arrowᵉ = map-equivᵉ codomain-equiv-equiv-double-arrowᵉ

  is-equiv-codomain-map-equiv-double-arrowᵉ :
    is-equivᵉ codomain-map-equiv-double-arrowᵉ
  is-equiv-codomain-map-equiv-double-arrowᵉ =
    is-equiv-map-equivᵉ codomain-equiv-equiv-double-arrowᵉ

  left-square-equiv-double-arrowᵉ :
    left-coherence-equiv-double-arrowᵉ aᵉ a'ᵉ
      ( domain-equiv-equiv-double-arrowᵉ)
      ( codomain-equiv-equiv-double-arrowᵉ)
  left-square-equiv-double-arrowᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ eᵉ))

  left-equiv-arrow-equiv-double-arrowᵉ :
    equiv-arrowᵉ (left-map-double-arrowᵉ aᵉ) (left-map-double-arrowᵉ a'ᵉ)
  pr1ᵉ left-equiv-arrow-equiv-double-arrowᵉ =
    domain-equiv-equiv-double-arrowᵉ
  pr1ᵉ (pr2ᵉ left-equiv-arrow-equiv-double-arrowᵉ) =
    codomain-equiv-equiv-double-arrowᵉ
  pr2ᵉ (pr2ᵉ left-equiv-arrow-equiv-double-arrowᵉ) =
    left-square-equiv-double-arrowᵉ

  right-square-equiv-double-arrowᵉ :
    right-coherence-equiv-double-arrowᵉ aᵉ a'ᵉ
      ( domain-equiv-equiv-double-arrowᵉ)
      ( codomain-equiv-equiv-double-arrowᵉ)
  right-square-equiv-double-arrowᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ eᵉ))

  right-equiv-arrow-equiv-double-arrowᵉ :
    equiv-arrowᵉ (right-map-double-arrowᵉ aᵉ) (right-map-double-arrowᵉ a'ᵉ)
  pr1ᵉ right-equiv-arrow-equiv-double-arrowᵉ =
    domain-equiv-equiv-double-arrowᵉ
  pr1ᵉ (pr2ᵉ right-equiv-arrow-equiv-double-arrowᵉ) =
    codomain-equiv-equiv-double-arrowᵉ
  pr2ᵉ (pr2ᵉ right-equiv-arrow-equiv-double-arrowᵉ) =
    right-square-equiv-double-arrowᵉ

  hom-equiv-double-arrowᵉ : hom-double-arrowᵉ aᵉ a'ᵉ
  pr1ᵉ hom-equiv-double-arrowᵉ =
    domain-map-equiv-double-arrowᵉ
  pr1ᵉ (pr2ᵉ hom-equiv-double-arrowᵉ) =
    codomain-map-equiv-double-arrowᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ hom-equiv-double-arrowᵉ)) =
    left-square-equiv-double-arrowᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ hom-equiv-double-arrowᵉ)) =
    right-square-equiv-double-arrowᵉ
```

### Equivalences of double arrows induced by morphisms of double arrows whose maps are equivalences

Givenᵉ aᵉ [morphismᵉ ofᵉ doubleᵉ arrows](foundation.morphisms-double-arrows.mdᵉ)

```text
           iᵉ                   iᵉ
     Aᵉ -------->ᵉ Xᵉ       Aᵉ -------->ᵉ Xᵉ
     |           |       |           |
   fᵉ |           | hᵉ   gᵉ |           | kᵉ
     |           |       |           |
     ∨ᵉ           ∨ᵉ       ∨ᵉ           ∨ᵉ
     Bᵉ -------->ᵉ Yᵉ       Bᵉ -------->ᵉ Yᵉ ,ᵉ
           jᵉ                   jᵉ
```

itᵉ sufficesᵉ to showᵉ thatᵉ `i`ᵉ andᵉ `j`ᵉ areᵉ equivalencesᵉ to obtainᵉ anᵉ equivalenceᵉ
ofᵉ doubleᵉ arrows.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (a'ᵉ : double-arrowᵉ l3ᵉ l4ᵉ)
  where

  equiv-hom-double-arrowᵉ :
    (hᵉ : hom-double-arrowᵉ aᵉ a'ᵉ) →
    is-equivᵉ (domain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ) →
    is-equivᵉ (codomain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ) →
    equiv-double-arrowᵉ aᵉ a'ᵉ
  pr1ᵉ (equiv-hom-double-arrowᵉ hᵉ is-equiv-domᵉ _) =
    (domain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ ,ᵉ is-equiv-domᵉ)
  pr1ᵉ (pr2ᵉ (equiv-hom-double-arrowᵉ hᵉ _ is-equiv-codᵉ)) =
    codomain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ ,ᵉ is-equiv-codᵉ
  pr2ᵉ (pr2ᵉ (equiv-hom-double-arrowᵉ hᵉ _ _)) =
    (left-square-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ ,ᵉ right-square-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)
```

### The identity equivalence of double arrows

```agda
module _
  {l1ᵉ l2ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ)
  where

  id-equiv-double-arrowᵉ : equiv-double-arrowᵉ aᵉ aᵉ
  pr1ᵉ id-equiv-double-arrowᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-double-arrowᵉ) = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-double-arrowᵉ) = (refl-htpyᵉ ,ᵉ refl-htpyᵉ)
```

### Composition of equivalences of double arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (bᵉ : double-arrowᵉ l3ᵉ l4ᵉ) (cᵉ : double-arrowᵉ l5ᵉ l6ᵉ)
  (fᵉ : equiv-double-arrowᵉ bᵉ cᵉ) (eᵉ : equiv-double-arrowᵉ aᵉ bᵉ)
  where

  comp-equiv-double-arrowᵉ : equiv-double-arrowᵉ aᵉ cᵉ
  comp-equiv-double-arrowᵉ =
    equiv-hom-double-arrowᵉ aᵉ cᵉ
      ( comp-hom-double-arrowᵉ aᵉ bᵉ cᵉ
        ( hom-equiv-double-arrowᵉ bᵉ cᵉ fᵉ)
        ( hom-equiv-double-arrowᵉ aᵉ bᵉ eᵉ))
      ( is-equiv-compᵉ _ _
        ( is-equiv-domain-map-equiv-double-arrowᵉ aᵉ bᵉ eᵉ)
        ( is-equiv-domain-map-equiv-double-arrowᵉ bᵉ cᵉ fᵉ))
      ( is-equiv-compᵉ _ _
        ( is-equiv-codomain-map-equiv-double-arrowᵉ aᵉ bᵉ eᵉ)
        ( is-equiv-codomain-map-equiv-double-arrowᵉ bᵉ cᵉ fᵉ))

  domain-equiv-comp-equiv-double-arrowᵉ :
    domain-double-arrowᵉ aᵉ ≃ᵉ domain-double-arrowᵉ cᵉ
  domain-equiv-comp-equiv-double-arrowᵉ =
    domain-equiv-equiv-double-arrowᵉ aᵉ cᵉ comp-equiv-double-arrowᵉ

  codomain-equiv-comp-equiv-double-arrowᵉ :
    codomain-double-arrowᵉ aᵉ ≃ᵉ codomain-double-arrowᵉ cᵉ
  codomain-equiv-comp-equiv-double-arrowᵉ =
    codomain-equiv-equiv-double-arrowᵉ aᵉ cᵉ comp-equiv-double-arrowᵉ

  left-square-comp-equiv-double-arrowᵉ :
    left-coherence-equiv-double-arrowᵉ aᵉ cᵉ
      ( domain-equiv-comp-equiv-double-arrowᵉ)
      ( codomain-equiv-comp-equiv-double-arrowᵉ)
  left-square-comp-equiv-double-arrowᵉ =
    left-square-equiv-double-arrowᵉ aᵉ cᵉ comp-equiv-double-arrowᵉ

  right-square-comp-equiv-double-arrowᵉ :
    right-coherence-equiv-double-arrowᵉ aᵉ cᵉ
      ( domain-equiv-comp-equiv-double-arrowᵉ)
      ( codomain-equiv-comp-equiv-double-arrowᵉ)
  right-square-comp-equiv-double-arrowᵉ =
    right-square-equiv-double-arrowᵉ aᵉ cᵉ comp-equiv-double-arrowᵉ
```
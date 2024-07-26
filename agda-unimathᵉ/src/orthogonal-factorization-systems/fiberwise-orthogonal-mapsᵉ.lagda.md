# Fiberwise orthogonal maps

```agda
module orthogonal-factorization-systems.fiberwise-orthogonal-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-morphisms-arrowsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.coproducts-pullbacksᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-products-pullbacksᵉ
open import foundation.dependent-sums-pullbacksᵉ
open import foundation.equivalencesᵉ
open import foundation.fibered-mapsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.postcomposition-pullbacksᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.products-pullbacksᵉ
open import foundation.propositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-cartesian-product-typesᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universal-property-pullbacksᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import orthogonal-factorization-systems.lifting-structures-on-squaresᵉ
open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.null-mapsᵉ
open import orthogonal-factorization-systems.orthogonal-mapsᵉ
open import orthogonal-factorization-systems.pullback-homᵉ
```

</details>

## Idea

Theᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "fiberwiseᵉ leftᵉ orthogonal"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ Agda=is-fiberwise-orthogonal-pullback-conditionᵉ}}
to `gᵉ : Xᵉ → Y`ᵉ ifᵉ everyᵉ [baseᵉ change](foundation.cartesian-morphisms-arrows.mdᵉ)
ofᵉ `f`ᵉ isᵉ [leftᵉ orthogonal](orthogonal-factorization-systems.mdᵉ) to `g`.ᵉ

Moreᵉ concretely,ᵉ `f`ᵉ _isᵉ fiberwiseᵉ leftᵉ orthogonalᵉ toᵉ_ `g`ᵉ ifᵉ forᵉ everyᵉ
[pullback](foundation-core.pullbacks.mdᵉ) squareᵉ

```text
    A'ᵉ ------->ᵉ Aᵉ
    | ⌟ᵉ         |
  f'|ᵉ           | fᵉ
    ∨ᵉ           ∨ᵉ
    B'ᵉ ------->ᵉ B,ᵉ
```

theᵉ exponentialᵉ squareᵉ

```text
             -ᵉ ∘ᵉ f'ᵉ
     B'ᵉ → Xᵉ ------->ᵉ A'ᵉ → Xᵉ
        |               |
  gᵉ ∘ᵉ -ᵉ |               | gᵉ ∘ᵉ -ᵉ
        ∨ᵉ               ∨ᵉ
     B'ᵉ → Yᵉ ------->ᵉ A'ᵉ → Yᵉ
             -ᵉ ∘ᵉ f'ᵉ
```

isᵉ alsoᵉ aᵉ pullback.ᵉ

## Definitions

### The pullback condition for fiberwise orthogonal maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-fiberwise-orthogonal-pullback-conditionᵉ : UUωᵉ
  is-fiberwise-orthogonal-pullback-conditionᵉ =
    {l5ᵉ l6ᵉ : Level} {A'ᵉ : UUᵉ l5ᵉ} {B'ᵉ : UUᵉ l6ᵉ}
    (f'ᵉ : A'ᵉ → B'ᵉ) (αᵉ : cartesian-hom-arrowᵉ f'ᵉ fᵉ) →
    is-orthogonal-pullback-conditionᵉ f'ᵉ gᵉ
```

### The universal property of fiberwise orthogonal maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  universal-property-fiberwise-orthogonal-mapsᵉ : UUωᵉ
  universal-property-fiberwise-orthogonal-mapsᵉ =
    {l5ᵉ l6ᵉ : Level} {A'ᵉ : UUᵉ l5ᵉ} {B'ᵉ : UUᵉ l6ᵉ}
    (f'ᵉ : A'ᵉ → B'ᵉ) (αᵉ : cartesian-hom-arrowᵉ f'ᵉ fᵉ) →
    universal-property-orthogonal-mapsᵉ f'ᵉ gᵉ
```

## Properties

### The pullback condition for fiberwise orthogonal maps is equivalent to the universal property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  universal-property-fiberwise-orthogonal-maps-is-fiberwise-orthogonal-pullback-conditionᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    universal-property-fiberwise-orthogonal-mapsᵉ fᵉ gᵉ
  universal-property-fiberwise-orthogonal-maps-is-fiberwise-orthogonal-pullback-conditionᵉ
    Hᵉ {A'ᵉ = A'ᵉ} f'ᵉ αᵉ =
    universal-property-pullback-is-pullbackᵉ
      ( precompᵉ f'ᵉ Yᵉ)
      ( postcompᵉ A'ᵉ gᵉ)
      ( cone-pullback-homᵉ f'ᵉ gᵉ)
      ( Hᵉ f'ᵉ αᵉ)

  is-fiberwise-orthogonal-pullback-condition-universal-property-fiberwise-orthogonal-mapsᵉ :
    universal-property-fiberwise-orthogonal-mapsᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-fiberwise-orthogonal-pullback-condition-universal-property-fiberwise-orthogonal-mapsᵉ
    Hᵉ {A'ᵉ = A'ᵉ} f'ᵉ αᵉ =
    is-pullback-universal-property-pullbackᵉ
      ( precompᵉ f'ᵉ Yᵉ)
      ( postcompᵉ A'ᵉ gᵉ)
      ( cone-pullback-homᵉ f'ᵉ gᵉ)
      ( Hᵉ f'ᵉ αᵉ)
```

### Fiberwise orthogonal maps are orthogonal

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-is-fiberwise-orthogonal-pullback-conditionᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-orthogonal-pullback-condition-is-fiberwise-orthogonal-pullback-conditionᵉ
    Hᵉ =
    Hᵉ fᵉ id-cartesian-hom-arrowᵉ
```

### Fiberwise orthogonality is preserved by homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  is-fiberwise-orthogonal-pullback-condition-htpy-leftᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (F'ᵉ : f'ᵉ ~ᵉ fᵉ) (gᵉ : Xᵉ → Yᵉ) →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ f'ᵉ gᵉ
  is-fiberwise-orthogonal-pullback-condition-htpy-leftᵉ F'ᵉ gᵉ Hᵉ f''ᵉ αᵉ =
    Hᵉ f''ᵉ (cartesian-hom-arrow-htpyᵉ refl-htpyᵉ F'ᵉ αᵉ)

  is-fiberwise-orthogonal-pullback-condition-htpy-rightᵉ :
    (fᵉ : Aᵉ → Bᵉ) {gᵉ g'ᵉ : Xᵉ → Yᵉ} (Gᵉ : gᵉ ~ᵉ g'ᵉ) →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ g'ᵉ
  is-fiberwise-orthogonal-pullback-condition-htpy-rightᵉ fᵉ {gᵉ} Gᵉ Hᵉ f''ᵉ αᵉ =
    is-orthogonal-pullback-condition-htpy-rightᵉ f''ᵉ gᵉ Gᵉ (Hᵉ f''ᵉ αᵉ)

  is-fiberwise-orthogonal-pullback-condition-htpyᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (F'ᵉ : f'ᵉ ~ᵉ fᵉ) {gᵉ g'ᵉ : Xᵉ → Yᵉ} (Gᵉ : gᵉ ~ᵉ g'ᵉ) →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ f'ᵉ g'ᵉ
  is-fiberwise-orthogonal-pullback-condition-htpyᵉ {fᵉ} {f'ᵉ} F'ᵉ {gᵉ} Gᵉ Hᵉ =
    is-fiberwise-orthogonal-pullback-condition-htpy-rightᵉ f'ᵉ Gᵉ
      ( is-fiberwise-orthogonal-pullback-condition-htpy-leftᵉ F'ᵉ gᵉ Hᵉ)
```

### Equivalences are fiberwise left and right orthogonal to every map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-is-equiv-leftᵉ :
    is-equivᵉ fᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-fiberwise-orthogonal-pullback-condition-is-equiv-leftᵉ Fᵉ f'ᵉ αᵉ =
    is-orthogonal-pullback-condition-is-equiv-leftᵉ f'ᵉ gᵉ
      ( is-equiv-source-is-equiv-target-cartesian-hom-arrowᵉ f'ᵉ fᵉ αᵉ Fᵉ)

  is-fiberwise-orthogonal-pullback-condition-is-equiv-rightᵉ :
    is-equivᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-fiberwise-orthogonal-pullback-condition-is-equiv-rightᵉ Gᵉ f'ᵉ _ =
    is-orthogonal-pullback-condition-is-equiv-rightᵉ f'ᵉ gᵉ Gᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ ≃ᵉ Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-equiv-leftᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ (map-equivᵉ fᵉ) gᵉ
  is-fiberwise-orthogonal-pullback-condition-equiv-leftᵉ =
    is-fiberwise-orthogonal-pullback-condition-is-equiv-leftᵉ
      ( map-equivᵉ fᵉ)
      ( gᵉ)
      ( is-equiv-map-equivᵉ fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ ≃ᵉ Yᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-equiv-rightᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ (map-equivᵉ gᵉ)
  is-fiberwise-orthogonal-pullback-condition-equiv-rightᵉ =
    is-fiberwise-orthogonal-pullback-condition-is-equiv-rightᵉ
      ( fᵉ)
      ( map-equivᵉ gᵉ)
      ( is-equiv-map-equivᵉ gᵉ)
```

### If `g` is fiberwise right orthogonal to `f` then it is null at the fibers of `f`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-null-map-fibers-is-fiberwise-orthogonal-pullback-conditionᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    (yᵉ : Bᵉ) → is-null-mapᵉ (fiberᵉ fᵉ yᵉ) gᵉ
  is-null-map-fibers-is-fiberwise-orthogonal-pullback-conditionᵉ Hᵉ yᵉ =
    is-null-map-is-orthogonal-pullback-condition-terminal-mapᵉ
      ( fiberᵉ fᵉ yᵉ)
      ( gᵉ)
      ( Hᵉ (terminal-mapᵉ (fiberᵉ fᵉ yᵉ)) (fiber-cartesian-hom-arrowᵉ fᵉ yᵉ))
```

### Closure properties of right fiberwise orthogonal maps

#### The right class is closed under composition and left cancellation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Zᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Yᵉ → Zᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-right-compᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ hᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ (hᵉ ∘ᵉ gᵉ)
  is-fiberwise-orthogonal-pullback-condition-right-compᵉ Hᵉ Gᵉ f'ᵉ αᵉ =
    is-orthogonal-pullback-condition-right-compᵉ f'ᵉ gᵉ hᵉ (Hᵉ f'ᵉ αᵉ) (Gᵉ f'ᵉ αᵉ)

  is-fiberwise-orthogonal-pullback-condition-right-right-factorᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ hᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ (hᵉ ∘ᵉ gᵉ) →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-fiberwise-orthogonal-pullback-condition-right-right-factorᵉ Hᵉ HGᵉ f'ᵉ αᵉ =
    is-orthogonal-pullback-condition-right-right-factorᵉ f'ᵉ gᵉ hᵉ
      ( Hᵉ f'ᵉ αᵉ)
      ( HGᵉ f'ᵉ αᵉ)
```

#### The right class is closed under dependent products

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : Iᵉ → UUᵉ l4ᵉ} {Yᵉ : Iᵉ → UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : (iᵉ : Iᵉ) → Xᵉ iᵉ → Yᵉ iᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-right-Πᵉ :
    ((iᵉ : Iᵉ) → is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ (gᵉ iᵉ)) →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ (map-Πᵉ gᵉ)
  is-fiberwise-orthogonal-pullback-condition-right-Πᵉ Gᵉ f'ᵉ αᵉ =
    is-orthogonal-pullback-condition-right-Πᵉ f'ᵉ gᵉ (λ iᵉ → Gᵉ iᵉ f'ᵉ αᵉ)
```

#### The right class is closed under exponentiation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (Sᵉ : UUᵉ l5ᵉ)
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-right-postcompᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ (postcompᵉ Sᵉ gᵉ)
  is-fiberwise-orthogonal-pullback-condition-right-postcompᵉ Gᵉ f'ᵉ αᵉ =
    is-orthogonal-pullback-condition-right-postcompᵉ Sᵉ f'ᵉ gᵉ (Gᵉ f'ᵉ αᵉ)
```

#### The right class is closed under cartesian products

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {X'ᵉ : UUᵉ l5ᵉ} {Y'ᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (g'ᵉ : X'ᵉ → Y'ᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-right-productᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ g'ᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ (map-productᵉ gᵉ g'ᵉ)
  is-fiberwise-orthogonal-pullback-condition-right-productᵉ Gᵉ G'ᵉ f'ᵉ αᵉ =
    is-orthogonal-pullback-condition-right-productᵉ f'ᵉ gᵉ g'ᵉ (Gᵉ f'ᵉ αᵉ) (G'ᵉ f'ᵉ αᵉ)
```

#### The right class is closed under base change

Givenᵉ aᵉ baseᵉ changeᵉ ofᵉ `g`ᵉ

```text
    X'ᵉ ----->ᵉ Xᵉ
    | ⌟ᵉ       |
  g'|ᵉ         | gᵉ
    ∨ᵉ         ∨ᵉ
    Y'ᵉ ----->ᵉ Y,ᵉ
```

ifᵉ `g`ᵉ isᵉ fiberwiseᵉ rightᵉ orthogonalᵉ to `f`,ᵉ thenᵉ `g'`ᵉ isᵉ fiberwiseᵉ rightᵉ
orthogonalᵉ to `f`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {X'ᵉ : UUᵉ l5ᵉ} {Y'ᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (g'ᵉ : X'ᵉ → Y'ᵉ) (βᵉ : cartesian-hom-arrowᵉ g'ᵉ gᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-right-base-changeᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ g'ᵉ
  is-fiberwise-orthogonal-pullback-condition-right-base-changeᵉ Gᵉ f'ᵉ αᵉ =
    is-orthogonal-pullback-condition-right-base-changeᵉ f'ᵉ gᵉ g'ᵉ βᵉ (Gᵉ f'ᵉ αᵉ)
```

### Closure properties of left fiberwise orthogonal maps

#### The left class is closed under composition and have the right cancellation property

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

#### The left class is closed under coproducts

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

#### The left class is preserved under base change

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {A'ᵉ : UUᵉ l5ᵉ} {B'ᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (f'ᵉ : A'ᵉ → B'ᵉ) (αᵉ : cartesian-hom-arrowᵉ f'ᵉ fᵉ)
  where

  is-fiberwise-orthogonal-pullback-condition-left-base-changeᵉ :
    is-fiberwise-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-fiberwise-orthogonal-pullback-conditionᵉ f'ᵉ gᵉ
  is-fiberwise-orthogonal-pullback-condition-left-base-changeᵉ Hᵉ f''ᵉ α'ᵉ =
    Hᵉ f''ᵉ (comp-cartesian-hom-arrowᵉ f''ᵉ f'ᵉ fᵉ αᵉ α'ᵉ)
```

#### The left class is closed under cobase change

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

#### The left class is closed transfininte composition

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

#### The left class is closed under cartesian products

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

#### The left class is closed under taking image inclusions

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

## References

-ᵉ Reidᵉ Barton'sᵉ noteᵉ onᵉ _Internalᵉ cd-structuresᵉ_
  ([GitHubᵉ upload](https://github.com/UniMath/agda-unimath/files/13429800/cd1.pdfᵉ))
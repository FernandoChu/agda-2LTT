# Orthogonal maps

```agda
module orthogonal-factorization-systems.orthogonal-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-morphisms-arrowsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.composition-algebraᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.coproducts-pullbacksᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-products-pullbacksᵉ
open import foundation.dependent-sums-pullbacksᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.fibered-mapsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.postcomposition-pullbacksᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.products-pullbacksᵉ
open import foundation.propositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
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
open import orthogonal-factorization-systems.pullback-homᵉ
```

</details>

## Idea

Theᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "orthogonal"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ Agda=is-orthogonalᵉ}} to
`gᵉ : Xᵉ → Y`ᵉ ifᵉ anyᵉ ofᵉ theᵉ followingᵉ equivalentᵉ definitionsᵉ holdᵉ

1.ᵉ Theirᵉ [pullback-hom](orthogonal-factorization-systems.pullback-hom.mdᵉ) isᵉ anᵉ
   equivalence.ᵉ

2.ᵉ Thereᵉ isᵉ aᵉ [unique](foundation-core.contractible-types.mdᵉ)
   [liftingᵉ operation](orthogonal-factorization-systems.lifting-operations.mdᵉ)
   betweenᵉ `f`ᵉ andᵉ `g`.ᵉ

3.ᵉ Theᵉ followingᵉ isᵉ aᵉ [pullback](foundation-core.pullbacks.mdᵉ) squareᵉ:

   ```text
                -ᵉ ∘ᵉ fᵉ
         Bᵉ → Xᵉ ------->ᵉ Aᵉ → Xᵉ
           |              |
     gᵉ ∘ᵉ -ᵉ |              | gᵉ ∘ᵉ -ᵉ
           ∨ᵉ              ∨ᵉ
         Bᵉ → Yᵉ ------->ᵉ Aᵉ → Y.ᵉ
                -ᵉ ∘ᵉ fᵉ
   ```

4.ᵉ Theᵉ inducedᵉ dependentᵉ precompositionᵉ mapᵉ

   ```text
     -ᵉ ∘ᵉ fᵉ : ((xᵉ : Bᵉ) → fiberᵉ gᵉ (hᵉ xᵉ)) -->ᵉ ((xᵉ : Aᵉ) → fiberᵉ gᵉ (hᵉ (fᵉ xᵉ)))
   ```

   isᵉ anᵉ equivalenceᵉ forᵉ everyᵉ `hᵉ : Bᵉ → Y`.ᵉ

Ifᵉ `f`ᵉ isᵉ orthogonalᵉ to `g`,ᵉ weᵉ sayᵉ thatᵉ `f`ᵉ isᵉ
{{#conceptᵉ "leftᵉ orthogonal"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ Agda=is-left-orthogonalᵉ}}
to `g`,ᵉ andᵉ `g`ᵉ isᵉ
{{#conceptᵉ "rightᵉ orthogonal"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ Agda=is-right-orthogonalᵉ}}
to `f`,ᵉ andᵉ mayᵉ writeᵉ `fᵉ ⊥ᵉ g`.ᵉ

## Definitions

### The orthogonality predicate

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonalᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-orthogonalᵉ = is-equivᵉ (pullback-homᵉ fᵉ gᵉ)

  _⊥ᵉ_ = is-orthogonalᵉ

  is-prop-is-orthogonalᵉ : is-propᵉ is-orthogonalᵉ
  is-prop-is-orthogonalᵉ = is-property-is-equivᵉ (pullback-homᵉ fᵉ gᵉ)

  is-orthogonal-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-orthogonal-Propᵉ = is-orthogonalᵉ
  pr2ᵉ is-orthogonal-Propᵉ = is-prop-is-orthogonalᵉ
```

Aᵉ termᵉ ofᵉ `is-right-orthogonalᵉ fᵉ g`ᵉ assertsᵉ thatᵉ `g`ᵉ isᵉ rightᵉ orthogonalᵉ to `f`.ᵉ

```agda
  is-right-orthogonalᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-right-orthogonalᵉ = is-orthogonalᵉ
```

Aᵉ termᵉ ofᵉ `is-left-orthogonalᵉ fᵉ g`ᵉ assertsᵉ thatᵉ `g`ᵉ isᵉ leftᵉ orthogonalᵉ to `f`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-left-orthogonalᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-left-orthogonalᵉ = is-orthogonalᵉ gᵉ fᵉ
```

### The pullback condition for orthogonal maps

Theᵉ mapsᵉ `f`ᵉ andᵉ `g`ᵉ areᵉ orthogonalᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ squareᵉ

```text
             -ᵉ ∘ᵉ fᵉ
      Bᵉ → Xᵉ ------->ᵉ Aᵉ → Xᵉ
        |              |
  gᵉ ∘ᵉ -ᵉ |              | gᵉ ∘ᵉ -ᵉ
        ∨ᵉ              ∨ᵉ
      Bᵉ → Yᵉ ------->ᵉ Aᵉ → Y.ᵉ
             -ᵉ ∘ᵉ fᵉ
```

isᵉ aᵉ pullback.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-conditionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-orthogonal-pullback-conditionᵉ =
    is-pullbackᵉ (precompᵉ fᵉ Yᵉ) (postcompᵉ Aᵉ gᵉ) (cone-pullback-homᵉ fᵉ gᵉ)

  is-orthogonal-pullback-condition-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-orthogonal-pullback-condition-Propᵉ =
    is-pullback-Propᵉ (precompᵉ fᵉ Yᵉ) (postcompᵉ Aᵉ gᵉ) (cone-pullback-homᵉ fᵉ gᵉ)

  is-prop-is-orthogonal-pullback-conditionᵉ :
    is-propᵉ is-orthogonal-pullback-conditionᵉ
  is-prop-is-orthogonal-pullback-conditionᵉ =
    is-prop-is-pullbackᵉ (precompᵉ fᵉ Yᵉ) (postcompᵉ Aᵉ gᵉ) (cone-pullback-homᵉ fᵉ gᵉ)
```

### The universal property of orthogonal pairs of maps

Theᵉ universalᵉ propertyᵉ ofᵉ orthogonalᵉ mapsᵉ isᵉ theᵉ universalᵉ propertyᵉ associatedᵉ
to theᵉ pullbackᵉ condition,ᵉ which,ᵉ asᵉ opposedᵉ to theᵉ pullbackᵉ conditionᵉ itself,ᵉ
isᵉ aᵉ largeᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  universal-property-orthogonal-mapsᵉ : UUωᵉ
  universal-property-orthogonal-mapsᵉ =
    universal-property-pullbackᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
```

### The fiber condition for orthogonal maps

Theᵉ mapsᵉ `f`ᵉ andᵉ `g`ᵉ areᵉ orthogonalᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ inducedᵉ familyᵉ ofᵉ mapsᵉ onᵉ
fibersᵉ

```text
                           (-ᵉ ∘ᵉ fᵉ)
   ((xᵉ : Bᵉ) → fiberᵉ gᵉ (hᵉ xᵉ)) -->ᵉ ((xᵉ : Aᵉ) → fiberᵉ gᵉ (hᵉ (fᵉ xᵉ)))
                      |               |
                      |               |
                      ∨ᵉ    (-ᵉ ∘ᵉ fᵉ)    ∨ᵉ
                   (Bᵉ → Xᵉ) ------>ᵉ (Aᵉ → Xᵉ)
                      |               |
              (gᵉ ∘ᵉ -ᵉ) |               | (gᵉ ∘ᵉ -ᵉ)
                      ∨ᵉ    (-ᵉ ∘ᵉ fᵉ)    ∨ᵉ
               hᵉ ∈ᵉ (Bᵉ → Yᵉ) ------>ᵉ (Aᵉ → Yᵉ)
```

isᵉ anᵉ equivalenceᵉ forᵉ everyᵉ `hᵉ : Bᵉ → Y`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-fiber-condition-right-mapᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-orthogonal-fiber-condition-right-mapᵉ =
    (hᵉ : Bᵉ → Yᵉ) → is-equivᵉ (precomp-Πᵉ fᵉ (fiberᵉ gᵉ ∘ᵉ hᵉ))
```

## Properties

### Being orthogonal means that the type of lifting squares is contractible

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  unique-lifting-structure-squares-is-orthogonalᵉ :
    is-orthogonalᵉ fᵉ gᵉ →
    (hᵉ : hom-arrowᵉ fᵉ gᵉ) →
    is-contrᵉ (lifting-structure-squareᵉ fᵉ gᵉ hᵉ)
  unique-lifting-structure-squares-is-orthogonalᵉ Hᵉ hᵉ =
    is-contr-equivᵉ
      ( fiberᵉ (pullback-homᵉ fᵉ gᵉ) hᵉ)
      ( compute-fiber-pullback-homᵉ fᵉ gᵉ hᵉ)
      ( is-contr-map-is-equivᵉ Hᵉ hᵉ)

  is-orthogonal-unique-lifting-structure-squaresᵉ :
    ( (hᵉ : hom-arrowᵉ fᵉ gᵉ) → is-contrᵉ (lifting-structure-squareᵉ fᵉ gᵉ hᵉ)) →
    is-orthogonalᵉ fᵉ gᵉ
  is-orthogonal-unique-lifting-structure-squaresᵉ Hᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ hᵉ →
        is-contr-equiv'ᵉ
          ( lifting-structure-squareᵉ fᵉ gᵉ hᵉ)
          ( compute-fiber-pullback-homᵉ fᵉ gᵉ hᵉ)
          ( Hᵉ hᵉ))
```

### Being orthogonal means satisfying the pullback condition of being orthogonal maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-is-orthogonalᵉ :
    is-orthogonalᵉ fᵉ gᵉ → is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-orthogonal-pullback-condition-is-orthogonalᵉ Hᵉ =
    is-equiv-left-map-triangleᵉ
      ( gap-pullback-homᵉ fᵉ gᵉ)
      ( map-compute-pullback-homᵉ fᵉ gᵉ)
      ( pullback-homᵉ fᵉ gᵉ)
      ( inv-htpyᵉ (triangle-pullback-homᵉ fᵉ gᵉ))
      ( Hᵉ)
      ( is-equiv-map-compute-pullback-homᵉ fᵉ gᵉ)

  is-orthogonal-is-orthogonal-pullback-conditionᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ → is-orthogonalᵉ fᵉ gᵉ
  is-orthogonal-is-orthogonal-pullback-conditionᵉ =
    is-equiv-top-map-triangleᵉ
      ( gap-pullback-homᵉ fᵉ gᵉ)
      ( map-compute-pullback-homᵉ fᵉ gᵉ)
      ( pullback-homᵉ fᵉ gᵉ)
      ( inv-htpyᵉ (triangle-pullback-homᵉ fᵉ gᵉ))
      ( is-equiv-map-compute-pullback-homᵉ fᵉ gᵉ)
```

### Being orthogonal means satisfying the universal property of being orthogonal

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  universal-property-orthogonal-maps-is-orthogonalᵉ :
    is-orthogonalᵉ fᵉ gᵉ → universal-property-orthogonal-mapsᵉ fᵉ gᵉ
  universal-property-orthogonal-maps-is-orthogonalᵉ Hᵉ =
    universal-property-pullback-is-pullbackᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Hᵉ)

  is-orthogonal-universal-property-orthogonal-mapsᵉ :
    universal-property-orthogonal-mapsᵉ fᵉ gᵉ → is-orthogonalᵉ fᵉ gᵉ
  is-orthogonal-universal-property-orthogonal-mapsᵉ Hᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
      ( is-pullback-universal-property-pullbackᵉ
        ( precompᵉ fᵉ Yᵉ)
        ( postcompᵉ Aᵉ gᵉ)
        ( cone-pullback-homᵉ fᵉ gᵉ)
        ( Hᵉ))
```

### Being orthogonal means satisfying the fiber condition for orthogonal maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-conditionᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-fiber-condition-right-mapᵉ fᵉ gᵉ
  is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-conditionᵉ Hᵉ hᵉ =
    is-equiv-source-is-equiv-target-equiv-arrowᵉ
      ( precomp-Πᵉ fᵉ (fiberᵉ gᵉ ∘ᵉ hᵉ))
      ( map-fiber-vertical-map-coneᵉ
        ( precompᵉ fᵉ Yᵉ)
        ( postcompᵉ Aᵉ gᵉ)
        ( cone-pullback-homᵉ fᵉ gᵉ)
        ( hᵉ))
      ( compute-map-fiber-vertical-pullback-homᵉ fᵉ gᵉ hᵉ)
      ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
        ( precompᵉ fᵉ Yᵉ)
        ( postcompᵉ Aᵉ gᵉ)
        ( cone-pullback-homᵉ fᵉ gᵉ)
        ( Hᵉ)
        ( hᵉ))

  is-orthogonal-fiber-condition-right-map-is-orthogonalᵉ :
    is-orthogonalᵉ fᵉ gᵉ →
    is-orthogonal-fiber-condition-right-mapᵉ fᵉ gᵉ
  is-orthogonal-fiber-condition-right-map-is-orthogonalᵉ Hᵉ =
    is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-conditionᵉ
      ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Hᵉ)

  is-orthogonal-pullback-condition-is-orthogonal-fiber-condition-right-mapᵉ :
    is-orthogonal-fiber-condition-right-mapᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-orthogonal-pullback-condition-is-orthogonal-fiber-condition-right-mapᵉ Hᵉ =
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( λ hᵉ →
        is-equiv-target-is-equiv-source-equiv-arrowᵉ
          ( precomp-Πᵉ fᵉ (fiberᵉ gᵉ ∘ᵉ hᵉ))
          ( map-fiber-vertical-map-coneᵉ
            ( precompᵉ fᵉ Yᵉ)
            ( postcompᵉ Aᵉ gᵉ)
            ( cone-pullback-homᵉ fᵉ gᵉ)
            ( hᵉ))
          ( compute-map-fiber-vertical-pullback-homᵉ fᵉ gᵉ hᵉ)
          ( Hᵉ hᵉ))

  is-orthogonal-is-orthogonal-fiber-condition-right-mapᵉ :
    is-orthogonal-fiber-condition-right-mapᵉ fᵉ gᵉ →
    is-orthogonalᵉ fᵉ gᵉ
  is-orthogonal-is-orthogonal-fiber-condition-right-mapᵉ Hᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
      ( is-orthogonal-pullback-condition-is-orthogonal-fiber-condition-right-mapᵉ
        ( Hᵉ))
```

### Orthogonality is preserved by homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-htpyᵉ :
    {f'ᵉ : Aᵉ → Bᵉ} {g'ᵉ : Xᵉ → Yᵉ} → fᵉ ~ᵉ f'ᵉ → gᵉ ~ᵉ g'ᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ f'ᵉ g'ᵉ
  is-orthogonal-pullback-condition-htpyᵉ Fᵉ Gᵉ =
    is-pullback-htpy'ᵉ
      ( htpy-precompᵉ Fᵉ Yᵉ)
      ( htpy-postcompᵉ Aᵉ Gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( ( htpy-postcompᵉ Bᵉ Gᵉ) ,ᵉ
        ( htpy-precompᵉ Fᵉ Xᵉ) ,ᵉ
        ( ( commutative-htpy-postcomp-htpy-precompᵉ Fᵉ Gᵉ) ∙hᵉ
          ( inv-htpy-right-unit-htpyᵉ)))

  is-orthogonal-pullback-condition-htpy-leftᵉ :
    {f'ᵉ : Aᵉ → Bᵉ} → fᵉ ~ᵉ f'ᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ f'ᵉ gᵉ
  is-orthogonal-pullback-condition-htpy-leftᵉ Fᵉ =
    is-orthogonal-pullback-condition-htpyᵉ Fᵉ refl-htpyᵉ

  is-orthogonal-pullback-condition-htpy-rightᵉ :
    {g'ᵉ : Xᵉ → Yᵉ} → gᵉ ~ᵉ g'ᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ g'ᵉ
  is-orthogonal-pullback-condition-htpy-rightᵉ =
    is-orthogonal-pullback-condition-htpyᵉ refl-htpyᵉ
```

### Equivalences are orthogonal to every map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-is-equiv-leftᵉ :
    is-equivᵉ fᵉ → is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-orthogonal-pullback-condition-is-equiv-leftᵉ is-equiv-fᵉ =
    is-pullback-is-equiv-horizontal-mapsᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( is-equiv-precomp-is-equivᵉ fᵉ is-equiv-fᵉ Yᵉ)
      ( is-equiv-precomp-is-equivᵉ fᵉ is-equiv-fᵉ Xᵉ)

  is-orthogonal-is-equiv-leftᵉ : is-equivᵉ fᵉ → is-orthogonalᵉ fᵉ gᵉ
  is-orthogonal-is-equiv-leftᵉ is-equiv-fᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
      ( is-orthogonal-pullback-condition-is-equiv-leftᵉ is-equiv-fᵉ)

  is-orthogonal-pullback-condition-is-equiv-rightᵉ :
    is-equivᵉ gᵉ → is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-orthogonal-pullback-condition-is-equiv-rightᵉ is-equiv-gᵉ =
    is-pullback-is-equiv-vertical-mapsᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( is-equiv-postcomp-is-equivᵉ gᵉ is-equiv-gᵉ Aᵉ)
      ( is-equiv-postcomp-is-equivᵉ gᵉ is-equiv-gᵉ Bᵉ)

  is-orthogonal-is-equiv-rightᵉ : is-equivᵉ gᵉ → is-orthogonalᵉ fᵉ gᵉ
  is-orthogonal-is-equiv-rightᵉ is-equiv-gᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
      ( is-orthogonal-pullback-condition-is-equiv-rightᵉ is-equiv-gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  is-orthogonal-pullback-condition-equiv-leftᵉ :
    (fᵉ : Aᵉ ≃ᵉ Bᵉ) (gᵉ : Xᵉ → Yᵉ) → is-orthogonal-pullback-conditionᵉ (map-equivᵉ fᵉ) gᵉ
  is-orthogonal-pullback-condition-equiv-leftᵉ fᵉ gᵉ =
    is-orthogonal-pullback-condition-is-equiv-leftᵉ
      ( map-equivᵉ fᵉ)
      ( gᵉ)
      ( is-equiv-map-equivᵉ fᵉ)

  is-orthogonal-equiv-leftᵉ :
    (fᵉ : Aᵉ ≃ᵉ Bᵉ) (gᵉ : Xᵉ → Yᵉ) → is-orthogonalᵉ (map-equivᵉ fᵉ) gᵉ
  is-orthogonal-equiv-leftᵉ fᵉ gᵉ =
    is-orthogonal-is-equiv-leftᵉ (map-equivᵉ fᵉ) gᵉ (is-equiv-map-equivᵉ fᵉ)

  is-orthogonal-pullback-condition-equiv-rightᵉ :
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ ≃ᵉ Yᵉ) → is-orthogonal-pullback-conditionᵉ fᵉ (map-equivᵉ gᵉ)
  is-orthogonal-pullback-condition-equiv-rightᵉ fᵉ gᵉ =
    is-orthogonal-pullback-condition-is-equiv-rightᵉ
      ( fᵉ)
      ( map-equivᵉ gᵉ)
      ( is-equiv-map-equivᵉ gᵉ)

  is-orthogonal-equiv-rightᵉ :
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ ≃ᵉ Yᵉ) → is-orthogonalᵉ fᵉ (map-equivᵉ gᵉ)
  is-orthogonal-equiv-rightᵉ fᵉ gᵉ =
    is-orthogonal-is-equiv-rightᵉ fᵉ (map-equivᵉ gᵉ) (is-equiv-map-equivᵉ gᵉ)
```

### Right orthogonal maps are closed under composition and have the left cancellation property

Givenᵉ twoᵉ composableᵉ mapsᵉ `h`ᵉ afterᵉ `g`,ᵉ ifᵉ `fᵉ ⊥ᵉ h`,ᵉ thenᵉ `fᵉ ⊥ᵉ g`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ
`fᵉ ⊥ᵉ (hᵉ ∘ᵉ g)`.ᵉ

**Proof:**ᵉ Byᵉ theᵉ pullbackᵉ conditionᵉ ofᵉ orthogonalᵉ maps,ᵉ theᵉ topᵉ squareᵉ in theᵉ
belowᵉ diagramᵉ isᵉ aᵉ pullbackᵉ preciselyᵉ whenᵉ `g`ᵉ isᵉ rightᵉ orthogonalᵉ to `f`ᵉ:

```text
             -ᵉ ∘ᵉ fᵉ
      Bᵉ → Xᵉ ------->ᵉ Aᵉ → Xᵉ
        |              |
  gᵉ ∘ᵉ -ᵉ |              | gᵉ ∘ᵉ -ᵉ
        ∨ᵉ              ∨ᵉ
      Bᵉ → Yᵉ ------->ᵉ Aᵉ → Yᵉ
        | ⌟ᵉ            |
  hᵉ ∘ᵉ -ᵉ |              | hᵉ ∘ᵉ -ᵉ
        ∨ᵉ              ∨ᵉ
      Bᵉ → Zᵉ ------->ᵉ Aᵉ → Z.ᵉ
             -ᵉ ∘ᵉ fᵉ
```

soᵉ theᵉ resultᵉ isᵉ anᵉ instance ofᵉ theᵉ verticalᵉ pastingᵉ propertyᵉ forᵉ pullbacks.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Zᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Yᵉ → Zᵉ)
  where

  is-orthogonal-pullback-condition-right-compᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ hᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ (hᵉ ∘ᵉ gᵉ)
  is-orthogonal-pullback-condition-right-compᵉ =
    is-pullback-rectangle-is-pullback-top-squareᵉ
      ( precompᵉ fᵉ Zᵉ)
      ( postcompᵉ Aᵉ hᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ hᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)

  up-orthogonal-right-compᵉ :
    universal-property-orthogonal-mapsᵉ fᵉ hᵉ →
    universal-property-orthogonal-mapsᵉ fᵉ gᵉ →
    universal-property-orthogonal-mapsᵉ fᵉ (hᵉ ∘ᵉ gᵉ)
  up-orthogonal-right-compᵉ =
    universal-property-pullback-rectangle-universal-property-pullback-topᵉ
      ( precompᵉ fᵉ Zᵉ)
      ( postcompᵉ Aᵉ hᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ hᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)

  is-orthogonal-right-compᵉ :
    is-orthogonalᵉ fᵉ hᵉ → is-orthogonalᵉ fᵉ gᵉ → is-orthogonalᵉ fᵉ (hᵉ ∘ᵉ gᵉ)
  is-orthogonal-right-compᵉ Hᵉ Gᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ (hᵉ ∘ᵉ gᵉ)
      ( is-orthogonal-pullback-condition-right-compᵉ
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ hᵉ Hᵉ)
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Gᵉ))

  is-orthogonal-pullback-condition-right-right-factorᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ hᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ (hᵉ ∘ᵉ gᵉ) →
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-orthogonal-pullback-condition-right-right-factorᵉ =
    is-pullback-top-square-is-pullback-rectangleᵉ
      ( precompᵉ fᵉ Zᵉ)
      ( postcompᵉ Aᵉ hᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ hᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)

  up-orthogonal-right-right-factorᵉ :
    universal-property-orthogonal-mapsᵉ fᵉ hᵉ →
    universal-property-orthogonal-mapsᵉ fᵉ (hᵉ ∘ᵉ gᵉ) →
    universal-property-orthogonal-mapsᵉ fᵉ gᵉ
  up-orthogonal-right-right-factorᵉ =
    universal-property-pullback-top-universal-property-pullback-rectangleᵉ
      ( precompᵉ fᵉ Zᵉ)
      ( postcompᵉ Aᵉ hᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ hᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)

  is-orthogonal-right-right-factorᵉ :
    is-orthogonalᵉ fᵉ hᵉ → is-orthogonalᵉ fᵉ (hᵉ ∘ᵉ gᵉ) → is-orthogonalᵉ fᵉ gᵉ
  is-orthogonal-right-right-factorᵉ Hᵉ HGᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
      ( is-orthogonal-pullback-condition-right-right-factorᵉ
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ hᵉ Hᵉ)
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ (hᵉ ∘ᵉ gᵉ) HGᵉ))
```

### Left orthogonal maps are closed under composition and have the right cancellation property

Givenᵉ twoᵉ composableᵉ mapsᵉ `h`ᵉ afterᵉ `f`,ᵉ ifᵉ `fᵉ ⊥ᵉ g`,ᵉ thenᵉ `hᵉ ⊥ᵉ g`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ
`(hᵉ ∘ᵉ fᵉ) ⊥ᵉ g`.ᵉ

**Proof:**ᵉ Byᵉ theᵉ universalᵉ propertyᵉ ofᵉ orthogonalᵉ maps,ᵉ theᵉ rightᵉ squareᵉ in theᵉ
belowᵉ diagramᵉ isᵉ aᵉ pullbackᵉ preciselyᵉ whenᵉ `f`ᵉ isᵉ leftᵉ orthogonalᵉ to `g`ᵉ:

```text
             -ᵉ ∘ᵉ hᵉ          -ᵉ ∘ᵉ fᵉ
      Cᵉ → Xᵉ ------->ᵉ Bᵉ → Xᵉ ------->ᵉ Aᵉ → Xᵉ
        |              | ⌟ᵉ            |
  gᵉ ∘ᵉ -ᵉ |              |              | gᵉ ∘ᵉ -ᵉ
        ∨ᵉ              ∨ᵉ              ∨ᵉ
      Cᵉ → Yᵉ ------->ᵉ Bᵉ → Yᵉ ------->ᵉ Aᵉ → Yᵉ
             -ᵉ ∘ᵉ hᵉ          -ᵉ ∘ᵉ fᵉ
```

soᵉ theᵉ resultᵉ isᵉ anᵉ instance ofᵉ theᵉ horizontalᵉ pastingᵉ propertyᵉ forᵉ pullbacks.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (hᵉ : Bᵉ → Cᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-left-compᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ hᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ (hᵉ ∘ᵉ fᵉ) gᵉ
  is-orthogonal-pullback-condition-left-compᵉ =
    is-pullback-rectangle-is-pullback-left-squareᵉ
      ( precompᵉ hᵉ Yᵉ)
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( cone-pullback-homᵉ hᵉ gᵉ)

  up-orthogonal-left-compᵉ :
    universal-property-orthogonal-mapsᵉ fᵉ gᵉ →
    universal-property-orthogonal-mapsᵉ hᵉ gᵉ →
    universal-property-orthogonal-mapsᵉ (hᵉ ∘ᵉ fᵉ) gᵉ
  up-orthogonal-left-compᵉ =
    universal-property-pullback-rectangle-universal-property-pullback-left-squareᵉ
      ( precompᵉ hᵉ Yᵉ)
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( cone-pullback-homᵉ hᵉ gᵉ)

  is-orthogonal-left-compᵉ :
    is-orthogonalᵉ fᵉ gᵉ → is-orthogonalᵉ hᵉ gᵉ → is-orthogonalᵉ (hᵉ ∘ᵉ fᵉ) gᵉ
  is-orthogonal-left-compᵉ Fᵉ Hᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ (hᵉ ∘ᵉ fᵉ) gᵉ
      ( is-orthogonal-pullback-condition-left-compᵉ
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Fᵉ)
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ hᵉ gᵉ Hᵉ))

  is-orthogonal-pullback-condition-left-left-factorᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ (hᵉ ∘ᵉ fᵉ) gᵉ →
    is-orthogonal-pullback-conditionᵉ hᵉ gᵉ
  is-orthogonal-pullback-condition-left-left-factorᵉ =
    is-pullback-left-square-is-pullback-rectangleᵉ
      ( precompᵉ hᵉ Yᵉ)
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( cone-pullback-homᵉ hᵉ gᵉ)

  up-orthogonal-left-left-factorᵉ :
    universal-property-orthogonal-mapsᵉ fᵉ gᵉ →
    universal-property-orthogonal-mapsᵉ (hᵉ ∘ᵉ fᵉ) gᵉ →
    universal-property-orthogonal-mapsᵉ hᵉ gᵉ
  up-orthogonal-left-left-factorᵉ =
    universal-property-pullback-left-square-universal-property-pullback-rectangleᵉ
      ( precompᵉ hᵉ Yᵉ)
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)
      ( cone-pullback-homᵉ hᵉ gᵉ)

  is-orthogonal-left-left-factorᵉ :
    is-orthogonalᵉ fᵉ gᵉ → is-orthogonalᵉ (hᵉ ∘ᵉ fᵉ) gᵉ → is-orthogonalᵉ hᵉ gᵉ
  is-orthogonal-left-left-factorᵉ Fᵉ HFᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ hᵉ gᵉ
      ( is-orthogonal-pullback-condition-left-left-factorᵉ
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Fᵉ)
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ (hᵉ ∘ᵉ fᵉ) gᵉ HFᵉ))
```

### Right orthogonality is preserved by dependent products

Ifᵉ `fᵉ ⊥ᵉ gᵢ`,ᵉ forᵉ eachᵉ `iᵉ : I`,ᵉ thenᵉ `fᵉ ⊥ᵉ (map-Πᵉ g)`.ᵉ

**Proof:**ᵉ Weᵉ needᵉ to showᵉ thatᵉ theᵉ squareᵉ

```text
                          -ᵉ ∘ᵉ fᵉ
         (Bᵉ → Πᵢᵉ Xᵢᵉ) --------------->ᵉ (Aᵉ → Πᵢᵉ Xᵢᵉ)
              |                           |
              |                           |
  map-Πᵉ gᵉ ∘ᵉ -ᵉ |                           | map-Πᵉ gᵉ ∘ᵉ -ᵉ
              |                           |
              ∨ᵉ                           ∨ᵉ
         (Bᵉ → Πᵢᵉ Yᵢᵉ) --------------->ᵉ (Aᵉ → Πᵢᵉ Yᵢᵉ)
                          -ᵉ ∘ᵉ fᵉ
```

isᵉ aᵉ pullback.ᵉ Byᵉ swappingᵉ theᵉ argumentsᵉ atᵉ eachᵉ vertex,ᵉ thisᵉ squareᵉ isᵉ
equivalentᵉ to

```text
                          map-Πᵉ (-ᵉ ∘ᵉ fᵉ)
            (Πᵢᵉ Bᵉ → Xᵢᵉ) --------------->ᵉ (Πᵢᵉ Aᵉ → Xᵢᵉ)
                  |                           |
                  |                           |
   map-Πᵉ (gᵢᵉ ∘ᵉ -ᵉ) |                           | map-Πᵉ (gᵢᵉ ∘ᵉ -ᵉ)
                  |                           |
                  ∨ᵉ                           ∨ᵉ
            (Πᵢᵉ Bᵉ → Yᵢᵉ) --------------->ᵉ (Πᵢᵉ Aᵉ → Yᵢᵉ)
                          map-Πᵉ (-ᵉ ∘ᵉ fᵉ)
```

whichᵉ isᵉ aᵉ pullbackᵉ byᵉ assumptionᵉ sinceᵉ pullbacksᵉ areᵉ preservedᵉ byᵉ dependentᵉ
products.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : Iᵉ → UUᵉ l4ᵉ} {Yᵉ : Iᵉ → UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : (iᵉ : Iᵉ) → Xᵉ iᵉ → Yᵉ iᵉ)
  where

  is-orthogonal-pullback-condition-right-Πᵉ :
    ((iᵉ : Iᵉ) → is-orthogonal-pullback-conditionᵉ fᵉ (gᵉ iᵉ)) →
    is-orthogonal-pullback-conditionᵉ fᵉ (map-Πᵉ gᵉ)
  is-orthogonal-pullback-condition-right-Πᵉ Gᵉ =
    is-pullback-bottom-is-pullback-top-cube-is-equivᵉ
      ( postcompᵉ Bᵉ (map-Πᵉ gᵉ))
      ( precompᵉ fᵉ ((iᵉ : Iᵉ) → Xᵉ iᵉ))
      ( precompᵉ fᵉ ((iᵉ : Iᵉ) → Yᵉ iᵉ))
      ( postcompᵉ Aᵉ (map-Πᵉ gᵉ))
      ( map-Πᵉ (λ iᵉ → postcompᵉ Bᵉ (gᵉ iᵉ)))
      ( map-Πᵉ (λ iᵉ → precompᵉ fᵉ (Xᵉ iᵉ)))
      ( map-Πᵉ (λ iᵉ → precompᵉ fᵉ (Yᵉ iᵉ)))
      ( map-Πᵉ (λ iᵉ → postcompᵉ Aᵉ (gᵉ iᵉ)))
      ( swap-Πᵉ)
      ( swap-Πᵉ)
      ( swap-Πᵉ)
      ( swap-Πᵉ)
      ( λ _ → eq-htpyᵉ refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( ( apᵉ swap-Πᵉ) ·lᵉ
        ( eq-htpy-refl-htpyᵉ ∘ᵉ map-Πᵉ (λ iᵉ → precompᵉ fᵉ (Yᵉ iᵉ) ∘ᵉ postcompᵉ Bᵉ (gᵉ iᵉ))))
      ( is-equiv-swap-Πᵉ)
      ( is-equiv-swap-Πᵉ)
      ( is-equiv-swap-Πᵉ)
      ( is-equiv-swap-Πᵉ)
      ( is-pullback-Πᵉ
        ( λ iᵉ → precompᵉ fᵉ (Yᵉ iᵉ))
        ( λ iᵉ → postcompᵉ Aᵉ (gᵉ iᵉ))
        ( λ iᵉ → cone-pullback-homᵉ fᵉ (gᵉ iᵉ))
        ( Gᵉ))

  is-orthogonal-right-Πᵉ :
    ((iᵉ : Iᵉ) → is-orthogonalᵉ fᵉ (gᵉ iᵉ)) → is-orthogonalᵉ fᵉ (map-Πᵉ gᵉ)
  is-orthogonal-right-Πᵉ Gᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ (map-Πᵉ gᵉ)
      ( is-orthogonal-pullback-condition-right-Πᵉ
        ( λ iᵉ → is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ (gᵉ iᵉ) (Gᵉ iᵉ)))
```

### Any map that is left orthogonal to a map `g` is also left orthogonal to postcomposing by `g`

Ifᵉ `fᵉ ⊥ᵉ g`ᵉ thenᵉ `fᵉ ⊥ᵉ postcompᵉ Sᵉ g`ᵉ forᵉ everyᵉ typeᵉ `S`.ᵉ

**Proof:**ᵉ Thisᵉ isᵉ aᵉ specialᵉ caseᵉ ofᵉ theᵉ previousᵉ resultᵉ byᵉ takingᵉ `g`ᵉ to beᵉ
constantᵉ overᵉ `S`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (Sᵉ : UUᵉ l5ᵉ)
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-right-postcompᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ (postcompᵉ Sᵉ gᵉ)
  is-orthogonal-pullback-condition-right-postcompᵉ Gᵉ =
    is-orthogonal-pullback-condition-right-Πᵉ fᵉ (λ _ → gᵉ) (λ _ → Gᵉ)

  is-orthogonal-right-postcompᵉ :
    is-orthogonalᵉ fᵉ gᵉ → is-orthogonalᵉ fᵉ (postcompᵉ Sᵉ gᵉ)
  is-orthogonal-right-postcompᵉ Gᵉ =
    is-orthogonal-right-Πᵉ fᵉ (λ _ → gᵉ) (λ _ → Gᵉ)
```

### Right orthogonality is preserved by products

Ifᵉ `fᵉ ⊥ᵉ g`ᵉ andᵉ `fᵉ ⊥ᵉ g'`,ᵉ thenᵉ `fᵉ ⊥ᵉ (gᵉ ×ᵉ g')`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {X'ᵉ : UUᵉ l5ᵉ} {Y'ᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (g'ᵉ : X'ᵉ → Y'ᵉ)
  where

  is-orthogonal-pullback-condition-right-productᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ g'ᵉ →
    is-orthogonal-pullback-conditionᵉ fᵉ (map-productᵉ gᵉ g'ᵉ)
  is-orthogonal-pullback-condition-right-productᵉ Gᵉ G'ᵉ =
    is-pullback-top-is-pullback-bottom-cube-is-equivᵉ
      ( map-productᵉ (postcompᵉ Bᵉ gᵉ) (postcompᵉ Bᵉ g'ᵉ))
      ( map-productᵉ (precompᵉ fᵉ Xᵉ) (precompᵉ fᵉ X'ᵉ))
      ( map-productᵉ (precompᵉ fᵉ Yᵉ) (precompᵉ fᵉ Y'ᵉ))
      ( map-productᵉ (postcompᵉ Aᵉ gᵉ) (postcompᵉ Aᵉ g'ᵉ))
      ( postcompᵉ Bᵉ (map-productᵉ gᵉ g'ᵉ))
      ( precompᵉ fᵉ (Xᵉ ×ᵉ X'ᵉ))
      ( precompᵉ fᵉ (Yᵉ ×ᵉ Y'ᵉ))
      ( postcompᵉ Aᵉ (map-productᵉ gᵉ g'ᵉ))
      ( map-up-productᵉ)
      ( map-up-productᵉ)
      ( map-up-productᵉ)
      ( map-up-productᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( up-productᵉ)
      ( up-productᵉ)
      ( up-productᵉ)
      ( up-productᵉ)
      ( is-pullback-product-is-pullbackᵉ
        ( precompᵉ fᵉ Yᵉ)
        ( postcompᵉ Aᵉ gᵉ)
        ( precompᵉ fᵉ Y'ᵉ)
        ( postcompᵉ Aᵉ g'ᵉ)
        ( cone-pullback-homᵉ fᵉ gᵉ)
        ( cone-pullback-homᵉ fᵉ g'ᵉ)
        ( Gᵉ)
        ( G'ᵉ))

  is-orthogonal-right-productᵉ :
    is-orthogonalᵉ fᵉ gᵉ → is-orthogonalᵉ fᵉ g'ᵉ → is-orthogonalᵉ fᵉ (map-productᵉ gᵉ g'ᵉ)
  is-orthogonal-right-productᵉ Gᵉ G'ᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ (map-productᵉ gᵉ g'ᵉ)
      ( is-orthogonal-pullback-condition-right-productᵉ
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Gᵉ)
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ g'ᵉ G'ᵉ))
```

### Left orthogonality is preserved by dependent sums

Ifᵉ `fᵢᵉ ⊥ᵉ g`ᵉ forᵉ everyᵉ `i`,ᵉ thenᵉ `(totᵉ fᵉ) ⊥ᵉ g`.ᵉ

**Proof:**ᵉ Weᵉ needᵉ to showᵉ thatᵉ theᵉ squareᵉ

```text
                  -ᵉ ∘ᵉ (totᵉ fᵉ)
  ((Σᵉ Iᵉ Bᵉ) → Xᵉ) --------------->ᵉ ((Σᵉ Iᵉ Aᵉ) → Xᵉ)
        |                               |
        |                               |
  gᵉ ∘ᵉ -ᵉ |                               | gᵉ ∘ᵉ -ᵉ
        |                               |
        ∨ᵉ                               ∨ᵉ
  ((Σᵉ Iᵉ Bᵉ) → Yᵉ) --------------->ᵉ ((Σᵉ Iᵉ Aᵉ) → Yᵉ)
                  -ᵉ ∘ᵉ (totᵉ fᵉ)
```

isᵉ aᵉ pullback.ᵉ However,ᵉ byᵉ theᵉ universalᵉ propertyᵉ ofᵉ dependentᵉ pairᵉ typesᵉ thisᵉ
squareᵉ isᵉ equivalentᵉ to

```text
                    Πᵢᵉ (-ᵉ ∘ᵉ fᵢᵉ)
        Πᵢᵉ (Bᵢᵉ → Xᵉ) ----------->ᵉ Πᵢᵉ (Aᵢᵉ → Xᵉ)
             |                        |
             |                        |
  Πᵢᵉ (gᵉ ∘ᵉ -ᵉ) |                        | Πᵢᵉ (gᵉ ∘ᵉ -ᵉ)
             |                        |
             ∨ᵉ                        ∨ᵉ
        Πᵢᵉ (Bᵢᵉ → Yᵉ) ----------->ᵉ Πᵢᵉ (Aᵢᵉ → Y),ᵉ
                    Πᵢᵉ (-ᵉ ∘ᵉ fᵢᵉ)
```

whichᵉ isᵉ aᵉ pullbackᵉ byᵉ assumptionᵉ andᵉ theᵉ factᵉ thatᵉ pullbacksᵉ areᵉ preservedᵉ
underᵉ dependentᵉ products.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-left-Σᵉ :
    ((iᵉ : Iᵉ) → is-orthogonal-pullback-conditionᵉ (fᵉ iᵉ) gᵉ) →
    is-orthogonal-pullback-conditionᵉ (totᵉ fᵉ) gᵉ
  is-orthogonal-pullback-condition-left-Σᵉ Fᵉ =
    is-pullback-top-is-pullback-bottom-cube-is-equivᵉ
      ( map-Πᵉ (λ iᵉ → postcompᵉ (Bᵉ iᵉ) gᵉ))
      ( map-Πᵉ (λ iᵉ → precompᵉ (fᵉ iᵉ) Xᵉ))
      ( map-Πᵉ (λ iᵉ → precompᵉ (fᵉ iᵉ) Yᵉ))
      ( map-Πᵉ (λ iᵉ → postcompᵉ (Aᵉ iᵉ) gᵉ))
      ( postcompᵉ (Σᵉ Iᵉ Bᵉ) gᵉ)
      ( precompᵉ (totᵉ fᵉ) Xᵉ)
      ( precompᵉ (totᵉ fᵉ) Yᵉ)
      ( postcompᵉ (Σᵉ Iᵉ Aᵉ) gᵉ)
      ( ev-pairᵉ)
      ( ev-pairᵉ)
      ( ev-pairᵉ)
      ( ev-pairᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( λ _ → eq-htpyᵉ refl-htpyᵉ)
      ( inv-htpyᵉ
        ( ( right-unit-htpyᵉ) ∙hᵉ
          ( ( eq-htpy-refl-htpyᵉ) ·rᵉ
            ( ( map-Πᵉ (λ iᵉ → precompᵉ (fᵉ iᵉ) Yᵉ)) ∘ᵉ
              ( map-Πᵉ (λ iᵉ → postcompᵉ (Bᵉ iᵉ) gᵉ)) ∘ᵉ
              ( ev-pairᵉ)))))
      ( is-equiv-ev-pairᵉ)
      ( is-equiv-ev-pairᵉ)
      ( is-equiv-ev-pairᵉ)
      ( is-equiv-ev-pairᵉ)
      ( is-pullback-Πᵉ
        ( λ iᵉ → precompᵉ (fᵉ iᵉ) Yᵉ)
        ( λ iᵉ → postcompᵉ (Aᵉ iᵉ) gᵉ)
        ( λ iᵉ → cone-pullback-homᵉ (fᵉ iᵉ) gᵉ)
        ( Fᵉ))

  is-orthogonal-left-Σᵉ :
    ((iᵉ : Iᵉ) → is-orthogonalᵉ (fᵉ iᵉ) gᵉ) → is-orthogonalᵉ (totᵉ fᵉ) gᵉ
  is-orthogonal-left-Σᵉ Fᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ (totᵉ fᵉ) gᵉ
      ( is-orthogonal-pullback-condition-left-Σᵉ
        ( λ iᵉ → is-orthogonal-pullback-condition-is-orthogonalᵉ (fᵉ iᵉ) gᵉ (Fᵉ iᵉ)))
```

### Left orthogonality is preserved by coproducts

Ifᵉ `fᵉ ⊥ᵉ g`ᵉ andᵉ `f'ᵉ ⊥ᵉ g`,ᵉ thenᵉ `(fᵉ +ᵉ f'ᵉ) ⊥ᵉ g`.ᵉ

**Proof:**ᵉ Weᵉ needᵉ to showᵉ thatᵉ theᵉ squareᵉ

```text
                     -ᵉ ∘ᵉ (fᵉ +ᵉ f'ᵉ)
  ((Bᵉ +ᵉ B'ᵉ) → Xᵉ) --------------->ᵉ ((Aᵉ +ᵉ A'ᵉ) → Xᵉ)
        |                               |
        |                               |
  gᵉ ∘ᵉ -ᵉ |                               | gᵉ ∘ᵉ -ᵉ
        |                               |
        ∨ᵉ                               ∨ᵉ
  ((Bᵉ +ᵉ B'ᵉ) → Yᵉ) --------------->ᵉ ((Aᵉ +ᵉ A'ᵉ) → Yᵉ)
                   -ᵉ ∘ᵉ (fᵉ +ᵉ f'ᵉ)
```

isᵉ aᵉ pullback.ᵉ However,ᵉ byᵉ theᵉ universalᵉ propertyᵉ ofᵉ coproductsᵉ thisᵉ squareᵉ isᵉ
equivalentᵉ to

```text
                            (-ᵉ ∘ᵉ fᵉ) ×ᵉ (-ᵉ ∘ᵉ f'ᵉ)
            (Bᵉ → Xᵉ) ×ᵉ (B'ᵉ → Xᵉ) ----------->ᵉ (Aᵉ → Xᵉ) ×ᵉ (A'ᵉ → Xᵉ)
                    |                               |
                    |                               |
  (gᵉ ∘ᵉ -ᵉ) ×ᵉ (gᵉ ∘ᵉ -ᵉ) |                               | (gᵉ ∘ᵉ -ᵉ) ×ᵉ (gᵉ ∘ᵉ -ᵉ)
                    |                               |
                    ∨ᵉ                               ∨ᵉ
            (Bᵉ → Yᵉ) ×ᵉ (B'ᵉ → Yᵉ) ----------->ᵉ (Aᵉ → Yᵉ) ×ᵉ (A'ᵉ → Y),ᵉ
                            (-ᵉ ∘ᵉ fᵉ) ×ᵉ (-ᵉ ∘ᵉ f'ᵉ)
```

whichᵉ isᵉ aᵉ pullbackᵉ byᵉ assumptionᵉ andᵉ theᵉ factᵉ thatᵉ pullbacksᵉ areᵉ preservedᵉ
underᵉ products.ᵉ

**Note:**ᵉ Thisᵉ resultᵉ canᵉ alsoᵉ beᵉ obtainedᵉ asᵉ aᵉ specialᵉ caseᵉ ofᵉ theᵉ previousᵉ oneᵉ
byᵉ takingᵉ theᵉ indexingᵉ typeᵉ to beᵉ theᵉ
[two-elementᵉ type](foundation.booleans.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {A'ᵉ : UUᵉ l3ᵉ} {B'ᵉ : UUᵉ l4ᵉ} {Xᵉ : UUᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (f'ᵉ : A'ᵉ → B'ᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-left-coproductᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ f'ᵉ gᵉ →
    is-orthogonal-pullback-conditionᵉ (map-coproductᵉ fᵉ f'ᵉ) gᵉ
  is-orthogonal-pullback-condition-left-coproductᵉ Fᵉ F'ᵉ =
    is-pullback-top-is-pullback-bottom-cube-is-equivᵉ
      ( map-productᵉ (postcompᵉ Bᵉ gᵉ) (postcompᵉ B'ᵉ gᵉ))
      ( map-productᵉ (precompᵉ fᵉ Xᵉ) (precompᵉ f'ᵉ Xᵉ))
      ( map-productᵉ (precompᵉ fᵉ Yᵉ) (precompᵉ f'ᵉ Yᵉ))
      ( map-productᵉ (postcompᵉ Aᵉ gᵉ) (postcompᵉ A'ᵉ gᵉ))
      ( postcompᵉ (Bᵉ +ᵉ B'ᵉ) gᵉ)
      ( precompᵉ (map-coproductᵉ fᵉ f'ᵉ) Xᵉ)
      ( precompᵉ (map-coproductᵉ fᵉ f'ᵉ) Yᵉ)
      ( postcompᵉ (Aᵉ +ᵉ A'ᵉ) gᵉ)
      ( ev-inl-inrᵉ (λ _ → Xᵉ))
      ( ev-inl-inrᵉ (λ _ → Yᵉ))
      ( ev-inl-inrᵉ (λ _ → Xᵉ))
      ( ev-inl-inrᵉ (λ _ → Yᵉ))
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( universal-property-coproductᵉ Xᵉ)
      ( universal-property-coproductᵉ Yᵉ)
      ( universal-property-coproductᵉ Xᵉ)
      ( universal-property-coproductᵉ Yᵉ)
      ( is-pullback-product-is-pullbackᵉ
        ( precompᵉ fᵉ Yᵉ)
        ( postcompᵉ Aᵉ gᵉ)
        ( precompᵉ f'ᵉ Yᵉ)
        ( postcompᵉ A'ᵉ gᵉ)
        ( cone-pullback-homᵉ fᵉ gᵉ)
        ( cone-pullback-homᵉ f'ᵉ gᵉ)
        ( Fᵉ)
        ( F'ᵉ))

  is-orthogonal-left-coproductᵉ :
    is-orthogonalᵉ fᵉ gᵉ →
    is-orthogonalᵉ f'ᵉ gᵉ →
    is-orthogonalᵉ (map-coproductᵉ fᵉ f'ᵉ) gᵉ
  is-orthogonal-left-coproductᵉ Fᵉ F'ᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ (map-coproductᵉ fᵉ f'ᵉ) gᵉ
      ( is-orthogonal-pullback-condition-left-coproductᵉ
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Fᵉ)
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ f'ᵉ gᵉ F'ᵉ))
```

### Right orthogonality is preserved under base change

Givenᵉ aᵉ pullbackᵉ squareᵉ

```text
    X'ᵉ ----->ᵉ Xᵉ
    | ⌟ᵉ       |
  g'|ᵉ         | gᵉ
    ∨ᵉ         ∨ᵉ
    Y'ᵉ ----->ᵉ Y,ᵉ
```

ifᵉ `fᵉ ⊥ᵉ g`,ᵉ thenᵉ `fᵉ ⊥ᵉ g'`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {X'ᵉ : UUᵉ l5ᵉ} {Y'ᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (g'ᵉ : X'ᵉ → Y'ᵉ) (αᵉ : cartesian-hom-arrowᵉ g'ᵉ gᵉ)
  where

  is-orthogonal-pullback-condition-right-base-changeᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ → is-orthogonal-pullback-conditionᵉ fᵉ g'ᵉ
  is-orthogonal-pullback-condition-right-base-changeᵉ Gᵉ =
    is-pullback-back-right-is-pullback-back-left-cubeᵉ
      ( refl-htpyᵉ)
      ( htpy-postcompᵉ Bᵉ (coh-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ))
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( htpy-postcompᵉ Aᵉ (coh-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ))
      ( refl-htpyᵉ)
      ( ( right-unit-htpyᵉ) ∙hᵉ
        ( right-unit-htpyᵉ) ∙hᵉ
        ( inv-htpyᵉ
          ( commutative-precomp-htpy-postcompᵉ
            ( fᵉ)
            ( coh-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ))))
      ( Gᵉ)
      ( is-pullback-postcomp-is-pullbackᵉ
        ( map-codomain-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ)
        ( gᵉ)
        ( cone-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ)
        ( Aᵉ))
      ( is-pullback-postcomp-is-pullbackᵉ
        ( map-codomain-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ)
        ( gᵉ)
        ( cone-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ g'ᵉ gᵉ αᵉ)
        ( Bᵉ))

  is-orthogonal-right-base-changeᵉ : is-orthogonalᵉ fᵉ gᵉ → is-orthogonalᵉ fᵉ g'ᵉ
  is-orthogonal-right-base-changeᵉ Gᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ g'ᵉ
      ( is-orthogonal-pullback-condition-right-base-changeᵉ
        ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Gᵉ))
```

### A type is `f`-local if and only if its terminal map is `f`-orthogonal

**Proofᵉ (forwardᵉ direction):**ᵉ Ifᵉ theᵉ terminalᵉ mapᵉ isᵉ rightᵉ orthogonalᵉ to `f`,ᵉ
thatᵉ meansᵉ weᵉ haveᵉ aᵉ pullbackᵉ squareᵉ

```text
            -ᵉ ∘ᵉ fᵉ
      Bᵉ → Xᵉ ----->ᵉ Aᵉ → Xᵉ
        | ⌟ᵉ          |
  !ᵉ ∘ᵉ -ᵉ |            | !ᵉ ∘ᵉ -ᵉ
        ∨ᵉ            ∨ᵉ
      Bᵉ → 1 ----->ᵉ Aᵉ → 1.ᵉ
            -ᵉ ∘ᵉ fᵉ
```

whichᵉ displaysᵉ `precompᵉ fᵉ X`ᵉ asᵉ aᵉ pullbackᵉ ofᵉ anᵉ equivalence,ᵉ henceᵉ itᵉ isᵉ itselfᵉ
anᵉ equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-local-is-orthogonal-pullback-condition-terminal-mapᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ (terminal-mapᵉ Xᵉ) → is-localᵉ fᵉ Xᵉ
  is-local-is-orthogonal-pullback-condition-terminal-mapᵉ =
    is-equiv-horizontal-map-is-pullbackᵉ
      ( precompᵉ fᵉ unitᵉ)
      ( postcompᵉ Aᵉ (terminal-mapᵉ Xᵉ))
      ( cone-pullback-homᵉ fᵉ (terminal-mapᵉ Xᵉ))
      ( is-local-is-contrᵉ fᵉ unitᵉ is-contr-unitᵉ)

  is-local-is-orthogonal-terminal-mapᵉ :
    is-orthogonalᵉ fᵉ (terminal-mapᵉ Xᵉ) → is-localᵉ fᵉ Xᵉ
  is-local-is-orthogonal-terminal-mapᵉ Fᵉ =
    is-local-is-orthogonal-pullback-condition-terminal-mapᵉ
      ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ (terminal-mapᵉ Xᵉ) Fᵉ)

  is-orthogonal-pullback-condition-terminal-map-is-localᵉ :
    is-localᵉ fᵉ Xᵉ → is-orthogonal-pullback-conditionᵉ fᵉ (terminal-mapᵉ Xᵉ)
  is-orthogonal-pullback-condition-terminal-map-is-localᵉ =
    is-pullback-is-equiv-horizontal-mapsᵉ
      ( precompᵉ fᵉ unitᵉ)
      ( postcompᵉ Aᵉ (terminal-mapᵉ Xᵉ))
      ( cone-pullback-homᵉ fᵉ (terminal-mapᵉ Xᵉ))
      ( is-local-is-contrᵉ fᵉ unitᵉ is-contr-unitᵉ)

  is-orthogonal-terminal-map-is-localᵉ :
    is-localᵉ fᵉ Xᵉ → is-orthogonalᵉ fᵉ (terminal-mapᵉ Xᵉ)
  is-orthogonal-terminal-map-is-localᵉ Fᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ (terminal-mapᵉ Xᵉ)
      ( is-orthogonal-pullback-condition-terminal-map-is-localᵉ Fᵉ)
```

### If the codomain of `g` is `f`-local, then `g` is `f`-orthogonal if and only if the domain of `g` is `f`-local

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-orthogonal-pullback-condition-is-local-domain-is-local-codomainᵉ :
    is-localᵉ fᵉ Yᵉ → is-localᵉ fᵉ Xᵉ → is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
  is-orthogonal-pullback-condition-is-local-domain-is-local-codomainᵉ =
    is-pullback-is-equiv-horizontal-mapsᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-pullback-homᵉ fᵉ gᵉ)

  is-orthogonal-is-local-domain-is-local-codomainᵉ :
    is-localᵉ fᵉ Yᵉ → is-localᵉ fᵉ Xᵉ → is-orthogonalᵉ fᵉ gᵉ
  is-orthogonal-is-local-domain-is-local-codomainᵉ Hᵉ Kᵉ =
    is-orthogonal-is-orthogonal-pullback-conditionᵉ fᵉ gᵉ
      ( is-orthogonal-pullback-condition-is-local-domain-is-local-codomainᵉ Hᵉ Kᵉ)

  is-local-domain-is-orthogonal-pullback-condition-is-local-codomainᵉ :
    is-localᵉ fᵉ Yᵉ → is-orthogonal-pullback-conditionᵉ fᵉ gᵉ → is-localᵉ fᵉ Xᵉ
  is-local-domain-is-orthogonal-pullback-condition-is-local-codomainᵉ Hᵉ Gᵉ =
    is-local-is-orthogonal-pullback-condition-terminal-mapᵉ fᵉ
      ( is-orthogonal-pullback-condition-right-compᵉ fᵉ gᵉ (terminal-mapᵉ Yᵉ)
        ( is-orthogonal-pullback-condition-terminal-map-is-localᵉ fᵉ Hᵉ)
        ( Gᵉ))

  is-local-domain-is-orthogonal-is-local-codomainᵉ :
    is-localᵉ fᵉ Yᵉ → is-orthogonalᵉ fᵉ gᵉ → is-localᵉ fᵉ Xᵉ
  is-local-domain-is-orthogonal-is-local-codomainᵉ Hᵉ Gᵉ =
    is-local-domain-is-orthogonal-pullback-condition-is-local-codomainᵉ Hᵉ
      ( is-orthogonal-pullback-condition-is-orthogonalᵉ fᵉ gᵉ Gᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ BW23ᵉ}}
# Null maps

```agda
module orthogonal-factorization-systems.null-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.families-of-equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-family-of-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-mapsᵉ
open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.null-families-of-typesᵉ
open import orthogonal-factorization-systems.null-typesᵉ
open import orthogonal-factorization-systems.orthogonal-mapsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "null"ᵉ Disambiguation="functionᵉ atᵉ aᵉ type"ᵉ Agda=is-null-mapᵉ}} atᵉ `Y`,ᵉ
orᵉ {{#conceptᵉ "`Y`-null"ᵉ Disambiguation="functionᵉ atᵉ aᵉ type"ᵉ Agda=is-null-mapᵉ}}
ifᵉ itsᵉ [fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
`Y`-[null](orthogonal-factorization-systems.null-types.md),ᵉ orᵉ equivalently,ᵉ ifᵉ
theᵉ squareᵉ

```text
         Δᵉ
    Aᵉ ------>ᵉ (Yᵉ → Aᵉ)
    |            |
  fᵉ |            | fᵉ ∘ᵉ -ᵉ
    ∨ᵉ            ∨ᵉ
    Bᵉ ------>ᵉ (Yᵉ → Bᵉ)
         Δᵉ
```

isᵉ aᵉ [pullback](foundation-core.pullbacks.md).ᵉ

## Definitions

### The fiber condition for `Y`-null maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-null-mapᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-null-mapᵉ = is-null-familyᵉ Yᵉ (fiberᵉ fᵉ)

  is-property-is-null-mapᵉ : is-propᵉ is-null-mapᵉ
  is-property-is-null-mapᵉ = is-property-is-null-familyᵉ Yᵉ (fiberᵉ fᵉ)

  is-null-map-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-null-map-Propᵉ = (is-null-mapᵉ ,ᵉ is-property-is-null-mapᵉ)
```

### The pullback condition for `Y`-null maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  cone-is-null-map-pullback-conditionᵉ :
    coneᵉ (diagonal-exponentialᵉ Bᵉ Yᵉ) (postcompᵉ Yᵉ fᵉ) Aᵉ
  cone-is-null-map-pullback-conditionᵉ =
    (fᵉ ,ᵉ diagonal-exponentialᵉ Aᵉ Yᵉ ,ᵉ refl-htpyᵉ)

  is-null-map-pullback-conditionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-null-map-pullback-conditionᵉ =
    is-pullbackᵉ
      ( diagonal-exponentialᵉ Bᵉ Yᵉ)
      ( postcompᵉ Yᵉ fᵉ)
      ( cone-is-null-map-pullback-conditionᵉ)

  is-prop-is-null-map-pullback-conditionᵉ :
    is-propᵉ is-null-map-pullback-conditionᵉ
  is-prop-is-null-map-pullback-conditionᵉ =
    is-prop-is-pullbackᵉ
      ( diagonal-exponentialᵉ Bᵉ Yᵉ)
      ( postcompᵉ Yᵉ fᵉ)
      ( cone-is-null-map-pullback-conditionᵉ)
```

## Properties

### A type family is `Y`-null if and only if its total space projection is

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  is-null-family-is-null-map-pr1ᵉ :
    is-null-mapᵉ Yᵉ (pr1ᵉ {Bᵉ = Bᵉ}) → is-null-familyᵉ Yᵉ Bᵉ
  is-null-family-is-null-map-pr1ᵉ =
    is-null-family-equiv-familyᵉ (inv-equiv-fiber-pr1ᵉ Bᵉ)

  is-null-map-pr1-is-null-familyᵉ :
    is-null-familyᵉ Yᵉ Bᵉ → is-null-mapᵉ Yᵉ (pr1ᵉ {Bᵉ = Bᵉ})
  is-null-map-pr1-is-null-familyᵉ =
    is-null-family-equiv-familyᵉ (equiv-fiber-pr1ᵉ Bᵉ)
```

### The pullback and fiber condition for `Y`-null maps are equivalent

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    compute-map-fiber-vertical-map-cone-is-null-map-pullback-conditionᵉ :
      (bᵉ : Bᵉ) →
      equiv-arrowᵉ
        ( map-fiber-vertical-map-coneᵉ
          ( diagonal-exponentialᵉ Bᵉ Yᵉ)
          ( postcompᵉ Yᵉ fᵉ)
          ( cone-is-null-map-pullback-conditionᵉ Yᵉ fᵉ)
          ( bᵉ))
        ( diagonal-exponentialᵉ (fiberᵉ fᵉ bᵉ) Yᵉ)
    compute-map-fiber-vertical-map-cone-is-null-map-pullback-conditionᵉ bᵉ =
      ( id-equivᵉ ,ᵉ
        inv-compute-Π-fiber-postcompᵉ Yᵉ fᵉ (diagonal-exponentialᵉ Bᵉ Yᵉ bᵉ) ,ᵉ
        ( λ where (xᵉ ,ᵉ reflᵉ) → reflᵉ))

  is-null-map-pullback-condition-is-null-mapᵉ :
    is-null-mapᵉ Yᵉ fᵉ → is-null-map-pullback-conditionᵉ Yᵉ fᵉ
  is-null-map-pullback-condition-is-null-mapᵉ Hᵉ =
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ
      ( diagonal-exponentialᵉ Bᵉ Yᵉ)
      ( postcompᵉ Yᵉ fᵉ)
      ( cone-is-null-map-pullback-conditionᵉ Yᵉ fᵉ)
      ( λ bᵉ →
        is-equiv-source-is-equiv-target-equiv-arrowᵉ
          ( map-fiber-vertical-map-coneᵉ
            ( diagonal-exponentialᵉ Bᵉ Yᵉ)
            ( postcompᵉ Yᵉ fᵉ)
            ( cone-is-null-map-pullback-conditionᵉ Yᵉ fᵉ)
            ( bᵉ))
          ( diagonal-exponentialᵉ (fiberᵉ fᵉ bᵉ) Yᵉ)
          ( compute-map-fiber-vertical-map-cone-is-null-map-pullback-conditionᵉ
            ( bᵉ))
          ( Hᵉ bᵉ))

  is-null-map-is-null-map-pullback-conditionᵉ :
    is-null-map-pullback-conditionᵉ Yᵉ fᵉ → is-null-mapᵉ Yᵉ fᵉ
  is-null-map-is-null-map-pullback-conditionᵉ Hᵉ bᵉ =
    is-equiv-target-is-equiv-source-equiv-arrowᵉ
      ( map-fiber-vertical-map-coneᵉ
        ( diagonal-exponentialᵉ Bᵉ Yᵉ)
        ( postcompᵉ Yᵉ fᵉ)
        ( cone-is-null-map-pullback-conditionᵉ Yᵉ fᵉ)
        ( bᵉ))
      ( diagonal-exponentialᵉ (fiberᵉ fᵉ bᵉ) Yᵉ)
      ( compute-map-fiber-vertical-map-cone-is-null-map-pullback-conditionᵉ bᵉ)
      ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
        ( diagonal-exponentialᵉ Bᵉ Yᵉ)
        ( postcompᵉ Yᵉ fᵉ)
        ( cone-is-null-map-pullback-conditionᵉ Yᵉ fᵉ)
        ( Hᵉ)
        ( bᵉ))
```

### A map is `Y`-null if and only if it is local at the terminal projection `Y → unit`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-local-terminal-map-is-null-mapᵉ :
    is-null-mapᵉ Yᵉ fᵉ → is-local-mapᵉ (terminal-mapᵉ Yᵉ) fᵉ
  is-local-terminal-map-is-null-mapᵉ Hᵉ xᵉ =
    is-local-terminal-map-is-nullᵉ Yᵉ (fiberᵉ fᵉ xᵉ) (Hᵉ xᵉ)

  is-null-map-is-local-terminal-mapᵉ :
    is-local-mapᵉ (terminal-mapᵉ Yᵉ) fᵉ → is-null-mapᵉ Yᵉ fᵉ
  is-null-map-is-local-terminal-mapᵉ Hᵉ xᵉ =
    is-null-is-local-terminal-mapᵉ Yᵉ (fiberᵉ fᵉ xᵉ) (Hᵉ xᵉ)

  equiv-is-local-terminal-map-is-null-mapᵉ :
    is-null-mapᵉ Yᵉ fᵉ ≃ᵉ is-local-mapᵉ (terminal-mapᵉ Yᵉ) fᵉ
  equiv-is-local-terminal-map-is-null-mapᵉ =
    equiv-iff-is-propᵉ
      ( is-property-is-null-mapᵉ Yᵉ fᵉ)
      ( is-property-is-local-mapᵉ (terminal-mapᵉ Yᵉ) fᵉ)
      ( is-local-terminal-map-is-null-mapᵉ)
      ( is-null-map-is-local-terminal-mapᵉ)

  equiv-is-null-map-is-local-terminal-mapᵉ :
    is-local-mapᵉ (terminal-mapᵉ Yᵉ) fᵉ ≃ᵉ is-null-mapᵉ Yᵉ fᵉ
  equiv-is-null-map-is-local-terminal-mapᵉ =
    inv-equivᵉ equiv-is-local-terminal-map-is-null-mapᵉ
```

### A map is `Y`-null if and only if the terminal projection of `Y` is orthogonal to `f`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-null-map-is-orthogonal-fiber-condition-terminal-mapᵉ :
    is-orthogonal-fiber-condition-right-mapᵉ (terminal-mapᵉ Yᵉ) fᵉ →
    is-null-mapᵉ Yᵉ fᵉ
  is-null-map-is-orthogonal-fiber-condition-terminal-mapᵉ Hᵉ bᵉ =
    is-equiv-target-is-equiv-source-equiv-arrowᵉ
      ( precompᵉ (terminal-mapᵉ Yᵉ) (fiberᵉ fᵉ bᵉ))
      ( diagonal-exponentialᵉ (fiberᵉ fᵉ bᵉ) Yᵉ)
      ( left-unit-law-function-typeᵉ (fiberᵉ fᵉ bᵉ) ,ᵉ id-equivᵉ ,ᵉ refl-htpyᵉ)
      ( Hᵉ (pointᵉ bᵉ))

  is-orthogonal-fiber-condition-terminal-map-is-null-mapᵉ :
    is-null-mapᵉ Yᵉ fᵉ →
    is-orthogonal-fiber-condition-right-mapᵉ (terminal-mapᵉ Yᵉ) fᵉ
  is-orthogonal-fiber-condition-terminal-map-is-null-mapᵉ Hᵉ bᵉ =
    is-equiv-source-is-equiv-target-equiv-arrowᵉ
      ( precompᵉ (terminal-mapᵉ Yᵉ) (fiberᵉ fᵉ (bᵉ starᵉ)))
      ( diagonal-exponentialᵉ (fiberᵉ fᵉ (bᵉ starᵉ)) Yᵉ)
      ( left-unit-law-function-typeᵉ (fiberᵉ fᵉ (bᵉ starᵉ)) ,ᵉ id-equivᵉ ,ᵉ refl-htpyᵉ)
      ( Hᵉ (bᵉ starᵉ))

  is-null-map-is-orthogonal-pullback-condition-terminal-mapᵉ :
    is-orthogonal-pullback-conditionᵉ (terminal-mapᵉ Yᵉ) fᵉ → is-null-mapᵉ Yᵉ fᵉ
  is-null-map-is-orthogonal-pullback-condition-terminal-mapᵉ Hᵉ =
    is-null-map-is-orthogonal-fiber-condition-terminal-mapᵉ
      ( is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-conditionᵉ
        ( terminal-mapᵉ Yᵉ)
        ( fᵉ)
        ( Hᵉ))

  is-orthogonal-pullback-condition-terminal-map-is-null-mapᵉ :
    is-null-mapᵉ Yᵉ fᵉ → is-orthogonal-pullback-conditionᵉ (terminal-mapᵉ Yᵉ) fᵉ
  is-orthogonal-pullback-condition-terminal-map-is-null-mapᵉ Hᵉ =
    is-orthogonal-pullback-condition-is-orthogonal-fiber-condition-right-mapᵉ
      ( terminal-mapᵉ Yᵉ)
      ( fᵉ)
      ( is-orthogonal-fiber-condition-terminal-map-is-null-mapᵉ Hᵉ)

  is-null-map-is-orthogonal-terminal-mapᵉ :
    is-orthogonalᵉ (terminal-mapᵉ Yᵉ) fᵉ → is-null-mapᵉ Yᵉ fᵉ
  is-null-map-is-orthogonal-terminal-mapᵉ Hᵉ =
    is-null-map-is-orthogonal-fiber-condition-terminal-mapᵉ
      ( is-orthogonal-fiber-condition-right-map-is-orthogonalᵉ
        ( terminal-mapᵉ Yᵉ)
        ( fᵉ)
        ( Hᵉ))

  is-orthogonal-terminal-map-is-null-mapᵉ :
    is-null-mapᵉ Yᵉ fᵉ → is-orthogonalᵉ (terminal-mapᵉ Yᵉ) fᵉ
  is-orthogonal-terminal-map-is-null-mapᵉ Hᵉ =
    is-orthogonal-is-orthogonal-fiber-condition-right-mapᵉ (terminal-mapᵉ Yᵉ) fᵉ
      ( is-orthogonal-fiber-condition-terminal-map-is-null-mapᵉ Hᵉ)
```
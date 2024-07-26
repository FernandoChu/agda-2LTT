# Local maps

```agda
module orthogonal-factorization-systems.local-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-morphisms-arrowsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-family-of-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-families-of-typesᵉ
open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.orthogonal-mapsᵉ
open import orthogonal-factorization-systems.pullback-homᵉ
```

</details>

## Idea

Aᵉ mapᵉ `gᵉ : Xᵉ → Y`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "local"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ Agda=is-local-mapᵉ}} atᵉ
`fᵉ : Aᵉ → B`,ᵉ orᵉ
{{#conceptᵉ "`f`-local"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ Agda=is-local-map}},ᵉ ifᵉ
allᵉ itsᵉ [fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
[`f`-localᵉ types](orthogonal-factorization-systems.local-types.md).ᵉ

Equivalently,ᵉ theᵉ mapᵉ `g`ᵉ isᵉ `f`-localᵉ ifᵉ andᵉ onlyᵉ ifᵉ `f`ᵉ isᵉ
[orthogonal](orthogonal-factorization-systems.orthogonal-maps.mdᵉ) to `g`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-local-mapᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-local-mapᵉ = is-local-familyᵉ fᵉ (fiberᵉ gᵉ)

  is-property-is-local-mapᵉ : is-propᵉ is-local-mapᵉ
  is-property-is-local-mapᵉ = is-property-is-local-familyᵉ fᵉ (fiberᵉ gᵉ)

  is-local-map-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-local-map-Propᵉ = is-local-family-Propᵉ fᵉ (fiberᵉ gᵉ)
```

### A type `B` is `f`-local if and only if the terminal map `B → unit` is `f`-local

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Bᵉ)
  where

  is-local-is-local-terminal-mapᵉ :
    is-local-mapᵉ fᵉ (terminal-mapᵉ Yᵉ) → is-localᵉ fᵉ Yᵉ
  is-local-is-local-terminal-mapᵉ Hᵉ =
    is-local-equivᵉ fᵉ (inv-equiv-fiber-terminal-mapᵉ starᵉ) (Hᵉ starᵉ)

  is-local-terminal-map-is-localᵉ :
    is-localᵉ fᵉ Yᵉ → is-local-mapᵉ fᵉ (terminal-mapᵉ Yᵉ)
  is-local-terminal-map-is-localᵉ Hᵉ uᵉ =
    is-local-equivᵉ fᵉ (equiv-fiber-terminal-mapᵉ uᵉ) Hᵉ
```

### A map is `f`-local if and only if it is `f`-orthogonal

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-local-map-is-orthogonal-pullback-conditionᵉ :
    is-orthogonal-pullback-conditionᵉ fᵉ gᵉ → is-local-mapᵉ fᵉ gᵉ
  is-local-map-is-orthogonal-pullback-conditionᵉ Gᵉ yᵉ =
    is-local-is-orthogonal-pullback-condition-terminal-mapᵉ fᵉ
      ( is-orthogonal-pullback-condition-right-base-changeᵉ fᵉ gᵉ
        ( terminal-mapᵉ (fiberᵉ gᵉ yᵉ))
        ( fiber-cartesian-hom-arrowᵉ gᵉ yᵉ)
        ( Gᵉ))

  is-local-map-is-orthogonalᵉ : is-orthogonalᵉ fᵉ gᵉ → is-local-mapᵉ fᵉ gᵉ
  is-local-map-is-orthogonalᵉ Gᵉ yᵉ =
    is-local-is-orthogonal-terminal-mapᵉ fᵉ
      ( is-orthogonal-right-base-changeᵉ fᵉ gᵉ
        ( terminal-mapᵉ (fiberᵉ gᵉ yᵉ))
        ( fiber-cartesian-hom-arrowᵉ gᵉ yᵉ)
        ( Gᵉ))
```

Theᵉ converseᵉ remainsᵉ to beᵉ formalized.ᵉ

## See also

-ᵉ [Localizationsᵉ with respectᵉ to maps](orthogonal-factorization-systems.localizations-maps.mdᵉ)
-ᵉ [Localizationsᵉ with respectᵉ to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.mdᵉ)
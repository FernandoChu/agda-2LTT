# Null types

```agda
module orthogonal-factorization-systems.null-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.retracts-of-mapsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universal-property-family-of-fibers-of-mapsᵉ
open import foundation.universal-property-unit-typeᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-mapsᵉ
open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.orthogonal-mapsᵉ
```

</details>

## Idea

Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "nullᵉ at"ᵉ Disambiguation="type"ᵉ Agda=is-nullᵉ}} `Y`,ᵉ orᵉ
{{#conceptᵉ "`Y`-null"ᵉ Disambiguation="type"ᵉ Agda=is-null}},ᵉ ifᵉ theᵉ
[diagonalᵉ map](foundation.diagonal-maps-of-types.mdᵉ)

```text
  Δᵉ : Aᵉ → (Yᵉ → Aᵉ)
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ Theᵉ ideaᵉ isᵉ thatᵉ `A`ᵉ
"observes"ᵉ theᵉ typeᵉ `Y`ᵉ to beᵉ
[contractible](foundation-core.contractible-types.md).ᵉ

## Definitions

### The predicate on a type of being `Y`-null

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) (Aᵉ : UUᵉ l2ᵉ)
  where

  is-nullᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-nullᵉ = is-equivᵉ (diagonal-exponentialᵉ Aᵉ Yᵉ)

  is-prop-is-nullᵉ : is-propᵉ is-nullᵉ
  is-prop-is-nullᵉ = is-property-is-equivᵉ (diagonal-exponentialᵉ Aᵉ Yᵉ)

  is-null-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-null-Propᵉ = is-nullᵉ
  pr2ᵉ is-null-Propᵉ = is-prop-is-nullᵉ
```

## Properties

### Closure under equivalences

Ifᵉ `B`ᵉ isᵉ `Y`-nullᵉ andᵉ weᵉ haveᵉ equivalencesᵉ `Xᵉ ≃ᵉ Y`ᵉ andᵉ `Aᵉ ≃ᵉ B`,ᵉ thenᵉ `A`ᵉ isᵉ
`X`-null.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : UUᵉ l4ᵉ}
  where

  is-null-equivᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) (fᵉ : Aᵉ ≃ᵉ Bᵉ) → is-nullᵉ Yᵉ Bᵉ → is-nullᵉ Xᵉ Aᵉ
  is-null-equivᵉ eᵉ fᵉ Hᵉ =
    is-equiv-htpy-equivᵉ
      ( equiv-precompᵉ eᵉ Aᵉ ∘eᵉ equiv-postcompᵉ Yᵉ (inv-equivᵉ fᵉ) ∘eᵉ (ᵉ_ ,ᵉ Hᵉ) ∘eᵉ fᵉ)
      ( λ xᵉ → eq-htpyᵉ (λ _ → invᵉ (is-retraction-map-inv-equivᵉ fᵉ xᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ}
  where

  is-null-equiv-exponentᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) → is-nullᵉ Yᵉ Aᵉ → is-nullᵉ Xᵉ Aᵉ
  is-null-equiv-exponentᵉ eᵉ Hᵉ =
    is-equiv-compᵉ
      ( precompᵉ (map-equivᵉ eᵉ) Aᵉ)
      ( diagonal-exponentialᵉ Aᵉ Yᵉ)
      ( Hᵉ)
      ( is-equiv-precomp-equivᵉ eᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Yᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  where

  is-null-equiv-baseᵉ : (fᵉ : Aᵉ ≃ᵉ Bᵉ) → is-nullᵉ Yᵉ Bᵉ → is-nullᵉ Yᵉ Aᵉ
  is-null-equiv-baseᵉ fᵉ Hᵉ =
    is-equiv-htpy-equivᵉ
      ( equiv-postcompᵉ Yᵉ (inv-equivᵉ fᵉ) ∘eᵉ (ᵉ_ ,ᵉ Hᵉ) ∘eᵉ fᵉ)
      ( λ bᵉ → eq-htpyᵉ (λ _ → invᵉ (is-retraction-map-inv-equivᵉ fᵉ bᵉ)))
```

### Closure under retracts

Ifᵉ `B`ᵉ isᵉ `Y`-nullᵉ andᵉ `X`ᵉ isᵉ aᵉ retractᵉ ofᵉ `Y`ᵉ andᵉ `A`ᵉ isᵉ aᵉ retractᵉ ofᵉ `B`,ᵉ thenᵉ
`A`ᵉ isᵉ `X`-null.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : UUᵉ l4ᵉ}
  where

  is-null-retractᵉ :
    Xᵉ retract-ofᵉ Yᵉ → Aᵉ retract-ofᵉ Bᵉ → is-nullᵉ Yᵉ Bᵉ → is-nullᵉ Xᵉ Aᵉ
  is-null-retractᵉ eᵉ fᵉ =
    is-equiv-retract-map-is-equivᵉ
      ( diagonal-exponentialᵉ Aᵉ Xᵉ)
      ( diagonal-exponentialᵉ Bᵉ Yᵉ)
      ( retract-map-diagonal-exponential-retractᵉ fᵉ eᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Yᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  where

  is-null-retract-baseᵉ : Aᵉ retract-ofᵉ Bᵉ → is-nullᵉ Yᵉ Bᵉ → is-nullᵉ Yᵉ Aᵉ
  is-null-retract-baseᵉ = is-null-retractᵉ id-retractᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ}
  where

  is-null-retract-exponentᵉ : Xᵉ retract-ofᵉ Yᵉ → is-nullᵉ Yᵉ Aᵉ → is-nullᵉ Xᵉ Aᵉ
  is-null-retract-exponentᵉ eᵉ = is-null-retractᵉ eᵉ id-retractᵉ
```

### A type is `Y`-null if and only if it is local at the terminal projection `Y → unit`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) (Aᵉ : UUᵉ l2ᵉ)
  where

  is-local-terminal-map-is-nullᵉ : is-nullᵉ Yᵉ Aᵉ → is-localᵉ (terminal-mapᵉ Yᵉ) Aᵉ
  is-local-terminal-map-is-nullᵉ =
    is-equiv-compᵉ
      ( diagonal-exponentialᵉ Aᵉ Yᵉ)
      ( map-left-unit-law-function-typeᵉ Aᵉ)
      ( is-equiv-map-left-unit-law-function-typeᵉ Aᵉ)

  is-null-is-local-terminal-mapᵉ : is-localᵉ (terminal-mapᵉ Yᵉ) Aᵉ → is-nullᵉ Yᵉ Aᵉ
  is-null-is-local-terminal-mapᵉ =
    is-equiv-compᵉ
      ( precompᵉ (terminal-mapᵉ Yᵉ) Aᵉ)
      ( map-inv-left-unit-law-function-typeᵉ Aᵉ)
      ( is-equiv-map-inv-left-unit-law-function-typeᵉ Aᵉ)

  equiv-is-local-terminal-map-is-nullᵉ :
    is-nullᵉ Yᵉ Aᵉ ≃ᵉ is-localᵉ (terminal-mapᵉ Yᵉ) Aᵉ
  equiv-is-local-terminal-map-is-nullᵉ =
    equiv-iff-is-propᵉ
      ( is-property-is-equivᵉ (diagonal-exponentialᵉ Aᵉ Yᵉ))
      ( is-property-is-equivᵉ (precompᵉ (terminal-mapᵉ Yᵉ) Aᵉ))
      ( is-local-terminal-map-is-nullᵉ)
      ( is-null-is-local-terminal-mapᵉ)

  equiv-is-null-is-local-terminal-mapᵉ :
    is-localᵉ (terminal-mapᵉ Yᵉ) Aᵉ ≃ᵉ is-nullᵉ Yᵉ Aᵉ
  equiv-is-null-is-local-terminal-mapᵉ =
    inv-equivᵉ equiv-is-local-terminal-map-is-nullᵉ
```

### A type is `Y`-null if and only if the terminal projection of `Y` is orthogonal to the terminal projection of `A`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Yᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ}
  where

  is-null-is-orthogonal-terminal-mapsᵉ :
    is-orthogonalᵉ (terminal-mapᵉ Yᵉ) (terminal-mapᵉ Aᵉ) → is-nullᵉ Yᵉ Aᵉ
  is-null-is-orthogonal-terminal-mapsᵉ Hᵉ =
    is-null-is-local-terminal-mapᵉ Yᵉ Aᵉ
      ( is-local-is-orthogonal-terminal-mapᵉ (terminal-mapᵉ Yᵉ) Hᵉ)

  is-orthogonal-terminal-maps-is-nullᵉ :
    is-nullᵉ Yᵉ Aᵉ → is-orthogonalᵉ (terminal-mapᵉ Yᵉ) (terminal-mapᵉ Aᵉ)
  is-orthogonal-terminal-maps-is-nullᵉ Hᵉ =
    is-orthogonal-is-orthogonal-fiber-condition-right-mapᵉ
      ( terminal-mapᵉ Yᵉ)
      ( terminal-mapᵉ Aᵉ)
      ( λ _ →
        is-equiv-source-is-equiv-target-equiv-arrowᵉ
          ( precompᵉ (terminal-mapᵉ Yᵉ) (fiberᵉ (terminal-mapᵉ Aᵉ) starᵉ))
          ( diagonal-exponentialᵉ Aᵉ Yᵉ)
          ( ( equiv-fiber-terminal-mapᵉ starᵉ) ∘eᵉ
            ( equiv-universal-property-unitᵉ (fiberᵉ (terminal-mapᵉ Aᵉ) starᵉ)) ,ᵉ
            ( equiv-postcompᵉ Yᵉ (equiv-fiber-terminal-mapᵉ starᵉ)) ,ᵉ
            ( refl-htpyᵉ))
          ( Hᵉ))
```

### A type is `f`-local if it is null at every fiber of `f`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Yᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} (fᵉ : Yᵉ → Xᵉ)
  where

  is-local-dependent-type-is-null-fiberᵉ :
    (Aᵉ : Xᵉ → UUᵉ l3ᵉ) →
    ((xᵉ : Xᵉ) → is-nullᵉ (fiberᵉ fᵉ xᵉ) (Aᵉ xᵉ)) → is-local-dependent-typeᵉ fᵉ Aᵉ
  is-local-dependent-type-is-null-fiberᵉ Aᵉ = is-equiv-precomp-Π-fiber-conditionᵉ

  is-local-is-null-fiberᵉ :
    (Aᵉ : UUᵉ l3ᵉ) → ((xᵉ : Xᵉ) → is-nullᵉ (fiberᵉ fᵉ xᵉ) Aᵉ) → is-localᵉ fᵉ Aᵉ
  is-local-is-null-fiberᵉ Aᵉ = is-local-dependent-type-is-null-fiberᵉ (λ _ → Aᵉ)
```
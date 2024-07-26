# `k`-acyclic maps

```agda
module synthetic-homotopy-theory.truncated-acyclic-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.connected-mapsᵉ
open import foundation.connected-typesᵉ
open import foundation.constant-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-epimorphisms-with-respect-to-truncated-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.epimorphisms-with-respect-to-truncated-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.retracts-of-mapsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-equivalencesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.truncationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-cartesian-product-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.codiagonals-of-mapsᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
open import synthetic-homotopy-theory.truncated-acyclic-typesᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ **`k`-acyclic**ᵉ ifᵉ itsᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
[`k`-acyclicᵉ types](synthetic-homotopy-theory.truncated-acyclic-types.md).ᵉ

## Definitions

### The predicate of being a `k`-acyclic map

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-truncated-acyclic-map-Propᵉ : (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-truncated-acyclic-map-Propᵉ fᵉ =
    Π-Propᵉ Bᵉ (λ bᵉ → is-truncated-acyclic-Propᵉ kᵉ (fiberᵉ fᵉ bᵉ))

  is-truncated-acyclic-mapᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-truncated-acyclic-mapᵉ fᵉ = type-Propᵉ (is-truncated-acyclic-map-Propᵉ fᵉ)

  is-prop-is-truncated-acyclic-mapᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-truncated-acyclic-mapᵉ fᵉ)
  is-prop-is-truncated-acyclic-mapᵉ fᵉ =
    is-prop-type-Propᵉ (is-truncated-acyclic-map-Propᵉ fᵉ)
```

## Properties

### A map is `k`-acyclic if and only if it is an [epimorphism with respect to `k`-types](foundation.epimorphisms-with-respect-to-truncated-types.md)

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ → is-truncated-acyclic-mapᵉ kᵉ fᵉ
  is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ eᵉ bᵉ =
    is-connected-equivᵉ
      ( equiv-fiber-codiagonal-map-suspension-fiberᵉ fᵉ bᵉ)
      ( is-connected-codiagonal-map-is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ eᵉ bᵉ)

  is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ :
    is-truncated-acyclic-mapᵉ kᵉ fᵉ → is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ acᵉ =
    is-epimorphism-is-connected-codiagonal-map-Truncated-Typeᵉ kᵉ fᵉ
      ( λ bᵉ →
        is-connected-equiv'ᵉ
          ( equiv-fiber-codiagonal-map-suspension-fiberᵉ fᵉ bᵉ)
          ( acᵉ bᵉ))
```

### A type is `k`-acyclic if and only if its terminal map is a `k`-acyclic map

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ lᵉ)
  where

  is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ :
    is-truncated-acyclicᵉ kᵉ Aᵉ →
    is-truncated-acyclic-mapᵉ kᵉ (terminal-mapᵉ Aᵉ)
  is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ acᵉ uᵉ =
    is-truncated-acyclic-equivᵉ (equiv-fiber-terminal-mapᵉ uᵉ) acᵉ

  is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ :
    is-truncated-acyclic-mapᵉ kᵉ (terminal-mapᵉ Aᵉ) →
    is-truncated-acyclicᵉ kᵉ Aᵉ
  is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ acᵉ =
    is-truncated-acyclic-equivᵉ inv-equiv-fiber-terminal-map-starᵉ (acᵉ starᵉ)
```

### A type is `k`-acyclic if and only if the constant map from any `k`-type is an embedding

Moreᵉ precisely,ᵉ `A`ᵉ isᵉ `k`-acyclicᵉ ifᵉ andᵉ onlyᵉ ifᵉ forᵉ allᵉ `k`-typesᵉ `X`,ᵉ theᵉ mapᵉ

```text
  Δᵉ : Xᵉ → (Aᵉ → Xᵉ)
```

isᵉ anᵉ embedding.ᵉ

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ lᵉ)
  where

  is-emb-diagonal-exponential-is-truncated-acyclic-Truncated-Typeᵉ :
    is-truncated-acyclicᵉ kᵉ Aᵉ →
    {l'ᵉ : Level} (Xᵉ : Truncated-Typeᵉ l'ᵉ kᵉ) →
    is-embᵉ (diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ)
  is-emb-diagonal-exponential-is-truncated-acyclic-Truncated-Typeᵉ acᵉ Xᵉ =
    is-emb-compᵉ
      ( precompᵉ (terminal-mapᵉ Aᵉ) (type-Truncated-Typeᵉ Xᵉ))
      ( map-inv-left-unit-law-function-typeᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ
        ( terminal-mapᵉ Aᵉ)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ Aᵉ acᵉ)
        ( Xᵉ))
      ( is-emb-is-equivᵉ
        ( is-equiv-map-inv-left-unit-law-function-typeᵉ (type-Truncated-Typeᵉ Xᵉ)))

  is-truncated-acyclic-is-emb-diagonal-exponential-Truncated-Typeᵉ :
    ({l'ᵉ : Level} (Xᵉ : Truncated-Typeᵉ l'ᵉ kᵉ) →
    is-embᵉ (diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ)) →
    is-truncated-acyclicᵉ kᵉ Aᵉ
  is-truncated-acyclic-is-emb-diagonal-exponential-Truncated-Typeᵉ eᵉ =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ Aᵉ
      ( is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ
        ( terminal-mapᵉ Aᵉ)
        ( λ Xᵉ →
          is-emb-triangle-is-equiv'ᵉ
            ( diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ)
            ( precompᵉ (terminal-mapᵉ Aᵉ) (type-Truncated-Typeᵉ Xᵉ))
            ( map-inv-left-unit-law-function-typeᵉ (type-Truncated-Typeᵉ Xᵉ))
            ( refl-htpyᵉ)
            ( is-equiv-map-inv-left-unit-law-function-typeᵉ
              ( type-Truncated-Typeᵉ Xᵉ))
            ( eᵉ Xᵉ)))
```

### A type is `k`-acyclic if and only if the constant map from any identity type of any `k`-type is an equivalence

Moreᵉ precisely,ᵉ `A`ᵉ isᵉ `k`-acyclicᵉ ifᵉ andᵉ onlyᵉ ifᵉ forᵉ allᵉ `k`-typesᵉ `X`ᵉ andᵉ
elementsᵉ `x,yᵉ : X`,ᵉ theᵉ mapᵉ

```text
  Δᵉ : (xᵉ ＝ᵉ yᵉ) → (Aᵉ → xᵉ ＝ᵉ yᵉ)
```

isᵉ anᵉ equivalence.ᵉ

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ lᵉ)
  where

  is-equiv-diagonal-exponential-Id-is-acyclic-Truncated-Typeᵉ :
    is-truncated-acyclicᵉ kᵉ Aᵉ →
    {l'ᵉ : Level} (Xᵉ : Truncated-Typeᵉ l'ᵉ kᵉ) (xᵉ yᵉ : type-Truncated-Typeᵉ Xᵉ) →
    is-equivᵉ (diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ)
  is-equiv-diagonal-exponential-Id-is-acyclic-Truncated-Typeᵉ acᵉ Xᵉ xᵉ yᵉ =
    is-equiv-htpyᵉ
      ( htpy-eqᵉ ∘ᵉ apᵉ (diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ) {xᵉ} {yᵉ})
      ( htpy-ap-diagonal-exponential-htpy-eq-diagonal-exponential-Idᵉ xᵉ yᵉ Aᵉ)
      ( is-equiv-compᵉ
        ( htpy-eqᵉ)
        ( apᵉ (diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ))
        ( is-emb-diagonal-exponential-is-truncated-acyclic-Truncated-Typeᵉ
          ( Aᵉ)
          ( acᵉ)
          ( Xᵉ)
          ( xᵉ)
          ( yᵉ))
        ( funextᵉ
          ( diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ xᵉ)
          ( diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ yᵉ)))

  is-truncated-acyclic-is-equiv-diagonal-exponential-Id-Truncated-Typeᵉ :
    ( {l'ᵉ : Level} (Xᵉ : Truncated-Typeᵉ l'ᵉ kᵉ) (xᵉ yᵉ : type-Truncated-Typeᵉ Xᵉ) →
      is-equivᵉ (diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ)) →
    is-truncated-acyclicᵉ kᵉ Aᵉ
  is-truncated-acyclic-is-equiv-diagonal-exponential-Id-Truncated-Typeᵉ hᵉ =
    is-truncated-acyclic-is-emb-diagonal-exponential-Truncated-Typeᵉ Aᵉ
      ( λ Xᵉ xᵉ yᵉ →
        is-equiv-right-factorᵉ
          ( htpy-eqᵉ)
          ( apᵉ (diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ))
          ( funextᵉ
            ( diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ xᵉ)
            ( diagonal-exponentialᵉ (type-Truncated-Typeᵉ Xᵉ) Aᵉ yᵉ))
          ( is-equiv-htpyᵉ
            ( diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ)
            ( htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eqᵉ
              ( xᵉ)
              ( yᵉ)
              ( Aᵉ))
            ( hᵉ Xᵉ xᵉ yᵉ)))
```

### A map is `k`-acyclic if and only if it is an [dependent `k`-epimorphism](foundation.dependent-epimorphisms-with-respect-to-truncated-types.md)

Theᵉ proofᵉ isᵉ similarᵉ to thatᵉ ofᵉ dependentᵉ epimorphismsᵉ andᵉ
[acyclic-maps](synthetic-homotopy-theory.acyclic-maps.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-truncated-acyclic-map-is-dependent-epimorphism-Truncated-Typeᵉ :
    is-dependent-epimorphism-Truncated-Typeᵉ kᵉ fᵉ → is-truncated-acyclic-mapᵉ kᵉ fᵉ
  is-truncated-acyclic-map-is-dependent-epimorphism-Truncated-Typeᵉ eᵉ =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ fᵉ
      ( is-epimorphism-is-dependent-epimorphism-Truncated-Typeᵉ fᵉ eᵉ)

  is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ :
    is-truncated-acyclic-mapᵉ kᵉ fᵉ → is-dependent-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ acᵉ Cᵉ =
    is-emb-compᵉ
      ( ( precomp-Πᵉ
          ( map-inv-equiv-total-fiberᵉ fᵉ)
          ( type-Truncated-Typeᵉ ∘ᵉ Cᵉ ∘ᵉ pr1ᵉ)) ∘ᵉ
        ( ind-Σᵉ))
      ( map-Πᵉ
        ( λ bᵉ → diagonal-exponentialᵉ (type-Truncated-Typeᵉ (Cᵉ bᵉ)) (fiberᵉ fᵉ bᵉ)))
      ( is-emb-compᵉ
        ( precomp-Πᵉ
          ( map-inv-equiv-total-fiberᵉ fᵉ)
          ( type-Truncated-Typeᵉ ∘ᵉ Cᵉ ∘ᵉ pr1ᵉ))
        ( ind-Σᵉ)
        ( is-emb-is-equivᵉ
          ( is-equiv-precomp-Π-is-equivᵉ
            ( is-equiv-map-inv-equiv-total-fiberᵉ fᵉ)
              (type-Truncated-Typeᵉ ∘ᵉ Cᵉ ∘ᵉ pr1ᵉ)))
        ( is-emb-is-equivᵉ is-equiv-ind-Σᵉ))
      ( is-emb-map-Πᵉ
        ( λ bᵉ →
          is-emb-diagonal-exponential-is-truncated-acyclic-Truncated-Typeᵉ
            ( fiberᵉ fᵉ bᵉ)
            ( acᵉ bᵉ)
            ( Cᵉ bᵉ)))
```

Inᵉ particular,ᵉ everyᵉ `k`-epimorphismᵉ isᵉ actuallyᵉ aᵉ dependentᵉ `k`-epimorphism.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-dependent-epimorphism-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    is-dependent-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-dependent-epimorphism-is-epimorphism-Truncated-Typeᵉ eᵉ =
    is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ fᵉ
      ( is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ fᵉ eᵉ)
```

### The class of `k`-acyclic maps is closed under composition and has the right cancellation property

Sinceᵉ theᵉ `k`-acyclicᵉ mapsᵉ areᵉ preciselyᵉ theᵉ `k`-epimorphismsᵉ thisᵉ followsᵉ fromᵉ
theᵉ correspondingᵉ factsᵉ aboutᵉ
[`k`-epimorphisms](foundation.epimorphisms-with-respect-to-truncated-types.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ)
  where

  is-truncated-acyclic-map-compᵉ :
    is-truncated-acyclic-mapᵉ kᵉ gᵉ →
    is-truncated-acyclic-mapᵉ kᵉ fᵉ →
    is-truncated-acyclic-mapᵉ kᵉ (gᵉ ∘ᵉ fᵉ)
  is-truncated-acyclic-map-compᵉ agᵉ afᵉ =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ (gᵉ ∘ᵉ fᵉ)
      ( is-epimorphism-comp-Truncated-Typeᵉ kᵉ gᵉ fᵉ
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ gᵉ agᵉ)
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ fᵉ afᵉ))

  is-truncated-acyclic-map-left-factorᵉ :
    is-truncated-acyclic-mapᵉ kᵉ (gᵉ ∘ᵉ fᵉ) →
    is-truncated-acyclic-mapᵉ kᵉ fᵉ →
    is-truncated-acyclic-mapᵉ kᵉ gᵉ
  is-truncated-acyclic-map-left-factorᵉ acᵉ afᵉ =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ gᵉ
      ( is-epimorphism-left-factor-Truncated-Typeᵉ kᵉ gᵉ fᵉ
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ (gᵉ ∘ᵉ fᵉ) acᵉ)
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ fᵉ afᵉ))
```

### Every `k`-connected map is `(k+1)`-acyclic

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-truncated-acyclic-map-succ-is-connected-mapᵉ :
    is-connected-mapᵉ kᵉ fᵉ → is-truncated-acyclic-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ
  is-truncated-acyclic-map-succ-is-connected-mapᵉ cᵉ bᵉ =
    is-truncated-acyclic-succ-is-connectedᵉ (cᵉ bᵉ)
```

Inᵉ particular,ᵉ theᵉ unitᵉ ofᵉ theᵉ `k`-truncationᵉ isᵉ `(k+1)`-acyclicᵉ

```agda
is-truncated-acyclic-map-succ-unit-truncᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ lᵉ) →
  is-truncated-acyclic-mapᵉ (succ-𝕋ᵉ kᵉ) (unit-truncᵉ {Aᵉ = Aᵉ})
is-truncated-acyclic-map-succ-unit-truncᵉ {kᵉ = kᵉ} Aᵉ =
  is-truncated-acyclic-map-succ-is-connected-mapᵉ
    ( unit-truncᵉ)
    ( is-connected-map-unit-truncᵉ kᵉ)
```

### A type is `(k+1)`-acyclic if and only if its `k`-truncation is

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ lᵉ)
  where

  is-truncated-acyclic-succ-is-truncated-acyclic-succ-type-truncᵉ :
    is-truncated-acyclicᵉ (succ-𝕋ᵉ kᵉ) (type-truncᵉ kᵉ Aᵉ) →
    is-truncated-acyclicᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
  is-truncated-acyclic-succ-is-truncated-acyclic-succ-type-truncᵉ acᵉ =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ Aᵉ
      ( is-truncated-acyclic-map-compᵉ
        ( terminal-mapᵉ (type-truncᵉ kᵉ Aᵉ))
        ( unit-truncᵉ)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ
          ( type-truncᵉ kᵉ Aᵉ)
          ( acᵉ))
        ( is-truncated-acyclic-map-succ-unit-truncᵉ Aᵉ))

  is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succᵉ :
    is-truncated-acyclicᵉ (succ-𝕋ᵉ kᵉ) Aᵉ →
    is-truncated-acyclicᵉ (succ-𝕋ᵉ kᵉ) (type-truncᵉ kᵉ Aᵉ)
  is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succᵉ acᵉ =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ
      ( type-truncᵉ kᵉ Aᵉ)
      ( is-truncated-acyclic-map-left-factorᵉ
        ( terminal-mapᵉ (type-truncᵉ kᵉ Aᵉ))
        ( unit-truncᵉ)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ Aᵉ acᵉ)
        ( is-truncated-acyclic-map-succ-unit-truncᵉ Aᵉ))
```

### Every `k`-equivalence is `k`-acyclic

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-truncated-acyclic-map-is-truncation-equivalenceᵉ :
    is-truncation-equivalenceᵉ kᵉ fᵉ → is-truncated-acyclic-mapᵉ kᵉ fᵉ
  is-truncated-acyclic-map-is-truncation-equivalenceᵉ eᵉ =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ fᵉ
      ( λ Cᵉ →
        is-emb-is-equivᵉ
          ( is-equiv-precomp-is-truncation-equivalenceᵉ kᵉ fᵉ eᵉ Cᵉ))
```

### `k`-acyclic maps are closed under pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  is-truncated-acyclic-map-vertical-map-cone-is-pullbackᵉ :
    is-pullbackᵉ fᵉ gᵉ cᵉ →
    is-truncated-acyclic-mapᵉ kᵉ gᵉ →
    is-truncated-acyclic-mapᵉ kᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ)
  is-truncated-acyclic-map-vertical-map-cone-is-pullbackᵉ pbᵉ acᵉ aᵉ =
    is-truncated-acyclic-equivᵉ
      ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ aᵉ ,ᵉ
        is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ fᵉ gᵉ cᵉ pbᵉ aᵉ)
      ( acᵉ (fᵉ aᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  is-truncated-acyclic-map-horizontal-map-cone-is-pullbackᵉ :
    is-pullbackᵉ fᵉ gᵉ cᵉ →
    is-truncated-acyclic-mapᵉ kᵉ fᵉ →
    is-truncated-acyclic-mapᵉ kᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
  is-truncated-acyclic-map-horizontal-map-cone-is-pullbackᵉ pbᵉ =
    is-truncated-acyclic-map-vertical-map-cone-is-pullbackᵉ gᵉ fᵉ
      ( swap-coneᵉ fᵉ gᵉ cᵉ)
      ( is-pullback-swap-coneᵉ fᵉ gᵉ cᵉ pbᵉ)
```

### `k`-acyclic types are closed under dependent pair types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  is-truncated-acyclic-Σᵉ :
    is-truncated-acyclicᵉ kᵉ Aᵉ →
    ((aᵉ : Aᵉ) → is-truncated-acyclicᵉ kᵉ (Bᵉ aᵉ)) →
    is-truncated-acyclicᵉ kᵉ (Σᵉ Aᵉ Bᵉ)
  is-truncated-acyclic-Σᵉ ac-Aᵉ ac-Bᵉ =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ
      ( Σᵉ Aᵉ Bᵉ)
      ( is-truncated-acyclic-map-compᵉ
        ( terminal-mapᵉ Aᵉ)
        ( pr1ᵉ)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ Aᵉ ac-Aᵉ)
        ( λ aᵉ → is-truncated-acyclic-equivᵉ (equiv-fiber-pr1ᵉ Bᵉ aᵉ) (ac-Bᵉ aᵉ)))
```

### `k`-acyclic types are closed under binary products

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  is-truncated-acyclic-productᵉ :
    is-truncated-acyclicᵉ kᵉ Aᵉ →
    is-truncated-acyclicᵉ kᵉ Bᵉ →
    is-truncated-acyclicᵉ kᵉ (Aᵉ ×ᵉ Bᵉ)
  is-truncated-acyclic-productᵉ ac-Aᵉ ac-Bᵉ =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ
      ( Aᵉ ×ᵉ Bᵉ)
      ( is-truncated-acyclic-map-compᵉ
        ( terminal-mapᵉ Bᵉ)
        ( pr2ᵉ)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ Bᵉ ac-Bᵉ)
        ( is-truncated-acyclic-map-horizontal-map-cone-is-pullbackᵉ
          ( terminal-mapᵉ Aᵉ)
          ( terminal-mapᵉ Bᵉ)
          ( cone-cartesian-productᵉ Aᵉ Bᵉ)
          ( is-pullback-cartesian-productᵉ Aᵉ Bᵉ)
          ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ Aᵉ ac-Aᵉ)))
```

### Inhabited, locally `k`-acyclic types are `k`-acyclic

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ lᵉ)
  where

  is-truncated-acyclic-inhabited-is-truncated-acyclic-Idᵉ :
    is-inhabitedᵉ Aᵉ →
    ((aᵉ bᵉ : Aᵉ) → is-truncated-acyclicᵉ kᵉ (aᵉ ＝ᵉ bᵉ)) →
    is-truncated-acyclicᵉ kᵉ Aᵉ
  is-truncated-acyclic-inhabited-is-truncated-acyclic-Idᵉ hᵉ l-acᵉ =
    apply-universal-property-trunc-Propᵉ hᵉ
      ( is-truncated-acyclic-Propᵉ kᵉ Aᵉ)
      ( λ aᵉ →
        is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ Aᵉ
          ( is-truncated-acyclic-map-left-factorᵉ
            ( terminal-mapᵉ Aᵉ)
            ( pointᵉ aᵉ)
            ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ
              ( unitᵉ)
              ( is-truncated-acyclic-unitᵉ))
            ( λ bᵉ →
              is-truncated-acyclic-equivᵉ
                ( compute-fiber-pointᵉ aᵉ bᵉ)
                ( l-acᵉ aᵉ bᵉ))))
```

### `k`-acyclic maps are closed under retracts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-truncated-acyclic-map-retract-ofᵉ :
    fᵉ retract-of-mapᵉ gᵉ →
    is-truncated-acyclic-mapᵉ kᵉ gᵉ →
    is-truncated-acyclic-mapᵉ kᵉ fᵉ
  is-truncated-acyclic-map-retract-ofᵉ Rᵉ acᵉ bᵉ =
    is-truncated-acyclic-retract-ofᵉ
      ( retract-fiber-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ)
      ( acᵉ (map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
```

### `k`-acyclic maps are closed under pushouts

**Proof:**ᵉ Weᵉ considerᵉ theᵉ pushoutᵉ squaresᵉ

```text
        gᵉ          jᵉ
   Sᵉ ------->ᵉ Bᵉ ------->ᵉ Cᵉ
   |          |          |
 fᵉ |          | jᵉ        | inrᵉ
   ∨ᵉ        ⌜ᵉ ∨ᵉ        ⌜ᵉ ∨ᵉ
   Aᵉ ------->ᵉ Cᵉ ------->ᵉ ∙ᵉ
        iᵉ          inlᵉ
```

Weᵉ assumeᵉ thatᵉ `f`ᵉ isᵉ `k`-acyclicᵉ andᵉ weᵉ wantᵉ to proveᵉ thatᵉ `j`ᵉ isᵉ too.ᵉ Forᵉ
this,ᵉ itᵉ sufficesᵉ to showᵉ thatᵉ forᵉ anyᵉ `k`-typeᵉ `X`,ᵉ theᵉ secondᵉ projectionᵉ
`coconeᵉ jᵉ jᵉ Xᵉ → (Cᵉ → X)`ᵉ isᵉ anᵉ equivalence,ᵉ asᵉ shownᵉ in theᵉ fileᵉ onᵉ
[epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.md).ᵉ

Forᵉ this,ᵉ weᵉ useᵉ theᵉ followingᵉ commutativeᵉ diagramᵉ

```text
                      ≃ᵉ
   (∙ᵉ → Xᵉ) ------------------------>ᵉ coconeᵉ fᵉ (jᵉ ∘ᵉ gᵉ) Xᵉ
      |      (byᵉ pushoutᵉ pastingᵉ)            |
      |                                      |
    ≃ᵉ | (universalᵉ                           | vertical-map-coconeᵉ
      |  propertyᵉ)                           | (secondᵉ projectionᵉ)
      ∨ᵉ                                      ∨ᵉ
 coconeᵉ jᵉ jᵉ Xᵉ -------------------------->ᵉ (Cᵉ → Xᵉ)
                 vertical-map-coconeᵉ
                 (secondᵉ projectionᵉ)
```

where weᵉ firstᵉ showᵉ theᵉ rightᵉ mapᵉ to beᵉ anᵉ equivalenceᵉ using thatᵉ `f`ᵉ isᵉ
`k`-acyclic.ᵉ

Asᵉ forᵉ [acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.md),ᵉ weᵉ useᵉ theᵉ
followingᵉ equivalencesᵉ forᵉ thatᵉ purposeᵉ:

```text
          cocone-mapᵉ fᵉ (jᵉ ∘ᵉ gᵉ)
 (Cᵉ → Xᵉ) ----------------------->ᵉ coconeᵉ fᵉ (jᵉ ∘ᵉ gᵉ) Xᵉ
                               ̇=ᵉ Σᵉ (lᵉ : Aᵉ → Xᵉ) ,ᵉ
                                 Σᵉ (rᵉ : Cᵉ → Xᵉ) ,ᵉ lᵉ ∘ᵉ fᵉ ~ᵉ rᵉ ∘ᵉ jᵉ ∘ᵉ gᵉ
       (usingᵉ theᵉ leftᵉ squareᵉ)
                               ≃ᵉ Σᵉ (lᵉ : Aᵉ → Xᵉ) ,ᵉ
                                 Σᵉ (rᵉ : Cᵉ → Xᵉ) ,ᵉ lᵉ ∘ᵉ fᵉ ~ᵉ rᵉ ∘ᵉ iᵉ ∘ᵉ fᵉ
 (sinceᵉ fᵉ isᵉ `k`-acyclic/epicᵉ)
                               ≃ᵉ Σᵉ (lᵉ : Aᵉ → Xᵉ) ,ᵉ Σᵉ (rᵉ : Cᵉ → Xᵉ) ,ᵉ lᵉ ~ᵉ rᵉ ∘ᵉ iᵉ
                               ≃ᵉ Σᵉ (rᵉ : Cᵉ → Xᵉ) ,ᵉ Σᵉ (lᵉ : Aᵉ → Xᵉ) ,ᵉ lᵉ ~ᵉ rᵉ ∘ᵉ iᵉ
        (contractingᵉ atᵉ rᵉ ∘ᵉ iᵉ)
                               ≃ᵉ (Cᵉ → Xᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {kᵉ : 𝕋ᵉ} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  {Cᵉ : UUᵉ l4ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Cᵉ)
  where

  equiv-cocone-postcomp-vertical-map-cocone-Truncated-Typeᵉ :
    is-truncated-acyclic-mapᵉ kᵉ fᵉ →
    {l5ᵉ : Level} (Xᵉ : Truncated-Typeᵉ l5ᵉ kᵉ) →
    coconeᵉ fᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ gᵉ) (type-Truncated-Typeᵉ Xᵉ) ≃ᵉ
    (Cᵉ → type-Truncated-Typeᵉ Xᵉ)
  equiv-cocone-postcomp-vertical-map-cocone-Truncated-Typeᵉ acᵉ Xᵉ =
    equivalence-reasoningᵉ
        coconeᵉ fᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ gᵉ) (type-Truncated-Typeᵉ Xᵉ)
      ≃ᵉ coconeᵉ fᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ) (type-Truncated-Typeᵉ Xᵉ)
        byᵉ
          equiv-totᵉ
          ( λ uᵉ →
            equiv-totᵉ
              ( λ vᵉ →
                equiv-concat-htpy'ᵉ
                  ( uᵉ ∘ᵉ fᵉ)
                  ( λ sᵉ → apᵉ vᵉ (inv-htpyᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ) sᵉ))))
      ≃ᵉ Σᵉ ( Aᵉ → type-Truncated-Typeᵉ Xᵉ)
          ( λ uᵉ →
            Σᵉ ( Cᵉ → type-Truncated-Typeᵉ Xᵉ)
              ( λ vᵉ → uᵉ ∘ᵉ fᵉ ＝ᵉ vᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ))
        byᵉ equiv-totᵉ ( λ uᵉ → equiv-totᵉ ( λ vᵉ → equiv-eq-htpyᵉ))
      ≃ᵉ Σᵉ ( Aᵉ → type-Truncated-Typeᵉ Xᵉ)
          ( λ uᵉ →
            Σᵉ ( Cᵉ → type-Truncated-Typeᵉ Xᵉ)
              ( λ vᵉ → uᵉ ＝ᵉ vᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ))
        byᵉ
          equiv-totᵉ
          ( λ uᵉ →
            equiv-totᵉ
              ( λ vᵉ →
                inv-equiv-ap-is-embᵉ
                  ( is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ
                    ( fᵉ)
                    ( acᵉ)
                    ( Xᵉ))))
      ≃ᵉ Σᵉ ( Cᵉ → type-Truncated-Typeᵉ Xᵉ)
          ( λ vᵉ →
            Σᵉ ( Aᵉ → type-Truncated-Typeᵉ Xᵉ)
              ( λ uᵉ → uᵉ ＝ᵉ vᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ))
        byᵉ
          equiv-left-swap-Σᵉ
      ≃ᵉ (Cᵉ → type-Truncated-Typeᵉ Xᵉ)
        byᵉ
          equiv-pr1ᵉ (λ vᵉ → is-torsorial-Id'ᵉ (vᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ))

  is-truncated-acyclic-map-vertical-map-cocone-is-pushoutᵉ :
    is-pushoutᵉ fᵉ gᵉ cᵉ →
    is-truncated-acyclic-mapᵉ kᵉ fᵉ →
    is-truncated-acyclic-mapᵉ kᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
  is-truncated-acyclic-map-vertical-map-cocone-is-pushoutᵉ poᵉ acᵉ =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ
      ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( is-epimorphism-is-equiv-vertical-map-cocone-Truncated-Typeᵉ kᵉ
        ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
        ( λ Xᵉ →
          is-equiv-bottom-is-equiv-top-squareᵉ
            ( cocone-mapᵉ
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( cocone-pushoutᵉ
                ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)))
            ( map-equivᵉ
              ( equiv-cocone-postcomp-vertical-map-cocone-Truncated-Typeᵉ acᵉ Xᵉ))
            ( cocone-mapᵉ fᵉ
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ gᵉ)
              ( cocone-comp-horizontalᵉ fᵉ gᵉ
                ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                ( cᵉ)
                ( cocone-pushoutᵉ
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ))))
            ( vertical-map-coconeᵉ
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ))
            ( refl-htpyᵉ)
            ( up-pushoutᵉ
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( type-Truncated-Typeᵉ Xᵉ))
            ( is-equiv-map-equivᵉ
              ( equiv-cocone-postcomp-vertical-map-cocone-Truncated-Typeᵉ acᵉ Xᵉ))
            ( universal-property-pushout-rectangle-universal-property-pushout-rightᵉ
              ( fᵉ)
              ( gᵉ)
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( cᵉ)
              ( cocone-pushoutᵉ
                ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ))
              ( universal-property-pushout-is-pushoutᵉ fᵉ gᵉ cᵉ poᵉ)
              ( up-pushoutᵉ
                ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ))
              ( type-Truncated-Typeᵉ Xᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {kᵉ : 𝕋ᵉ} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  {Cᵉ : UUᵉ l4ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Cᵉ)
  where

  is-truncated-acyclic-map-horizontal-map-cocone-is-pushoutᵉ :
    is-pushoutᵉ fᵉ gᵉ cᵉ →
    is-truncated-acyclic-mapᵉ kᵉ gᵉ →
    is-truncated-acyclic-mapᵉ kᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
  is-truncated-acyclic-map-horizontal-map-cocone-is-pushoutᵉ poᵉ =
    is-truncated-acyclic-map-vertical-map-cocone-is-pushoutᵉ gᵉ fᵉ
      ( swap-coconeᵉ fᵉ gᵉ Cᵉ cᵉ)
      ( is-pushout-swap-cocone-is-pushoutᵉ fᵉ gᵉ Cᵉ cᵉ poᵉ)
```

## See also

-ᵉ [Acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.mdᵉ)
-ᵉ [Acyclicᵉ types](synthetic-homotopy-theory.acyclic-types.mdᵉ)
-ᵉ [`k`-acyclicᵉ types](synthetic-homotopy-theory.truncated-acyclic-types.mdᵉ)
-ᵉ [Dependentᵉ epimorphisms](foundation.dependent-epimorphisms.mdᵉ)
-ᵉ [Epimorphisms](foundation.epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)
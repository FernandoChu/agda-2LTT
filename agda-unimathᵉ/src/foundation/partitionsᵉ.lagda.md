# Partitions

```agda
module foundation.partitionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.conjunctionᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.fiber-inclusionsᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.sigma-decompositionsᵉ
open import foundation.small-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ partitionᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ subsetᵉ `P`ᵉ ofᵉ theᵉ typeᵉ ofᵉ inhabitedᵉ subsetsᵉ ofᵉ
`A`ᵉ suchᵉ thatᵉ forᵉ eachᵉ `aᵉ : A`ᵉ theᵉ typeᵉ

```text
  Σᵉ (Qᵉ : inhabited-subtypeᵉ (A)),ᵉ P(Qᵉ) ×ᵉ Q(aᵉ)
```

isᵉ contractible.ᵉ Inᵉ otherᵉ words,ᵉ itᵉ isᵉ aᵉ collectionᵉ `P`ᵉ ofᵉ inhabitedᵉ subtypesᵉ ofᵉ
`A`ᵉ suchᵉ thatᵉ eachᵉ elementᵉ ofᵉ `A`ᵉ isᵉ in aᵉ uniqueᵉ inhabitedᵉ subtypeᵉ in `P`.ᵉ

## Definition

```agda
is-partition-Propᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l3ᵉ (inhabited-subtypeᵉ l2ᵉ Aᵉ)) →
  Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
is-partition-Propᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ} Pᵉ =
  Π-Propᵉ Aᵉ
    ( λ xᵉ →
      is-contr-Propᵉ
        ( Σᵉ ( type-subtypeᵉ Pᵉ)
            ( λ Qᵉ → is-in-inhabited-subtypeᵉ (inclusion-subtypeᵉ Pᵉ Qᵉ) xᵉ)))

is-partitionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l3ᵉ (inhabited-subtypeᵉ l2ᵉ Aᵉ)) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
is-partitionᵉ Pᵉ = type-Propᵉ (is-partition-Propᵉ Pᵉ)

partitionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
partitionᵉ {l1ᵉ} l2ᵉ l3ᵉ Aᵉ = type-subtypeᵉ (is-partition-Propᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ})

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  subtype-partitionᵉ : subtypeᵉ l3ᵉ (inhabited-subtypeᵉ l2ᵉ Aᵉ)
  subtype-partitionᵉ = pr1ᵉ Pᵉ

  is-partition-subtype-partitionᵉ : is-partitionᵉ subtype-partitionᵉ
  is-partition-subtype-partitionᵉ = pr2ᵉ Pᵉ

  is-block-partitionᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ → UUᵉ l3ᵉ
  is-block-partitionᵉ = is-in-subtypeᵉ subtype-partitionᵉ

  is-prop-is-block-partitionᵉ :
    (Qᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ) → is-propᵉ (is-block-partitionᵉ Qᵉ)
  is-prop-is-block-partitionᵉ = is-prop-is-in-subtypeᵉ subtype-partitionᵉ
```

Weᵉ introduceᵉ theᵉ typeᵉ ofᵉ blocksᵉ ofᵉ aᵉ partition.ᵉ However,ᵉ weᵉ willᵉ soonᵉ beᵉ ableᵉ to
reduceᵉ theᵉ universeᵉ levelᵉ ofᵉ thisᵉ type.ᵉ Thereforeᵉ weᵉ callᵉ thisᵉ typeᵉ ofᵉ blocksᵉ
`large`.ᵉ

```agda
  block-partition-Large-Typeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  block-partition-Large-Typeᵉ = type-subtypeᵉ subtype-partitionᵉ

  inhabited-subtype-block-partition-Large-Typeᵉ :
    block-partition-Large-Typeᵉ → inhabited-subtypeᵉ l2ᵉ Aᵉ
  inhabited-subtype-block-partition-Large-Typeᵉ =
    inclusion-subtypeᵉ subtype-partitionᵉ

  is-emb-inhabited-subtype-block-partition-Large-Typeᵉ :
    is-embᵉ inhabited-subtype-block-partition-Large-Typeᵉ
  is-emb-inhabited-subtype-block-partition-Large-Typeᵉ =
    is-emb-inclusion-subtypeᵉ subtype-partitionᵉ

  emb-inhabited-subtype-block-partition-Large-Typeᵉ :
    block-partition-Large-Typeᵉ ↪ᵉ inhabited-subtypeᵉ l2ᵉ Aᵉ
  emb-inhabited-subtype-block-partition-Large-Typeᵉ =
    emb-subtypeᵉ subtype-partitionᵉ

  is-block-inhabited-subtype-block-partition-Large-Typeᵉ :
    (Bᵉ : block-partition-Large-Typeᵉ) →
    is-block-partitionᵉ (inhabited-subtype-block-partition-Large-Typeᵉ Bᵉ)
  is-block-inhabited-subtype-block-partition-Large-Typeᵉ =
    is-in-subtype-inclusion-subtypeᵉ subtype-partitionᵉ

  subtype-block-partition-Large-Typeᵉ :
    block-partition-Large-Typeᵉ → subtypeᵉ l2ᵉ Aᵉ
  subtype-block-partition-Large-Typeᵉ =
    subtype-inhabited-subtypeᵉ ∘ᵉ inhabited-subtype-block-partition-Large-Typeᵉ

  is-inhabited-subtype-block-partition-Large-Typeᵉ :
    (Bᵉ : block-partition-Large-Typeᵉ) →
    is-inhabited-subtypeᵉ (subtype-block-partition-Large-Typeᵉ Bᵉ)
  is-inhabited-subtype-block-partition-Large-Typeᵉ Bᵉ =
    is-inhabited-subtype-inhabited-subtypeᵉ
      ( inhabited-subtype-block-partition-Large-Typeᵉ Bᵉ)

  type-block-partition-Large-Typeᵉ : block-partition-Large-Typeᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-block-partition-Large-Typeᵉ Qᵉ =
    type-inhabited-subtypeᵉ (inhabited-subtype-block-partition-Large-Typeᵉ Qᵉ)

  inhabited-type-block-partition-Large-Typeᵉ :
    block-partition-Large-Typeᵉ → Inhabited-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  inhabited-type-block-partition-Large-Typeᵉ Qᵉ =
    inhabited-type-inhabited-subtypeᵉ
      ( inhabited-subtype-block-partition-Large-Typeᵉ Qᵉ)

  is-in-block-partition-Large-Typeᵉ : block-partition-Large-Typeᵉ → Aᵉ → UUᵉ l2ᵉ
  is-in-block-partition-Large-Typeᵉ Qᵉ =
    is-in-inhabited-subtypeᵉ (inhabited-subtype-block-partition-Large-Typeᵉ Qᵉ)

  is-prop-is-in-block-partition-Large-Typeᵉ :
    (Qᵉ : block-partition-Large-Typeᵉ) (aᵉ : Aᵉ) →
    is-propᵉ (is-in-block-partition-Large-Typeᵉ Qᵉ aᵉ)
  is-prop-is-in-block-partition-Large-Typeᵉ Qᵉ =
    is-prop-is-in-inhabited-subtypeᵉ
      ( inhabited-subtype-block-partition-Large-Typeᵉ Qᵉ)

  large-block-element-partitionᵉ : Aᵉ → block-partition-Large-Typeᵉ
  large-block-element-partitionᵉ aᵉ =
    pr1ᵉ (centerᵉ (is-partition-subtype-partitionᵉ aᵉ))

  is-surjective-large-block-element-partitionᵉ :
    is-surjectiveᵉ large-block-element-partitionᵉ
  is-surjective-large-block-element-partitionᵉ Bᵉ =
    apply-universal-property-trunc-Propᵉ
      ( is-inhabited-subtype-block-partition-Large-Typeᵉ Bᵉ)
      ( trunc-Propᵉ (fiberᵉ large-block-element-partitionᵉ Bᵉ))
      ( λ (aᵉ ,ᵉ uᵉ) →
        unit-trunc-Propᵉ
          ( pairᵉ aᵉ
            ( eq-type-subtypeᵉ
              ( subtype-partitionᵉ)
              ( apᵉ pr1ᵉ
                ( apᵉ
                  ( inclusion-subtypeᵉ
                    ( λ Qᵉ → subtype-inhabited-subtypeᵉ (pr1ᵉ Qᵉ) aᵉ))
                  ( contractionᵉ
                    ( is-partition-subtype-partitionᵉ aᵉ)
                    ( pairᵉ Bᵉ uᵉ)))))))

  is-locally-small-block-partition-Large-Typeᵉ :
    is-locally-smallᵉ (l1ᵉ ⊔ l2ᵉ) block-partition-Large-Typeᵉ
  is-locally-small-block-partition-Large-Typeᵉ =
    is-locally-small-type-subtypeᵉ
      ( subtype-partitionᵉ)
      ( is-locally-small-inhabited-subtypeᵉ is-small'ᵉ)

  is-small-block-partition-Large-Typeᵉ :
    is-smallᵉ (l1ᵉ ⊔ l2ᵉ) block-partition-Large-Typeᵉ
  is-small-block-partition-Large-Typeᵉ =
    is-small-is-surjectiveᵉ
      ( is-surjective-large-block-element-partitionᵉ)
      ( is-small-lmaxᵉ l2ᵉ Aᵉ)
      ( is-locally-small-block-partition-Large-Typeᵉ)
```

### The (small) type of blocks of a partition

Weᵉ willᵉ nowᵉ introduceᵉ theᵉ typeᵉ ofᵉ blocksᵉ ofᵉ aᵉ partition,ᵉ andᵉ showᵉ thatᵉ theᵉ typeᵉ
ofᵉ blocksᵉ containingᵉ aᵉ fixedᵉ elementᵉ `a`ᵉ isᵉ contractible.ᵉ Onceᵉ thisᵉ isᵉ done,ᵉ weᵉ
willᵉ haveᵉ noᵉ moreᵉ useᵉ forᵉ theᵉ largeᵉ typeᵉ ofᵉ blocksᵉ ofᵉ aᵉ partition.ᵉ

```agda
  block-partitionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  block-partitionᵉ = type-is-smallᵉ is-small-block-partition-Large-Typeᵉ

  compute-block-partitionᵉ : block-partition-Large-Typeᵉ ≃ᵉ block-partitionᵉ
  compute-block-partitionᵉ = equiv-is-smallᵉ is-small-block-partition-Large-Typeᵉ

  map-compute-block-partitionᵉ : block-partition-Large-Typeᵉ → block-partitionᵉ
  map-compute-block-partitionᵉ = map-equivᵉ compute-block-partitionᵉ

  make-block-partitionᵉ :
    (Qᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ) → is-block-partitionᵉ Qᵉ → block-partitionᵉ
  make-block-partitionᵉ Qᵉ Hᵉ = map-compute-block-partitionᵉ (pairᵉ Qᵉ Hᵉ)

  map-inv-compute-block-partitionᵉ : block-partitionᵉ → block-partition-Large-Typeᵉ
  map-inv-compute-block-partitionᵉ =
    map-inv-equivᵉ compute-block-partitionᵉ

  is-section-map-inv-compute-block-partitionᵉ :
    ( map-compute-block-partitionᵉ ∘ᵉ map-inv-compute-block-partitionᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-block-partitionᵉ =
    is-section-map-inv-equivᵉ compute-block-partitionᵉ

  is-retraction-map-inv-compute-block-partitionᵉ :
    ( map-inv-compute-block-partitionᵉ ∘ᵉ map-compute-block-partitionᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-block-partitionᵉ =
    is-retraction-map-inv-equivᵉ compute-block-partitionᵉ

  inhabited-subtype-block-partitionᵉ : block-partitionᵉ → inhabited-subtypeᵉ l2ᵉ Aᵉ
  inhabited-subtype-block-partitionᵉ =
    inhabited-subtype-block-partition-Large-Typeᵉ ∘ᵉ
    map-inv-compute-block-partitionᵉ

  is-emb-inhabited-subtype-block-partitionᵉ :
    is-embᵉ inhabited-subtype-block-partitionᵉ
  is-emb-inhabited-subtype-block-partitionᵉ =
    is-emb-compᵉ
      ( inhabited-subtype-block-partition-Large-Typeᵉ)
      ( map-inv-compute-block-partitionᵉ)
      ( is-emb-inhabited-subtype-block-partition-Large-Typeᵉ)
      ( is-emb-is-equivᵉ (is-equiv-map-inv-equivᵉ compute-block-partitionᵉ))

  emb-inhabited-subtype-block-partitionᵉ :
    block-partitionᵉ ↪ᵉ inhabited-subtypeᵉ l2ᵉ Aᵉ
  pr1ᵉ emb-inhabited-subtype-block-partitionᵉ = inhabited-subtype-block-partitionᵉ
  pr2ᵉ emb-inhabited-subtype-block-partitionᵉ =
    is-emb-inhabited-subtype-block-partitionᵉ

  is-block-inhabited-subtype-block-partitionᵉ :
    (Bᵉ : block-partitionᵉ) →
    is-block-partitionᵉ (inhabited-subtype-block-partitionᵉ Bᵉ)
  is-block-inhabited-subtype-block-partitionᵉ Bᵉ =
    is-block-inhabited-subtype-block-partition-Large-Typeᵉ
      ( map-inv-compute-block-partitionᵉ Bᵉ)

  subtype-block-partitionᵉ : block-partitionᵉ → subtypeᵉ l2ᵉ Aᵉ
  subtype-block-partitionᵉ =
    subtype-block-partition-Large-Typeᵉ ∘ᵉ map-inv-compute-block-partitionᵉ

  inhabited-type-block-partitionᵉ : block-partitionᵉ → Inhabited-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  inhabited-type-block-partitionᵉ Bᵉ =
    inhabited-type-block-partition-Large-Typeᵉ
      ( map-inv-compute-block-partitionᵉ Bᵉ)

  is-inhabited-subtype-block-partitionᵉ :
    (Bᵉ : block-partitionᵉ) → is-inhabited-subtypeᵉ (subtype-block-partitionᵉ Bᵉ)
  is-inhabited-subtype-block-partitionᵉ Bᵉ =
    is-inhabited-subtype-block-partition-Large-Typeᵉ
      ( map-inv-compute-block-partitionᵉ Bᵉ)

  type-block-partitionᵉ : block-partitionᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-block-partitionᵉ Bᵉ =
    type-block-partition-Large-Typeᵉ (map-inv-compute-block-partitionᵉ Bᵉ)

  is-in-block-partitionᵉ : (Bᵉ : block-partitionᵉ) → Aᵉ → UUᵉ l2ᵉ
  is-in-block-partitionᵉ Bᵉ =
    is-in-block-partition-Large-Typeᵉ (map-inv-compute-block-partitionᵉ Bᵉ)

  is-prop-is-in-block-partitionᵉ :
    (Bᵉ : block-partitionᵉ) (aᵉ : Aᵉ) → is-propᵉ (is-in-block-partitionᵉ Bᵉ aᵉ)
  is-prop-is-in-block-partitionᵉ Bᵉ =
    is-prop-is-in-block-partition-Large-Typeᵉ
      ( map-inv-compute-block-partitionᵉ Bᵉ)

  abstract
    compute-is-in-block-partitionᵉ :
      (Bᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ) (Hᵉ : is-block-partitionᵉ Bᵉ) (xᵉ : Aᵉ) →
      is-in-inhabited-subtypeᵉ Bᵉ xᵉ ≃ᵉ
      is-in-block-partitionᵉ (make-block-partitionᵉ Bᵉ Hᵉ) xᵉ
    compute-is-in-block-partitionᵉ Bᵉ Hᵉ xᵉ =
      equiv-trᵉ
        ( λ Cᵉ → is-in-block-partition-Large-Typeᵉ Cᵉ xᵉ)
        ( invᵉ (is-retraction-map-inv-compute-block-partitionᵉ (Bᵉ ,ᵉ Hᵉ)))

  abstract
    make-is-in-block-partitionᵉ :
      (Bᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ) (Hᵉ : is-block-partitionᵉ Bᵉ) (xᵉ : Aᵉ) →
      is-in-inhabited-subtypeᵉ Bᵉ xᵉ →
      is-in-block-partitionᵉ (make-block-partitionᵉ Bᵉ Hᵉ) xᵉ
    make-is-in-block-partitionᵉ Bᵉ Hᵉ xᵉ Kᵉ =
      map-equivᵉ (compute-is-in-block-partitionᵉ Bᵉ Hᵉ xᵉ) Kᵉ

  block-containing-element-partitionᵉ : Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  block-containing-element-partitionᵉ aᵉ =
    Σᵉ block-partitionᵉ (λ Bᵉ → is-in-block-partitionᵉ Bᵉ aᵉ)

  abstract
    is-contr-block-containing-element-partitionᵉ :
      (aᵉ : Aᵉ) → is-contrᵉ (block-containing-element-partitionᵉ aᵉ)
    is-contr-block-containing-element-partitionᵉ aᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ block-partition-Large-Typeᵉ
          ( λ Bᵉ → is-in-block-partition-Large-Typeᵉ Bᵉ aᵉ))
        ( equiv-Σᵉ
          ( λ Bᵉ → is-in-block-partitionᵉ Bᵉ aᵉ)
          ( compute-block-partitionᵉ)
          ( λ Bᵉ →
            equiv-trᵉ
              ( λ Cᵉ → is-in-block-partition-Large-Typeᵉ Cᵉ aᵉ)
              ( invᵉ (is-retraction-map-inv-compute-block-partitionᵉ Bᵉ))))
        ( is-partition-subtype-partitionᵉ aᵉ)

  center-block-containing-element-partitionᵉ :
    (aᵉ : Aᵉ) → block-containing-element-partitionᵉ aᵉ
  center-block-containing-element-partitionᵉ aᵉ =
    centerᵉ (is-contr-block-containing-element-partitionᵉ aᵉ)

  class-partitionᵉ : Aᵉ → block-partitionᵉ
  class-partitionᵉ aᵉ =
    pr1ᵉ (center-block-containing-element-partitionᵉ aᵉ)

  is-block-class-partitionᵉ :
    (aᵉ : Aᵉ) →
    is-block-partitionᵉ (inhabited-subtype-block-partitionᵉ (class-partitionᵉ aᵉ))
  is-block-class-partitionᵉ aᵉ =
    is-block-inhabited-subtype-block-partitionᵉ (class-partitionᵉ aᵉ)

  is-in-block-class-partitionᵉ :
    (aᵉ : Aᵉ) → is-in-block-partitionᵉ (class-partitionᵉ aᵉ) aᵉ
  is-in-block-class-partitionᵉ aᵉ =
    pr2ᵉ (center-block-containing-element-partitionᵉ aᵉ)

  compute-base-type-partitionᵉ : Σᵉ block-partitionᵉ type-block-partitionᵉ ≃ᵉ Aᵉ
  compute-base-type-partitionᵉ =
    ( right-unit-law-Σ-is-contrᵉ
      ( λ xᵉ → is-contr-block-containing-element-partitionᵉ xᵉ)) ∘eᵉ
    ( equiv-left-swap-Σᵉ)
```

## Properties

### Characterizing equality of partitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  has-same-blocks-partitionᵉ :
    {l4ᵉ : Level} (Qᵉ : partitionᵉ l2ᵉ l4ᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  has-same-blocks-partitionᵉ Qᵉ =
    has-same-elements-subtypeᵉ (subtype-partitionᵉ Pᵉ) (subtype-partitionᵉ Qᵉ)

  refl-has-same-blocks-partitionᵉ : has-same-blocks-partitionᵉ Pᵉ
  refl-has-same-blocks-partitionᵉ =
    refl-has-same-elements-subtypeᵉ (subtype-partitionᵉ Pᵉ)

  extensionality-partitionᵉ :
    (Qᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ) → (Pᵉ ＝ᵉ Qᵉ) ≃ᵉ has-same-blocks-partitionᵉ Qᵉ
  extensionality-partitionᵉ =
    extensionality-type-subtypeᵉ
      ( is-partition-Propᵉ)
      ( is-partition-subtype-partitionᵉ Pᵉ)
      ( refl-has-same-elements-subtypeᵉ (subtype-partitionᵉ Pᵉ))
      ( extensionality-subtypeᵉ (subtype-partitionᵉ Pᵉ))

  eq-has-same-blocks-partitionᵉ :
    (Qᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ) → has-same-blocks-partitionᵉ Qᵉ → Pᵉ ＝ᵉ Qᵉ
  eq-has-same-blocks-partitionᵉ Qᵉ =
    map-inv-equivᵉ (extensionality-partitionᵉ Qᵉ)
```

### Characterizing equality of blocks of partitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ) (Bᵉ : block-partitionᵉ Pᵉ)
  where

  has-same-elements-block-partition-Propᵉ :
    block-partitionᵉ Pᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  has-same-elements-block-partition-Propᵉ Cᵉ =
    has-same-elements-inhabited-subtype-Propᵉ
      ( inhabited-subtype-block-partitionᵉ Pᵉ Bᵉ)
      ( inhabited-subtype-block-partitionᵉ Pᵉ Cᵉ)

  has-same-elements-block-partitionᵉ :
    block-partitionᵉ Pᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-same-elements-block-partitionᵉ Cᵉ =
    has-same-elements-inhabited-subtypeᵉ
      ( inhabited-subtype-block-partitionᵉ Pᵉ Bᵉ)
      ( inhabited-subtype-block-partitionᵉ Pᵉ Cᵉ)

  is-prop-has-same-elements-block-partitionᵉ :
    (Cᵉ : block-partitionᵉ Pᵉ) → is-propᵉ (has-same-elements-block-partitionᵉ Cᵉ)
  is-prop-has-same-elements-block-partitionᵉ Cᵉ =
    is-prop-has-same-elements-inhabited-subtypeᵉ
      ( inhabited-subtype-block-partitionᵉ Pᵉ Bᵉ)
      ( inhabited-subtype-block-partitionᵉ Pᵉ Cᵉ)

  refl-has-same-elements-block-partitionᵉ :
    has-same-elements-block-partitionᵉ Bᵉ
  refl-has-same-elements-block-partitionᵉ =
    refl-has-same-elements-inhabited-subtypeᵉ
      ( inhabited-subtype-block-partitionᵉ Pᵉ Bᵉ)

  abstract
    is-torsorial-has-same-elements-block-partitionᵉ :
      is-torsorialᵉ has-same-elements-block-partitionᵉ
    is-torsorial-has-same-elements-block-partitionᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ ( block-partitionᵉ Pᵉ)
            ( λ Cᵉ →
              inhabited-subtype-block-partitionᵉ Pᵉ Bᵉ ＝ᵉ
              inhabited-subtype-block-partitionᵉ Pᵉ Cᵉ))
        ( equiv-totᵉ
          ( λ Cᵉ →
            extensionality-inhabited-subtypeᵉ
              ( inhabited-subtype-block-partitionᵉ Pᵉ Bᵉ)
              ( inhabited-subtype-block-partitionᵉ Pᵉ Cᵉ)))
        ( fundamental-theorem-id'ᵉ
          ( λ Cᵉ → apᵉ (inhabited-subtype-block-partitionᵉ Pᵉ))
          ( is-emb-inhabited-subtype-block-partitionᵉ Pᵉ Bᵉ))

  has-same-elements-eq-block-partitionᵉ :
    (Cᵉ : block-partitionᵉ Pᵉ) → (Bᵉ ＝ᵉ Cᵉ) →
    has-same-elements-block-partitionᵉ Cᵉ
  has-same-elements-eq-block-partitionᵉ .Bᵉ reflᵉ =
    refl-has-same-elements-block-partitionᵉ

  is-equiv-has-same-elements-eq-block-partitionᵉ :
    (Cᵉ : block-partitionᵉ Pᵉ) →
    is-equivᵉ (has-same-elements-eq-block-partitionᵉ Cᵉ)
  is-equiv-has-same-elements-eq-block-partitionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-has-same-elements-block-partitionᵉ
      has-same-elements-eq-block-partitionᵉ

  extensionality-block-partitionᵉ :
    (Cᵉ : block-partitionᵉ Pᵉ) →
    (Bᵉ ＝ᵉ Cᵉ) ≃ᵉ has-same-elements-block-partitionᵉ Cᵉ
  pr1ᵉ (extensionality-block-partitionᵉ Cᵉ) =
    has-same-elements-eq-block-partitionᵉ Cᵉ
  pr2ᵉ (extensionality-block-partitionᵉ Cᵉ) =
    is-equiv-has-same-elements-eq-block-partitionᵉ Cᵉ

  eq-has-same-elements-block-partitionᵉ :
    (Cᵉ : block-partitionᵉ Pᵉ) →
    has-same-elements-block-partitionᵉ Cᵉ → Bᵉ ＝ᵉ Cᵉ
  eq-has-same-elements-block-partitionᵉ Cᵉ =
    map-inv-equivᵉ (extensionality-block-partitionᵉ Cᵉ)
```

### The type of blocks of a partition is a set

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  is-set-block-partitionᵉ : is-setᵉ (block-partitionᵉ Pᵉ)
  is-set-block-partitionᵉ Bᵉ Cᵉ =
    is-prop-equivᵉ
      ( extensionality-block-partitionᵉ Pᵉ Bᵉ Cᵉ)
      ( is-prop-has-same-elements-block-partitionᵉ Pᵉ Bᵉ Cᵉ)

  block-partition-Setᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ block-partition-Setᵉ = block-partitionᵉ Pᵉ
  pr2ᵉ block-partition-Setᵉ = is-set-block-partitionᵉ
```

### The inclusion of a block into the base type of a partition is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  emb-inclusion-block-partitionᵉ :
    (Bᵉ : block-partitionᵉ Pᵉ) → type-block-partitionᵉ Pᵉ Bᵉ ↪ᵉ Aᵉ
  emb-inclusion-block-partitionᵉ Bᵉ =
    comp-embᵉ
      ( emb-equivᵉ (compute-base-type-partitionᵉ Pᵉ))
      ( emb-fiber-inclusionᵉ
        ( type-block-partitionᵉ Pᵉ)
        ( is-set-block-partitionᵉ Pᵉ)
        ( Bᵉ))
```

### Two blocks of a partition are equal if they share a common element

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ)
  (Bᵉ : block-partitionᵉ Pᵉ)
  where

  share-common-element-block-partition-Propᵉ :
    (Cᵉ : block-partitionᵉ Pᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  share-common-element-block-partition-Propᵉ Cᵉ =
    ∃ᵉ Aᵉ (λ aᵉ → subtype-block-partitionᵉ Pᵉ Bᵉ aᵉ ∧ᵉ subtype-block-partitionᵉ Pᵉ Cᵉ aᵉ)

  share-common-element-block-partitionᵉ :
    (Cᵉ : block-partitionᵉ Pᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  share-common-element-block-partitionᵉ Cᵉ =
    type-Propᵉ (share-common-element-block-partition-Propᵉ Cᵉ)

  eq-share-common-element-block-partitionᵉ :
    (Cᵉ : block-partitionᵉ Pᵉ) → share-common-element-block-partitionᵉ Cᵉ → Bᵉ ＝ᵉ Cᵉ
  eq-share-common-element-block-partitionᵉ Cᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( Id-Propᵉ (block-partition-Setᵉ Pᵉ) Bᵉ Cᵉ)
      ( λ (aᵉ ,ᵉ Kᵉ ,ᵉ Lᵉ) →
        apᵉ
          ( pr1ᵉ)
          ( eq-is-contrᵉ
            ( is-contr-block-containing-element-partitionᵉ Pᵉ aᵉ)
            { Bᵉ ,ᵉ Kᵉ}
            { Cᵉ ,ᵉ Lᵉ}))
```

### The condition of being a partition is equivalent to the condition that the total space of all blocks is equivalent to the base type

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  compute-total-block-partitionᵉ :
    Σᵉ (block-partitionᵉ Pᵉ) (type-block-partitionᵉ Pᵉ) ≃ᵉ Aᵉ
  compute-total-block-partitionᵉ =
    ( right-unit-law-Σ-is-contrᵉ
      ( is-contr-block-containing-element-partitionᵉ Pᵉ)) ∘eᵉ
    ( equiv-left-swap-Σᵉ)

  map-compute-total-block-partitionᵉ :
    Σᵉ (block-partitionᵉ Pᵉ) (type-block-partitionᵉ Pᵉ) → Aᵉ
  map-compute-total-block-partitionᵉ = map-equivᵉ compute-total-block-partitionᵉ
```

### The type of partitions of `A` is equivalent to the type of set-indexed Σ-decompositions of `A`

#### The set-indexed Σ-decomposition obtained from a partition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  set-indexed-Σ-decomposition-partitionᵉ :
    Set-Indexed-Σ-Decompositionᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ) Aᵉ
  pr1ᵉ set-indexed-Σ-decomposition-partitionᵉ = block-partition-Setᵉ Pᵉ
  pr1ᵉ (pr2ᵉ set-indexed-Σ-decomposition-partitionᵉ) =
    inhabited-type-block-partitionᵉ Pᵉ
  pr2ᵉ (pr2ᵉ set-indexed-Σ-decomposition-partitionᵉ) =
    inv-equivᵉ (compute-total-block-partitionᵉ Pᵉ)
```

#### The partition obtained from a set-indexed Σ-decomposition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Dᵉ : Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  is-block-partition-Set-Indexed-Σ-Decompositionᵉ :
    {l4ᵉ : Level} → inhabited-subtypeᵉ l4ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-block-partition-Set-Indexed-Σ-Decompositionᵉ Qᵉ =
    Σᵉ ( indexing-type-Set-Indexed-Σ-Decompositionᵉ Dᵉ)
      ( λ iᵉ →
        (xᵉ : Aᵉ) →
        ( is-in-inhabited-subtypeᵉ Qᵉ xᵉ) ≃ᵉ
        ( index-Set-Indexed-Σ-Decompositionᵉ Dᵉ xᵉ ＝ᵉ iᵉ))

  is-prop-is-block-partition-Set-Indexed-Σ-Decompositionᵉ :
    {l4ᵉ : Level} (Qᵉ : inhabited-subtypeᵉ l4ᵉ Aᵉ) →
    is-propᵉ (is-block-partition-Set-Indexed-Σ-Decompositionᵉ Qᵉ)
  is-prop-is-block-partition-Set-Indexed-Σ-Decompositionᵉ Qᵉ =
    apply-universal-property-trunc-Propᵉ
      ( is-inhabited-subtype-inhabited-subtypeᵉ Qᵉ)
      ( is-prop-Propᵉ (is-block-partition-Set-Indexed-Σ-Decompositionᵉ Qᵉ))
      ( λ (aᵉ ,ᵉ qᵉ) →
        is-prop-all-elements-equalᵉ
          ( λ (iᵉ ,ᵉ Hᵉ) (jᵉ ,ᵉ Kᵉ) →
            eq-type-subtypeᵉ
            ( λ uᵉ →
              Π-Propᵉ Aᵉ
              ( λ xᵉ →
                equiv-Propᵉ
                ( subtype-inhabited-subtypeᵉ Qᵉ xᵉ)
                  ( Id-Propᵉ
                    ( indexing-set-Set-Indexed-Σ-Decompositionᵉ Dᵉ)
                    ( pr1ᵉ
                      ( map-matching-correspondence-Set-Indexed-Σ-Decompositionᵉ
                        Dᵉ xᵉ))
                    ( uᵉ))))
            ( invᵉ (map-equivᵉ (Hᵉ aᵉ) qᵉ) ∙ᵉ map-equivᵉ (Kᵉ aᵉ) qᵉ)))

  subtype-partition-Set-Indexed-Σ-Decompositionᵉ :
    {l4ᵉ : Level} → subtypeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ) (inhabited-subtypeᵉ l4ᵉ Aᵉ)
  pr1ᵉ (subtype-partition-Set-Indexed-Σ-Decompositionᵉ Qᵉ) =
    is-block-partition-Set-Indexed-Σ-Decompositionᵉ Qᵉ
  pr2ᵉ (subtype-partition-Set-Indexed-Σ-Decompositionᵉ Qᵉ) =
    is-prop-is-block-partition-Set-Indexed-Σ-Decompositionᵉ Qᵉ

  abstract
    is-partition-subtype-partition-Set-Indexed-Σ-Decompositionᵉ :
      is-partitionᵉ (subtype-partition-Set-Indexed-Σ-Decompositionᵉ {l2ᵉ})
    is-partition-subtype-partition-Set-Indexed-Σ-Decompositionᵉ aᵉ =
      is-contr-equivᵉ
        ( Σᵉ ( inhabited-subtypeᵉ l2ᵉ Aᵉ)
            ( has-same-elements-inhabited-subtypeᵉ
                ( pairᵉ
                  ( λ xᵉ →
                    Id-Propᵉ
                      ( indexing-set-Set-Indexed-Σ-Decompositionᵉ Dᵉ)
                      ( index-Set-Indexed-Σ-Decompositionᵉ Dᵉ xᵉ)
                      ( index-Set-Indexed-Σ-Decompositionᵉ Dᵉ aᵉ))
                  ( unit-trunc-Propᵉ (pairᵉ aᵉ reflᵉ)))))
        ( ( equiv-totᵉ
            ( λ Qᵉ →
              ( ( ( equiv-Π-equiv-familyᵉ
                    ( λ xᵉ →
                      inv-equivᵉ
                        ( equiv-equiv-iffᵉ
                          ( Id-Propᵉ
                            ( indexing-set-Set-Indexed-Σ-Decompositionᵉ Dᵉ)
                            ( index-Set-Indexed-Σ-Decompositionᵉ Dᵉ xᵉ)
                            ( index-Set-Indexed-Σ-Decompositionᵉ Dᵉ aᵉ))
                          ( subtype-inhabited-subtypeᵉ Qᵉ xᵉ)) ∘eᵉ
                      ( equiv-inv-equivᵉ))) ∘eᵉ
                  ( left-unit-law-Σ-is-contrᵉ
                    ( is-torsorial-Idᵉ (index-Set-Indexed-Σ-Decompositionᵉ Dᵉ aᵉ))
                    ( pairᵉ
                      ( index-Set-Indexed-Σ-Decompositionᵉ Dᵉ aᵉ)
                      ( reflᵉ)))) ∘eᵉ
                ( equiv-right-swap-Σᵉ)) ∘eᵉ
              ( equiv-totᵉ (λ ieᵉ → pr2ᵉ ieᵉ aᵉ)))) ∘eᵉ
          ( associative-Σᵉ
            ( inhabited-subtypeᵉ l2ᵉ Aᵉ)
            ( is-block-partition-Set-Indexed-Σ-Decompositionᵉ)
            ( λ Bᵉ → is-in-inhabited-subtypeᵉ (pr1ᵉ Bᵉ) aᵉ)))
        ( is-torsorial-has-same-elements-inhabited-subtypeᵉ
          ( pairᵉ
            ( λ xᵉ →
              Id-Propᵉ
                ( indexing-set-Set-Indexed-Σ-Decompositionᵉ Dᵉ)
                ( index-Set-Indexed-Σ-Decompositionᵉ Dᵉ xᵉ)
                ( index-Set-Indexed-Σ-Decompositionᵉ Dᵉ aᵉ))
            ( unit-trunc-Propᵉ (pairᵉ aᵉ reflᵉ))))

partition-Set-Indexed-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ → partitionᵉ l2ᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
pr1ᵉ (partition-Set-Indexed-Σ-Decompositionᵉ Dᵉ) =
  subtype-partition-Set-Indexed-Σ-Decompositionᵉ Dᵉ
pr2ᵉ (partition-Set-Indexed-Σ-Decompositionᵉ Dᵉ) =
  is-partition-subtype-partition-Set-Indexed-Σ-Decompositionᵉ Dᵉ
```

#### The partition obtained from the set-indexed Σ-decomposition induced by a partition has the same blocks as the original partition

```text
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ (l1ᵉ ⊔ l2ᵉ) l3ᵉ Aᵉ)
  where

  is-block-is-block-partition-set-indexed-Σ-decomposition-partitionᵉ :
    ( Qᵉ : inhabited-subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ) →
    is-block-partitionᵉ
      ( partition-Set-Indexed-Σ-Decompositionᵉ
        ( set-indexed-Σ-decomposition-partitionᵉ Pᵉ))
      ( Qᵉ) →
    is-block-partitionᵉ Pᵉ Qᵉ
  is-block-is-block-partition-set-indexed-Σ-decomposition-partitionᵉ Qᵉ (iᵉ ,ᵉ Hᵉ) =
    apply-universal-property-trunc-Propᵉ
      ( is-inhabited-subtype-inhabited-subtypeᵉ Qᵉ)
      ( subtype-partitionᵉ Pᵉ Qᵉ)
      ( λ (aᵉ ,ᵉ qᵉ) → {!ᵉ  !ᵉ})

{-ᵉ  iᵉ : Xᵉ  Hᵉ : (xᵉ : Aᵉ) → Qᵉ xᵉ ≃ᵉ (pr1ᵉ (inv-equivᵉ
(compute-total-block-partitionᵉ Pᵉ) xᵉ) ＝ᵉ iᵉ)  aᵉ : Aᵉ  qᵉ : Qᵉ aᵉ

 Hᵉ aᵉ qᵉ : pr1ᵉ (inv-equivᵉ (compute-total-block-partitionᵉ Pᵉ) aᵉ) ＝ᵉ iᵉ

 H'ᵉ : (Bᵉ : blockᵉ)  -ᵉ}

  is-block-partition-set-indexed-Σ-decomposition-is-block-partitionᵉ :
    ( Qᵉ : inhabited-subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ) →
    is-block-partitionᵉ Pᵉ Qᵉ →
    is-block-partitionᵉ
      ( partition-Set-Indexed-Σ-Decompositionᵉ
        ( set-indexed-Σ-decomposition-partitionᵉ Pᵉ))
      ( Qᵉ)
  is-block-partition-set-indexed-Σ-decomposition-is-block-partitionᵉ Qᵉ Hᵉ = {!ᵉ  !ᵉ}

  has-same-blocks-partition-set-indexed-Σ-decomposition-partitionᵉ :
    has-same-blocks-partitionᵉ
      ( partition-Set-Indexed-Σ-Decompositionᵉ
        ( set-indexed-Σ-decomposition-partitionᵉ Pᵉ))
      ( Pᵉ)
  pr1ᵉ (has-same-blocks-partition-set-indexed-Σ-decomposition-partitionᵉ Bᵉ) =
    is-block-is-block-partition-set-indexed-Σ-decomposition-partitionᵉ Bᵉ
  pr2ᵉ (has-same-blocks-partition-set-indexed-Σ-decomposition-partitionᵉ Bᵉ) =
    is-block-partition-set-indexed-Σ-decomposition-is-block-partitionᵉ Bᵉ
```
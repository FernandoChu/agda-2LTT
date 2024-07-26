# Partitions of finite types

```agda
module univalent-combinatorics.partitionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ **partition**ᵉ ofᵉ aᵉ [finiteᵉ type](univalent-combinatorics.finite-types.mdᵉ) `X`ᵉ
canᵉ beᵉ definedᵉ in severalᵉ equivalentᵉ waysᵉ:

-ᵉ Aᵉ partitionᵉ isᵉ aᵉ [subset](foundation.subtypes.mdᵉ) `P`ᵉ ofᵉ theᵉ
  [powerset](foundation.powersets.mdᵉ) ofᵉ `X`ᵉ suchᵉ thatᵉ eachᵉ `Uᵉ ⊆ᵉ X`ᵉ in `P`ᵉ isᵉ
  [inhabited](foundation.inhabited-types.mdᵉ) andᵉ eachᵉ elementᵉ `xᵉ : X`ᵉ isᵉ in
  exactlyᵉ oneᵉ subsetᵉ `Uᵉ ⊆ᵉ X`ᵉ in `P`.ᵉ
-ᵉ Aᵉ partitionᵉ isᵉ anᵉ
  [equivalenceᵉ relation](foundation-core.equivalence-relations.mdᵉ) onᵉ `X`ᵉ
-ᵉ Aᵉ partitionᵉ isᵉ aᵉ decompositionᵉ ofᵉ `X`ᵉ intoᵉ aᵉ typeᵉ ofᵉ theᵉ formᵉ `Σᵉ Aᵉ B`ᵉ where
  `A`ᵉ isᵉ finiteᵉ andᵉ `B`ᵉ isᵉ aᵉ familyᵉ ofᵉ inhabitedᵉ finiteᵉ types,ᵉ i.e.,ᵉ itᵉ consistsᵉ
  ofᵉ suchᵉ `A`ᵉ andᵉ `B`ᵉ andᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ)
  `Xᵉ ≃ᵉ Σᵉ Aᵉ B`.ᵉ

Noteᵉ thatᵉ theᵉ lastᵉ descriptionᵉ isᵉ subtlyᵉ differentᵉ fromᵉ theᵉ notionᵉ ofᵉ
[unlabeledᵉ partition](univalent-combinatorics.ferrers-diagrams.mdᵉ) (i.e.,ᵉ
Ferrersᵉ diagram),ᵉ becauseᵉ itᵉ onlyᵉ usesᵉ
[mereᵉ equivalences](foundation.mere-equivalences.md).ᵉ

## Definition

### Partitions

```agda
partition-𝔽ᵉ : {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) → 𝔽ᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
partition-𝔽ᵉ l2ᵉ l3ᵉ Xᵉ =
  Σᵉ ( 𝔽ᵉ l2ᵉ)
    ( λ Yᵉ →
      Σᵉ ( type-𝔽ᵉ Yᵉ → 𝔽ᵉ l3ᵉ)
        ( λ Zᵉ →
          ( (yᵉ : type-𝔽ᵉ Yᵉ) → type-trunc-Propᵉ (type-𝔽ᵉ (Zᵉ yᵉ))) ×ᵉ
          ( equiv-𝔽ᵉ Xᵉ (Σ-𝔽ᵉ Yᵉ Zᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ : partition-𝔽ᵉ l2ᵉ l3ᵉ Xᵉ)
  where

  finite-indexing-type-partition-𝔽ᵉ : 𝔽ᵉ l2ᵉ
  finite-indexing-type-partition-𝔽ᵉ = pr1ᵉ Pᵉ

  indexing-type-partition-𝔽ᵉ : UUᵉ l2ᵉ
  indexing-type-partition-𝔽ᵉ = type-𝔽ᵉ finite-indexing-type-partition-𝔽ᵉ

  is-finite-indexing-type-partition-𝔽ᵉ : is-finiteᵉ indexing-type-partition-𝔽ᵉ
  is-finite-indexing-type-partition-𝔽ᵉ =
    is-finite-type-𝔽ᵉ finite-indexing-type-partition-𝔽ᵉ

  number-of-elements-indexing-type-partition-𝔽ᵉ : ℕᵉ
  number-of-elements-indexing-type-partition-𝔽ᵉ =
    number-of-elements-is-finiteᵉ is-finite-indexing-type-partition-𝔽ᵉ

  finite-block-partition-𝔽ᵉ : indexing-type-partition-𝔽ᵉ → 𝔽ᵉ l3ᵉ
  finite-block-partition-𝔽ᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  block-partition-𝔽ᵉ : indexing-type-partition-𝔽ᵉ → UUᵉ l3ᵉ
  block-partition-𝔽ᵉ iᵉ = type-𝔽ᵉ (finite-block-partition-𝔽ᵉ iᵉ)

  is-finite-block-partition-𝔽ᵉ :
    (iᵉ : indexing-type-partition-𝔽ᵉ) → is-finiteᵉ (block-partition-𝔽ᵉ iᵉ)
  is-finite-block-partition-𝔽ᵉ iᵉ = is-finite-type-𝔽ᵉ (finite-block-partition-𝔽ᵉ iᵉ)

  number-of-elements-block-partition-𝔽ᵉ : indexing-type-partition-𝔽ᵉ → ℕᵉ
  number-of-elements-block-partition-𝔽ᵉ iᵉ =
    number-of-elements-is-finiteᵉ (is-finite-block-partition-𝔽ᵉ iᵉ)

  is-inhabited-block-partition-𝔽ᵉ :
    (iᵉ : indexing-type-partition-𝔽ᵉ) → type-trunc-Propᵉ (block-partition-𝔽ᵉ iᵉ)
  is-inhabited-block-partition-𝔽ᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Pᵉ))

  conversion-partition-𝔽ᵉ :
    equiv-𝔽ᵉ Xᵉ (Σ-𝔽ᵉ finite-indexing-type-partition-𝔽ᵉ finite-block-partition-𝔽ᵉ)
  conversion-partition-𝔽ᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Pᵉ))

  map-conversion-partition-𝔽ᵉ :
    type-𝔽ᵉ Xᵉ → Σᵉ indexing-type-partition-𝔽ᵉ block-partition-𝔽ᵉ
  map-conversion-partition-𝔽ᵉ = map-equivᵉ conversion-partition-𝔽ᵉ

  rel-partition-𝔽-Propᵉ : type-𝔽ᵉ Xᵉ → type-𝔽ᵉ Xᵉ → Propᵉ l2ᵉ
  rel-partition-𝔽-Propᵉ xᵉ yᵉ =
    Id-Propᵉ
      ( set-𝔽ᵉ finite-indexing-type-partition-𝔽ᵉ)
      ( pr1ᵉ (map-conversion-partition-𝔽ᵉ xᵉ))
      ( pr1ᵉ (map-conversion-partition-𝔽ᵉ yᵉ))

  rel-partition-𝔽ᵉ : type-𝔽ᵉ Xᵉ → type-𝔽ᵉ Xᵉ → UUᵉ l2ᵉ
  rel-partition-𝔽ᵉ xᵉ yᵉ = type-Propᵉ (rel-partition-𝔽-Propᵉ xᵉ yᵉ)

  is-prop-rel-partition-𝔽ᵉ : (xᵉ yᵉ : type-𝔽ᵉ Xᵉ) → is-propᵉ (rel-partition-𝔽ᵉ xᵉ yᵉ)
  is-prop-rel-partition-𝔽ᵉ xᵉ yᵉ = is-prop-type-Propᵉ (rel-partition-𝔽-Propᵉ xᵉ yᵉ)

  refl-rel-partition-𝔽ᵉ : is-reflexiveᵉ rel-partition-𝔽ᵉ
  refl-rel-partition-𝔽ᵉ xᵉ = reflᵉ

  symmetric-rel-partition-𝔽ᵉ : is-symmetricᵉ rel-partition-𝔽ᵉ
  symmetric-rel-partition-𝔽ᵉ xᵉ yᵉ = invᵉ

  transitive-rel-partition-𝔽ᵉ : is-transitiveᵉ rel-partition-𝔽ᵉ
  transitive-rel-partition-𝔽ᵉ xᵉ yᵉ zᵉ rᵉ sᵉ = sᵉ ∙ᵉ rᵉ

  equivalence-relation-partition-𝔽ᵉ : equivalence-relationᵉ l2ᵉ (type-𝔽ᵉ Xᵉ)
  pr1ᵉ equivalence-relation-partition-𝔽ᵉ = rel-partition-𝔽-Propᵉ
  pr1ᵉ (pr2ᵉ equivalence-relation-partition-𝔽ᵉ) = refl-rel-partition-𝔽ᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-partition-𝔽ᵉ)) = symmetric-rel-partition-𝔽ᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-partition-𝔽ᵉ)) = transitive-rel-partition-𝔽ᵉ
```

### Equivalences of partitions

```agda
equiv-partition-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) →
  partition-𝔽ᵉ l2ᵉ l3ᵉ Xᵉ → partition-𝔽ᵉ l4ᵉ l5ᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
equiv-partition-𝔽ᵉ Xᵉ Pᵉ Qᵉ =
  Σᵉ ( indexing-type-partition-𝔽ᵉ Xᵉ Pᵉ ≃ᵉ indexing-type-partition-𝔽ᵉ Xᵉ Qᵉ)
    ( λ eᵉ →
      Σᵉ ( (iᵉ : indexing-type-partition-𝔽ᵉ Xᵉ Pᵉ) →
          block-partition-𝔽ᵉ Xᵉ Pᵉ iᵉ ≃ᵉ block-partition-𝔽ᵉ Xᵉ Qᵉ (map-equivᵉ eᵉ iᵉ))
        ( λ fᵉ →
          htpy-equivᵉ
            ( ( equiv-Σᵉ (block-partition-𝔽ᵉ Xᵉ Qᵉ) eᵉ fᵉ) ∘eᵉ
              ( conversion-partition-𝔽ᵉ Xᵉ Pᵉ))
            ( conversion-partition-𝔽ᵉ Xᵉ Qᵉ)))

id-equiv-partition-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ)
  (Pᵉ : partition-𝔽ᵉ l2ᵉ l3ᵉ Xᵉ) → equiv-partition-𝔽ᵉ Xᵉ Pᵉ Pᵉ
pr1ᵉ (id-equiv-partition-𝔽ᵉ Xᵉ Pᵉ) = id-equivᵉ
pr1ᵉ (pr2ᵉ (id-equiv-partition-𝔽ᵉ Xᵉ Pᵉ)) iᵉ = id-equivᵉ
pr2ᵉ (pr2ᵉ (id-equiv-partition-𝔽ᵉ Xᵉ Pᵉ)) = refl-htpyᵉ

extensionality-partition-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ Qᵉ : partition-𝔽ᵉ l2ᵉ l3ᵉ Xᵉ) →
  Idᵉ Pᵉ Qᵉ ≃ᵉ equiv-partition-𝔽ᵉ Xᵉ Pᵉ Qᵉ
extensionality-partition-𝔽ᵉ Xᵉ Pᵉ =
  extensionality-Σᵉ
    ( λ {Yᵉ} Zfᵉ eᵉ →
      Σᵉ ( (iᵉ : indexing-type-partition-𝔽ᵉ Xᵉ Pᵉ) →
          block-partition-𝔽ᵉ Xᵉ Pᵉ iᵉ ≃ᵉ type-𝔽ᵉ (pr1ᵉ Zfᵉ (map-equivᵉ eᵉ iᵉ)))
        ( λ fᵉ →
          htpy-equivᵉ
            ( equiv-Σᵉ (type-𝔽ᵉ ∘ᵉ pr1ᵉ Zfᵉ) eᵉ fᵉ ∘eᵉ conversion-partition-𝔽ᵉ Xᵉ Pᵉ)
            ( pr2ᵉ (pr2ᵉ Zfᵉ))))
    ( id-equivᵉ)
    ( pairᵉ (λ iᵉ → id-equivᵉ) refl-htpyᵉ)
    ( extensionality-𝔽ᵉ (finite-indexing-type-partition-𝔽ᵉ Xᵉ Pᵉ))
    ( extensionality-Σᵉ
      ( λ {Zᵉ} fᵉ αᵉ →
        htpy-equivᵉ
          ( equiv-Σᵉ (type-𝔽ᵉ ∘ᵉ Zᵉ) id-equivᵉ αᵉ ∘eᵉ conversion-partition-𝔽ᵉ Xᵉ Pᵉ)
          ( pr2ᵉ fᵉ))
      ( λ iᵉ → id-equivᵉ)
      ( refl-htpyᵉ)
      ( extensionality-fam-𝔽ᵉ (finite-block-partition-𝔽ᵉ Xᵉ Pᵉ))
      ( λ αᵉ →
        ( ( extensionality-equivᵉ (conversion-partition-𝔽ᵉ Xᵉ Pᵉ) (pr2ᵉ αᵉ)) ∘eᵉ
          ( left-unit-law-product-is-contrᵉ
            ( is-prop-Πᵉ
              ( λ _ → is-prop-type-trunc-Propᵉ)
              ( is-inhabited-block-partition-𝔽ᵉ Xᵉ Pᵉ)
              ( pr1ᵉ αᵉ)))) ∘eᵉ
        ( equiv-pair-eqᵉ (pr2ᵉ (pr2ᵉ Pᵉ)) αᵉ)))
```

## Properties

### The type of finite partitions of a finite type `X` is equivalent to the type of decidable partitions of `X` in the usual sense

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#747](https://github.com/UniMath/agda-unimath/issues/747ᵉ)

### The type of finite partitions of a finite type `X` is equivalent to the type of equivalence relations on `X`

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#747](https://github.com/UniMath/agda-unimath/issues/747ᵉ)

### The type of finite partitions of a finite type is finite

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#747](https://github.com/UniMath/agda-unimath/issues/747ᵉ)

### The number of elements of the type of finite partitions of a finite type is a Stirling number of the second kind

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#747](https://github.com/UniMath/agda-unimath/issues/747ᵉ)

### The type of finite partitions of a contractible type is contractible

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#747](https://github.com/UniMath/agda-unimath/issues/747ᵉ)
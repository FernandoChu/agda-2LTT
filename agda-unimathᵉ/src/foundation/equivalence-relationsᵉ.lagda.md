# Equivalence relations

```agda
module foundation.equivalence-relationsᵉ where

open import foundation-core.equivalence-relationsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.equivalence-classesᵉ
open import foundation.full-subtypesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.partitionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.set-quotientsᵉ
open import foundation.sigma-decompositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.uniqueness-set-quotientsᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Properties

### Characterization of equality in the type of equivalence relations

```agda
relate-same-elements-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  equivalence-relationᵉ l2ᵉ Aᵉ → equivalence-relationᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-equivalence-relationᵉ Rᵉ Sᵉ =
  relates-same-elements-Relation-Propᵉ
    ( prop-equivalence-relationᵉ Rᵉ)
    ( prop-equivalence-relationᵉ Sᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  refl-relate-same-elements-equivalence-relationᵉ :
    relate-same-elements-equivalence-relationᵉ Rᵉ Rᵉ
  refl-relate-same-elements-equivalence-relationᵉ =
    refl-relates-same-elements-Relation-Propᵉ (prop-equivalence-relationᵉ Rᵉ)

  is-torsorial-relate-same-elements-equivalence-relationᵉ :
    is-torsorialᵉ (relate-same-elements-equivalence-relationᵉ Rᵉ)
  is-torsorial-relate-same-elements-equivalence-relationᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-relates-same-elements-Relation-Propᵉ
        ( prop-equivalence-relationᵉ Rᵉ))
      ( is-prop-is-equivalence-relationᵉ)
      ( prop-equivalence-relationᵉ Rᵉ)
      ( refl-relate-same-elements-equivalence-relationᵉ)
      ( is-equivalence-relation-prop-equivalence-relationᵉ Rᵉ)

  relate-same-elements-eq-equivalence-relationᵉ :
    (Sᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
    (Rᵉ ＝ᵉ Sᵉ) → relate-same-elements-equivalence-relationᵉ Rᵉ Sᵉ
  relate-same-elements-eq-equivalence-relationᵉ .Rᵉ reflᵉ =
    refl-relate-same-elements-equivalence-relationᵉ

  is-equiv-relate-same-elements-eq-equivalence-relationᵉ :
    (Sᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
    is-equivᵉ (relate-same-elements-eq-equivalence-relationᵉ Sᵉ)
  is-equiv-relate-same-elements-eq-equivalence-relationᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-relate-same-elements-equivalence-relationᵉ
      relate-same-elements-eq-equivalence-relationᵉ

  extensionality-equivalence-relationᵉ :
    (Sᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
    (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relate-same-elements-equivalence-relationᵉ Rᵉ Sᵉ
  pr1ᵉ (extensionality-equivalence-relationᵉ Sᵉ) =
    relate-same-elements-eq-equivalence-relationᵉ Sᵉ
  pr2ᵉ (extensionality-equivalence-relationᵉ Sᵉ) =
    is-equiv-relate-same-elements-eq-equivalence-relationᵉ Sᵉ

  eq-relate-same-elements-equivalence-relationᵉ :
    (Sᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
    relate-same-elements-equivalence-relationᵉ Rᵉ Sᵉ → (Rᵉ ＝ᵉ Sᵉ)
  eq-relate-same-elements-equivalence-relationᵉ Sᵉ =
    map-inv-equivᵉ (extensionality-equivalence-relationᵉ Sᵉ)
```

### The type of equivalence relations on `A` is equivalent to the type of partitions on `A`

#### The partition obtained from an equivalence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-block-prop-partition-equivalence-relationᵉ :
    subtypeᵉ (l1ᵉ ⊔ l2ᵉ) (inhabited-subtypeᵉ l2ᵉ Aᵉ)
  is-block-prop-partition-equivalence-relationᵉ Qᵉ =
    is-equivalence-class-Propᵉ Rᵉ (subtype-inhabited-subtypeᵉ Qᵉ)

  is-block-partition-equivalence-relationᵉ :
    inhabited-subtypeᵉ l2ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-block-partition-equivalence-relationᵉ Qᵉ =
    type-Propᵉ (is-block-prop-partition-equivalence-relationᵉ Qᵉ)

  abstract
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relationᵉ :
      is-partitionᵉ
        ( is-equivalence-class-inhabited-subtype-equivalence-relationᵉ Rᵉ)
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relationᵉ xᵉ =
      is-contr-equivᵉ
        ( Σᵉ ( Σᵉ ( equivalence-classᵉ Rᵉ)
                ( λ Cᵉ → is-in-equivalence-classᵉ Rᵉ Cᵉ xᵉ))
            ( λ tᵉ → is-inhabited-subtypeᵉ (subtype-equivalence-classᵉ Rᵉ (pr1ᵉ tᵉ))))
        ( ( equiv-right-swap-Σᵉ) ∘eᵉ
          ( equiv-Σᵉ
            ( λ Qᵉ → is-in-subtypeᵉ (subtype-equivalence-classᵉ Rᵉ (pr1ᵉ Qᵉ)) xᵉ)
            ( equiv-right-swap-Σᵉ)
            ( λ Qᵉ → id-equivᵉ)))
        ( is-contr-Σᵉ
          ( is-torsorial-is-in-equivalence-classᵉ Rᵉ xᵉ)
          ( center-total-is-in-equivalence-classᵉ Rᵉ xᵉ)
          ( is-proof-irrelevant-is-propᵉ
            ( is-prop-type-trunc-Propᵉ)
            ( is-inhabited-subtype-equivalence-classᵉ Rᵉ (classᵉ Rᵉ xᵉ))))

  partition-equivalence-relationᵉ : partitionᵉ l2ᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
  pr1ᵉ partition-equivalence-relationᵉ =
    is-block-prop-partition-equivalence-relationᵉ
  pr2ᵉ partition-equivalence-relationᵉ =
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relationᵉ

  equiv-block-equivalence-classᵉ :
    equivalence-classᵉ Rᵉ ≃ᵉ block-partitionᵉ partition-equivalence-relationᵉ
  equiv-block-equivalence-classᵉ =
    ( compute-block-partitionᵉ partition-equivalence-relationᵉ) ∘eᵉ
    ( ( equiv-right-swap-Σᵉ) ∘eᵉ
      ( inv-equivᵉ
        ( equiv-inclusion-is-full-subtypeᵉ
          ( is-inhabited-subtype-Propᵉ ∘ᵉ subtype-equivalence-classᵉ Rᵉ)
          ( is-inhabited-subtype-equivalence-classᵉ Rᵉ))))
```

#### The equivalence relation obtained from a partition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  sim-partitionᵉ : Aᵉ → Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  sim-partitionᵉ xᵉ yᵉ =
    Σᵉ ( block-partitionᵉ Pᵉ)
      ( λ Qᵉ → is-in-block-partitionᵉ Pᵉ Qᵉ xᵉ ×ᵉ is-in-block-partitionᵉ Pᵉ Qᵉ yᵉ)

  is-proof-irrelevant-sim-partitionᵉ :
    (xᵉ yᵉ : Aᵉ) → is-proof-irrelevantᵉ (sim-partitionᵉ xᵉ yᵉ)
  is-proof-irrelevant-sim-partitionᵉ xᵉ yᵉ (Qᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    is-contr-equiv'ᵉ
      ( Σᵉ ( Σᵉ ( block-partitionᵉ Pᵉ)
              ( λ Bᵉ → is-in-block-partitionᵉ Pᵉ Bᵉ xᵉ))
          ( λ Bᵉ → is-in-block-partitionᵉ Pᵉ (pr1ᵉ Bᵉ) yᵉ))
      ( associative-Σᵉ
        ( block-partitionᵉ Pᵉ)
        ( λ Uᵉ → is-in-block-partitionᵉ Pᵉ Uᵉ xᵉ)
        ( λ Uᵉ → is-in-block-partitionᵉ Pᵉ (pr1ᵉ Uᵉ) yᵉ))
      ( is-contr-Σᵉ
        ( is-contr-block-containing-element-partitionᵉ Pᵉ xᵉ)
        ( pairᵉ Qᵉ pᵉ)
        ( is-proof-irrelevant-is-propᵉ
          ( is-prop-is-in-block-partitionᵉ Pᵉ Qᵉ yᵉ)
          ( qᵉ)))

  is-prop-sim-partitionᵉ : (xᵉ yᵉ : Aᵉ) → is-propᵉ (sim-partitionᵉ xᵉ yᵉ)
  is-prop-sim-partitionᵉ xᵉ yᵉ =
    is-prop-is-proof-irrelevantᵉ (is-proof-irrelevant-sim-partitionᵉ xᵉ yᵉ)

  prop-equivalence-relation-partitionᵉ : Relation-Propᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
  pr1ᵉ (prop-equivalence-relation-partitionᵉ xᵉ yᵉ) = sim-partitionᵉ xᵉ yᵉ
  pr2ᵉ (prop-equivalence-relation-partitionᵉ xᵉ yᵉ) = is-prop-sim-partitionᵉ xᵉ yᵉ

  refl-sim-partitionᵉ : is-reflexiveᵉ sim-partitionᵉ
  pr1ᵉ (refl-sim-partitionᵉ xᵉ) = class-partitionᵉ Pᵉ xᵉ
  pr1ᵉ (pr2ᵉ (refl-sim-partitionᵉ xᵉ)) = is-in-block-class-partitionᵉ Pᵉ xᵉ
  pr2ᵉ (pr2ᵉ (refl-sim-partitionᵉ xᵉ)) = is-in-block-class-partitionᵉ Pᵉ xᵉ

  symmetric-sim-partitionᵉ : is-symmetricᵉ sim-partitionᵉ
  pr1ᵉ (symmetric-sim-partitionᵉ xᵉ yᵉ (Qᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) = Qᵉ
  pr1ᵉ (pr2ᵉ (symmetric-sim-partitionᵉ xᵉ yᵉ (Qᵉ ,ᵉ pᵉ ,ᵉ qᵉ))) = qᵉ
  pr2ᵉ (pr2ᵉ (symmetric-sim-partitionᵉ xᵉ yᵉ (Qᵉ ,ᵉ pᵉ ,ᵉ qᵉ))) = pᵉ

  transitive-sim-partitionᵉ : is-transitiveᵉ sim-partitionᵉ
  pr1ᵉ (transitive-sim-partitionᵉ xᵉ yᵉ zᵉ (Bᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (B'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ)) = Bᵉ
  pr1ᵉ (pr2ᵉ (transitive-sim-partitionᵉ xᵉ yᵉ zᵉ (Bᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (B'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ))) =
    backward-implicationᵉ
      ( has-same-elements-eq-inhabited-subtypeᵉ
        ( inhabited-subtype-block-partitionᵉ Pᵉ Bᵉ)
        ( inhabited-subtype-block-partitionᵉ Pᵉ B'ᵉ)
        ( apᵉ
          ( inhabited-subtype-block-partitionᵉ Pᵉ)
          ( apᵉ
            ( pr1ᵉ)
            ( eq-is-contrᵉ
              ( is-contr-block-containing-element-partitionᵉ Pᵉ yᵉ)
              { Bᵉ ,ᵉ pᵉ}
              { B'ᵉ ,ᵉ q'ᵉ})))
        ( xᵉ))
      ( p'ᵉ)
  pr2ᵉ (pr2ᵉ (transitive-sim-partitionᵉ xᵉ yᵉ zᵉ (Bᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (B'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ))) = qᵉ

  equivalence-relation-partitionᵉ : equivalence-relationᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
  pr1ᵉ equivalence-relation-partitionᵉ = prop-equivalence-relation-partitionᵉ
  pr1ᵉ (pr2ᵉ equivalence-relation-partitionᵉ) = refl-sim-partitionᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-partitionᵉ)) = symmetric-sim-partitionᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-partitionᵉ)) = transitive-sim-partitionᵉ

  is-inhabited-subtype-prop-equivalence-relation-partitionᵉ :
    (aᵉ : Aᵉ) → is-inhabited-subtypeᵉ (prop-equivalence-relation-partitionᵉ aᵉ)
  is-inhabited-subtype-prop-equivalence-relation-partitionᵉ aᵉ =
    unit-trunc-Propᵉ (aᵉ ,ᵉ refl-sim-partitionᵉ aᵉ)

  inhabited-subtype-equivalence-relation-partitionᵉ :
    (aᵉ : Aᵉ) → inhabited-subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
  pr1ᵉ (inhabited-subtype-equivalence-relation-partitionᵉ aᵉ) =
    prop-equivalence-relation-partitionᵉ aᵉ
  pr2ᵉ (inhabited-subtype-equivalence-relation-partitionᵉ aᵉ) =
    is-inhabited-subtype-prop-equivalence-relation-partitionᵉ aᵉ

  is-block-inhabited-subtype-equivalence-relation-partitionᵉ :
    (aᵉ : Aᵉ) →
    is-block-partitionᵉ
      ( partition-equivalence-relationᵉ equivalence-relation-partitionᵉ)
      ( inhabited-subtype-equivalence-relation-partitionᵉ aᵉ)
  is-block-inhabited-subtype-equivalence-relation-partitionᵉ aᵉ =
    unit-trunc-Propᵉ (aᵉ ,ᵉ λ xᵉ → pairᵉ idᵉ idᵉ)
```

#### The equivalence relation obtained from the partition induced by an equivalence relation `R` is `R` itself

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  relate-same-elements-equivalence-relation-partition-equivalence-relationᵉ :
    relate-same-elements-equivalence-relationᵉ
      ( equivalence-relation-partitionᵉ (partition-equivalence-relationᵉ Rᵉ))
      ( Rᵉ)
  pr1ᵉ
    ( relate-same-elements-equivalence-relation-partition-equivalence-relationᵉ
      xᵉ yᵉ)
    ( Cᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    apply-universal-property-trunc-Propᵉ
      ( is-block-inhabited-subtype-block-partitionᵉ
        ( partition-equivalence-relationᵉ Rᵉ)
        ( Cᵉ))
      ( prop-equivalence-relationᵉ Rᵉ xᵉ yᵉ)
      ( λ (zᵉ ,ᵉ Kᵉ) →
        transitive-equivalence-relationᵉ Rᵉ
          xᵉ _ yᵉ
          ( forward-implicationᵉ (Kᵉ yᵉ) qᵉ)
          ( symmetric-equivalence-relationᵉ Rᵉ _ xᵉ (forward-implicationᵉ (Kᵉ xᵉ) pᵉ)))
  pr1ᵉ
    ( pr2ᵉ
      ( relate-same-elements-equivalence-relation-partition-equivalence-relationᵉ
        xᵉ yᵉ)
      ( rᵉ)) =
    make-block-partitionᵉ
      ( partition-equivalence-relationᵉ Rᵉ)
      ( inhabited-subtype-equivalence-classᵉ Rᵉ (classᵉ Rᵉ xᵉ))
      ( is-equivalence-class-equivalence-classᵉ Rᵉ (classᵉ Rᵉ xᵉ))
  pr1ᵉ
    ( pr2ᵉ
      ( pr2ᵉ
        ( relate-same-elements-equivalence-relation-partition-equivalence-relationᵉ
          xᵉ yᵉ)
        ( rᵉ))) =
    make-is-in-block-partitionᵉ
      ( partition-equivalence-relationᵉ Rᵉ)
      ( inhabited-subtype-equivalence-classᵉ Rᵉ (classᵉ Rᵉ xᵉ))
      ( is-equivalence-class-equivalence-classᵉ Rᵉ (classᵉ Rᵉ xᵉ))
      ( xᵉ)
      ( refl-equivalence-relationᵉ Rᵉ xᵉ)
  pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ
        ( relate-same-elements-equivalence-relation-partition-equivalence-relationᵉ
          xᵉ yᵉ)
        ( rᵉ))) =
    make-is-in-block-partitionᵉ
      ( partition-equivalence-relationᵉ Rᵉ)
      ( inhabited-subtype-equivalence-classᵉ Rᵉ (classᵉ Rᵉ xᵉ))
      ( is-equivalence-class-equivalence-classᵉ Rᵉ (classᵉ Rᵉ xᵉ))
      ( yᵉ)
      ( rᵉ)

is-section-equivalence-relation-partition-equivalence-relationᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (Rᵉ : equivalence-relationᵉ lᵉ Aᵉ) →
  equivalence-relation-partitionᵉ (partition-equivalence-relationᵉ Rᵉ) ＝ᵉ Rᵉ
is-section-equivalence-relation-partition-equivalence-relationᵉ Rᵉ =
  eq-relate-same-elements-equivalence-relationᵉ
    ( equivalence-relation-partitionᵉ (partition-equivalence-relationᵉ Rᵉ))
    ( Rᵉ)
    ( relate-same-elements-equivalence-relation-partition-equivalence-relationᵉ
      Rᵉ)
```

#### The partition obtained from the equivalence relation induced by a partition is the partition itself

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : partitionᵉ l1ᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-block-is-equivalence-class-equivalence-relation-partitionᵉ :
      (Qᵉ : inhabited-subtypeᵉ l1ᵉ Aᵉ) →
      is-equivalence-classᵉ
        ( equivalence-relation-partitionᵉ Pᵉ)
        ( subtype-inhabited-subtypeᵉ Qᵉ) →
      is-block-partitionᵉ Pᵉ Qᵉ
    is-block-is-equivalence-class-equivalence-relation-partitionᵉ Qᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( subtype-partitionᵉ Pᵉ Qᵉ)
        ( λ (aᵉ ,ᵉ Kᵉ) →
          trᵉ
            ( is-block-partitionᵉ Pᵉ)
            ( invᵉ
              ( eq-has-same-elements-inhabited-subtypeᵉ Qᵉ
                ( inhabited-subtype-block-partitionᵉ Pᵉ (class-partitionᵉ Pᵉ aᵉ))
                ( λ xᵉ →
                  ( iff-equivᵉ
                    ( ( left-unit-law-Σ-is-contrᵉ
                        ( is-contr-block-containing-element-partitionᵉ Pᵉ aᵉ)
                        ( center-block-containing-element-partitionᵉ Pᵉ aᵉ)) ∘eᵉ
                      ( inv-associative-Σᵉ
                        ( block-partitionᵉ Pᵉ)
                        ( λ Bᵉ → is-in-block-partitionᵉ Pᵉ Bᵉ aᵉ)
                        ( λ Bᵉ → is-in-block-partitionᵉ Pᵉ (pr1ᵉ Bᵉ) xᵉ)))) ∘iffᵉ
                  ( Kᵉ xᵉ))))
            ( is-block-class-partitionᵉ Pᵉ aᵉ))

  abstract
    is-equivalence-class-is-block-partitionᵉ :
      (Qᵉ : inhabited-subtypeᵉ l1ᵉ Aᵉ) →
      is-block-partitionᵉ Pᵉ Qᵉ →
      is-equivalence-classᵉ
        ( equivalence-relation-partitionᵉ Pᵉ)
        ( subtype-inhabited-subtypeᵉ Qᵉ)
    is-equivalence-class-is-block-partitionᵉ Qᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-inhabited-subtype-inhabited-subtypeᵉ Qᵉ)
        ( is-equivalence-class-Propᵉ
          ( equivalence-relation-partitionᵉ Pᵉ)
          ( subtype-inhabited-subtypeᵉ Qᵉ))
        ( λ (aᵉ ,ᵉ qᵉ) →
          unit-trunc-Propᵉ
            ( pairᵉ
              ( aᵉ)
              ( λ xᵉ →
                iff-equivᵉ
                ( ( inv-equivᵉ
                    ( ( left-unit-law-Σ-is-contrᵉ
                        ( is-contr-block-containing-element-partitionᵉ Pᵉ aᵉ)
                        ( pairᵉ
                          ( make-block-partitionᵉ Pᵉ Qᵉ Hᵉ)
                          ( make-is-in-block-partitionᵉ Pᵉ Qᵉ Hᵉ aᵉ qᵉ))) ∘eᵉ
                      ( inv-associative-Σᵉ
                        ( block-partitionᵉ Pᵉ)
                        ( λ Bᵉ → is-in-block-partitionᵉ Pᵉ Bᵉ aᵉ)
                        ( λ Bᵉ → is-in-block-partitionᵉ Pᵉ (pr1ᵉ Bᵉ) xᵉ)))) ∘eᵉ
                  ( compute-is-in-block-partitionᵉ Pᵉ Qᵉ Hᵉ xᵉ)))))

  has-same-elements-partition-equivalence-relation-partitionᵉ :
    has-same-elements-subtypeᵉ
      ( subtype-partitionᵉ
        ( partition-equivalence-relationᵉ (equivalence-relation-partitionᵉ Pᵉ)))
      ( subtype-partitionᵉ Pᵉ)
  pr1ᵉ (has-same-elements-partition-equivalence-relation-partitionᵉ Qᵉ) Hᵉ =
    is-block-is-equivalence-class-equivalence-relation-partitionᵉ Qᵉ Hᵉ
  pr2ᵉ (has-same-elements-partition-equivalence-relation-partitionᵉ Qᵉ) Hᵉ =
    is-equivalence-class-is-block-partitionᵉ Qᵉ Hᵉ

is-retraction-equivalence-relation-partition-equivalence-relationᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (Pᵉ : partitionᵉ lᵉ lᵉ Aᵉ) →
  partition-equivalence-relationᵉ (equivalence-relation-partitionᵉ Pᵉ) ＝ᵉ Pᵉ
is-retraction-equivalence-relation-partition-equivalence-relationᵉ Pᵉ =
  eq-has-same-blocks-partitionᵉ
    ( partition-equivalence-relationᵉ (equivalence-relation-partitionᵉ Pᵉ))
    ( Pᵉ)
    ( has-same-elements-partition-equivalence-relation-partitionᵉ Pᵉ)
```

#### The map `equivalence-relation-partition` is an equivalence

```agda
abstract
  is-equiv-equivalence-relation-partitionᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    is-equivᵉ (equivalence-relation-partitionᵉ {lᵉ} {lᵉ} {lᵉ} {Aᵉ})
  is-equiv-equivalence-relation-partitionᵉ =
    is-equiv-is-invertibleᵉ
      partition-equivalence-relationᵉ
      is-section-equivalence-relation-partition-equivalence-relationᵉ
      is-retraction-equivalence-relation-partition-equivalence-relationᵉ

equiv-equivalence-relation-partitionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → partitionᵉ lᵉ lᵉ Aᵉ ≃ᵉ equivalence-relationᵉ lᵉ Aᵉ
pr1ᵉ equiv-equivalence-relation-partitionᵉ = equivalence-relation-partitionᵉ
pr2ᵉ equiv-equivalence-relation-partitionᵉ =
  is-equiv-equivalence-relation-partitionᵉ
```

### Equivalence relations are equivalent to set-indexed Σ-decompositions

#### The Σ-decomposition obtained from an equivalence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  set-indexed-Σ-decomposition-equivalence-relationᵉ :
    Set-Indexed-Σ-Decompositionᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ) Aᵉ
  set-indexed-Σ-decomposition-equivalence-relationᵉ =
    set-indexed-Σ-decomposition-partitionᵉ (partition-equivalence-relationᵉ Rᵉ)
```

### The type of equivalence relations on `A` is equivalent to the type of sets `X` equipped with a surjective map from `A` into `X`

#### The surjection into a set obtained from an equivalence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  surjection-into-set-equivalence-relationᵉ :
    Surjection-Into-Setᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
  pr1ᵉ surjection-into-set-equivalence-relationᵉ = quotient-Setᵉ Rᵉ
  pr2ᵉ surjection-into-set-equivalence-relationᵉ = surjection-quotient-mapᵉ Rᵉ
```

#### The equivalence relation obtained from a surjection into a set

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Xᵉ)
  where

  rel-map-into-setᵉ : Relation-Propᵉ l2ᵉ Aᵉ
  rel-map-into-setᵉ xᵉ yᵉ = Id-Propᵉ Xᵉ (fᵉ xᵉ) (fᵉ yᵉ)

  sim-map-into-setᵉ : Relationᵉ l2ᵉ Aᵉ
  sim-map-into-setᵉ xᵉ yᵉ = type-Propᵉ (rel-map-into-setᵉ xᵉ yᵉ)

  refl-sim-map-into-setᵉ : is-reflexiveᵉ sim-map-into-setᵉ
  refl-sim-map-into-setᵉ xᵉ = reflᵉ

  symmetric-sim-map-into-setᵉ : is-symmetricᵉ sim-map-into-setᵉ
  symmetric-sim-map-into-setᵉ xᵉ yᵉ Hᵉ = invᵉ Hᵉ

  transitive-sim-map-into-setᵉ : is-transitiveᵉ sim-map-into-setᵉ
  transitive-sim-map-into-setᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ = Kᵉ ∙ᵉ Hᵉ

  equivalence-relation-map-into-setᵉ : equivalence-relationᵉ l2ᵉ Aᵉ
  pr1ᵉ equivalence-relation-map-into-setᵉ = rel-map-into-setᵉ
  pr1ᵉ (pr2ᵉ equivalence-relation-map-into-setᵉ) xᵉ = refl-sim-map-into-setᵉ xᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-map-into-setᵉ)) xᵉ yᵉ =
    symmetric-sim-map-into-setᵉ xᵉ yᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-map-into-setᵉ)) xᵉ yᵉ zᵉ =
    transitive-sim-map-into-setᵉ xᵉ yᵉ zᵉ

  is-effective-map-into-setᵉ :
    is-effectiveᵉ equivalence-relation-map-into-setᵉ fᵉ
  is-effective-map-into-setᵉ xᵉ yᵉ = id-equivᵉ

equivalence-relation-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  Surjection-Into-Setᵉ l2ᵉ Aᵉ → equivalence-relationᵉ l2ᵉ Aᵉ
equivalence-relation-Surjection-Into-Setᵉ fᵉ =
  equivalence-relation-map-into-setᵉ
    ( set-Surjection-Into-Setᵉ fᵉ)
    ( map-Surjection-Into-Setᵉ fᵉ)

is-effective-map-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Surjection-Into-Setᵉ l2ᵉ Aᵉ) →
  is-effectiveᵉ
    ( equivalence-relation-Surjection-Into-Setᵉ fᵉ)
    ( map-Surjection-Into-Setᵉ fᵉ)
is-effective-map-Surjection-Into-Setᵉ fᵉ =
  is-effective-map-into-setᵉ
    ( set-Surjection-Into-Setᵉ fᵉ)
    ( map-Surjection-Into-Setᵉ fᵉ)
```

#### The equivalence relation obtained from the quotient map induced by an equivalence relation is that same equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relationᵉ :
    relate-same-elements-equivalence-relationᵉ
      ( equivalence-relation-Surjection-Into-Setᵉ
        ( surjection-into-set-equivalence-relationᵉ Rᵉ))
      ( Rᵉ)
  relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relationᵉ
    xᵉ yᵉ =
    iff-equivᵉ (is-effective-quotient-mapᵉ Rᵉ xᵉ yᵉ)

is-retraction-equivalence-relation-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ) →
  equivalence-relation-Surjection-Into-Setᵉ
    ( surjection-into-set-equivalence-relationᵉ Rᵉ) ＝ᵉ
  Rᵉ
is-retraction-equivalence-relation-Surjection-Into-Setᵉ Rᵉ =
  eq-relate-same-elements-equivalence-relationᵉ
    ( equivalence-relation-Surjection-Into-Setᵉ
      ( surjection-into-set-equivalence-relationᵉ Rᵉ))
    ( Rᵉ)
    ( relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relationᵉ
      Rᵉ)
```

#### The surjection into a set obtained from the equivalence relation induced by a surjection into a set is the original surjection into a set

```agda
equiv-surjection-into-set-equivalence-relation-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Surjection-Into-Setᵉ l2ᵉ Aᵉ) →
  equiv-Surjection-Into-Setᵉ
    ( surjection-into-set-equivalence-relationᵉ
      ( equivalence-relation-Surjection-Into-Setᵉ fᵉ))
    ( fᵉ)
equiv-surjection-into-set-equivalence-relation-Surjection-Into-Setᵉ fᵉ =
  centerᵉ
    ( uniqueness-set-quotientᵉ
      ( equivalence-relation-Surjection-Into-Setᵉ fᵉ)
      ( quotient-Setᵉ (equivalence-relation-Surjection-Into-Setᵉ fᵉ))
      ( reflecting-map-quotient-mapᵉ
        ( equivalence-relation-Surjection-Into-Setᵉ fᵉ))
      ( is-set-quotient-set-quotientᵉ
        ( equivalence-relation-Surjection-Into-Setᵉ fᵉ))
      ( set-Surjection-Into-Setᵉ fᵉ)
      ( pairᵉ
        ( map-Surjection-Into-Setᵉ fᵉ)
        ( λ Hᵉ → Hᵉ))
      ( is-set-quotient-is-surjective-and-effectiveᵉ
        ( equivalence-relation-Surjection-Into-Setᵉ fᵉ)
        ( set-Surjection-Into-Setᵉ fᵉ)
        ( pr1ᵉ (pr2ᵉ fᵉ) ,ᵉ (λ {xᵉ} {yᵉ} zᵉ → zᵉ))
        ( pairᵉ
          ( is-surjective-Surjection-Into-Setᵉ fᵉ)
          ( is-effective-map-Surjection-Into-Setᵉ fᵉ))))

is-section-equivalence-relation-Surjection-Into-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Surjection-Into-Setᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ) →
  surjection-into-set-equivalence-relationᵉ
    ( equivalence-relation-Surjection-Into-Setᵉ fᵉ) ＝ᵉ
  fᵉ
is-section-equivalence-relation-Surjection-Into-Setᵉ fᵉ =
  eq-equiv-Surjection-Into-Setᵉ
    ( surjection-into-set-equivalence-relationᵉ
      ( equivalence-relation-Surjection-Into-Setᵉ fᵉ))
    ( fᵉ)
    ( equiv-surjection-into-set-equivalence-relation-Surjection-Into-Setᵉ fᵉ)
```

#### The type of equivalence relations on `A` is equivalent to the type of surjections from `A` into a set

```agda
is-equiv-surjection-into-set-equivalence-relationᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  is-equivᵉ (surjection-into-set-equivalence-relationᵉ {l1ᵉ} {l1ᵉ} {Aᵉ})
is-equiv-surjection-into-set-equivalence-relationᵉ {l1ᵉ} {Aᵉ} =
  is-equiv-is-invertibleᵉ
    ( equivalence-relation-Surjection-Into-Setᵉ {l1ᵉ} {l1ᵉ} {Aᵉ})
    ( is-section-equivalence-relation-Surjection-Into-Setᵉ {l1ᵉ} {l1ᵉ} {Aᵉ})
    ( is-retraction-equivalence-relation-Surjection-Into-Setᵉ {l1ᵉ} {l1ᵉ} {Aᵉ})

equiv-surjection-into-set-equivalence-relationᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  equivalence-relationᵉ l1ᵉ Aᵉ ≃ᵉ Surjection-Into-Setᵉ l1ᵉ Aᵉ
pr1ᵉ (equiv-surjection-into-set-equivalence-relationᵉ Aᵉ) =
  surjection-into-set-equivalence-relationᵉ
pr2ᵉ (equiv-surjection-into-set-equivalence-relationᵉ Aᵉ) =
  is-equiv-surjection-into-set-equivalence-relationᵉ
```

### Equality on a set is an equivalence relation

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ)
  where

  Id-equivalence-relationᵉ : equivalence-relationᵉ l1ᵉ (type-Setᵉ Aᵉ)
  pr1ᵉ Id-equivalence-relationᵉ = Id-Propᵉ Aᵉ
  pr1ᵉ (pr2ᵉ Id-equivalence-relationᵉ) _ = reflᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ Id-equivalence-relationᵉ)) _ _ = invᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ Id-equivalence-relationᵉ)) _ _ _ Hᵉ Kᵉ = Kᵉ ∙ᵉ Hᵉ

  id-reflects-Id-equivalence-relationᵉ :
    reflects-equivalence-relationᵉ Id-equivalence-relationᵉ idᵉ
  id-reflects-Id-equivalence-relationᵉ = idᵉ

  id-reflecting-map-Id-equivalence-relationᵉ :
    reflecting-map-equivalence-relationᵉ Id-equivalence-relationᵉ (type-Setᵉ Aᵉ)
  pr1ᵉ id-reflecting-map-Id-equivalence-relationᵉ = idᵉ
  pr2ᵉ id-reflecting-map-Id-equivalence-relationᵉ =
    id-reflects-Id-equivalence-relationᵉ

  is-surjective-and-effective-id-Id-equivalence-relationᵉ :
    is-surjective-and-effectiveᵉ Id-equivalence-relationᵉ idᵉ
  pr1ᵉ is-surjective-and-effective-id-Id-equivalence-relationᵉ aᵉ =
    unit-trunc-Propᵉ (aᵉ ,ᵉ reflᵉ)
  pr2ᵉ is-surjective-and-effective-id-Id-equivalence-relationᵉ aᵉ bᵉ = id-equivᵉ
```

### For any set `A`, `Id` is a set quotient for the equality relation

```agda
module _
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ)
  where

  is-set-quotient-id-Id-equivalence-relationᵉ :
    is-set-quotientᵉ
      ( Id-equivalence-relationᵉ Aᵉ)
      ( Aᵉ)
      ( id-reflecting-map-Id-equivalence-relationᵉ Aᵉ)
  is-set-quotient-id-Id-equivalence-relationᵉ =
    is-set-quotient-is-surjective-and-effectiveᵉ (Id-equivalence-relationᵉ Aᵉ) Aᵉ
      ( id-reflecting-map-Id-equivalence-relationᵉ Aᵉ)
      ( is-surjective-and-effective-id-Id-equivalence-relationᵉ Aᵉ)
```
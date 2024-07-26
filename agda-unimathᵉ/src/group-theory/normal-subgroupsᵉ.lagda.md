# Normal subgroups

```agda
module group-theory.normal-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.binary-transportᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.congruence-relations-groupsᵉ
open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ normalᵉ subgroupᵉ ofᵉ `G`ᵉ isᵉ aᵉ subgroupᵉ `H`ᵉ ofᵉ `G`ᵉ whichᵉ isᵉ closedᵉ underᵉ
conjugation.ᵉ

## Definition

```agda
is-normal-prop-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-normal-prop-Subgroupᵉ Gᵉ Hᵉ =
  Π-Propᵉ
    ( type-Groupᵉ Gᵉ)
    ( λ gᵉ →
      Π-Propᵉ
        ( type-Subgroupᵉ Gᵉ Hᵉ)
        ( λ hᵉ →
          subset-Subgroupᵉ Gᵉ Hᵉ
            ( conjugation-Groupᵉ Gᵉ gᵉ (inclusion-Subgroupᵉ Gᵉ Hᵉ hᵉ))))

is-normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-normal-Subgroupᵉ Gᵉ Hᵉ = type-Propᵉ (is-normal-prop-Subgroupᵉ Gᵉ Hᵉ)

is-prop-is-normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) →
  is-propᵉ (is-normal-Subgroupᵉ Gᵉ Hᵉ)
is-prop-is-normal-Subgroupᵉ Gᵉ Hᵉ =
  is-prop-type-Propᵉ (is-normal-prop-Subgroupᵉ Gᵉ Hᵉ)

is-normal-Subgroup'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-normal-Subgroup'ᵉ Gᵉ Hᵉ =
  (xᵉ : type-Groupᵉ Gᵉ) (yᵉ : type-Subgroupᵉ Gᵉ Hᵉ) →
  is-in-Subgroupᵉ Gᵉ Hᵉ
    ( conjugation-Group'ᵉ Gᵉ xᵉ (inclusion-Subgroupᵉ Gᵉ Hᵉ yᵉ))

is-normal-is-normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) →
  is-normal-Subgroupᵉ Gᵉ Hᵉ → is-normal-Subgroup'ᵉ Gᵉ Hᵉ
is-normal-is-normal-Subgroupᵉ Gᵉ Hᵉ Kᵉ xᵉ yᵉ =
  trᵉ
    ( is-in-Subgroupᵉ Gᵉ Hᵉ)
    ( invᵉ (htpy-conjugation-Groupᵉ Gᵉ xᵉ (inclusion-Subgroupᵉ Gᵉ Hᵉ yᵉ)))
    ( Kᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ)

is-normal-is-normal-Subgroup'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) →
  is-normal-Subgroup'ᵉ Gᵉ Hᵉ → is-normal-Subgroupᵉ Gᵉ Hᵉ
is-normal-is-normal-Subgroup'ᵉ Gᵉ Hᵉ Kᵉ xᵉ yᵉ =
  trᵉ
    ( is-in-Subgroupᵉ Gᵉ Hᵉ)
    ( invᵉ (htpy-conjugation-Group'ᵉ Gᵉ xᵉ (inclusion-Subgroupᵉ Gᵉ Hᵉ yᵉ)))
    ( Kᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ)

Normal-Subgroupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Normal-Subgroupᵉ l2ᵉ Gᵉ = Σᵉ (Subgroupᵉ l2ᵉ Gᵉ) (is-normal-Subgroupᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  subgroup-Normal-Subgroupᵉ : Subgroupᵉ l2ᵉ Gᵉ
  subgroup-Normal-Subgroupᵉ = pr1ᵉ Nᵉ

  subset-Normal-Subgroupᵉ : subset-Groupᵉ l2ᵉ Gᵉ
  subset-Normal-Subgroupᵉ = subset-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  type-Normal-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Normal-Subgroupᵉ = type-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  inclusion-Normal-Subgroupᵉ : type-Normal-Subgroupᵉ → type-Groupᵉ Gᵉ
  inclusion-Normal-Subgroupᵉ =
    inclusion-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-emb-inclusion-Normal-Subgroupᵉ : is-embᵉ inclusion-Normal-Subgroupᵉ
  is-emb-inclusion-Normal-Subgroupᵉ =
    is-emb-inclusion-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  emb-inclusion-Normal-Subgroupᵉ : type-Normal-Subgroupᵉ ↪ᵉ type-Groupᵉ Gᵉ
  emb-inclusion-Normal-Subgroupᵉ =
    emb-inclusion-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-in-Normal-Subgroupᵉ : type-Groupᵉ Gᵉ → UUᵉ l2ᵉ
  is-in-Normal-Subgroupᵉ = is-in-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-closed-under-eq-Normal-Subgroupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-in-Normal-Subgroupᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-Normal-Subgroupᵉ yᵉ
  is-closed-under-eq-Normal-Subgroupᵉ =
    is-closed-under-eq-subtypeᵉ subset-Normal-Subgroupᵉ

  is-closed-under-eq-Normal-Subgroup'ᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-in-Normal-Subgroupᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-Normal-Subgroupᵉ xᵉ
  is-closed-under-eq-Normal-Subgroup'ᵉ =
    is-closed-under-eq-subtype'ᵉ subset-Normal-Subgroupᵉ

  is-prop-is-in-Normal-Subgroupᵉ :
    (gᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (is-in-Normal-Subgroupᵉ gᵉ)
  is-prop-is-in-Normal-Subgroupᵉ =
    is-prop-is-in-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-in-normal-subgroup-inclusion-Normal-Subgroupᵉ :
    (xᵉ : type-Normal-Subgroupᵉ) →
    is-in-Normal-Subgroupᵉ (inclusion-Normal-Subgroupᵉ xᵉ)
  is-in-normal-subgroup-inclusion-Normal-Subgroupᵉ =
    is-in-subgroup-inclusion-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-subgroup-Normal-Subgroupᵉ :
    is-subgroup-subset-Groupᵉ Gᵉ subset-Normal-Subgroupᵉ
  is-subgroup-Normal-Subgroupᵉ =
    is-subgroup-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  contains-unit-Normal-Subgroupᵉ : is-in-Normal-Subgroupᵉ (unit-Groupᵉ Gᵉ)
  contains-unit-Normal-Subgroupᵉ =
    contains-unit-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  unit-Normal-Subgroupᵉ : type-Normal-Subgroupᵉ
  unit-Normal-Subgroupᵉ = unit-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-closed-under-multiplication-Normal-Subgroupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-Normal-Subgroupᵉ
  is-closed-under-multiplication-Normal-Subgroupᵉ =
    is-closed-under-multiplication-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  mul-Normal-Subgroupᵉ :
    type-Normal-Subgroupᵉ → type-Normal-Subgroupᵉ → type-Normal-Subgroupᵉ
  mul-Normal-Subgroupᵉ = mul-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-closed-under-inverses-Normal-Subgroupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-Normal-Subgroupᵉ
  is-closed-under-inverses-Normal-Subgroupᵉ =
    is-closed-under-inverses-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  inv-Normal-Subgroupᵉ : type-Normal-Subgroupᵉ → type-Normal-Subgroupᵉ
  inv-Normal-Subgroupᵉ = inv-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-closed-under-inverses-Normal-Subgroup'ᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) →
    is-in-Normal-Subgroupᵉ (inv-Groupᵉ Gᵉ xᵉ) → is-in-Normal-Subgroupᵉ xᵉ
  is-closed-under-inverses-Normal-Subgroup'ᵉ =
    is-closed-under-inverses-Subgroup'ᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-in-normal-subgroup-left-factor-Normal-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-in-Normal-Subgroupᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) →
    is-in-Normal-Subgroupᵉ yᵉ → is-in-Normal-Subgroupᵉ xᵉ
  is-in-normal-subgroup-left-factor-Normal-Subgroupᵉ =
    is-in-subgroup-left-factor-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-in-normal-subgroup-right-factor-Normal-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-in-Normal-Subgroupᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) →
    is-in-Normal-Subgroupᵉ xᵉ → is-in-Normal-Subgroupᵉ yᵉ
  is-in-normal-subgroup-right-factor-Normal-Subgroupᵉ =
    is-in-subgroup-right-factor-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  group-Normal-Subgroupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-Normal-Subgroupᵉ = group-Subgroupᵉ Gᵉ subgroup-Normal-Subgroupᵉ

  is-normal-Normal-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-in-Normal-Subgroupᵉ yᵉ →
    is-in-Normal-Subgroupᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ)
  is-normal-Normal-Subgroupᵉ xᵉ yᵉ pᵉ = pr2ᵉ Nᵉ xᵉ (yᵉ ,ᵉ pᵉ)

  is-normal-Normal-Subgroup'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-in-Normal-Subgroupᵉ yᵉ →
    is-in-Normal-Subgroupᵉ (conjugation-Group'ᵉ Gᵉ xᵉ yᵉ)
  is-normal-Normal-Subgroup'ᵉ xᵉ yᵉ pᵉ =
    is-normal-is-normal-Subgroupᵉ Gᵉ
      ( subgroup-Normal-Subgroupᵉ)
      ( λ xᵉ yᵉ → is-normal-Normal-Subgroupᵉ xᵉ (pr1ᵉ yᵉ) (pr2ᵉ yᵉ))
      ( xᵉ)
      ( pairᵉ yᵉ pᵉ)

  closure-property-Normal-Subgroupᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    is-in-Normal-Subgroupᵉ yᵉ →
    is-in-Normal-Subgroupᵉ (mul-Groupᵉ Gᵉ xᵉ zᵉ) →
    is-in-Normal-Subgroupᵉ (mul-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) zᵉ)
  closure-property-Normal-Subgroupᵉ {xᵉ} {yᵉ} {zᵉ} pᵉ qᵉ =
    is-closed-under-eq-Normal-Subgroupᵉ
      ( is-closed-under-multiplication-Normal-Subgroupᵉ
        ( is-normal-Normal-Subgroupᵉ xᵉ yᵉ pᵉ)
        ( qᵉ))
      ( ( associative-mul-Groupᵉ Gᵉ
          ( mul-Groupᵉ Gᵉ xᵉ yᵉ)
          ( inv-Groupᵉ Gᵉ xᵉ)
          ( mul-Groupᵉ Gᵉ xᵉ zᵉ)) ∙ᵉ
        ( apᵉ
          ( mul-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ))
          ( is-retraction-left-div-Groupᵉ Gᵉ xᵉ zᵉ)))

  closure-property-Normal-Subgroup'ᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    is-in-Normal-Subgroupᵉ yᵉ →
    is-in-Normal-Subgroupᵉ (mul-Groupᵉ Gᵉ xᵉ zᵉ) →
    is-in-Normal-Subgroupᵉ (mul-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ yᵉ zᵉ))
  closure-property-Normal-Subgroup'ᵉ {xᵉ} {yᵉ} {zᵉ} pᵉ qᵉ =
    is-closed-under-eq-Normal-Subgroupᵉ
      ( closure-property-Normal-Subgroupᵉ pᵉ qᵉ)
      ( associative-mul-Groupᵉ Gᵉ xᵉ yᵉ zᵉ)

  conjugation-Normal-Subgroupᵉ :
    type-Groupᵉ Gᵉ → type-Normal-Subgroupᵉ → type-Normal-Subgroupᵉ
  pr1ᵉ (conjugation-Normal-Subgroupᵉ yᵉ uᵉ) =
    conjugation-Groupᵉ Gᵉ yᵉ (inclusion-Normal-Subgroupᵉ uᵉ)
  pr2ᵉ (conjugation-Normal-Subgroupᵉ yᵉ uᵉ) =
    is-normal-Normal-Subgroupᵉ yᵉ (pr1ᵉ uᵉ) (pr2ᵉ uᵉ)

  conjugation-Normal-Subgroup'ᵉ :
    type-Groupᵉ Gᵉ → type-Normal-Subgroupᵉ → type-Normal-Subgroupᵉ
  pr1ᵉ (conjugation-Normal-Subgroup'ᵉ yᵉ uᵉ) =
    conjugation-Group'ᵉ Gᵉ yᵉ (inclusion-Normal-Subgroupᵉ uᵉ)
  pr2ᵉ (conjugation-Normal-Subgroup'ᵉ yᵉ uᵉ) =
    is-normal-Normal-Subgroup'ᵉ yᵉ (pr1ᵉ uᵉ) (pr2ᵉ uᵉ)
```

## Properties

### Extensionality of the type of all normal subgroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  has-same-elements-Normal-Subgroupᵉ :
    {l3ᵉ : Level} → Normal-Subgroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Normal-Subgroupᵉ Kᵉ =
    has-same-elements-Subgroupᵉ Gᵉ
      ( subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( subgroup-Normal-Subgroupᵉ Gᵉ Kᵉ)

  extensionality-Normal-Subgroupᵉ :
    (Kᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ) →
    (Nᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Normal-Subgroupᵉ Kᵉ
  extensionality-Normal-Subgroupᵉ =
    extensionality-type-subtypeᵉ
      ( is-normal-prop-Subgroupᵉ Gᵉ)
      ( λ xᵉ yᵉ →
        is-normal-Normal-Subgroupᵉ Gᵉ Nᵉ xᵉ (pr1ᵉ yᵉ) (pr2ᵉ yᵉ))
      ( λ xᵉ → pairᵉ idᵉ idᵉ)
      ( extensionality-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ))

  eq-has-same-elements-Normal-Subgroupᵉ :
    (Kᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ) →
    has-same-elements-Normal-Subgroupᵉ Kᵉ → Nᵉ ＝ᵉ Kᵉ
  eq-has-same-elements-Normal-Subgroupᵉ Kᵉ =
    map-inv-equivᵉ (extensionality-Normal-Subgroupᵉ Kᵉ)
```

### The containment relation of normal subgroups

```agda
leq-prop-Normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Normal-Subgroupᵉ l2ᵉ Gᵉ → Normal-Subgroupᵉ l3ᵉ Gᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
leq-prop-Normal-Subgroupᵉ Gᵉ Hᵉ Kᵉ =
  leq-prop-Subgroupᵉ Gᵉ
    ( subgroup-Normal-Subgroupᵉ Gᵉ Hᵉ)
    ( subgroup-Normal-Subgroupᵉ Gᵉ Kᵉ)

leq-Normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Normal-Subgroupᵉ l2ᵉ Gᵉ → Normal-Subgroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
leq-Normal-Subgroupᵉ Gᵉ Hᵉ Kᵉ =
  leq-Subgroupᵉ Gᵉ
    ( subgroup-Normal-Subgroupᵉ Gᵉ Hᵉ)
    ( subgroup-Normal-Subgroupᵉ Gᵉ Kᵉ)

is-prop-leq-Normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) →
  is-propᵉ (leq-Normal-Subgroupᵉ Gᵉ Nᵉ Mᵉ)
is-prop-leq-Normal-Subgroupᵉ Gᵉ Nᵉ Mᵉ =
  is-prop-leq-Subgroupᵉ Gᵉ
    ( subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)
    ( subgroup-Normal-Subgroupᵉ Gᵉ Mᵉ)

refl-leq-Normal-Subgroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-reflexive-Large-Relationᵉ
    ( λ lᵉ → Normal-Subgroupᵉ lᵉ Gᵉ)
    ( leq-Normal-Subgroupᵉ Gᵉ)
refl-leq-Normal-Subgroupᵉ Gᵉ Hᵉ =
  refl-leq-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Hᵉ)

transitive-leq-Normal-Subgroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-transitive-Large-Relationᵉ
    ( λ lᵉ → Normal-Subgroupᵉ lᵉ Gᵉ)
    ( leq-Normal-Subgroupᵉ Gᵉ)
transitive-leq-Normal-Subgroupᵉ Gᵉ Hᵉ Kᵉ Lᵉ =
  transitive-leq-Subgroupᵉ Gᵉ
    ( subgroup-Normal-Subgroupᵉ Gᵉ Hᵉ)
    ( subgroup-Normal-Subgroupᵉ Gᵉ Kᵉ)
    ( subgroup-Normal-Subgroupᵉ Gᵉ Lᵉ)

antisymmetric-leq-Normal-Subgroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-antisymmetric-Large-Relationᵉ
    ( λ lᵉ → Normal-Subgroupᵉ lᵉ Gᵉ)
    ( leq-Normal-Subgroupᵉ Gᵉ)
antisymmetric-leq-Normal-Subgroupᵉ Gᵉ Hᵉ Kᵉ αᵉ βᵉ =
  eq-has-same-elements-Normal-Subgroupᵉ Gᵉ Hᵉ Kᵉ (λ xᵉ → (αᵉ xᵉ ,ᵉ βᵉ xᵉ))

Normal-Subgroup-Large-Preorderᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Large-Preorderᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
type-Large-Preorderᵉ (Normal-Subgroup-Large-Preorderᵉ Gᵉ) l2ᵉ =
  Normal-Subgroupᵉ l2ᵉ Gᵉ
leq-prop-Large-Preorderᵉ (Normal-Subgroup-Large-Preorderᵉ Gᵉ) Hᵉ Kᵉ =
  leq-prop-Normal-Subgroupᵉ Gᵉ Hᵉ Kᵉ
refl-leq-Large-Preorderᵉ (Normal-Subgroup-Large-Preorderᵉ Gᵉ) =
  refl-leq-Normal-Subgroupᵉ Gᵉ
transitive-leq-Large-Preorderᵉ (Normal-Subgroup-Large-Preorderᵉ Gᵉ) =
  transitive-leq-Normal-Subgroupᵉ Gᵉ

Normal-Subgroup-Preorderᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ) →
  Preorderᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Normal-Subgroup-Preorderᵉ l2ᵉ Gᵉ =
  preorder-Large-Preorderᵉ (Normal-Subgroup-Large-Preorderᵉ Gᵉ) l2ᵉ

Normal-Subgroup-Large-Posetᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
large-preorder-Large-Posetᵉ (Normal-Subgroup-Large-Posetᵉ Gᵉ) =
  Normal-Subgroup-Large-Preorderᵉ Gᵉ
antisymmetric-leq-Large-Posetᵉ (Normal-Subgroup-Large-Posetᵉ Gᵉ) =
  antisymmetric-leq-Normal-Subgroupᵉ Gᵉ

Normal-Subgroup-Posetᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ) →
  Posetᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Normal-Subgroup-Posetᵉ l2ᵉ Gᵉ =
  poset-Large-Posetᵉ (Normal-Subgroup-Large-Posetᵉ Gᵉ) l2ᵉ

preserves-order-subgroup-Normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) →
  leq-Normal-Subgroupᵉ Gᵉ Nᵉ Mᵉ →
  leq-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ) (subgroup-Normal-Subgroupᵉ Gᵉ Mᵉ)
preserves-order-subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ Mᵉ = idᵉ

subgroup-normal-subgroup-hom-Large-Posetᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  hom-Large-Posetᵉ
    ( λ lᵉ → lᵉ)
    ( Normal-Subgroup-Large-Posetᵉ Gᵉ)
    ( Subgroup-Large-Posetᵉ Gᵉ)
subgroup-normal-subgroup-hom-Large-Posetᵉ Gᵉ =
  make-hom-Large-Preorderᵉ
    ( subgroup-Normal-Subgroupᵉ Gᵉ)
    ( preserves-order-subgroup-Normal-Subgroupᵉ Gᵉ)
```

### Normal subgroups are in 1-1 correspondence with congruence relations on groups

#### The standard similarity relation obtained from a normal subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  sim-congruence-Normal-Subgroupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  sim-congruence-Normal-Subgroupᵉ =
    right-sim-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)

  is-prop-sim-congruence-Normal-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-propᵉ (sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Normal-Subgroupᵉ =
    is-prop-right-sim-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)

  prop-congruence-Normal-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → Propᵉ l2ᵉ
  prop-congruence-Normal-Subgroupᵉ =
    prop-right-equivalence-relation-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)
```

#### The left equivalence relation obtained from a normal subgroup

```agda
  left-equivalence-relation-congruence-Normal-Subgroupᵉ :
    equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ)
  left-equivalence-relation-congruence-Normal-Subgroupᵉ =
    left-equivalence-relation-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)

  left-sim-congruence-Normal-Subgroupᵉ :
    type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ → UUᵉ l2ᵉ
  left-sim-congruence-Normal-Subgroupᵉ =
    left-sim-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)
```

#### The left similarity relation of a normal subgroup relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-Normal-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ →
    left-sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ
  left-sim-sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ Hᵉ =
    is-closed-under-eq-Normal-Subgroupᵉ Gᵉ Nᵉ
      ( is-normal-Normal-Subgroupᵉ Gᵉ Nᵉ yᵉ
        ( inv-Groupᵉ Gᵉ (left-div-Groupᵉ Gᵉ xᵉ yᵉ))
        ( is-closed-under-inverses-Normal-Subgroupᵉ Gᵉ Nᵉ Hᵉ))
      ( ( apᵉ (conjugation-Groupᵉ Gᵉ yᵉ) (inv-left-div-Groupᵉ Gᵉ xᵉ yᵉ)) ∙ᵉ
        ( conjugation-left-div-Groupᵉ Gᵉ yᵉ xᵉ))

  sim-left-sim-congruence-Normal-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    left-sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ →
    sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ
  sim-left-sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ Hᵉ =
    is-closed-under-eq-Normal-Subgroupᵉ Gᵉ Nᵉ
      ( is-normal-Normal-Subgroup'ᵉ Gᵉ Nᵉ xᵉ
        ( inv-Groupᵉ Gᵉ (right-div-Groupᵉ Gᵉ xᵉ yᵉ))
        ( is-closed-under-inverses-Normal-Subgroupᵉ Gᵉ Nᵉ Hᵉ))
      ( ( apᵉ (conjugation-Group'ᵉ Gᵉ xᵉ) (inv-right-div-Groupᵉ Gᵉ xᵉ yᵉ)) ∙ᵉ
        ( conjugation-right-div-Groupᵉ Gᵉ yᵉ xᵉ))
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-Normal-Subgroupᵉ :
    is-reflexiveᵉ sim-congruence-Normal-Subgroupᵉ
  refl-congruence-Normal-Subgroupᵉ =
    refl-right-sim-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)

  symmetric-congruence-Normal-Subgroupᵉ :
    is-symmetricᵉ sim-congruence-Normal-Subgroupᵉ
  symmetric-congruence-Normal-Subgroupᵉ =
    symmetric-right-sim-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)

  transitive-congruence-Normal-Subgroupᵉ :
    is-transitiveᵉ sim-congruence-Normal-Subgroupᵉ
  transitive-congruence-Normal-Subgroupᵉ =
    transitive-right-sim-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)

  equivalence-relation-congruence-Normal-Subgroupᵉ :
    equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ)
  equivalence-relation-congruence-Normal-Subgroupᵉ =
    right-equivalence-relation-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)

  relate-same-elements-left-sim-congruence-Normal-Subgroupᵉ :
    relate-same-elements-equivalence-relationᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ)
      ( left-equivalence-relation-congruence-Normal-Subgroupᵉ)
  pr1ᵉ (relate-same-elements-left-sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ) =
    left-sim-sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ
  pr2ᵉ (relate-same-elements-left-sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ) =
    sim-left-sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ

  mul-congruence-Normal-Subgroupᵉ :
    is-congruence-Groupᵉ Gᵉ equivalence-relation-congruence-Normal-Subgroupᵉ
  mul-congruence-Normal-Subgroupᵉ
    {xᵉ} {x'ᵉ} {yᵉ} {y'ᵉ} pᵉ qᵉ =
    is-closed-under-eq-Normal-Subgroupᵉ Gᵉ Nᵉ
      ( closure-property-Normal-Subgroupᵉ Gᵉ Nᵉ pᵉ qᵉ)
      ( ( apᵉ
          ( mul-Group'ᵉ Gᵉ y'ᵉ)
          ( ( invᵉ
              ( associative-mul-Groupᵉ Gᵉ
                ( inv-Groupᵉ Gᵉ yᵉ)
                ( inv-Groupᵉ Gᵉ xᵉ)
                ( x'ᵉ))) ∙ᵉ
            ( apᵉ
              ( mul-Group'ᵉ Gᵉ x'ᵉ)
              ( invᵉ (distributive-inv-mul-Groupᵉ Gᵉ))))) ∙ᵉ
        ( associative-mul-Groupᵉ Gᵉ
          ( inv-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ))
          ( x'ᵉ)
          ( y'ᵉ)))

  congruence-Normal-Subgroupᵉ : congruence-Groupᵉ l2ᵉ Gᵉ
  pr1ᵉ congruence-Normal-Subgroupᵉ =
    equivalence-relation-congruence-Normal-Subgroupᵉ
  pr2ᵉ congruence-Normal-Subgroupᵉ =
    mul-congruence-Normal-Subgroupᵉ

  inv-congruence-Normal-Subgroupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Normal-Subgroupᵉ xᵉ yᵉ →
    sim-congruence-Normal-Subgroupᵉ (inv-Groupᵉ Gᵉ xᵉ) (inv-Groupᵉ Gᵉ yᵉ)
  inv-congruence-Normal-Subgroupᵉ =
    inv-congruence-Groupᵉ Gᵉ congruence-Normal-Subgroupᵉ

  unit-congruence-Normal-Subgroupᵉ :
    {xᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Normal-Subgroupᵉ xᵉ (unit-Groupᵉ Gᵉ) →
    is-in-Normal-Subgroupᵉ Gᵉ Nᵉ xᵉ
  unit-congruence-Normal-Subgroupᵉ {xᵉ} Hᵉ =
    is-closed-under-inverses-Normal-Subgroup'ᵉ Gᵉ Nᵉ xᵉ
      ( is-closed-under-eq-Normal-Subgroupᵉ Gᵉ Nᵉ Hᵉ
        ( right-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)))

  unit-congruence-Normal-Subgroup'ᵉ :
    {xᵉ : type-Groupᵉ Gᵉ} →
    is-in-Normal-Subgroupᵉ Gᵉ Nᵉ xᵉ →
    sim-congruence-Normal-Subgroupᵉ xᵉ (unit-Groupᵉ Gᵉ)
  unit-congruence-Normal-Subgroup'ᵉ {xᵉ} Hᵉ =
    is-closed-under-eq-Normal-Subgroup'ᵉ Gᵉ Nᵉ
      ( is-closed-under-inverses-Normal-Subgroupᵉ Gᵉ Nᵉ Hᵉ)
      ( right-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
```

#### The normal subgroup obtained from a congruence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ : congruence-Groupᵉ l2ᵉ Gᵉ)
  where

  subset-congruence-Groupᵉ : subset-Groupᵉ l2ᵉ Gᵉ
  subset-congruence-Groupᵉ = prop-congruence-Groupᵉ Gᵉ Rᵉ (unit-Groupᵉ Gᵉ)

  is-in-subset-congruence-Groupᵉ : (type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  is-in-subset-congruence-Groupᵉ = type-Propᵉ ∘ᵉ subset-congruence-Groupᵉ

  contains-unit-subset-congruence-Groupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-congruence-Groupᵉ
  contains-unit-subset-congruence-Groupᵉ =
    refl-congruence-Groupᵉ Gᵉ Rᵉ (unit-Groupᵉ Gᵉ)

  is-closed-under-multiplication-subset-congruence-Groupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-congruence-Groupᵉ
  is-closed-under-multiplication-subset-congruence-Groupᵉ Hᵉ Kᵉ =
    concatenate-eq-sim-congruence-Groupᵉ Gᵉ Rᵉ
      ( invᵉ (left-unit-law-mul-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ)))
      ( mul-congruence-Groupᵉ Gᵉ Rᵉ Hᵉ Kᵉ)

  is-closed-under-inverses-subset-congruence-Groupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-congruence-Groupᵉ
  is-closed-under-inverses-subset-congruence-Groupᵉ Hᵉ =
    concatenate-eq-sim-congruence-Groupᵉ Gᵉ Rᵉ
      ( invᵉ (inv-unit-Groupᵉ Gᵉ))
      ( inv-congruence-Groupᵉ Gᵉ Rᵉ Hᵉ)

  subgroup-congruence-Groupᵉ : Subgroupᵉ l2ᵉ Gᵉ
  pr1ᵉ subgroup-congruence-Groupᵉ = subset-congruence-Groupᵉ
  pr1ᵉ (pr2ᵉ subgroup-congruence-Groupᵉ) =
    contains-unit-subset-congruence-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ subgroup-congruence-Groupᵉ)) =
    is-closed-under-multiplication-subset-congruence-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ subgroup-congruence-Groupᵉ)) =
    is-closed-under-inverses-subset-congruence-Groupᵉ

  is-normal-subgroup-congruence-Groupᵉ :
    is-normal-Subgroupᵉ Gᵉ subgroup-congruence-Groupᵉ
  is-normal-subgroup-congruence-Groupᵉ xᵉ (pairᵉ yᵉ Hᵉ) =
    concatenate-eq-sim-congruence-Groupᵉ Gᵉ Rᵉ
      ( invᵉ (conjugation-unit-Groupᵉ Gᵉ xᵉ))
      ( conjugation-congruence-Groupᵉ Gᵉ Rᵉ xᵉ Hᵉ)

  normal-subgroup-congruence-Groupᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ
  pr1ᵉ normal-subgroup-congruence-Groupᵉ = subgroup-congruence-Groupᵉ
  pr2ᵉ normal-subgroup-congruence-Groupᵉ =
    is-normal-subgroup-congruence-Groupᵉ
```

#### The normal subgroup obtained from the congruence relation of a normal subgroup `N` is `N` itself

```agda
has-same-elements-normal-subgroup-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ) →
  has-same-elements-Normal-Subgroupᵉ Gᵉ
    ( normal-subgroup-congruence-Groupᵉ Gᵉ (congruence-Normal-Subgroupᵉ Gᵉ Nᵉ))
    ( Nᵉ)
pr1ᵉ (has-same-elements-normal-subgroup-congruence-Groupᵉ Gᵉ Nᵉ xᵉ) Hᵉ =
  is-closed-under-eq-Normal-Subgroupᵉ Gᵉ Nᵉ Hᵉ
    ( apᵉ (mul-Group'ᵉ Gᵉ xᵉ) (inv-unit-Groupᵉ Gᵉ) ∙ᵉ left-unit-law-mul-Groupᵉ Gᵉ xᵉ)
pr2ᵉ (has-same-elements-normal-subgroup-congruence-Groupᵉ Gᵉ Nᵉ xᵉ) Hᵉ =
  is-closed-under-eq-Normal-Subgroup'ᵉ Gᵉ Nᵉ Hᵉ
    ( apᵉ (mul-Group'ᵉ Gᵉ xᵉ) (inv-unit-Groupᵉ Gᵉ) ∙ᵉ left-unit-law-mul-Groupᵉ Gᵉ xᵉ)

is-retraction-normal-subgroup-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ) →
  ( normal-subgroup-congruence-Groupᵉ Gᵉ
    ( congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)) ＝ᵉ
  ( Nᵉ)
is-retraction-normal-subgroup-congruence-Groupᵉ Gᵉ Nᵉ =
  eq-has-same-elements-Normal-Subgroupᵉ Gᵉ
    ( normal-subgroup-congruence-Groupᵉ Gᵉ (congruence-Normal-Subgroupᵉ Gᵉ Nᵉ))
    ( Nᵉ)
    ( has-same-elements-normal-subgroup-congruence-Groupᵉ Gᵉ Nᵉ)
```

#### The congruence relation of the normal subgroup obtained from a congruence relation `R` is `R` itself

```agda
relate-same-elements-congruence-normal-subgroup-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ : congruence-Groupᵉ l2ᵉ Gᵉ) →
  relate-same-elements-congruence-Groupᵉ Gᵉ
    ( congruence-Normal-Subgroupᵉ Gᵉ
      ( normal-subgroup-congruence-Groupᵉ Gᵉ Rᵉ))
    ( Rᵉ)
pr1ᵉ
  ( relate-same-elements-congruence-normal-subgroup-congruence-Groupᵉ
    Gᵉ Rᵉ xᵉ yᵉ) Hᵉ =
  binary-trᵉ
    ( sim-congruence-Groupᵉ Gᵉ Rᵉ)
    ( right-unit-law-mul-Groupᵉ Gᵉ xᵉ)
    ( is-section-left-div-Groupᵉ Gᵉ xᵉ yᵉ)
    ( left-mul-congruence-Groupᵉ Gᵉ Rᵉ xᵉ Hᵉ)
pr2ᵉ
  ( relate-same-elements-congruence-normal-subgroup-congruence-Groupᵉ
    Gᵉ Rᵉ xᵉ yᵉ) Hᵉ =
  symmetric-congruence-Groupᵉ Gᵉ Rᵉ
    ( left-div-Groupᵉ Gᵉ xᵉ yᵉ)
    ( unit-Groupᵉ Gᵉ)
    ( map-sim-left-div-unit-congruence-Groupᵉ Gᵉ Rᵉ Hᵉ)

is-section-normal-subgroup-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ : congruence-Groupᵉ l2ᵉ Gᵉ) →
  ( congruence-Normal-Subgroupᵉ Gᵉ
    ( normal-subgroup-congruence-Groupᵉ Gᵉ Rᵉ)) ＝ᵉ
  ( Rᵉ)
is-section-normal-subgroup-congruence-Groupᵉ Gᵉ Rᵉ =
  eq-relate-same-elements-congruence-Groupᵉ Gᵉ
    ( congruence-Normal-Subgroupᵉ Gᵉ
      ( normal-subgroup-congruence-Groupᵉ Gᵉ Rᵉ))
    ( Rᵉ)
    ( relate-same-elements-congruence-normal-subgroup-congruence-Groupᵉ Gᵉ Rᵉ)
```

#### The equivalence of normal subgroups and congruence relations

```agda
is-equiv-congruence-Normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-equivᵉ (congruence-Normal-Subgroupᵉ {l1ᵉ} {l2ᵉ} Gᵉ)
is-equiv-congruence-Normal-Subgroupᵉ Gᵉ =
  is-equiv-is-invertibleᵉ
    ( normal-subgroup-congruence-Groupᵉ Gᵉ)
    ( is-section-normal-subgroup-congruence-Groupᵉ Gᵉ)
    ( is-retraction-normal-subgroup-congruence-Groupᵉ Gᵉ)

equiv-congruence-Normal-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Normal-Subgroupᵉ l2ᵉ Gᵉ ≃ᵉ congruence-Groupᵉ l2ᵉ Gᵉ
pr1ᵉ (equiv-congruence-Normal-Subgroupᵉ Gᵉ) =
  congruence-Normal-Subgroupᵉ Gᵉ
pr2ᵉ (equiv-congruence-Normal-Subgroupᵉ Gᵉ) =
  is-equiv-congruence-Normal-Subgroupᵉ Gᵉ

is-equiv-normal-subgroup-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-equivᵉ (normal-subgroup-congruence-Groupᵉ {l1ᵉ} {l2ᵉ} Gᵉ)
is-equiv-normal-subgroup-congruence-Groupᵉ Gᵉ =
  is-equiv-is-invertibleᵉ
    ( congruence-Normal-Subgroupᵉ Gᵉ)
    ( is-retraction-normal-subgroup-congruence-Groupᵉ Gᵉ)
    ( is-section-normal-subgroup-congruence-Groupᵉ Gᵉ)

equiv-normal-subgroup-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  congruence-Groupᵉ l2ᵉ Gᵉ ≃ᵉ Normal-Subgroupᵉ l2ᵉ Gᵉ
pr1ᵉ (equiv-normal-subgroup-congruence-Groupᵉ Gᵉ) =
  normal-subgroup-congruence-Groupᵉ Gᵉ
pr2ᵉ (equiv-normal-subgroup-congruence-Groupᵉ Gᵉ) =
  is-equiv-normal-subgroup-congruence-Groupᵉ Gᵉ
```
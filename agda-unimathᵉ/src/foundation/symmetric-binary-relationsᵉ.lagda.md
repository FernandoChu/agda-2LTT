# Symmetric binary relations

```agda
module foundation.symmetric-binary-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.function-extensionalityᵉ
open import foundation.morphisms-binary-relationsᵉ
open import foundation.symmetric-operationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ **symmetricᵉ binaryᵉ relation**ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ typeᵉ familyᵉ `R`ᵉ overᵉ theᵉ typeᵉ
ofᵉ [unorderedᵉ pairs](foundation.unordered-pairs.mdᵉ) ofᵉ elementsᵉ ofᵉ `A`.ᵉ Givenᵉ aᵉ
symmetricᵉ binaryᵉ relationᵉ `R`ᵉ onᵉ `A`ᵉ andᵉ anᵉ equivalenceᵉ ofᵉ unorderedᵉ pairsᵉ
`pᵉ ＝ᵉ q`,ᵉ weᵉ haveᵉ `Rᵉ pᵉ ≃ᵉ Rᵉ q`.ᵉ Inᵉ particular,ᵉ weᵉ haveᵉ

```text
  Rᵉ ({x,yᵉ}) ≃ᵉ Rᵉ ({y,xᵉ})
```

forᵉ anyᵉ twoᵉ elementsᵉ `xᵉ yᵉ : A`,ᵉ where `{x,y}`ᵉ isᵉ theᵉ _standardᵉ unorderedᵉ pairᵉ_
consistingᵉ ofᵉ `x`ᵉ andᵉ `y`.ᵉ

Noteᵉ thatᵉ aᵉ symmetricᵉ binaryᵉ relationᵉ Rᵉ onᵉ aᵉ typeᵉ isᵉ justᵉ aᵉ
[symmetricᵉ operation](foundation.symmetric-operations.mdᵉ) fromᵉ `A`ᵉ intoᵉ aᵉ
universeᵉ `𝒰`.ᵉ

## Definitions

### Symmetric binary relations

```agda
Symmetric-Relationᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Symmetric-Relationᵉ l2ᵉ Aᵉ = symmetric-operationᵉ Aᵉ (UUᵉ l2ᵉ)
```

### Action on symmetries of symmetric binary relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Symmetric-Relationᵉ l2ᵉ Aᵉ)
  where

  abstract
    equiv-tr-Symmetric-Relationᵉ :
      (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → Eq-unordered-pairᵉ pᵉ qᵉ → Rᵉ pᵉ ≃ᵉ Rᵉ qᵉ
    equiv-tr-Symmetric-Relationᵉ pᵉ =
      ind-Eq-unordered-pairᵉ pᵉ (λ qᵉ eᵉ → Rᵉ pᵉ ≃ᵉ Rᵉ qᵉ) id-equivᵉ

    compute-refl-equiv-tr-Symmetric-Relationᵉ :
      (pᵉ : unordered-pairᵉ Aᵉ) →
      equiv-tr-Symmetric-Relationᵉ pᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ) ＝ᵉ
      id-equivᵉ
    compute-refl-equiv-tr-Symmetric-Relationᵉ pᵉ =
      compute-refl-ind-Eq-unordered-pairᵉ pᵉ (λ qᵉ eᵉ → Rᵉ pᵉ ≃ᵉ Rᵉ qᵉ) id-equivᵉ

    htpy-compute-refl-equiv-tr-Symmetric-Relationᵉ :
      (pᵉ : unordered-pairᵉ Aᵉ) →
      htpy-equivᵉ
        ( equiv-tr-Symmetric-Relationᵉ pᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ))
        ( id-equivᵉ)
    htpy-compute-refl-equiv-tr-Symmetric-Relationᵉ pᵉ =
      htpy-eq-equivᵉ (compute-refl-equiv-tr-Symmetric-Relationᵉ pᵉ)

  abstract
    tr-Symmetric-Relationᵉ :
      (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → Eq-unordered-pairᵉ pᵉ qᵉ → Rᵉ pᵉ → Rᵉ qᵉ
    tr-Symmetric-Relationᵉ pᵉ qᵉ eᵉ =
      map-equivᵉ (equiv-tr-Symmetric-Relationᵉ pᵉ qᵉ eᵉ)

    tr-inv-Symmetric-Relationᵉ :
      (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → Eq-unordered-pairᵉ pᵉ qᵉ → Rᵉ qᵉ → Rᵉ pᵉ
    tr-inv-Symmetric-Relationᵉ pᵉ qᵉ eᵉ =
      map-inv-equivᵉ (equiv-tr-Symmetric-Relationᵉ pᵉ qᵉ eᵉ)

    is-section-tr-inv-Symmetric-Relationᵉ :
      (pᵉ qᵉ : unordered-pairᵉ Aᵉ) (eᵉ : Eq-unordered-pairᵉ pᵉ qᵉ) →
      tr-Symmetric-Relationᵉ pᵉ qᵉ eᵉ ∘ᵉ
      tr-inv-Symmetric-Relationᵉ pᵉ qᵉ eᵉ ~ᵉ
      idᵉ
    is-section-tr-inv-Symmetric-Relationᵉ pᵉ qᵉ eᵉ =
      is-section-map-inv-equivᵉ (equiv-tr-Symmetric-Relationᵉ pᵉ qᵉ eᵉ)

    is-retraction-tr-inv-Symmetric-Relationᵉ :
      (pᵉ qᵉ : unordered-pairᵉ Aᵉ) (eᵉ : Eq-unordered-pairᵉ pᵉ qᵉ) →
      tr-inv-Symmetric-Relationᵉ pᵉ qᵉ eᵉ ∘ᵉ
      tr-Symmetric-Relationᵉ pᵉ qᵉ eᵉ ~ᵉ
      idᵉ
    is-retraction-tr-inv-Symmetric-Relationᵉ pᵉ qᵉ eᵉ =
      is-retraction-map-inv-equivᵉ (equiv-tr-Symmetric-Relationᵉ pᵉ qᵉ eᵉ)

    compute-refl-tr-Symmetric-Relationᵉ :
      (pᵉ : unordered-pairᵉ Aᵉ) →
      tr-Symmetric-Relationᵉ pᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ) ＝ᵉ idᵉ
    compute-refl-tr-Symmetric-Relationᵉ pᵉ =
      apᵉ map-equivᵉ (compute-refl-equiv-tr-Symmetric-Relationᵉ pᵉ)

    htpy-compute-refl-tr-Symmetric-Relationᵉ :
      (pᵉ : unordered-pairᵉ Aᵉ) →
      tr-Symmetric-Relationᵉ pᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ) ~ᵉ idᵉ
    htpy-compute-refl-tr-Symmetric-Relationᵉ pᵉ =
      htpy-eqᵉ (compute-refl-tr-Symmetric-Relationᵉ pᵉ)
```

### The underlying binary relation of a symmetric binary relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Symmetric-Relationᵉ l2ᵉ Aᵉ)
  where

  relation-Symmetric-Relationᵉ : Relationᵉ l2ᵉ Aᵉ
  relation-Symmetric-Relationᵉ xᵉ yᵉ = Rᵉ (standard-unordered-pairᵉ xᵉ yᵉ)

  equiv-symmetric-relation-Symmetric-Relationᵉ :
    {xᵉ yᵉ : Aᵉ} →
    relation-Symmetric-Relationᵉ xᵉ yᵉ ≃ᵉ
    relation-Symmetric-Relationᵉ yᵉ xᵉ
  equiv-symmetric-relation-Symmetric-Relationᵉ {xᵉ} {yᵉ} =
    equiv-tr-Symmetric-Relationᵉ Rᵉ
      ( standard-unordered-pairᵉ xᵉ yᵉ)
      ( standard-unordered-pairᵉ yᵉ xᵉ)
      ( swap-standard-unordered-pairᵉ xᵉ yᵉ)

  symmetric-relation-Symmetric-Relationᵉ :
    {xᵉ yᵉ : Aᵉ} →
    relation-Symmetric-Relationᵉ xᵉ yᵉ →
    relation-Symmetric-Relationᵉ yᵉ xᵉ
  symmetric-relation-Symmetric-Relationᵉ =
    map-equivᵉ equiv-symmetric-relation-Symmetric-Relationᵉ
```

### The forgetful functor from binary relations to symmetric binary relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  symmetric-relation-Relationᵉ : Symmetric-Relationᵉ l2ᵉ Aᵉ
  symmetric-relation-Relationᵉ pᵉ =
    Σᵉ ( type-unordered-pairᵉ pᵉ)
      ( λ iᵉ →
        Rᵉ (element-unordered-pairᵉ pᵉ iᵉ) (other-element-unordered-pairᵉ pᵉ iᵉ))

  unit-symmetric-relation-Relationᵉ :
    (xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ →
    relation-Symmetric-Relationᵉ symmetric-relation-Relationᵉ xᵉ yᵉ
  pr1ᵉ (unit-symmetric-relation-Relationᵉ xᵉ yᵉ rᵉ) = zero-Finᵉ 1
  pr2ᵉ (unit-symmetric-relation-Relationᵉ xᵉ yᵉ rᵉ) =
    trᵉ
      ( Rᵉ xᵉ)
      ( invᵉ (compute-other-element-standard-unordered-pairᵉ xᵉ yᵉ (zero-Finᵉ 1ᵉ)))
      ( rᵉ)
```

### Morphisms of symmetric binary relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  hom-Symmetric-Relationᵉ :
    Symmetric-Relationᵉ l2ᵉ Aᵉ → Symmetric-Relationᵉ l3ᵉ Aᵉ →
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-Symmetric-Relationᵉ Rᵉ Sᵉ =
    (pᵉ : unordered-pairᵉ Aᵉ) → Rᵉ pᵉ → Sᵉ pᵉ

  hom-relation-hom-Symmetric-Relationᵉ :
    (Rᵉ : Symmetric-Relationᵉ l2ᵉ Aᵉ) (Sᵉ : Symmetric-Relationᵉ l3ᵉ Aᵉ) →
    hom-Symmetric-Relationᵉ Rᵉ Sᵉ →
    hom-Relationᵉ
      ( relation-Symmetric-Relationᵉ Rᵉ)
      ( relation-Symmetric-Relationᵉ Sᵉ)
  hom-relation-hom-Symmetric-Relationᵉ Rᵉ Sᵉ fᵉ xᵉ yᵉ =
    fᵉ (standard-unordered-pairᵉ xᵉ yᵉ)
```
# Reflecting maps for equivalence relations

```agda
module foundation.reflecting-maps-equivalence-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ outᵉ ofᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with anᵉ equivalenceᵉ relationᵉ `R`ᵉ isᵉ
saidᵉ to **reflect**ᵉ `R`ᵉ ifᵉ weᵉ haveᵉ `Rᵉ xᵉ yᵉ → fᵉ xᵉ ＝ᵉ fᵉ y`ᵉ forᵉ everyᵉ `xᵉ yᵉ : A`.ᵉ

## Definitions

### Maps reflecting equivalence relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  reflects-equivalence-relationᵉ :
    {l3ᵉ : Level} {Bᵉ : UUᵉ l3ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  reflects-equivalence-relationᵉ fᵉ =
    {xᵉ yᵉ : Aᵉ} → sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ → (fᵉ xᵉ ＝ᵉ fᵉ yᵉ)

  reflecting-map-equivalence-relationᵉ : {l3ᵉ : Level} → UUᵉ l3ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  reflecting-map-equivalence-relationᵉ Bᵉ =
    Σᵉ (Aᵉ → Bᵉ) reflects-equivalence-relationᵉ

  map-reflecting-map-equivalence-relationᵉ :
    {l3ᵉ : Level} {Bᵉ : UUᵉ l3ᵉ} → reflecting-map-equivalence-relationᵉ Bᵉ → Aᵉ → Bᵉ
  map-reflecting-map-equivalence-relationᵉ = pr1ᵉ

  reflects-map-reflecting-map-equivalence-relationᵉ :
    {l3ᵉ : Level} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : reflecting-map-equivalence-relationᵉ Bᵉ) →
    reflects-equivalence-relationᵉ (map-reflecting-map-equivalence-relationᵉ fᵉ)
  reflects-map-reflecting-map-equivalence-relationᵉ = pr2ᵉ

  is-prop-reflects-equivalence-relationᵉ :
    {l3ᵉ : Level} (Bᵉ : Setᵉ l3ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    is-propᵉ (reflects-equivalence-relationᵉ fᵉ)
  is-prop-reflects-equivalence-relationᵉ Bᵉ fᵉ =
    is-prop-implicit-Πᵉ
      ( λ xᵉ →
        is-prop-implicit-Πᵉ
          ( λ yᵉ →
            is-prop-function-typeᵉ (is-set-type-Setᵉ Bᵉ (fᵉ xᵉ) (fᵉ yᵉ))))

  reflects-prop-equivalence-relationᵉ :
    {l3ᵉ : Level} (Bᵉ : Setᵉ l3ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ (reflects-prop-equivalence-relationᵉ Bᵉ fᵉ) = reflects-equivalence-relationᵉ fᵉ
  pr2ᵉ (reflects-prop-equivalence-relationᵉ Bᵉ fᵉ) =
    is-prop-reflects-equivalence-relationᵉ Bᵉ fᵉ
```

## Properties

### Any surjective and effective map reflects the equivalence relation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (qᵉ : Aᵉ → type-Setᵉ Bᵉ)
  where

  reflects-equivalence-relation-is-surjective-and-effectiveᵉ :
    is-surjective-and-effectiveᵉ Rᵉ qᵉ → reflects-equivalence-relationᵉ Rᵉ qᵉ
  reflects-equivalence-relation-is-surjective-and-effectiveᵉ Eᵉ {xᵉ} {yᵉ} =
    map-inv-equivᵉ (pr2ᵉ Eᵉ xᵉ yᵉ)

  reflecting-map-equivalence-relation-is-surjective-and-effectiveᵉ :
    is-surjective-and-effectiveᵉ Rᵉ qᵉ →
    reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)
  pr1ᵉ (reflecting-map-equivalence-relation-is-surjective-and-effectiveᵉ Eᵉ) = qᵉ
  pr2ᵉ (reflecting-map-equivalence-relation-is-surjective-and-effectiveᵉ Eᵉ) =
    reflects-equivalence-relation-is-surjective-and-effectiveᵉ Eᵉ
```

### Characterizing the identity type of reflecting maps into sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  where

  htpy-reflecting-map-equivalence-relationᵉ :
    (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-reflecting-map-equivalence-relationᵉ gᵉ =
    pr1ᵉ fᵉ ~ᵉ pr1ᵉ gᵉ

  refl-htpy-reflecting-map-equivalence-relationᵉ :
    htpy-reflecting-map-equivalence-relationᵉ fᵉ
  refl-htpy-reflecting-map-equivalence-relationᵉ = refl-htpyᵉ

  htpy-eq-reflecting-map-equivalence-relationᵉ :
    (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    fᵉ ＝ᵉ gᵉ → htpy-reflecting-map-equivalence-relationᵉ gᵉ
  htpy-eq-reflecting-map-equivalence-relationᵉ .fᵉ reflᵉ =
    refl-htpy-reflecting-map-equivalence-relationᵉ

  is-torsorial-htpy-reflecting-map-equivalence-relationᵉ :
    is-torsorialᵉ (htpy-reflecting-map-equivalence-relationᵉ)
  is-torsorial-htpy-reflecting-map-equivalence-relationᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpyᵉ (pr1ᵉ fᵉ))
      ( is-prop-reflects-equivalence-relationᵉ Rᵉ Bᵉ)
      ( pr1ᵉ fᵉ)
      ( refl-htpyᵉ)
      ( pr2ᵉ fᵉ)

  is-equiv-htpy-eq-reflecting-map-equivalence-relationᵉ :
    (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    is-equivᵉ (htpy-eq-reflecting-map-equivalence-relationᵉ gᵉ)
  is-equiv-htpy-eq-reflecting-map-equivalence-relationᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-reflecting-map-equivalence-relationᵉ
      htpy-eq-reflecting-map-equivalence-relationᵉ

  extensionality-reflecting-map-equivalence-relationᵉ :
    (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-reflecting-map-equivalence-relationᵉ gᵉ
  pr1ᵉ (extensionality-reflecting-map-equivalence-relationᵉ gᵉ) =
    htpy-eq-reflecting-map-equivalence-relationᵉ gᵉ
  pr2ᵉ (extensionality-reflecting-map-equivalence-relationᵉ gᵉ) =
    is-equiv-htpy-eq-reflecting-map-equivalence-relationᵉ gᵉ

  eq-htpy-reflecting-map-equivalence-relationᵉ :
    (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    htpy-reflecting-map-equivalence-relationᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-reflecting-map-equivalence-relationᵉ gᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-reflecting-map-equivalence-relationᵉ gᵉ)
```
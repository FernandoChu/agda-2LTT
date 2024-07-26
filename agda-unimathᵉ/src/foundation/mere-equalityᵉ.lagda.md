# Mere equality

```agda
module foundation.mere-equalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalence-relationsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ in aᵉ typeᵉ areᵉ saidᵉ to beᵉ merelyᵉ equalᵉ ifᵉ thereᵉ isᵉ anᵉ elementᵉ ofᵉ theᵉ
propositionallyᵉ truncatedᵉ identityᵉ typeᵉ betweenᵉ them.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  mere-eq-Propᵉ : Aᵉ → Aᵉ → Propᵉ lᵉ
  mere-eq-Propᵉ xᵉ yᵉ = trunc-Propᵉ (xᵉ ＝ᵉ yᵉ)

  mere-eqᵉ : Aᵉ → Aᵉ → UUᵉ lᵉ
  mere-eqᵉ xᵉ yᵉ = type-Propᵉ (mere-eq-Propᵉ xᵉ yᵉ)

  is-prop-mere-eqᵉ : (xᵉ yᵉ : Aᵉ) → is-propᵉ (mere-eqᵉ xᵉ yᵉ)
  is-prop-mere-eqᵉ xᵉ yᵉ = is-prop-type-trunc-Propᵉ
```

## Properties

### Reflexivity

```agda
abstract
  refl-mere-eqᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-reflexiveᵉ (mere-eqᵉ {lᵉ} {Aᵉ})
  refl-mere-eqᵉ _ = unit-trunc-Propᵉ reflᵉ
```

### Symmetry

```agda
abstract
  symmetric-mere-eqᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-symmetricᵉ (mere-eqᵉ {lᵉ} {Aᵉ})
  symmetric-mere-eqᵉ _ _ = map-trunc-Propᵉ invᵉ
```

### Transitivity

```agda
abstract
  transitive-mere-eqᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-transitiveᵉ (mere-eqᵉ {lᵉ} {Aᵉ})
  transitive-mere-eqᵉ xᵉ yᵉ zᵉ pᵉ qᵉ =
    apply-universal-property-trunc-Propᵉ qᵉ
      ( mere-eq-Propᵉ xᵉ zᵉ)
      ( λ p'ᵉ → map-trunc-Propᵉ (p'ᵉ ∙ᵉ_) pᵉ)
```

### Mere equality is an equivalence relation

```agda
mere-eq-equivalence-relationᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → equivalence-relationᵉ l1ᵉ Aᵉ
pr1ᵉ (mere-eq-equivalence-relationᵉ Aᵉ) = mere-eq-Propᵉ
pr1ᵉ (pr2ᵉ (mere-eq-equivalence-relationᵉ Aᵉ)) = refl-mere-eqᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (mere-eq-equivalence-relationᵉ Aᵉ))) = symmetric-mere-eqᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (mere-eq-equivalence-relationᵉ Aᵉ))) = transitive-mere-eqᵉ
```

### Any map into a set reflects mere equality

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Xᵉ)
  where

  reflects-mere-eqᵉ :
    reflects-equivalence-relationᵉ (mere-eq-equivalence-relationᵉ Aᵉ) fᵉ
  reflects-mere-eqᵉ {xᵉ} {yᵉ} rᵉ =
    apply-universal-property-trunc-Propᵉ rᵉ
      ( Id-Propᵉ Xᵉ (fᵉ xᵉ) (fᵉ yᵉ))
      ( apᵉ fᵉ)

  reflecting-map-mere-eqᵉ :
    reflecting-map-equivalence-relationᵉ
      ( mere-eq-equivalence-relationᵉ Aᵉ)
      ( type-Setᵉ Xᵉ)
  pr1ᵉ reflecting-map-mere-eqᵉ = fᵉ
  pr2ᵉ reflecting-map-mere-eqᵉ = reflects-mere-eqᵉ
```

### If mere equality maps into the identity type of `A`, then `A` is a set

```agda
is-set-mere-eq-in-idᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → ((xᵉ yᵉ : Aᵉ) → mere-eqᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ) → is-setᵉ Aᵉ
is-set-mere-eq-in-idᵉ =
  is-set-prop-in-idᵉ
    ( mere-eqᵉ)
    ( is-prop-mere-eqᵉ)
    ( refl-mere-eqᵉ)
```
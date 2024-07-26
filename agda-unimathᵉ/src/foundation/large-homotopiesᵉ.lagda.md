# Large homotopies

```agda
module foundation.large-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ largeᵉ homotopyᵉ ofᵉ identificationsᵉ isᵉ aᵉ pointwiseᵉ equalityᵉ betweenᵉ largeᵉ
dependentᵉ functions.ᵉ

## Definitions

```agda
module _
  {Xᵉ : UUωᵉ} {Pᵉ : Xᵉ → UUωᵉ} (fᵉ gᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ)
  where

  eq-large-valueᵉ : Xᵉ → UUωᵉ
  eq-large-valueᵉ xᵉ = (fᵉ xᵉ ＝ωᵉ gᵉ xᵉ)
```

```agda
module _
  {Aᵉ : UUωᵉ} {Bᵉ : Aᵉ → UUωᵉ}
  where

  _~ωᵉ_ : (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → UUωᵉ
  fᵉ ~ωᵉ gᵉ = (xᵉ : Aᵉ) → eq-large-valueᵉ fᵉ gᵉ xᵉ
```

## Properties

### Reflexivity

```agda
module _
  {Aᵉ : UUωᵉ} {Bᵉ : Aᵉ → UUωᵉ}
  where

  refl-large-htpyᵉ : {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → fᵉ ~ωᵉ fᵉ
  refl-large-htpyᵉ xᵉ = reflωᵉ

  refl-large-htpy'ᵉ : (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ωᵉ fᵉ
  refl-large-htpy'ᵉ fᵉ = refl-large-htpyᵉ
```
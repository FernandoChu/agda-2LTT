# Equivalences of concrete groups

```agda
module group-theory.equivalences-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ

open import higher-group-theory.equivalences-higher-groupsᵉ
open import higher-group-theory.higher-groupsᵉ
```

</details>

## Idea

Anᵉ equivalenceᵉ ofᵉ concreteᵉ groupsᵉ consistsᵉ ofᵉ aᵉ pointedᵉ equivalenceᵉ betweenᵉ
theirᵉ classifyingᵉ typesᵉ

## Definition

### Equivalences of concrete groups

```agda
equiv-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-Concrete-Groupᵉ Gᵉ Hᵉ =
  equiv-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ) (∞-group-Concrete-Groupᵉ Hᵉ)
```

### The identity equivalence of a concrete group

```agda
id-equiv-Concrete-Groupᵉ :
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ) → equiv-Concrete-Groupᵉ Gᵉ Gᵉ
id-equiv-Concrete-Groupᵉ Gᵉ = id-equiv-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)
```

## Properties

### Characterization of equality in the type of concrete groups

```agda
module _
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ)
  where

  is-torsorial-equiv-Concrete-Groupᵉ :
    is-torsorialᵉ (equiv-Concrete-Groupᵉ Gᵉ)
  is-torsorial-equiv-Concrete-Groupᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-equiv-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ))
      ( λ Hᵉ → is-prop-is-setᵉ (type-∞-Groupᵉ Hᵉ))
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( id-equiv-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ))
      ( is-set-type-Concrete-Groupᵉ Gᵉ)

  equiv-eq-Concrete-Groupᵉ :
    (Hᵉ : Concrete-Groupᵉ lᵉ) → (Gᵉ ＝ᵉ Hᵉ) → equiv-Concrete-Groupᵉ Gᵉ Hᵉ
  equiv-eq-Concrete-Groupᵉ .Gᵉ reflᵉ = id-equiv-Concrete-Groupᵉ Gᵉ

  is-equiv-equiv-eq-Concrete-Groupᵉ :
    (Hᵉ : Concrete-Groupᵉ lᵉ) → is-equivᵉ (equiv-eq-Concrete-Groupᵉ Hᵉ)
  is-equiv-equiv-eq-Concrete-Groupᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Concrete-Groupᵉ
      equiv-eq-Concrete-Groupᵉ

  extensionality-Concrete-Groupᵉ :
    (Hᵉ : Concrete-Groupᵉ lᵉ) → (Gᵉ ＝ᵉ Hᵉ) ≃ᵉ equiv-Concrete-Groupᵉ Gᵉ Hᵉ
  pr1ᵉ (extensionality-Concrete-Groupᵉ Hᵉ) = equiv-eq-Concrete-Groupᵉ Hᵉ
  pr2ᵉ (extensionality-Concrete-Groupᵉ Hᵉ) = is-equiv-equiv-eq-Concrete-Groupᵉ Hᵉ

  eq-equiv-Concrete-Groupᵉ :
    (Hᵉ : Concrete-Groupᵉ lᵉ) → equiv-Concrete-Groupᵉ Gᵉ Hᵉ → Gᵉ ＝ᵉ Hᵉ
  eq-equiv-Concrete-Groupᵉ Hᵉ = map-inv-equivᵉ (extensionality-Concrete-Groupᵉ Hᵉ)
```
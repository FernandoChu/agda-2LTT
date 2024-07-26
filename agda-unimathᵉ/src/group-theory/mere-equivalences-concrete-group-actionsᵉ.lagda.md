# Mere equivalences of concrete group actions

```agda
module group-theory.mere-equivalences-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.equivalences-concrete-group-actionsᵉ
```

</details>

## Definition

```agda
mere-equiv-prop-action-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) →
  action-Concrete-Groupᵉ l2ᵉ Gᵉ → action-Concrete-Groupᵉ l3ᵉ Gᵉ →
  Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
mere-equiv-prop-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ =
  trunc-Propᵉ (equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)

mere-equiv-action-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) →
  action-Concrete-Groupᵉ l2ᵉ Gᵉ → action-Concrete-Groupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
mere-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ =
  type-Propᵉ (mere-equiv-prop-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)

is-prop-mere-equiv-action-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ) (Yᵉ : action-Concrete-Groupᵉ l3ᵉ Gᵉ) →
  is-propᵉ (mere-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
is-prop-mere-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ =
  is-prop-type-Propᵉ (mere-equiv-prop-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)

refl-mere-equiv-action-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ) →
  mere-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Xᵉ
refl-mere-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ =
  unit-trunc-Propᵉ (id-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ)
```

## Properties

### Mere equivalences of concrete group actions give mere equalities

```agda
mere-eq-mere-equiv-action-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ) (Yᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ) →
  mere-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ →
  mere-eqᵉ Xᵉ Yᵉ
mere-eq-mere-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ =
  map-trunc-Propᵉ (eq-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
```
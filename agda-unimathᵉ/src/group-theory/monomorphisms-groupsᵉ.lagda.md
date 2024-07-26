# Monomorphisms in the category of groups

```agda
module group-theory.monomorphisms-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.monomorphisms-in-large-precategoriesᵉ

open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.precategory-of-groupsᵉ
```

</details>

## Idea

Aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `fᵉ : xᵉ → y`ᵉ isᵉ aᵉ
**monomorphism**ᵉ ifᵉ wheneverᵉ weᵉ haveᵉ twoᵉ groupᵉ homomorphismsᵉ `gᵉ hᵉ : wᵉ → x`ᵉ suchᵉ
thatᵉ `fᵉ ∘ᵉ gᵉ = fᵉ ∘ᵉ h`,ᵉ thenᵉ in factᵉ `gᵉ = h`.ᵉ Theᵉ wayᵉ to stateᵉ thisᵉ in Homotopyᵉ
Typeᵉ Theoryᵉ isᵉ to sayᵉ thatᵉ postcompositionᵉ byᵉ `f`ᵉ isᵉ anᵉ
[embedding](foundation-core.embeddings.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ)
  (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  is-mono-prop-hom-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-mono-prop-hom-Groupᵉ =
    is-mono-prop-Large-Precategoryᵉ Group-Large-Precategoryᵉ l3ᵉ Gᵉ Hᵉ fᵉ

  is-mono-hom-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-mono-hom-Groupᵉ = type-Propᵉ is-mono-prop-hom-Groupᵉ

  is-prop-is-mono-hom-Groupᵉ : is-propᵉ is-mono-hom-Groupᵉ
  is-prop-is-mono-hom-Groupᵉ = is-prop-type-Propᵉ is-mono-prop-hom-Groupᵉ
```

## Properties

### Isomorphisms are monomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ)
  (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : iso-Groupᵉ Gᵉ Hᵉ)
  where

  is-mono-iso-Groupᵉ : is-mono-hom-Groupᵉ l3ᵉ Gᵉ Hᵉ (hom-iso-Groupᵉ Gᵉ Hᵉ fᵉ)
  is-mono-iso-Groupᵉ =
    is-mono-iso-Large-Precategoryᵉ Group-Large-Precategoryᵉ l3ᵉ Gᵉ Hᵉ fᵉ
```
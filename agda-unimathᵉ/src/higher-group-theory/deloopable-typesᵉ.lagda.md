# Deloopable types

```agda
module higher-group-theory.deloopable-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.small-typesᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.equivalences-higher-groupsᵉ
open import higher-group-theory.higher-groupsᵉ
open import higher-group-theory.small-higher-groupsᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.small-pointed-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `X`ᵉ andᵉ aᵉ pointedᵉ
[connected](foundation.0-connected-types.mdᵉ) typeᵉ `Y`.ᵉ Weᵉ sayᵉ thatᵉ `Y`ᵉ isᵉ aᵉ
{{#conceptᵉ "delooping"ᵉ Disambiguation="pointedᵉ type"ᵉ Agda=is-deloopingᵉ}} ofᵉ `X`ᵉ
ifᵉ weᵉ haveᵉ aᵉ [pointedᵉ equivalence](structured-types.pointed-equivalences.mdᵉ)

```text
  Xᵉ ≃∗ᵉ Ωᵉ Y.ᵉ
```

Recallᵉ thatᵉ aᵉ pointedᵉ connectedᵉ typeᵉ isᵉ anᵉ
[∞-group](higher-group-theory.higher-groups.md).ᵉ Anᵉ ∞-groupᵉ `G`ᵉ isᵉ thereforeᵉ aᵉ
deloopingᵉ ofᵉ `X`ᵉ ifᵉ itsᵉ underlyingᵉ pointedᵉ typeᵉ isᵉ pointedᵉ equivalentᵉ to `X`.ᵉ Aᵉ
{{#conceptᵉ "delooping"ᵉ Disambiguation="pointedᵉ type"ᵉ Agda=deloopingᵉ}} ofᵉ `X`ᵉ
thereforeᵉ consistᵉ ofᵉ anᵉ ∞-groupᵉ `G`ᵉ andᵉ aᵉ pointedᵉ equivalenceᵉ

```text
  Xᵉ ≃∗ᵉ type-∞-Groupᵉ Gᵉ
```

Inᵉ otherᵉ words,ᵉ theᵉ typeᵉ ofᵉ deloopingsᵉ ofᵉ `X`ᵉ isᵉ definedᵉ to beᵉ

```text
  deloopingᵉ Xᵉ :=ᵉ Σᵉ (Yᵉ : ∞-Group),ᵉ Xᵉ ≃∗ᵉ Ωᵉ Y.ᵉ
```

### Relation to higher group structures

Aᵉ deloopingᵉ ofᵉ aᵉ pointedᵉ typeᵉ `X`ᵉ is,ᵉ in quiteᵉ aᵉ literalᵉ way,ᵉ anᵉ
{{#conceptᵉ "∞-groupᵉ structure"ᵉ Agda=deloopingᵉ}} onᵉ `X`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ typeᵉ
`deloopingᵉ X`ᵉ isᵉ theᵉ typeᵉ ofᵉ ∞-groupᵉ structuresᵉ onᵉ `X`.ᵉ Indeed,ᵉ theᵉ typeᵉ ofᵉ allᵉ
pointedᵉ typesᵉ equippedᵉ with deloopingsᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ ofᵉ ∞-groups,ᵉ byᵉ
extensionalityᵉ ofᵉ theᵉ typeᵉ ofᵉ pointedᵉ types.ᵉ

Beingᵉ deloopableᵉ isᵉ thereforeᵉ aᵉ [structure](foundation.structure.md),ᵉ andᵉ
usuallyᵉ notᵉ aᵉ [property](foundation-core.propositions.md).ᵉ Ifᵉ thereᵉ areᵉ multipleᵉ
distinctᵉ waysᵉ to equipᵉ aᵉ pointedᵉ typeᵉ `X`ᵉ with theᵉ structureᵉ ofᵉ anᵉ ∞-group,ᵉ orᵉ
evenᵉ with theᵉ structureᵉ ofᵉ aᵉ [group](group-theory.groups.md),ᵉ thenᵉ theᵉ typeᵉ ofᵉ
deloopingsᵉ ofᵉ `X`ᵉ willᵉ notᵉ beᵉ aᵉ proposition.ᵉ Forᵉ instance,ᵉ theᵉ
[standardᵉ `4`-elementᵉ type](univalent-combinatorics.standard-finite-types.mdᵉ)
`Finᵉ 4`ᵉ isᵉ deloopableᵉ in multipleᵉ distinctᵉ ways,ᵉ byᵉ equippingᵉ itᵉ with theᵉ
[cyclicᵉ groupᵉ structure](group-theory.cyclic-groups.mdᵉ) ofᵉ `ℤ₄`ᵉ orᵉ byᵉ equippingᵉ
itᵉ with theᵉ groupᵉ structureᵉ ofᵉ `ℤ₂ᵉ ×ᵉ ℤ₂`.ᵉ

### Universe levels in the definition of being deloopable

Noteᵉ thatᵉ thereᵉ isᵉ aᵉ smallᵉ questionᵉ aboutᵉ universeᵉ levelsᵉ in theᵉ definitionᵉ ofᵉ
beingᵉ aᵉ deloopableᵉ type.ᵉ Weᵉ sayᵉ thatᵉ aᵉ typeᵉ isᵉ deloopableᵉ in aᵉ universeᵉ `𝒰`ᵉ ifᵉ
thereᵉ isᵉ anᵉ ∞-groupᵉ `Y`ᵉ in theᵉ universeᵉ `𝒰`ᵉ thatᵉ isᵉ aᵉ deloopingᵉ ofᵉ `X`.ᵉ However,ᵉ
byᵉ theᵉ [typeᵉ theoreticᵉ replacementᵉ principle](foundation.replacement.mdᵉ) itᵉ
followsᵉ thatᵉ anyᵉ deloopingᵉ ofᵉ `X`ᵉ isᵉ alwaysᵉ [small](foundation.small-types.mdᵉ)
with respectᵉ to theᵉ universeᵉ ofᵉ `X`ᵉ itself.ᵉ Thereforeᵉ weᵉ simplyᵉ sayᵉ thatᵉ `X`ᵉ isᵉ
deloopable,ᵉ i.e.,ᵉ withoutᵉ referenceᵉ to anyᵉ universes,ᵉ ifᵉ `X`ᵉ isᵉ deloopableᵉ in
itsᵉ ownᵉ universe.ᵉ

## Definitions

### The predicate of being a delooping

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-deloopingᵉ : (Gᵉ : ∞-Groupᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-deloopingᵉ Gᵉ = Xᵉ ≃∗ᵉ pointed-type-∞-Groupᵉ Gᵉ
```

### The type of deloopings of a pointed type, in a given universe

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  delooping-Levelᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
  delooping-Levelᵉ lᵉ = Σᵉ (∞-Groupᵉ lᵉ) (is-deloopingᵉ Xᵉ)

  module _
    {lᵉ : Level} (Yᵉ : delooping-Levelᵉ lᵉ)
    where

    ∞-group-delooping-Levelᵉ : ∞-Groupᵉ lᵉ
    ∞-group-delooping-Levelᵉ = pr1ᵉ Yᵉ

    classifying-pointed-type-∞-group-delooping-Levelᵉ : Pointed-Typeᵉ lᵉ
    classifying-pointed-type-∞-group-delooping-Levelᵉ =
      classifying-pointed-type-∞-Groupᵉ ∞-group-delooping-Levelᵉ

    classifying-type-∞-group-delooping-Levelᵉ : UUᵉ lᵉ
    classifying-type-∞-group-delooping-Levelᵉ =
      classifying-type-∞-Groupᵉ ∞-group-delooping-Levelᵉ

    is-delooping-delooping-Levelᵉ : is-deloopingᵉ Xᵉ ∞-group-delooping-Levelᵉ
    is-delooping-delooping-Levelᵉ = pr2ᵉ Yᵉ

    equiv-is-delooping-delooping-Levelᵉ :
      type-Pointed-Typeᵉ Xᵉ ≃ᵉ type-∞-Groupᵉ ∞-group-delooping-Levelᵉ
    equiv-is-delooping-delooping-Levelᵉ =
      equiv-pointed-equivᵉ is-delooping-delooping-Levelᵉ
```

### The type of deloopings of a pointed type

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  deloopingᵉ : UUᵉ (lsuc l1ᵉ)
  deloopingᵉ = delooping-Levelᵉ Xᵉ l1ᵉ
```

## Properties

### The delooping of a pointed type in a universe `𝒰` is a `𝒰`-small ∞-group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ) (Hᵉ : delooping-Levelᵉ Xᵉ l2ᵉ)
  where

  abstract
    is-small-∞-group-delooping-Levelᵉ :
      is-small-∞-Groupᵉ l1ᵉ (∞-group-delooping-Levelᵉ Xᵉ Hᵉ)
    pr1ᵉ is-small-∞-group-delooping-Levelᵉ = type-Pointed-Typeᵉ Xᵉ
    pr2ᵉ is-small-∞-group-delooping-Levelᵉ =
      inv-equivᵉ (equiv-is-delooping-delooping-Levelᵉ Xᵉ Hᵉ)

  abstract
    is-small-classifying-type-∞-group-delooping-Levelᵉ :
      is-smallᵉ l1ᵉ (classifying-type-∞-group-delooping-Levelᵉ Xᵉ Hᵉ)
    is-small-classifying-type-∞-group-delooping-Levelᵉ =
      is-small-classifying-type-is-small-∞-Groupᵉ
        ( ∞-group-delooping-Levelᵉ Xᵉ Hᵉ)
        ( is-small-∞-group-delooping-Levelᵉ)

  abstract
    is-pointed-small-classifying-pointed-type-∞-group-delooping-Levelᵉ :
      is-pointed-small-Pointed-Typeᵉ l1ᵉ
        ( classifying-pointed-type-∞-group-delooping-Levelᵉ Xᵉ Hᵉ)
    is-pointed-small-classifying-pointed-type-∞-group-delooping-Levelᵉ =
      is-pointed-small-is-small-Pointed-Typeᵉ
        ( classifying-pointed-type-∞-group-delooping-Levelᵉ Xᵉ Hᵉ)
        ( is-small-classifying-type-∞-group-delooping-Levelᵉ)
```

### If a pointed type in universe `𝒰 l1` is deloopable in any universe, then it is deloopable in `𝒰 l1`

Supposeᵉ `X`ᵉ isᵉ aᵉ pointedᵉ typeᵉ ofᵉ universeᵉ levelᵉ `l1`,ᵉ whichᵉ isᵉ deloopableᵉ in
universeᵉ levelᵉ `l2`.ᵉ Thenᵉ thereᵉ isᵉ anᵉ ∞-groupᵉ `H`ᵉ ofᵉ universeᵉ levelᵉ `l2`ᵉ
equippedᵉ with aᵉ pointedᵉ equivalenceᵉ

```text
  Xᵉ ≃∗ᵉ type-∞-Groupᵉ H.ᵉ
```

Thisᵉ impliesᵉ thatᵉ theᵉ ∞-groupᵉ `H`ᵉ isᵉ `l1`-small,ᵉ becauseᵉ itsᵉ underlyingᵉ typeᵉ isᵉ
equivalentᵉ to theᵉ underlyingᵉ typeᵉ ofᵉ `X`.ᵉ Henceᵉ thereᵉ isᵉ anᵉ ∞-groupᵉ `K`ᵉ equippedᵉ
with anᵉ
[equivalenceᵉ ofᵉ ∞-groups](higher-group-theory.equivalences-higher-groups.mdᵉ)

```text
  Hᵉ ≃ᵉ K.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ) (Hᵉ : delooping-Levelᵉ Xᵉ l2ᵉ)
  where

  ∞-group-delooping-delooping-levelᵉ : ∞-Groupᵉ l1ᵉ
  ∞-group-delooping-delooping-levelᵉ =
    ∞-group-is-small-∞-Groupᵉ
      ( ∞-group-delooping-Levelᵉ Xᵉ Hᵉ)
      ( type-Pointed-Typeᵉ Xᵉ ,ᵉ
        equiv-inv-pointed-equivᵉ (is-delooping-delooping-Levelᵉ Xᵉ Hᵉ))

  is-delooping-delooping-delooping-Levelᵉ :
    is-deloopingᵉ Xᵉ ∞-group-delooping-delooping-levelᵉ
  is-delooping-delooping-delooping-Levelᵉ =
    comp-pointed-equivᵉ
      ( pointed-equiv-equiv-∞-Groupᵉ
        ( ∞-group-delooping-Levelᵉ Xᵉ Hᵉ)
        ( ∞-group-delooping-delooping-levelᵉ)
        ( equiv-∞-group-is-small-∞-Groupᵉ
          ( ∞-group-delooping-Levelᵉ Xᵉ Hᵉ)
          ( type-Pointed-Typeᵉ Xᵉ ,ᵉ
            equiv-inv-pointed-equivᵉ (is-delooping-delooping-Levelᵉ Xᵉ Hᵉ))))
      ( is-delooping-delooping-Levelᵉ Xᵉ Hᵉ)

  delooping-delooping-Levelᵉ : deloopingᵉ Xᵉ
  pr1ᵉ delooping-delooping-Levelᵉ = ∞-group-delooping-delooping-levelᵉ
  pr2ᵉ delooping-delooping-Levelᵉ = is-delooping-delooping-delooping-Levelᵉ
```

## See also

-ᵉ [Deloopableᵉ H-spaces](higher-group-theory.deloopable-h-spaces.mdᵉ)
-ᵉ [Deloopableᵉ groups](higher-group-theory.deloopable-groups.mdᵉ)
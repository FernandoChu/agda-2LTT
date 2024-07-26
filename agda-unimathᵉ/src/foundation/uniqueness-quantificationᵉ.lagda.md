# Uniqueness quantification

```agda
module foundation.uniqueness-quantificationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ predicateᵉ `Pᵉ : Aᵉ → Prop`ᵉ weᵉ sayᵉ thereᵉ
{{#conceptᵉ "uniquelyᵉ exists"ᵉ Disambiguation="inᵉ aᵉ subtype"ᵉ WDID=Q2502253ᵉ WD="uniquenessᵉ quantification"ᵉ Agda=∃!ᵉ}}
_anᵉ `xᵉ : A`ᵉ satisfyingᵉ `P`_,ᵉ ifᵉ theᵉ [subtype](foundation-core.subtypes.mdᵉ)
`Σᵉ (xᵉ : A),ᵉ (Pᵉ x)`ᵉ isᵉ [contractible](foundation-core.contractible-types.md).ᵉ

Moreᵉ generally,ᵉ givenᵉ aᵉ [structure](foundation.structure.mdᵉ) `Bᵉ : Aᵉ → 𝒰`ᵉ weᵉ sayᵉ
thereᵉ
{{#conceptᵉ "uniquelyᵉ exists"ᵉ Disambiguation="structure"ᵉ Agda=uniquely-exists-structureᵉ}}
_anᵉ `xᵉ : A`ᵉ andᵉ aᵉ `yᵉ : Bᵉ x`_,ᵉ ifᵉ theᵉ
[totalᵉ type](foundation.dependent-pair-types.mdᵉ) `Σᵉ (xᵉ : A),ᵉ (Bᵉ x)`ᵉ isᵉ
contractible.ᵉ

Noteᵉ thatᵉ theᵉ uniqueᵉ existenceᵉ ofᵉ structureᵉ isᵉ definedᵉ in theᵉ exactᵉ sameᵉ wayᵉ asᵉ
theᵉ conceptᵉ ofᵉ
[torsorialᵉ typeᵉ families](foundation-core.torsorial-type-families.md).ᵉ Whetherᵉ
to useᵉ theᵉ conceptᵉ ofᵉ uniqueᵉ existenceᵉ ofᵉ aᵉ structureᵉ orᵉ theᵉ conceptᵉ ofᵉ
torsorialᵉ typeᵉ familyᵉ isᵉ dependentᵉ onᵉ theᵉ context.ᵉ Torsorialityᵉ isᵉ usedᵉ oftenᵉ to
emphasizeᵉ theᵉ relationᵉ ofᵉ theᵉ typeᵉ familyᵉ to theᵉ identityᵉ type,ᵉ whereasᵉ
uniquenessᵉ ofᵉ structureᵉ isᵉ usedᵉ to emphasizeᵉ theᵉ uniquenessᵉ ofᵉ elementsᵉ equippedᵉ
with furtherᵉ structure.ᵉ Forᵉ example,ᵉ weᵉ tendᵉ to useᵉ uniqueᵉ existenceᵉ in
combinationᵉ with universalᵉ properties,ᵉ in orderᵉ to concludeᵉ thatᵉ aᵉ certainᵉ mapᵉ
equippedᵉ with someᵉ homotopiesᵉ existsᵉ uniquely.ᵉ

Asᵉ aᵉ specialᵉ caseᵉ ofᵉ uniquenessᵉ quantification,ᵉ weᵉ recoverᵉ
[exclusiveᵉ disjunction](foundation.exclusive-disjunction.mdᵉ) whenᵉ theᵉ indexingᵉ
typeᵉ isᵉ aᵉ [2-elementᵉ type](univalent-combinatorics.2-element-types.md).ᵉ
Concretely,ᵉ weᵉ haveᵉ theᵉ equivalenceᵉ

```text
  ∃!ᵉ (tᵉ : bool),ᵉ (Pᵉ tᵉ) ≐ᵉ is-contrᵉ (Σᵉ (tᵉ : bool),ᵉ (Pᵉ tᵉ))
                       ≃ᵉ is-contrᵉ ((Pᵉ falseᵉ) +ᵉ (Pᵉ trueᵉ))
                       ≐ᵉ Pᵉ falseᵉ ⊻ᵉ Pᵉ true.ᵉ
```

## Definitions

### Unique existence of structure

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  uniquely-exists-structure-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  uniquely-exists-structure-Propᵉ = is-torsorial-Propᵉ Bᵉ

  uniquely-exists-structureᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  uniquely-exists-structureᵉ = type-Propᵉ uniquely-exists-structure-Propᵉ

  is-prop-uniquely-exists-structureᵉ : is-propᵉ uniquely-exists-structureᵉ
  is-prop-uniquely-exists-structureᵉ =
    is-prop-type-Propᵉ uniquely-exists-structure-Propᵉ
```

### Unique existence in a subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Pᵉ : Aᵉ → Propᵉ l2ᵉ)
  where

  uniquely-exists-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  uniquely-exists-Propᵉ = uniquely-exists-structure-Propᵉ Aᵉ (type-Propᵉ ∘ᵉ Pᵉ)

  uniquely-existsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  uniquely-existsᵉ = type-Propᵉ uniquely-exists-Propᵉ

  is-prop-uniquely-existsᵉ : is-propᵉ uniquely-existsᵉ
  is-prop-uniquely-existsᵉ = is-prop-type-Propᵉ uniquely-exists-Propᵉ

  ∃!ᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  ∃!ᵉ = uniquely-exists-Propᵉ
```

### Components of unique existence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  pair-uniquely-existsᵉ : uniquely-exists-structureᵉ Aᵉ Bᵉ → Σᵉ Aᵉ Bᵉ
  pair-uniquely-existsᵉ = centerᵉ

  pr1-uniquely-existsᵉ : uniquely-exists-structureᵉ Aᵉ Bᵉ → Aᵉ
  pr1-uniquely-existsᵉ = pr1ᵉ ∘ᵉ pair-uniquely-existsᵉ

  pr2-uniquely-existsᵉ :
    (pᵉ : uniquely-exists-structureᵉ Aᵉ Bᵉ) → Bᵉ (pr1-uniquely-existsᵉ pᵉ)
  pr2-uniquely-existsᵉ = pr2ᵉ ∘ᵉ pair-uniquely-existsᵉ

  contraction-uniquely-existsᵉ :
    (pᵉ : uniquely-exists-structureᵉ Aᵉ Bᵉ) →
    (qᵉ : Σᵉ Aᵉ Bᵉ) → pair-uniquely-existsᵉ pᵉ ＝ᵉ qᵉ
  contraction-uniquely-existsᵉ = contractionᵉ
```

## See also

-ᵉ Uniqueᵉ existenceᵉ isᵉ theᵉ indexedᵉ counterpartᵉ to
  [exclusiveᵉ disjunction](foundation.exclusive-disjunction.md).ᵉ
-ᵉ Aᵉ differentᵉ nameᵉ forᵉ _uniqueᵉ existenceᵉ_ isᵉ
  [torsoriality](foundation.torsorial-type-families.md).ᵉ

## External links

-ᵉ [uniquenessᵉ quantifier](https://ncatlab.org/nlab/show/uniqueness+quantifierᵉ)
  atᵉ $n$Labᵉ
-ᵉ [Uniquenessᵉ quantification](https://en.wikipedia.org/wiki/Uniqueness_quantificationᵉ)
  atᵉ Wikipediaᵉ
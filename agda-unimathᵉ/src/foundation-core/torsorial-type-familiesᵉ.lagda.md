# Torsorial type families

```agda
module foundation-core.torsorial-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "torsorial"ᵉ Disambiguation="typeᵉ family"ᵉ Agda=is-torsorialᵉ}} ifᵉ itsᵉ
[totalᵉ space](foundation.dependent-pair-types.mdᵉ) isᵉ
[contractible](foundation-core.contractible-types.md).ᵉ

Theᵉ terminologyᵉ ofᵉ torsorialᵉ typeᵉ familiesᵉ isᵉ derivedᵉ fromᵉ torsorsᵉ ofᵉ
[higherᵉ groupᵉ theory](higher-group-theory.md),ᵉ whichᵉ areᵉ typeᵉ familiesᵉ
`Xᵉ : BGᵉ → 𝒰`ᵉ with contractibleᵉ totalᵉ space.ᵉ Inᵉ theᵉ conventionalᵉ senseᵉ ofᵉ theᵉ
word,ᵉ aᵉ torsorᵉ isᵉ thereforeᵉ aᵉ torsorialᵉ typeᵉ familyᵉ overᵉ aᵉ
[pointedᵉ connectedᵉ type](higher-group-theory.higher-groups.md).ᵉ Ifᵉ weᵉ dropᵉ theᵉ
conditionᵉ thatᵉ theyᵉ areᵉ definedᵉ overᵉ aᵉ pointedᵉ connectedᵉ type,ᵉ weᵉ getᵉ to theᵉ
notionᵉ ofᵉ 'torsor-like',ᵉ orᵉ indeedᵉ 'torsorial'ᵉ typeᵉ families.ᵉ

Theᵉ notionᵉ ofᵉ torsorialityᵉ ofᵉ typeᵉ familiesᵉ isᵉ centralᵉ in manyᵉ characterizationsᵉ
ofᵉ identityᵉ types.ᵉ Indeed,ᵉ theᵉ
[fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.mdᵉ)
showsᵉ thatᵉ forᵉ anyᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ andᵉ anyᵉ `aᵉ : A`,ᵉ theᵉ typeᵉ familyᵉ `B`ᵉ
isᵉ torsorialᵉ ifᵉ andᵉ onlyᵉ ifᵉ everyᵉ
[familyᵉ ofᵉ maps](foundation.families-of-maps.mdᵉ)

```text
  (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Bᵉ xᵉ
```

isᵉ aᵉ [familyᵉ ofᵉ equivalences](foundation.families-of-equivalences.md).ᵉ Indeed,ᵉ
theᵉ principalᵉ exampleᵉ ofᵉ aᵉ torsorialᵉ typeᵉ familyᵉ isᵉ theᵉ
[identityᵉ type](foundation-core.identity-types.mdᵉ) itself.ᵉ Moreᵉ generally,ᵉ anyᵉ
typeᵉ familyᵉ in theᵉ [connectedᵉ component](foundation.connected-components.mdᵉ) ofᵉ
theᵉ identityᵉ typeᵉ `xᵉ ↦ᵉ aᵉ ＝ᵉ x`ᵉ isᵉ torsorial.ᵉ Theseᵉ includeᵉ torsorsᵉ ofᵉ higherᵉ
groupsᵉ andᵉ [torsors](group-theory.torsors.mdᵉ) ofᵉ
[concreteᵉ groups](group-theory.concrete-groups.md).ᵉ

Establishingᵉ torsorialityᵉ ofᵉ typeᵉ familiesᵉ isᵉ thereforeᵉ oneᵉ ofᵉ theᵉ routineᵉ tasksᵉ
in univalentᵉ mathematics.ᵉ Someᵉ filesᵉ thatᵉ provideᵉ generalᵉ toolsᵉ forᵉ establishingᵉ
torsorialityᵉ ofᵉ typeᵉ familiesᵉ includeᵉ:

-ᵉ [Equalityᵉ ofᵉ dependentᵉ functionᵉ types](foundation.equality-dependent-function-types.md),ᵉ
-ᵉ Theᵉ
  [structureᵉ identityᵉ principle](foundation.structure-identity-principle.md),ᵉ
-ᵉ Theᵉ [subtypeᵉ identityᵉ principle](foundation.subtype-identity-principle.md).ᵉ

## Definition

### The predicate of being a torsorial type family

```agda
is-torsorialᵉ :
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l1ᵉ} → (Bᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-torsorialᵉ Eᵉ = is-contrᵉ (Σᵉ _ Eᵉ)
```

## Examples

### Identity types are torsorial

Weᵉ proveᵉ twoᵉ variantsᵉ ofᵉ theᵉ claimᵉ thatᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) areᵉ torsorialᵉ:

-ᵉ Theᵉ typeᵉ familyᵉ `xᵉ ↦ᵉ aᵉ ＝ᵉ x`ᵉ isᵉ torsorial,ᵉ andᵉ
-ᵉ Theᵉ typeᵉ familyᵉ `xᵉ ↦ᵉ xᵉ ＝ᵉ a`ᵉ isᵉ torsorial.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-torsorial-Idᵉ : (aᵉ : Aᵉ) → is-torsorialᵉ (λ xᵉ → aᵉ ＝ᵉ xᵉ)
    pr1ᵉ (pr1ᵉ (is-torsorial-Idᵉ aᵉ)) = aᵉ
    pr2ᵉ (pr1ᵉ (is-torsorial-Idᵉ aᵉ)) = reflᵉ
    pr2ᵉ (is-torsorial-Idᵉ aᵉ) (.aᵉ ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-torsorial-Id'ᵉ : (aᵉ : Aᵉ) → is-torsorialᵉ (λ xᵉ → xᵉ ＝ᵉ aᵉ)
    pr1ᵉ (pr1ᵉ (is-torsorial-Id'ᵉ aᵉ)) = aᵉ
    pr2ᵉ (pr1ᵉ (is-torsorial-Id'ᵉ aᵉ)) = reflᵉ
    pr2ᵉ (is-torsorial-Id'ᵉ aᵉ) (.aᵉ ,ᵉ reflᵉ) = reflᵉ
```

### See also

-ᵉ [Discreteᵉ relations](foundation.discrete-relations.mdᵉ) areᵉ binaryᵉ torsorialᵉ
  typeᵉ families.ᵉ
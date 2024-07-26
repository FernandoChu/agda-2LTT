# Indexed W-types

```agda
module trees.indexed-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ conceptᵉ ofᵉ _indexedᵉ W-typesᵉ_ isᵉ aᵉ generalizationᵉ ofᵉ ordinaryᵉ
[W-types](trees.w-types.mdᵉ) using aᵉ dependentlyᵉ typedᵉ variantᵉ ofᵉ
[polynomialᵉ endofunctors](trees.polynomial-endofunctors.md).ᵉ Theᵉ mainᵉ ideaᵉ isᵉ
thatᵉ indexedᵉ W-typesᵉ areᵉ initialᵉ
[algebras](trees.algebras-polynomial-endofunctors.mdᵉ) forᵉ theᵉ polynomialᵉ
endofunctorᵉ

```text
  (Xᵉ : Iᵉ → UUᵉ) ↦ᵉ (λ (jᵉ : Iᵉ) → Σᵉ (aᵉ : Aᵉ j),ᵉ Πᵉ (iᵉ : I),ᵉ Bᵉ iᵉ jᵉ aᵉ → Xᵉ i),ᵉ
```

where `Bᵉ : (iᵉ jᵉ : Iᵉ) → Aᵉ jᵉ → 𝒰`ᵉ isᵉ aᵉ typeᵉ family.ᵉ Inᵉ otherᵉ words,ᵉ givenᵉ theᵉ data

```text
  Aᵉ : Iᵉ → 𝒰ᵉ
  Bᵉ : (iᵉ jᵉ : Iᵉ) → Aᵉ jᵉ → 𝒰ᵉ
```

ofᵉ anᵉ indexedᵉ containerᵉ weᵉ obtainᵉ forᵉ eachᵉ `jᵉ : I`ᵉ aᵉ multivariableᵉ polynomialᵉ

```text
  Σᵉ (aᵉ : Aᵉ j),ᵉ Πᵉ (iᵉ : I),ᵉ Bᵉ iᵉ jᵉ aᵉ → Xᵉ iᵉ
```

Sinceᵉ theᵉ functorialᵉ operationᵉ

```text
  (Xᵉ : Iᵉ → UUᵉ) ↦ᵉ (λ (jᵉ : Iᵉ) → Σᵉ (aᵉ : Aᵉ j),ᵉ Πᵉ (iᵉ : I),ᵉ Bᵉ iᵉ jᵉ aᵉ → Xᵉ i),ᵉ
```

takesᵉ anᵉ `I`-indexedᵉ familyᵉ ofᵉ inputsᵉ andᵉ returnsᵉ anᵉ `I`-indexedᵉ familyᵉ ofᵉ
outputs,ᵉ itᵉ isᵉ endofunctorial,ᵉ meaningᵉ thatᵉ itᵉ canᵉ beᵉ iteratedᵉ andᵉ weᵉ canᵉ
considerᵉ initialᵉ algebrasᵉ forᵉ thisᵉ endofunctor.ᵉ

Weᵉ willᵉ formallyᵉ defineᵉ theᵉ {{#conceptᵉ "indexedᵉ W-type"ᵉ Agda=indexed-𝕎ᵉ}}
associatedᵉ to theᵉ data ofᵉ anᵉ indexedᵉ containerᵉ asᵉ theᵉ inductive typeᵉ generatedᵉ
byᵉ

```text
  tree-indexed-𝕎ᵉ :
    (xᵉ : Aᵉ jᵉ) (αᵉ : (iᵉ : Iᵉ) (yᵉ : Bᵉ iᵉ jᵉ xᵉ) → indexed-𝕎ᵉ iᵉ) → indexed-𝕎ᵉ j.ᵉ
```

**Note.**ᵉ Inᵉ theᵉ usualᵉ definitionᵉ ofᵉ indexedᵉ container,ᵉ theᵉ typeᵉ familyᵉ `B`ᵉ isᵉ
directlyᵉ givenᵉ asᵉ aᵉ typeᵉ familyᵉ overᵉ `A`ᵉ

```text
  Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → 𝒰,ᵉ
```

andᵉ furthermoreᵉ thereᵉ isᵉ aᵉ reindexingᵉ functionᵉ

```text
  jᵉ : (iᵉ : Iᵉ) (aᵉ : Aᵉ iᵉ) → Bᵉ iᵉ aᵉ → I.ᵉ
```

Theᵉ pairᵉ `(Bᵉ ,ᵉ j)`ᵉ ofᵉ suchᵉ aᵉ typeᵉ familyᵉ andᵉ aᵉ reindexingᵉ functionᵉ isᵉ viaᵉ
[typeᵉ duality](foundation.type-duality.mdᵉ) equivalentᵉ to aᵉ singleᵉ typeᵉ familyᵉ

```text
  (jᵉ iᵉ : Iᵉ) → Aᵉ iᵉ → 𝒰.ᵉ
```

## Definitions

### The indexed W-type associated to an indexed container

```agda
data
  indexed-𝕎ᵉ
    {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Aᵉ : Iᵉ → UUᵉ l2ᵉ)
    (Bᵉ : (iᵉ jᵉ : Iᵉ) → Aᵉ jᵉ → UUᵉ l3ᵉ) (jᵉ : Iᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
    where
  tree-indexed-𝕎ᵉ :
    (xᵉ : Aᵉ jᵉ) (αᵉ : (iᵉ : Iᵉ) (yᵉ : Bᵉ iᵉ jᵉ xᵉ) → indexed-𝕎ᵉ Iᵉ Aᵉ Bᵉ iᵉ) →
    indexed-𝕎ᵉ Iᵉ Aᵉ Bᵉ jᵉ
```
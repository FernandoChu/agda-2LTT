# The action on identifications of dependent functions

```agda
module foundation.action-on-identifications-dependent-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.dependent-identificationsᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ dependentᵉ functionᵉ `fᵉ : (xᵉ : Aᵉ) → Bᵉ x`ᵉ andᵉ anᵉ
[identification](foundation-core.identity-types.mdᵉ) `pᵉ : xᵉ ＝ᵉ y`ᵉ in `A`,ᵉ weᵉ
cannotᵉ directlyᵉ compareᵉ theᵉ valuesᵉ `fᵉ x`ᵉ andᵉ `fᵉ y`,ᵉ sinceᵉ `fᵉ x`ᵉ isᵉ anᵉ elementᵉ ofᵉ
typeᵉ `Bᵉ x`ᵉ whileᵉ `fᵉ y`ᵉ isᵉ anᵉ elementᵉ ofᵉ typeᵉ `Bᵉ y`.ᵉ However,ᵉ weᵉ canᵉ
[transport](foundation-core.transport-along-identifications.mdᵉ) theᵉ valueᵉ `fᵉ x`ᵉ
alongᵉ `p`ᵉ to obtainᵉ anᵉ elementᵉ ofᵉ typeᵉ `Bᵉ y`ᵉ thatᵉ isᵉ comparableᵉ to theᵉ valueᵉ
`fᵉ y`.ᵉ Inᵉ otherᵉ words,ᵉ weᵉ canᵉ considerᵉ theᵉ typeᵉ ofᵉ
[dependentᵉ identifications](foundation-core.dependent-identifications.mdᵉ) overᵉ
`p`ᵉ fromᵉ `fᵉ x`ᵉ to `fᵉ y`.ᵉ Theᵉ **dependentᵉ actionᵉ onᵉ identifications**ᵉ ofᵉ `f`ᵉ onᵉ
`p`ᵉ isᵉ aᵉ dependentᵉ identificationᵉ

```text
  apdᵉ fᵉ pᵉ : dependent-identificationᵉ Bᵉ pᵉ (fᵉ xᵉ) (fᵉ y).ᵉ
```

## Definition

### Functorial action of dependent functions on identity types

```agda
apdᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) {xᵉ yᵉ : Aᵉ}
  (pᵉ : xᵉ ＝ᵉ yᵉ) → dependent-identificationᵉ Bᵉ pᵉ (fᵉ xᵉ) (fᵉ yᵉ)
apdᵉ fᵉ reflᵉ = reflᵉ
```

## See also

-ᵉ [Actionᵉ ofᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
-ᵉ [Actionᵉ ofᵉ functionsᵉ onᵉ higherᵉ identifications](foundation.action-on-higher-identifications-functions.md).ᵉ
-ᵉ [Actionᵉ ofᵉ binaryᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-binary-functions.md).ᵉ
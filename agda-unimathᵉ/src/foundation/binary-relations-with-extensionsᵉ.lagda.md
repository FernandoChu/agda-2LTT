# Binary relations with extensions

```agda
module foundation.binary-relations-with-extensionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
```

</details>

## Idea

Weᵉ sayᵉ aᵉ [relation](foundation.binary-relations.mdᵉ) `R`ᵉ
{{#conceptᵉ "hasᵉ extensions"ᵉ Disambiguation="binaryᵉ relationsᵉ ofᵉ types"ᵉ Agda=has-extensions-Relationᵉ}}
ifᵉ forᵉ everyᵉ tripleᵉ `xᵉ yᵉ zᵉ : A`,ᵉ thereᵉ isᵉ aᵉ binaryᵉ operationᵉ

```text
  Rᵉ xᵉ yᵉ → Rᵉ xᵉ zᵉ → Rᵉ yᵉ z.ᵉ
```

Relationsᵉ with extensionsᵉ areᵉ closelyᵉ relatedᵉ to transitiveᵉ relations.ᵉ But,ᵉ
insteadᵉ ofᵉ givingᵉ forᵉ everyᵉ diagramᵉ

```text
       yᵉ
      ∧ᵉ \ᵉ
     /ᵉ   \ᵉ
    /ᵉ     ∨ᵉ
  xᵉ        zᵉ
```

aᵉ horizontalᵉ arrowᵉ `xᵉ → z`,ᵉ aᵉ binaryᵉ relationᵉ with extensionsᵉ gives,ᵉ forᵉ everyᵉ
spanᵉ

```text
       yᵉ
      ∧ᵉ
     /ᵉ
    /ᵉ
  xᵉ ----->ᵉ z,ᵉ
```

anᵉ _extensionᵉ_ `yᵉ → z`.ᵉ Byᵉ symmetryᵉ itᵉ alsoᵉ givesᵉ anᵉ extensionᵉ in theᵉ oppositeᵉ
directionᵉ `zᵉ → y`.ᵉ

Dually,ᵉ aᵉ relationᵉ `R`ᵉ
[hasᵉ lifts](foundation.binary-relations-with-extensions.mdᵉ) ifᵉ forᵉ everyᵉ tripleᵉ
`xᵉ yᵉ zᵉ : A`,ᵉ thereᵉ isᵉ aᵉ binaryᵉ operationᵉ

```text
  Rᵉ xᵉ zᵉ → Rᵉ yᵉ zᵉ → Rᵉ xᵉ y.ᵉ
```

## Definition

### The structure on relations of having extensions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  has-extensions-Relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-extensions-Relationᵉ = {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ xᵉ zᵉ → Rᵉ yᵉ zᵉ
```

## Properties

### If there is an element that relates to `y` and the relation has extensions, then `y` relates to `y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  rel-self-any-rel-has-extensions-Relationᵉ :
    has-extensions-Relationᵉ Rᵉ → {xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ yᵉ yᵉ
  rel-self-any-rel-has-extensions-Relationᵉ Hᵉ pᵉ = Hᵉ pᵉ pᵉ
```

### The reverse of an extension

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  reverse-has-extensions-Relationᵉ :
    has-extensions-Relationᵉ Rᵉ → {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ zᵉ xᵉ → Rᵉ zᵉ yᵉ → Rᵉ yᵉ xᵉ
  reverse-has-extensions-Relationᵉ Hᵉ pᵉ qᵉ = Hᵉ qᵉ pᵉ
```

### Reflexive relations with extensions are symmetric

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  (Hᵉ : has-extensions-Relationᵉ Rᵉ)
  where

  is-symmetric-is-reflexive-has-extensions-Relationᵉ :
    is-reflexiveᵉ Rᵉ → is-symmetricᵉ Rᵉ
  is-symmetric-is-reflexive-has-extensions-Relationᵉ rᵉ xᵉ yᵉ pᵉ = Hᵉ pᵉ (rᵉ xᵉ)
```

### Reflexive relations with extensions are transitive

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  (Hᵉ : has-extensions-Relationᵉ Rᵉ)
  where

  is-transitive-is-symmetric-has-extensions-Relationᵉ :
    is-symmetricᵉ Rᵉ → is-transitiveᵉ Rᵉ
  is-transitive-is-symmetric-has-extensions-Relationᵉ sᵉ xᵉ yᵉ zᵉ pᵉ qᵉ = Hᵉ (sᵉ xᵉ yᵉ qᵉ) pᵉ

  is-transitive-is-reflexive-has-extensions-Relationᵉ :
    is-reflexiveᵉ Rᵉ → is-transitiveᵉ Rᵉ
  is-transitive-is-reflexive-has-extensions-Relationᵉ rᵉ =
    is-transitive-is-symmetric-has-extensions-Relationᵉ
      ( is-symmetric-is-reflexive-has-extensions-Relationᵉ Rᵉ Hᵉ rᵉ)
```

## See also

-ᵉ [Strictᵉ symmetrizationᵉ ofᵉ binaryᵉ relations](foundation.strict-symmetrization-binary-relations.mdᵉ)
# Binary relations with lifts

```agda
module foundation.binary-relations-with-liftsᵉ where
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
{{#conceptᵉ "hasᵉ lifts"ᵉ Disambiguation="binaryᵉ relationsᵉ ofᵉ types"ᵉ Agda=has-lifts-Relationᵉ}}
ifᵉ forᵉ everyᵉ tripleᵉ `xᵉ yᵉ zᵉ : A`,ᵉ thereᵉ isᵉ aᵉ binaryᵉ operationᵉ

```text
  Rᵉ xᵉ zᵉ → Rᵉ yᵉ zᵉ → Rᵉ xᵉ y.ᵉ
```

Relationsᵉ with liftsᵉ areᵉ closelyᵉ relatedᵉ to transitiveᵉ relations.ᵉ But,ᵉ insteadᵉ
ofᵉ givingᵉ forᵉ everyᵉ diagramᵉ

```text
       yᵉ
      ∧ᵉ \ᵉ
     /ᵉ   \ᵉ
    /ᵉ     ∨ᵉ
  xᵉ        zᵉ
```

aᵉ horizontalᵉ arrowᵉ `xᵉ → z`,ᵉ aᵉ binaryᵉ relationᵉ with liftsᵉ gives,ᵉ forᵉ everyᵉ cospanᵉ

```text
       yᵉ
        \ᵉ
         \ᵉ
          ∨ᵉ
  xᵉ ----->ᵉ z,ᵉ
```

aᵉ _liftᵉ_ `xᵉ → y`.ᵉ Byᵉ symmetryᵉ itᵉ alsoᵉ givesᵉ aᵉ liftᵉ in theᵉ oppositeᵉ directionᵉ
`yᵉ → x`.ᵉ

Dually,ᵉ aᵉ relationᵉ `R`ᵉ
[hasᵉ extensions](foundation.binary-relations-with-extensions.mdᵉ) ifᵉ forᵉ everyᵉ
tripleᵉ `xᵉ yᵉ zᵉ : A`,ᵉ thereᵉ isᵉ aᵉ binaryᵉ operationᵉ

```text
  Rᵉ xᵉ yᵉ → Rᵉ xᵉ zᵉ → Rᵉ yᵉ z.ᵉ
```

## Definition

### The structure on relations of having lifts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  has-lifts-Relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-lifts-Relationᵉ = {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ xᵉ zᵉ → Rᵉ yᵉ zᵉ → Rᵉ xᵉ yᵉ
```

## Properties

### If `x` relates to an element and the relation has lifts, then `x` relates to `x`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  rel-self-rel-any-has-lifts-Relationᵉ :
    has-lifts-Relationᵉ Rᵉ → {xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ xᵉ xᵉ
  rel-self-rel-any-has-lifts-Relationᵉ Hᵉ pᵉ = Hᵉ pᵉ pᵉ
```

### The reverse of a lift

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  reverse-has-lifts-Relationᵉ :
    has-lifts-Relationᵉ Rᵉ → {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ xᵉ zᵉ → Rᵉ yᵉ zᵉ → Rᵉ yᵉ xᵉ
  reverse-has-lifts-Relationᵉ Hᵉ pᵉ qᵉ = Hᵉ qᵉ pᵉ
```

### Reflexive relations with lifts are symmetric

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  (Hᵉ : has-lifts-Relationᵉ Rᵉ)
  where

  is-symmetric-is-reflexive-has-lifts-Relationᵉ :
    is-reflexiveᵉ Rᵉ → is-symmetricᵉ Rᵉ
  is-symmetric-is-reflexive-has-lifts-Relationᵉ rᵉ xᵉ yᵉ pᵉ = Hᵉ (rᵉ yᵉ) pᵉ
```

### Reflexive relations with lifts are transitive

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  (Hᵉ : has-lifts-Relationᵉ Rᵉ)
  where

  is-transitive-is-symmetric-has-lifts-Relationᵉ :
    is-symmetricᵉ Rᵉ → is-transitiveᵉ Rᵉ
  is-transitive-is-symmetric-has-lifts-Relationᵉ sᵉ xᵉ yᵉ zᵉ pᵉ qᵉ = Hᵉ qᵉ (sᵉ yᵉ zᵉ pᵉ)

  is-transitive-is-reflexive-has-lifts-Relationᵉ :
    is-reflexiveᵉ Rᵉ → is-transitiveᵉ Rᵉ
  is-transitive-is-reflexive-has-lifts-Relationᵉ rᵉ =
    is-transitive-is-symmetric-has-lifts-Relationᵉ
      ( is-symmetric-is-reflexive-has-lifts-Relationᵉ Rᵉ Hᵉ rᵉ)
```
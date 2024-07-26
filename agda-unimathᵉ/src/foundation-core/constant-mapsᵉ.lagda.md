# Constant maps

```agda
module foundation-core.constant-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "constantᵉ map"ᵉ Agda=constᵉ}} fromᵉ `A`ᵉ to `B`ᵉ atᵉ anᵉ elementᵉ `bᵉ : B`ᵉ
isᵉ theᵉ functionᵉ `xᵉ ↦ᵉ b`ᵉ mappingᵉ everyᵉ elementᵉ `xᵉ : A`ᵉ to theᵉ givenᵉ elementᵉ
`bᵉ : B`.ᵉ Inᵉ commonᵉ typeᵉ theoreticᵉ notation,ᵉ theᵉ constantᵉ mapᵉ atᵉ `b`ᵉ isᵉ theᵉ
functionᵉ

```text
  λ xᵉ → b.ᵉ
```

## Definition

```agda
constᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} → Bᵉ → Aᵉ → Bᵉ
constᵉ Aᵉ bᵉ xᵉ = bᵉ
```

## See also

-ᵉ [Constantᵉ pointedᵉ maps](structured-types.constant-pointed-maps.mdᵉ)
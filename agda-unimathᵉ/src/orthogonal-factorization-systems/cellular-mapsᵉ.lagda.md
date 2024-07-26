# Cellular maps

```agda
module orthogonal-factorization-systems.cellular-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-mapsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.mere-lifting-propertiesᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ **`k`-cellular**ᵉ ifᵉ itᵉ satisfiesᵉ theᵉ leftᵉ
[mereᵉ liftingᵉ propery](orthogonal-factorization-systems.mere-lifting-properties.mdᵉ)
with respectᵉ to [`k`-connectedᵉ maps](foundation.connected-maps.md).ᵉ Inᵉ otherᵉ
words,ᵉ aᵉ mapᵉ `f`ᵉ isᵉ `k`-cellularᵉ ifᵉ theᵉ
[pullback-hom](orthogonal-factorization-systems.pullback-hom.mdᵉ)

```text
  ⟨ᵉ fᵉ ,ᵉ gᵉ ⟩ᵉ
```

with anyᵉ `k`-connectedᵉ mapᵉ `g`ᵉ isᵉ [surjective](foundation.surjective-maps.md).ᵉ
Theᵉ terminologyᵉ `k`-cellularᵉ comesᵉ fromᵉ theᵉ factᵉ thatᵉ theᵉ `k`-connectedᵉ mapsᵉ areᵉ
preciselyᵉ theᵉ mapsᵉ thatᵉ satisfyᵉ theᵉ rightᵉ mereᵉ liftingᵉ propertyᵉ wtihᵉ respectᵉ to
theᵉ [spheres](synthetic-homotopy-theory.spheres.mdᵉ)

```text
  Sⁱᵉ → unitᵉ
```

forᵉ allᵉ `-1ᵉ ≤ᵉ iᵉ ≤ᵉ k`.ᵉ Inᵉ thisᵉ sense,ᵉ `k`-cellularᵉ mapsᵉ areᵉ "builtᵉ outᵉ ofᵉ
spheres".ᵉ Alternatively,ᵉ `k`-cellularᵉ mapsᵉ mightᵉ alsoᵉ beᵉ calledᵉ **`k`-projectiveᵉ
maps**.ᵉ Thisᵉ emphasizesᵉ theᵉ conditionᵉ thatᵉ `k`-projectiveᵉ mapsᵉ liftᵉ againstᵉ
`k`-connectedᵉ maps.ᵉ

Inᵉ theᵉ toposᵉ ofᵉ spaces,ᵉ theᵉ `k`-cellularᵉ mapsᵉ areᵉ theᵉ leftᵉ classᵉ ofᵉ anᵉ
_externalᵉ_ weakᵉ factorizationᵉ systemᵉ onᵉ spacesᵉ ofᵉ whichᵉ theᵉ rightᵉ classᵉ isᵉ theᵉ
classᵉ ofᵉ `k`-connectedᵉ maps,ᵉ butᵉ thereᵉ isᵉ noᵉ suchᵉ weakᵉ factorizationᵉ systemᵉ
definableᵉ internally.ᵉ

## Definitions

### The predicate of being a `k`-cellular map

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-cellular-mapᵉ : UUωᵉ
  is-cellular-mapᵉ =
    {l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (gᵉ : Xᵉ → Yᵉ) →
    is-connected-mapᵉ kᵉ gᵉ → mere-diagonal-liftᵉ fᵉ gᵉ
```
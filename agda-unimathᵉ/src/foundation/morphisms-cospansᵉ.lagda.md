# Morphisms of cospans

```agda
module foundation.morphisms-cospansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.cospansᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [cospans](foundation.cospans.mdᵉ) `cᵉ :=ᵉ (Xᵉ ,ᵉ fᵉ ,ᵉ g)`ᵉ andᵉ
`dᵉ :=ᵉ (Yᵉ ,ᵉ hᵉ ,ᵉ k)`ᵉ fromᵉ `A`ᵉ to `B`.ᵉ Aᵉ
{{#conceptᵉ "morphismᵉ ofᵉ cospans"ᵉ Agda=hom-cospanᵉ}} fromᵉ `c`ᵉ to `d`ᵉ consistsᵉ ofᵉ aᵉ
mapᵉ `uᵉ : Xᵉ → Y`ᵉ equippedᵉ with [homotopies](foundation-core.homotopies.mdᵉ)
witnessingᵉ thatᵉ theᵉ twoᵉ trianglesᵉ

```text
      uᵉ              uᵉ
  Xᵉ ---->ᵉ Yᵉ      Xᵉ ---->ᵉ Yᵉ
   \ᵉ     /ᵉ        \ᵉ     /ᵉ
  fᵉ \ᵉ   /ᵉ hᵉ      gᵉ \ᵉ   /ᵉ kᵉ
     ∨ᵉ ∨ᵉ            ∨ᵉ ∨ᵉ
      Aᵉ              Bᵉ
```

[commute](foundation.commuting-triangles-of-maps.md).ᵉ

## Definitions

### Morphisms of cospans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (cᵉ : cospanᵉ l3ᵉ Aᵉ Bᵉ) (dᵉ : cospanᵉ l4ᵉ Aᵉ Bᵉ)
  where

  coherence-hom-cospanᵉ :
    (codomain-cospanᵉ cᵉ → codomain-cospanᵉ dᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  coherence-hom-cospanᵉ hᵉ =
    ( coherence-triangle-mapsᵉ (left-map-cospanᵉ dᵉ) hᵉ (left-map-cospanᵉ cᵉ)) ×ᵉ
    ( coherence-triangle-mapsᵉ (right-map-cospanᵉ dᵉ) hᵉ (right-map-cospanᵉ cᵉ))

  hom-cospanᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-cospanᵉ =
    Σᵉ ( codomain-cospanᵉ cᵉ → codomain-cospanᵉ dᵉ)
      ( coherence-hom-cospanᵉ)
```
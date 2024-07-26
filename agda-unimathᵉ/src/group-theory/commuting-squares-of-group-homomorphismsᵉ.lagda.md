# Commuting squares of group homomorphisms

```agda
module group-theory.commuting-squares-of-group-homomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
```

</details>

## Idea

Aᵉ squareᵉ ofᵉ [groupᵉ homomorphisms](group-theory.homomorphisms-groups.mdᵉ)

```text
        fᵉ
    Gᵉ ----->ᵉ Hᵉ
    |        |
  gᵉ |        | hᵉ
    ∨ᵉ        ∨ᵉ
    Kᵉ ----->ᵉ Lᵉ
        kᵉ
```

isᵉ saidᵉ to **commute**ᵉ ifᵉ theᵉ underlyingᵉ squareᵉ ofᵉ mapsᵉ
[commutes](foundation.commuting-squares-of-maps.md),ᵉ i.e.,ᵉ ifᵉ `kᵉ ∘ᵉ gᵉ ~ᵉ hᵉ ∘ᵉ f`.ᵉ

## Definitions

### Commuting squares of group homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (Kᵉ : Groupᵉ l3ᵉ) (Lᵉ : Groupᵉ l4ᵉ)
  (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) (gᵉ : hom-Groupᵉ Gᵉ Kᵉ)
  (hᵉ : hom-Groupᵉ Hᵉ Lᵉ) (kᵉ : hom-Groupᵉ Kᵉ Lᵉ)
  where

  coherence-square-hom-Groupᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-square-hom-Groupᵉ =
    coherence-square-mapsᵉ
      ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( map-hom-Groupᵉ Gᵉ Kᵉ gᵉ)
      ( map-hom-Groupᵉ Hᵉ Lᵉ hᵉ)
      ( map-hom-Groupᵉ Kᵉ Lᵉ kᵉ)
```
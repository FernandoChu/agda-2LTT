# Sequential diagrams

```agda
module synthetic-homotopy-theory.sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **sequentialᵉ diagram**ᵉ `(A,ᵉ a)`ᵉ isᵉ aᵉ [sequence](foundation.sequences.mdᵉ) ofᵉ
typesᵉ `Aᵉ : ℕᵉ → 𝒰`ᵉ overᵉ theᵉ naturalᵉ numbers,ᵉ equippedᵉ with aᵉ familyᵉ ofᵉ mapsᵉ
`aₙᵉ : Aₙᵉ → Aₙ₊₁`ᵉ forᵉ allᵉ `n`.ᵉ

Theyᵉ canᵉ beᵉ representedᵉ byᵉ diagramsᵉ

```text
     a₀ᵉ      a₁ᵉ      a₂ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
```

extendingᵉ infinitelyᵉ to theᵉ right.ᵉ

Sequentialᵉ diagramsᵉ areᵉ dualᵉ to
[inverseᵉ sequentialᵉ diagrams](foundation.inverse-sequential-diagrams.md),ᵉ andᵉ
areᵉ alsoᵉ sometimesᵉ calledᵉ **cotowers**.ᵉ

## Definition

```agda
sequential-diagramᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
sequential-diagramᵉ lᵉ = Σᵉ (ℕᵉ → UUᵉ lᵉ) (λ Aᵉ → (nᵉ : ℕᵉ) → Aᵉ nᵉ → Aᵉ (succ-ℕᵉ nᵉ))

module _
  { lᵉ : Level} (Aᵉ : sequential-diagramᵉ lᵉ)
  where

  family-sequential-diagramᵉ : ℕᵉ → UUᵉ lᵉ
  family-sequential-diagramᵉ = pr1ᵉ Aᵉ

  map-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) → family-sequential-diagramᵉ nᵉ → family-sequential-diagramᵉ (succ-ℕᵉ nᵉ)
  map-sequential-diagramᵉ = pr2ᵉ Aᵉ
```

```agda
module _
  { lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  constant-sequential-diagramᵉ : sequential-diagramᵉ lᵉ
  pr1ᵉ constant-sequential-diagramᵉ _ = Xᵉ
  pr2ᵉ constant-sequential-diagramᵉ _ xᵉ = xᵉ
```

## Properties

Theᵉ [identityᵉ type](foundation.identity-types.mdᵉ) ofᵉ sequentialᵉ diagramsᵉ isᵉ
characterizedᵉ in theᵉ fileᵉ aboutᵉ
[equivalencesᵉ ofᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md).ᵉ

### Postcomposition sequential diagrams

Givenᵉ aᵉ sequentialᵉ diagramᵉ `A`ᵉ andᵉ aᵉ typeᵉ `X`ᵉ thereᵉ isᵉ aᵉ sequentialᵉ diagramᵉ
`Xᵉ → A`ᵉ definedᵉ byᵉ levelwiseᵉ postcomposition.ᵉ

```text
           (f₀ᵉ ∘ᵉ -ᵉ)          (f₁ᵉ ∘ᵉ -ᵉ)          (f₂ᵉ ∘ᵉ -ᵉ)
  (Xᵉ → A₀ᵉ) ------->ᵉ (Xᵉ → A₁ᵉ) ------->ᵉ (Xᵉ → A₂ᵉ) ------->ᵉ (Xᵉ → A₃ᵉ) ------->ᵉ ⋯ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Aᵉ : sequential-diagramᵉ l2ᵉ)
  where

  postcomp-sequential-diagramᵉ : sequential-diagramᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ postcomp-sequential-diagramᵉ nᵉ = Xᵉ → family-sequential-diagramᵉ Aᵉ nᵉ
  pr2ᵉ postcomp-sequential-diagramᵉ nᵉ gᵉ xᵉ = map-sequential-diagramᵉ Aᵉ nᵉ (gᵉ xᵉ)
```

### A sequential diagram of contractible types consists of equivalences

Thisᵉ isᵉ anᵉ easyᵉ corollaryᵉ ofᵉ theᵉ factᵉ thatᵉ everyᵉ mapᵉ betweenᵉ
[contractibleᵉ types](foundation-core.contractible-types.mdᵉ) isᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ

```agda
module _
  {l1ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  where

  is-equiv-sequential-diagram-is-contrᵉ :
    ((nᵉ : ℕᵉ) → is-contrᵉ (family-sequential-diagramᵉ Aᵉ nᵉ)) →
    (nᵉ : ℕᵉ) → is-equivᵉ (map-sequential-diagramᵉ Aᵉ nᵉ)
  is-equiv-sequential-diagram-is-contrᵉ contrsᵉ nᵉ =
    is-equiv-is-contrᵉ
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( contrsᵉ nᵉ)
      ( contrsᵉ (succ-ℕᵉ nᵉ))
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ SvDR20ᵉ}}
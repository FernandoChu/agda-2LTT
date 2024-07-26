# Propositional resizing

```agda
module foundation.propositional-resizingᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Weᵉ sayᵉ thatᵉ aᵉ universeᵉ `𝒱`ᵉ satisfiesᵉ `𝒰`-smallᵉ
{{#conceptᵉ "propositionalᵉ resizing"ᵉ}} ifᵉ thereᵉ isᵉ aᵉ typeᵉ `Ω`ᵉ in `𝒰`ᵉ
[equipped](foundation.structure.mdᵉ) with aᵉ
[subtype](foundation-core.subtypes.mdᵉ) `Q`ᵉ suchᵉ thatᵉ forᵉ eachᵉ propositionᵉ `P`ᵉ in
`𝒱`ᵉ thereᵉ isᵉ anᵉ elementᵉ `uᵉ : Ω`ᵉ suchᵉ thatᵉ `Qᵉ uᵉ ≃ᵉ P`.ᵉ Suchᵉ aᵉ typeᵉ `Ω`ᵉ isᵉ calledᵉ
anᵉ `𝒰`-smallᵉ {{#conceptᵉ "classifier"ᵉ Disambiguation="ofᵉ smallᵉ subobjects"ᵉ}} ofᵉ
`𝒱`-smallᵉ subobjects.ᵉ

## Definition

```agda
propositional-resizingᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
propositional-resizingᵉ l1ᵉ l2ᵉ =
  Σᵉ ( Σᵉ (UUᵉ l1ᵉ) (subtypeᵉ l1ᵉ))
    ( λ Ωᵉ → (Pᵉ : Propᵉ l2ᵉ) → Σᵉ (pr1ᵉ Ωᵉ) (λ uᵉ → type-equiv-Propᵉ (pr2ᵉ Ωᵉ uᵉ) Pᵉ))
```

## See also

-ᵉ [Theᵉ largeᵉ localeᵉ ofᵉ propositions](foundation.large-locale-of-propositions.mdᵉ)

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}
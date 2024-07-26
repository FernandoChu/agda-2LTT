# Negation

```agda
module foundation-core.negationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.empty-typesᵉ
```

</details>

## Idea

Theᵉ Curry-Howardᵉ interpretationᵉ ofᵉ _negationᵉ_ in typeᵉ theoryᵉ isᵉ theᵉ
interpretationᵉ ofᵉ theᵉ propositionᵉ `Pᵉ ⇒ᵉ ⊥`ᵉ using propositionsᵉ asᵉ types.ᵉ Thus,ᵉ theᵉ
{{#conceptᵉ "negation"ᵉ Disambiguation="ofᵉ aᵉ type"ᵉ WDID=Q190558ᵉ WD="logicalᵉ negation"ᵉ Agda=¬ᵉ_}}
ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ theᵉ typeᵉ `Aᵉ → empty`.ᵉ

## Definition

```agda
infix 25 ¬ᵉ_

¬ᵉ_ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
¬ᵉ Aᵉ = Aᵉ → emptyᵉ

map-negᵉ :
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} →
  (Pᵉ → Qᵉ) → (¬ᵉ Qᵉ → ¬ᵉ Pᵉ)
map-negᵉ fᵉ nqᵉ pᵉ = nqᵉ (fᵉ pᵉ)
```

## External links

-ᵉ [negation](https://ncatlab.org/nlab/show/negationᵉ) atᵉ $n$Labᵉ
-ᵉ [Negation](https://en.wikipedia.org/wiki/Negationᵉ) atᵉ Wikipediaᵉ
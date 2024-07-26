# Opposite pointed spans

```agda
module structured-types.opposite-pointed-spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-spansᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ [pointedᵉ span](structured-types.pointed-spans.mdᵉ) `𝒮ᵉ :=ᵉ (Sᵉ ,ᵉ fᵉ ,ᵉ g)`ᵉ
fromᵉ `A`ᵉ to `B`.ᵉ Theᵉ
{{#conceptᵉ "oppositeᵉ pointedᵉ span"ᵉ Agda=opposite-pointed-spanᵉ}} ofᵉ
`𝒮ᵉ :=ᵉ (Sᵉ ,ᵉ fᵉ ,ᵉ g)`ᵉ isᵉ theᵉ pointedᵉ spanᵉ `(Sᵉ ,ᵉ gᵉ ,ᵉ f)`ᵉ fromᵉ `B`ᵉ to `A`.ᵉ Inᵉ otherᵉ
words,ᵉ theᵉ oppositeᵉ ofᵉ aᵉ pointedᵉ spanᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

isᵉ theᵉ pointedᵉ spanᵉ

```text
       gᵉ       fᵉ
  Bᵉ <-----ᵉ Sᵉ ----->ᵉ A.ᵉ
```

## Definitions

### The opposite of a pointed span

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  where

  opposite-pointed-spanᵉ :
    pointed-spanᵉ l3ᵉ Aᵉ Bᵉ → pointed-spanᵉ l3ᵉ Bᵉ Aᵉ
  pr1ᵉ (opposite-pointed-spanᵉ sᵉ) =
    spanning-pointed-type-pointed-spanᵉ sᵉ
  pr1ᵉ (pr2ᵉ (opposite-pointed-spanᵉ sᵉ)) =
    right-pointed-map-pointed-spanᵉ sᵉ
  pr2ᵉ (pr2ᵉ (opposite-pointed-spanᵉ sᵉ)) =
    left-pointed-map-pointed-spanᵉ sᵉ
```

## See also

-ᵉ [Transpositionsᵉ ofᵉ spanᵉ diagrams](foundation.transposition-span-diagrams.mdᵉ)
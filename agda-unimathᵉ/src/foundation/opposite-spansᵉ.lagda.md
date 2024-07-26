# Opposite spans

```agda
module foundation.opposite-spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [span](foundation.spans.mdᵉ) `(Sᵉ ,ᵉ fᵉ ,ᵉ g)`ᵉ fromᵉ `A`ᵉ to `B`.ᵉ Theᵉ
{{#conceptᵉ "oppositeᵉ span"ᵉ Agda=opposite-spanᵉ}} ofᵉ `(Sᵉ ,ᵉ fᵉ ,ᵉ g)`ᵉ isᵉ theᵉ spanᵉ
`(Sᵉ ,ᵉ gᵉ ,ᵉ f)`ᵉ fromᵉ `B`ᵉ to `A`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ oppositeᵉ ofᵉ aᵉ spanᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

isᵉ theᵉ spanᵉ

```text
       gᵉ       fᵉ
  Bᵉ <-----ᵉ Sᵉ ----->ᵉ A.ᵉ
```

Recallᵉ thatᵉ [binaryᵉ typeᵉ duality](foundation.binary-type-duality.mdᵉ) showsᵉ thatᵉ
spansᵉ areᵉ equivalentᵉ to [binaryᵉ relations](foundation.binary-relations.mdᵉ) fromᵉ
`A`ᵉ to `B`.ᵉ Theᵉ oppositeᵉ ofᵉ aᵉ spanᵉ correspondsᵉ to theᵉ oppositeᵉ ofᵉ aᵉ binaryᵉ
relation.ᵉ

## Definitions

### The opposite of a span

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  opposite-spanᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ → spanᵉ l3ᵉ Bᵉ Aᵉ
  pr1ᵉ (opposite-spanᵉ sᵉ) = spanning-type-spanᵉ sᵉ
  pr1ᵉ (pr2ᵉ (opposite-spanᵉ sᵉ)) = right-map-spanᵉ sᵉ
  pr2ᵉ (pr2ᵉ (opposite-spanᵉ sᵉ)) = left-map-spanᵉ sᵉ
```

## See also

-ᵉ [Transpositionsᵉ ofᵉ spanᵉ diagrams](foundation.transposition-span-diagrams.mdᵉ)
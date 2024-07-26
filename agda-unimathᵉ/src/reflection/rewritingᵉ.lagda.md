# Rewriting

```agda
{-# OPTIONSᵉ --rewritingᵉ #-}

module reflection.rewritingᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Agda'sᵉ rewritingᵉ functionalityᵉ allowsᵉ usᵉ to addᵉ newᵉ strictᵉ equalitiesᵉ to ourᵉ
typeᵉ theory.ᵉ Givenᵉ anᵉ [identification](foundation-core.identity-types.mdᵉ)
`βᵉ : xᵉ ＝ᵉ y`,ᵉ thenᵉ addingᵉ aᵉ rewriteᵉ ruleᵉ forᵉ `β`ᵉ with

```text
{-# REWRITEᵉ βᵉ #-}
```

willᵉ makeᵉ itᵉ soᵉ `x`ᵉ rewritesᵉ to `y`,ᵉ i.e.,ᵉ `xᵉ ≐ᵉ y`.ᵉ

**Warning.**ᵉ Rewritingᵉ isᵉ byᵉ natureᵉ aᵉ veryᵉ unsafeᵉ toolᵉ soᵉ weᵉ adviceᵉ exercisingᵉ
abundantᵉ cautionᵉ whenᵉ definingᵉ suchᵉ rules.ᵉ

## Definitions

Weᵉ declareᵉ to Agdaᵉ thatᵉ theᵉ
[standardᵉ identityᵉ relation](foundation.identity-types.mdᵉ) mayᵉ beᵉ usedᵉ to defineᵉ
rewriteᵉ rules.ᵉ

```agda

```

## See also

-ᵉ [Erasingᵉ equality](reflection.erasing-equality.mdᵉ)

## External links

-ᵉ [Rewriting](https://agda.readthedocs.io/en/latest/language/rewriting.htmlᵉ) atᵉ
  Agda'sᵉ documentationᵉ pagesᵉ
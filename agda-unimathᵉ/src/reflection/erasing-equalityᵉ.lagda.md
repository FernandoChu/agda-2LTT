# Erasing equality

```agda
module reflection.erasing-equalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Agda'sᵉ builtinᵉ primitive `primEraseEquality`ᵉ isᵉ aᵉ specialᵉ constructᵉ onᵉ
[identifications](foundation-core.identity-types.mdᵉ) thatᵉ forᵉ everyᵉ
identificationᵉ `xᵉ ＝ᵉ y`ᵉ givesᵉ anᵉ identificationᵉ `xᵉ ＝ᵉ y`ᵉ with theᵉ followingᵉ
reductionᵉ behaviourᵉ:

-ᵉ Ifᵉ theᵉ twoᵉ endᵉ pointsᵉ `xᵉ ＝ᵉ y`ᵉ normalizeᵉ to theᵉ sameᵉ term,ᵉ `primEraseEquality`ᵉ
  reducesᵉ to `refl`.ᵉ

Forᵉ example,ᵉ `primEraseEquality`ᵉ appliedᵉ to theᵉ loopᵉ ofᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.mdᵉ) willᵉ computeᵉ to `refl`,ᵉ whileᵉ
`primEraseEquality`ᵉ appliedᵉ to theᵉ nontrivialᵉ identificationᵉ in theᵉ
[interval](synthetic-homotopy-theory.interval-type.mdᵉ) willᵉ notᵉ reduce.ᵉ

Thisᵉ primitive isᵉ usefulᵉ forᵉ [rewriteᵉ rules](reflection.rewriting.md),ᵉ asᵉ itᵉ
ensuresᵉ thatᵉ theᵉ identificationᵉ usedᵉ in definingᵉ theᵉ rewriteᵉ ruleᵉ alsoᵉ computesᵉ
to `refl`.ᵉ Concretely,ᵉ ifᵉ theᵉ identificationᵉ `β`ᵉ definesᵉ aᵉ rewriteᵉ rule,ᵉ andᵉ `β`ᵉ
isᵉ definedᵉ viaᵉ `primEraseEqaulity`,ᵉ thenᵉ weᵉ haveᵉ theᵉ strictᵉ equalityᵉ `βᵉ ≐ᵉ refl`.ᵉ

## Primitives

```agda
primitive
  primEraseEqualityᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ yᵉ
```

## External links

-ᵉ [Built-ins#Equality](https://agda.readthedocs.io/en/latest/language/built-ins.html#equalityᵉ)
  atᵉ Agda'sᵉ documentationᵉ pagesᵉ
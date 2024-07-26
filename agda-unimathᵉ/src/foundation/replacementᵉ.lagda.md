# The type theoretic replacement axiom

```agda
module foundation.replacementᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.imagesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.small-typesᵉ
```

</details>

## Idea

Theᵉ **typeᵉ theoreticᵉ replacementᵉ axiom**ᵉ assertsᵉ thatᵉ theᵉ
[image](foundation.images.mdᵉ) ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ fromᵉ aᵉ
[smallᵉ type](foundation-core.small-types.mdᵉ) `A`ᵉ intoᵉ aᵉ
[locallyᵉ smallᵉ type](foundation.locally-small-types.mdᵉ) `B`ᵉ isᵉ small.ᵉ

## Statement

```agda
instance-replacementᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) →
  UUᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
instance-replacementᵉ lᵉ {Aᵉ = Aᵉ} {Bᵉ} fᵉ =
  is-smallᵉ lᵉ Aᵉ → is-locally-smallᵉ lᵉ Bᵉ → is-smallᵉ lᵉ (imᵉ fᵉ)

replacement-axiom-Levelᵉ : (lᵉ l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc lᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ)
replacement-axiom-Levelᵉ lᵉ l1ᵉ l2ᵉ =
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) → instance-replacementᵉ lᵉ fᵉ

replacement-axiomᵉ : UUωᵉ
replacement-axiomᵉ = {lᵉ l1ᵉ l2ᵉ : Level} → replacement-axiom-Levelᵉ lᵉ l1ᵉ l2ᵉ
```

## Postulate

```agda
postulate
  replacementᵉ : replacement-axiomᵉ
```

```agda
replacement'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-locally-smallᵉ l1ᵉ Bᵉ → is-smallᵉ l1ᵉ (imᵉ fᵉ)
replacement'ᵉ fᵉ = replacementᵉ fᵉ is-small'ᵉ
```

## References

-ᵉ Theoremᵉ 4.6ᵉ in {{#citeᵉ Rij17}}.ᵉ
-ᵉ Sectionᵉ 2.19ᵉ in {{#citeᵉ SymmetryBook}}.ᵉ

{{#bibliographyᵉ}}
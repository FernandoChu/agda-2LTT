# Lawvere's fixed point theorem

```agda
module foundation.lawveres-fixed-point-theoremᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

{{#conceptᵉ "Lawvere'sᵉ fixedᵉ pointᵉ theorem"ᵉ Agda=fixed-point-theorem-Lawvereᵉ}}
assertsᵉ thatᵉ ifᵉ thereᵉ isᵉ aᵉ [surjectiveᵉ map](foundation.surjective-maps.mdᵉ)
`Aᵉ → (Aᵉ → B)`,ᵉ thenᵉ anyᵉ mapᵉ `Bᵉ → B`ᵉ mustᵉ haveᵉ aᵉ fixedᵉ point.ᵉ

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Aᵉ → Bᵉ}
  where

  abstract
    fixed-point-theorem-Lawvereᵉ :
      is-surjectiveᵉ fᵉ → (hᵉ : Bᵉ → Bᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → hᵉ bᵉ ＝ᵉ bᵉ)
    fixed-point-theorem-Lawvereᵉ Hᵉ hᵉ =
      apply-universal-property-trunc-Propᵉ
        ( Hᵉ gᵉ)
        ( exists-structure-Propᵉ Bᵉ (λ bᵉ → hᵉ bᵉ ＝ᵉ bᵉ))
        ( λ (xᵉ ,ᵉ pᵉ) → intro-existsᵉ (fᵉ xᵉ xᵉ) (invᵉ (htpy-eqᵉ pᵉ xᵉ)))
      where
      gᵉ : Aᵉ → Bᵉ
      gᵉ aᵉ = hᵉ (fᵉ aᵉ aᵉ)
```
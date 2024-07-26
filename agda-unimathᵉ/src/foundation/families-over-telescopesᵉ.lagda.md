# Families of types over telescopes

```agda
module foundation.families-over-telescopesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.raising-universe-levelsᵉ
open import foundation.telescopesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "typeᵉ family"ᵉ Disambiguation="overᵉ aᵉ telescope"ᵉ Agda=family-over-telescopeᵉ}}
overᵉ aᵉ [telescope](foundation.telescopes.mdᵉ) isᵉ aᵉ familyᵉ ofᵉ typesᵉ definedᵉ in theᵉ
contextᵉ ofᵉ theᵉ telescope.ᵉ

Forᵉ instance,ᵉ givenᵉ aᵉ lengthᵉ threeᵉ telescopeᵉ

```text
  Γᵉ :=ᵉ ⟨xᵉ : A,ᵉ yᵉ : Bᵉ x,ᵉ zᵉ : Cᵉ xᵉ yᵉ z⟩ᵉ
```

aᵉ typeᵉ familyᵉ overᵉ `Γ`ᵉ isᵉ aᵉ ternaryᵉ familyᵉ ofᵉ typesᵉ

```text
  Dᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) (zᵉ : Cᵉ xᵉ yᵉ zᵉ) → 𝒰.ᵉ
```

## Definitions

### Type families over telescopes

```agda
family-over-telescopeᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) {nᵉ : ℕᵉ} → telescopeᵉ l1ᵉ nᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
family-over-telescopeᵉ {l1ᵉ} l2ᵉ (base-telescopeᵉ Xᵉ) =
  raiseᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (UUᵉ l2ᵉ)
family-over-telescopeᵉ l2ᵉ (cons-telescopeᵉ {Xᵉ = Xᵉ} Γᵉ) =
  (xᵉ : Xᵉ) → family-over-telescopeᵉ l2ᵉ (Γᵉ xᵉ)
```
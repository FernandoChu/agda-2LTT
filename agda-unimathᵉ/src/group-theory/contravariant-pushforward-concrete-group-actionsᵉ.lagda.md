# Contravariant pushforwards of concrete group actions

```agda
module group-theory.contravariant-pushforward-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
```

</details>

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ)
  where

{-ᵉ
  contravariant-pushforward-action-Concrete-Groupᵉ :
    {lᵉ : Level} → action-Concrete-Groupᵉ lᵉ Gᵉ → action-Concrete-Groupᵉ {!!ᵉ} Hᵉ
  contravariant-pushforward-action-Concrete-Groupᵉ Xᵉ yᵉ = {!!ᵉ}

    --ᵉ Theᵉ followingᵉ shouldᵉ beᵉ constructedᵉ asᵉ aᵉ setᵉ
    hom-action-Concrete-Groupᵉ Gᵉ Xᵉ
      ( subst-action-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ (λ yᵉ → Idᵉ (shape-Concrete-Groupᵉ Hᵉ) yᵉ))
      -ᵉ}
```
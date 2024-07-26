# Morphisms of cospan diagrams

```agda
module foundation.morphisms-cospan-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "morphismᵉ ofᵉ cospanᵉ diagrams"ᵉ Agda=hom-cospan-diagramᵉ}} isᵉ aᵉ
commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
  Aᵉ ----->ᵉ Xᵉ <-----ᵉ Bᵉ
  |        |        |
  |        |        |
  ∨ᵉ        ∨ᵉ        ∨ᵉ
  A'ᵉ ---->ᵉ X'ᵉ <----ᵉ B'.ᵉ
```

## Definitions

### Morphisms of cospan diagrams

```agda
hom-cospan-diagramᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l1'ᵉ ⊔ l2'ᵉ ⊔ l3'ᵉ)
hom-cospan-diagramᵉ {Aᵉ = Aᵉ} {Bᵉ} {Xᵉ} fᵉ gᵉ {A'ᵉ} {B'ᵉ} {X'ᵉ} f'ᵉ g'ᵉ =
  Σᵉ ( Aᵉ → A'ᵉ)
    ( λ hAᵉ →
      Σᵉ ( Bᵉ → B'ᵉ)
        ( λ hBᵉ →
          Σᵉ ( Xᵉ → X'ᵉ)
            ( λ hXᵉ → (f'ᵉ ∘ᵉ hAᵉ ~ᵉ hXᵉ ∘ᵉ fᵉ) ×ᵉ (g'ᵉ ∘ᵉ hBᵉ ~ᵉ hXᵉ ∘ᵉ gᵉ))))
```

### Identity morphisms of cospan diagrams

```agda
id-hom-cospan-diagramᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) →
  hom-cospan-diagramᵉ fᵉ gᵉ fᵉ gᵉ
pr1ᵉ (id-hom-cospan-diagramᵉ fᵉ gᵉ) = idᵉ
pr1ᵉ (pr2ᵉ (id-hom-cospan-diagramᵉ fᵉ gᵉ)) = idᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (id-hom-cospan-diagramᵉ fᵉ gᵉ))) = idᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (id-hom-cospan-diagramᵉ fᵉ gᵉ)))) = refl-htpyᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (id-hom-cospan-diagramᵉ fᵉ gᵉ)))) = refl-htpyᵉ
```

### Rotating cospan diagrams of cospan diagrams

```agda
cospan-hom-cospan-diagram-rotateᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l1''ᵉ l2''ᵉ l3''ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  {A''ᵉ : UUᵉ l1''ᵉ} {B''ᵉ : UUᵉ l2''ᵉ} {X''ᵉ : UUᵉ l3''ᵉ}
  (f''ᵉ : A''ᵉ → X''ᵉ) (g''ᵉ : B''ᵉ → X''ᵉ)
  (hᵉ : hom-cospan-diagramᵉ f'ᵉ g'ᵉ fᵉ gᵉ) (h'ᵉ : hom-cospan-diagramᵉ f''ᵉ g''ᵉ fᵉ gᵉ) →
  hom-cospan-diagramᵉ (pr1ᵉ hᵉ) (pr1ᵉ h'ᵉ) (pr1ᵉ (pr2ᵉ (pr2ᵉ hᵉ))) (pr1ᵉ (pr2ᵉ (pr2ᵉ h'ᵉ)))
pr1ᵉ
  ( cospan-hom-cospan-diagram-rotateᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
    ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
    ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ)) = f'ᵉ
pr1ᵉ
  ( pr2ᵉ
    ( cospan-hom-cospan-diagram-rotateᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
      ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
      ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ))) = f''ᵉ
pr1ᵉ
  ( pr2ᵉ
    ( pr2ᵉ
      ( cospan-hom-cospan-diagram-rotateᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
        ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
        ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ)))) = fᵉ
pr1ᵉ
  ( pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ
        ( cospan-hom-cospan-diagram-rotateᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
          ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
          ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ))))) = inv-htpyᵉ HAᵉ
pr2ᵉ
  ( pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ
        ( cospan-hom-cospan-diagram-rotateᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
          ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
          ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ))))) = inv-htpyᵉ HA'ᵉ

cospan-hom-cospan-diagram-rotate'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l1''ᵉ l2''ᵉ l3''ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  {A''ᵉ : UUᵉ l1''ᵉ} {B''ᵉ : UUᵉ l2''ᵉ} {X''ᵉ : UUᵉ l3''ᵉ}
  (f''ᵉ : A''ᵉ → X''ᵉ) (g''ᵉ : B''ᵉ → X''ᵉ)
  (hᵉ : hom-cospan-diagramᵉ f'ᵉ g'ᵉ fᵉ gᵉ) (h'ᵉ : hom-cospan-diagramᵉ f''ᵉ g''ᵉ fᵉ gᵉ) →
  hom-cospan-diagramᵉ
    (pr1ᵉ (pr2ᵉ hᵉ)) (pr1ᵉ (pr2ᵉ h'ᵉ)) (pr1ᵉ (pr2ᵉ (pr2ᵉ hᵉ))) (pr1ᵉ (pr2ᵉ (pr2ᵉ h'ᵉ)))
pr1ᵉ
  ( cospan-hom-cospan-diagram-rotate'ᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
    ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
    ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ)) = g'ᵉ
pr1ᵉ
  ( pr2ᵉ
    ( cospan-hom-cospan-diagram-rotate'ᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
      ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
      ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ))) = g''ᵉ
pr1ᵉ
  ( pr2ᵉ
    ( pr2ᵉ
      ( cospan-hom-cospan-diagram-rotate'ᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
        ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
        ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ)))) = gᵉ
pr1ᵉ
  ( pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ
        ( cospan-hom-cospan-diagram-rotate'ᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
          ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
          ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ))))) = inv-htpyᵉ HBᵉ
pr2ᵉ
  ( pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ
        ( cospan-hom-cospan-diagram-rotate'ᵉ fᵉ gᵉ f'ᵉ g'ᵉ f''ᵉ g''ᵉ
          ( hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ)
          ( hA'ᵉ ,ᵉ hB'ᵉ ,ᵉ hX'ᵉ ,ᵉ HA'ᵉ ,ᵉ HB'ᵉ))))) = inv-htpyᵉ HB'ᵉ
```
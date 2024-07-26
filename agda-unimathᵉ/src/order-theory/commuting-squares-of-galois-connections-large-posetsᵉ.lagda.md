# Commuting squares of Galois connections between large posets

```agda
module order-theory.commuting-squares-of-galois-connections-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import order-theory.commuting-squares-of-order-preserving-maps-large-posetsᵉ
open import order-theory.galois-connections-large-posetsᵉ
open import order-theory.large-posetsᵉ
```

</details>

## Idea

Considerᵉ aᵉ diagramᵉ ofᵉ
[Galoisᵉ connections](order-theory.galois-connections-large-posets.mdᵉ)

```text
           LIᵉ
        ------->ᵉ
      Pᵉ     ⊥ᵉ    Uᵉ
     |  <-------ᵉ
     | ∧ᵉ   UIᵉ   | ∧ᵉ
     | |        | |
  LFᵉ | |     LGᵉ | |
     |⊣|ᵉ UFᵉ     |⊣|ᵉ UGᵉ
     | |        | |
     ∨ᵉ |   LJᵉ   ∨ᵉ |
        ------->ᵉ  |
      Qᵉ     ⊥ᵉ    V.ᵉ
        <-------ᵉ
           UJᵉ
```

betweenᵉ [largeᵉ posets](order-theory.large-posets.md).ᵉ Weᵉ sayᵉ thatᵉ theᵉ diagramᵉ
**commutes**ᵉ ifᵉ thereᵉ isᵉ aᵉ
[similarity](order-theory.similarity-of-order-preserving-maps-large-posets.mdᵉ)
`LJᵉ ∘ᵉ LFᵉ ≈ᵉ LGᵉ ∘ᵉ LI`.ᵉ Thisᵉ conditionᵉ isᵉ
[equivalent](foundation.logical-equivalences.mdᵉ) theᵉ conditionᵉ thatᵉ thereᵉ isᵉ aᵉ
similarityᵉ `UFᵉ ∘ᵉ UJᵉ ≈ᵉ UIᵉ ∘ᵉ UG`.ᵉ

## Definitions

### Commuting squares of Galois connections

```agda
module _
  {αPᵉ αQᵉ αUᵉ αVᵉ γFᵉ γGᵉ γIᵉ γJᵉ δFᵉ δGᵉ δIᵉ δJᵉ : Level → Level}
  {βPᵉ βQᵉ βUᵉ βVᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Uᵉ : Large-Posetᵉ αUᵉ βUᵉ)
  (Vᵉ : Large-Posetᵉ αVᵉ βVᵉ)
  (Iᵉ : galois-connection-Large-Posetᵉ γIᵉ δIᵉ Pᵉ Uᵉ)
  (Fᵉ : galois-connection-Large-Posetᵉ γFᵉ δFᵉ Pᵉ Qᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γGᵉ δGᵉ Uᵉ Vᵉ)
  (Jᵉ : galois-connection-Large-Posetᵉ γJᵉ δJᵉ Qᵉ Vᵉ)
  where

  lower-coherence-square-galois-connection-Large-Posetᵉ : UUωᵉ
  lower-coherence-square-galois-connection-Large-Posetᵉ =
    lower-sim-galois-connection-Large-Posetᵉ Pᵉ Vᵉ
      ( comp-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Vᵉ Jᵉ Fᵉ)
      ( comp-galois-connection-Large-Posetᵉ Pᵉ Uᵉ Vᵉ Gᵉ Iᵉ)

  upper-coherence-square-galois-connection-Large-Posetᵉ : UUωᵉ
  upper-coherence-square-galois-connection-Large-Posetᵉ =
    upper-sim-galois-connection-Large-Posetᵉ Pᵉ Vᵉ
      ( comp-galois-connection-Large-Posetᵉ Pᵉ Uᵉ Vᵉ Gᵉ Iᵉ)
      ( comp-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Vᵉ Jᵉ Fᵉ)
```

## Properties

### A commuting square of lower adjoints of galois connections induces a commuting square of upper adjoints and vice versa

```agda
module _
  {αPᵉ αQᵉ αUᵉ αVᵉ γFᵉ γGᵉ γIᵉ γJᵉ δFᵉ δGᵉ δIᵉ δJᵉ : Level → Level}
  {βPᵉ βQᵉ βUᵉ βVᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Uᵉ : Large-Posetᵉ αUᵉ βUᵉ)
  (Vᵉ : Large-Posetᵉ αVᵉ βVᵉ)
  (Iᵉ : galois-connection-Large-Posetᵉ γIᵉ δIᵉ Pᵉ Uᵉ)
  (Fᵉ : galois-connection-Large-Posetᵉ γFᵉ δFᵉ Pᵉ Qᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γGᵉ δGᵉ Uᵉ Vᵉ)
  (Jᵉ : galois-connection-Large-Posetᵉ γJᵉ δJᵉ Qᵉ Vᵉ)
  where

  lower-coherence-square-upper-coherence-square-galois-connection-Large-Posetᵉ :
    upper-coherence-square-galois-connection-Large-Posetᵉ
      Pᵉ Qᵉ Uᵉ Vᵉ Iᵉ Fᵉ Gᵉ Jᵉ →
    lower-coherence-square-galois-connection-Large-Posetᵉ
      Pᵉ Qᵉ Uᵉ Vᵉ Iᵉ Fᵉ Gᵉ Jᵉ
  lower-coherence-square-upper-coherence-square-galois-connection-Large-Posetᵉ =
    lower-sim-upper-sim-galois-connection-Large-Posetᵉ Pᵉ Vᵉ
      ( comp-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Vᵉ Jᵉ Fᵉ)
      ( comp-galois-connection-Large-Posetᵉ Pᵉ Uᵉ Vᵉ Gᵉ Iᵉ)

  upper-coherence-square-lower-coherence-square-galois-connection-Large-Posetᵉ :
    lower-coherence-square-galois-connection-Large-Posetᵉ
      Pᵉ Qᵉ Uᵉ Vᵉ Iᵉ Fᵉ Gᵉ Jᵉ →
    upper-coherence-square-galois-connection-Large-Posetᵉ
      Pᵉ Qᵉ Uᵉ Vᵉ Iᵉ Fᵉ Gᵉ Jᵉ
  upper-coherence-square-lower-coherence-square-galois-connection-Large-Posetᵉ =
    upper-sim-lower-sim-galois-connection-Large-Posetᵉ Pᵉ Vᵉ
      ( comp-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Vᵉ Jᵉ Fᵉ)
      ( comp-galois-connection-Large-Posetᵉ Pᵉ Uᵉ Vᵉ Gᵉ Iᵉ)
```
# Diagonals of morphisms of arrows

```agda
module foundation.diagonals-of-morphisms-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Theᵉ {{#conceptᵉ "diagonal"ᵉ Disambiguation="morphismᵉ ofᵉ arrows"ᵉ}} ofᵉ aᵉ
[morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

isᵉ obtainedᵉ byᵉ takingᵉ theᵉ [diagonals](foundation.diagonals-of-maps.mdᵉ) ofᵉ theᵉ
mapsᵉ `i`ᵉ andᵉ `j`,ᵉ whichᵉ fitᵉ in aᵉ naturalityᵉ squareᵉ

```text
       Δᵉ iᵉ
    Aᵉ ----->ᵉ Aᵉ ×_Xᵉ Aᵉ
    |           |
  fᵉ |           | functorialityᵉ Δᵉ gᵉ
    ∨ᵉ           ∨ᵉ
    Bᵉ ----->ᵉ Bᵉ ×_Yᵉ B.ᵉ
       Δᵉ jᵉ
```

Inᵉ otherᵉ words,ᵉ theᵉ diagonalᵉ ofᵉ aᵉ morphismᵉ ofᵉ arrowsᵉ `hᵉ : hom-arrowᵉ fᵉ g`ᵉ isᵉ aᵉ
morphismᵉ ofᵉ arrowsᵉ `Δᵉ hᵉ : hom-arrowᵉ fᵉ (functorialityᵉ Δᵉ g).ᵉ

Noteᵉ thatᵉ thisᵉ operationᵉ preservesᵉ
[cartesianᵉ squares](foundation.cartesian-morphisms-arrows.md).ᵉ Furthermore,ᵉ byᵉ aᵉ
lemmaᵉ ofᵉ [Davidᵉ Wärn](https://ncatlab.org/nlab/show/David+Wärnᵉ) itᵉ alsoᵉ followsᵉ
thatᵉ thisᵉ operationᵉ perservesᵉ
[cocartesianᵉ morphismsᵉ ofᵉ arrows](synthetic-homotopy-theory.cocartesian-morphisms-arrows.mdᵉ)
outᵉ ofᵉ [embeddings](foundation.embeddings.md).ᵉ
# agda-2LTT

WIP of 2LTT using the [agda-unimath](https://github.com/UniMath/agda-unimath)
library.

## Installation

Clone the repo

```
$ git clone --recurse-submodules git@github.com:FernandoChu/agda-2LTT.git
```

And run the 2ltt script from the root of the folder

```
$ python3 ./scripts/unimath-to-2ltt.py 
```

## Formalization notes

We allow ourselves to use `Σ` and `Π` types mixing both the inner and outer level, despite this not being considered in the original paper. This could be understood as an implicit coercion of the inner types.

Some definitions, such as being cofibrant or sharp, require some data about fibrant types. When it makes sense, we will instead change the definition to be about (not-necessarily coerced) inner types.
This is because of our first convention above, plus our assumption of axiom T3.

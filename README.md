# Agda

This repository contains an Agda formalisation of the Introduction to Homotopy Type Theory book by Egbert Rijke. 

## Organisation

There is one file per section in the book, and the formalization follows the book in a linear fashion. As far as we can, we make sure that numbering in the book of definitions, lemmas, theorems, etc, corresponds to numbering in the formal development.

## Conventions

* Most commonly, we use all lowercase names where words are separated by hyphens.
* Structure on the natural numbers has `ℕ` at the end of its name. For example, we have `zero-ℕ`, `one-ℕ`, `succ-ℕ`, `add-ℕ`, `mul-ℕ`. We only use `ℕ` once at the end of a name. For instance, the fact that multiplication distributes from the left over addition is called `left-distributive-mul-add-ℕ`. Similar for structure on the integers, the finite sets, the rationals, and so on.
* Capitalization is used at the end of a name if we want to specify the category in which we are working. For example `hom-Group` is the type of group homomorphisms between any two groups, and `ℤ-Group` is the object `ℤ` seen as a group.
* In the naming scheme, the conclusion comes first, followed by the assumptions. For example, `is-contr-map-is-equiv` is the theorem that concludes that a map is contractible if it is an equivalence. Another example, `type-Group` is the underlying type of a group.

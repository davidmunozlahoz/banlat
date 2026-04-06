# Dependency Graph

```
                         Basic
                        / | \
                       /  |  \
               Sublattice |  Normed        Operators.Hom     OrderComplete
                    \      |   / \              / |               |
                     \     |  /   \            /  |               |
                      Ideal      Banach ------'   |               |
                     / | \      / |  \            |               |
                    /  |  \    /  |   \           |               |
                Band   | ALSpace |  Operators.Positive            |
                 /|    |         |       |                        |
              Atom |   |         |       |                        |
                   |   |         |       |                        |
          OrderContinuous     AMSpace    |                        |
                            /       \   Operators.OrderBounded    |
                     Examples.Lp  Examples.CofK   |    \         |
                                       |          |     \        |
                                Examples.MofK     |      \       |
                                       |          | Operators.RieszKantorovich
                          Preliminaries.SignedMeasure  /          |
                                                  |  /           |
                                         Operators.Regular------'
```

## Edges

| Module                     | Imports                              |
|----------------------------|--------------------------------------|
| Basic                      | _(none within BanLat)_               |
| Sublattice                 | Basic                                |
| Normed                     | Basic                                |
| Operators.Hom              | Basic                                |
| OrderComplete              | Basic                                |
| Ideal                      | Sublattice, Normed                   |
| Banach                     | Normed, Operators.Hom                |
| Band                       | Ideal, Operators.Hom                 |
| Atom                       | Band                                 |
| ALSpace                    | Banach, Ideal                        |
| AMSpace                    | Banach, Ideal                        |
| Quotient                   | Ideal, Operators.Hom, Banach         |
| Operators.Positive         | Banach                               |
| Operators.OrderBounded     | Operators.Positive                   |
| Operators.Regular          | Operators.OrderBounded, Operators.RieszKantorovich, OrderComplete|
| Operators.RieszKantorovich | Operators.OrderBounded, OrderComplete|
| Dual                       | Operators.Regular, Operators.RieszKantorovich |
| OrderContinuous            | Banach, Band                         |
| Preliminaries.SignedMeasure| _(none within BanLat)_               |
| Examples.MofK              | Banach, Preliminaries.SignedMeasure  |
| Examples.CofK              | AMSpace, Dual, Examples.MofK         |
| Examples.Lp                | AMSpace                              |

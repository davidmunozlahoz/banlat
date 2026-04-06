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
                  |    |         |       |                        |
          OrderContinuous     AMSpace    |                        |
                            /       \   Operators.OrderBounded    |
                     Examples.Lp  Examples.CofK   |    \         |
                                                  |     \        |
                                                  |      \       |
                                                  | Operators.RieszKantorovich
                                                  |      /       |
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
| ALSpace                    | Banach, Ideal                        |
| AMSpace                    | Banach, Ideal                        |
| Quotient                   | Ideal, Operators.Hom, Banach         |
| Operators.Positive         | Banach                               |
| Operators.OrderBounded     | Operators.Positive                   |
| Operators.Regular          | Operators.OrderBounded, Operators.RieszKantorovich, OrderComplete|
| Operators.RieszKantorovich | Operators.OrderBounded, OrderComplete|
| Dual                       | Operators.Regular, Operators.RieszKantorovich |
| OrderContinuous            | Banach, Band                         |
| Examples.CofK              | AMSpace                              |
| Examples.Lp                | AMSpace                              |

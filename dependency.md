# Dependency Graph

```
                         Basic
                        / | \
                       /  |  \
               Sublattice |  Normed        Operators.Hom     OrderComplete
                    \      |   / \              / |               |
                     \     |  /   \            /  |               |
                      Ideal      Banach ------'   |               |
                     / |        / |  \            |               |
                    /  |       /  |   \           |               |
                Band   |      /   |  Operators.Positive           |
                 /|    |     /    |       |                       |
              Atom |   |    /     |       |                       |
                   |   |   /      |       |                       |
          OrderContinuous AMSpace |  Operators.OrderBounded       |
                       \    |  \  |       |    \                  |
                        \   |   \ |       |     \                 |
                         \  |  Examples.Lp|      \                |
                          \ |             | Operators.RieszKantorovich
                           \|             |    /                  |
                            |    Operators.Regular ---------------'
                            |             |
                            |            Dual
                            |           / | \
                            |          /  |  \
                          ALSpace ----'   | Bidual
                                          |
                                Examples.CofK
                                          |
                                Examples.MofK
                                          |
                       Preliminaries.SignedMeasure
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
| ALSpace                    | AMSpace, Banach, Dual, Ideal, OrderContinuous |
| AMSpace                    | Banach, Ideal                        |
| Quotient                   | Ideal, Operators.Hom, Banach         |
| Operators.Positive         | Banach                               |
| Operators.OrderBounded     | Operators.Positive                   |
| Operators.Regular          | Operators.OrderBounded, Operators.RieszKantorovich, OrderComplete|
| Operators.RieszKantorovich | Operators.OrderBounded, OrderComplete|
| Dual                       | Operators.Regular, Operators.RieszKantorovich |
| Bidual                     | Dual                                 |
| OrderContinuous            | Banach, Band, OrderComplete          |
| Preliminaries.SignedMeasure| _(none within BanLat)_               |
| Examples.MofK              | Banach, Preliminaries.SignedMeasure  |
| Examples.CofK              | AMSpace, Dual, Examples.MofK         |
| Examples.Lp                | AMSpace                              |
| Pi                         | ALSpace, AMSpace, Banach             |
| Kakutani                   | AMSpace, Examples.CofK               |

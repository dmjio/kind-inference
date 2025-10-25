kind-inference
===================

Type and kind inference for Haskell98 using HM(x) constraint solving.

This project provides an AST of Haskell98 and performs both kind and type inference through elaboration and solving of equality constraints using metavariables and an HM(x) framework.

For more information on HM(x) see page 422 of [Advanced Topics in Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/attapl/frontmatter.pdf) and the original [The Essence of ML Type Inference](https://gallium.inria.fr/~fpottier/publis/emlti-final.pdf).

## Run

```bash
$ nix-shell -p ghc --run 'runghc Main.hs'
```

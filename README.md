networkdesign
====
[![Build Status](https://app.travis-ci.com/44534/networkdesign.svg?token=x2S1pLSLXWsyktpey5Ua&branch=master)](https://travis-ci.org/44534/networkdesign)

Enumeration of instances to find lower bounds on the Price of Stability in broadcast games using an SMT solver.

Features
----

* Find the highest lower bound on the PoS for a given class by complete enumeration of all instances
* Find all instances of a given class achieving a given value of the PoS
* Find lower bounds on the PoS for a given class by evolutionary search


Installation
---

```
stack install
```

The following SMT solvers have to be installed separately and be available in `$PATH` with the given names:

* [opensmt](http://verify.inf.usi.ch/opensmt) - opensmt
* [z3](https://github.com/Z3Prover/z3) - z3
* [cvc4](https://cvc4.github.io/) - cvc4
* [yices](https://yices.csl.sri.com/) - yices-smt2


Options
----

Suppported options are:
```
> networkdesign --help

Enumeration of instances to find lower bounds on the Price of Stability in
broadcast games using an SMT solver.

Usage: networkdesign ((--enum | --find)
                       (--all NrNodes | --path NrNodes | --disj NrNodes |
                         --star NrNodes | --wheel NrNodes | --cube DIM |
                         --twopaths NrNodes | --fof-b NrNodes --fof-t NrNodes |
                         --bintree HEIGHT | --grid-w WIDTH --grid-h HEIGHT)
                       (-b|--backend NAME) [-c|--cores NR] --start VALUE
                       (-s|--step ARG) [--complete] (--pos | --poa)
                       [--normalize] [--continue] [--debug FILENAME]
                       [--showsystems FILENAME] |
                       (--random | --ring | --fan | (-w|--width ARG)
                         (-h|--height ARG)) (-n|--nrNodes ARG) (-s|--startN ARG)
                       (-k|--keepN ARG) (-m|--measure pos | gnene) |
                       (--qbip-2fan ARG | --qbip-fan3fans ARG |
                         --qbip-italian ARG) (-b|--backend ARG) (-s|--step ARG))
                     (--fair | --harmonic | --sharing2 ARG --sharingslope ARG |
                       --power A) [--no-prettyprint]
  networkdesign

Available options:
  -h,--help                Show this help text
  --enum                   enumerate all instances trying to find the highest
                           PoS
  --find                   find all instances that achieve a given value for the
                           PoS
  --all NrNodes            all pairs of trees with NrNodes nodes are considered
                           for OPT and NE
  --path NrNodes           OPT is fixed to be a path of length NrNodes having
                           the root as one endpoint
  --disj NrNodes           only edge-disjoint trees with NrNodes nodes are
                           considered for OPT and NE
  --star NrNodes           NE is fixed to be the star with the root as center
                           and NrNodes nodes
  --wheel NrNodes          the underlying graph is the wheel with NrNodes nodes
  --cube DIM               the underlying graph is the DIM-dimensional cube
  --twopaths NrNodes       OPT is the path 1-...-NrNodes, all other paths are
                           considered as NE
  --fof-b NrNodes          size of each fan in the second level
  --fof-t NrNodes          nr of nodes in the first level
  --bintree HEIGHT         NE is fixed to be the complete binary tree of height
                           HEIGHT, OPTs consist of the level paths with all
                           possible connections
  --grid-w WIDTH           the underlying graph is the WIDTH x HEIGHT grid
  --grid-h HEIGHT          the underlying graph is the WIDTH x HEIGHT grid
  -b,--backend NAME        the smt solver to be used, currently available
                           options: z3, cvc4, opensmt, yices
  -c,--cores NR            the number of parallel computations to be done,
                           waiting for all to finish. This has to be combined
                           with the "+RTS" option
  --start VALUE            A lower bound on the PoS. Resulting instances will
                           have PoS > VALUE.
  -s,--step ARG            The value to increment the ratio in each step when
                           enumerating. Has no affect for "--find".
  --complete               Whether to consider the complete graph or just the
                           union of OPT and NE tree (default). Relevant only for
                           --all, --path and --star.
  --pos                    whether to consider the PoS ...
  --poa                    ... or PoA
  --normalize              whether to normalize the social cost of OPT to 1
  --continue               run forever increasing NrNodes
  --debug FILENAME         verbose output and saves times in FILENAME.
  --showsystems FILENAME   Save systems sent to solver in FILE
  --random                 evolution of random instances. Every edge of the
                           complete graph gets a random weight between 0 and
                           nrNodes.
  --ring                   evolution of random ring instances.
  --fan                    evolution of random fan instance.
  -h,--height ARG          evolution of random w x h grid instances.
  -n,--nrNodes ARG         number of nodes of the instances. Has no effect on
                           grid instances.
  -s,--startN ARG          the number of individuals in the initial population
  -k,--keepN ARG           the number of individuals to keep in each generation
  -m,--measure pos | gnene the evaluation function. Either PoS or C(best
                           NE)/C(best go-it-alone NE)
  --fair                   fair cost sharing f(k) = 1/k
  --harmonic               f(k) = H(k) / k
  --sharing2 ARG           the value of 2f(2)
  --sharingslope ARG       the slope of kf(k). f(1) = 1, f(2) = sharing2 / 2,
                           f(k) = (sharing2 + slope * (k-2)) / k
  --power A                f(k) = k^(A-1)
  --no-prettyprint         turn off pretty print

```

Example call:
```
networkdesign --enum --all 4 --complete -b opensmt --start 1 --pos --fair --normalize -s 0.001 -c 4 +RTS -N2
```
This enumerates all instances in the complete graph with 4 nodes (`--enum --all 4 --complete`) and fair cost allocation (`--fair`).
It finds lower bounds on the PoS (`--pos`) starting at 1 (`--start 1`) with a step size of 0.001 (`-s 0.001`).
We normalize the social cost of the optimum tree to 1 (`--normalize`).
opensmt is used as SMT solver (`-b opensmt`) and we split the instances in groups of 4 (`-c 4`) to be handled in parallel.

The output shows the progress of the enumeration.
```
4

opt: 1 [ 2 [ 3 ] , 4 ]
(1.33255103,(1 [ 2 , 4 [ 3 ] ],[ ({1,2},0.66568878) , ({1,3},0.66715560) , ({1,4},0.0) , ({2,3},0.33431121) , ({2,4},0.66568878) , ({3,4},0.66700892) ]))
(1.33255103,(1 [ 4 [ 2 , 3 ] ],[ ({1,2},0.66568878) , ({1,3},0.66700892) , ({1,4},0.0) , ({2,3},0.33431121) , ({2,4},0.66568878) , ({3,4},0.66700892) ]))

opt: 1 [ 2 [ 3 , 4 ] ]
(1.38444283,(1 [ 2 , 3 , 4 ],[ ({1,2},0.46148652) , ({1,3},0.46148652) , ({1,4},0.46148652) , ({2,3},0.23076000) , ({2,4},0.30775347) , ({3,4},0.30775347) ]))

opt: 1 [ 2 [ 3 [ 4 ] ] ]
(1.48485115,(1 [ 2 , 3 , 4 ],[ ({1,2},0.45662925) , ({1,3},0.51373264) , ({1,4},0.51455520) , ({2,3},0.28545100) , ({2,4},0.36236744) , ({3,4},0.25791974) ]))

opt: 1 [ 2 , 3 , 4 ]
--------
(1.48485115,(1 [ 2 [ 3 [ 4 ] ] ],(1 [ 2 , 3 , 4 ],[ ({1,2},0.45662925) , ({1,3},0.51373264) , ({1,4},0.51455520) , ({2,3},0.28545100) , ({2,4},0.36236744) , ({3,4},0.25791974) ])))
```
The instances are grouped by the optimum tree.
For each optimum tree a new line is printed, if there is an ne tree with a higher lower bound on the PoS.
These lines are of the form
`(lower bound, (ne tree, scaling factors on the edges ))`.
After the complete enumeration the highest lower bound is printed after `--------` in the format `(lower bound, (opt tree, (ne tree, scaling factors)))`.
Trees are given recursively by `node label [list of subtrees]` for example:
```
1 [ 2 [ 3 [ 4 ] ] ] and 1 [ 2 , 3 , 4 ] correspond to
  1                         1
 /                         /|\
2-3-4                     2 3 4
```

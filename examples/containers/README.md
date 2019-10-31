This directory contains the Coq representation of Haskell's `containers`
library, as well as our specifications and proofs.

Our ICFP'18 paper ["Ready, set, verify! applying hs-to-coq to real-world Haskell
code (experience report)"](https://dl.acm.org/citation.cfm?id=3236784) and its
[extended version](https://arxiv.org/abs/1803.06960) describe the verification
of the this library.

The most important components of this work are in the `lib` and `theories`
directories:
* `lib` contains the pre-translated Coq representation of Haskell's `containers`
  library.
* `theories` contains our specifications and proofs for `containers` library. A
  more detailed documentation about it can be found [here](theories/README.md).

You do not need to compile the `hs-to-coq` tool to compile files in the above
directories, but you will need Coq 8.8.1 and the ssreflect plugin.

You can regenerate file in the `lib` directory yourself by running `make clean;
make` from this directory (you will need to compile the `hs-to-coq` tool for
doing that, for detailed instructions check [here](../../README.md)).

Other notable components in this directories are:
* the `edits` file and the `module-edits` directory (organized in the same
  structure as the `lib` directory) record all the edits we make for the
  translation.
* `manual` contains all the manually translated modules.
* `hs-spec` contains all the properties we translated from Haskell's
  QuickCheck properties.
* `extraction` contains the extraction of our translation back to Haskell.

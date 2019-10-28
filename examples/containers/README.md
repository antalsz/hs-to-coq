This directory contains the Coq representation of Haskell's
`containers` library, as well as our specifications and proofs.

Our ICFP'18 paper ["Ready, set, verify! applying hs-to-coq to
real-world Haskell code (experience
report)"](https://dl.acm.org/citation.cfm?id=3236784) and its
[extended version](https://arxiv.org/abs/1803.06960) describe the
verification of the this library.

The most important components of this work are in the `lib` and
`theories` directories:
* `lib` contains the pre-translated Coq representation of Haskell's
  `containers` library. Running `make` from here will reproduce the
  exactly same translated code in the `lib` directory, provided that
  you have the proper git submodule downloaded.
* `theories` contains our specifications and proofs for `containers`
  library. A more detailed documentation about it can be found
  [here](theories/README.md).

Other notable components:
* the `edits` file and the `module-edits` directory (organized in the
  same structure as the `lib` directory) record all the edits we make
  for the translation.
* `manual` contains all the manually translated modules.
* `hs-spec` contains all the properties we translated from Haskell's
  QuickCheck properties.
* `extraction` contains the extraction of our translation back to
  Haskell.

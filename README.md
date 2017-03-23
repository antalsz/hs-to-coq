# hs-to-coq

This repository contains a converter from Haskell code to equivalent Coq code,
as part of the [CoreSpec] component of the [DeepSpec] project.

There are two projects in this repository:

1. `hs-to-coq`: The aforementioned converter.  In fairly good shape.

2. `dummy-plugin`: A GHC plugin that connects the re-extracted converted code
   back into GHC, allowing us to run Haskell programs against
   verified/verifiable code.  Currently does not work.

[CoreSpec]: http://www.deepspec.org/research/Haskell/
[DeepSpec]: http://www.deepspec.org/


# How to use this file:
#
# To work on the Coq code related to hs-to-coq:
#   nix-shell -A coqPackages.hs-to-coq
#
# To build the hs-to-coq utility:
#   nix-build -A haskellPackages.hs-to-coq
# After building, you can run result/bin/hs-to-coq

{ coqPackages ? "coqPackages_8_8"
, ghcVersion  ? "ghc882"

, rev    ? "1fe82110febdf005d97b2927610ee854a38a8f26"
, sha256 ? "08x6saa7iljyq2m0j6p9phy0v17r3p8l7vklv7y7gvhdc7a85ppi"

, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let
  coqPackages' = pkgs.${coqPackages} // {
    hs-to-coq = with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
      name = "coq${coq.coq-version}-hs-to-coq-${version}";
      version = "1.0";

      src =
        if pkgs.lib.inNixShell
        then null
        else if pkgs ? coqFilterSource
             then pkgs.coqFilterSource [] ./.
             else ./.;

      buildInputs = [
        coq coq.ocaml coq.camlp5 coq.findlib mathcomp
      ];
      enableParallelBuilding = true;

      buildPhase = "make -j$NIX_BUILD_CORES";
      preBuild = "coq_makefile -f _CoqProject -o Makefile";
      installPhase = "mkdir -p $out";
      # installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

      env = pkgs.buildEnv { name = name; paths = buildInputs; };
      passthru = {
        compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
     };
    };
  };

  haskellPackages' = pkgs.haskell.packages.${ghcVersion} // {
    hs-to-coq =
      with pkgs.haskell.lib;
      with pkgs.haskell.packages.${ghcVersion}.override {
        overrides = self: super: {
          tasty      = doJailbreak super.tasty;
          indents    = doJailbreak super.indents;
          validation = doJailbreak super.validation;
        };
      };
      callCabal2nix "hs-to-coq" ./. {};
  };

in {
  coqPackages = coqPackages';
  haskellPackages = haskellPackages';
}

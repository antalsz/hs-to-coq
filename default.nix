{ nixpkgs ? import <nixpkgs> {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let inherit (nixpkgs) pkgs;
in with pkgs.coqPackages_8_8; pkgs.stdenv.mkDerivation rec {
  name        = "hs-to-coq";
  version     = "1.0";
  src         = if pkgs.lib.inNixShell then null else ./.;
  buildInputs = [ coq mathcomp ];
  env         = pkgs.buildEnv { name = name; paths = buildInputs; };
}

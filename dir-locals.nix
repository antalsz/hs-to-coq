let pkgs = import <nixpkgs> {};
project = pkgs.callPackage ./. {}; in
pkgs.nixBufferBuilders.withPackages (project.buildInputs)

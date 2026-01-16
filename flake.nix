{
  description = "FM";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/release-25.11";
    flake-parts.url = "github:hercules-ci/flake-parts";
    flake-utils.url = "github:numtide/flake-utils";
    revealjs = {
      url = "github:hakimel/reveal.js";
      flake = false;
    };
    mathjax = {
      url = "github:mathjax/mathjax";
      flake = false;
    };
    plantumlC4 = {
      url = "github:plantuml-stdlib/c4-plantuml";
      flake = false;
    };
    plantumlEIP = {
      url = "github:plantuml-stdlib/EIP-PlantUML";
      flake = false;
    };
    decktape = {
      url = "github:astefanutti/decktape";
      flake = false;
    };
  };

  outputs =
    inputs@{
      self,
      flake-parts,
      flake-utils,
      nixpkgs,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
        "aarch64-linux"
      ];
      perSystem =
        { system, self', ... }:
        let
          # Pin GHC version for easier, explicit upgrades later
          ghcVersion = "9122";
          legacyPackages = nixpkgs.legacyPackages.${system};
          makePkgs =
            nixpkgsImport:
            import nixpkgsImport {
              inherit system;
              config.allowUnfree = true;
              overlays = [
                (
                  final: prev:
                  let
                    hlib = final.haskell.lib.compose;
                  in
                  {
                    haskellPackages = prev.haskell.packages."ghc${ghcVersion}".override (old: {
                      overrides = final.lib.composeExtensions (old.overrides or (_: _: { })) (
                        hfinal: hprev: {
                          store = hlib.dontCheck hprev.store;
                          liquidhaskell-boot = hprev.liquidhaskell-boot_0_9_12_2;
                          liquid-fixpoint = hlib.dontCheck hprev.liquid-fixpoint_0_9_6_3_3;
                          liquidhaskell = hlib.overrideCabal (drv: { doHaddock = false; }) hprev.liquidhaskell_0_9_12_2;
                        }
                      );
                    });
                    z3 = prev.z3.overrideAttrs (oldAttrs: {
                      doCheck = false;
                    });
                  }
                )
              ];
            };
          pkgs = makePkgs nixpkgs;
          emacs = pkgs.emacs30.pkgs.withPackages (p: [
            p.org-re-reveal
            p.haskell-mode
          ]);

          hlib = pkgs.haskell.lib.compose;
        in
        {
          formatter = pkgs.nixfmt;
          devShells = {
            haskell =
              let
                liquid-haskell-project =
                  (pkgs.haskellPackages.callCabal2nix "liquid-haskell" (pkgs.lib.cleanSource ./liquid-haskell) { })
                  .overrideAttrs
                    (old: {
                      nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ pkgs.z3 ];
                    });
              in
              pkgs.haskellPackages.shellFor {
                packages = _: [
                  liquid-haskell-project
                ];
                nativeBuildInputs = [ pkgs.haskellPackages.doctest ];
                buildInputs = [
                  pkgs.cabal-install
                  self'.packages.hls
                  pkgs.z3
                ];
                shellHook = ''
                  export PS1="\n\[\033[1;32m\][nix-shell:\W \[\033[1;31m\]FM\[\033[1;32m\]]\$\[\033[0m\] "
                  echo -e "\n\033[1;31m ♣ ♠ Welcome to FM - Haskell! ♥ ♦ \033[0m\n"
                  echo -e "   Use the following command to open VSCode in this directory:\n"
                  echo "       code ."
                '';
              };

            haskell-withVSCode = self.devShells.${system}.haskell.overrideAttrs (
              old:
              let
                vscode = pkgs.vscode-with-extensions.override {
                  vscodeExtensions = with pkgs.vscode-extensions; [
                    bbenoist.nix
                    haskell.haskell
                    justusadam.language-haskell
                  ];
                };
              in
              {
                buildInputs = old.buildInputs ++ [ vscode ];
                shellHook =
                  old.shellHook + ''echo -e "\n   All required extensions should be pre-installed and ready."'';
              }
            );

            verifast =
              let
                # if we use this for Haskell dev shell, things fail in spectacularly mysterious ways
                nixpkgsPatched = legacyPackages.applyPatches {
                  name = "verifast-on-macos";
                  src = nixpkgs;
                  patches = legacyPackages.fetchpatch {
                    url = "https://patch-diff.githubusercontent.com/raw/NixOS/nixpkgs/pull/429378.patch";
                    hash = "sha256-Xtm/5VhoaLW6T1uKbDOZiw+ZaFQcUZy3cmWdNTHHIHE=";
                  };
                };
              in
              pkgs.mkShell {
                packages = [
                  (makePkgs nixpkgsPatched).verifast
                ];

                shellHook = ''
                  export PS1="\n\[\033[1;32m\][nix-shell:\W \[\033[1;31m\]FM\[\033[1;32m\]]\$\[\033[0m\] "
                  echo -e "\n\033[1;31m ♣ ♠ Welcome to FM - Verifast! ♥ ♦ \033[0m\n"
                '';
              };

          };

          legacyPackages = pkgs;

          packages = {
            hls = pkgs.haskell-language-server.override {
              supportedGhcVersions = [ ghcVersion ];
            };
            # To be able to specifically build decktape without the Nix sandbox,
            # we need to make it a package instead of an app.
            decktapeWithDependencies = pkgs.stdenv.mkDerivation {
              name = "decktape-with-dependencies";
              src = inputs.decktape;
              buildInputs = [
                pkgs.nodejs
                pkgs.cacert
              ];
              buildPhase = "HOME=$TMP npm install";
              installPhase = "cp -r . $out";
            };

            # Provide the Emacs that is used to build the slides; might be useful
            # for debugging.
            emacs = pkgs.writeShellScriptBin "reveal-emacs" ''
              ${emacs}/bin/emacs -Q
            '';

            watch = pkgs.writeShellScriptBin "watch-and-commit" ''
              ${pkgs.lib.getExe pkgs.watch} -n 10 "git add . && git commit -m update && git push"
            '';
          };

          apps = {
            # The default target for `nix run`. This builds the reveal.js slides.
            slides =
              let
                app = pkgs.writeShellScript "org-re-reveal" ''
                  if [ ! -e slides/plantuml/plugins ]; then
                    mkdir -p slides/plantuml/plugins
                    ln -snf ${inputs.plantumlC4}/*.puml slides/plantuml/plugins/.
                    echo Symlinked PlantUML C4 to ./slides/plantuml/plugins
                    ln -snf ${inputs.plantumlEIP}/dist/*.puml slides/plantuml/plugins/.
                    echo Symlinked PlantUML EIP to ./slides/plantuml/plugins
                  fi

                  export REVEAL_ROOT="${inputs.revealjs}"
                  export REVEAL_MATHJAX_URL=
                  export PATH=${pkgs.plantuml}/bin:$PATH
                  echo $@
                  ${emacs}/bin/emacs --batch -q -l slides/export.el \
                      --eval="(org-re-reveal-export-file \"$@\" \"${inputs.revealjs}\" \"${inputs.mathjax}/tex-chtml.js\")"
                '';
              in
              {
                type = "app";
                program = "${app}";
              };

            # May be used to create the PDF version of the talk. See the Makefile
            # for an actual invocation.
            decktape =
              let
                app = pkgs.writeShellScript "run-decktape" "${pkgs.nodejs}/bin/node ${
                  self.packages.${system}.decktapeWithDependencies
                }/decktape.js $@";
              in
              {
                type = "app";
                program = "${app}";
              };
            pdfunite =
              let
                poppler = pkgs.poppler_utils;
              in
              {
                type = "app";
                program = "${poppler}/bin/pdfunite";
              };
          };
        };
    };
}

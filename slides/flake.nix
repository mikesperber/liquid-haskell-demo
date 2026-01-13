{
  description = "An Active Group presentation";

  nixConfig.sandbox = false;

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
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

  outputs = inputs@{ self, nixpkgs, flake-utils, ... }:
    let
      supportedSystems = with flake-utils.lib.system; [
        x86_64-linux
        x86_64-darwin
        aarch64-darwin
      ];
    in flake-utils.lib.eachSystem supportedSystems (system:
      let
        pkgs = import nixpkgs { inherit system; };
        emacs = pkgs.emacs30.pkgs.withPackages (p: [
          p.org-re-reveal
          p.gnuplot
          p.gnuplot-mode
          p.haskell-mode
          p.clojure-mode
        ]);
      in {
        packages = {
          # To be able to specifically build decktape without the Nix sandbox,
          # we need to make it a package instead of an app.
          decktapeWithDependencies = pkgs.stdenv.mkDerivation {
            name = "decktape-with-dependencies";
            src = inputs.decktape;
            buildInputs = [ pkgs.nodejs pkgs.cacert ];
            buildPhase = "HOME=$TMP npm install";
            installPhase = "cp -r . $out";
          };

          # Provide the Emacs that is used to build the slides; might be useful
          # for debugging.
          emacs = pkgs.writeShellScriptBin "reveal-emacs" ''
            ${emacs}/bin/emacs -Q
          '';
        };

        apps = {
          # The default target for `nix run`. This builds the reveal.js slides.
          default = let
            app = pkgs.writeShellScript "org-re-reveal" ''
              if [ ! -e plantuml/plugins ]; then
                mkdir -p plantuml/plugins
                ln -snf ${inputs.plantumlC4}/*.puml plantuml/plugins/.
                echo Symlinked PlantUML C4 to ./plantuml/plugins
                ln -snf ${inputs.plantumlEIP}/dist/*.puml plantuml/plugins/.
                echo Symlinked PlantUML EIP to ./plantuml/plugins
              fi

              export REVEAL_ROOT="${inputs.revealjs}"
              export REVEAL_MATHJAX_URL=
              export PATH=${pkgs.plantuml}/bin:${pkgs.gnuplot}/bin:$PATH
              echo $@
              ${emacs}/bin/emacs --batch -q -l export.el \
                  --eval="(org-re-reveal-export-file \"$@\" \"${inputs.revealjs}\" \"${inputs.mathjax}/es5/tex-chtml.js\")"
            '';
          in {
            type = "app";
            program = "${app}";
          };

          # May be used to create the PDF version of the talk. See the Makefile
          # for an actual invocation.
          decktape = let
            app = pkgs.writeShellScript "run-decktape"
              "${pkgs.nodejs}/bin/node ${
                self.packages.${system}.decktapeWithDependencies
              }/decktape.js $@";
          in {
            type = "app";
            program = "${app}";
          };
          pdfunite = let poppler = pkgs.poppler_utils;
          in {
            type = "app";
            program = "${poppler}/bin/pdfunite";
          };
        };
      });
}

{
  description = "FM";

  inputs = {
    # nixpkgs.url = "github:nixos/nixpkgs/release-25.11";
    nixpkgs.url = "path:/Users/sperber/build/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs =
    inputs@{ self, flake-parts, ... }:
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
          pkgs = import inputs.nixpkgs {
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
                        liquidhaskell = hprev.liquidhaskell_0_9_12_2;
                      }
                    );
                  });
                }
              )
            ];
          };
          hlib = pkgs.haskell.lib.compose;
          liquid-haskell =
            (pkgs.haskellPackages.callCabal2nix "liquid-haskell" (pkgs.lib.cleanSource ./liquid-haskell) { })
            .overrideAttrs
              (old: {
                nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ pkgs.z3 ];
              });
        in
        {
          formatter = pkgs.nixfmt;
          devShells = {
            default = pkgs.haskellPackages.shellFor {
              packages = _: [
                liquid-haskell
              ];
              nativeBuildInputs = [ pkgs.haskellPackages.doctest ];
              buildInputs = [
                pkgs.cabal-install
                self'.packages.hls
                pkgs.z3
              ];
              shellHook = ''
                export PS1="\n\[\033[1;32m\][nix-shell:\W \[\033[1;31m\]FM\[\033[1;32m\]]\$\[\033[0m\] "
                echo -e "\n\033[1;31m ♣ ♠ Welcome to FM! ♥ ♦ \033[0m\n"
                echo -e "   Use the following command to open VSCode in this directory:\n"
                echo "       code ."
              '';
            };

            withVSCode = self.devShells.${system}.default.overrideAttrs (
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
          };

          legacyPackages = pkgs;

          packages = {
            inherit liquid-haskell;
            inherit (pkgs) cabal-install;

            hls = pkgs.haskell-language-server.override {
              supportedGhcVersions = [ ghcVersion ];
            };

            # HACK: We rely on how `shellFor` constructs its `nativeBuildInputs`
            # in order to grab the `ghcWithPackages` from out of there. That way
            # we're able to globally install this GHC in the Docker image and
            # get rid of direnv as a dependency.
            ghcForFm = builtins.head self.devShells.${system}.default.nativeBuildInputs;

            watch = pkgs.writeShellScriptBin "watch-and-commit" ''
              ${pkgs.lib.getExe pkgs.watch} -n 10 "git add . && git commit -m update && git push"
            '';
          };
        };
    };
}

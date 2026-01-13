# FIXME Presentation title

## Usage

Build the HTML presentations with `make`.  Convert the slides to PDF
with `make pdf`.

## Updating flake inputs

Sometimes it's necessary to update the flake inputs, like `nixpkgs`
or `plantuml`.  The command

```shell
nix flake update
```

updates *all* flake inputs, while

```shell
nix flake lock --update-input <my-input>
```

may be used to update a single input to its latest version.  See the
respective help pages for the specific Nix commands, like `nix flake
lock --help`.
